//**************************************************************************
// Copyright by MPRC in Peking University
//
// The Perceptron Predictor need one cycle when accepting a reques. 
// It accuire very high prediction accurancy, higher than gshare with 
// cost about half of gshare.
// The Perceptron 's parameter can be set in parameter.scala, including 
// history_length, num_entries which must be 2's power, theta which is about
// 1.94 * history_length + 14, weight_width which need be carefully set and 
// it can accomadate perceptron sum
//--------------------------------------------------------------------------
//--------------------------------------------------------------------------
//************ RISCV Perceptron Branch Predictor****************************
//--------------------------------------------------------------------------
//--------------------------------------------------------------------------
//
// Yongquan Hu
// 2018.3 


package boom

import Chisel._
import config.{Parameters, Field}

case class PerceptronParameters(
	enabled: Boolean = true,
	history_length: Int = 15,
	num_entries: Int = 64,
	theta: Int = 43,
	weight_width : Int = 9
)

class PerceptronResp(index_sz: Int, fetch_width: Int, history_length: Int) extends Bundle
{
// need to update predictor at Commit
	val index = UInt(width = index_sz)
	val percepSumIsBigEnough = UInt(width = fetch_width) 
	val oldHistory = UInt(width = history_length)
	
	override def cloneType: this.type = new PerceptronResp(index_sz, fetch_width, history_length).asInstanceOf[this.type]
}

object PerceptronBrPredictor
{
	def GetRespInfoSize(p: Parameters, index_sz: Int, fetch_width: Int, history_length: Int): Int = 
	{
		val dummy = new PerceptronResp(index_sz, fetch_width, history_length)
		dummy.getWidth
	}
}

class PerceptronBrPredictor(
	fetch_width: Int,
	history_length: Int = 15,
	num_entries: Int = 64,
	theta: Int = 43,
	weight_width : Int = 9
	)(implicit p: Parameters) extends BrPredictor(fetch_width, history_length)(p)
{
	//val num_entries = 64

	require (coreInstBytes == 4)

	// perceptron table	
	val table = Mem(num_entries, Vec(history_length + 1,SInt(0, width=weight_width)))


	// Initialize table
	// It's very nessary or the table will be initialized randomly and the prediction result is very bad 
	val cycleCount = Reg(init = SInt(0, 32))
	val temp = Wire(init=Vec.fill(history_length + 1) {SInt(0, weight_width)})
	temp(0) := 1.S
	for(j <-1 until history_length + 1)
	{
		temp(j) := 0.S
	}
	when(cycleCount === 0.S)
	{
		printf("Perceptron\n")
		for(i <- 0 until num_entries)
		{
			table(i) := temp
		}
	}
	cycleCount := cycleCount + 1.S
	


	val percepSumIsBigEnough = Wire(Vec(fetch_width, Bool()))
	//val percepSumIsBigEnough = Wire(init=UInt(0, width = fetch_width))
	private def GetPrediction(idx: UInt): Vec[Bool] =
	{
		//val theta = Wire(init=SInt(30))
		//theta := SInt(2 * history_length + 14)
		//var newyout = Vec(fetch_width, SInt(width=8))
		val predictions = Wire(Vec(fetch_width, Bool()))
		for(i <- 0 until fetch_width)
		{
			//val weights = Wire(Vec(history_length + 1, SInt(width=8.W)))
			val weights = table(idx + UInt(i))
			var percepSum = Wire(init=SInt(0, weight_width))
			percepSum = weights(0)
			for(j <- 1 until history_length + 1)
			{
				val adder = Wire(init=weights(j))
				
				when(this.ghistory(j-1) === false.B)
				{
					adder := SInt(0) - weights(j)

				}
				percepSum = percepSum + adder
			}

			predictions(i) := !percepSum(8)
			
			when(percepSum < SInt(theta) && percepSum > SInt(-theta))
			{
				percepSumIsBigEnough(i) := Bool(false)
				//percepSumIsBigEnough(i) := percepSumIsBigEnough(i) & (~(1.U << i.asUInt))
			}
			.otherwise
			{
				percepSumIsBigEnough(i) := Bool(true)
				//percepSumIsBigEnough(i) := percepSumIsBigEnough(i) | (1.U << i.asUInt)
			}

			// debug
			//printf("percepSum: %d ", percepSum)
			//printf("prediction: %d ", predictions(i))
			//printf("isBigEnought: %d    ", percepSumIsBigEnough(i))

		}
		//printf("\n")
		predictions
			
	}


	val predictionCount = Reg(init= SInt(0, 32))
	val mispredCount = Reg(init = SInt(0, 32))
	private def UpdateTable(
		valid: Bool,
		enables: Vec[Bool],
		idx: UInt,
		takens: Vec[Bool],
		mispredictions: Vec[Bool],
		oldHistories: UInt,
		percepSumIsBigEnough: UInt
	) =
	{
		for(i <- 0 until fetch_width)
		{
			when(valid){
				when (enables(i) && ((mispredictions(i)) || percepSumIsBigEnough(i) === 0.U))
				{
					
					val index = idx + UInt(i)
					//val tmp = Wire(Vec(history_length + 1, SInt(width=8.W)))
					//tmp := table(index)
					val updatedWeights = table(index)
					when(takens(i) === Bool(true))
					{
						updatedWeights(0) := updatedWeights(0) + SInt(1)
					}
					.otherwise
					{
						updatedWeights(0) := updatedWeights(0) - SInt(1)
					}
					for(j <- 0 until history_length)
					{
						when (oldHistories(j) === takens(i))
						{
							updatedWeights(j + 1) := updatedWeights(j + 1) + SInt(1)
						}
						.otherwise
						{
							updatedWeights(j + 1) := updatedWeights(j + 1) - SInt(1)
						}
					}
					table(index) := updatedWeights
				}

				//statis misprediction ratio
				when(enables(i))
				{
					predictionCount := predictionCount + 1.S
					when(mispredictions(i))
					{
						mispredCount := mispredCount + 1.S	
					}
					printf("mis_preict = %d   br_total = %d\n", mispredCount, predictionCount)
				}
			}
		}
	}

	//-----------------------------------------------------------------
	// Get prediction
	val stall = !io.resp.ready
	val idx = (io.req_pc >> UInt(log2Up(coreInstBytes)) >> UInt(log2Up(fetch_width)) << UInt(log2Up(fetch_width)))(log2Up(num_entries) - 1, 0)
	//val idx = io.req_pc >> 3 << 1
	val resp_info = Wire(new PerceptronResp(log2Up(num_entries), 2, history_length))

	resp_info.index := RegNext(idx)
	resp_info.percepSumIsBigEnough := RegNext(percepSumIsBigEnough.asUInt)
	resp_info.oldHistory := RegNext(this.ghistory)

	io.resp.valid := Bool(true)
	io.resp.bits.takens := RegNext(GetPrediction(idx).toBits)
	//io.resp.bits.takens := (GetPrediction(idx).toBits)
	//io.resp.bits.takens := UInt(0)
	io.resp.bits.info := resp_info.asUInt
	
	val commit_info =new PerceptronResp(log2Up(num_entries), 2, history_length).fromBits(commit.bits.info.info)

	UpdateTable(this.commit.valid, this.commit.bits.ctrl.executed, commit_info.index, this.commit.bits.ctrl.taken, this.commit.bits.ctrl.mispredicted, commit_info.oldHistory, commit_info.percepSumIsBigEnough)
	
	/*when(commit.valid)
	{
		printf("-- %x --\n", io.resp.bits.takens)
	}*/
}
