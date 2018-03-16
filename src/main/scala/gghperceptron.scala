//*************************************************************************
// Copyright by MPRC in Peking University
//
// The GGHPerceptron Predictor need also one cycle when accepting a request. 
// The GGHPerceptron 's parameter can be set in configs.scala,including 
// history_length, num_entries, theta, weight_width, which ia like Perceptron
// predictor, and extra num_groups, one_group_width ,which set the grouped
// global history.
//
//
//-------------------------------------------------------------------------
//-------------------------------------------------------------------------
//***************** RISCV GGHPerceptron Predictor *************************
//-------------------------------------------------------------------------
//-------------------------------------------------------------------------
//
// Yongquan Hu
// 2018.3


package boom

import Chisel._
import config.{Parameters, Field}

case class GGHPerceptronParameters(
	enabled: Boolean = true,
	num_entries: Int = 64,
	num_groups: Int = 8,
	one_group_width: Int = 2,
	history_length: Int = 16,
	theta: Int = 43,
	weight_width: Int = 9
)

class GGHPerceptronResp(index_sz: Int, fetch_width: Int, history_length: Int, group_index_sz: Int) extends Bundle
{
	val index = UInt(width = index_sz)
	val gghperceptronSumIsBigEnough = UInt(width = fetch_width)
	val oldHistory = UInt(width = history_length)
	val group_index = UInt(width = group_index_sz)
	
	override def cloneType: this.type = new GGHPerceptronResp(index_sz, fetch_width, history_length, group_index_sz).asInstanceOf[this.type]
}

object GGHPerceptronBrPredictor
{
	def GetRespInfoSize(p: Parameters, index_sz: Int, fetch_width: Int, history_length: Int, group_index_sz: Int): Int =
	{
		val dummy = new GGHPerceptronResp(index_sz, fetch_width, history_length, group_index_sz)
		dummy.getWidth
	}
}


class GGHPerceptronBrPredictor(
	fetch_width: Int = 2,
	num_entries: Int = 64,
	num_groups: Int = 8,
	one_group_width: Int = 2,
	history_length: Int = 16,
	theta: Int = 43,
	weight_width : Int = 9
	)(implicit p: Parameters) extends BrPredictor(fetch_width, num_groups * one_group_width)(p)
{

	require (coreInstBytes == 4)
	
	// gghperceptron table	
	val table = Mem(num_entries, Vec(history_length + 1,SInt(0, width=weight_width)))


	// Initialize table
	// It's very nessary or the table will be initialized randomly and the prediction result is very bad 
	val cycleCount = Reg(init = SInt(0, 32))
	val temp = Wire(init=Vec.fill(history_length + 1) {SInt(0, weight_width)})
	temp(0) := 1.S
	for(j <- 1 until history_length + 1)
	{
		temp(j) := 0.S
	}
	when(cycleCount === 0.S)
	{
		for(i <- 0 until num_entries)
		{
			table(i) := temp
		}
	}
	cycleCount := cycleCount + 1.S
	


	val gghistoryRegister = new GGHistoryRegister(num_groups, one_group_width, fetch_width)

	// for spective update gghistory
	val last_index = RegNext((io.req_pc >> log2Up(coreInstBytes*fetch_width))(log2Up(num_groups) - 1, 0))

	val gghistory = gghistoryRegister.getGGHistory(
      io.hist_update_spec.valid,
      io.hist_update_spec.bits,
	  last_index,
      io.exe_bpd_update.valid,
      io.exe_bpd_update.bits,
      r_flush)
	
	gghistoryRegister.update(
		io.hist_update_spec.valid,
		io.hist_update_spec.bits,
		last_index,
		io.exe_bpd_update.valid,
		io.exe_bpd_update.bits,
		r_flush,
		disable = Bool(false))

// carefull ,may be problem; Reuse io.f3_resp_history to store one_group_hist
	val group_index_sz = log2Up(num_groups)
	val req_group_index = (io.req_pc >> (coreInstBytes * fetch_width))(group_index_sz - 1, 0)
	val one_group_hist = gghistoryRegister.getOneGroupHist(
														req_group_index,
														io.hist_update_spec.valid,
														io.hist_update_spec.bits,
														last_index,
														io.exe_bpd_update.valid,
														io.exe_bpd_update.bits,
														r_flush
														)
	this.ghistory := one_group_hist << (history_length - one_group_width) >> (history_length - one_group_width)

	io.f3_resp_history match
	{
	   case Some(resp_history: UInt) => resp_history := ghistory
	   case _ => require (ENABLE_VLHR)
	}	

	val gghperceptronSumIsBigEnough = Wire(Vec(fetch_width, Bool()))

	private def GetPrediction(idx: UInt): Vec[Bool] =
	{
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
				
				when(gghistory(j-1) === false.B)
				{
					adder := SInt(0) - weights(j)

				}
				percepSum = percepSum + adder
			}

			predictions(i) := !percepSum(8)
			
			when(percepSum < SInt(theta) && percepSum > SInt(-theta))
			{
				gghperceptronSumIsBigEnough(i) := Bool(false)
			}
			.otherwise
			{
				gghperceptronSumIsBigEnough(i) := Bool(true)
			}

			// debug
			//printf("percepSum: %d ", percepSum)
			//printf("prediction: %d ", predictions(i))
			//printf("isBigEnought: %d    ", gghperceptronSumIsBigEnough(i))

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
		gghperceptronSumIsBigEnough: UInt
	) =
	{
		for(i <- 0 until fetch_width)
		{
			when(valid){
				when (enables(i) && ((mispredictions(i)) || gghperceptronSumIsBigEnough(i) === 0.U))
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
					printf("mispredict = %d    br = %d\n", mispredCount, predictionCount)
				}
			}
		}
	}

	//-----------------------------------------------------------------
	// Get prediction
	val stall = !io.resp.ready
	val idx = (io.req_pc >> UInt(log2Up(coreInstBytes)) >> UInt(log2Up(fetch_width)) << UInt(log2Up(fetch_width)))(log2Up(num_entries) - 1, 0)
	//val idx = io.req_pc >> 3 << 1
	val resp_info = Wire(new GGHPerceptronResp(log2Up(num_entries), 2, history_length, group_index_sz))

	resp_info.index := RegNext(idx)
	resp_info.gghperceptronSumIsBigEnough := RegNext(gghperceptronSumIsBigEnough.asUInt)
	resp_info.oldHistory := RegNext(gghistory)
	resp_info.group_index := RegNext(req_group_index)

	io.resp.valid := Bool(true)
	io.resp.bits.takens := RegNext(GetPrediction(idx).toBits)
	io.resp.bits.info := resp_info.asUInt
	
	
	val commit_info =new GGHPerceptronResp(log2Up(num_entries), 2, history_length, group_index_sz).fromBits(commit.bits.info.info)

	UpdateTable(this.commit.valid, 
				this.commit.bits.ctrl.executed, 
				commit_info.index,
				this.commit.bits.ctrl.taken,
				this.commit.bits.ctrl.mispredicted, 
				commit_info.oldHistory, 
				commit_info.gghperceptronSumIsBigEnough)
	
	// update commit_gghhistory
	when(commit.valid)
	{
		gghistoryRegister.commit(commit_info.group_index, this.commit.bits.ctrl.taken.reduce(_|_))
	}

}


class GGHistoryRegister(num_groups: Int, one_group_width: Int, fetch_width: Int)
{
	//private val r_history = Wire(Vec(num_groups, Reg(init = Bits(0, width = one_group_width))))
	//private val r_commit_history = Wire(Vec(num_groups, Reg(init = Bits(0, width = one_group_width))))
	private val r_history = Mem(num_groups, UInt(0,width=one_group_width))
	private val r_commit_history = Mem(num_groups, UInt(0,width=one_group_width))

	val coreInstBytes = 4

	def getGGHistory(
      hist_update_spec_valid: Bool,
      hist_update_spec_bits: GHistUpdate,
      last_index: UInt,
      br_resolution_valid: Bool,
      br_resolution_bits: BpdUpdate,
      flush: Bool
      ): UInt =
	  {
	  	val res = Wire(init=UInt(1, num_groups * one_group_width))

		// Bypass get gghistory
		when(flush)
		{
			//res := r_commit_history.toBits
			var tmp = r_commit_history(0)
			for(i <- 1 until num_groups)
			{
				tmp = Cat(tmp, r_commit_history(i))
			}
			res := tmp
		}
		.elsewhen (hist_update_spec_valid)
		{
			val specialGroupHistInUpdateSpec = Cat(r_history(last_index), hist_update_spec_bits.taken)(one_group_width - 1, 0)
			val tmp1 = r_history
			tmp1(last_index) := specialGroupHistInUpdateSpec

			var tmp2 = tmp1(0)
			for(i <- 1 until num_groups)
			{
				tmp2 = Cat(tmp2, tmp1(i))
			}
			res := tmp2
		}
		.elsewhen (br_resolution_valid && br_resolution_bits.mispredict && br_resolution_bits.new_pc_same_packet)
		{
			//use resolutionhistory
			val specialIdx = (br_resolution_bits.pc >> log2Up(coreInstBytes * fetch_width))(log2Up(num_groups) - 1, 0)
			val specialGroupHistInBrResolution = getHistory(br_resolution_bits)(one_group_width - 1, 0)//history(one_group_width - 1, 0)
			//val tmp = Wire(Vec(num_groups, Reg(Bits(width=one_group_width))))
			val tmp1 = r_history
			tmp1(specialIdx) := specialGroupHistInBrResolution
			//res := tmp.toBits
			//var tmp = if(specialIdx === 0) specialGroupHistInBrResolution else 
			var tmp2 = tmp1(0)
			for(i <- 1 until num_groups)
			{
				tmp2 = Cat(tmp2, tmp1(i))
			}
			res := tmp2
		}
		.elsewhen(br_resolution_valid && br_resolution_bits.bpd_mispredict)
		{
			//fixed history
			val specialIdx = (br_resolution_bits.pc >> log2Up(coreInstBytes * fetch_width))(log2Up(num_groups) - 1, 0)
			val fixedSpecilGroupHist = Cat(getHistory(br_resolution_bits), br_resolution_bits.taken)(one_group_width - 1, 0)
			val tmp1 = r_history
			tmp1(specialIdx) := fixedSpecilGroupHist
			var tmp2 = tmp1(0)
			for(i <- 1 until num_groups)
			{
				tmp2 = Cat(tmp2, tmp1(i))
			}
			res := tmp2
		}
		.otherwise
		{
			//res := r_history.toBits
			var tmp = r_history(0)
			for(i <- 1 until num_groups)
			{
				tmp = Cat(tmp, r_commit_history(i))
			}
			res := tmp
		}
	 
		res
	  }



	  def getHistory(resolution: BpdUpdate): UInt =
   	  {
   	     resolution.history match
   	     {
   	        case Some(history: UInt) => history
   	        case _ => UInt(0) // enable vlhr
   	     }
   	  }
	  
	  def update(
      hist_update_spec_valid: Bool,
      hist_update_spec_bits: GHistUpdate,
	  last_index: UInt,
      br_resolution_valid: Bool,
      br_resolution_bits: BpdUpdate,
      flush: Bool,
      disable: Bool
	  ) = 
	  {
	  	when (disable)
		{
		//	r_history := r_history
		}
		.elsewhen (flush)
		{
			for(i <- 0 until num_groups)
			{
				r_history(i) := r_commit_history(i)
			}
		}
		.elsewhen (br_resolution_valid && br_resolution_bits.mispredict)
		{
			val specialIdx = (br_resolution_bits.pc >> log2Up(coreInstBytes * fetch_width))(log2Up(num_groups) - 1, 0)
			val ret_history =  getHistory(br_resolution_bits)
			r_history(specialIdx) := 
				Cat(ret_history, br_resolution_bits.taken)(one_group_width - 1, 0)
		}
		.elsewhen (hist_update_spec_valid)
		{
			val fixed_group = Wire(init=UInt(0, num_groups*one_group_width))
			fixed_group := (Cat(r_history(last_index), hist_update_spec_bits.taken))(one_group_width - 1, 0)
			r_history(last_index) := fixed_group
		}
	  
	  }

	
	  def commit(index: UInt, taken: Bool) =
	  {
	  	val tmp = r_commit_history(index)
	  	r_commit_history(index) := Cat(tmp, taken)(one_group_width - 1, 0)
	
	  }

	// Bypass to get one group history to pass to pipeline
	  def getOneGroupHist(
	  	index: UInt,
      	hist_update_spec_valid: Bool,
      	hist_update_spec_bits: GHistUpdate,
		last_index: UInt,
      	br_resolution_valid: Bool,
      	br_resolution_bits: BpdUpdate,
      	flush: Bool): UInt = 
	  {
	  	val res = Wire(init = UInt(1, log2Up(num_groups)))
		val specialIdx = (br_resolution_bits.pc >> log2Up(coreInstBytes * fetch_width))(log2Up(num_groups) - 1, 0)

		when (flush)
		{
			res := r_commit_history(index)
		}
		.elsewhen (br_resolution_valid && br_resolution_bits.mispredict && br_resolution_bits.new_pc_same_packet && specialIdx === index)
		{
			res := getHistory(br_resolution_bits)(one_group_width - 1, 0)
		}
		.elsewhen (br_resolution_valid && br_resolution_bits.bpd_mispredict && specialIdx === index) 
		{
			res := Cat(getHistory(br_resolution_bits), br_resolution_bits.taken)(one_group_width - 1, 0)
		}
		.elsewhen (hist_update_spec_valid && last_index === index)
		{
			res := Cat(r_history(index), hist_update_spec_bits.taken)(one_group_width - 1, 0)
		}
		.otherwise
		{
	  		res := r_history(index)
		}
		res
	  }
}


