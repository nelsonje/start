class Function
	attr_accessor :bbs
	def initialize(name)
		@name = name
		@bbs = []
	end

	public
	def build_cfg
		#This assures that building CFG is low complexity
		bb_index = {}
		@bbs.each do |bb|
			inst_n = (bb.instructions.first.inst_str)[1].scan(/[\d]+/)
			inst_n = Integer(inst_n[0])
			bb_index[inst_n] = bb
		end
		@bbs.each do |bb|
			last_inst = bb.instructions.last
			case last_inst.opcode
			when "call", "br"
				target = last_inst.operands[0]
				target_bb = bb_index[target]
				bb.sucs.push target_bb
				target_bb.preds.push bb
			when "blbc", "blbs"
				target = last_inst.operands[1]
				target_bb = bb_index[target]
				bb.sucs.push target_bb
				target_bb.preds.push bb
			end
		end
	end





end
