class Instruction
	attr_accessor	:opcode, :operands
	attr_reader	:inst_str

	def initialize(inst)
		if inst[0] == "instr"
			@opcode = inst[2]
		else
			@opcode = inst[0]
		end
		@operands = []
		case @opcode
		when "method"
			info = inst[1].scan(/[^@:]+/)
			@operands.push info[0]
			@operands.push Integer(info[1])
		when "call", "br"
			info = inst[3].scan(/[\d]+/)
			@operands.push Integer(info[0])
		when "blbc", "blbs"
			info = inst[3].scan(/[\d]+/)
			@operands.push Integer(info[0])
			info = inst[4].scan(/[\d]+/)
			@operands.push Integer(info[0])
		when "ret", "enter"
			@operands.push Integer(inst[3])
		else
		end
		@inst_str = inst
	end


end

