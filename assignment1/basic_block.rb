class BasicBlock
	attr_accessor :sucs, :preds, :instructions

	def initialize(insts, first, last)
		@sucs = []
		@preds = []
		@instructions = []
		for i in first..last
			@instructions.push insts[i]
		end
	end









end
