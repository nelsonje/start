class BasicBlock
	attr_accessor :sucs, :preds, :instructions, :id, :visited, :topo_id

	def initialize(insts, first, last)
		@sucs = []
		@preds = []
		@instructions = []
		for i in first..last
			@instructions.push insts[i]
		end
          @visited = :unvisited
	end


        def id
          if @instructions.empty?
            return -1
          else
            return instructions[0].id
          end
        end





end
