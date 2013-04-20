class BasicBlock
  attr_accessor :sucs, :preds, :instructions, :id, :visited, :topo_id, :postorder_id, :dom_processed, :idom, :idominates, :df

  def initialize(insts, first, last)
    @sucs = []
    @preds = []
    @instructions = []
    for i in first..last
      @instructions.push insts[i]
    end
    @visited = :unvisited
    @dom_processed = false
    @idom = self
    #BBs immediately dominated by this one.
    #Necessary for constructing the DF.
    @idominates = []
    #Dominance frontier
    @df = []
  end


  def id
    if @instructions.empty?
      return -1
    else
      return instructions[0].id
    end
  end

  def ignore
    if @instructions.empty?
      return false
    else
      return instructions[0].nop
    end
  end

end
