class BasicBlock
  attr_accessor :sucs, :preds, :instructions, :id, :visited, :topo_id, :postorder_id, :dom_processed, :idom, :idominates, :df, :phi, :original_id, :count

  def initialize(insts, first, last)
    @sucs = []
    @preds = []
    @instructions = []
    for i in first..last
      @instructions.push insts[i]
      insts[i].bb = self
    end
    @visited = :unvisited
    @dom_processed = false
    @idom = nil
    #BBs immediately dominated by this one.
    #Necessary for constructing the DF.
    @idominates = []
    #Dominance frontier
    @df = []
    #Phi instructions
    @phi = {}

      @original_id = -1
      @count = 0
  end


  def id
    if @instructions.empty?
      return -1
    else
      return instructions[0].id
    end
  end

  def pre_ssa_id
    if @instructions.empty?
      return -1
    else
      return instructions[0].pre_ssa_id
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
