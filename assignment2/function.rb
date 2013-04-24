class Function
  attr_accessor :bbs, :name
  def initialize(name)
    @name = name
    @bbs = []
    @topo = []
    @doms = []
    #For each variable, gives the set of BBs in which it's assigned to.
    #Necessary for SSA construction
    @var_bb_def = {}
    #Set of all vars
    @vars = []

    #Auxiliary vars needed for SSA construction (var renaming)
    @c = []
    @s = []
  end

  public
  def to_ssa
  	compute_df
	set_vars_assign
	place_phis
  end

  private
  def which_pred(x, y)
  	y.preds.each_index do |i|
		if y.preds[i] == x
			which = i
		end
	end
	which
  end

  #private
  #def search_phi_renaming(x)
  #	x.instructions.each do |a|
#		a.rhs.each do |v|
#			a.operands.each do |operand|
#				if operand == v
#					operand = operand + "{" + @s[v].last.to_s + "}"
#				end
#			end
#		end
#		a.lhs.each do |v|
#			i = @c[v]
#			a.operands.each do |operand|
#				if operand == v
#					operand = operand + "{" + i.to_s + "}"
#				end
#			end
#			@s[v].push i
#			@c[v] = i + 1
#		end
#	end

#	x.sucs.each do |y|
#		j = which_pred(y, x)
#	end
#  end

 # private
 # def rename_vars
  #	@vars.each do |v|
#		@c[v] = 0
#		@s[v] = []
#	end
#	search_phi_renaming(@doms[0])
 # end

  #Differs (113) or i#-4 from 113 or 4.
  private
  def is_constant(str)
  	if (str =~ /\(/) || (str =~ /#/)
		false
	else
		true
	end
  end

  #TODO
  #Handle the unknown instructions mentioned in Instruction.rb
  private
  def set_vars_assign
  	@bbs.each do |bb|
		bb.instructions.each do |inst|
			case inst.opcode
			when "sub", "add", "mul", "div", "mod", "cmpeq", "cmple", "cmplt"
				if @var_bb_def[inst.id.to_s] == nil
					@var_bb_def[inst.id.to_s] = []
				end
				@var_bb_def[inst.id.to_s].push bb
				@vars.push inst.id.to_s
				inst.lhs.push inst.id.to_s
				if !is_constant(inst.operands[0])
					new_str = inst.operands[0].chomp(")")
					new_str.sub!(/^[(]/, '')
					@vars.push new_str
					inst.rhs.push new_str
				end
				if !is_constant(inst.operands[1])
					new_str = inst.operands[1].chomp(")")
					new_str.sub!(/^[(]/, '')
					@vars.push new_str
					inst.rhs.push new_str
				end
			when "istype", "checktype", "load", "isnull", "newlist", "checknull", "lddynamic"
				if @var_bb_def[inst.id.to_s] == nil
					@var_bb_def[inst.id.to_s] = []
				end
				@var_bb_def[inst.id.to_s].push bb
				@vars.push inst.id.to_s
				inst.lhs.push inst.id.to_s
				if !is_constant(inst.operands[0])
					new_str = inst.operands[0].chomp(")")
					new_str.sub!(/^[(]/, '')
					@vars.push new_str
					inst.rhs.push new_str
				end
			when "new"
				if @var_bb_def[inst.id.to_s] == nil
					@var_bb_def[inst.id.to_s] = []
				end
				@var_bb_def[inst.id.to_s].push bb
				@vars.push inst.id.to_s
				inst.lhs.push inst.id.to_s
			when "move"
				new_str = inst.operands.last.chomp(")")
				new_str.sub!(/^[(]/, '')
				if @var_bb_def[new_str] == nil
					@var_bb_def[new_str] = []
				end
				@var_bb_def[new_str].push bb
				@vars.push new_str
				inst.lhs.push new_str
				if !is_constant(inst.operands[0])
					new_str = inst.operands[0].chomp(")")
					new_str.sub!(/^[(]/, '')
					@vars.push new_str
					inst.rhs.push new_str
				end
			when "blbc", "blbs"
				@vars.push inst.operands[0].to_s
				inst.rhs.push inst.operands[0].to_s
			when "store", "checkbounds", "stdynamic"
				if !is_constant(inst.operands[0])
					new_str = inst.operands[0].chomp(")")
					new_str.sub!(/^[(]/, '')
					@vars.push new_str
					inst.rhs.push new_str
				end
				if !is_constant(inst.operands[1])
					new_str = inst.operands[1].chomp(")")
					new_str.sub!(/^[(]/, '')
					@vars.push new_str
					inst.rhs.push new_str
				end
			when "write", "param"
				if !is_constant(inst.operands[0])
					new_str = inst.operands[0].chomp(")")
					new_str.sub!(/^[(]/, '')
					@vars.push new_str
					inst.rhs.push new_str
				end
			end
		end
	end
	@vars.uniq!
	@var_bb_def.each_value {|av| av.uniq!}
  end

  private
  def place_phis
  	iter_count = 0
	has_already = {}
	work = {}
	@bbs.each do |x|
		has_already[x] = 0
		work[x] = 0
	end

	w = []
	#@var_bb_def.each do |v, av|
	@vars.each do |v|
		iter_count += 1
		#av.each do |x|
		if @var_bb_def[v] != nil
			@var_bb_def[v].each do |x|
				work[x] = iter_count
				w.push x
			end
		end
		while !w.empty?
			x = w.shift
			x.df.each do |y|
				if has_already[y] < iter_count
					hash = { v => [] }
					y.phi.merge! hash
					has_already[y] = iter_count
					if work[y] < iter_count
						work[y] = iter_count
						w.push y
					end
				end
			end
		end
	end
  end

  public
  def n_nodes
    @bbs.length
  end

  public
  def n_edges
    n = 0
    @bbs.each do |bb|
      n += bb.sucs.length
    end
    n
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
      when "br"
        target = last_inst.operands[0]
        target_bb = bb_index[target]
        bb.sucs.push target_bb
        target_bb.preds.push bb
      when "blbc", "blbs"
        target = last_inst.operands[1]
        target_bb = bb_index[target]
        if !bb.sucs.empty? && (target_bb != bb.sucs[0])
          bb.sucs.push target_bb
          target_bb.preds.push bb
        end
      end
    end
  end

  private
  def find_topo_order

    # reset visited status
    @bbs.each do |bb|
      bb.visited = :unvisited
    end

    # helper for topological order
    def visit( bb )
      # ignore if we've been here before
      if bb.visited == :unvisited
        # note that we're visiting here
        bb.visited = :visiting

        # recurse
        bb.sucs.reverse.each do |suc|
          visit suc
        end

        # now finish this node
        bb.visited = :visited
        @topo.push bb
      end
    end

    # compute topological order
    @bbs.each do |bb|
      # recurse down all unvisited blocks that are connected to something
      if bb.visited == :unvisited && bb.ignore == false
        visit bb
      end
    end

    # we did that backwards, so reverse.
    @topo.reverse!

    # record topological ids in bbs
    index = 0
    max = @topo.length - 1
    @topo.each do |bb|
      bb.topo_id = index
      bb.postorder_id = max - index
      index += 1
    end

  end

  public
  def print_doms
    puts "Dominators"
    @doms.each_index do |i|
      if @doms[i].nil?
        puts @topo[i].id.to_s + ": idom nil"
      else
        puts @topo[i].id.to_s + ": idom " + @doms[i].id.to_s
      end
    end
  end


  public
  def find_doms
    
    # compute order
    find_topo_order

    # helper for dominator constructor
    def intersect( b1, b2 )
      finger1 = b1
      finger2 = b2

      while finger1 != finger2
        while finger1.postorder_id < finger2.postorder_id
          finger1 = @doms[ finger1.topo_id ]
        end
        while finger2.postorder_id < finger1.postorder_id
          finger2 = @doms[ finger2.topo_id ]
        end
      end

      return finger1
    end

    # initialize dominator array
    @topo.each do |bb|
      @doms.push nil
    end

    # start with first node
    start = @topo[0]
    @doms[0] = start
    start.dom_processed = true

    # loop while something changed
    changed = true
    while changed
      
      changed = false
      # postorder iteration
      @topo.each do |bb|
        # skip first node
        if bb != start

          initial_new_idom = nil

          # find an already-processed predecessor
          bb.preds.each do |pred|
            if pred.dom_processed
              initial_new_idom = pred
              break
            end
          end

          # if necessary, refine based on other predecessors 
          new_idom = initial_new_idom
          bb.preds.each do |pred|
            if pred != initial_new_idom
              # if we already have a dominator for this predecessor,
              if !@doms[ pred.topo_id ].nil?
                # see if it gets us a better dominator
                new_idom = intersect pred, new_idom 
              end
            end
          end

          # if domintor changed, update it
          if @doms[bb.topo_id] != new_idom
            @doms[bb.topo_id] = new_idom
            changed = true
          end

          # mark as processed
          bb.dom_processed = true
        end # if bb != start
      end

    end

    # initialize idom fields
    @bbs.each do |bb|
      # clean up leftover nop nodes, etc.
      topo_id = bb.topo_id
      #Bugfix: A node never idominates itself
      if (!topo_id.nil?) && (@doms[bb.topo_id] != bb)
        bb.idom = @doms[bb.topo_id]
      end
    end
    

  end

  	private
	def compute_df_helper(node)
		node.idominates.each do |bb|
			compute_df_helper bb if bb != node
		end
		node.sucs.each {|y| node.df.push y if y.idom != node}
		node.idominates.each do |z|
			z.df.each {|y| node.df.push y if y.idom != node}
		end
	end


	private
	def compute_df
		#Build dominators tree
		@bbs.each do |bb|
			bb.idom.idominates.push bb if bb.idom != nil
		end
		compute_df_helper @doms[0]
	end

end
