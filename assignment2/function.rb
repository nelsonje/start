class Function
  attr_accessor :bbs, :name, :inst_str
  attr_reader   :n_cprop, :n_expr_eliminated
  def initialize(name, inststr, initial_offset, header)
    @name = name
      @method_header = header
    @bbs = []
    @topo = []
    @doms = []
    @inst_str = inststr
    #For each variable, gives the set of BBs in which it's assigned to.
    #Necessary for SSA construction
    @var_bb_def = {}
    #Set of all vars
    @vars = []

    @n_expr_eliminated = 0
    @n_cprop = 0

    #Value Numbers
    @vn = {}

    #Auxiliary vars needed for SSA construction (var renaming)
    @c = {}
    @s = {}

      # storage for ssa-to-normal variables
      @new_instruction_index = 0

      # start allocating new variables at this offset
      @new_variable_index = initial_offset
      @ssa_temp_vars = []

      # new-to-old instruction/bb id map
      @instruction_map = {}
      @bb_map = {}

      # temporary mapping of phi nodes to variable names
      @phi_variables = {}

      # symbol table
      @symbol_table = {}


  end

  private
  def push_var( var, inst )
      if $debug
	  puts "Adding var #{var} from instruction #{inst.inst_str}"
      end
      @vars.push var
  end

  public
  def to_ssa(last_id)

  	compute_df
  	set_var_bb_def
	last_id = place_phis(last_id)
	rename_vars
      @new_instruction_index = last_id + 1

      # build map for later jump target adjustment
      build_bb_map( @doms[0] )
      #dump_bb_map

	last_id
  end

  public
  def gcse
  	@bbs.each do |bb|
		bb.phi.each_value do |right|
			for i in 0...right.length
				@vn[right[i]] = right[i]
			end
		end
	end
  	dvnt(@doms[0], {})
  end

  private
  def which_pred(x, y)
  	which = nil
  	x.preds.each_index do |i|
		if x.preds[i] == y
			which = i
		end
	end
	which
  end

  private
  def search_phi_renaming(x)
	x.phi.each do |left, right|
		old_name = right[0].dup
		i = @c[right[0]]
		right[0] = right[0] + "$" + i.to_s
		@s[old_name].push i
		#puts "(Phi) Pushing " + i.to_s + " for " + old_name
		@c[old_name] = i + 1
	end

  	x.instructions.each do |a|
		a.rhs.each do |v|
			if a.opcode == "move"
				if strip_address(a.operands[0]) == v
					new_operand = strip_address a.operands[0]
					a.operands[0] = new_operand + "$" + @s[v].last.to_s
					a.ssa_mod_operands.push 0
				end
			else
				a.operands.each_index do |op_index|
					if strip_address(a.operands[op_index]) == v
						new_operand = strip_address a.operands[op_index]
						a.operands[op_index] = new_operand + "$" + @s[v].last.to_s
						a.ssa_mod_operands.push op_index
					end
				end
			end
		end
		#Only happens for "move" instructions
		a.lhs.each do |v|
	      puts "id #{a.id} changed before: #{a.opcode}: [#{a.operands[0]}] [#{a.operands[1]}] [#{a.operands[2]}]" if $debug
			i = @c[v]
			if strip_address(a.operands[1]) == v
				new_operand = strip_address a.operands[1]
				a.operands[1] = new_operand + "$" + i.to_s
				a.ssa_mod_operands.push 1
			end
				    puts "id #{a.id} changed: #{a.opcode}: [#{a.operands[0]}] [#{a.operands[1]}] [#{a.operands[2]}]" if $debug

			@s[v].push i
			#puts "(Normal) Pushing " + i.to_s + " for " + v
			@c[v] = i + 1
		end
	end

	x.sucs.each do |y|
		j = which_pred(y, x)
	  #	  puts "#{x} successor #{y} pred #{j}"
	  y.phi.each do |left, right|
	      #	      puts "#{x} successor #{y} pred #{j} left #{left} right #{right}"
	      right[j+1] = strip_address(right[0]) + "$" + @s[strip_address(right[0])].last.to_s
	      #	      puts "Index: " + @s[strip_address(right[0])].last.to_s + "       Strip: " + strip_address(right[0])
	  end
	end

	x.idominates.each do |y|
		search_phi_renaming y if x != y
	end

	x.instructions.each do |a|
		a.lhs.each do |v|
			@s[strip_address(v)].pop
			#puts "(Normal) Popping " + @s[strip_address(v)].to_s + " for " + v
		end
	end
	x.phi.each do |left, right|
		@s[strip_address(right[0])].pop
		#puts "(Phi) Popping " + @s[strip_address(right[0])].to_s + " for " + strip_address(right[0])
	end

  end

  private
  def strip_address(str)
  	new_str = str.scan /[^#\$]+/
	new_str[0]
  end

  private
  def rename_vars
	if !@vars.empty?
 		@vars.each do |v|
			@c[v] = 0
			@s[v] = []
		end
	end
	search_phi_renaming(@doms[0])
	#p @vars
  end

  #Differs (113) or i#-4 from 113 or 4.
  private
  def is_var(str)
  	new_str = strip_address str
	if @vars.find_index(new_str) != nil
		true
	else
		false
	end
  end

  #TODO
  #Handle the unknown instructions mentioned in Instruction.rb
  public
  def set_vars(method_ops)
  	for i in 2...method_ops.length
		@vars.push method_ops[i].dup
	end
	#p @vars
  end

  private
  def set_var_bb_def
  	@bbs.each do |bb|
		bb.instructions.each do |inst|
			case inst.opcode
			when "sub", "add", "mul", "div", "mod", "cmpeq", "cmple", "cmplt", "store", "checkbounds", "stdynamic"
				inst.rhs.push strip_address(inst.operands[0]) if is_var(inst.operands[0])
				inst.rhs.push strip_address(inst.operands[1]) if is_var(inst.operands[1])

			when "istype", "checktype", "load", "isnull", "newlist", "checknull", "lddynamic", "write", "param"
				inst.rhs.push strip_address(inst.operands[0]) if is_var(inst.operands[0])

			when "move"
				if is_var(inst.operands.last)
					if @var_bb_def[strip_address(inst.operands.last)] == nil
						@var_bb_def[strip_address(inst.operands.last)] = []
					end
					@var_bb_def[strip_address(inst.operands.last)].push bb
					inst.lhs.push strip_address(inst.operands.last)
				end
				inst.rhs.push strip_address(inst.operands[0]) if is_var(inst.operands[0])

			when "blbc", "blbs"
				inst.rhs.push strip_address(inst.inst_str[3]) if is_var(inst.inst_str[3])

			end
			inst.rhs.uniq!
			inst.lhs.uniq!
		end
	end
	@var_bb_def.each_value {|av| av.uniq!}
  end

  private
  def place_phis(last_id)
  	iter_count = 0
	has_already = {}
	work = {}
	@bbs.each do |x|
		has_already[x] = 0
		work[x] = 0
	end

	w = []
	#p @vars
	@vars.each do |v|
		iter_count += 1
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
					last_id += 1
					hash = { last_id => [v.dup] }
					if false
					    puts "At BB #{y.id} with variable #{v}, merging #{hash} into #{y.phi}"
					end
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
	last_id
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

	public
	def compute_ssc
	    
	end


	private 
	def get_phi_name(p)
	    #p.
	end


	private
	def count_phi_nodes( bb )
	    nodes = bb.phi.length
	    bb.idominates.each do |child|
		if bb != child
		    nodes += count_phi_nodes( child )
		end
	    end
	    nodes
	end

	private
	def is_register?( operand )
	    return operand.include?("(")
	end

	private
	def is_true_or_false?( operand )
	    return (operand == "true" or
		    operand == "false")
	end

	private
	def is_constant?( operand )
	    return (is_true_or_false?( operand ) or
		    # reject all strings that contain something other than digits
		    ( not operand.scan(/[0-9]/).empty? and operand.scan(/[^0-9]/).empty? ) )
	end

	# turn moves to ssa variables into register operations
	private
	def convert_ssa_moves( bb )
	    puts "convert_ssa_moves for bb #{bb.id}: #{bb.instructions[0].opcode}" if $debug
	    bb.instructions.each_index do |i|
		ins = bb.instructions[i]

		# if it's a move to an ssa variable
		if ins.opcode == "move" and ins.operands[1].include?("$") and not ins.operands[1].include?("#")
		    puts "checking id #{ins.id}/#{ins.pre_ssa_id}: #{ins.opcode} #{ins.operands}" if $debug

		    # from a register
		    if is_register?( ins.operands[0] ) or is_constant?( ins.operands[0] )
#		    if ins.operands[1].include?("$") and not ins.operands[1].include?("#")

			puts "found register-to-SSA move at id #{ins.id}/#{ins.pre_ssa_id}: #{ins.opcode} #{ins.operands}" if $debug

			if true
			    # insert into symbol table
			    puts "id #{ins.id}/#{ins.pre_ssa_id}: Inserting (moves) @symbol_table[ #{ins.operands[1]} ] = #{ins.operands[0]}" if $debug
			    @symbol_table[ ins.operands[1] ] = ins.operands[0].to_s
			    
			    # might this be a jump target? if so, make it a nop instead of deleting.
			    if i == 0 and bb.instructions.length < 2 and false
				mh = "instr #{ins.id}: nop"
				bb.instructions[i].reset( mh.scan(/[^\s]+/) )
			    else
				# remove instruction
				puts "Deleting instruction #{bb.instructions[i].id} in de-ssa conversion" if $debug
				#bb.instructions.delete_at(i)
				# mark for deletion
				bb.instructions[i] = nil
			    end
			else
			    # it's a move to an ssa variable: convert to load
			    puts "id #{ins.id}/#{ins.pre_ssa_id}: Converting move to #{ins.operands[0]} to load from #{ins.operands[1]}" if $debug
			    ins.opcode = "add"
			    @symbol_table[ ins.operands[1] ] = "(" + ins.id.to_s + ")"
			    ins.operands[1] = "0"
			end


			# from another ssa variable 
		    elsif ins.operands[0].include?("$") and not ins.operands[0].include?("#")
			puts "found ssa-to-SSA move at id #{ins.id}/#{ins.pre_ssa_id}: #{ins.opcode} #{ins.operands}" if $debug
			# is a move to an ssa variable from another ssa variable
			# so convert to load
			puts "id #{ins.id}/#{ins.pre_ssa_id}: Converting move to #{ins.operands[1]} to load from #{ins.operands[0]}" if $debug
			ins.opcode = "add"
			@symbol_table[ ins.operands[1] ] = "(" + ins.id.to_s + ")"
			ins.operands[1] = "0"
		    # elsif ins.operands[1].include?("$") and not ins.operands[1].include?("#")
		    # 	puts "foo"
		    end
		end
	    end

	    # delete marked instructions
	    bb.instructions.delete(nil)

	    # recurse down dominator tree
	    bb.idominates.each do |y|
		puts "maybe convert_ssa_moves for bb #{y.id} from bb #{bb.id}: #{y.instructions[0].opcode}" if $debug
	    	convert_ssa_moves y if bb != y
	    end

	end


	# allocate temporary variable and insert reads
	private
	def insert_ssa_reads( bb )

	    # add temporary variable and read for every phi node
	    bb.phi.each do | key, value |
		# extract variable name. why is this not the key?
		variable_name = strip_address(value[0])

		# allocate space for variables
		# this is always a 4-byte integer or pointer
		@new_variable_index -= 4
		phi_variable_name = "__#{variable_name}$#{key}#" + @new_variable_index.to_s
		@phi_variables[key] = phi_variable_name

		# insert new instruction
		if true
		    #line = "instr #{@new_instruction_index}: move #{phi_variable_name} #{value[0]}"
		    line = "instr #{@new_instruction_index}: add #{phi_variable_name} 0"
		    inst = line.scan(/[^\s]+/)
		    bb.instructions.unshift Instruction.new( inst )
		    puts "In bb #{bb.id}, adding read from #{phi_variable_name} instruction #{inst}" if $debug

		    # insert this ssa variable's name and register number in symbol table
		    reg = '(' + @new_instruction_index.to_s + ')'
		    puts "Inserting (reads) @symbol_table[ #{value[0]} ] = #{reg}" if $debug
		    @symbol_table[ value[0] ] = reg

		    @new_instruction_index += 1
		else 
		    # insert this ssa variable's name and register number in symbol table
		    puts "Inserting (reads) @symbol_table[ #{value[0]} ] = #{phi_variable_name}" if $debug
		    @symbol_table[ value[0] ] = phi_variable_name
		end

		# todo more types?
		@ssa_temp_vars.push phi_variable_name + ":int"
	    end

	    # recurse down dominator tree
	    bb.idominates.each do |y|
	    	insert_ssa_reads y if bb != y
	    end

	end

	# add writes to temporary ssa variables
	private
	def insert_ssa_writes( bb )

	    # for each successor of this block
	    bb.sucs.each do | succ |
		# whiy don't we just store this?
		bb_source_id = which_pred(succ, bb)

	    	# for each phi node we are a source for, insert a variable 
	    	succ.phi.each do |key, value|
	    	    # extract variable name. why is this not the key?
	    	    variable_name = strip_address(value[0])
		    source_str = value[bb_source_id+1]

	    	    # is this block a source for this variable?
		    phi_variable_name = @phi_variables[key]
		    line = "instr #{@new_instruction_index}: move #{source_str} #{phi_variable_name}"
		    puts "In bb #{bb.id}, adding write to #{phi_variable_name} from #{source_str}: #{line}" if $debug
		    # split instruction string so we can instantiate the instruction
		    inst = line.scan(/[^\s]+/)

		    # prev = @symbol_table[ source_str ]
		    # puts "key: #{key} source_str: #{source_str} prev: #{prev} new: #{phi_variable_name}"

		    # if not @symbol_table.include?( source_str )
		    # 	@symbol_table[ source_str ] = phi_variable_name
		    # end
		    
		    # must make sure write comes before branches, but after normal code (that may do assignments)
		    last_inst = bb.instructions.pop
		    if last_inst.nil?
			bb.instructions.push Instruction.new( inst )
		    else
			case last_inst.opcode
			when "br", "blbc", "blbs", "ret"
			    bb.instructions.push Instruction.new( inst )
			    bb.instructions.push last_inst
			else
			    bb.instructions.push last_inst
			    bb.instructions.push Instruction.new( inst )
			end
		    end
		    @new_instruction_index += 1
	    	end
	    end

	    bb.idominates.each do |y|
	    	insert_ssa_writes y if bb != y
	    end

	end

	private
	def remove_phi_nodes( bb )

	    bb.phi = {}
	    
	    # recurse
    	    bb.idominates.each do |y|
	    	remove_phi_nodes y if bb != y
	    end
	end

	private
	def fix_branch_targets( bb )
	    bb.instructions.each do |i|
		# assign new id
		i.post_ssa_id = @new_instruction_index
		@new_instruction_index += 1

		# update new-to-old map
		puts "Adding mapping from old #{i.id} to new #{i.post_ssa_id}" if $debug
		@instruction_map[i.id] = i.post_ssa_id
	    end
	    
	    # recurse
    	    bb.idominates.each do |y|
	    	fix_branch_targets y if bb != y
	    end
	end

	private
	def renumber_instructions( bb )
	    bb.instructions.each do |i|

		# assign new id
		i.post_ssa_id = @new_instruction_index
		#puts "instruction #{i.id}/#{i.post_ssa_id}: #{i.codegen(self)}"
		@new_instruction_index += 1

		# update new-to-old map
		#puts "Adding mapping from old #{i.id} to new #{i.post_ssa_id}"
		@instruction_map[i.id] = i.post_ssa_id
		i.id = i.post_ssa_id

	    end
	    
	    # recurse
    	    bb.idominates.each do |y|
	    	renumber_instructions y if bb != y
	    end
	end

	private
	def insert_empty_block_noops( bb )
	    if bb.instructions.length == 0 and false
		mh = "instr #{@new_instruction_index}: nop"
		bb.instructions.push Instruction.new(mh.scan(/[^\s]+/))
		@new_instruction_index += 1
	    end
	    
	    # recurse
    	    bb.idominates.each do |y|
	    	insert_empty_block_noops y if bb != y
	    end
	end

	private
	def build_bb_map( bb )
	    @bb_map[ bb.id ] = bb
	    
	    # recurse
    	    bb.idominates.each do |y|
	    	build_bb_map y if bb != y
	    end
	end

	private
	def dump_bb_map
	    if $debug
		puts "Current BB map:"
		@bb_map.each_pair do |id,bb|
		    puts "   #{id}: #{bb.id}"
		end
	    end
	end

	private
	def renumber_operands( bb )
	    bb.instructions.each do |ins|
		case ins.opcode
		when "enter"
		    ins.operands[0] = -@new_variable_index
		when "br"
		    if @bb_map.has_key?( ins.operands[0] )
			puts "Found BB map entry for #{ ins.operands[0] }" if $debug
			ins.operands[0] = @bb_map[ ins.operands[0] ].id
		    else
			t = ins.operands[0].to_i
			new1 = @instruction_map[ t ]
			# if !@instruction_map.has_key?( t ) 
			#     new1 = bb.sucs[1].id
			# end
			new1 = @instruction_map[ t ]
			puts "Didn't find BB map entry for #{ ins.operands[0] }: #{ ins.opcode } should be near #{ @instruction_map[ ins.operands[0] ] }, using #{ new1 } instead" if $debug
			ins.operands[0] = new1
		    end
		when "call"
		    #ins.operands[0] = @instruction_map[ ins.operands[0] ]
		when "blbc", "blbs"
		    #puts "found #{ins.opcode} #{ins.id} #{ins.post_ssa_id} with #{ins.operands[0]}, #{ins.operands[1]}"
		    if ins.operands[0].is_a?(String)
			new0 = ins.operands[0]
		    else
			new0 = @instruction_map[ ins.operands[0] ]
		    end

		    if false
		    t = ins.operands[1].to_i
		    # while !@instruction_map.has_key?( t )
		    # 	t += 1
		    # end

		    # TODO: FIX Value numbering instruction deletion
		    new1 = @instruction_map[ t ]
		    if @bb_map.has_key?( t )
			puts "Found BB map entry for #{t}" if $debug
			new1 = @bb_map[ t ].id
		    else
			puts "Didn't find BB map entry for #{t} (post-ssa ins #{new1})" if $debug
		    end
		    if !@instruction_map.has_key?( t )
		    	new1 = bb.sucs[1].id
		    end
		    new1 = @instruction_map[ t ]
		    end

		    new1 = @bb_map[ ins.operands[1] ].id

		    #puts "#{ins.opcode}: [#{ins.operands[0]}] [#{ins.operands[1]}] [#{new0}] [#{new1}]"
		    ins.operands[0] = new0
		    ins.operands[1] = new1
		else
		    puts "id #{ins.id}/#{ins.pre_ssa_id} before: #{ins.opcode}: [#{ins.operands[0]}] [#{ins.operands[1]}] [#{ins.operands[2]}]" if $debug
		    ins.operands.each_index do |i|
		    	# might we need to convert it?
		    	if ins.operands[i].is_a?(String)
		    	    s = ins.operands[i]
		    	    # is it a register operand?
		    	    if s[0] == "("
		    		reg = ins.operands[i].sub('(','').sub(')','').to_i
		    		new_reg = @instruction_map[ reg ]
				if ins.opcode == "blbc"
				    puts "id #{ins.id}/#{ins.pre_ssa_id}: #{ins.opcode}: [#{ins.operands[0]}] [#{ins.operands[1]}] [#{ins.operands[2]}] replacing #{reg} with #{new_reg}" if $debug
				end
		    		ins.operands[i] = "(#{ new_reg })"

			    elsif ins.operands[i][-1] == "$"
				# is it an ssa initial value?
		    	    	ins.operands[i] = @symbol_table[ ins.operands[i] ]

		    	    elsif ins.operands[i].include?("$")
				# is it an ssa use?
				#puts "id #{ins.id} ssa use: #{ins.opcode}: [#{ins.operands[0]}] [#{ins.operands[1]}] [#{ins.operands[2]}]" if $debug

		    	    	# is it an ssa temporary?
		    	    	if ins.operands[i].include?("#")
		    	    	    # leave it alone
		    	    	else    # ssa use, so replace with def register
		    	    	    #puts "id #{ins.id}: processing ssa use #{ins.opcode} #{ins.operands.join(' ')} with operand #{ins.operands[i]}" if $debug
		    	    	    var = ins.operands[i]
				    #puts "Checking for #{ins.operands[i]} = #{@symbol_table[ ins.operands[i] ]}" if $debug
		    	    	    old_reg = @symbol_table[ var ]
				    new_reg = old_reg
				    done = false
				    while not done
					puts "id #{ins.id}/#{ins.pre_ssa_id} ssa use walk: #{ins.opcode}: [#{ins.operands[0]}] [#{ins.operands[1]}] [#{ins.operands[2]}] at #{new_reg}" if $debug
					#puts "at #{new_reg}" if $debug
					if new_reg.is_a?(String) 
					    #puts "at #{new_reg} string"
					    if new_reg.include?("(")
						new_reg_num = new_reg.sub('(','').sub(')','').to_i
						# check if this was a move into an ssa variable: replace it with a load
						if ins.opcode == "move" and i == 1 and new_reg_num = ins.id
						    puts "id #{ins.id}/#{ins.pre_ssa_id} move problem: #{ins.opcode}: [#{ins.operands[0]}] [#{ins.operands[1]}] [#{ins.operands[2]}] at #{new_reg}" if $debug
						    ins.opcode = "load"
						    new_reg = ""
						else
						    new_reg = "(" + @instruction_map[ new_reg.sub('(','').sub(')','').to_i ].to_s + ")"
						end
						done = true
					    elsif new_reg.is_a?(String) and new_reg.include?("$") and new_reg.include?("#")
						done = true
					    elsif new_reg.is_a?(String) and new_reg.include?("$") and not new_reg.include?("#")
						hmm = @symbol_table[ new_reg ]
						#puts "at #{new_reg} next #{hmm}"
						new_reg = hmm
					    else
						done = true
					    end
					else
					    done = true
					end
				    end
		    	    	    #puts "id #{ins.id}: processing ssa use #{ins.opcode} #{ins.operands.join(' ')} with var #{var} old_reg #{old_reg} new_reg #{new_reg}"
		    	    	    ins.operands[i] = new_reg
		    	    	end
		    	    end

		    	else
		    	    puts "id #{ins.id}: What do I do with #{ins.opcode} #{ins.operands[i]}" if $debug
		    	end
		    end
		    puts "id #{ins.id}/#{ins.pre_ssa_id} after: #{ins.opcode}: [#{ins.operands[0]}] [#{ins.operands[1]}] [#{ins.operands[2]}]" if $debug

		end
	    end
	    
	    # recurse
    	    bb.idominates.each do |y|
	    	renumber_operands y if bb != y
	    end
	end

	private
	def print_symbol_table
    	    # dump symbol table
	    if $debug
		puts "Current symbol table: {"
		@symbol_table.each do |key, value|
		    puts "      symbol #{key} => #{value}"
		end
		puts "   }"
	    end
	end

	public
	def convert_from_ssa( initial_index )

	    # we use the naive ssa tranlation approach, followed by 

	    # for every phi node, we insert and write to a new
	    # variable in the phi node source blocks. then we replace
	    # the phi node with a read of the variable into a
	    # register. 

	    # to make this work we need to:
	    # - allocate space for the phi-replacement variables
	    # - add write instructions for the phi-replacement variables
	    # - add read instructions for the phi-replacement variables
	    # - replace ssa writes/moves with register uses
	    # - fix up ssa uses to use register results of reads
	    # - renumber all instructions

	    # initialize symbol table with initial variables
	    initial_vars = @inst_str
	    initial_vars.shift(2)
	    initial_vars.each do |v|
		# insert ssa initial mapping
		@symbol_table[ strip_address(v) + '$' ] = v.split(':')[0]
		@symbol_table[ strip_address(v) + '$0' ] = v.split(':')[0]
	    end
	    print_symbol_table

	    # add noops if we have empty blocks for looks
	    insert_empty_block_noops( @doms[0] )

	    # turn phi nodes into variable reads/writes
	    puts "Inserting SSA reads...." if $debug
	    insert_ssa_reads(@doms[0])

	    puts "Inserting SSA writes...." if $debug
	    insert_ssa_writes(@doms[0])
	    print_symbol_table
	    
	    # turn ssa defs into registers
	    puts "Converting SSA moves...." if $debug
	    convert_ssa_moves(@doms[0])
	    print_symbol_table

	    # bbs.each do |bb|
	    # 	bb.instructions.each do |ins|
	    # 	    puts "hi: #{ins.id}: #{ins.opcode}"
	    # 	end
	    # end


	    # renumber instructions
	    puts "Renumbering instructions...." if $debug
	    @new_instruction_index = initial_index
	    renumber_instructions(@doms[0])
	    print_symbol_table

	    # dump instruction mapping
	    if false
		@instruction_map.each do |key, value|
		    puts "instruction #{key} => #{value}"
		end
	    end

	    #dump_bb_map

	    # replace ssa variable uses with registers from variable reads
	    # this fixes branch targets too
	    renumber_operands(@doms[0])

	    #dump_bb_map

	    #puts @ssa_temp_vars

	    # remove phi nodes
	    remove_phi_nodes(@doms[0])

	    # update function entry point
	    mh = "method #{name}@#{@doms[0].id} #{initial_vars.join(' ')} #{@ssa_temp_vars.join(' ')}"
	    @method_header.reset( mh.scan(/[^\s]+/) )
	    #puts @method_header

	    return @new_instruction_index, @doms[0].id
	end

	public
	def fix_up_calls( functions_info, orig_functions_index )
	    bbs.each do |bb|
		bb.instructions.each do |i|
		    if i.opcode == "call"
			new_entry = functions_info[ orig_functions_index[ i.operands[0] ] ]
			#puts "old entry #{i.operands[0]} new entry #{new_entry}"
			i.operands[0] = new_entry
		    end
		end
	    end
	end

	private
	def write_il_helper(file, bb)
	    bb.instructions.each do |i|
		file.puts( i.codegen( self ))
	    end
	    bb.idominates.each do |y|
	    	write_il_helper( file, y ) if bb != y
	    end
	end

	public
	def write_il(file)
	    write_il_helper file, @doms[0]
	end

	######################################### GCSE ###########################################

	    private
	def is_redundant_phi(phi_f, dest, bb)
		all_equal = true
		last_vn = @vn[phi_f[1]]
		for i in 2...phi_f.length
			if (last_vn == nil) || (@vn[phi_f[i]] == nil)
				all_equal = false
			else
				if last_vn != @vn[phi_f[i]]
					all_equal = false
				end
			end
			last_vn = @vn[phi_f[i]]
		end

		phi = phi_f.dup
		phi.shift
		phi.uniq!

		redundant = false
		bb.phi.each_pair do |dest2, phi_f2|
			if dest2 != dest
				phi2 = phi_f2.dup
				phi2.shift
				phi2.uniq!
				found = []
				for i in 0...phi.length
					found.push false
					for j in 0...phi2.length
						if phi[i] == phi2[j]
							found[i] = true
						end
					end
				end

				if phi.length == phi2.length
					different_phis = false
					found.each do |e|
						if e == false
							different_phis = true
						end
					end
					if !different_phis
						#p phi_f
						#p "Redundant with:"
						#p phi_f2
						redundant = true
					end
				end
			end
		end
		all_equal || redundant
	end

	#Dominator-based value number main procedure
	private
	def dvnt(b, scoped_hash)
		hash_expr_vn = scoped_hash.dup
		to_be_deleted = []
		b.phi.each_key do |phi_key|
			if is_redundant_phi(b.phi[phi_key], phi_key, b)
				@vn[b.phi[phi_key][0]] = hash_expr_vn[b.phi[phi_key]]
				to_be_deleted.push phi_key
			else
				@vn[b.phi[phi_key][0]] = b.phi[phi_key][0]
				new_entry = { b.phi[phi_key] => b.phi[phi_key][0] }
				hash_expr_vn.merge! new_entry
			end
		end
		to_be_deleted.each do |x|
			@n_expr_eliminated += 1
			b.phi.delete x
		end
		to_be_deleted = []
		set_assignments b
		b.instructions.each do |inst|
			if !inst.expr.empty?
				for i in 2...inst.expr.length
					if @vn[inst.expr[i]] != nil
						inst.expr[i] = @vn[inst.expr[i]] 
						inst.operands[i-2] = @vn[inst.operands[i-2]]
					end
				end
				if inst.expr.length == 4
					tmp = hash_expr_vn[[inst.expr[1], inst.expr[2], inst.expr[3]]]
				else
					tmp = hash_expr_vn[[inst.expr[1], inst.expr[2]]]
				end
				if tmp != nil
					@vn[inst.expr[0]] = tmp
					to_be_deleted.push b.instructions.find_index(inst)
				else
					@vn[inst.expr[0]] = inst.expr[0]
					new_entry = {}
					if inst.expr.length == 4
						new_entry = { [inst.expr[1], inst.expr[2], inst.expr[3]] => inst.expr[0] }
					else
						new_entry = { [inst.expr[1], inst.expr[2]] => inst.expr[0] }
					end
					hash_expr_vn.merge! new_entry
				end
			end
		end
		this_id = b.id
	    if to_be_deleted.size > 0
		puts "VN: Visiting BB #{this_id} with #{b.instructions.size} instructions to_be_deleted #{ to_be_deleted.size }" if $debug
	    end
		to_be_deleted.each do |i|
		#puts "VN: Preparing deletion for instruction #{ b.instructions[i].id } index #{i} bb id #{ b.id } len #{ b.instructions.size }"
			@bbs.each do |bb|
				bb.instructions.each_index do |j|
					if bb.instructions[j] != nil
						case bb.instructions[j].opcode
						when "blbc", "blbs"
							if bb.instructions[j].inst_str[3] == b.instructions[i].expr[0]
								dest = @vn[b.instructions[i].expr[0]].scan(/[\d]+/)
								bb.instructions[j].operands[0] = Integer(dest[0])
								bb.instructions[j].inst_str[3] = @vn[b.instructions[i].expr[0]]
							end
# 						when "br"
# #						    puts "At #{ bb.instructions[j].id }: #{ bb.instructions[j].opcode }"
# 							if bb.instructions[j].inst_str[2] == b.instructions[i].expr[0]
# 								dest = @vn[b.instructions[i].expr[0]].scan(/[\d]+/)
# 								bb.instructions[j].operands[0] = Integer(dest[0])
# 								bb.instructions[j].inst_str[2] = @vn[b.instructions[i].expr[0]]
# 							end
						when "istype", "checktype", "lddynamic", "isnull", "load", "checknull", "write", "param"
							if bb.instructions[j].inst_str[3] == b.instructions[i].expr[0]
								bb.instructions[j].operands[0] = @vn[b.instructions[i].expr[0]]
								bb.instructions[j].inst_str[3] = @vn[b.instructions[i].expr[0]]
							end
						when "store", "move", "checkbounds"
							if bb.instructions[j].inst_str[3] == b.instructions[i].expr[0]
								bb.instructions[j].operands[0] = @vn[b.instructions[i].expr[0]]
								bb.instructions[j].inst_str[3] = @vn[b.instructions[i].expr[0]]
							end
							if bb.instructions[j].inst_str[4] == b.instructions[i].expr[0]
								bb.instructions[j].operands[1] = @vn[b.instructions[i].expr[0]]
								bb.instructions[j].inst_str[4] = @vn[b.instructions[i].expr[0]]
							end
						end
					end
				end
			end
			@n_expr_eliminated += 1
			b.instructions[i] = nil
		end
	    #puts "At #{ b.id }, deleting"
		b.instructions.delete(nil)
	    if to_be_deleted.size > 0
		puts "VN: Done visiting BB #{this_id} with #{b.instructions.size} " if $debug
	    end
	    #puts "BB #{ this_id } instructions"
		b.sucs.each do |succ|
			adjust_phis(succ, b)
		end
		b.idominates.each { |child| dvnt(child, hash_expr_vn) }
	end

	private
	def adjust_phis(bb, pred)
		j = which_pred(bb, pred)
		bb.phi.each_value do |right|
			right[j+1] = @vn[right[j+1]] if @vn[right[j+1]] != nil
		end
	end


	private
	def set_assignments(bb)
		bb.instructions.each do |inst|
			case inst.opcode
			#Treat "checkbounds" because I don't know if it assigns to anything
			when "sub", "add", "mul", "div", "mod", "cmpeq", "cmple", "cmplt"
				new_expr = ["("+inst.id.to_s+")", inst.opcode, inst.operands[0], inst.operands[1]]
				inst.expr = new_expr
			else
				inst.expr = []
			end
		end
	end

	####################################### SCP ######################################################

	private
	def is_const_scp(v)
		return_value = true
		return_value = false if (v =~ /[\$\(\)\[\]]/) || ((v =~ /[a-zA-Z]/) && !(v =~ /[\$]/))
		return_value = true if (v =~ /offset/) && (v =~ /[\?]/)
		return_value
	end

	public
	def scp
		w = []
		@bbs.each do |bb|
			bb.phi.each_key do |key|
				w.push bb.phi[key]
			end
			bb.instructions.each_index do |i|
				w.push bb.instructions[i]
			end
		end

		while !w.empty?
			s = w.shift
			#Is phi?
			if s.kind_of?(Array)
				all_const = true
				which_const = nil
				for i in 1...s.length
					if !is_const_scp(s[i])
						all_const = false
					else
						if which_const == nil
							which_const = s[i]
						else
							all_const = false if which_const != s[i]
						end
					end
				end
				if all_const
					s[1] = which_const.to_s
					s.slice!(0..1)
				end
			end

			#Is constant phi?
			if s.kind_of?(Array) && (s.length == 2) && (is_const_scp(s[1]))
				@n_cprop += 1
				@bbs.each do |bb|
					bb.phi.each_key do |key|
						if bb.phi[key] == s
							bb.phi.delete key
						else
							for i in 1...bb.phi[key].length
								bb.phi[key][i] = s[1] if bb.phi[key][i] == s[0]
							end
							w.push bb.phi[key]
						end
					end
					bb.instructions.each_index do |i|
						changed = replace_by(bb.instructions[i], s[0], s[1])
						w.push bb.instructions[i] if changed
					end
				end
			end

			#Is constant non-phi?
			if !s.kind_of?(Array) && is_const_inst(s)
				@n_cprop += 1
				case s.opcode
				when "move"
					op1 = nil
					op0 = nil
					if s.operands[1].instance_of? Fixnum
						op1 = s.operands[1]
					else
						op1 = s.operands[1].dup
					end
					if s.operands[0].instance_of? Fixnum
						op0 = s.operands[0]
					else
						op0 = s.operands[0].dup
					end
					@bbs.each do |bb|
						to_be_deleted = []
						bb.instructions.each_index do |i|
							if bb.instructions[i] == s
								to_be_deleted.push i
							else
								changed = replace_by(bb.instructions[i], op1, op0)
								w.push bb.instructions[i]
							end
						end
						to_be_deleted.each do |i|
							bb.preds.each do |pred|
								last = pred.instructions.last
								case last.opcode
								when "call", "br"
									if last.operands[0] == bb.instructions[i].id
										last.operands[0] += 1
										last.inst_str[3] = "[" + last.operands[0].to_s + "]"
									end
								when "blbc", "blbs"
									if last.operands[1] == bb.instructions[i].id
										last.operands[1] += 1
										last.inst_str[4] = "[" + last.operands[1].to_s + "]"
									end
								end
							end
				puts "Deleting instruction #{bb.instructions[i].id} in simple constant propagation (1)" if $debug
							bb.instructions.delete_at i
						end
						bb.phi.each_key do |key|
							for i in 1...bb.phi[key].length
								bb.phi[key][i] = op0.to_s if bb.phi[key][i] == op1
								w.push bb.phi[key]
							end
						end
					end
				else
					if (s.opcode != "blbc") && (s.opcode != "blbs")
						target = "(" + s.id.to_s + ")"
						result = eval_expr s
					    puts "scp id #{s.id}/#{s.pre_ssa_id}: #{s.opcode} target #{target} result #{result}" if $debug
						@bbs.each do |bb|
							to_be_deleted = []
							bb.instructions.each_index do |i|
								if bb.instructions[i] == s
									to_be_deleted.push i
								else
									changed = replace_by(bb.instructions[i], target, result)
									w.push bb.instructions[i]
								end
							end
							to_be_deleted.each do |i|
								bb.preds.each do |pred|
					# unnecessary with new BB-map-based branch target resolution
					if false
									last = pred.instructions.last
									case last.opcode
									when "call", "br"
										if last.operands[0] == bb.instructions[i].id
											last.operands[0] += 1
											last.inst_str[3] = "[" + last.operands[0].to_s + "]"
										end
									when "blbc", "blbs"
										if last.operands[1] == bb.instructions[i].id
											last.operands[1] += 1
											last.inst_str[4] = "[" + last.operands[1].to_s + "]"
										end
								end
					end
							end
				    puts "Deleting instruction #{bb.instructions[i].id} in simple constant propagation (2)" if $debug
							bb.instructions.delete_at i
							end
						end
					end
				end
			end
		end
	end

	private
	def replace_by(inst, from, to)
		changed = false
		if ((inst.opcode == "blbc") || (inst.opcode == "blbs")) && (inst.bl_operand == from)
		    puts "scp id #{inst.id}/#{inst.pre_ssa_id}: #{inst.opcode} from #{from.to_s} to #{to.to_s}" if $debug
			inst.bl_operand = to.to_s
			inst.operands[0] = to.to_s
			inst.inst_str[3] = to.to_s
			changed = true
		end
		case inst.opcode
		when "sub", "add", "mul", "div", "mod", "cmpeq", "cmple", "cmplt", "stdynamic"
			if inst.operands[0] == from
				inst.operands[0] = to
				inst.inst_str[3] = to.to_s
				changed = true
			end
			if inst.operands[1] == from
				inst.operands[1] = to
				inst.inst_str[4] = to.to_s
				changed = true
			end
		when "store", "move", "istype", "checkbounds", "checktype", "isnull", "checknull", "write", "param", "load", "lddynamic"
			if inst.operands[0] == from
				inst.operands[0] = to
				inst.inst_str[3] = to.to_s
				changed = true
			end
		end
		changed
	end

	private
	def is_const_inst(s)
		ret_val = false
		case s.opcode
		when "sub", "add", "mul", "div", "mod", "cmpeq", "cmple", "cmplt"
			ret_val = true if is_const_scp(s.operands[0]) && is_const_scp(s.operands[1])
		when "move"
			ret_val = true if is_const_scp(s.operands[0])
		when "blbc", "blbs"
			ret_val = true if is_const_scp(s.bl_operand)
		end
		ret_val
	end

	private
	def strip_offset(s)
		if (s =~ /[o][f][f][s][e][t]/) && !(s =~ /[\?]/)
			s.slice!(/[^#]+#/)
			p s
		end
		s
	end

	private
	def eval_expr(s)
		case s.opcode
		when "sub"
			result = Integer(strip_offset(s.operands[0])) - Integer(strip_offset(s.operands[1]))
		when "add"
			result = Integer(strip_offset(s.operands[0])) + Integer(strip_offset(s.operands[1]))
		when "mul"
			result = Integer(strip_offset(s.operands[0])) * Integer(strip_offset(s.operands[1]))
		when "div"
			result = Integer(strip_offset(s.operands[0])) / Integer(strip_offset(s.operands[1]))
		when "mod"
			result = Integer(strip_offset(s.operands[0])) % Integer(strip_offset(s.operands[1]))
		when "cmpeq"
			result = Integer(strip_offset(s.operands[0])) == Integer(strip_offset(s.operands[1]))
		when "cmple"
			result = Integer(strip_offset(s.operands[0])) <= Integer(strip_offset(s.operands[1]))
		when "cmplt"
			result = Integer(strip_offset(s.operands[0])) < Integer(strip_offset(s.operands[1]))
		end
	end
    end



