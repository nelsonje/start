require_relative 'instruction'
require_relative 'function'
require_relative 'basic_block'

class Program
  def initialize
    @instructions = [nil]
      @types = ["int", "bool", "List", "Integer", "dynamic" ]
    @header = []
    
    # maps name of function to index of first instruction
    @functions_info = {}
    @orig_functions_index = {}
    
    # maps name of function to function object
    @functions = {}

    #TODO
    #Jacob, are you sure we need this?
    @doms = []

    @last_inst_id = 0
    @last_counter = 0
    
  end

	public
	def is_recursive(f_name)
		start_addr = @functions_info[f_name]
		result = false
		start_idx = 0
		@instructions.each_index do |i|
			if @instructions[i].id == start_addr
				if @instructions[i].opcode == "entrypc"
					start_idx = i + 1
				else if @instructions[i].opcode == "enter"
					start_idx = i
				else
					puts "\n\nBug in is_recursive\n\n"
					5/0
				end
			end
		end
		start_idx += 1
		while (start_idx < @instructions.length) && (@instructions[start_idx].opcode != "enter") && (@instructions[start_idx].opcode != "entrypc")
			result = true if (@instructions[start_idx].opcode == "call") && (@instructions[start_idx].operands[0] == start_addr)
		end
		result
	end

	private
	def get_params_locals f
		header = f.method_header
		params = []
		locals = []
		for i in 2...header.inst_str.length
			new_str =  header.inst_str[i]
			# new_str = (new_str.split(":"))[0]
			if new_str =~ "#-"
				locals.push new_str.dup
			else
				params.push new_str.dup
			end
		end
		[params, locals]
	end

	public
	def inline(inst_idx, f1, f2)
		if @instructions[inst_idx-1].opcode != "count"
			puts "\n\n\nUninstrumented call???\n\n\n"
			5/0
		end
		# Delete the counter -- not needed anymore
		@instructions.delete_at (inst_idx - 1)
		inst_idx -= 1

		# Get the parameters and the local variables of the
		# functions that will be inlined here
		params_locals = get_params_locals(f2)
		params = params_locals[0]
		locals = params_locals[1]

		map_new_locals = {}
		# For each parameter of the function that will be inlined,
		# create a new local variable in this function
		params.each do |param|
			f1.new_variable_index -= 4
			new_var_name = "andre_var#" + f1.new_variable_index.to_s
			map_new_locals[param] = new_var_name.dup + ":" + param.split(":")[1]
		end
		# For each local variable of the function that will be inlined,
		# create a new local variable in this function
		locals.each do |local|
			f1.new_variable_index -= 4
			new_var_name = "andre_var#" + f1.new_variable_index.to_s
			map_new_locals[local] = new_var_name.dup + ":" + local.split(":")[1]
		end

		# Replace "param" by "moves"

		i = inst_idx
		j = params.length - 1
		while j >= 0
			i -= 1
			while @instructions[i].opcode != "param"
				i -= 1
			end
			# "i" now points to the next "param" instruction bottom-up

			# Replace this "param" instruction by a "move"
			new_move_str = "instr #{@instructions[i].id}: move #{@instructions[i].operands[0]} #{map_new_locals[params[j]].split(":")[0]}"
			@instructions[i].reset( new_move_str.scan(/[^\s]+/) )

			j -= 1
		end

		# Fix this function's "method" instruction to include the new locals
		new_method = f1.method_header.inst_str.dup
		new_vars = []
		params.each do |param|
			new_vars.push map_new_locals[param]
		end
		locals.each do |local|
			new_vars.push map_new_locals[local]
		end
		new_vars.each do |var|
			new_method.push var
		end
		f1.method_header.reset( new_method )

		# Fix this function's "enter" and "return" instructions to allocate/free more space
		start_idx = 0
		start_addr = @functions_info[f1.name]
		@instructions.each_index do |i|
			if @instructions[i].id == start_addr
				if @instructions[i].opcode == "entrypc"
					start_idx = i + 1
				else
					start_idx = i
				end
			end
		end

		# start_idx must point to an "enter" instruction here
		@instructions[start_idx].inst_str[3] = @instructions[start_idx].operands[0] + 4*(params.length + locals.length)
		@instructions[start_idx].reset( @instructions[start_idx].inst_str.dup )

		start_idx += 1
		while (start_idx < @instructions.length) && (@instructions[start_idx].opcode != "enter") && (@instructions[start_idx].opcode != "entrypc")
			if @instructions[start_idx].opcode == "ret"
				@instructions[start_idx].inst_str[3] = @instructions[start_idx].operands[0] + 4*(params.length + locals.length)
				@instructions[start_idx].reset( @instructions[start_idx].inst_str.dup )
			end

			start_idx += 1
		end

		# "inst_idx" should point to the call that will be inlined
		@instructions.delete_at inst_idx

		# Get the start and end index of the function that will be inlined
		start_idx_f2 = 0
		start_addr = @functions_info[f2.name]
		@instructions.each_index do |i|
			start_idx_f2 = i if @instructions[i].id == start_addr
		end
		start_idx_f2 += 1
		# Handle "entrypc" case
		start_idx_f2 += 1 if @instructions[start_idx_f2].opcode == "enter"

		i = start_idx_f2
		while (i < @instructions.length) && (@instructions[i].opcode != "enter") && (@instructions[i].opcode != "entrypc")
			i += 1
		end
		# Last "ret" is not necessary
		end_idx_f2 = i - 2

		# Copy the instructions that will be inlined with the new id
		# Create a map between old and new ids
		tmp_insts = []
		id_map = {}
		i = start_idx
		while i <= end_idx_f2
			new_str = @instructions[i].inst_str.dup
			old_id = new_str[1].chomp(':')
			@last_inst_id += 1
			new_str[1] = @last_inst_id.to_s + ":"
			id_map[old_id] = @last_inst_id.to_s
			new_inst = Instruction.new(new_str)
			tmp_insts.push new_inst
			i += 1
		end

		# Fix regs, jumps and everything related to ids
		# "ret"s are replaced by branches
		tmp_insts.each do |inst|
			case inst.opcode
			when "call", "br"
				new_dest = id_map[inst.operand[0].to_s]
				if new_dest != nil
					new_str = inst.inst_str.dup
					new_str[3] = "[" + new_dest + "]"
					inst.reset( new_str )
				end
			when "blbc", "blbs"
				new_dest = id_map[inst.operand[1].to_s]
				if new_dest != nil
					new_str = inst.inst_str.dup
					new_str[4] = "[" + new_dest + "]"
					inst.reset( new_str )
				end
			when "ret"
				new_str = inst.inst_str.dup
				new_str[2] = "br"
				new_str[3] = "[" + @instructions[inst_idx].id.to_s + "]"
				inst.reset( new_str )
			when "sub", "add", "mul", "div", "mod", "cmpeq", "cmple", "cmplt", "store", "move", "checkbounds", "stdynamic"
				new_str = inst.inst_str.dup
				if new_str[3] =~ /\(/
					reg = new_str[3].scan(/[\d]+/)
					new_reg = id_map[reg]
					if new_reg != nil
						new_str[3] = "(" + new_reg + ")"
					end
				end
				if new_str[4] =~ /\(/
					reg = new_str[4].scan(/[\d]+/)
					new_reg = id_map[reg]
					if new_reg != nil
						new_str[4] = "(" + new_reg + ")"
					end
				end
				inst.reset( new_str )
			when "istype", "checktype", "lddynamic", "isnull", "load", "new", "newlist", "checknull", "write", "param"
				new_str = inst.inst_str.dup
				if new_str[3] =~ /\(/
					reg = new_str[3].scan(/[\d]+/)
					new_reg = id_map[reg]
					if new_reg != nil
						new_str[3] = "(" + new_reg + ")"
						inst.reset( new_str )
					end
				end
			end
		end


		# Fix vars and params

		params2 = params.dup
		locals2 = locals.dup
		map_new_locals2 = {}

		params2.each_index do |i|
			map_result = map_new_locals[params2[i]].split(":")[0]
			params2[i] = params2[i].split(":")[0]
			map_new_locals2[params2[i]] = map_result
		end
		locals2.each_index do |i|
			map_result = map_new_locals[locals2[i]].split(":")[0]
			locals2[i] = locals2[i].split(":")[0]
			map_new_locals2[locals2[i]] = map_result
		end

		tmp_insts.each do |inst|
			case inst.opcode
			when "blbc", "blbs", "istype", "checktype", "lddynamic", "isnull", "load", "newlist", "checknull", "write", "param"
				new_var = map_new_locals2[inst.inst_str[3]]
				if new_var != nil
					new_str = inst.inst_str.dup
					new_str[3] = new_var.dup
					inst.reset( new_str )
				end
			when "sub", "add", "mul", "div", "mod", "cmpeq", "cmple", "cmplt", "store", "move", "checkbounds", "stdynamic"
				new_var = map_new_locals2[inst.inst_str[3]]
				new_str = inst.inst_str.dup
				if new_var != nil
					new_str[3] = new_var.dup
				end
				new_var = map_new_locals2[inst.inst_str[4]]
				if new_var != nil
					new_str[4] = new_var.dup
				end
				inst.reset( new_str )


			end
		end

		# Inline everything
		tmp_insts.each do |inst|
			@instructions.insert(inst_idx, inst)
			inst_idx += 1
		end

	end

	public
	def instrument
  		@functions.each do |name, f|
			ret = f.instrument(@last_inst_id, @last_counter)
			@last_inst_id = ret[0]
			@last_counter = ret[1]
		end
	end

  public
  def to_ssa
  	@functions.each do |name, f|
		@last_inst_id = f.to_ssa(@last_inst_id)
	end
  end

  public
  def capture_bb_map
  	@functions.each do |name, f|
	  f.build_bb_map
	end
  end

  public
  def gcse
  	@functions.each do |name, f|
		f.gcse
	end
  end

  public
  def scp
  	@functions.each do |name, f|
		f.scp
	end
  end

  public
  def dump_info(filename)
    @functions.each do |name, f|
      this_filename = filename + "-" + f.name + "-info.txt"
      file = File.new(this_filename, "w")
      file.print("Function " + f.name + "\nEntry index: " + @functions_info[f.name].to_s + "\n\n\n")
      f.bbs.each do |bb|
        bb.instructions.each do |i|
          text = ""
          i.inst_str.each {|str| text << str << " "}
          file.puts text
        end
        file.print("Predecessors: ")
        if bb.preds.empty?
          file.print "none"
        else
          bb.preds.each_index do |index|
            if index != 0
              file.print ", "
            end
            file.print bb.preds[index].id.to_s
          end
        end
        file.print("\nSuccessors: ")
        if bb.sucs.empty?
          file.print "none"
        else
          bb.sucs.each_index do |index|
            if index != 0
              file.print ", "
            end
            file.print bb.sucs[index].id.to_s
          end
        end
	if bb.idom
	    idom = bb.idom.id.to_s
	else
	    idom = "none"
	end
        file.print("\nImmediate dominator: " + idom + "\n\n\n")
      end
      file.close
    end
  end

  public
  def report_gen_scp
  	@functions.each do |name, f|
		puts "Function: " + name
		puts "Number of constants propagated: " + f.n_cprop.to_s
	end
  end

  public
  def report_gen_gcse
  	@functions.each do |name, f|
		puts "Function: " + name
		puts "Number of expressions eliminated: " + f.n_expr_eliminated.to_s
	end
  end

  public
  def dump_cfgs(filename)
    index = 0
    @functions.each do |name, f|
      this_filename = filename + "-" + f.name + "-cfg.dot"
      file = File.new( this_filename, "w")
      index += 1
      file.puts "digraph cfg {"
      file.puts "node [shape=record];"
      file.puts "splines=true;"
      file.puts "entry [label=\"Entry\"];"
      for i in 0...f.bbs.length
	  if f.bbs[i].id != -1
        file.print("n" + i.to_s + " [label=\"{BB " + f.bbs[i].id.to_s + "/" + f.bbs[i].pre_ssa_id.to_s + " (idom: ")
	if f.bbs[i].idom  == nil
		file.print("none")
	else
		file.print(f.bbs[i].idom.id.to_s)
	end
	file.print(")|")
	file.print("DF:")
	file.print(" empty") if f.bbs[i].df.empty?
	f.bbs[i].df.each {|bb| file.print(" " + bb.id.to_s)}
	file.print("|")
	      file.print("count: #{ f.bbs[i].count }|")

	phi_counter = 0
	f.bbs[i].phi.each do |var, options|
		if true
		    #puts "Adding phi node for #{var} with options #{options}"
		end
		phi_counter += 1
		text = ""
		# text << var.to_s << " = phi("
		# options.each_index do |i|
		# 	text << options[i]
		# 	if i != options.length - 1
		# 		text << ", "
		# 	end
		# end

		  # print phi nodes like the rest of the world
		text << var.to_s << " = " << options[0] << " = phi("
		options.each_index do |i|
		      if i > 0 
			  text << options[i]
			  if i != options.length - 1
			      text << ", "
			  end
		      end
		end

		text << ")"
		file.print("<phi-" + var.to_s + "> " + text)
		if (phi_counter == f.bbs[i].phi.length) && (f.bbs[i].instructions.length == 0)
			file.print("}\"];\n")
		else
			file.print("|")
		end
	end

        for inst in 0...f.bbs[i].instructions.length
	  #f.bbs[i].instructions[inst].fix_inst_string_ssa
          text = ""
	    #f.bbs[i].instructions[inst].inst_str.each {|str| text << " " << str}
	    #f.bbs[i].instructions[inst].inst_str.each {|str| text << " " << str.to_s}
	    text << f.bbs[i].instructions[inst].codegen(self)
          file.print("<c" + inst.to_s + "> " + text)
	    #puts "inst is #{inst}, len is #{f.bbs[i].instructions.length-1}: #{f.bbs[i].instructions[inst].inst_str} #{0 == inst and inst == (f.bbs[i].instructions.length - 1)}"
	    #file.print( f.bbs[i].instructions[inst].opcode )
          if inst == (f.bbs[i].instructions.length - 1)
            file.print("}\"];\n")
          else
            file.print("|")
          end
        end

	  else
	      puts "Warning: empty block"
	  end
      end

      file.puts("entry -> n0;") if !(f.bbs.empty?)

      for i in 0...f.bbs.length
#        file.print("n" + i.to_s )
#        file.print(" -> n" + f.bbs.find_index(f.bbs[i].idom).to_s + " [color=red,style=dashed];\n")
        f.bbs[i].sucs.each do |s|
          file.print("n" + i.to_s )
          file.print(" -> n" + (f.bbs.find_index(s)).to_s + ";\n")
        end
      end
      file.print "}\n\n"
      file.close
    end
  end

  private
  def read_instruction(line)
    inst = line.scan(/[^\s]+/)
    #if line is empty, return
    i = Instruction.new(inst)
    if inst[0] == "instr"
      @instructions.push(i)
      @last_inst_id = Integer(inst[1].chomp(':'))
    elsif inst[0] == "type"
	@types.push(i)
	@header.push(i)
    else
	# any non-blank lines are header instructions
	if ! i.inst_str.empty?
	    @header.push(i)
	end
    end
  end

  public
  def read_program(filename)
    file = File.new(filename, "r")
    # if file doesn't exist, print & exit
    file.each_line { |line| read_instruction(line) }
    file.close
    set_functions_info
  end

  private
  def set_functions_info
    for i in @header
      if i.opcode == "method"
        @functions_info[i.operands[0]] = i.operands[1]
        @orig_functions_index[i.operands[1]] = i.operands[0]
	  # get offset of last operand
	  initial_offset = 0
	  if i.inst_str.size > 2
	      initial_offset = i.inst_str[-1].split("#")[1].split(":")[0].to_i
	      if initial_offset > 0
		  initial_offset = 0
	      end
	  end
	  #puts "instruction #{i.inst_str} operands #{i.operands} initial_offset #{initial_offset}"
        f = Function.new(i.operands[0], i.inst_str, initial_offset, i)
	f.set_vars i.operands
        @functions.merge!((i.operands[0]) => f)
      end
    end
  end

  private
  def build_bbs_function(name, f_start, f_end)
    starts = [f_start, (f_end + 1)]
    for i in f_start..f_end
      case @instructions[i].opcode
      when "br"
        starts.push (i + 1) if i != f_end
        starts.push @instructions[i].operands[0]
        if (@instructions[i].operands[0] >= f_start) && (@instructions[i].operands[0] <= f_end)
          starts.push @instructions[i].operands[0]
        end
      when "blbc", "blbs"
        starts.push (i + 1) if i != f_end
        if (@instructions[i].operands[1] >= f_start) && (@instructions[i].operands[1] <= f_end)
          starts.push @instructions[i].operands[1]
        end
      when "ret"
        starts.push (i + 1) if i != f_end
      when "call"
        if (@instructions[i].operands[0] >= f_start) && (@instructions[i].operands[0] <= f_end)
          starts.push @instructions[i].operands[0]
        end
      when "nop"
        starts.push i
        starts.push (i + 1) if i != f_end
      end
    end
    starts.uniq!
    starts.sort!
    first = starts.shift
    while !starts.empty?
      last = starts.shift
      last -= 1 if last >= 1
      bb = BasicBlock.new(@instructions, first, last)
      if (!(@functions[name].bbs.empty?)) && (@functions[name].bbs.last.instructions.last.opcode != "ret") && (@functions[name].bbs.last.instructions.last.opcode != "br")
        bb.preds.push @functions[name].bbs.last
        @functions[name].bbs.last.sucs.push bb
      end
      @functions[name].bbs.push bb
      first = last + 1
    end
  end

  public
  def build_bbs
    sorted_funcs = @functions_info.sort_by {|func, start| start}
    start = sorted_funcs.shift
    while !sorted_funcs.empty?
      last = sorted_funcs.shift
      build_bbs_function(start[0], start[1], last[1] - 1)
      start = last
    end
    build_bbs_function(start[0], start[1], @instructions.length - 1)
  end

  public
  def build_cfgs
    @functions.each do |name, f|
      f.build_cfg
    end
  end

  def build_doms
    @functions.each do |name, f|
      f.find_doms
    end
  end


  def from_ssa
      #puts @functions_info
      initial_index = 1
      @functions.each do |name, f|
	  puts "\n\nWorking on #{name} at #{initial_index}" if $debug
	  initial_index, entry_point = f.convert_from_ssa(initial_index)
	  @functions_info[name] = entry_point
      end
      
      # now fix up call instructions
      @functions.each do |name, f|
	  f.fix_up_calls( @functions_info, @orig_functions_index )
      end
  end

  def codegen(filename)
      this_filename = filename + "o"
      file = File.new(this_filename, "w")

      @header.each do |i|
	  file.puts i.codegen( self )
      end

      @functions.each do |name, f|
	  f.write_il file
      end

      file.close
  end

  def parse_profile filename
      bb_count_map = {}
      likely_type_map = {}

      file = File.new(filename, "r")
      file.each_line do |line|
	  elems = line.split(":")

	  id = elems[0].to_i
	  count = elems[1].to_i

	  lower_id = id & 0xffff
	  upper_id = id >> 16

	  puts "Reading profile count upper #{upper_id} and lower #{lower_id} from #{line}" if $debug

	  # capture basic block profile counts
	  if upper_id != 0 
	      if lower_id == 0
		  bb_count_map[ upper_id ] = count
	      else
		  # capture type profiling
		  if likely_type_map[ upper_id ].nil?
		      likely_type_map[ upper_id ] = {}
		  end
		  likely_type_map[ upper_id ][ lower_id ] = count
	      end
	  end
      end
      file.close

      # process type profiling info
      @functions.each do |name, f|
	  f.bbs.each do |bb|
	      bb.count = bb_count_map[ bb.original_id ]
	      bb.instructions.each do |ins|
		  if likely_type_map.has_key?( ins.id )
		      count = 0
		      type = nil
		      likely_type_map[ ins.id ].each do |key, value|
		      	  if count < value
		      	      type = key
		      	  end
		      end
		      puts "Adding likely type #{type} to #{ ins.id }: #{ ins.opcode }" if $debug
		      ins.likely_type_id = type
		  end
	      end
	  end

	  # now specialize dynamic instructions
	  ret = f.specialize_dynamic(@last_inst_id, @types)
	  @last_inst_id = ret[0]
      end

  end


end

