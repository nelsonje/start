require_relative 'instruction'
require_relative 'function'
require_relative 'basic_block'

class Program
  def initialize
    @instructions = [nil]
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
    
  end

  public
  def to_ssa
  	@functions.each do |name, f|
		@last_inst_id = f.to_ssa(@last_inst_id)
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
        file.print("\nImmediate dominator: " + bb.idom.id.to_s + "\n\n\n") 
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
        file.print("n" + i.to_s + " [label=\"{BB " + f.bbs[i].id.to_s + " (idom: ")
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
	  puts "\n\nWorking on #{name} at #{initial_index}" if $debug_print
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

end

