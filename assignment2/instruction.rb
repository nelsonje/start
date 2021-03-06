class Instruction
  attr_accessor   :id, :opcode, :operands, :rhs, :lhs, :ssa_mod_operands, :expr, :bb, :bl_operand, :pre_ssa_id, :post_ssa_id, :likely_type_id, :fields, :field_is_int
  attr_reader     :inst_str, :nop

  def initialize(inst)
    #Necessary for SSA
    #These are gonna be contructed when calling set_vars_assign
    #for the function
    @rhs = []
    @lhs = []
    #Useful for printing after changing operands
    @ssa_mod_operands = []
    @old_inst_str = ""
    #Value number vars
    @expr = []
    if inst[0] == "instr"
      @opcode = inst[2]
      @id = Integer( inst[1].chomp(':') )
      if @opcode.eql? "nop"
        @nop = true
      else 
        @nop = false
      end
    elsif inst[0] == "type"
	@opcode = inst[0]
	@id = inst[1].chomp(":")
	# parse type line and build field map
	@fields = {}
	@field_is_int = {}
	inst.each do |s|
	      if s.include?("#")
		  a = s.split(/:|#/)
		  @fields[ a[0] ] = a[1]
		  @field_is_int[ a[0] ] = a[2] == "int"
	      end
	  end
    else
      @opcode = inst[0]
      @id = -1
    end
    @operands = []
    #BB to which this inst belongs
    @bb
    @bl_operand

      @pre_ssa_id = id
      @post_ssa_id = -1

      @likely_type_id = nil

    #TODO
    #Unknown instructions' semantics
    #neg
    #Instructions that define variables: sub, add, mul, div, mod, cmpeq, cmple, cmplt, istype, move, checktype, lddynamic, isnull, load, new, newlist, checknull
    case @opcode
    when "method"
      info = inst[1].scan(/[^@:]+/)
      @operands.push info[0]
      @operands.push Integer(info[1])
      for i in 2...inst.length
      	@operands.push (inst[i].scan(/[^#:]+/))[0]
      end
    when "call", "br"
      info = inst[3].scan(/[\d]+/)
      @operands.push Integer(info[0])
    when "blbc", "blbs"
      info = inst[3].scan(/[\d]+/)
      @operands.push Integer(info[0])
      @bl_operand = inst[3]
      info = inst[4].scan(/[\d]+/)
      @operands.push Integer(info[0])
    when "ret", "enter"
      @operands.push Integer(inst[3])
    when "sub", "add", "mul", "div", "mod", "cmpeq", "cmple", "cmplt", "istype", "store", "move", "checkbounds", "checktype", "lddynamic"
    	@operands.push inst[3]
    	@operands.push inst[4]
    when "isnull", "load", "new", "newlist", "checknull", "write", "param", "count"
    	@operands.push inst[3]
    when "stdynamic"
    	@operands.push inst[3]
    	@operands.push inst[4]
    	@operands.push inst[5]
    when "global", "nop", "entrypc", "wrl", nil, "type"
	#puts "Do something here for #{inst}"
    else
    	puts "Unknown instruction detected: " + inst.join(' ')
	#TODO
	#Since I don't know how to exit in Ruby, divide by zero LOL
	5/0
    end
    @inst_str = inst
  end

  public
  def fix_inst_string_ssa
      @old_inst_str = @inst_str.dup
      @ssa_mod_operands.uniq!
      #p @inst_str
      #p @ssa_mod_operands
      #p @operands
      @ssa_mod_operands.each do |op_i|
	  case @opcode
	  when "blbc", "blbs", "sub", "add", "mul", "div", "mod", "cmpeq", "cmple", "cmplt", "istype", "store", "move", "checkbounds", "checktype", "lddynamic", "isnull", "load", "new", "newlist", "checknull", "write", "param", "stdynamic"
	      #puts "Replacing"
	      #p @inst_str[op_i+3]
	      #puts "By"
	      #p @operands[op_i]
	      #p op_i
	      if @operands[op_i].instance_of? Fixnum
		  @inst_str[op_i+3] = @operands[op_i]
	      else
		  @inst_str[op_i+3] = @operands[op_i].dup
	      end
	  end
      end
      if !@expr.empty?
	  for i in 2...@expr.length
	      @operands[i-2] = @expr[i]
	      @inst_str[i+1] = @expr[i]
	  end
      end
  end

  def codegen(f)
      extra = ""
      # for hand-debugging (won't run)
      #extra = "/#{pre_ssa_id}"

      case @opcode
      when  "method", "global", "type"
	  "#{ @inst_str.join(' ') }"
      when "blbc", "blbs"
	  # operand may be register, integer constant, or boolean constant
	  str = @operands[0].to_s
	  if @bl_operand.include?("(")
	      str = "(" + str + ")"
	  elsif @operands[0] == "false"
	      str = "0"
	  elsif @operands[0] == "true"
	      str = "1"
	  end
	  "instr #{id}#{extra}: #{@opcode} #{ str } [#{ @operands[1] }]" # (#{ @inst_str.join(' ') }) "
      when "br", "call"
	  # TODO doesn't quite work if these ops take constant arguments
	  "instr #{id}#{extra}: #{@opcode} [#{ @operands[0] }]"
      else
	  "instr #{id}#{extra}: #{@opcode} #{ @operands.join(' ') }"
      end
  end

  public 
  def reset(inst)
      initialize(inst)
  end

end

