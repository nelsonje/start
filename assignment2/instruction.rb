class Instruction
  attr_accessor   :id, :opcode, :operands, :rhs, :lhs, :ssa_mod_operands, :expr
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
    else
      @opcode = inst[0]
      @id = -1
    end
    @operands = []


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
      info = inst[4].scan(/[\d]+/)
      @operands.push Integer(info[0])
    when "ret", "enter"
      @operands.push Integer(inst[3])
    when "sub", "add", "mul", "div", "mod", "cmpeq", "cmple", "cmplt", "istype", "store", "move", "checkbounds", "checktype", "lddynamic"
    	@operands.push inst[3]
    	@operands.push inst[4]
    when "isnull", "load", "new", "newlist", "checknull", "write", "param"
    	@operands.push inst[3]
    when "stdynamic"
    	@operands.push inst[3]
    	@operands.push inst[4]
    	@operands.push inst[5]
    when "global", "nop", "entrypc", "wrl", nil, "type"
	#puts "Do something here for #{inst}"
    else
    	puts "Unknown instruction detected: " + @opcode
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
			@inst_str[op_i+3] = @operands[op_i].dup
		end
	end

  end

end

