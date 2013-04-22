class Instruction
  attr_accessor   :id, :opcode, :operands
  attr_reader     :inst_str, :nop

  def initialize(inst)
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
    else
    	puts "Unknown instructions detected: " + @opcode
	#TODO
	#Since I don't know how to exit in Ruby, divide by zero LOL
	5/0
    end
    @inst_str = inst
  end


end

