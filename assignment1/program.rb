require_relative 'instruction'
require_relative 'function'
require_relative 'basic_block'
#require_relative 'cfg'

class Program
	def initialize
		@instructions = [nil]
		@header = []
		@functions_info = {}
		@functions = {}
		@cfgs = [] # are you using this?
	end

	private
	def read_instruction(line)
		inst = line.scan(/[^\s]+/)
		#if line is empty, return
		i = Instruction.new(inst)
		if inst[0] == "instr"
			@instructions.push(i)
		else
			@header.push(i)
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
				f = Function.new(i.operands[0])
				@functions.merge!((i.operands[0]) => f)
			end
		end
	end

	private
	def build_bbs_function(name, f_start, f_end)
		starts = []
		for i in f_start..f_end
			case @instructions[i].opcode
			when "br"
				starts.push (i + 1)
				starts.push @instructions[i].operands[0]
				if (@instructions[i].operands[0] >= f_start) && (@instructions[i].operands[0] <= f_end)
					starts.push @instructions[i].operands[0]
				end
			when "blbc", "blbs"
				starts.push (i + 1)
				if (@instructions[i].operands[1] >= f_start) && (@instructions[i].operands[1] <= f_end)
					starts.push @instructions[i].operands[1]
				end
			when "ret"
				starts.push (i + 1)
			when "call"
				if (@instructions[i].operands[0] >= f_start) && (@instructions[i].operands[0] <= f_end)
					starts.push @instructions[i].operands[0]
				end
			else
				#is this else necessary?
			end
		end
		starts.uniq!
		starts.sort!
		first = f_start
		while !starts.empty?
			last = starts.shift
			last -= 1
			bb = BasicBlock.new(@instructions, first, last)
			if (!(@functions[name].bbs.empty?))
				#p @functions[name].bbs.last.instructions
			end
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


#	public
#	def build_cfgs
#		sorted_funcs = @functions_info.sort_by {|func, start| start}
#		for i in 0...(sorted_funcs.length-1)
#			cfg = CFG.new(@instructions, sorted_funcs[i][0], sorted_funcs[i][1], sorted_funcs[i+1][1])
#			@cfgs.push(cfg)
#		end
#		cfg = CFG.new(@instructions, sorted_funcs[i][0], sorted_funcs[i][1], @instructions.length - 2)
#		@cfgs.push(cfg)
#	end

end

