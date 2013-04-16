require_relative 'instruction'
require_relative 'function'
require_relative 'basic_block'

class Program
	def initialize
		@instructions = [nil]
		@header = []
		
		# maps name of function to index of first instruction
		@functions_info = {}
		
		# maps name of function to function object
		@functions = {}

          @doms = []
          
	end

	public
	def dump_cfgs
		file = File.new("output/cfg.dot", "w")
		@functions.each do |name, f|
			file.puts "digraph cfg {"
			file.puts "node [shape=record];"
			file.puts "splines=true;"
			file.puts "entry [label=\"Entry\"];"
			for i in 0...f.bbs.length
				file.print("n" + i.to_s + " [label=\"{BB " + f.bbs[i].id.to_s + "|")
				for inst in 0...f.bbs[i].instructions.length
					text = ""
					f.bbs[i].instructions[inst].inst_str.each {|str| text << " " << str}
					file.print("<c" + inst.to_s + "> " + text)
					if inst == (f.bbs[i].instructions.length - 1)
						file.print("}\"];\n")
					else
						file.print("|")
					end
				end
			end

			file.puts("entry -> n0;") if !(f.bbs.empty?)

			for i in 0...f.bbs.length
				f.bbs[i].sucs.each do |s|
					file.print("n" + i.to_s + ":c" + (f.bbs[i].instructions.length - 1).to_s)
					file.print(" -> n" + (f.bbs.find_index(s)).to_s + ":c0;\n")
				end
			end
			file.print "}\n\n"
		end
		file.close
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


        



end

