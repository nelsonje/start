require_relative 'program'

p = Program.new
p.read_program(ARGV[0])
#p.build_cfgs
p.build_bbs
p.build_cfgs


