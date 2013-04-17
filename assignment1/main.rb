require_relative 'program'

p = Program.new
p.read_program(ARGV[0])

p.build_bbs
p.build_cfgs

p.build_doms

p.dump_cfgs ARGV[0]
p.dump_info ARGV[0]



