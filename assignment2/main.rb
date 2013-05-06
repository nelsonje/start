require_relative 'program'

# enable logging
$debug = false

p = Program.new
p.read_program(ARGV[0])

p.build_bbs
p.build_cfgs

p.build_doms

#p.dump_info ARGV[0]

p.to_ssa
#p.gcse
p.dump_cfgs ARGV[0]


