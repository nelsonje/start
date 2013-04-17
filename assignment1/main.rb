require_relative 'program'

p = Program.new
p.read_program(ARGV[0])
#p.build_cfgs
p.build_bbs
p.build_cfgs

start_time = Time.now
p.build_doms
elapsed_time = Time.now - start_time
puts "Dominator construction took " + elapsed_time.to_s + " seconds"

p.dump_cfgs ARGV[0]



