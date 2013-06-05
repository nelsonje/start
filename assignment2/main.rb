require_relative 'program'

ssa_enabled = true
cse_enabled = true
scp_enabled = true
profiling_enabled = true

cfg_enabled = true
ir_enabled = true
bssa_enabled = true
report_enabled = true

profile_filename = nil
$debug = false

ARGV.each do |str|
    if str.include? "-debug"
	$debug = true
    end

    if str.include? "-profile="
	opts = str.split('=')
	profile_filename = opts[1]
    end

    if str.include? "-opt="
	ssa_enabled = false
	cse_enabled = false
	scp_enabled = false
	profiling_enabled = false
	opts = str.split('=')[1].split(',')
	opts.each do |opt|
	    case opt
	    when 'cse'
		cse_enabled = true
	    when 'scp'
		scp_enabled = true
	    when 'ssa'
		ssa_enabled = true
	    when 'profile'
		profiling_enabled = true
	    end
	end
    end

    if str.include? "-backend="
	cfg_enabled = false
	ir_enabled = false
	bssa_enabled = false
	report_enabled = false
	opts = str.split('=')[1].split(',')
	opts.each do |opt|
	    case opt
	    when 'cfg'
		cfg_enabled = true
	    when 'ir'
		ir_enabled = true
	    when 'ssa'
		bssa_enabled = true
		ir_enabled = true
	    when 'report'
		report_enabled = true
	    end
	end
    end
end

if cse_enabled and not ssa_enabled
    abort "Common subexpression elimination requires SSA to be enabled."
end

if scp_enabled and not ssa_enabled
    abort "Simple constant propagation requires SSA to be enabled."
end

if profiling_enabled and not ssa_enabled
    abort "Profiling requires SSA to be enabled."
end


p = Program.new
p.read_program( ARGV[0] )

p.build_bbs
p.build_cfgs

p.build_doms

p.dump_info ARGV[0] if report_enabled

p.capture_bb_map

p.parse_profile profile_filename if profile_filename != nil

p.instrument if profiling_enabled

p.to_ssa if ssa_enabled

p.scp if scp_enabled
p.report_gen_scp if scp_enabled and report_enabled

p.gcse if cse_enabled
p.report_gen_gcse if cse_enabled and report_enabled

p.from_ssa if bssa_enabled

p.dump_cfgs ARGV[0] if cfg_enabled
p.codegen ARGV[0] if ir_enabled

