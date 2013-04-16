class Function
	attr_accessor :bbs
	def initialize(name)
		@name = name
		@bbs = []
          @topo = []
          @doms = []
	end

	public
	def build_cfg
		#This assures that building CFG is low complexity
		bb_index = {}
		@bbs.each do |bb|
			inst_n = (bb.instructions.first.inst_str)[1].scan(/[\d]+/)
			inst_n = Integer(inst_n[0])
			bb_index[inst_n] = bb
		end
		@bbs.each do |bb|
			last_inst = bb.instructions.last
			case last_inst.opcode
			when "br"
				target = last_inst.operands[0]
				target_bb = bb_index[target]
				bb.sucs.push target_bb
				target_bb.preds.push bb
			when "blbc", "blbs"
				target = last_inst.operands[1]
				target_bb = bb_index[target]
				bb.sucs.push target_bb
				target_bb.preds.push bb
			end
		end
	end

        private
        def find_topo_order

          # reset visited status
          @bbs.each do |bb|
            bb.visited = :unvisited
          end

          # helper for topological order
          def visit( bb )
            # ignore if we've been here before
            if bb.visited == :unvisited
              # note that we're visiting here
              bb.visited = :visiting

              # recurse
              bb.sucs.reverse.each do |suc|
                visit suc
              end

              # now finish this node
              bb.visited = :visited
              puts "Visiting " + bb.id.to_s
              @topo.push bb
            end
          end

          # compute topological order
          @bbs.each do |bb|
            # recurse down all unvisited blocks that are connected to something
            if bb.visited == :unvisited and !(bb.sucs.empty? and bb.preds.empty?)
              print "Starting from ", bb.id, "\n"
              visit bb
            end
          end

          # we did that backwards, so reverse.
          @topo.reverse!

          # record topological ids in bbs
          index = 0
          @topo.each do |bb|
            bb.topo_id = index
            index += 1
          end

        end

        public
        def find_doms
          
          # compute order
          print "Starting\n"
          find_topo_order


          # helper for doms
          def intersect( b1, b2 )
            finger1 = b1
            finger2 = b2

            while finger1 != finger2
              puts "Refining with " + finger1.id.to_s + " and " + finger2.id.to_s

              while finger1.topo_id < finger2.topo_id
                puts "Finger1 " + finger1.id.to_s + " = " + @doms[ finger1.topo_id ].id.to_s
                finger1 = @doms[ finger1.topo_id ]
              end
              while finger2.topo_id < finger1.topo_id
                puts "Finger2 " + finger2.id.to_s + " (" + finger2.topo_id.to_s + ")" + " = " + @doms[ finger2.topo_id ].id.to_s + " (" + @doms[ finger2.topo_id ].topo_id.to_s + ")"
                finger2 = @doms[ finger2.topo_id ]
              end
            end

            return finger1
          end

          # initialize dominator array
          @topo.each do |bb|
            @doms.push nil
          end
          
          # start with first node
          @doms[0] = @topo[0]
          start = @topo[0]
          puts "Starting doms from " + start.id.to_s
          puts "Topo order"
          @topo.each do |t|
            puts t.id.to_s
          end

          # loop while something changed
          changed = true
          while changed
            
            changed = false
            @topo.reverse.each do |bb|
              # skip first node
              if bb != start

                new_idom = nil
                bb.preds.each_index do |i|
                  pred = bb.preds[i]
                  if i == 0
                    puts "Initial new_idom for " + bb.id.to_s + " is " + pred.id.to_s
                    new_idom = pred
                  else
                    # if we already have a dominator for this predecessor,
                    if !@doms[ pred.topo_id ].nil?
                      # refine it
                      puts "Need to find better new_idom for " + bb.id.to_s
                      new_idom = intersect pred, new_idom 
                    end
                  end
                end

                if @doms[bb.topo_id] != new_idom
                  @doms[bb.topo_id] = new_idom
                  changed = true
                end

              end
            end

          end

          puts "Dominators"
          @doms.each_index do |i|
            puts @topo[i].id.to_s + ": idom " + @doms[i].id.to_s
          end


        end



end
