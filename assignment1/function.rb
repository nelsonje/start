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
				if !bb.sucs.empty? && (target_bb != bb.sucs[0])
					bb.sucs.push target_bb
					target_bb.preds.push bb
				end
			when "blbc", "blbs"
				target = last_inst.operands[1]
				target_bb = bb_index[target]
				if !bb.sucs.empty? && (target_bb != bb.sucs[0])
					bb.sucs.push target_bb
					target_bb.preds.push bb
				end
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
          max = @topo.length - 1
          @topo.each do |bb|
            bb.topo_id = index
            bb.postorder_id = max - index
            index += 1
          end

        end

        public
        def print_doms
          puts "Dominators"
          @doms.each_index do |i|
            if @doms[i].nil?
              puts @topo[i].id.to_s + ": idom nil"
            else
              puts @topo[i].id.to_s + ": idom " + @doms[i].id.to_s
            end
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

              while finger1.postorder_id < finger2.postorder_id
                puts "1: finger1=" + finger1.id.to_s + " finger2=" + finger2.id.to_s
#                print_doms
                finger1 = @doms[ finger1.topo_id ]
                puts "1a: finger1=" + finger1.id.to_s + " finger2=" + finger2.id.to_s
              end
              while finger2.postorder_id < finger1.postorder_id
                puts "2: finger1=" + finger1.id.to_s + " finger2=" + finger2.id.to_s
                finger2 = @doms[ finger2.topo_id ]
                puts "2a: finger1=" + finger1.id.to_s + " finger2=" + finger2.id.to_s
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
          start.dom_processed = true
          puts "Starting doms from " + start.id.to_s

          puts "Topo order"
          @topo.each do |t|
            puts t.id.to_s + ": postorder id " + t.postorder_id.to_s
          end

          # loop while something changed
          changed = true
          while changed
            
            changed = false
            # postorder iteration
            @topo.each do |bb|
              # skip first node
              if bb != start

                initial_new_idom = nil

                # find an already-processed predecessor
                bb.preds.each do |pred|
                  if pred.dom_processed
                    initial_new_idom = pred
                    break
                  end
                end

                # if necessary, refine based on other predecessors 
                new_idom = initial_new_idom
                bb.preds.each do |pred|
                  if pred != initial_new_idom
                    # if we already have a dominator for this predecessor,
                    if !@doms[ pred.topo_id ].nil?
                      # see if it gets us a better dominator
                      puts "Need to find better new_idom for " + bb.id.to_s
                      new_idom = intersect pred, new_idom 
                    end
                  end
                end

                # if domintor changed, update it
                if @doms[bb.topo_id] != new_idom
                  @doms[bb.topo_id] = new_idom
                  changed = true
                end

              end # if bb != start

              # mark as processed
              bb.dom_processed = true
            end

          end

          print_doms

        end



end
