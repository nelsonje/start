    method print@2: i#20:int j#16:int k#12:int l#8:int
    method main@5: i#-4:int j#-8:int k#-12:int l#-16:int
    instr 1: nop
    instr 2: enter 0
    instr 3: move 0 i#20
    instr 4: ret 16
    instr 5: entrypc
    instr 6: enter 16
    instr 7: move 1 i#-4
    instr 8: move 1 j#-8
    instr 9: move 1 k#-12
    instr 10: move 1 l#-16
    instr 11: cmpeq 1 0 :bool
    instr 12: blbc (11) [41]
    instr 13: cmpeq 1 1 :bool
    instr 14: blbc (13) [24]
    instr 15: move i#-4 j#-8
    instr 16: cmpeq 1 1 :bool
    instr 17: blbc (16) [20]
    instr 18: move 2 l#-16
    instr 19: br [21]
    instr 20: move 3 l#-16
    instr 21: add k#-12 1 :int
    instr 22: move (21) k#-12
    instr 23: br [26]
    instr 24: add k#-12 2 :int
    instr 25: move (24) k#-12
    instr 26: param i#-4
    instr 27: param j#-8
    instr 28: param k#-12
    instr 29: param l#-16
    instr 30: call [2]
    instr 31: cmpeq 1 0 :bool
    instr 32: blbc (31) [38]
    instr 33: cmpeq 1 1 :bool
    instr 34: blbc (33) [37]
    instr 35: add l#-16 4 :int
    instr 36: move (35) l#-16
    instr 37: br [31]
    instr 38: add i#-4 6 :int
    instr 39: move (38) i#-4
    instr 40: br [11]
    instr 41: ret 0
    instr 42: nop

