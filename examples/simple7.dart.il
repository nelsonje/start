    method other@2: x#-4:int y#-8:int
    method main@9: x#-4:int y#-8:int
    instr 1: nop
    instr 2: enter 8
    instr 3: move 0 x#-4
    instr 4: cmpeq 1 1 :bool
    instr 5: blbc (4) [8]
    instr 6: add x#-4 1 :int
    instr 7: move (6) x#-4
    instr 8: ret 0
    instr 9: entrypc
    instr 10: enter 8
    instr 11: move 0 x#-4
    instr 12: cmpeq 1 1 :bool
    instr 13: blbc (12) [25]
    instr 14: cmpeq 1 1 :bool
    instr 15: blbc (14) [25]
    instr 16: add x#-4 1 :int
    instr 17: move (16) x#-4
    instr 18: cmpeq 1 1 :bool
    instr 19: blbc (18) [25]
    instr 20: add x#-4 1 :int
    instr 21: move (20) x#-4
    instr 22: call [2]
    instr 23: add x#-4 1 :int
    instr 24: move (23) x#-4
    instr 25: write x#-4
    instr 26: write y#-8
    instr 27: wrl
    instr 28: ret 0
    instr 29: nop

