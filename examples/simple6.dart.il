    method main@2: x#-4:int y#-8:int
    instr 1: nop
    instr 2: entrypc
    instr 3: enter 8
    instr 4: move 0 x#-4
    instr 5: cmpeq 1 1 :bool
    instr 6: blbc (5) [19]
    instr 7: cmpeq 1 1 :bool
    instr 8: blbc (7) [19]
    instr 9: add x#-4 1 :int
    instr 10: move (9) x#-4
    instr 11: cmpeq 1 1 :bool
    instr 12: blbc (11) [19]
    instr 13: add x#-4 1 :int
    instr 14: move (13) x#-4
    instr 15: add x#-4 1 :int
    instr 16: move (15) x#-4
    instr 17: add x#-4 1 :int
    instr 18: move (17) x#-4
    instr 19: write x#-4
    instr 20: write y#-8
    instr 21: wrl
    instr 22: ret 0
    instr 23: nop

