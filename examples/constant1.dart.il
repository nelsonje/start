    method main@2: x#-4:int y#-8:int z#-12:int
    instr 1: nop
    instr 2: entrypc
    instr 3: enter 12
    instr 4: move 1 x#-4
    instr 5: move x#-4 y#-8
    instr 6: cmpeq x#-4 y#-8 :bool
    instr 7: blbc (6) [9]
    instr 8: move y#-8 z#-12
    instr 9: ret 0
    instr 10: nop

