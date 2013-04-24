    method main@2: x#-4:int
    instr 1: nop
    instr 2: entrypc
    instr 3: enter 4
    instr 4: cmpeq 1 2 :bool
    instr 5: blbc (4) [8]
    instr 6: move 1 x#-4
    instr 7: br [13]
    instr 8: cmpeq 2 3 :bool
    instr 9: blbc (8) [12]
    instr 10: move 2 x#-4
    instr 11: br [13]
    instr 12: move 3 x#-4
    instr 13: ret 0
    instr 14: nop

