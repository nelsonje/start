    method main@2: a#-4:int
    instr 1: nop
    instr 2: entrypc
    instr 3: enter 4
    instr 4: cmpeq 1 0 :bool
    instr 5: blbc (4) [8]
    instr 6: move 1 a#-4
    instr 7: br [4]
    instr 8: ret 0
    instr 9: nop

