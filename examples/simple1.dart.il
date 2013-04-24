    method main@2: x#-4:int
    instr 1: nop
    instr 2: entrypc
    instr 3: enter 4
    instr 4: cmpeq 1 0 :bool
    instr 5: blbc (4) [9]
    instr 6: add x#-4 1 :int
    instr 7: move (6) x#-4
    instr 8: br [4]
    instr 9: ret 0
    instr 10: nop

