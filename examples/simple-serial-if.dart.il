    method main@2:
    global n1#32764:int
    global result#32760:int
    instr 1: nop
    instr 2: entrypc
    instr 3: enter 0
    instr 4: add result_base#32760 GP :int*
    instr 5: store 0 (4)
    instr 6: add n1_base#32764 GP :int*
    instr 7: load (6) :int
    instr 8: cmple (7) 0 :bool
    instr 9: blbs (8) [10]
    instr 10: add result_base#32760 GP :int*
    instr 11: load (10) :int
    instr 12: add (11) 1 :int
    instr 13: add result_base#32760 GP :int*
    instr 14: store (12) (13)
    instr 15: ret 0
    instr 16: nop

