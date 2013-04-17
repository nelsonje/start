    method main@2:
    global n#32764:int
    global result#32760:int
    instr 1: nop
    instr 2: entrypc
    instr 3: enter 0
    instr 4: add result_base#32760 GP :int*
    instr 5: store 0 (4)
    instr 6: add n_base#32764 GP :int*
    instr 7: load (6) :int
    instr 8: cmple (7) 0 :bool
    instr 9: blbs (8) [51]
    instr 10: add n_base#32764 GP :int*
    instr 11: load (10) :int
    instr 12: cmple (11) 0 :bool
    instr 13: blbs (12) [51]
    instr 14: add n_base#32764 GP :int*
    instr 15: load (14) :int
    instr 16: cmple (15) 0 :bool
    instr 17: blbs (16) [51]
    instr 18: add n_base#32764 GP :int*
    instr 19: load (18) :int
    instr 20: cmple (19) 0 :bool
    instr 21: blbs (20) [51]
    instr 22: add n_base#32764 GP :int*
    instr 23: load (22) :int
    instr 24: cmple (23) 0 :bool
    instr 25: blbs (24) [51]
    instr 26: add n_base#32764 GP :int*
    instr 27: load (26) :int
    instr 28: cmple (27) 0 :bool
    instr 29: blbs (28) [51]
    instr 30: add n_base#32764 GP :int*
    instr 31: load (30) :int
    instr 32: cmple (31) 0 :bool
    instr 33: blbs (32) [51]
    instr 34: add n_base#32764 GP :int*
    instr 35: load (34) :int
    instr 36: cmple (35) 0 :bool
    instr 37: blbs (36) [51]
    instr 38: add n_base#32764 GP :int*
    instr 39: load (38) :int
    instr 40: cmple (39) 0 :bool
    instr 41: blbs (40) [51]
    instr 42: add n_base#32764 GP :int*
    instr 43: load (42) :int
    instr 44: cmple (43) 0 :bool
    instr 45: blbs (44) [51]
    instr 46: add result_base#32760 GP :int*
    instr 47: load (46) :int
    instr 48: add (47) 1 :int
    instr 49: add result_base#32760 GP :int*
    instr 50: store (48) (49)
    instr 51: ret 0
    instr 52: nop

