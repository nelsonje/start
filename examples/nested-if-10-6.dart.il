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
    instr 9: blbs (8) [35]
    instr 10: add n_base#32764 GP :int*
    instr 11: load (10) :int
    instr 12: cmple (11) 0 :bool
    instr 13: blbs (12) [35]
    instr 14: add n_base#32764 GP :int*
    instr 15: load (14) :int
    instr 16: cmple (15) 0 :bool
    instr 17: blbs (16) [35]
    instr 18: add n_base#32764 GP :int*
    instr 19: load (18) :int
    instr 20: cmple (19) 0 :bool
    instr 21: blbs (20) [35]
    instr 22: add n_base#32764 GP :int*
    instr 23: load (22) :int
    instr 24: cmple (23) 0 :bool
    instr 25: blbs (24) [35]
    instr 26: add n_base#32764 GP :int*
    instr 27: load (26) :int
    instr 28: cmple (27) 0 :bool
    instr 29: blbs (28) [35]
    instr 30: add result_base#32760 GP :int*
    instr 31: load (30) :int
    instr 32: add (31) 1 :int
    instr 33: add result_base#32760 GP :int*
    instr 34: store (32) (33)
    instr 35: add n_base#32764 GP :int*
    instr 36: load (35) :int
    instr 37: cmple (36) 0 :bool
    instr 38: blbs (37) [56]
    instr 39: add n_base#32764 GP :int*
    instr 40: load (39) :int
    instr 41: cmple (40) 0 :bool
    instr 42: blbs (41) [56]
    instr 43: add n_base#32764 GP :int*
    instr 44: load (43) :int
    instr 45: cmple (44) 0 :bool
    instr 46: blbs (45) [56]
    instr 47: add n_base#32764 GP :int*
    instr 48: load (47) :int
    instr 49: cmple (48) 0 :bool
    instr 50: blbs (49) [56]
    instr 51: add result_base#32760 GP :int*
    instr 52: load (51) :int
    instr 53: add (52) 1 :int
    instr 54: add result_base#32760 GP :int*
    instr 55: store (53) (54)
    instr 56: ret 0
    instr 57: nop

