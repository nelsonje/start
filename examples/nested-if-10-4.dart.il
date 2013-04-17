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
    instr 9: blbs (8) [27]
    instr 10: add n_base#32764 GP :int*
    instr 11: load (10) :int
    instr 12: cmple (11) 0 :bool
    instr 13: blbs (12) [27]
    instr 14: add n_base#32764 GP :int*
    instr 15: load (14) :int
    instr 16: cmple (15) 0 :bool
    instr 17: blbs (16) [27]
    instr 18: add n_base#32764 GP :int*
    instr 19: load (18) :int
    instr 20: cmple (19) 0 :bool
    instr 21: blbs (20) [27]
    instr 22: add result_base#32760 GP :int*
    instr 23: load (22) :int
    instr 24: add (23) 1 :int
    instr 25: add result_base#32760 GP :int*
    instr 26: store (24) (25)
    instr 27: add n_base#32764 GP :int*
    instr 28: load (27) :int
    instr 29: cmple (28) 0 :bool
    instr 30: blbs (29) [48]
    instr 31: add n_base#32764 GP :int*
    instr 32: load (31) :int
    instr 33: cmple (32) 0 :bool
    instr 34: blbs (33) [48]
    instr 35: add n_base#32764 GP :int*
    instr 36: load (35) :int
    instr 37: cmple (36) 0 :bool
    instr 38: blbs (37) [48]
    instr 39: add n_base#32764 GP :int*
    instr 40: load (39) :int
    instr 41: cmple (40) 0 :bool
    instr 42: blbs (41) [48]
    instr 43: add result_base#32760 GP :int*
    instr 44: load (43) :int
    instr 45: add (44) 1 :int
    instr 46: add result_base#32760 GP :int*
    instr 47: store (45) (46)
    instr 48: add n_base#32764 GP :int*
    instr 49: load (48) :int
    instr 50: cmple (49) 0 :bool
    instr 51: blbs (50) [61]
    instr 52: add n_base#32764 GP :int*
    instr 53: load (52) :int
    instr 54: cmple (53) 0 :bool
    instr 55: blbs (54) [61]
    instr 56: add result_base#32760 GP :int*
    instr 57: load (56) :int
    instr 58: add (57) 1 :int
    instr 59: add result_base#32760 GP :int*
    instr 60: store (58) (59)
    instr 61: ret 0
    instr 62: nop

