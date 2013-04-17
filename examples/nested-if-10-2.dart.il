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
    instr 9: blbs (8) [19]
    instr 10: add n_base#32764 GP :int*
    instr 11: load (10) :int
    instr 12: cmple (11) 0 :bool
    instr 13: blbs (12) [19]
    instr 14: add result_base#32760 GP :int*
    instr 15: load (14) :int
    instr 16: add (15) 1 :int
    instr 17: add result_base#32760 GP :int*
    instr 18: store (16) (17)
    instr 19: add n_base#32764 GP :int*
    instr 20: load (19) :int
    instr 21: cmple (20) 0 :bool
    instr 22: blbs (21) [32]
    instr 23: add n_base#32764 GP :int*
    instr 24: load (23) :int
    instr 25: cmple (24) 0 :bool
    instr 26: blbs (25) [32]
    instr 27: add result_base#32760 GP :int*
    instr 28: load (27) :int
    instr 29: add (28) 1 :int
    instr 30: add result_base#32760 GP :int*
    instr 31: store (29) (30)
    instr 32: add n_base#32764 GP :int*
    instr 33: load (32) :int
    instr 34: cmple (33) 0 :bool
    instr 35: blbs (34) [45]
    instr 36: add n_base#32764 GP :int*
    instr 37: load (36) :int
    instr 38: cmple (37) 0 :bool
    instr 39: blbs (38) [45]
    instr 40: add result_base#32760 GP :int*
    instr 41: load (40) :int
    instr 42: add (41) 1 :int
    instr 43: add result_base#32760 GP :int*
    instr 44: store (42) (43)
    instr 45: add n_base#32764 GP :int*
    instr 46: load (45) :int
    instr 47: cmple (46) 0 :bool
    instr 48: blbs (47) [58]
    instr 49: add n_base#32764 GP :int*
    instr 50: load (49) :int
    instr 51: cmple (50) 0 :bool
    instr 52: blbs (51) [58]
    instr 53: add result_base#32760 GP :int*
    instr 54: load (53) :int
    instr 55: add (54) 1 :int
    instr 56: add result_base#32760 GP :int*
    instr 57: store (55) (56)
    instr 58: add n_base#32764 GP :int*
    instr 59: load (58) :int
    instr 60: cmple (59) 0 :bool
    instr 61: blbs (60) [71]
    instr 62: add n_base#32764 GP :int*
    instr 63: load (62) :int
    instr 64: cmple (63) 0 :bool
    instr 65: blbs (64) [71]
    instr 66: add result_base#32760 GP :int*
    instr 67: load (66) :int
    instr 68: add (67) 1 :int
    instr 69: add result_base#32760 GP :int*
    instr 70: store (68) (69)
    instr 71: ret 0
    instr 72: nop

