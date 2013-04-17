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
    instr 9: blbs (8) [23]
    instr 10: add n_base#32764 GP :int*
    instr 11: load (10) :int
    instr 12: cmple (11) 0 :bool
    instr 13: blbs (12) [23]
    instr 14: add n_base#32764 GP :int*
    instr 15: load (14) :int
    instr 16: cmple (15) 0 :bool
    instr 17: blbs (16) [23]
    instr 18: add result_base#32760 GP :int*
    instr 19: load (18) :int
    instr 20: add (19) 1 :int
    instr 21: add result_base#32760 GP :int*
    instr 22: store (20) (21)
    instr 23: add n_base#32764 GP :int*
    instr 24: load (23) :int
    instr 25: cmple (24) 0 :bool
    instr 26: blbs (25) [40]
    instr 27: add n_base#32764 GP :int*
    instr 28: load (27) :int
    instr 29: cmple (28) 0 :bool
    instr 30: blbs (29) [40]
    instr 31: add n_base#32764 GP :int*
    instr 32: load (31) :int
    instr 33: cmple (32) 0 :bool
    instr 34: blbs (33) [40]
    instr 35: add result_base#32760 GP :int*
    instr 36: load (35) :int
    instr 37: add (36) 1 :int
    instr 38: add result_base#32760 GP :int*
    instr 39: store (37) (38)
    instr 40: add n_base#32764 GP :int*
    instr 41: load (40) :int
    instr 42: cmple (41) 0 :bool
    instr 43: blbs (42) [57]
    instr 44: add n_base#32764 GP :int*
    instr 45: load (44) :int
    instr 46: cmple (45) 0 :bool
    instr 47: blbs (46) [57]
    instr 48: add n_base#32764 GP :int*
    instr 49: load (48) :int
    instr 50: cmple (49) 0 :bool
    instr 51: blbs (50) [57]
    instr 52: add result_base#32760 GP :int*
    instr 53: load (52) :int
    instr 54: add (53) 1 :int
    instr 55: add result_base#32760 GP :int*
    instr 56: store (54) (55)
    instr 57: add n_base#32764 GP :int*
    instr 58: load (57) :int
    instr 59: cmple (58) 0 :bool
    instr 60: blbs (59) [66]
    instr 61: add result_base#32760 GP :int*
    instr 62: load (61) :int
    instr 63: add (62) 1 :int
    instr 64: add result_base#32760 GP :int*
    instr 65: store (63) (64)
    instr 66: ret 0
    instr 67: nop

