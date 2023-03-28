# Preview

```sh
$ (cd ../spec && dune exec ../src/exe-watsup/main.exe -- *.watsup -v -l)
watsup 0.3 generator
== Parsing...
== Multiplicity checking...
== Elaboration...
== Printing...

;; 1-syntax.watsup:3.1-3.15
syntax n = nat

;; 1-syntax.watsup:9.1-9.37
syntax name = text

;; 1-syntax.watsup:14.1-14.36
syntax byte = nat

;; 1-syntax.watsup:15.1-15.45
syntax u32 = nat

;; 1-syntax.watsup:20.1-20.36
syntax idx = nat

;; 1-syntax.watsup:21.1-21.49
syntax funcidx = idx

;; 1-syntax.watsup:22.1-22.49
syntax globalidx = idx

;; 1-syntax.watsup:23.1-23.47
syntax tableidx = idx

;; 1-syntax.watsup:24.1-24.46
syntax memidx = idx

;; 1-syntax.watsup:25.1-25.45
syntax elemidx = idx

;; 1-syntax.watsup:26.1-26.45
syntax dataidx = idx

;; 1-syntax.watsup:27.1-27.47
syntax labelidx = idx

;; 1-syntax.watsup:28.1-28.47
syntax localidx = idx

;; 1-syntax.watsup:36.1-37.22
syntax numtype =
  | I32
  | I64
  | F32
  | F64

;; 1-syntax.watsup:38.1-39.5
syntax vectype =
  | V128

;; 1-syntax.watsup:40.1-41.20
syntax reftype =
  | FUNCREF
  | EXTERNREF

;; 1-syntax.watsup:42.1-43.34
syntax valtype =
  | numtype
  | vectype
  | reftype
  | BOT

;; 1-syntax.watsup:50.1-51.11
syntax resulttype = valtype*

;; 1-syntax.watsup:53.1-54.16
syntax limits = `[%..%]`(u32, u32)

;; 1-syntax.watsup:55.1-56.15
syntax globaltype = `MUT%?%`(()?, valtype)

;; 1-syntax.watsup:57.1-58.27
syntax functype = `%->%`(resulttype, resulttype)

;; 1-syntax.watsup:59.1-60.17
syntax tabletype = `%%`(limits, reftype)

;; 1-syntax.watsup:61.1-62.12
syntax memtype = `%I8`(limits)

;; 1-syntax.watsup:63.1-64.10
syntax elemtype = reftype

;; 1-syntax.watsup:65.1-66.5
syntax datatype = OK

;; 1-syntax.watsup:67.1-68.66
syntax externtype =
  | GLOBAL(globaltype)
  | FUNC(functype)
  | TABLE(tabletype)
  | MEM(memtype)

;; 1-syntax.watsup:81.1-81.23
syntax c_numtype = nat

;; 1-syntax.watsup:82.1-82.23
syntax c_vectype = nat

;; 1-syntax.watsup:85.1-85.44
syntax sx =
  | U
  | S

;; 1-syntax.watsup:87.1-87.52
syntax blocktype = functype

;; 1-syntax.watsup:90.1-90.26
syntax unop_numtype = XXX

;; 1-syntax.watsup:91.1-91.27
syntax binop_numtype = XXX

;; 1-syntax.watsup:92.1-92.28
syntax testop_numtype = XXX

;; 1-syntax.watsup:93.1-93.27
syntax relop_numtype = XXX

;; 1-syntax.watsup:94.1-94.19
syntax cvtop = XXX

;; 1-syntax.watsup:133.1-154.55
rec {

;; 1-syntax.watsup:133.1-154.55
syntax instr =
  | UNREACHABLE
  | NOP
  | DROP
  | SELECT(valtype?)
  | BLOCK(blocktype, instr*)
  | LOOP(blocktype, instr*)
  | IF(blocktype, instr*, instr*)
  | BR(labelidx)
  | BR_IF(labelidx)
  | BR_TABLE(labelidx*, labelidx)
  | CALL(funcidx)
  | CALL_INDIRECT(tableidx, functype)
  | RETURN
  | CONST(numtype, c_numtype)
  | UNOP(numtype, unop_numtype)
  | BINOP(numtype, binop_numtype)
  | TESTOP(numtype, testop_numtype)
  | RELOP(numtype, relop_numtype)
  | EXTEND(numtype, n)
  | CVTOP(numtype, cvtop, numtype, sx?)
  | REF.NULL(reftype)
  | REF.FUNC(funcidx)
  | REF.IS_NULL
  | LOCAL.GET(localidx)
  | LOCAL.SET(localidx)
  | LOCAL.TEE(localidx)
  | GLOBAL.GET(globalidx)
  | GLOBAL.SET(globalidx)
  | TABLE.GET(tableidx)
  | TABLE.SET(tableidx)
  | TABLE.SIZE(tableidx)
  | TABLE.GROW(tableidx)
  | TABLE.FILL(tableidx)
  | TABLE.COPY(tableidx, tableidx)
  | TABLE.INIT(tableidx, elemidx)
  | ELEM.DROP(elemidx)
  | MEMORY.SIZE
  | MEMORY.GROW
  | MEMORY.FILL
  | MEMORY.COPY
  | MEMORY.INIT(dataidx)
  | DATA.DROP(dataidx)
  | LOAD(numtype, (n, sx)?, nat, nat)
  | STORE(numtype, n?, nat, nat)
}

;; 1-syntax.watsup:156.1-157.9
syntax expr = instr*

;; 1-syntax.watsup:162.1-164.8
syntax elemmode =
  | TABLE(tableidx, expr)
  | DECLARE

;; 1-syntax.watsup:165.1-166.19
syntax datamode =
  | MEMORY(memidx, expr)

;; 1-syntax.watsup:168.1-169.30
syntax func = FUNC(functype, valtype*, expr)

;; 1-syntax.watsup:170.1-171.25
syntax global = GLOBAL(globaltype, expr)

;; 1-syntax.watsup:172.1-173.18
syntax table = TABLE(tabletype)

;; 1-syntax.watsup:174.1-175.14
syntax mem = MEM(memtype)

;; 1-syntax.watsup:176.1-177.31
syntax elem = ELEM(reftype, expr*, elemmode?)

;; 1-syntax.watsup:178.1-179.26
syntax data = DATA(byte**, datamode?)

;; 1-syntax.watsup:180.1-181.16
syntax start = START(funcidx)

;; 1-syntax.watsup:183.1-184.62
syntax externuse =
  | FUNC(funcidx)
  | GLOBAL(globalidx)
  | TABLE(tableidx)
  | MEM(memidx)

;; 1-syntax.watsup:185.1-186.24
syntax export = EXPORT(name, externuse)

;; 1-syntax.watsup:187.1-188.30
syntax import = IMPORT(name, name, externtype)

;; 1-syntax.watsup:190.1-191.70
syntax module = MODULE(import*, func*, global*, table*, mem*, elem*, data*, start*, export*)

;; 2-aux.watsup:5.1-5.41
def size : numtype -> nat
  ;; 2-aux.watsup:9.1-9.20
  def size(F64) = 64
  ;; 2-aux.watsup:8.1-8.20
  def size(F32) = 32
  ;; 2-aux.watsup:7.1-7.20
  def size(I64) = 64
  ;; 2-aux.watsup:6.1-6.20
  def size(I32) = 32

;; 2-aux.watsup:14.1-14.40
def test_sub_ATOM_22 : n -> nat
  ;; 2-aux.watsup:15.1-15.38
  def {n_3_ATOM_y : n} test_sub_ATOM_22(n_3_ATOM_y) = 0

;; 2-aux.watsup:17.1-17.26
def curried_ : (n, n) -> nat
  ;; 2-aux.watsup:18.1-18.39
  def {n_1 : n, n_2 : n} curried_(n_1, n_2) = (n_1 + n_2)

;; 2-aux.watsup:20.1-29.39
syntax testfuse =
  | AB_(nat, nat, nat)
  | CD(nat, nat, nat)
  | EF(nat, nat, nat)
  | GH(nat, nat, nat)
  | IJ(nat, nat, nat)
  | KL(nat, nat, nat)
  | MN(nat, nat, nat)
  | OP(nat, nat, nat)
  | QR(nat, nat, nat)

;; 3-typing.watsup:3.1-6.60
syntax context = {FUNC functype*, GLOBAL globaltype*, TABLE tabletype*, MEM memtype*, ELEM elemtype*, DATA datatype*, LOCAL valtype*, LABEL resulttype*, RETURN resulttype?}

;; 3-typing.watsup:14.1-14.64
relation Functype_ok: `|-%:OK`(functype)
  ;; 3-typing.watsup:20.1-21.13
  rule _ {ft : functype}:
    `|-%:OK`(ft)

;; 3-typing.watsup:15.1-15.66
relation Globaltype_ok: `|-%:OK`(globaltype)
  ;; 3-typing.watsup:23.1-24.13
  rule _ {gt : globaltype}:
    `|-%:OK`(gt)

;; 3-typing.watsup:18.1-18.66
relation Limits_ok: `|-%:%`(limits, nat)
  ;; 3-typing.watsup:34.1-36.25
  rule _ {k : nat, n_1 : n, n_2 : n}:
    `|-%:%`(`[%..%]`(n_1, n_2), k)
    -- iff ((n_1 <= n_2) /\ (n_2 <= k))

;; 3-typing.watsup:16.1-16.65
relation Tabletype_ok: `|-%:OK`(tabletype)
  ;; 3-typing.watsup:26.1-28.35
  rule _ {lim : limits, rt : reftype}:
    `|-%:OK`(`%%`(lim, rt))
    -- Limits_ok: `|-%:%`(lim, ((2 ^ 32) - 1))

;; 3-typing.watsup:17.1-17.63
relation Memtype_ok: `|-%:OK`(memtype)
  ;; 3-typing.watsup:30.1-32.33
  rule _ {lim : limits}:
    `|-%:OK`(`%I8`(lim))
    -- Limits_ok: `|-%:%`(lim, (2 ^ 16))

;; 3-typing.watsup:42.1-42.65
relation Valtype_sub: `|-%<:%`(valtype, valtype)
  ;; 3-typing.watsup:48.1-49.14
  rule bot {t : valtype}:
    `|-%<:%`(BOT, t)

  ;; 3-typing.watsup:45.1-46.12
  rule refl {t : valtype}:
    `|-%<:%`(t, t)

;; 3-typing.watsup:43.1-43.72
relation Resulttype_sub: `|-%<:%`(valtype*, valtype*)
  ;; 3-typing.watsup:51.1-53.35
  rule _ {t_1 : valtype, t_2 : valtype}:
    `|-%<:%`(t_1*, t_2*)
    -- (Valtype_sub: `|-%<:%`(t_1, t_2))*

;; 3-typing.watsup:56.1-56.73
relation Functype_sub: `|-%<:%`(functype, functype)
  ;; 3-typing.watsup:63.1-64.14
  rule _ {ft : functype}:
    `|-%<:%`(ft, ft)

;; 3-typing.watsup:57.1-57.75
relation Globaltype_sub: `|-%<:%`(globaltype, globaltype)
  ;; 3-typing.watsup:66.1-67.14
  rule _ {gt : globaltype}:
    `|-%<:%`(gt, gt)

;; 3-typing.watsup:60.1-60.75
relation Limits_sub: `|-%<:%`(limits, limits)
  ;; 3-typing.watsup:77.1-80.22
  rule _ {n_11 : n, n_12 : n, n_21 : n, n_22 : n}:
    `|-%<:%`(`[%..%]`(n_11, n_12), `[%..%]`(n_21, n_22))
    -- iff (n_11 >= n_21)
    -- iff (n_12 <= n_22)

;; 3-typing.watsup:58.1-58.74
relation Tabletype_sub: `|-%<:%`(tabletype, tabletype)
  ;; 3-typing.watsup:69.1-71.35
  rule _ {lim_1 : limits, lim_2 : limits, rt : reftype}:
    `|-%<:%`(`%%`(lim_1, rt), `%%`(lim_2, rt))
    -- Limits_sub: `|-%<:%`(lim_1, lim_2)

;; 3-typing.watsup:59.1-59.72
relation Memtype_sub: `|-%<:%`(memtype, memtype)
  ;; 3-typing.watsup:73.1-75.35
  rule _ {lim_1 : limits, lim_2 : limits}:
    `|-%<:%`(`%I8`(lim_1), `%I8`(lim_2))
    -- Limits_sub: `|-%<:%`(lim_1, lim_2)

;; 3-typing.watsup:61.1-61.75
relation Externtype_sub: `|-%<:%`(externtype, externtype)
  ;; 3-typing.watsup:94.1-96.34
  rule mem {mt_1 : memtype, mt_2 : memtype}:
    `|-%<:%`(MEM(mt_1), MEM(mt_2))
    -- Memtype_sub: `|-%<:%`(mt_1, mt_2)

  ;; 3-typing.watsup:90.1-92.36
  rule table {tt_1 : tabletype, tt_2 : tabletype}:
    `|-%<:%`(TABLE(tt_1), TABLE(tt_2))
    -- Tabletype_sub: `|-%<:%`(tt_1, tt_2)

  ;; 3-typing.watsup:86.1-88.37
  rule global {gt_1 : globaltype, gt_2 : globaltype}:
    `|-%<:%`(GLOBAL(gt_1), GLOBAL(gt_2))
    -- Globaltype_sub: `|-%<:%`(gt_1, gt_2)

  ;; 3-typing.watsup:82.1-84.35
  rule func {ft_1 : functype, ft_2 : functype}:
    `|-%<:%`(FUNC(ft_1), FUNC(ft_2))
    -- Functype_sub: `|-%<:%`(ft_1, ft_2)

;; 3-typing.watsup:144.1-144.76
relation Blocktype_ok: `%|-%:%`(context, blocktype, functype)
  ;; 3-typing.watsup:145.1-147.29
  rule _ {C : context, ft : functype}:
    `%|-%:%`(C, ft, ft)
    -- Functype_ok: `|-%:OK`(ft)

;; 3-typing.watsup:102.1-103.67
rec {

;; 3-typing.watsup:102.1-102.66
relation Instr_ok: `%|-%:%`(context, instr, functype)
  ;; 3-typing.watsup:205.1-206.37
  rule relop {C : context, nt : numtype, relop : relop_numtype}:
    `%|-%:%`(C, RELOP(nt, relop), `%->%`([(nt <: valtype)] :: [(nt <: valtype)], [I32]))

  ;; 3-typing.watsup:202.1-203.36
  rule testop {C : context, nt : numtype, testop : testop_numtype}:
    `%|-%:%`(C, TESTOP(nt, testop), `%->%`([(nt <: valtype)], [I32]))

  ;; 3-typing.watsup:199.1-200.36
  rule binop {C : context, binop : binop_numtype, nt : numtype}:
    `%|-%:%`(C, BINOP(nt, binop), `%->%`([(nt <: valtype)] :: [(nt <: valtype)], [(nt <: valtype)]))

  ;; 3-typing.watsup:196.1-197.31
  rule unop {C : context, nt : numtype, unop : unop_numtype}:
    `%|-%:%`(C, UNOP(nt, unop), `%->%`([(nt <: valtype)], [(nt <: valtype)]))

  ;; 3-typing.watsup:193.1-194.37
  rule const {C : context, c_nt : c_numtype, nt : numtype}:
    `%|-%:%`(C, CONST(nt, c_nt), `%->%`([], [(nt <: valtype)]))

  ;; 3-typing.watsup:187.1-190.27
  rule call_indirect {C : context, ft : functype, lim : limits, t_1 : valtype, t_2 : valtype, x : idx}:
    `%|-%:%`(C, CALL_INDIRECT(x, ft), `%->%`(t_1* :: [I32], t_2*))
    -- iff (C.TABLE[x] = `%%`(lim, FUNCREF))
    -- iff (ft = `%->%`(t_1*, t_2*))

  ;; 3-typing.watsup:183.1-185.34
  rule call {C : context, t_1 : valtype, t_2 : valtype, x : idx}:
    `%|-%:%`(C, CALL(x), `%->%`(t_1*, t_2*))
    -- iff (C.FUNC[x] = `%->%`(t_1*, t_2*))

  ;; 3-typing.watsup:179.1-181.25
  rule return {C : context, t : valtype, t_1 : valtype, t_2 : valtype}:
    `%|-%:%`(C, RETURN, `%->%`(t_1* :: t*, t_2*))
    -- iff (C.RETURN = ?(t*))

  ;; 3-typing.watsup:174.1-177.42
  rule br_table {C : context, l : labelidx, l' : labelidx, t : valtype, t_1 : valtype, t_2 : valtype}:
    `%|-%:%`(C, BR_TABLE(l*, l'), `%->%`(t_1* :: t*, t_2*))
    -- (Resulttype_sub: `|-%<:%`(t*, C.LABEL[l]))*
    -- Resulttype_sub: `|-%<:%`(t*, C.LABEL[l'])

  ;; 3-typing.watsup:170.1-172.25
  rule br_if {C : context, l : labelidx, t : valtype}:
    `%|-%:%`(C, BR_IF(l), `%->%`(t* :: [I32], t*))
    -- iff (C.LABEL[l] = t*)

  ;; 3-typing.watsup:166.1-168.25
  rule br {C : context, l : labelidx, t : valtype, t_1 : valtype, t_2 : valtype}:
    `%|-%:%`(C, BR(l), `%->%`(t_1* :: t*, t_2*))
    -- iff (C.LABEL[l] = t*)

  ;; 3-typing.watsup:159.1-163.59
  rule if {C : context, bt : blocktype, instr_1 : instr, instr_2 : instr, t_1 : valtype, t_2 : valtype}:
    `%|-%:%`(C, IF(bt, instr_1*, instr_2*), `%->%`(t_1*, [t_2]))
    -- Blocktype_ok: `%|-%:%`(C, bt, `%->%`(t_1*, [t_2]))
    -- InstrSeq_ok: `%|-%:%`(C ++ {FUNC [], GLOBAL [], TABLE [], MEM [], ELEM [], DATA [], LOCAL [], LABEL [t_2]*, RETURN ?()}, instr_1*, `%->%`(t_1*, t_2*))
    -- InstrSeq_ok: `%|-%:%`(C ++ {FUNC [], GLOBAL [], TABLE [], MEM [], ELEM [], DATA [], LOCAL [], LABEL [t_2]*, RETURN ?()}, instr_2*, `%->%`(t_1*, t_2*))

  ;; 3-typing.watsup:154.1-157.56
  rule loop {C : context, bt : blocktype, instr : instr, t_1 : valtype, t_2 : valtype}:
    `%|-%:%`(C, LOOP(bt, instr*), `%->%`(t_1*, t_2*))
    -- Blocktype_ok: `%|-%:%`(C, bt, `%->%`(t_1*, t_2*))
    -- InstrSeq_ok: `%|-%:%`(C ++ {FUNC [], GLOBAL [], TABLE [], MEM [], ELEM [], DATA [], LOCAL [], LABEL [t_1]*, RETURN ?()}, instr*, `%->%`(t_1*, [t_2]))

  ;; 3-typing.watsup:149.1-152.57
  rule block {C : context, bt : blocktype, instr : instr, t_1 : valtype, t_2 : valtype}:
    `%|-%:%`(C, BLOCK(bt, instr*), `%->%`(t_1*, t_2*))
    -- Blocktype_ok: `%|-%:%`(C, bt, `%->%`(t_1*, t_2*))
    -- InstrSeq_ok: `%|-%:%`(C ++ {FUNC [], GLOBAL [], TABLE [], MEM [], ELEM [], DATA [], LOCAL [], LABEL [t_2]*, RETURN ?()}, instr*, `%->%`(t_1*, t_2*))

  ;; 3-typing.watsup:138.1-141.38
  rule select-impl {C : context, numtype : numtype, t : valtype, t' : valtype, vectype : vectype}:
    `%|-%:%`(C, SELECT(?()), `%->%`([t] :: [t] :: [I32], [t]))
    -- Valtype_sub: `|-%<:%`(t, t')
    -- iff ((t' = (numtype <: valtype)) \/ (t' = (vectype <: valtype)))

  ;; 3-typing.watsup:135.1-136.31
  rule select-expl {C : context, t : valtype}:
    `%|-%:%`(C, SELECT(?(t)), `%->%`([t] :: [t] :: [I32], [t]))

  ;; 3-typing.watsup:131.1-132.27
  rule drop {C : context, t : valtype}:
    `%|-%:%`(C, DROP, `%->%`([t], []))

  ;; 3-typing.watsup:128.1-129.32
  rule nop {C : context}:
    `%|-%:%`(C, NOP, `%->%`([], []))

  ;; 3-typing.watsup:125.1-126.34
  rule unreachable {C : context, t_1 : valtype, t_2 : valtype}:
    `%|-%:%`(C, UNREACHABLE, `%->%`(t_1*, t_2*))

;; 3-typing.watsup:103.1-103.67
relation InstrSeq_ok: `%|-%:%`(context, instr*, functype)
  ;; 3-typing.watsup:120.1-122.45
  rule frame {C : context, instr : instr, t : valtype, t_1 : valtype, t_2 : valtype}:
    `%|-%:%`(C, instr*, `%->%`(t* :: t_1*, t* :: t_2*))
    -- InstrSeq_ok: `%|-%:%`(C, instr*, `%->%`(t_1*, t_2*))

  ;; 3-typing.watsup:113.1-118.38
  rule weak {C : context, instr : instr, t'_1 : valtype, t'_2 : valtype, t_1 : valtype, t_2 : valtype}:
    `%|-%:%`(C, instr*, `%->%`([t'_1], t'_2*))
    -- InstrSeq_ok: `%|-%:%`(C, instr*, `%->%`(t_1*, t_2*))
    -- Resulttype_sub: `|-%<:%`(t'_1*, t_1*)
    -- Resulttype_sub: `|-%<:%`(t_2*, t'_2*)

  ;; 3-typing.watsup:108.1-111.46
  rule seq {C : context, instr_1 : instr, instr_2 : instr, t_1 : valtype, t_2 : valtype, t_3 : valtype}:
    `%|-%:%`(C, [instr_1] :: instr_2*, `%->%`(t_1*, t_3*))
    -- Instr_ok: `%|-%:%`(C, instr_1, `%->%`(t_1*, t_2*))
    -- InstrSeq_ok: `%|-%:%`(C, [instr_2], `%->%`(t_2*, t_3*))

  ;; 3-typing.watsup:105.1-106.36
  rule empty {C : context}:
    `%|-%:%`(C, [], `%->%`([], []))
}

;; 3-typing.watsup:214.1-214.67
relation Instr_const: `%|-%CONST`(context, instr)
  ;; 3-typing.watsup:226.1-228.33
  rule global.get {C : context, t : valtype, x : idx}:
    `%|-%CONST`(C, GLOBAL.GET(x))
    -- iff (C.GLOBAL[x] = `MUT%?%`(?(), t))

  ;; 3-typing.watsup:223.1-224.26
  rule ref.func {C : context, x : idx}:
    `%|-%CONST`(C, REF.FUNC(x))

  ;; 3-typing.watsup:220.1-221.27
  rule ref.null {C : context, rt : reftype}:
    `%|-%CONST`(C, REF.NULL(rt))

  ;; 3-typing.watsup:217.1-218.26
  rule const {C : context, c : c_numtype, nt : numtype}:
    `%|-%CONST`(C, CONST(nt, c))

;; 3-typing.watsup:215.1-215.66
relation Expr_const: `%|-%CONST`(context, instr*)
  ;; 3-typing.watsup:231.1-232.38
  rule _ {C : context, instr : instr}:
    `%|-%CONST`(C, instr*)
    -- (Instr_const: `%|-%CONST`(C, instr))*

;; 4-runtime.watsup:3.1-3.39
syntax addr = nat

;; 4-runtime.watsup:4.1-4.53
syntax funcaddr = addr

;; 4-runtime.watsup:5.1-5.53
syntax globaladdr = addr

;; 4-runtime.watsup:6.1-6.51
syntax tableaddr = addr

;; 4-runtime.watsup:7.1-7.50
syntax memaddr = addr

;; 4-runtime.watsup:8.1-8.49
syntax elemaddr = addr

;; 4-runtime.watsup:9.1-9.49
syntax dataaddr = addr

;; 4-runtime.watsup:10.1-10.51
syntax labeladdr = addr

;; 4-runtime.watsup:11.1-11.49
syntax hostaddr = addr

;; 4-runtime.watsup:24.1-25.24
syntax num =
  | CONST(numtype, c_numtype)

;; 4-runtime.watsup:26.1-27.67
syntax ref =
  | REF.NULL(reftype)
  | REF.FUNC_ADDR(funcaddr)
  | REF.HOST_ADDR(hostaddr)

;; 4-runtime.watsup:28.1-29.10
syntax val =
  | num
  | ref

;; 4-runtime.watsup:31.1-32.18
syntax result =
  | _VALS(val*)
  | TRAP

;; 4-runtime.watsup:38.1-39.66
syntax externval =
  | FUNC(funcaddr)
  | GLOBAL(globaladdr)
  | TABLE(tableaddr)
  | MEM(memaddr)

;; 4-runtime.watsup:44.1-44.29
def default_ : valtype -> val
  ;; 4-runtime.watsup:49.1-49.34
  def {rt : reftype} default_(rt <: valtype) = REF.NULL(rt)
  ;; 4-runtime.watsup:48.1-48.35
  def default_(F64) = CONST(F64, 0)
  ;; 4-runtime.watsup:47.1-47.35
  def default_(F32) = CONST(F32, 0)
  ;; 4-runtime.watsup:46.1-46.35
  def default_(I64) = CONST(I64, 0)
  ;; 4-runtime.watsup:45.1-45.35
  def default_(I32) = CONST(I32, 0)

;; 4-runtime.watsup:60.1-60.71
syntax exportinst = EXPORT(name, externval)

;; 4-runtime.watsup:70.1-77.25
syntax moduleinst = {FUNC funcaddr*, GLOBAL globaladdr*, TABLE tableaddr*, MEM memaddr*, ELEM elemaddr*, DATA dataaddr*, EXPORT exportinst*}

;; 4-runtime.watsup:54.1-54.66
syntax funcinst = `%;%`(moduleinst, func)

;; 4-runtime.watsup:55.1-55.53
syntax globalinst = val

;; 4-runtime.watsup:56.1-56.52
syntax tableinst = ref*

;; 4-runtime.watsup:57.1-57.52
syntax meminst = byte*

;; 4-runtime.watsup:58.1-58.53
syntax eleminst = ref*

;; 4-runtime.watsup:59.1-59.51
syntax datainst = byte*

;; 4-runtime.watsup:62.1-68.21
syntax store = {FUNC funcinst*, GLOBAL globalinst*, TABLE tableinst*, MEM meminst*, ELEM eleminst*, DATA datainst*}

;; 4-runtime.watsup:79.1-79.51
syntax frame = `%;%`(moduleinst, val*)

;; 4-runtime.watsup:80.1-80.47
syntax state = `%;%`(store, frame)

;; 4-runtime.watsup:111.1-118.5
rec {

;; 4-runtime.watsup:111.1-118.5
syntax admininstr =
  | instr
  | REF.FUNC_ADDR(funcaddr)
  | REF.HOST_ADDR(hostaddr)
  | CALL_ADDR(funcaddr)
  | LABEL_(n, instr*, admininstr*)
  | FRAME_(n, frame, admininstr*)
  | TRAP
}

;; 4-runtime.watsup:81.1-81.62
syntax config = `%;%`(state, admininstr*)

;; 4-runtime.watsup:96.1-96.52
def funcaddr : state -> funcaddr*
  ;; 4-runtime.watsup:97.1-97.39
  def {m : moduleinst, s : store, val : val} funcaddr(`%;%`(s, `%;%`(m, val*))) = m.FUNC

;; 4-runtime.watsup:99.1-99.52
def funcinst : state -> funcinst*
  ;; 4-runtime.watsup:100.1-100.31
  def {f : frame, s : store} funcinst(`%;%`(s, f)) = s.FUNC

;; 4-runtime.watsup:102.1-102.61
def func : (state, funcidx) -> funcinst
  ;; 4-runtime.watsup:103.1-103.49
  def {m : moduleinst, s : store, val : val, x : idx} func(`%;%`(s, `%;%`(m, val*)), x) = s.FUNC[m.FUNC[x]]

;; 4-runtime.watsup:105.1-105.65
def table : (state, tableidx) -> tableinst
  ;; 4-runtime.watsup:106.1-106.52
  def {m : moduleinst, s : store, val : val, x : idx} table(`%;%`(s, `%;%`(m, val*)), x) = s.TABLE[m.TABLE[x]]

;; 4-runtime.watsup:120.1-123.21
rec {

;; 4-runtime.watsup:120.1-123.21
syntax E =
  | _HOLE
  | _SEQ(val*, E, instr*)
  | LABEL_(n, instr*, E)
}

;; 5-reduction.watsup:5.1-5.63
relation Step_pure: `%~>%`(admininstr*, admininstr*)
  ;; 5-reduction.watsup:70.1-72.19
  rule br_table-le {i : nat, l : labelidx, l' : labelidx}:
    `%~>%`([CONST(I32, i) BR_TABLE(l*, l')], [BR(l')])
    -- iff (i >= |l*|)

  ;; 5-reduction.watsup:66.1-68.18
  rule br_table-lt {i : nat, l : labelidx, l' : labelidx}:
    `%~>%`([CONST(I32, i) BR_TABLE(l*, l')], [BR(l*[i])])
    -- iff (i < |l*|)

  ;; 5-reduction.watsup:61.1-63.15
  rule br_if-false {c : c_numtype, l : labelidx}:
    `%~>%`([CONST(I32, c) BR_IF(l)], [])
    -- iff (c = 0)

  ;; 5-reduction.watsup:57.1-59.17
  rule br_if-true {c : c_numtype, l : labelidx}:
    `%~>%`([CONST(I32, c) BR_IF(l)], [BR(l)])
    -- iff (c =/= 0)

  ;; 5-reduction.watsup:53.1-54.65
  rule br-succ {instr : instr, instr' : instr, l : labelidx, n : n, val : val}:
    `%~>%`([LABEL_(n, instr'*, (val <: admininstr)* :: [BR(l + 1)] :: (instr <: admininstr)*)], (val <: admininstr)* :: [BR(l)])

  ;; 5-reduction.watsup:50.1-51.69
  rule br-zero {instr : instr, instr' : instr, n : n, val : val, val' : val}:
    `%~>%`([LABEL_(n, instr'*, (val' <: admininstr)* :: (val <: admininstr)^n :: [BR(0)] :: (instr <: admininstr)*)], (val <: admininstr)^n :: (instr' <: admininstr)*)

  ;; 5-reduction.watsup:45.1-47.15
  rule if-false {bt : blocktype, c : c_numtype, instr_1 : instr, instr_2 : instr}:
    `%~>%`([CONST(I32, c) IF(bt, instr_1*, instr_2*)], [BLOCK(bt, instr_2*)])
    -- iff (c = 0)

  ;; 5-reduction.watsup:41.1-43.17
  rule if-true {bt : blocktype, c : c_numtype, instr_1 : instr, instr_2 : instr}:
    `%~>%`([CONST(I32, c) IF(bt, instr_1*, instr_2*)], [BLOCK(bt, instr_1*)])
    -- iff (c =/= 0)

  ;; 5-reduction.watsup:37.1-39.29
  rule loop {bt : blocktype, instr : instr, k : nat, n : n, t_1 : valtype, t_2 : valtype, val : val}:
    `%~>%`((val <: admininstr)^k :: [LOOP(bt, instr*)], [LABEL_(n, [LOOP(bt, instr*)], (val <: admininstr)^k :: (instr <: admininstr)*)])
    -- iff (bt = `%->%`(t_1^k, t_2^n))

  ;; 5-reduction.watsup:33.1-35.29
  rule block {bt : blocktype, instr : instr, k : nat, n : n, t_1 : valtype, t_2 : valtype, val : val}:
    `%~>%`((val <: admininstr)^k :: [BLOCK(bt, instr*)], [LABEL_(n, [], (val <: admininstr)^k :: (instr <: admininstr)*)])
    -- iff (bt = `%->%`(t_1^k, t_2^n))

  ;; 5-reduction.watsup:29.1-31.15
  rule select-false {c : c_numtype, t : valtype, val_1 : val, val_2 : val}:
    `%~>%`([(val_1 <: admininstr)] :: [(val_2 <: admininstr)] :: [CONST(I32, c) SELECT(t?)], [(val_2 <: admininstr)])
    -- iff (c = 0)

  ;; 5-reduction.watsup:25.1-27.17
  rule select-true {c : c_numtype, t : valtype, val_1 : val, val_2 : val}:
    `%~>%`([(val_1 <: admininstr)] :: [(val_2 <: admininstr)] :: [CONST(I32, c) SELECT(t?)], [(val_1 <: admininstr)])
    -- iff (c =/= 0)

  ;; 5-reduction.watsup:22.1-23.24
  rule drop {val : val}:
    `%~>%`([(val <: admininstr)] :: [DROP], [])

  ;; 5-reduction.watsup:19.1-20.19
  rule nop:
    `%~>%`([NOP], [])

  ;; 5-reduction.watsup:16.1-17.24
  rule unreachable:
    `%~>%`([UNREACHABLE], [TRAP])

;; 5-reduction.watsup:4.1-4.63
relation Step_read: `%~>%`(config, admininstr*)
  ;; 5-reduction.watsup:87.1-89.62
  rule call_addr {a : addr, instr : instr, k : nat, m : moduleinst, n : n, t : valtype, t_1 : valtype, t_2 : valtype, val : val, z : state}:
    `%~>%`(`%;%`(z, (val <: admininstr)^k :: [CALL_ADDR(a)]), [FRAME_(n, `%;%`(m, val^k :: $default_(t)*), [LABEL_(n, [], (instr <: admininstr)*)])])
    -- iff ($funcinst(z)[a] = `%;%`(m, FUNC(`%->%`(t_1^k, t_2^n), t*, instr*)))

  ;; 5-reduction.watsup:83.1-85.15
  rule call_indirect-trap {ft : functype, i : nat, x : idx, z : state}:
    `%~>%`(`%;%`(z, [CONST(I32, i) CALL_INDIRECT(x, ft)]), [TRAP])
    -- otherwise

  ;; 5-reduction.watsup:78.1-81.35
  rule call_indirect-call {a : addr, ft : functype, func : func, i : nat, m : moduleinst, x : idx, z : state}:
    `%~>%`(`%;%`(z, [CONST(I32, i) CALL_INDIRECT(x, ft)]), [CALL_ADDR(a)])
    -- iff ($table(z, x)[i] = REF.FUNC_ADDR(a))
    -- iff ($funcinst(z)[a] = `%;%`(m, func))

  ;; 5-reduction.watsup:75.1-76.47
  rule call {x : idx, z : state}:
    `%~>%`(`%;%`(z, [CALL(x)]), [CALL_ADDR($funcaddr(z)[x])])

;; 5-reduction.watsup:3.1-3.63
relation Step: `%~>%`(config, config)
  ;; 5-reduction.watsup:11.1-13.37
  rule read {instr : instr, instr' : instr, z : state}:
    `%~>%`(`%;%`(z, (instr <: admininstr)*), `%;%`(z, (instr' <: admininstr)*))
    -- Step_read: `%~>%`(`%;%`(z, (instr <: admininstr)*), (instr' <: admininstr)*)

  ;; 5-reduction.watsup:7.1-9.34
  rule pure {instr : instr, instr' : instr, z : state}:
    `%~>%`(`%;%`(z, (instr <: admininstr)*), `%;%`(z, (instr' <: admininstr)*))
    -- Step_pure: `%~>%`((instr <: admininstr)*, (instr' <: admininstr)*)

== IL Validation...
== Latex Generation...
$$
\begin{array}{@{}lrrl@{}}
& \mathit{n} &::=& \mathit{nat} \\
\end{array}
$$

$$
\begin{array}{@{}lrrl@{}}
\mbox{(name)} & \mathit{name} &::=& \mathit{text} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lrrl@{}}
\mbox{(byte)} & \mathit{byte} &::=& \mathit{nat} \\
\mbox{(32-bit integer)} & \mathit{u32} &::=& \mathit{nat} \\
\mbox{(index)} & \mathit{idx} &::=& \mathit{nat} \\
\mbox{(function index)} & \mathit{funcidx} &::=& \mathit{idx} \\
\mbox{(global index)} & \mathit{globalidx} &::=& \mathit{idx} \\
\mbox{(table index)} & \mathit{tableidx} &::=& \mathit{idx} \\
\mbox{(memory index)} & \mathit{memidx} &::=& \mathit{idx} \\
\mbox{(elem index)} & \mathit{elemidx} &::=& \mathit{idx} \\
\mbox{(data index)} & \mathit{dataidx} &::=& \mathit{idx} \\
\mbox{(label index)} & \mathit{labelidx} &::=& \mathit{idx} \\
\mbox{(local index)} & \mathit{localidx} &::=& \mathit{idx} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lrrl@{}}
\mbox{(number type)} & \mathit{numtype} &::=& \mathsf{i32} ~|~ \mathsf{i64} ~|~ \mathsf{f32} ~|~ \mathsf{f64} \\
\mbox{(vector type)} & \mathit{vectype} &::=& \mathsf{v128} \\
\mbox{(reference type)} & \mathit{reftype} &::=& \mathsf{funcref} ~|~ \mathsf{externref} \\
\mbox{(value type)} & \mathit{valtype} &::=& \mathit{numtype} ~|~ \mathit{vectype} ~|~ \mathit{reftype} ~|~ \mathsf{bot} \\
\end{array}
$$

$$
\begin{array}{@{}lrrl@{}}
\mbox{(result type)} & \mathit{resulttype} &::=& \mathit{valtype}^\ast \\
\mbox{(limits)} & \mathit{limits} &::=& [\mathit{u32} .. \mathit{u32}] \\
\mbox{(global type)} & \mathit{globaltype} &::=& \mathsf{mut}^?~\mathit{valtype} \\
\mbox{(function type)} & \mathit{functype} &::=& \mathit{resulttype} \rightarrow \mathit{resulttype} \\
\mbox{(table type)} & \mathit{tabletype} &::=& \mathit{limits}~\mathit{reftype} \\
\mbox{(memory type)} & \mathit{memtype} &::=& \mathit{limits}~\mathsf{i8} \\
\mbox{(element type)} & \mathit{elemtype} &::=& \mathit{reftype} \\
\mbox{(data type)} & \mathit{datatype} &::=& \mathsf{ok} \\
\mbox{(external type)} & \mathit{externtype} &::=& \mathsf{global}~\mathit{globaltype} ~|~ \mathsf{func}~\mathit{functype} ~|~ \mathsf{table}~\mathit{tabletype} ~|~ \mathsf{mem}~\mathit{memtype} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lrrl@{}}
& \mathit{c}_{\mathit{numtype}} &::=& \mathit{nat} \\
& \mathit{c}_{\mathit{vectype}} &::=& \mathit{nat} \\
\end{array}
$$

$$
\begin{array}{@{}lrrl@{}}
\mbox{(signedness)} & \mathit{sx} &::=& \mathsf{u} ~|~ \mathsf{s} \\
\mbox{(block type)} & \mathit{blocktype} &::=& \mathit{functype} \\
\end{array}
$$

$$
\begin{array}{@{}lrrl@{}}
& \mathit{unop}_{\mathit{numtype}} &::=& \mathsf{xxx} \\
& \mathit{binop}_{\mathit{numtype}} &::=& \mathsf{xxx} \\
& \mathit{testop}_{\mathit{numtype}} &::=& \mathsf{xxx} \\
& \mathit{relop}_{\mathit{numtype}} &::=& \mathsf{xxx} \\
& \mathit{cvtop} &::=& \mathsf{xxx} \\
\end{array}
$$

$$
\begin{array}{@{}lrrl@{}}
& \mathit{instr} &::=& \mathsf{unreachable} \\ &&|&
\mathsf{nop} \\ &&|&
\mathsf{drop} \\ &&|&
\mathsf{select}~\mathit{valtype}^? \\ &&|&
\mathsf{block}~\mathit{blocktype}~\mathit{instr}^\ast \\ &&|&
\mathsf{loop}~\mathit{blocktype}~\mathit{instr}^\ast \\ &&|&
\mathsf{if}~\mathit{blocktype}~\mathit{instr}^\ast~\mathsf{else}~\mathit{instr}^\ast \\ &&|&
\mathsf{br}~\mathit{labelidx} \\ &&|&
\mathsf{br\_if}~\mathit{labelidx} \\ &&|&
\mathsf{br\_table}~\mathit{labelidx}^\ast~\mathit{labelidx} \\ &&|&
\mathsf{call}~\mathit{funcidx} \\ &&|&
\mathsf{call\_indirect}~\mathit{tableidx}~\mathit{functype} \\ &&|&
\mathsf{return} \\ &&|&
\mathsf{\mathit{numtype}}.\mathsf{const}~\mathsf{\mathit{c}\_{\mathit{numtype}}} \\ &&|&
\mathsf{\mathit{numtype}} . \mathsf{\mathit{unop}\_{\mathit{numtype}}} \\ &&|&
\mathsf{\mathit{numtype}} . \mathsf{\mathit{binop}\_{\mathit{numtype}}} \\ &&|&
\mathsf{\mathit{numtype}} . \mathsf{\mathit{testop}\_{\mathit{numtype}}} \\ &&|&
\mathsf{\mathit{numtype}} . \mathsf{\mathit{relop}\_{\mathit{numtype}}} \\ &&|&
{\mathsf{\mathit{numtype}}.\mathsf{extend}}{\mathsf{\mathit{n}}} \\ &&|&
\mathsf{\mathit{numtype}} . {{{{\mathsf{\mathit{cvtop}}}{\mathsf{\_}}}{\mathsf{\mathit{numtype}}}}{\mathsf{\_}}}{\mathsf{\mathit{sx}^?}} \\ &&|&
\mathsf{ref.null}~\mathit{reftype} \\ &&|&
\mathsf{ref.func}~\mathit{funcidx} \\ &&|&
\mathsf{ref.is\_null} \\ &&|&
\mathsf{local.get}~\mathit{localidx} \\ &&|&
\mathsf{local.set}~\mathit{localidx} \\ &&|&
\mathsf{local.tee}~\mathit{localidx} \\ &&|&
\mathsf{global.get}~\mathit{globalidx} \\ &&|&
\mathsf{global.set}~\mathit{globalidx} \\ &&|&
\mathsf{table.get}~\mathit{tableidx} \\ &&|&
\mathsf{table.set}~\mathit{tableidx} \\ &&|&
\mathsf{table.size}~\mathit{tableidx} \\ &&|&
\mathsf{table.grow}~\mathit{tableidx} \\ &&|&
\mathsf{table.fill}~\mathit{tableidx} \\ &&|&
\mathsf{table.copy}~\mathit{tableidx}~\mathit{tableidx} \\ &&|&
\mathsf{table.init}~\mathit{tableidx}~\mathit{elemidx} \\ &&|&
\mathsf{elem.drop}~\mathit{elemidx} \\ &&|&
\mathsf{memory.size} \\ &&|&
\mathsf{memory.grow} \\ &&|&
\mathsf{memory.fill} \\ &&|&
\mathsf{memory.copy} \\ &&|&
\mathsf{memory.init}~\mathit{dataidx} \\ &&|&
\mathsf{data.drop}~\mathit{dataidx} \\ &&|&
{\mathsf{\mathit{numtype}}.\mathsf{load}}{\mathsf{(\mathit{n}~\mathit{sx})^?}~\mathsf{\mathit{nat}}~\mathsf{\mathit{nat}}} \\ &&|&
{\mathsf{\mathit{numtype}}.\mathsf{store}}{\mathsf{\mathit{n}^?}~\mathsf{\mathit{nat}}~\mathsf{\mathit{nat}}} \\
\mbox{(expression)} & \mathit{expr} &::=& \mathit{instr}^\ast \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lrrl@{}}
& \mathit{elemmode} &::=& \mathsf{table}~\mathit{tableidx}~\mathit{expr} \\ &&|&
\mathsf{declare} \\
& \mathit{datamode} &::=& \mathsf{memory}~\mathit{memidx}~\mathit{expr} \\
\mbox{(function)} & \mathit{func} &::=& \mathsf{func}~\mathit{functype}~\mathit{valtype}^\ast~\mathit{expr} \\
\mbox{(global)} & \mathit{global} &::=& \mathsf{global}~\mathit{globaltype}~\mathit{expr} \\
\mbox{(table)} & \mathit{table} &::=& \mathsf{table}~\mathit{tabletype} \\
\mbox{(memory)} & \mathit{mem} &::=& \mathsf{mem}~\mathit{memtype} \\
\mbox{(table segment)} & \mathit{elem} &::=& \mathsf{elem}~\mathit{reftype}~\mathit{expr}^\ast~\mathit{elemmode}^? \\
\mbox{(memory segment)} & \mathit{data} &::=& \mathsf{data}~(\mathit{byte}^\ast)^\ast~\mathit{datamode}^? \\
\mbox{(start function)} & \mathit{start} &::=& \mathsf{start}~\mathit{funcidx} \\
\mbox{(external use)} & \mathit{externuse} &::=& \mathsf{func}~\mathit{funcidx} ~|~ \mathsf{global}~\mathit{globalidx} ~|~ \mathsf{table}~\mathit{tableidx} ~|~ \mathsf{mem}~\mathit{memidx} \\
\mbox{(export)} & \mathit{export} &::=& \mathsf{export}~\mathit{name}~\mathit{externuse} \\
\mbox{(import)} & \mathit{import} &::=& \mathsf{import}~\mathit{name}~\mathit{name}~\mathit{externtype} \\
\mbox{(module)} & \mathit{module} &::=& \mathsf{module}~\mathit{import}^\ast~\mathit{func}^\ast~\mathit{global}^\ast~\mathit{table}^\ast~\mathit{mem}^\ast~\mathit{elem}^\ast~\mathit{data}^\ast~\mathit{start}^\ast~\mathit{export}^\ast \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{|\mathsf{i32}|} &=& 32 &  \\
{|\mathsf{i64}|} &=& 64 &  \\
{|\mathsf{f32}|} &=& 32 &  \\
{|\mathsf{f64}|} &=& 64 &  \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lcl@{}l@{}}
\mathrm{test}_{\mathit{sub}_{\mathsf{atom}_{22}}}(\mathit{n}_{3_{\mathsf{atom}_{\mathit{y}}}}) &=& 0 &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
\mathrm{curried}_{\mathit{n}_{1}}(\mathit{n}_{2}) &=& \mathit{n}_{1} + \mathit{n}_{2} &  \\
\end{array}
$$

$$
\begin{array}{@{}lrrl@{}}
& \mathit{testfuse} &::=& \mathsf{ab}_{\mathit{nat}}\,\,\mathit{nat}~\mathit{nat} \\ &&|&
\mathsf{cd}_{\mathsf{\mathit{nat}}}\,\mathsf{\mathit{nat}}~\mathsf{\mathit{nat}} \\ &&|&
{\mathsf{ef\_}}{\mathsf{\mathit{nat}}~\mathsf{\mathit{nat}}~\mathsf{\mathit{nat}}} \\ &&|&
{\mathsf{gh}_{\mathsf{\mathit{nat}}}}{\mathsf{\mathit{nat}}~\mathsf{\mathit{nat}}} \\ &&|&
{\mathsf{ij}_{\mathsf{\mathit{nat}}}}{\mathsf{\mathit{nat}}~\mathsf{\mathit{nat}}} \\ &&|&
{\mathsf{kl\_ab}}{\mathsf{\mathit{nat}}~\mathsf{\mathit{nat}}~\mathsf{\mathit{nat}}} \\ &&|&
{\mathsf{mn\_}}{\mathsf{ab}~\mathsf{\mathit{nat}}~\mathsf{\mathit{nat}}~\mathsf{\mathit{nat}}} \\ &&|&
{{\mathsf{op\_}}{\mathsf{ab}}}{\mathsf{\mathit{nat}}~\mathsf{\mathit{nat}}~\mathsf{\mathit{nat}}} \\ &&|&
{\mathsf{qr}_{\mathsf{\mathit{nat}}}}{\mathsf{ab}~\mathsf{\mathit{nat}}~\mathsf{\mathit{nat}}} \\
\mbox{(context)} & \mathit{context} &::=& \{\; \begin{array}[t]{@{}l@{}}
\mathsf{func}~\mathit{functype}^\ast,\; \mathsf{global}~\mathit{globaltype}^\ast,\; \mathsf{table}~\mathit{tabletype}^\ast,\; \mathsf{mem}~\mathit{memtype}^\ast,\; \\
  \mathsf{elem}~\mathit{elemtype}^\ast,\; \mathsf{data}~\mathit{datatype}^\ast,\; \\
  \mathsf{local}~\mathit{valtype}^\ast,\; \mathsf{label}~\mathit{resulttype}^\ast,\; \mathsf{return}~\mathit{resulttype}^? \;\}\end{array} \\
\end{array}
$$

\vspace{1ex}

$\boxed{{ \vdash }\;\mathit{functype} : \mathsf{ok}}$

$\boxed{{ \vdash }\;\mathit{globaltype} : \mathsf{ok}}$

$\boxed{{ \vdash }\;\mathit{tabletype} : \mathsf{ok}}$

$\boxed{{ \vdash }\;\mathit{memtype} : \mathsf{ok}}$

$\boxed{{ \vdash }\;\mathit{limits} : \mathit{nat}}$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{ \vdash }\;\mathit{ft} : \mathsf{ok}
} \, {[\textsc{\scriptsize K-func}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{ \vdash }\;\mathit{gt} : \mathsf{ok}
} \, {[\textsc{\scriptsize K-global}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{ \vdash }\;\mathit{lim} : 2^{32} - 1
}{
{ \vdash }\;\mathit{lim}~\mathit{rt} : \mathsf{ok}
} \, {[\textsc{\scriptsize K-table}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{ \vdash }\;\mathit{lim} : 2^{16}
}{
{ \vdash }\;\mathit{lim}~\mathsf{i8} : \mathsf{ok}
} \, {[\textsc{\scriptsize K-mem}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
\mathit{n}_{1} \leq \mathit{n}_{2} \leq \mathit{k}
}{
{ \vdash }\;[\mathit{n}_{1} .. \mathit{n}_{2}] : \mathit{k}
} \, {[\textsc{\scriptsize K-limits}]}
\qquad
\end{array}
$$

\vspace{1ex}

$\boxed{{ \vdash }\;\mathit{valtype} \leq \mathit{valtype}}$

$\boxed{{ \vdash }\;\mathit{valtype}^\ast \leq \mathit{valtype}^\ast}$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{ \vdash }\;\mathit{t} \leq \mathit{t}
} \, {[\textsc{\scriptsize S-refl}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{ \vdash }\;\mathsf{bot} \leq \mathit{t}
} \, {[\textsc{\scriptsize S-bot}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
({ \vdash }\;\mathit{t}_{1} \leq \mathit{t}_{2})^\ast
}{
{ \vdash }\;\mathit{t}_{1}^\ast \leq \mathit{t}_{2}^\ast
} \, {[\textsc{\scriptsize S-result}]}
\qquad
\end{array}
$$

\vspace{1ex}

$\boxed{{ \vdash }\;\mathit{functype} \leq \mathit{functype}}$

$\boxed{{ \vdash }\;\mathit{globaltype} \leq \mathit{globaltype}}$

$\boxed{{ \vdash }\;\mathit{tabletype} \leq \mathit{tabletype}}$

$\boxed{{ \vdash }\;\mathit{memtype} \leq \mathit{memtype}}$

$\boxed{{ \vdash }\;\mathit{limits} \leq \mathit{limits}}$

$\boxed{{ \vdash }\;\mathit{externtype} \leq \mathit{externtype}}$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{ \vdash }\;\mathit{ft} \leq \mathit{ft}
} \, {[\textsc{\scriptsize S-func}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
{ \vdash }\;\mathit{gt} \leq \mathit{gt}
} \, {[\textsc{\scriptsize S-global}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{ \vdash }\;\mathit{lim}_{1} \leq \mathit{lim}_{2}
}{
{ \vdash }\;\mathit{lim}_{1}~\mathit{rt} \leq \mathit{lim}_{2}~\mathit{rt}
} \, {[\textsc{\scriptsize S-table}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{ \vdash }\;\mathit{lim}_{1} \leq \mathit{lim}_{2}
}{
{ \vdash }\;\mathit{lim}_{1}~\mathsf{i8} \leq \mathit{lim}_{2}~\mathsf{i8}
} \, {[\textsc{\scriptsize S-mem}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
\mathit{n}_{11} \geq \mathit{n}_{21}
 \qquad
\mathit{n}_{12} \leq \mathit{n}_{22}
}{
{ \vdash }\;[\mathit{n}_{11} .. \mathit{n}_{12}] \leq [\mathit{n}_{21} .. \mathit{n}_{22}]
} \, {[\textsc{\scriptsize S-limits}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{ \vdash }\;\mathit{ft}_{1} \leq \mathit{ft}_{2}
}{
{ \vdash }\;\mathsf{func}~\mathit{ft}_{1} \leq \mathsf{func}~\mathit{ft}_{2}
} \, {[\textsc{\scriptsize S-extern-func}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{ \vdash }\;\mathit{gt}_{1} \leq \mathit{gt}_{2}
}{
{ \vdash }\;\mathsf{global}~\mathit{gt}_{1} \leq \mathsf{global}~\mathit{gt}_{2}
} \, {[\textsc{\scriptsize S-extern-global}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{ \vdash }\;\mathit{tt}_{1} \leq \mathit{tt}_{2}
}{
{ \vdash }\;\mathsf{table}~\mathit{tt}_{1} \leq \mathsf{table}~\mathit{tt}_{2}
} \, {[\textsc{\scriptsize S-extern-table}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{ \vdash }\;\mathit{mt}_{1} \leq \mathit{mt}_{2}
}{
{ \vdash }\;\mathsf{mem}~\mathit{mt}_{1} \leq \mathsf{mem}~\mathit{mt}_{2}
} \, {[\textsc{\scriptsize S-extern-mem}]}
\qquad
\end{array}
$$

\vspace{1ex}

$\boxed{\mathit{context} \vdash \mathit{instr} : \mathit{functype}}$

$\boxed{\mathit{context} \vdash \mathit{instr}^\ast : \mathit{functype}}$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
\mathit{C} \vdash \epsilon : \epsilon \rightarrow \epsilon
} \, {[\textsc{\scriptsize T*-empty}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
\mathit{C} \vdash \mathit{instr}_{1} : \mathit{t}_{1}^\ast \rightarrow \mathit{t}_{2}^\ast
 \qquad
\mathit{C} \vdash \mathit{instr}_{2} : \mathit{t}_{2}^\ast \rightarrow \mathit{t}_{3}^\ast
}{
\mathit{C} \vdash \mathit{instr}_{1}~\mathit{instr}_{2}^\ast : \mathit{t}_{1}^\ast \rightarrow \mathit{t}_{3}^\ast
} \, {[\textsc{\scriptsize T*-seq}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
\begin{array}{@{}c@{}}
\mathit{C} \vdash \mathit{instr}^\ast : \mathit{t}_{1}^\ast \rightarrow \mathit{t}_{2}^\ast
 \\
{ \vdash }\;{\mathit{t}'}_{1}^\ast \leq \mathit{t}_{1}^\ast
 \qquad
{ \vdash }\;\mathit{t}_{2}^\ast \leq {\mathit{t}'}_{2}^\ast
\end{array}
}{
\mathit{C} \vdash \mathit{instr}^\ast : {\mathit{t}'}_{1} \rightarrow {\mathit{t}'}_{2}^\ast
} \, {[\textsc{\scriptsize T*-weak}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
\mathit{C} \vdash \mathit{instr}^\ast : \mathit{t}_{1}^\ast \rightarrow \mathit{t}_{2}^\ast
}{
\mathit{C} \vdash \mathit{instr}^\ast : \mathit{t}^\ast~\mathit{t}_{1}^\ast \rightarrow \mathit{t}^\ast~\mathit{t}_{2}^\ast
} \, {[\textsc{\scriptsize T*-frame}]}
\qquad
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
\mathit{C} \vdash \mathsf{unreachable} : \mathit{t}_{1}^\ast \rightarrow \mathit{t}_{2}^\ast
} \, {[\textsc{\scriptsize T-unreachable}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
\mathit{C} \vdash \mathsf{nop} : \epsilon \rightarrow \epsilon
} \, {[\textsc{\scriptsize T-nop}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
\mathit{C} \vdash \mathsf{drop} : \mathit{t} \rightarrow \epsilon
} \, {[\textsc{\scriptsize T-drop}]}
\qquad
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
\mathit{C} \vdash \mathsf{select}~\mathit{t} : \mathit{t}~\mathit{t}~\mathsf{i32} \rightarrow \mathit{t}
} \, {[\textsc{\scriptsize T-select-expl}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{ \vdash }\;\mathit{t} \leq {\mathit{t}'}
 \qquad
{\mathit{t}'} = \mathit{numtype} \lor {\mathit{t}'} = \mathit{vectype}
}{
\mathit{C} \vdash \mathsf{select} : \mathit{t}~\mathit{t}~\mathsf{i32} \rightarrow \mathit{t}
} \, {[\textsc{\scriptsize T-select-impl}]}
\qquad
\end{array}
$$

\vspace{1ex}

$\boxed{\mathit{context} \vdash \mathit{blocktype} : \mathit{functype}}$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
{ \vdash }\;\mathit{ft} : \mathsf{ok}
}{
\mathit{C} \vdash \mathit{ft} : \mathit{ft}
} \, {[\textsc{\scriptsize K-block}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
\mathit{C} \vdash \mathit{bt} : \mathit{t}_{1}^\ast \rightarrow \mathit{t}_{2}^\ast
 \qquad
\mathit{C}, \mathsf{label}~\mathit{t}_{2}^\ast \vdash \mathit{instr}^\ast : \mathit{t}_{1}^\ast \rightarrow \mathit{t}_{2}^\ast
}{
\mathit{C} \vdash \mathsf{block}~\mathit{bt}~\mathit{instr}^\ast : \mathit{t}_{1}^\ast \rightarrow \mathit{t}_{2}^\ast
} \, {[\textsc{\scriptsize T-block}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
\mathit{C} \vdash \mathit{bt} : \mathit{t}_{1}^\ast \rightarrow \mathit{t}_{2}^\ast
 \qquad
\mathit{C}, \mathsf{label}~\mathit{t}_{1}^\ast \vdash \mathit{instr}^\ast : \mathit{t}_{1}^\ast \rightarrow \mathit{t}_{2}
}{
\mathit{C} \vdash \mathsf{loop}~\mathit{bt}~\mathit{instr}^\ast : \mathit{t}_{1}^\ast \rightarrow \mathit{t}_{2}^\ast
} \, {[\textsc{\scriptsize T-loop}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
\mathit{C} \vdash \mathit{bt} : \mathit{t}_{1}^\ast \rightarrow \mathit{t}_{2}
 \qquad
\mathit{C}, \mathsf{label}~\mathit{t}_{2}^\ast \vdash \mathit{instr}_{1}^\ast : \mathit{t}_{1}^\ast \rightarrow \mathit{t}_{2}^\ast
 \qquad
\mathit{C}, \mathsf{label}~\mathit{t}_{2}^\ast \vdash \mathit{instr}_{2}^\ast : \mathit{t}_{1}^\ast \rightarrow \mathit{t}_{2}^\ast
}{
\mathit{C} \vdash \mathsf{if}~\mathit{bt}~\mathit{instr}_{1}^\ast~\mathsf{else}~\mathit{instr}_{2}^\ast : \mathit{t}_{1}^\ast \rightarrow \mathit{t}_{2}
} \, {[\textsc{\scriptsize T-if}]}
\qquad
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
\mathit{C}.\mathsf{label}[\mathit{l}] = \mathit{t}^\ast
}{
\mathit{C} \vdash \mathsf{br}~\mathit{l} : \mathit{t}_{1}^\ast~\mathit{t}^\ast \rightarrow \mathit{t}_{2}^\ast
} \, {[\textsc{\scriptsize T-br}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
\mathit{C}.\mathsf{label}[\mathit{l}] = \mathit{t}^\ast
}{
\mathit{C} \vdash \mathsf{br\_if}~\mathit{l} : \mathit{t}^\ast~\mathsf{i32} \rightarrow \mathit{t}^\ast
} \, {[\textsc{\scriptsize T-br\_if}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
({ \vdash }\;\mathit{t}^\ast \leq \mathit{C}.\mathsf{label}[\mathit{l}])^\ast
 \qquad
{ \vdash }\;\mathit{t}^\ast \leq \mathit{C}.\mathsf{label}[{\mathit{l}'}]
}{
\mathit{C} \vdash \mathsf{br\_table}~\mathit{l}^\ast~{\mathit{l}'} : \mathit{t}_{1}^\ast~\mathit{t}^\ast \rightarrow \mathit{t}_{2}^\ast
} \, {[\textsc{\scriptsize T-br\_table}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
\mathit{C}.\mathsf{return} = (\mathit{t}^\ast)
}{
\mathit{C} \vdash \mathsf{return} : \mathit{t}_{1}^\ast~\mathit{t}^\ast \rightarrow \mathit{t}_{2}^\ast
} \, {[\textsc{\scriptsize T-return}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
\mathit{C}.\mathsf{func}[\mathit{x}] = \mathit{t}_{1}^\ast \rightarrow \mathit{t}_{2}^\ast
}{
\mathit{C} \vdash \mathsf{call}~\mathit{x} : \mathit{t}_{1}^\ast \rightarrow \mathit{t}_{2}^\ast
} \, {[\textsc{\scriptsize T-call}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
\mathit{C}.\mathsf{table}[\mathit{x}] = \mathit{lim}~\mathsf{funcref}
 \qquad
\mathit{ft} = \mathit{t}_{1}^\ast \rightarrow \mathit{t}_{2}^\ast
}{
\mathit{C} \vdash \mathsf{call\_indirect}~\mathit{x}~\mathit{ft} : \mathit{t}_{1}^\ast~\mathsf{i32} \rightarrow \mathit{t}_{2}^\ast
} \, {[\textsc{\scriptsize T-call\_indirect}]}
\qquad
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
\mathit{C} \vdash \mathit{nt}.\mathsf{const}~\mathit{c}_{\mathit{nt}} : \epsilon \rightarrow \mathit{nt}
} \, {[\textsc{\scriptsize T-const}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
\mathit{C} \vdash \mathit{nt} . \mathit{unop} : \mathit{nt} \rightarrow \mathit{nt}
} \, {[\textsc{\scriptsize T-unop}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
\mathit{C} \vdash \mathit{nt} . \mathit{binop} : \mathit{nt}~\mathit{nt} \rightarrow \mathit{nt}
} \, {[\textsc{\scriptsize T-binop}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
\mathit{C} \vdash \mathit{nt} . \mathit{testop} : \mathit{nt} \rightarrow \mathsf{i32}
} \, {[\textsc{\scriptsize T-testop}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
\mathit{C} \vdash \mathit{nt} . \mathit{relop} : \mathit{nt}~\mathit{nt} \rightarrow \mathsf{i32}
} \, {[\textsc{\scriptsize T-relop}]}
\qquad
\end{array}
$$

\vspace{1ex}

\vspace{1ex}

$\boxed{\mathit{context} \vdash \mathit{instr}~\mathsf{const}}$

$\boxed{\mathit{context} \vdash \mathit{instr}^\ast~\mathsf{const}}$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
\mathit{C} \vdash (\mathit{nt}.\mathsf{const}~\mathit{c})~\mathsf{const}
} \, {[\textsc{\scriptsize C-instr-const}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
\mathit{C} \vdash (\mathsf{ref.null}~\mathit{rt})~\mathsf{const}
} \, {[\textsc{\scriptsize C-instr-ref.null}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
}{
\mathit{C} \vdash (\mathsf{ref.func}~\mathit{x})~\mathsf{const}
} \, {[\textsc{\scriptsize C-instr-ref.func}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
\mathit{C}.\mathsf{global}[\mathit{x}] = \epsilon~\mathit{t}
}{
\mathit{C} \vdash (\mathsf{global.get}~\mathit{x})~\mathsf{const}
} \, {[\textsc{\scriptsize C-instr-global.get}]}
\qquad
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}c@{}}\displaystyle
\frac{
(\mathit{C} \vdash \mathit{instr}~\mathsf{const})^\ast
}{
\mathit{C} \vdash \mathit{instr}^\ast~\mathsf{const}
} \, {[\textsc{\scriptsize C-expr}]}
\qquad
\end{array}
$$

$$
\begin{array}{@{}lrrl@{}}
\mbox{(address)} & \mathit{addr} &::=& \mathit{nat} \\
\mbox{(function address)} & \mathit{funcaddr} &::=& \mathit{addr} \\
\mbox{(global address)} & \mathit{globaladdr} &::=& \mathit{addr} \\
\mbox{(table address)} & \mathit{tableaddr} &::=& \mathit{addr} \\
\mbox{(memory address)} & \mathit{memaddr} &::=& \mathit{addr} \\
\mbox{(elem address)} & \mathit{elemaddr} &::=& \mathit{addr} \\
\mbox{(data address)} & \mathit{dataaddr} &::=& \mathit{addr} \\
\mbox{(label address)} & \mathit{labeladdr} &::=& \mathit{addr} \\
\mbox{(host address)} & \mathit{hostaddr} &::=& \mathit{addr} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lrrl@{}}
\mbox{(number)} & \mathit{num} &::=& \mathsf{\mathit{numtype}}.\mathsf{const}~\mathsf{\mathit{c}\_{\mathit{numtype}}} \\
\mbox{(reference)} & \mathit{ref} &::=& \mathsf{ref.null}~\mathit{reftype} ~|~ \mathsf{ref.func}~\mathsf{\mathit{funcaddr}} ~|~ \mathsf{ref.extern}~\mathsf{\mathit{hostaddr}} \\
\mbox{(value)} & \mathit{val} &::=& \mathit{num} ~|~ \mathit{ref} \\
\mbox{(result)} & \mathit{result} &::=& \mathit{val}^\ast ~|~ \mathsf{trap} \\
\end{array}
$$

$$
\begin{array}{@{}lrrl@{}}
\mbox{(external value)} & \mathit{externval} &::=& \mathsf{func}~\mathit{funcaddr} ~|~ \mathsf{global}~\mathit{globaladdr} ~|~ \mathsf{table}~\mathit{tableaddr} ~|~ \mathsf{mem}~\mathit{memaddr} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lcl@{}l@{}}
\mathrm{default}_{\mathsf{i32}} &=& (\mathsf{i32}.\mathsf{const}~0) &  \\
\mathrm{default}_{\mathsf{i64}} &=& (\mathsf{i64}.\mathsf{const}~0) &  \\
\mathrm{default}_{\mathsf{f32}} &=& (\mathsf{f32}.\mathsf{const}~0) &  \\
\mathrm{default}_{\mathsf{f64}} &=& (\mathsf{f64}.\mathsf{const}~0) &  \\
\mathrm{default}_{\mathit{rt}} &=& (\mathsf{ref.null}~\mathit{rt}) &  \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lrrl@{}}
\mbox{(function instance)} & \mathit{funcinst} &::=& \mathit{moduleinst} ; \mathit{func} \\
\mbox{(global instance)} & \mathit{globalinst} &::=& \mathit{val} \\
\mbox{(table instance)} & \mathit{tableinst} &::=& \mathit{ref}^\ast \\
\mbox{(memory instance)} & \mathit{meminst} &::=& \mathit{byte}^\ast \\
\mbox{(element instance)} & \mathit{eleminst} &::=& \mathit{ref}^\ast \\
\mbox{(data instance)} & \mathit{datainst} &::=& \mathit{byte}^\ast \\
\mbox{(export instance)} & \mathit{exportinst} &::=& \mathsf{export}~\mathit{name}~\mathit{externval} \\
\mbox{(store)} & \mathit{store} &::=& \{\; \begin{array}[t]{@{}l@{}}
\mathsf{func}~\mathit{funcinst}^\ast,\; \\
  \mathsf{global}~\mathit{globalinst}^\ast,\; \\
  \mathsf{table}~\mathit{tableinst}^\ast,\; \\
  \mathsf{mem}~\mathit{meminst}^\ast,\; \\
  \mathsf{elem}~\mathit{eleminst}^\ast,\; \\
  \mathsf{data}~\mathit{datainst}^\ast \;\}\end{array} \\
\mbox{(module instance)} & \mathit{moduleinst} &::=& \{\; \begin{array}[t]{@{}l@{}}
\mathsf{func}~\mathit{funcaddr}^\ast,\; \\
  \mathsf{global}~\mathit{globaladdr}^\ast,\; \\
  \mathsf{table}~\mathit{tableaddr}^\ast,\; \\
  \mathsf{mem}~\mathit{memaddr}^\ast,\; \\
  \mathsf{elem}~\mathit{elemaddr}^\ast,\; \\
  \mathsf{data}~\mathit{dataaddr}^\ast,\; \\
  \mathsf{export}~\mathit{exportinst}^\ast \;\}\end{array} \\
\mbox{(frame)} & \mathit{frame} &::=& \mathit{moduleinst} ; \mathit{val}^\ast \\
\mbox{(state)} & \mathit{state} &::=& \mathit{store} ; \mathit{frame} \\
\mbox{(configuration)} & \mathit{config} &::=& \mathit{state} ; \mathit{instr}^\ast \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
(\mathit{s} ; (\mathit{m} ; \mathit{val}^\ast)).\mathsf{func} &=& \mathit{m}.\mathsf{func} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
(\mathit{s} ; \mathit{f}).\mathsf{func} &=& \mathit{s}.\mathsf{func} &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{(\mathit{s} ; (\mathit{m} ; \mathit{val}^\ast)).\mathsf{func}}{[\mathit{x}]} &=& \mathit{s}.\mathsf{func}[\mathit{m}.\mathsf{func}[\mathit{x}]] &  \\
\end{array}
$$

$$
\begin{array}{@{}lcl@{}l@{}}
{(\mathit{s} ; (\mathit{m} ; \mathit{val}^\ast)).\mathsf{table}}{[\mathit{x}]} &=& \mathit{s}.\mathsf{table}[\mathit{m}.\mathsf{table}[\mathit{x}]] &  \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}lrrl@{}}
\mbox{(administrative instruction)} & \mathit{instr} &::=& \mathit{instr} \\ &&|&
\mathsf{ref.func}~\mathsf{\mathit{funcaddr}} \\ &&|&
\mathsf{ref.extern}~\mathsf{\mathit{hostaddr}} \\ &&|&
\mathsf{call}~\mathsf{\mathit{funcaddr}} \\ &&|&
{\mathsf{label}_{\mathsf{\mathit{n}}}}{\mathsf{\{\mathit{instr}^\ast\}}~\mathsf{\mathit{instr}^\ast}} \\ &&|&
{\mathsf{frame}_{\mathsf{\mathit{n}}}}{\mathsf{\{\mathit{frame}\}}~\mathsf{\mathit{instr}^\ast}} \\ &&|&
\mathsf{trap} \\
\mbox{(evaluation context)} & \mathit{E} &::=& [\mathsf{\_}] \\ &&|&
\mathit{val}^\ast~\mathit{E}~\mathit{instr}^\ast \\ &&|&
{\mathsf{label}_{\mathsf{\mathit{n}}}}{\mathsf{\{\mathit{instr}^\ast\}}~\mathsf{\mathit{e}}} \\
\end{array}
$$

$\boxed{\mathit{config} \hookrightarrow \mathit{config}}$

$\boxed{\mathit{config} \hookrightarrow \mathit{instr}^\ast}$

$\boxed{\mathit{instr}^\ast \hookrightarrow \mathit{instr}^\ast}$

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E-pure}]} \quad & \mathit{z} ; \mathit{instr}^\ast &\hookrightarrow& \mathit{z} ; {\mathit{instr}'}^\ast &\quad
  \mbox{if}~\mathit{instr}^\ast \hookrightarrow {\mathit{instr}'}^\ast \\
{[\textsc{\scriptsize E-read}]} \quad & \mathit{z} ; \mathit{instr}^\ast &\hookrightarrow& \mathit{z} ; {\mathit{instr}'}^\ast &\quad
  \mbox{if}~\mathit{z} ; \mathit{instr}^\ast \hookrightarrow {\mathit{instr}'}^\ast \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E-unreachable}]} \quad & \mathsf{unreachable} &\hookrightarrow& \mathsf{trap} &  \\
{[\textsc{\scriptsize E-nop}]} \quad & \mathsf{nop} &\hookrightarrow& \epsilon &  \\
{[\textsc{\scriptsize E-drop}]} \quad & \mathit{val}~\mathsf{drop} &\hookrightarrow& \epsilon &  \\
{[\textsc{\scriptsize E-select-true}]} \quad & \mathit{val}_{1}~\mathit{val}_{2}~(\mathsf{i32}.\mathsf{const}~\mathit{c})~(\mathsf{select}~\mathit{t}^?) &\hookrightarrow& \mathit{val}_{1} &\quad
  \mbox{if}~\mathit{c} \neq 0 \\
{[\textsc{\scriptsize E-select-false}]} \quad & \mathit{val}_{1}~\mathit{val}_{2}~(\mathsf{i32}.\mathsf{const}~\mathit{c})~(\mathsf{select}~\mathit{t}^?) &\hookrightarrow& \mathit{val}_{2} &\quad
  \mbox{if}~\mathit{c} = 0 \\
{[\textsc{\scriptsize E-block}]} \quad & \mathit{val}^{\mathit{k}}~(\mathsf{block}~\mathit{bt}~\mathit{instr}^\ast) &\hookrightarrow& ({\mathsf{label}_{\mathit{n}}}{\{\epsilon\}~\mathit{val}^{\mathit{k}}~\mathit{instr}^\ast}) &\quad
  \mbox{if}~\mathit{bt} = \mathit{t}_{1}^{\mathit{k}} \rightarrow \mathit{t}_{2}^{\mathit{n}} \\
{[\textsc{\scriptsize E-loop}]} \quad & \mathit{val}^{\mathit{k}}~(\mathsf{loop}~\mathit{bt}~\mathit{instr}^\ast) &\hookrightarrow& ({\mathsf{label}_{\mathit{n}}}{\{\mathsf{loop}~\mathit{bt}~\mathit{instr}^\ast\}~\mathit{val}^{\mathit{k}}~\mathit{instr}^\ast}) &\quad
  \mbox{if}~\mathit{bt} = \mathit{t}_{1}^{\mathit{k}} \rightarrow \mathit{t}_{2}^{\mathit{n}} \\
{[\textsc{\scriptsize E-if-true}]} \quad & (\mathsf{i32}.\mathsf{const}~\mathit{c})~(\mathsf{if}~\mathit{bt}~\mathit{instr}_{1}^\ast~\mathsf{else}~\mathit{instr}_{2}^\ast) &\hookrightarrow& (\mathsf{block}~\mathit{bt}~\mathit{instr}_{1}^\ast) &\quad
  \mbox{if}~\mathit{c} \neq 0 \\
{[\textsc{\scriptsize E-if-false}]} \quad & (\mathsf{i32}.\mathsf{const}~\mathit{c})~(\mathsf{if}~\mathit{bt}~\mathit{instr}_{1}^\ast~\mathsf{else}~\mathit{instr}_{2}^\ast) &\hookrightarrow& (\mathsf{block}~\mathit{bt}~\mathit{instr}_{2}^\ast) &\quad
  \mbox{if}~\mathit{c} = 0 \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E-br-zero}]} \quad & ({\mathsf{label}_{\mathit{n}}}{\{{\mathit{instr}'}^\ast\}~{\mathit{val}'}^\ast~\mathit{val}^{\mathit{n}}~(\mathsf{br}~0)~\mathit{instr}^\ast}) &\hookrightarrow& \mathit{val}^{\mathit{n}}~{\mathit{instr}'}^\ast &  \\
{[\textsc{\scriptsize E-br-succ}]} \quad & ({\mathsf{label}_{\mathit{n}}}{\{{\mathit{instr}'}^\ast\}~\mathit{val}^\ast~(\mathsf{br}~\mathit{l} + 1)~\mathit{instr}^\ast}) &\hookrightarrow& \mathit{val}^\ast~(\mathsf{br}~\mathit{l}) &  \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E-br\_if-true}]} \quad & (\mathsf{i32}.\mathsf{const}~\mathit{c})~(\mathsf{br\_if}~\mathit{l}) &\hookrightarrow& (\mathsf{br}~\mathit{l}) &\quad
  \mbox{if}~\mathit{c} \neq 0 \\
{[\textsc{\scriptsize E-br\_if-false}]} \quad & (\mathsf{i32}.\mathsf{const}~\mathit{c})~(\mathsf{br\_if}~\mathit{l}) &\hookrightarrow& \epsilon &\quad
  \mbox{if}~\mathit{c} = 0 \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E-br\_table-lt}]} \quad & (\mathsf{i32}.\mathsf{const}~\mathit{i})~(\mathsf{br\_table}~\mathit{l}^\ast~{\mathit{l}'}) &\hookrightarrow& (\mathsf{br}~\mathit{l}^\ast[\mathit{i}]) &\quad
  \mbox{if}~\mathit{i} < {|\mathit{l}^\ast|} \\
{[\textsc{\scriptsize E-br\_table-le}]} \quad & (\mathsf{i32}.\mathsf{const}~\mathit{i})~(\mathsf{br\_table}~\mathit{l}^\ast~{\mathit{l}'}) &\hookrightarrow& (\mathsf{br}~{\mathit{l}'}) &\quad
  \mbox{if}~\mathit{i} \geq {|\mathit{l}^\ast|} \\
\end{array}
$$

\vspace{1ex}

$$
\begin{array}{@{}l@{}lcl@{}l@{}}
{[\textsc{\scriptsize E-call}]} \quad & \mathit{z} ; (\mathsf{call}~\mathit{x}) &\hookrightarrow& (\mathsf{call}~\mathit{z}.\mathsf{func}[\mathit{x}]) &  \\
{[\textsc{\scriptsize E-call\_indirect-call}]} \quad & \mathit{z} ; (\mathsf{i32}.\mathsf{const}~\mathit{i})~(\mathsf{call\_indirect}~\mathit{x}~\mathit{ft}) &\hookrightarrow& (\mathsf{call}~\mathit{a}) &\quad
  \mbox{if}~{\mathit{z}.\mathsf{table}}{[\mathit{x}]}[\mathit{i}] = (\mathsf{ref.func}~\mathit{a}) \\
 &&&\quad {\land}~\mathit{z}.\mathsf{func}[\mathit{a}] = \mathit{m} ; \mathit{func} \\
{[\textsc{\scriptsize E-call\_indirect-trap}]} \quad & \mathit{z} ; (\mathsf{i32}.\mathsf{const}~\mathit{i})~(\mathsf{call\_indirect}~\mathit{x}~\mathit{ft}) &\hookrightarrow& \mathsf{trap} &\quad
  \mbox{otherwise} \\
{[\textsc{\scriptsize E-call\_addr}]} \quad & \mathit{z} ; \mathit{val}^{\mathit{k}}~(\mathsf{call}~\mathit{a}) &\hookrightarrow& ({\mathsf{frame}_{\mathit{n}}}{\{\mathit{m} ; \mathit{val}^{\mathit{k}}~(\mathrm{default}_{\mathit{t}})^\ast\}~({\mathsf{label}_{\mathit{n}}}{\{\epsilon\}~\mathit{instr}^\ast})}) &\quad
  \mbox{if}~\mathit{z}.\mathsf{func}[\mathit{a}] = \mathit{m} ; \mathsf{func}~(\mathit{t}_{1}^{\mathit{k}} \rightarrow \mathit{t}_{2}^{\mathit{n}})~\mathit{t}^\ast~\mathit{instr}^\ast \\
\end{array}
$$


== Complete.
```