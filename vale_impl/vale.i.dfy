// Trusted machine definition
datatype reg = X | Y | Z | W

datatype ins =
  InsImm(dstImm:reg, imm:int)
| InsAdd(dstAdd:reg, srcAdd:reg)

datatype obool = OLe(r1:reg, r2:reg)

datatype codes = CNil | va_CCons(hd:code, tl:codes)
datatype code =
  Ins(ins:ins)
| Block(block:codes)
| IfElse(ifCond:obool, ifTrue:code, ifFalse:code)
| While(whileCond:obool, whileBody:code)

// States may be "good" (ok == true) or "bad" (ok == false)
datatype state = state(ok:bool, regs:map<reg, int>)

function getReg(s:state, r:reg):int { if r in s.regs then s.regs[r] else 0 }

predicate evalOBool(s:state, cond:obool)
{
    getReg(s, cond.r1) <= getReg(s, cond.r2)
}

// Evaluation:
// We want to prove that:
//   - a program never reaches a bad state (ok == false)
//   - if a program terminates, it terminates in a good state that satisfies some postcondition
// We do this by modeling all possible finite executions from state s0 to state sN:
//   - if a program goes bad, it will do so in a finite number of steps
//   - if a program terminates, it will do so in a finite number of steps
// evalCode(c, s0, sN) says that it is possible for code c to step from state s0 to state sN in
// a finite number of steps.
// For clarity's sake, when a program reaches a bad state, it stops (no more steps).

predicate evalIns(ins:ins, s0:state, s1:state)
{
    match ins
        case InsImm(dst, imm) => s1 == s0.(regs := s0.regs[dst := imm])
        case InsAdd(dst, src) => s1 == s0.(regs := s0.regs[dst := getReg(s0, dst) + getReg(s0, src)])
}

predicate evalBlock(block:codes, s0:state, sN:state)
{
    if block.CNil? then sN == s0
    else exists s1:state ::
        evalCode(block.hd, s0, s1) && (if s1.ok then evalBlock(block.tl, s1, sN) else s1 == sN)
}

predicate evalWhile(b:obool, c:code, n:nat, s0:state, sN:state)
    decreases c, n
{
    if n == 0 then !evalOBool(s0, b) && s0 == sN
    else exists s1:state ::
        evalOBool(s0, b) && evalCode(c, s0, s1) && (if s1.ok then evalWhile(b, c, n - 1, s1, sN) else s1 == sN)
}

predicate evalCode(c:code, s0:state, sN:state)
    decreases c, 0
{
    s0.ok
 && (match c
        case Ins(ins) => evalIns(ins, s0, sN)
        case Block(block) => evalBlock(block, s0, sN)
        case IfElse(cond, ifT, ifF) => if evalOBool(s0, cond) then evalCode(ifT, s0, sN) else evalCode(ifF, s0, sN)
        case While(cond, body) => exists n:nat :: evalWhile(cond, body, n, s0, sN)
    )
}

///////////////////////////////////////////////////////////////////////////////
// Untrusted Vale interface

type opr = reg
type va_operand_opr = opr
type va_value_opr = int
function method va_op_opr_reg(r:reg):opr { r }
function method va_op_cmp_reg(r:reg):opr { r }
predicate va_is_src_opr(o:opr, s:va_state) { true }
predicate va_is_dst_opr(o:opr, s:va_state) { true }

type va_code = code
type va_codes = codes
type va_state = state

function va_get_ok(s:va_state):bool { s.ok }
function va_get_reg(r:reg, s:va_state):int { getReg(s, r) }

function va_update_ok(sM:va_state, sK:va_state):va_state { sK.(ok := sM.ok) }
function va_update_reg(r:reg, sM:va_state, sK:va_state):va_state requires r in sM.regs { sK.(regs := sK.regs[r := sM.regs[r]]) }

function va_update_operand_opr(o:opr, sM:va_state, sK:va_state):va_state
    requires o in sM.regs
{
    va_update_reg(o, sM, sK)
}

predicate va_state_eq(s0:va_state, s1:va_state)
{
    s0.ok == s1.ok
 && s0.regs == s1.regs
}

function method va_CNil():codes { CNil }
function method va_Block(block:codes):code { Block(block) }
function method va_IfElse(ifb:obool, ift:code, iff:code):code { IfElse(ifb, ift, iff) }
function method va_While(whileb:obool, whilec:code):code { While(whileb, whilec) }
function method va_cmp_le(o1:opr, o2:opr):obool { OLe(o1, o2) }

function va_get_block(c:va_code):va_codes requires c.Block? { c.block }
function va_get_ifCond(c:code):obool requires c.IfElse? { c.ifCond }
function va_get_ifTrue(c:code):code requires c.IfElse? { c.ifTrue }
function va_get_ifFalse(c:code):code requires c.IfElse? { c.ifFalse }
function va_get_whileCond(c:code):obool requires c.While? { c.whileCond }
function va_get_whileBody(c:code):code requires c.While? { c.whileBody }

predicate{:opaque} evalWhileOpaque(b:obool, c:code, n:nat, s0:state, sN:state) { evalWhile(b, c, n, s0, sN) }
predicate{:opaque} evalCodeOpaque(c:code, s0:state, sN:state) { evalCode(c, s0, sN) }

// For the proof, we define a more liberal evaluation relation evalCode_lax that
// allows arbitrary "zombie steps" from a bad state to any other state.
// The proof proceeds as follows:
//   - suppose s0.ok; i.e., we start in a good state
//   - suppose evalCode(c, s0, sN); i.e., c takes non-zombie steps from s0 to sN
//   - then evalCode_lax(c, s0, sN) holds; i.e., c takes possibly-zombie steps from s0 to sN
//   - we first use evalCode_lax to prove some initial basic properties of the evaluation
//   - we finally prove that the possibly-zombie steps are in fact non-zombie steps,
//     by proving that ok holds for all intermediate states s0,s1,s2,...,sN
// Ultimately, we still prove precisely what we want: if s.ok and evalCode(c, s0, sN),
// then sN.ok and postcondition(sN).
// It may seem strange to allow zombie steps and then prove that there are no
// zombie steps, but this allows us to factor the proof for  procedures
// so that the proof of non-zombieness comes after other parts of the proof.
// Specifically, the "refined" lemmas will allow zombie steps, and only at the
// end of each refined lemma will we call the "abstract" lemma that
// retroactively eliminates the possibility that there were zombie steps.
predicate evalCode_lax(c:code, s0:state, sN:state) { s0.ok ==> evalCodeOpaque(c, s0, sN) }
predicate evalWhile_lax(b:obool, c:code, n:nat, s0:state, sN:state) { s0.ok ==> evalWhileOpaque(b, c, n, s0, sN) }

function va_eval_opr(s:state, o:opr):int
{
    getReg(s, o)
}

predicate valid_state(s:state)
{
  forall r:reg :: r in s.regs
}

predicate va_require(block0:va_codes, c:va_code, s0:va_state, sN:va_state)
{
    block0.va_CCons?
 && block0.hd == c
 && evalCode_lax(va_Block(block0), s0, sN)
 && valid_state(s0)
}

predicate va_ensure(b0:va_codes, b1:va_codes, s0:va_state, s1:va_state, sN:va_state)
{
    b0.va_CCons?
 && b0.tl == b1
 && (s1.ok ==> evalCode_lax(b0.hd, s0, s1))
 && evalCode_lax(va_Block(b1), s1, sN)
 && valid_state(s1)
}

predicate va_whileInv(b:obool, c:code, n:int, s0:va_state, sN:va_state)
{
    n >= 0
 && evalWhile_lax(b, c, n, s0, sN)
 && valid_state(s0)
}

lemma va_ins_lemma(b0:code, s0:va_state)
{
}

lemma va_lemma_block(b0:va_codes, s0:state, sN:state) returns(s1:state, c1:va_code, b1:va_codes)
    requires b0.va_CCons?
    requires evalCode_lax(va_Block(b0), s0, sN)
    ensures  b0 == va_CCons(c1, b1)
    ensures  evalCode_lax(c1, s0, s1)
    ensures  evalCode_lax(va_Block(b1), s1, sN)
{
    reveal_evalCodeOpaque();
    c1 := b0.hd;
    b1 := b0.tl;
    if (s0.ok)
    {
        assert evalBlock(b0, s0, sN);
        s1 :| evalCode(b0.hd, s0, s1) && (if s1.ok then evalBlock(b0.tl, s1, sN) else s1 == sN);
    }
    else
    {
        s1 := s0;
    }
}

lemma va_lemma_empty(s0:va_state, sN:va_state) returns(sM:va_state)
    requires evalCode_lax(va_Block(va_CNil()), s0, sN)
    ensures  s0 == sM
    ensures  s0.ok ==> s0 == sN
{
    reveal_evalCodeOpaque();
    sM := s0;
}

lemma va_lemma_while(b:obool, c:code, s0:va_state, sN:va_state) returns(n:nat, s1:va_state)
    requires evalCode_lax(While(b, c), s0, sN)
    ensures  evalWhile_lax(b, c, n, s0, sN)
    ensures  s1 == s0
{
    reveal_evalCodeOpaque();
    reveal_evalWhileOpaque();
    if (s0.ok)
    {
        assert evalCode(While(b, c), s0, sN);
        n :| evalWhile(b, c, n, s0, sN);
    }
    else
    {
        n := 0;
    }
    s1 := s0;
}

lemma va_lemma_whileTrue(b:obool, c:code, n:nat, s0:va_state, sN:va_state) returns(s0':va_state, s1:va_state)
    requires n > 0
    requires evalWhile_lax(b, c, n, s0, sN)
    ensures  s0' == s0
    ensures  s0.ok ==> evalOBool(s0, b)
    ensures  evalCode_lax(c, s0', s1)
    ensures  evalWhile_lax(b, c, n - 1, s1, sN)
{
    reveal_evalCodeOpaque();
    reveal_evalWhileOpaque();
    s0' := s0;
    if (s0.ok)
    {
        s1 :| evalOBool(s0, b) && evalCode(c, s0, s1) && (if s1.ok then evalWhile(b, c, n - 1, s1, sN) else s1 == sN);
    }
    else
    {
        s1 := s0;
    }
}

lemma va_lemma_whileFalse(b:obool, c:code, s0:va_state, sN:va_state) returns(s1:va_state)
    requires evalWhile_lax(b, c, 0, s0, sN)
    ensures  s1 == s0
    ensures  s0.ok ==> !evalOBool(s0, b)
    ensures  s0.ok ==> s1 == sN
{
    reveal_evalCodeOpaque();
    reveal_evalWhileOpaque();
    s1 := if s0.ok then sN else s0;
}
