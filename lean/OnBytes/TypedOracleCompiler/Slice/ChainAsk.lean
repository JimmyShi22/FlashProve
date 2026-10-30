-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/ChainAsk.lean: the checker on bytes of a chain with stored tables that asks the
oracle for every hash and returns a Link string typed over the sibling; and that it fits the
sibling's encoding. The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made
with; it builds on definitions of Compile/.

"The line": the files of OnBytes/Slice/ and OnBytes/Tie/, over the library's compiler.

After OnBytes/Slice/OneWorldChain.lean (`chainPost`) and OnBytes/Slice/ChainChkAsk.lean
(`chainChkBy`, `chainChkAsk`, `chainChkFn` and their laws);
`withinT` after `Tie.withinX`. THE
READING HALF IS THE LINE'S, AS IT LIES: the reader that asks (`Tie.readByR` with `readByR_det`,
`readByR_bound`, `qp_askB`), the count `Tie.CostX.fileNX`, `RootsIn`, `chainRoots`, `s0Of`, `over`:
none of them names a typed family. THE TYPING HALF IS THE SIBLING'S: the checker returns `LinkOut
256 ((xdOf S0 stm).L Bd dec)`, made by the sibling's `toBPrfX` and `asLink`.

AS TEXT but for names, `_root_.`, the argument Bd and the short name `Pre` (8; held by a program
that undoes these substitutions and compares declaration by declaration).
`chainPost`, `chainChkBy`, `chainChkAsk`, `chainChkFn`, `chainChkBy_det`, `det_chainChkAsk_fn`,
`chainChkBy_bound`, `chainChkAsk_bound`.
TURNED (1).
 `withinT`            the text of `Tie.withinX` at the sibling's `XD.ok`.
NEW (6).
 `chainChkAsk_fit_over`   its core is one call of `accepts_allRoots_at`. The
                      implementation is `implAtPd`.
 `Pre γ`              a short name for the type of what stands before a chain.
 `withinT_spec`       the limits clause by clause, at any statement function: `XD.ok` does not read
                      the field `stm` (it does read the base's statement).
 `oB_over_call`, `chainChkFn_roots`, `chainChkAsk_roots`.


NOT SAID: `chainChk`, `chainChkPd`, `chainChkAt` and their laws (the checkers that hold a digest);
the laws at `bitsOf` and `oBits`.

WHAT IT IMPORTS OF THE LINE: OnBytes/Slice/ChainChkAsk.lean, under which files of OnBytes/Hash/
stand.

WHAT IS NOT SAID. That the checker ever returns something. No program calls it. That any bodies meet
`OwnFits` and `hi`, or any description `FitsS` and `withinT`. Nothing on soundness; no probability.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.AllRootsAt
import OnBytes.TypedOracleCompiler.Slice.LinkClause
import OnBytes.Slice.ChainChkAsk

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom Prob _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop MeasureTheory
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (bytesToDig digToBytes size_digToBytes oB bytesToBits strOf)
open _root_.Run.PQ (View SgX)
open TypedOracleCompiler.Run (IsCall169)
open TypedOracleCompiler.Run.PQ (XD xdOf withStatement BodyD LeafD StmInv OwnE OwnFits FitsS skeletonOverBothExternalStrings toBPrfX
  asLink WkAny implAtPd accepts_allRoots_at oStr_number leafSL)
open OnBytes.Slice (RootsIn chainRoots s0Of over over_mem over_not_mem)
open OnBytes.Tie (readByR readByR_det readByR_bound qp_askB)
open scoped ENNReal

/-! ## The limits, over the sibling -/

/-- The limits within which a chain that opens stored tables is covered, over the sibling: the
sibling's `XD.ok` (the random bytes counted as standing in the file), random bytes in the chain, and
each table opened at most once. The text of `Tie.withinX`. It reads the description's statement. -/
def withinT (S : _root_.Fmt.SpecX) : Bool :=
  (xdOf S fun _ _ => ByteArray.empty).ok && !S.base.rand.isNone &&
    decide (S.stored.flatten.map (·.item == 1)).Nodup

/-- The limits, clause by clause, at any statement function: `XD.ok` does not read that field. -/
theorem withinT_spec (S : _root_.Fmt.SpecX) (stm : ByteArray → ByteArray → ByteArray)
    (hw : withinT S = true) :
    (xdOf S stm).ok = true ∧ S.base.rand.isNone = false ∧
      (S.stored.flatten.map (·.item == 1)).Nodup := by
  unfold withinT at hw
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hw
  exact ⟨hw.1.1, hw.1.2, hw.2⟩

/-! ## The oracle with a table put over it, at calls with another number -/

/-- At a call whose number is not 169 modulo 65536, the oracle with a table put over it at strings
of calls with the number 169 answers as the oracle itself. -/
theorem oB_over_call (S : Finset (List Bool)) (hS : ∀ s ∈ S, IsCall169 s) (T : List Bool → Dig 256)
    (g : Fam (rom 256)) (q : _root_.Fmt.OQ) (hq : q.number % 65536 ≠ 169) :
    oB ((over S T g) ()) (strOf q) = oB (g ()) (strOf q) := by
  have hn : bytesToBits (strOf q) ∉ S := by
    intro hm
    obtain ⟨half, t, i, st, bs, -, -, e⟩ := hS _ hm
    have e' : strOf q = _root_.Fmt.oStr half 169 t i st bs := _root_.Run.bytesToBits_inj e
    have h1 := oStr_number q.half q.number q.tree q.index q.start q.bytes
    have h2 := oStr_number half 169 t i st bs
    have e2 : _root_.Fmt.oStr q.half q.number q.tree q.index q.start q.bytes =
        _root_.Fmt.oStr half 169 t i st bs := e'
    rw [e2, h2] at h1
    exact hq (by omega)
  show digToBytes (over S T g () (bytesToBits (strOf q))) =
    digToBytes (g () (bytesToBits (strOf q)))
  rw [over_not_mem T g hn]

/-! ## The checkers -/

/-- What stands before a chain, read off a maker's output: two roots, bytes, a place and a last
test; or nothing. -/
abbrev Pre (γ : Type) : Type := γ → Option (ByteArray × ByteArray × ByteArray × ℕ × (ℕ → Bool))

section
variable {γ : Type} (Bd : Type) (S0 : _root_.Fmt.SpecX)
  (stm : ByteArray → ByteArray → ByteArray) (dec : View → Bool)

/-- What the checker makes of what the reader returns: nothing if the reader has refused, if the
last test fails at the place where the chain ended, if the decision says no on the view, or if the
typing refuses; otherwise the two roots and the typed string. The typing reads no statement. -/
def chainPost (r0 r1 : ByteArray) (fin : ℕ → Bool) :
    Option (_root_.Fmt.ChainOut × ℕ) → Option (LinkOut 256 ((xdOf S0 stm).L Bd dec))
  | none => none
  | some (o, n) =>
    if fin n && dec (_root_.Fmt.viewX (withStatement S0 (stm r0 r1)) o) then
      (toBPrfX S0.base.plan.salt S0.base.cfg (xdOf S0 stm).C (xdOf S0 stm).ds (xdOf S0 stm).a
        (xdOf S0 stm).xs dec o).map fun π =>
          (bytesToDig r0, bytesToDig r1, asLink (Bd := Bd) (xdOf S0 stm) dec π)
    else none

/-- The checker on bytes, with the reader that asks by `ask`. `pre` gives two roots, bytes, a
place and a last test, or refuses. The checker returns something exactly if both roots have 32
bytes, the description with the statement of these roots is within the sibling's limits, the reader
reads a chain from that place, and `chainPost` returns something. No program calls it. -/
def chainChkBy (ask : ByteArray → ZKCP.OComp 256 ByteArray) (pre : Pre γ) (x : γ) :
    OComp (rom 256) (Option (LinkOut 256 ((xdOf S0 stm).L Bd dec))) :=
  match pre x with
  | none => OComp.pure none
  | some (r0, r1, b, i, fin) =>
    if r0.size = 32 ∧ r1.size = 32 ∧ withinT (withStatement S0 (stm r0 r1)) = true then
      (readByR ask (withStatement S0 (stm r0 r1)) [] b i).bind fun rd =>
        OComp.pure (chainPost Bd S0 stm dec r0 r1 fin rd)
    else OComp.pure none

/-- The checker that asks the oracle for every hash of the chain's reader, the digest of the
parameter bytes among them. What stands before the chain, the statement function and the decision
ask nothing; the configuration's digest is not asked for. -/
def chainChkAsk (pre : Pre γ) (x : γ) :
    OComp (rom 256) (Option (LinkOut 256 ((xdOf S0 stm).L Bd dec))) :=
  chainChkBy Bd S0 stm dec _root_.Run.askB pre x

/-- The checker's text as a plain function of a function O on byte strings, at the hash that O
induces. -/
def chainChkFn (O : ByteArray → ByteArray) (pre : Pre γ) (x : γ) :
    Option (LinkOut 256 ((xdOf S0 stm).L Bd dec)) :=
  match pre x with
  | none => none
  | some (r0, r1, b, i, fin) =>
    if r0.size = 32 ∧ r1.size = 32 ∧ withinT (withStatement S0 (stm r0 r1)) = true then
      chainPost Bd S0 stm dec r0 r1 fin
        (_root_.Fmt.readChainX (m := Id) (_root_.Fmt.HO O) (withStatement S0 (stm r0 r1)) [] b i)
    else none

/-- If at the oracle g every `ask s` gives `O s`, the value at g of the checker that asks by `ask`
is the plain function at O. -/
theorem chainChkBy_det (ask : ByteArray → ZKCP.OComp 256 ByteArray) (g : Fam (rom 256))
    (O : ByteArray → ByteArray) (h : ∀ s, (ask s).det (g ()) = O s) (pre : Pre γ) (x : γ) :
    (chainChkBy Bd S0 stm dec ask pre x).det g = chainChkFn Bd S0 stm dec O pre x := by
  unfold chainChkBy chainChkFn
  cases pre x with
  | none => rfl
  | some p =>
    obtain ⟨r0, r1, b, i, fin⟩ := p
    dsimp only
    by_cases hc : r0.size = 32 ∧ r1.size = 32 ∧ withinT (withStatement S0 (stm r0 r1)) = true
    · rw [if_pos hc, if_pos hc, OComp.det_bind, readByR_det g ask O h]
      rfl
    · rw [if_neg hc, if_neg hc]
      rfl

/-- The value at g of the checker that asks for every hash: the plain function at g's function. -/
theorem det_chainChkAsk_fn (g : Fam (rom 256)) (pre : Pre γ) (x : γ) :
    (chainChkAsk Bd S0 stm dec pre x).det g = chainChkFn Bd S0 stm dec (oB (g ())) pre x :=
  chainChkBy_det Bd S0 stm dec _ g _ (fun _ => rfl) pre x

/-- If every `ask s` tosses no coin and asks at most one question, the checker that asks by `ask`
tosses no coin and asks the oracle at most `CostX.fileNX S0 * 2` strings, whatever the maker's
output. -/
theorem chainChkBy_bound (ask : ByteArray → ZKCP.OComp 256 ByteArray)
    (h : ∀ s, (_root_.Run.qp 256).le (ask s) 1 fun _ => True) (pre : Pre γ) (x : γ) :
    (chainChkBy Bd S0 stm dec ask pre x).NoCoin ∧
      (chainChkBy Bd S0 stm dec ask pre x).QueryBound (OnBytes.Tie.CostX.fileNX S0 * 2) := by
  unfold chainChkBy
  split
  · exact ⟨trivial, trivial⟩
  · rename_i r0 r1 b i fin _
    split
    · have hb := readByR_bound ask h (withStatement S0 (stm r0 r1)) [] b i
      rw [OnBytes.Tie.CostX.fileNX_congr (withStatement S0 (stm r0 r1)) S0 rfl rfl] at hb
      refine ⟨hb.1.bind fun _ => trivial, ?_⟩
      have h2 : ((readByR ask (withStatement S0 (stm r0 r1)) [] b i).bind fun rd =>
          OComp.pure (chainPost Bd S0 stm dec r0 r1 fin rd)).QueryBound
            (OnBytes.Tie.CostX.fileNX S0 * 2 + 0) := hb.2.bind fun _ => trivial
      exact h2
    · exact ⟨trivial, trivial⟩

/-- The checker that asks for every hash tosses no coin and asks at most `CostX.fileNX S0 * 2`
strings. -/
theorem chainChkAsk_bound (pre : Pre γ) (x : γ) :
    (chainChkAsk Bd S0 stm dec pre x).NoCoin ∧
      (chainChkAsk Bd S0 stm dec pre x).QueryBound (OnBytes.Tie.CostX.fileNX S0 * 2) :=
  chainChkBy_bound Bd S0 stm dec _ qp_askB pre x

/-- The roots that the plain function returns are those that `pre` reads off the maker's output. -/
theorem chainChkFn_roots (O : ByteArray → ByteArray) (pre : Pre γ) (x : γ)
    (lo : LinkOut 256 ((xdOf S0 stm).L Bd dec)) (h : chainChkFn Bd S0 stm dec O pre x = some lo) :
    chainRoots pre x = some (lo.1, lo.2.1) := by
  unfold chainChkFn at h
  unfold chainRoots
  split at h
  · cases h
  · rename_i r0 r1 b i fin hpre
    rw [hpre]
    split at h
    · cases e : _root_.Fmt.readChainX (m := Id) (_root_.Fmt.HO O)
          (withStatement S0 (stm r0 r1)) [] b i with
      | none =>
        rw [e] at h
        cases h
      | some on =>
        obtain ⟨o, n⟩ := on
        rw [e] at h
        have h2 : (if fin n && dec (_root_.Fmt.viewX (withStatement S0 (stm r0 r1)) o) then
            (toBPrfX S0.base.plan.salt S0.base.cfg (xdOf S0 stm).C (xdOf S0 stm).ds
              (xdOf S0 stm).a (xdOf S0 stm).xs dec o).map fun π =>
                (bytesToDig r0, bytesToDig r1, asLink (Bd := Bd) (xdOf S0 stm) dec π)
          else none) = some lo := h
        split at h2
        · obtain ⟨π, -, rfl⟩ := Option.map_eq_some_iff.1 h2
          rfl
        · cases h2
    · cases h

/-- The roots that the asking checker returns are those that `pre` reads off the maker's output. -/
theorem chainChkAsk_roots (pre : Pre γ) (g : Fam (rom 256)) (x : γ)
    (lo : LinkOut 256 ((xdOf S0 stm).L Bd dec))
    (h : (chainChkAsk Bd S0 stm dec pre x).det g = some lo) :
    chainRoots pre x = some (lo.1, lo.2.1) :=
  chainChkFn_roots Bd S0 stm dec _ pre x lo
    ((det_chainChkAsk_fn Bd S0 stm dec g pre x).symm.trans h)

end

/-! ## The checker fits the encoding -/

section
variable {γ Bd : Type} (B : BodyD Bd) (S0 : _root_.Fmt.SpecX)
  (stm : ByteArray → ByteArray → ByteArray) (Lf : LeafD (xdOf S0 stm) B) (dec : View → Bool)
  (hcfg : S0.base.cfg.size = 32) (V : StmInv (xdOf S0 stm)) (E : OwnE Bd (xdOf S0 stm))

/-- If the checker that asks returns lo under the oracle with the table put over it, the sibling's
compiled Link verifier accepts lo under the family that is read out of the oracle itself through the
encoding that holds the table's value. The table's value is the one at `s0Of S0.base.params`, the
string at which the checker asks for the digest of the parameter bytes. Asked: that string lies in
S; all strings of S are strings of calls with the number 169; the statement holds the roots
(`RootsIn`); the bounds `FitsS`; of bodies `OwnFits` and `hi`. NOTHING IS PINNED: the reader stands
at the function that `over S T g` induces. From `accepts_allRoots_at`. An implication between two
yeses: nothing on soundness; no probability. -/
theorem chainChkAsk_fit_over (F : FitsS (xdOf S0 stm).base (xdOf S0 stm).K)
    (hOwn : OwnFits B (xdOf S0 stm) Lf E.emb)
    (hi : ∀ p a, B.own (E.emb (.inr p) a) =
      some (leafSL (xdOf S0 stm).C S0.base.plan.salt (xdOf S0 stm).ds ⟨p, a⟩))
    (hroots : RootsIn S0 stm)
    (S : Finset (List Bool)) (T : List Bool → Dig 256)
    (h0S : s0Of S0.base.params ∈ S) (hS : ∀ s ∈ S, IsCall169 s) (pre : Pre γ)
    (g : Fam (rom 256)) (x : γ) (lo : LinkOut 256 ((xdOf S0 stm).L Bd dec))
    (h : (chainChkAsk Bd S0 stm dec pre x).det (over S T g) = some lo) :
    (vLS (WkAny B (xdOf S0 stm) dec E) (256 + 8 * S0.base.plan.salt) 256 lo.1 lo.2.1 lo.2.2).det
      (readBlocks (implAtPd B S0 stm Lf dec hcfg V (T (s0Of S0.base.params))) g) = true := by
  rw [det_chainChkAsk_fn] at h
  unfold chainChkFn at h
  split at h
  · cases h
  · rename_i r0 r1 b i fin _
    split at h
    · rename_i hc
      obtain ⟨h0, h1, hw⟩ := hc
      obtain ⟨hok, hn, honce⟩ := withinT_spec _ stm hw
      cases e : _root_.Fmt.readChainX (m := Id) (_root_.Fmt.HO (oB ((over S T g) ())))
          (withStatement S0 (stm r0 r1)) [] b i with
      | none =>
        rw [e] at h
        cases h
      | some on =>
        obtain ⟨o, n⟩ := on
        rw [e] at h
        have h2 : (if fin n && dec (_root_.Fmt.viewX (withStatement S0 (stm r0 r1)) o) then
            (toBPrfX S0.base.plan.salt S0.base.cfg (xdOf S0 stm).C (xdOf S0 stm).ds
              (xdOf S0 stm).a (xdOf S0 stm).xs dec o).map fun π =>
                (bytesToDig r0, bytesToDig r1, asLink (Bd := Bd) (xdOf S0 stm) dec π)
          else none) = some lo := h
        split at h2
        · rename_i hb
          obtain ⟨π, hπ, rfl⟩ := Option.map_eq_some_iff.1 h2
          have hdec : dec (_root_.Fmt.viewX (withStatement S0 (stm r0 r1)) o) = true :=
            (Bool.and_eq_true_iff.1 hb).2
          have hpd : _root_.Fmt.HO (oB ((over S T g) ())) 169 0 1 _root_.Fmt.zero32 S0.base.params =
              digToBytes (T (s0Of S0.base.params)) := by
            show digToBytes (over S T g () (s0Of S0.base.params)) = _
            rw [over_mem T g h0S]
          obtain ⟨π', hty, hv⟩ := accepts_allRoots_at B S0 stm Lf dec hcfg V E
            (T (s0Of S0.base.params)) F hOwn hi hn honce g (oB ((over S T g) ()))
            (fun _ => size_digToBytes _) hpd (oB_over_call S hS T g) r0 r1 h0 h1
            hok (hroots r0 r1 h0 h1) [] b i o n e hdec
          have eπ : π' = π := Option.some.inj (hty.symm.trans hπ)
          subst eπ
          exact hv
        · cases h2
    · cases h

end

end TypedOracleCompiler.Slice
