-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/TieYes.lean: where the entry's checker of OnBytes/Slice/ returns something, the
checker over the sibling does, with the same two roots. The compiler under OnBytes/TypedOracleCompiler/ is the one
that `innerCompiledVerifier` is made with; it builds on definitions of Compile/.


"The line": the files of OnBytes/Slice/ and OnBytes/Tie/, over the library's compiler. "The
sibling": the files of OnBytes/TypedOracleCompiler/: the library's compiler said again, with a list of roots in a
query and a leaf's body of a type that the interface chooses.

WHY. Of the clauses of `Part.OK` two speak only where the checker returns something, and a join asks
of its entry part that a yes of the verifier's step gives the checker's yes with the two roots.

The checker over the sibling differs from the line's in two of its
tests: the limits (`withinT` for `Tie.withinX`) and the typing (the sibling's `toBPrfX`). Reader,
last test and decision are one term in both.

3 DECLARATIONS.
NEW (3).
 `withinT_of_withinX`   the line's limits test implies the sibling's (by `ok_asTypedCompilerDescription`).
 `typed_allRoots`       behind the checker's other tests the sibling's typing makes a string, at any
                        function with answers of 32 bytes (`accG_core`, `accG_reStated`).
 `chainChkFn_of_line`   for every description: where the line's plain function returns something,
                        the sibling's does, with the same two roots.



WHAT IS NOT SAID. THE CONVERSE: that the line's checker returns something wherever the sibling's
does. That the two typed strings are tied beyond the two roots. That either checker
ever returns something.
Two yeses at one oracle: no probability; nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.TieRaw

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (bytesToDig digToBytes size_digToBytes oB)
open _root_.Run.PQ (View SgX)
open TypedOracleCompiler.Run
open TypedOracleCompiler.Run.PQ (BodyD OwnE leafSL withStatement)
open OnBytes.Slice (RootsIn over)

/-! ## The limits -/

/-- The limits test of OnBytes/Tie/ implies the sibling's. -/
theorem withinT_of_withinX (S : _root_.Fmt.SpecX) (hw : OnBytes.Tie.withinX S = true) :
    withinT S = true := by
  unfold OnBytes.Tie.withinX at hw
  unfold withinT
  simp only [Bool.and_eq_true] at hw ⊢
  exact ⟨⟨ok_asTypedCompilerDescription (OnBytes.Tie.xdOf S fun _ _ => ByteArray.empty) hw.1.1, hw.1.2⟩, hw.2⟩

/-! ## The typing does not refuse what the reader has read -/

section
variable {Bd : Type} (B : BodyD Bd) (S0 : _root_.Fmt.SpecX)
  (stm : ByteArray → ByteArray → ByteArray) (dec : View → Bool) (E : OwnE Bd (PQ.xdOf S0 stm))

/-- Behind the checker's other tests the sibling's typing makes a string: of what the strict
reader, at the hash of any function O with answers of 32 bytes, has read under the statement of two
roots of 32 bytes, if the description with that statement is within the sibling's limits, the
statement's items hold the roots, and the decision says yes. The first half of
`accepts_allRoots_at`. Some embedding of own symbols that spells them as the format does and meets
no stored symbol is asked to exist; the typing does not read it. -/
theorem typed_allRoots
    (hi : ∀ p a, B.own (E.emb (.inr p) a) =
      some (leafSL (PQ.xdOf S0 stm).C S0.base.plan.salt (PQ.xdOf S0 stm).ds ⟨p, a⟩))
    (hns : ∀ p a, B.getE (E.emb (.inr p) a) = none)
    (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32)
    (r0 r1 : ByteArray) (h0 : r0.size = 32) (h1 : r1.size = 32)
    (hw : withinT (withStatement S0 (stm r0 r1)) = true)
    (hroot : ∀ t ∈ S0.stored.flatten,
      _root_.Fmt.itemRoot (stm r0 r1) t.item = some (if t.item == 1 then r1 else r0))
    (seen : _root_.Fmt.Seen) (b : ByteArray) (i : ℕ) (o : _root_.Fmt.ChainOut) (j : ℕ)
    (e : _root_.Fmt.readChainX (m := Id) (_root_.Fmt.HO O) (withStatement S0 (stm r0 r1)) seen b i =
      some (o, j))
    (hdec : dec (_root_.Fmt.viewX (withStatement S0 (stm r0 r1)) o) = true) :
    ∃ π, PQ.toBPrfX S0.base.plan.salt S0.base.cfg (PQ.xdOf S0 stm).C (PQ.xdOf S0 stm).ds
      (PQ.xdOf S0 stm).a (PQ.xdOf S0 stm).xs dec o = some π := by
  obtain ⟨hok, hn, honce⟩ := withinT_spec _ stm hw
  have A := (PQ.accG_reStated B S0 (stm r0 r1) stm _ O dec (bytesToDig r0) (bytesToDig r1) o).1
    (PQ.accG_core B (withStatement S0 (stm r0 r1)) stm dec O hO _ r0 r1 h0 h1 hok hn honce rfl hroot
      rfl seen b i o j e hdec)
  obtain ⟨π, t1, -⟩ := A E.emb hi hns
  exact ⟨π, t1⟩

/-! ## Where the checker of OnBytes/Slice/ returns something, the sibling's does -/

variable {γ : Type}

/-- Where the plain function of OnBytes/Slice/ChainChkAsk.lean returns something, the sibling's
does, with the same two roots. Guard: `withinT_of_withinX`. Reader, last test and decision are one
term in both. Typing: `typed_allRoots`. One way. -/
theorem chainChkFn_of_line
    (hi : ∀ p a, B.own (E.emb (.inr p) a) =
      some (leafSL (PQ.xdOf S0 stm).C S0.base.plan.salt (PQ.xdOf S0 stm).ds ⟨p, a⟩))
    (hns : ∀ p a, B.getE (E.emb (.inr p) a) = none)
    (hroots : RootsIn S0 stm) (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32)
    (pre : Pre γ) (x : γ)
    (lo : OnBytes.Slice.LinkOut 256 ((OnBytes.Tie.xdOf S0 stm).L dec))
    (h : OnBytes.Slice.chainChkFn S0 stm dec O pre x = some lo) :
    ∃ lo', chainChkFn Bd S0 stm dec O pre x = some lo' ∧ lo'.1 = lo.1 ∧ lo'.2.1 = lo.2.1 := by
  unfold OnBytes.Slice.chainChkFn at h
  unfold chainChkFn
  split at h
  · cases h
  · rename_i r0 r1 b i fin hpre
    rw [hpre]
    split at h
    · rename_i hc
      obtain ⟨h0, h1, hw⟩ := hc
      have hwT : withinT (withStatement S0 (stm r0 r1)) = true := withinT_of_withinX _ hw
      show ∃ lo', (if r0.size = 32 ∧ r1.size = 32 ∧
          withinT (withStatement S0 (stm r0 r1)) = true then
          chainPost Bd S0 stm dec r0 r1 fin
            (_root_.Fmt.readChainX (m := Id) (_root_.Fmt.HO O) (withStatement S0 (stm r0 r1)) [] b
              i)
        else none) = some lo' ∧ lo'.1 = lo.1 ∧ lo'.2.1 = lo.2.1
      rw [if_pos ⟨h0, h1, hwT⟩]
      cases e : _root_.Fmt.readChainX (m := Id) (_root_.Fmt.HO O) (withStatement S0 (stm r0 r1)) []
          b i with
      | none =>
        have e' : _root_.Fmt.readChainX (m := Id) (_root_.Fmt.HO O)
            (OnBytes.Slice.reStated S0 (stm r0 r1)) [] b i = none := e
        rw [e'] at h
        cases h
      | some on =>
        obtain ⟨o, n⟩ := on
        have e' : _root_.Fmt.readChainX (m := Id) (_root_.Fmt.HO O)
            (OnBytes.Slice.reStated S0 (stm r0 r1)) [] b i = some (o, n) := e
        rw [e'] at h
        have h2 : (if fin n && dec (_root_.Fmt.viewX (withStatement S0 (stm r0 r1)) o) then
            (_root_.Run.PQ.toBPrfX S0.base.plan.salt S0.base.cfg (OnBytes.Tie.xdOf S0 stm).C
              (OnBytes.Tie.xdOf S0 stm).ds (OnBytes.Tie.xdOf S0 stm).a (OnBytes.Tie.xdOf S0 stm).xs
              dec o).map fun π =>
                (bytesToDig r0, bytesToDig r1, OnBytes.Slice.asLink (OnBytes.Tie.xdOf S0 stm) dec π)
          else none) = some lo := h
        split at h2
        · rename_i hb
          obtain ⟨π, -, rfl⟩ := Option.map_eq_some_iff.1 h2
          obtain ⟨π', hπ'⟩ := typed_allRoots B S0 stm dec E hi hns O hO r0 r1 h0 h1 hwT
            (hroots r0 r1 h0 h1) [] b i o n e (Bool.and_eq_true_iff.1 hb).2
          refine ⟨(bytesToDig r0, bytesToDig r1, PQ.asLink (Bd := Bd) (PQ.xdOf S0 stm) dec π'), ?_,
              rfl, rfl⟩
          show (if fin n && dec (_root_.Fmt.viewX (withStatement S0 (stm r0 r1)) o) then
            (PQ.toBPrfX S0.base.plan.salt S0.base.cfg (PQ.xdOf S0 stm).C (PQ.xdOf S0 stm).ds
                (PQ.xdOf S0 stm).a (PQ.xdOf S0 stm).xs dec o).map
              fun π => (bytesToDig r0, bytesToDig r1, PQ.asLink (Bd := Bd) (PQ.xdOf S0 stm) dec π)
            else none) = _
          rw [if_pos hb, hπ']
          rfl
        · cases h2
    · cases h

end

/-! ## A digest of 32 bytes as a variable

-/

end TypedOracleCompiler.Slice
