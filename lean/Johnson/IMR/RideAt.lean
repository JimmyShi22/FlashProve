--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/RideAt.lean: IN THE GOALS' SCOPE, AT THE OLDER HASH: AT THE 101 NUMBERS
OF THE FIRST CHAIN WHOSE KIND IS K3, K4, K5, K6, K8 OR K11: every accepting step of the sub-protocol
AS IT IS SEATED is Quiet, Outer and leaves the open link's context. One theorem, proved.



  three_at   c.blocksInOrder[k]? = some b, b's kind one of the six, b.step ft s rs cols = .ok (s', n): Quiet
    s s' ∧ Outer s s' ∧ SameLink s s': the three premises of more_quiet
    (Johnson/Goal/Meaning/QuietRide.lean). By the case split flat_cases: such a
    number stands in front of a batching, behind the link's first place; the seated form's accepting
    is its lot's own's (alone_underR); quiet_lot, outer_lot, link_lot.

OBJECT: c.blocksInOrder[k]. USER: none in Lean yet. LETTERS: ft, s, rs, cols: free.

What is not claimed. Anything on the public items. No soundness.
-/
import Johnson.IMR.SendsLeft
import Johnson.IMR.ShapesJoin
import Johnson.IMR.OuterLot

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName OpenedColumn)
open VerifiableInference.Desc.First (S kindsBeforeBatching closeKinds backKinds)
open Meaning.K2 (Quiet)
open Meaning.Out (Outer)
open Meaning.Lnk (SameLink)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **THE THREE RELATIONS AT OUR 101 NUMBERS.** -/
theorem three_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {k : ℕ} {b : Block S Cl}
    (hb : c.blocksInOrder[k]? = some b) (hq : quietMaker b.place.kind = true) {ft : ℕ} {s s' : S}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} {n : ℕ} (hy : b.step ft s rs cols = .ok (s', n)) :
    Quiet s s' ∧ Outer s s' ∧ SameLink s s' := by
  have hkind : kindW k = some b.place.kind := by
    unfold kindW
    rw [place_at hS hR O hb]
    rfl
  cases flat_cases hS hR O k b hb with
  | front b hr hd =>
    rw [kinds_ends.1] at hkind
    rw [← Option.some.inj hkind] at hq
    exact absurd hq (by decide)
  | laid l hl b hr hd =>
    rw [(kinds_at hl).1] at hkind
    rw [← Option.some.inj hkind] at hq
    exact absurd hq (by decide)
  | first l hl k0 b b' hk lot hp hj =>
    rw [joined_spot hj] at hq
    have hq' : quietMaker k0 = true := hq
    exfalso
    by_cases h24 : l < 24
    · have e := (first_kind l h24).symm.trans hk
      by_cases h0 : l = 0
      · rw [if_pos h0] at e
        rw [← Option.some.inj e] at hq'
        exact absurd hq' (by decide)
      · rw [if_neg h0] at e
        rw [← Option.some.inj e] at hq'
        exact absurd hq' (by decide)
    · obtain rfl : l = 24 := by omega
      obtain rfl : KindName.K7 = k0 := Option.some.inj hk
      exact absurd hq' (by decide)
  | hear l hl i hi k0 b b' name hk lot hp hla =>
    obtain ⟨L, hL, hb'⟩ := lot
    have hq' : quietMaker b'.place.kind = true := by
      rw [alone_place hla] at hq
      rw [hp]
      exact hq
    have hy' := VerifiableInference.Desc.step_under (alone_underR hla) hy
    obtain ⟨-, -, -, hd⟩ := VerifiableInference.Desc.step_inv ft b' s s' rs cols n hy'
    exact ⟨quiet_lot hL hb' hq' s _ _ s' hd, outer_lot hL hb' hq' s _ _ s' hd,
      link_lot hL hb' hq' s _ _ s' hd⟩
  | batch l hl Lk p e1 hp hal =>
    rw [(kinds_at hl).2.1] at hkind
    rw [← Option.some.inj hkind] at hq
    exact absurd hq (by decide)
  | behind l hl Lk b e1 hr hd =>
    rw [(kinds_at hl).2.2.1] at hkind
    rw [← Option.some.inj hkind] at hq
    exact absurd hq (by decide)
  | close l hl p Q q k0 b x hp hQ hk ex hla =>
    rw [alone_place hla] at hq
    have hm := List.mem_of_getElem? hk
    have hq' : quietMaker k0 = true := hq
    exfalso
    clear hq hla hk hkind hb ex hy
    revert hm hq'
    cases k0 <;> decide
  | cleared l hl fs f b hfs hf hr hd =>
    rw [(kinds_at hl).2.2.2.2.2.2] at hkind
    rw [← Option.some.inj hkind] at hq
    exact absurd hq (by decide)
  | back q k0 b b' name hk lot hp hla =>
    have hq' : quietMaker k0 = true := by
      have e : b.place = { chain := 1, link := none, piece := q + 1, kind := k0 } :=
        alone_place hla
      have hq2 : quietMaker b.place.kind = true := hq
      rw [e] at hq2
      exact hq2
    have hm := List.mem_of_getElem? hk
    exfalso
    clear hq hla hk hkind hb hy hp lot
    revert hm hq'
    cases k0 <;> decide
  | last lot hla =>
    rw [kinds_ends.2.2] at hkind
    rw [← Option.some.inj hkind] at hq
    exact absurd hq (by decide)

end IM

#print axioms IM.three_at
