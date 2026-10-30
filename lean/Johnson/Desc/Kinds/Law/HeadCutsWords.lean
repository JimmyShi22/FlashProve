-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/HeadCutsWords.lean: Law/HeadCutsK6.lean's headCuts_k6 WITH ITS PREMISE hWord
("the 24th equation": the head's copy of the last stream is the last group's) PAID by

Johnson/P5J/WordsAtQ.lean: words_ownQ: at every witness, from conditions on public letters alone.

  headCuts_k6_words   P5J.HeadCuts pp put (hidAtSeat ...) (headPartK6 ...), under: the scope · the
                   sizes fit (a test with code) · one seat for reader and owner · no place that a
                   borrower's seats name is a pad's place · and the public premises of headCuts_k6.

WHAT IT IS NOT. An implication on letters. PadsFree is a premise here, at letters; at
the composed meaning's constant's terms, under the head, its test with code is padsAtZ
(Law/PadsFreeAtAll.lean: padsFree_atAll); no run of that test is recorded here; sizesFit and
SeatsOne are shown at no plan here. All that Law/HeadCutsK6.lean's head says. Nothing on soundness.
LETTERS. No letter stands under "there is".

-/
import Mathlib
import Johnson.Desc.Kinds.Law.HeadCutsK6
import Johnson.P5J.WordsAtQ

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open OnBytes.Model.Verify (publicOf)
open Inst.Model (ppref ScalesAndPolicy)
open Inst.Model.Layout (kRef hRef)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc (Strs)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.Sound (Mem MsgT SeatsNamed GroupsSeated)

/-- **THE HEAD's FOUR PARTS TOGETHER GIVE THE HEAD's HALF IN PLAIN INTEGERS: NO PREMISE ON A
WITNESS IS LEFT.** -/
theorem headCuts_k6_words {rows cols : Nat} (cs : OnBytes.Codes) {Tok : Type}
    (arr : Nat → Nat → Nat) (msR : List Mem) (N : Numbers) (s : Nat → Cb.Pv.Tail.Size)
    (seat : ∀ k, Fin (s k).NM → Nat → Nat → Nat × Nat × Nat) (Wp : OnBytes.Model.Verify.Public)
    (pl : Nat → Nat × Bool × Nat × Nat) {P : Type} {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy}
    {lay : Option ByteArray} (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (hX : publicOf Z.pol Z.KL lay = .ok Wp) (hr0 : rows ≤ hRef) (hc0 : cols ≤ 2 ^ kRef)
    (tab : Nat → Nat) (put : P5J.TReq → Fin ppref.V → P5J.TReq) (tokV : Tok → Fin ppref.V)
    (req : P × P5J.TS → P5J.TReq)
    (dec : P × P5J.TS → Strs → Option (Fin rows → Fin cols → GE))
    (hSN : SeatsNamed arr N s seat) (hGS : GroupsSeated msR N) (tokH : P × P5J.TS → Fin ppref.V)
    (hplan : (parOf Wp.hS (workOf Wp)).ok = true)
    (htab : ∀ u, u < 2 ^ 16 → (tab u : Int) = Inst.Model.EX u)
    (hfit : Meaning.sizesFit Wp s = true) (hone : Meaning.SeatsOne Wp s seat)
    (hpads : P5J.PadsFree cs arr msR N s seat Wp) :
    P5J.HeadCuts pp put (P5J.hidAtSeat Wp cs arr msR N s seat tokV req dec hSN hGS)
      (headPartK6 cs arr msR N s seat Wp pl tab put
        (P5J.hidAtSeat Wp cs arr msR N s seat tokV req dec hSN hGS) tokH) :=
  headCuts_k6 cs arr msR N s seat Wp pl hZ hR hX hr0 hc0 tab put tokV req dec hSN hGS tokH hplan
    htab fun w => (P5J.words_ownQ hfit hone hSN hGS hpads w).2

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.headCuts_k6_words
