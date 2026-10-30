-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.ClosedOfPins354
import Johnson.Desc.First.CutWritten
/-
Johnson/Loose/H2K12/ToldOfPins354.lean: The proximity test (the kind K12) on the proof file's first
chain, sub-protocol number 354 of the table of joints: THE LAST OF THE SIX CLOSED TESTS OF `PublicLeft354`
(H2K12/PublicAt354.lean), "told": the listed shape of the tree in which the one member sits is what the IOP as
written in Lean tells of it: FROM THE VERIFIER's TWO ENTRY TESTS ON THE WRITTEN VALUES. Definitions, statements
and proofs: calls, one general lemma on lists, closed facts by Lean's kernel with a negative test.
THE ROAD. Where the entry test on the division into sub-protocols accepts, what each sub-protocol of the first
chain tells is a written list (`told_at_written`, Johnson/Desc/First/CutWritten.lean): so what the IOP as written
tells of tree 76 is a closed oracle. Where the entry test on the sendings accepts, the listed shapes are those
of a closed term (`laid_written`, H2K12/ClosedOfPins354.lean). `ShapeIs` of the two is evaluated.
H2K12/ToldAt354.lean goes another road to the same end (`ToldTies`: three of its clauses have no payer); this
file calls nothing of it.
  `oraclesOf_told`: general: what a chain's sub-protocols tell, in order, is what each tells, laid flat.
  `shapeIsB`, `shapeIs_of_B`: `ShapeIs` (Johnson/Desc/K12/Coin/FramesTie.lean) as a test with code.
  `toldB`, `told_full` | `told_full_no`, `told_len`: THE CLOSED FACTS: at tree 76 it accepts; against what is told
    of tree 75 it rejects; more than 76 trees are told.
  `told_of_pins`: the field "told", to the letter.
  `publicLeft_of_two`: `PublicLeft354`, all six fields, from `Written354`, "what is told is the written list", the
    laying's return, an equation on the letter N, and ONE EQUATION ON A RADIUS.
What it is not. NO EXAMPLE BY A THEOREM. THE WRITTEN CUT RESTS ON PRINTS OF LEAN's EVALUATOR: no theorem says that
it is the value's; the entry test compares it at a run (that file's own limit). The full size alone. No soundness
is claimed. Nothing on hiding.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12
open OnBytes Johnson.G
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Numbers toldOf toldCut)
open VerifiableInference.Desc.K12.Door (Laid laidOf laidAtCodes)
open VerifiableInference.Desc.K12.Coin (ShapeIs)

/-- What a chain's sub-protocols tell, in order, is what each tells, laid flat. -/
theorem oraclesOf_told {St Cl : Type} (bs : List (Block St Cl)) :
    oraclesOf bs = (toldOf bs).flatten := by
  unfold oraclesOf toldOf
  rw [List.flatMap_def]
  simp

/-- `ShapeIs`, as a test with code. -/
def shapeIsB (T : TreeShape) (u : VerifiableInference.Desc.Oracle) : Bool :=
  decide (T.mainSymbols.toList = u.tenants.map (·.main)) &&
    decide (T.maskSymbols.toList = u.tenants.map (·.mask)) && decide (T.logN = u.logLength)

theorem shapeIs_of_B {T : TreeShape} {u : VerifiableInference.Desc.Oracle}
    (h : shapeIsB T u = true) : ShapeIs T u := by
  simp only [shapeIsB, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- The listed tree number j against what is told of tree number i, at the written values; it rejects where
either is lacking. -/
def toldB (j i : ℕ) : Bool :=
  match (laidOf codesFull2 noticesFull).bind (·.shapes[j]?), toldCut.flatten[i]? with
  | some T, some u => shapeIsB T u
  | _, _ => false

set_option maxRecDepth 1000000 in
theorem told_full : toldB 76 76 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The negative test: against what is told of the tree in front. -/
theorem told_full_no : toldB 76 75 = false := by decide +kernel

set_option maxRecDepth 1000000 in
theorem told_len : 76 < toldCut.flatten.length := by decide +kernel

/-- **"told", from the two entry tests' equations.** -/
theorem told_of_pins {Zp : ProofFile.Pub} (W : Written354 Zp) (rad : ℕ → ℕ → ℕ) {Xi : Type}
    (G : FileDescription Xi) (hc : toldOf G.first.blocksInOrder = toldCut) (L : Laid)
    (hL : laidAtCodes Zp.first.codes Zp.made.proof.1 = some L) (N : Numbers)
    (hN : N.sent 25 0 = (P5T.numbersOf (P5T.planSeats Zp Zp.D.1)).sent 25 0) :
    ∀ x ∈ P5T.msAtR Zp rad, seatOf x ∈ pinsOpen N O354 25 → MemberTold G L.shapes x := by
  intro x _ hp u T hu hT
  rw [pins_354, hN, sent_of W, List.mem_singleton] at hp
  have e : x.1.seat x.2 = (76, 0) := hp
  rw [e] at hu hT
  unfold FileDescription.oracleAt at hu
  rw [oraclesOf_told, hc, List.append_assoc, List.getElem?_append_left told_len] at hu
  have h := told_full
  unfold toldB at h
  rw [laid_written W L hL] at h
  have hT' : (some L : Option Laid).bind (·.shapes[76]?) = some T := hT
  rw [hT', hu] at h
  exact shapeIs_of_B h

/-- **All six closed tests, from the two entry tests' equations and one equation on a radius.** -/
theorem publicLeft_of_two {Zp : ProofFile.Pub} (W : Written354 Zp) (rad : ℕ → ℕ → ℕ) {Xi : Type}
    (G : FileDescription Xi) (d : First.FoldData) (N : Numbers)
    (hL : laidAtCodes Zp.first.codes Zp.made.proof.1 = some d.L) (hrad : rad 75 0 = e0L)
    (hN : N.sent 25 0 = (P5T.numbersOf (P5T.planSeats Zp Zp.D.1)).sent 25 0)
    (hc : toldOf G.first.blocksInOrder = toldCut) :
    PublicLeft354 Zp.first.codes G d N 25 O354 (P5T.msAtR Zp rad) :=
  publicLeft_of_pins W rad G d N hL hrad hN (told_of_pins W rad G hc d.L hL N hN)

end H2K12

#print axioms H2K12.oraclesOf_told
#print axioms H2K12.shapeIs_of_B
#print axioms H2K12.told_full
#print axioms H2K12.told_full_no
#print axioms H2K12.told_len
#print axioms H2K12.told_of_pins
#print axioms H2K12.publicLeft_of_two
