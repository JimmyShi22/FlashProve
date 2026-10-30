-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/ShutFactsPaid.lean: A PAYMENT BENEATH THE SHUTTING's LIST OF DEBTS
(`ShutList`, ShutList.lean): ITS FIELD hS ENDS IN `ShutFacts Zc ps.base a.1` (FifthTieShut.lean):
here
that sentence is had from the facts on reached states (`FoldFacts`,
Johnson/Desc/First/FoldFacts.lean).
Two theorems.

  `firstTree_at`: where the proof file's own maker makes the public part Z: AT EVERY m', whether a
    switch opens group m' + 1 or none does, the number of the first tree that `ShutFacts.ord` names
    is 0. (Where there is no such place the numbers are the default's, whose first tree is 0; where
    there is one it is the chain's first, which is 0.) SO THE CLAUSE "FOR ALL m'" OF
`ShutFacts.ord`,
    WHICH IS NOT FENCED BY "carry m' rides", CAN BE MET.
  `shutFacts_of_fold`: **FoldFacts Rz at_ d reqW links pl · d.ft = 0 · Z is made · reached · no mark
·
    rows · size ⊢ ShutFacts Z base (at_ a).2.** ord: bookInOrder; fit: bookFits.
Limits. TWO OF THE FOUR FACTS STAY PREMISES: rows (to the letter the field rowsSent of FoldFacts)
and size (the book holds at most base trees). FoldFacts'
own fields are shown in Johnson/P5J/FoldJ3Whole.lean (P5J.foldFacts_at_head') at the letters
fun a => a.1 · At.foldD Zp cF L · At.reqW · At.links · At.ps, under h : P5J.AtMg at secondHashFunction, hR, hl,
hs and hB; NO MEMBER is shown there. No soundness statement.

-/
import Johnson.Desc.First.Link.Law.FifthTieShut
import Johnson.Desc.First.FoldFacts
import Johnson.IMR.SeatKeeps
import Johnson.Top.H0.K2Hears.FtAtPub

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S ModelPart FoldFacts FoldData)
open VerifiableInference.Desc.First.K2 (par9)

/-- par9 keeps the first tree. -/
theorem par9_firstTree (p : VerifiableInference.Desc.First.K2.P2) :
    (par9 p).firstTree = p.firstTree := by
  unfold par9
  split <;> rfl

/-- **At every m' the first tree that `ShutFacts.ord` names is 0.** -/
theorem firstTree_at {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z) (m' : ℕ) :
    (par9 (ProofFile.pAtK2 Z m')).firstTree = 0 := by
  rw [par9_firstTree]
  unfold ProofFile.pAtK2
  cases h : ProofFile.pAtK2? Z m' with
  | none => rfl
  | some p =>
    show p.firstTree = 0
    unfold ProofFile.pAtK2? at h
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
    have hm := List.mem_of_find?_eq_some hx
    unfold ProofFile.k2SpotsAt at hm
    cases hG : ProofFile.blankBy ProofFile.pureRoad.links Z with
    | none =>
      rw [hG] at hm
      cases hm
    | some G =>
      rw [hG] at hm
      exact (Meaning.K2.pureSpots_firstTree (G := G) hm).trans (P1K2.firstTree_of_pub hZ)

/-- **`ShutFacts` FROM THE FACTS ON REACHED STATES.** -/
theorem shutFacts_of_fold {X P : Type} {Rch : ℕ → X → Prop} {at_ : X → P × S} {d : FoldData}
    {reqW : P → Array UInt32} {links : List ModelPart} {ps : List Place}
    (FF : FoldFacts Rch at_ d reqW links ps) (hft : d.ft = 0)
    {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (hZ : ProofFile.pureRoad.pub o pol lay KL = .ok Z) {k : ℕ} {a : X} (hR : Rch k a)
    (hu : (at_ a).2.failed = none) (base : ℕ)
    (hrows : ∀ o ∈ singleRowsOracles (at_ a).2.live.frame.rows, o < (at_ a).2.book.place.size)
    (hsize : (at_ a).2.book.trees.size ≤ base) : ShutFacts Z base (at_ a).2 where
  ord m' := by
    rw [firstTree_at hZ m', ← hft]
    exact FF.bookInOrder k a hR hu
  fit := FF.bookFits k a hR hu
  rows := hrows
  size := hsize

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.firstTree_at
#print axioms VerifiableInference.Desc.LinkJoin.shutFacts_of_fold
