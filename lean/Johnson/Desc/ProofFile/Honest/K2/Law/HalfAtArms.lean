-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/HalfAtArms.lean: the kind "the code switch" (K2): WHAT THE
PROVER THAT `onlineProverFromPublicFiles` RETURNS HOLDS AT THE KIND's TWO ARMS' PLACES (the output head's switch; the
switch behind the last segment), THE FILLING A LETTER: the search in its first list finds the kind's
half. The sisters of `link_half_fill` (AtFill.lean of this folder, of other authors), which stands
at the 23 links' places. Statements with their proofs: joins; no definition.

WHICH SLOT IT IS FOR. It pays the first of the four premises that `head_playsS_head` and
`fin_playsS_head` (PlaysAtArms.lean of this folder) leave, at the prover that the frame's maker
returns: a sentence on the filling's lots. `head_acceptedS_head` and `fin_acceptedS_head`
(AcceptedAtArms.lean of this folder) ask that the search finds some half, and that it has two
rounds: the first is had by this; the second, of `switchHalf`, is not shown here.

  `switch_half_fill`   A TOOL, GENERAL IN THE PLACE: at a member p of `switchPlaces` whose place is
                    of the kind K2. AT A LINK's PLACE IT SAYS WHAT `link_half_fill` SAYS: it is
                    typed for the arms
  `head_half_fill`, `fin_half_fill`   THE ENDS

hex: some lot of P lays the switch's lot's halves. ho: every lot of P lays no half at a place of the
kind K2, or lays just these. Both speak of one kind.

By, of other authors, each called once: `atPure_ok` (Honest/AtPureLaw.lean) · `fill_find_eq`
(Honest/Thread/FirstFillPairs.lean) · `k2_find_at` (Honest/Thread/FirstFillK2.lean).

Limits. THAT `onlineProverFromPublicFiles` RETURNS AT P IS A PREMISE. hex AND ho ARE PREMISES: no filling is named at
which they hold. That a member of `switchPlaces` stands at either arm's place is not said here: p is
a letter with its equation. Which half stands at a place: public data and two letters: no run, no
coin, no thread. All five types of the filling are letters. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstFillPairs
import Johnson.Desc.ProofFile.Honest.Thread.FirstFillK2
import Johnson.Desc.ProofFile.Honest.K2.Exact
import Johnson.Desc.K2.Honest.Returns.SeatAtArms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open OnBytes
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K2.Honest.Returns (headPlaceAt)
open IM (k2PlaceF)
open P5J (F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

variable {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {Wp : VerifierAndGoals.PublicFiles} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}

/-- hA, hex AND ho ARE PREMISES. **A TOOL, GENERAL IN THE PLACE: the search in the prover's first
list finds the kind's half: the filling a letter.** -/
theorem switch_half_fill
    (O : IM.Open OnBytes.secondHashFunction Wp.pol Wp.lay Wp.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Wp.pol Wp.lay Wp.KL P = .ok A) (Dt : RowDataOf ProofFile.Inst)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers)
    (hex : ∃ M ∈ P.lots, M.halves A.Z A.G = (switchLot (X := X) Dt readers).halves A.Z A.G)
    (ho : ∀ M ∈ P.lots, (∀ y ∈ M.halves A.Z A.G, y.place.kind ≠ .K2) ∨
      M.halves A.Z A.G = (switchLot (X := X) Dt readers).halves A.Z A.G)
    {p : SwitchPlace} (hp : p ∈ switchPlaces Zp Bs.G₀) (hk : p.place.kind = .K2) :
    (A.H.first.find? fun a => a.place == p.place) =
      some (switchHalf (coreSender freshTable) Dt readers
        (lotClosingAt Bs.G₀.first.layout (segmentsOf Zp Bs.G₀)) p) := by
  obtain ⟨hZ, hG, -⟩ := atPure_ok hA
  obtain rfl : A.Z = Zp := Except.ok.inj (hZ.symm.trans O.pub)
  have eG : A.G = Bs.G₀ := Option.some.inj (hG.symm.trans O.blank)
  have e1 := FirstFill.fill_find_eq hA hex ho (p := p.place) hk
  have e2 := FirstFill.k2_find_at (X := X) Dt readers A.Z A.G O (p := p) (by rw [eG]; exact hp)
  rw [e1, e2, eG]
  rfl

/-- hA, hex AND ho ARE PREMISES. **At the output head's switch.** -/
theorem head_half_fill
    (O : IM.Open OnBytes.secondHashFunction Wp.pol Wp.lay Wp.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Wp.pol Wp.lay Wp.KL P = .ok A) (Dt : RowDataOf ProofFile.Inst)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers)
    (hex : ∃ M ∈ P.lots, M.halves A.Z A.G = (switchLot (X := X) Dt readers).halves A.Z A.G)
    (ho : ∀ M ∈ P.lots, (∀ y ∈ M.halves A.Z A.G, y.place.kind ≠ .K2) ∨
      M.halves A.Z A.G = (switchLot (X := X) Dt readers).halves A.Z A.G)
    {p : SwitchPlace} (hp : p ∈ switchPlaces Zp Bs.G₀) (hpp : p.place = headPlaceAt) :
    (A.H.first.find? fun a => a.place == p.place) =
      some (switchHalf (coreSender freshTable) Dt readers
        (lotClosingAt Bs.G₀.first.layout (segmentsOf Zp Bs.G₀)) p) :=
  switch_half_fill O hA Dt readers hex ho hp (by rw [hpp])

/-- hA, hex AND ho ARE PREMISES. **At the switch behind the last segment.** -/
theorem fin_half_fill
    (O : IM.Open OnBytes.secondHashFunction Wp.pol Wp.lay Wp.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Wp.pol Wp.lay Wp.KL P = .ok A) (Dt : RowDataOf ProofFile.Inst)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers)
    (hex : ∃ M ∈ P.lots, M.halves A.Z A.G = (switchLot (X := X) Dt readers).halves A.Z A.G)
    (ho : ∀ M ∈ P.lots, (∀ y ∈ M.halves A.Z A.G, y.place.kind ≠ .K2) ∨
      M.halves A.Z A.G = (switchLot (X := X) Dt readers).halves A.Z A.G)
    {p : SwitchPlace} (hp : p ∈ switchPlaces Zp Bs.G₀) (hpp : p.place = k2PlaceF) :
    (A.H.first.find? fun a => a.place == p.place) =
      some (switchHalf (coreSender freshTable) Dt readers
        (lotClosingAt Bs.G₀.first.layout (segmentsOf Zp Bs.G₀)) p) :=
  switch_half_fill O hA Dt readers hex ho hp (by rw [hpp])

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.switch_half_fill
#print axioms ProofFile.Honest.K2.Law.head_half_fill
#print axioms ProofFile.Honest.K2.Law.fin_half_fill
