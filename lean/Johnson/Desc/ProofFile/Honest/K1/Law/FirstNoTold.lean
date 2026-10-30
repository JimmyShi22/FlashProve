-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/FirstNoTold.lean: THE SHARED "SENDING" (the kind K1) IN THE
FRAME FOR THE HONEST SIDE: THE NUMBER THAT A JOB's FIRST NEW MESSAGE GETS (lotNo,
Honest/K1/LotNoPure.lean) IS THE TABLE's OWN NUMBER OF MESSAGES AT THE PLACE (Numbers.msgsAt, filled
off what the blocks tell). Statements and proofs; no definition. PUBLIC: no coin, no witness, no
input.

  firstNoOf_idx   on a list of blocks: firstNoOf at a place that stands in the list is what the
                blocks in front of its first block tell (msgsTold, Johnson/Desc/First/BookFit.lean)
  firstNoAt_told  the same of the total form
  firstNo_withTold   so, at numbers that are filled off the telling (Numbers.withTold) at the
                blocks' own list of places: msgsAt (some p) = firstNoAt bs p
  lotNo_made    THE DESCRIPTION THAT lotNo MAKES ANEW IS onlineDescription's OWN VALUE: where onlineDescription
                returns and is opened (IM.Open, Johnson/IMR/SeatOpen.lean): lotNo o Z a =
                firstNoAt c.blocksInOrder a
  firstNo_laid  in scope, where the value is laid (P5J.LaidAt, Johnson/P5J/LaidOpens.lean):
                (P5J.At.N Zp cF).msgsAt (some p) = lotNo secondHashFunction Zp p at every written place
  firstNo_at_head, firstNo_at   under the one head (P5J.AtMg); at a place by its number

WHY THE THIRD GROUND FALLS. lotNo calls onlineDescriptionFromPublicPart Z (pureSeat o Z) by itself. Under the head the first
chain cF is the chain of onlineDescription's value at the same three files (LaidAt.value, LaidAt.opened), and
onlineDescription is onlineDescriptionFromPublicPart at pureSeat behind the public part (descPure_made,
Johnson/Desc/ProofFile/Law/MakerPublic.lean): one function at one argument: one value.

By lotNo_at (Honest/K1/LotNoAt.lean), places_scope (Johnson/IMR/PlacesScope.lean), places_written
(Johnson/LPFK9R/HtinAtConstant.lean).

Limits. AT THE HEAD's OWN PUBLIC PART Zp: that a prover's ground is made of that public part is not
said here. The head is a hypothesis. The full size alone from firstNo_laid on. Of the first chain
alone. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.LotNoAt
import Johnson.Desc.ProofFile.Law.MakerPublic
import Johnson.Desc.Sound.PieceFence
import Johnson.IMR.PlacesScope
import Johnson.LPFK9R.HtinAtConstant
import Johnson.P5J.AtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Place FileDescription)
open VerifiableInference.Desc.First (Numbers msgsTold)
open OnBytes.Maker (WholeD)

variable {S Cl : Type}

/-- **firstNoOf at a place that stands in the list is what the blocks in front of its first block
tell.** -/
theorem firstNoOf_idx : ∀ (bs : List (Block S Cl)) (a : Place), a ∈ bs.map (·.place) →
    firstNoOf bs a = some (msgsTold (Sound.toldOf bs) ((bs.map (·.place)).idxOf a))
  | [], a, h => by cases h
  | b :: bs, a, h => by
    by_cases hb : b.place = a
    · subst hb
      have e0 : ((b :: bs).map (·.place)).idxOf b.place = 0 := by
        show (b.place :: bs.map (·.place)).idxOf b.place = 0
        exact List.idxOf_cons_self
      rw [e0]
      unfold firstNoOf
      rw [beq_self_eq_true]
      rfl
    · have hmem : a ∈ bs.map (·.place) := by
        rw [List.map_cons] at h
        rcases List.mem_cons.1 h with e | e
        · exact absurd e.symm hb
        · exact e
      have hq : (b.place == a) = false := beq_eq_false_iff_ne.2 hb
      have ih := firstNoOf_idx bs a hmem
      have e1 : ((b :: bs).map (·.place)).idxOf a = (bs.map (·.place)).idxOf a + 1 := by
        show (b.place :: bs.map (·.place)).idxOf a = _
        exact List.idxOf_cons_ne _ hb
      have e2 : msgsTold (Sound.toldOf (b :: bs)) ((bs.map (·.place)).idxOf a + 1) =
          ((b.oracles.flatMap id).map fun o => o.tenants.length).sum +
            msgsTold (Sound.toldOf bs) ((bs.map (·.place)).idxOf a) := rfl
      unfold firstNoOf
      rw [hq, ih, e1, e2, List.flatMap_id, Nat.add_comm]
      rfl

/-- The same of the total form. -/
theorem firstNoAt_told (bs : List (Block S Cl)) (a : Place) (h : a ∈ bs.map (·.place)) :
    firstNoAt bs a = msgsTold (Sound.toldOf bs) ((bs.map (·.place)).idxOf a) := by
  unfold firstNoAt
  rw [firstNoOf_idx bs a h]
  rfl

/-- **At numbers that are filled off the telling, at the blocks' own list of places.** -/
theorem firstNo_withTold (N₀ : Numbers) (ps : List Place) (bs : List (Block S Cl))
    (hps : bs.map (·.place) = ps) {p : Place} (hp : p ∈ ps) :
    (N₀.withTold ps (Sound.toldOf bs)).msgsAt (some p) = firstNoAt bs p := by
  subst hps
  rw [firstNoAt_told bs p hp]
  rfl

/-- **THE DESCRIPTION THAT lotNo MAKES ANEW IS onlineDescription's OWN VALUE.** -/
theorem lotNo_made {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
    {base : List (Block VerifiableInference.Desc.First.S ProofFile.Cl)}
    {c : Chain VerifiableInference.Desc.First.S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hF : ProofFile.onlineDescription o pol lay KL = .ok F) (O : IM.Open o pol lay KL F Z Bs base c A B)
    (a : Place) : lotNo o Z a = firstNoAt c.blocksInOrder a := by
  obtain ⟨Z', hZ', hz⟩ := ProofFile.Law.descPure_made hF
  obtain rfl : Z' = Z := Except.ok.inj (hZ'.symm.trans O.pub)
  rw [lotNo_at o Z' F hz a]
  have e := O.desc
  subst e
  rfl

/-- **In scope, where the value is laid: the table's number of messages at a written place is
lotNo's.** -/
theorem firstNo_laid {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {D : WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    (hS : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (L : P5J.LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) {p : Place}
    (hp : p ∈ P5J.At.ps) :
    (P5J.At.N Zp cF).msgsAt (some p) = lotNo OnBytes.secondHashFunction Zp p := by
  obtain ⟨Bs, base, O⟩ := L.opened
  have hps : cF.blocksInOrder.map (·.place) = P5J.At.ps :=
    (IM.places_scope hS hR O).trans LPFK9.places_written.symm
  rw [lotNo_made L.value O p]
  exact firstNo_withTold _ P5J.At.ps cF.blocksInOrder hps hp

/-- Under the one head. -/
theorem firstNo_at_head {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {p : Place} (hp : p ∈ P5J.At.ps) :
    (P5J.At.N Zp cF).msgsAt (some p) = lotNo OnBytes.secondHashFunction Zp p :=
  firstNo_laid h.scope h.reads h.laid hp

/-- At a place by its number: under the record's own field placeAt. -/
theorem firstNo_at {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {b : Nat} {p : Place}
    (hp : (P5J.At.ps)[b]? = some p) :
    (P5J.At.N Zp cF).msgsAt (some p) = lotNo OnBytes.secondHashFunction Zp p :=
  firstNo_at_head h (List.mem_of_getElem? hp)

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.firstNoOf_idx
#print axioms ProofFile.Honest.K1.firstNoAt_told
#print axioms ProofFile.Honest.K1.firstNo_withTold
#print axioms ProofFile.Honest.K1.lotNo_made
#print axioms ProofFile.Honest.K1.firstNo_laid
#print axioms ProofFile.Honest.K1.firstNo_at_head
#print axioms ProofFile.Honest.K1.firstNo_at
