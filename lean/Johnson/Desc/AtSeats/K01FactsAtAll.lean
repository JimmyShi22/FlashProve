-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/K01FactsAtAll.lean: KIND K1's PREMISE ALONG REACHED STATES,
hFacts OF k01_fifty_atThree, PAID AT THE CLOSED CONSTANT BY CALLS, but for its clause on
the letter xb. hFacts asks, at the two borders of each of the fifty later sendings, at every reached
state without a mark: FactsK13 (the nine tests of NineK13 and the silence of the wider public tests
at eight names); of the open segment's own copy: its frame's group is the listed one and its frame's
shape the public one; and xb.

OBJECT. hFacts at Dm := hA.𝔇, dk := d12Full, Rch := "reached, with a typed public part".
USER. k01_fifty_atThree's caller at the constant (P5J.mgAtAll): hFacts falls; hLT and hX come in.
LETTERS. Zl, D, r₀, Zp, Np, cF, x₀: the head's own. xb: the kind's letter.

CLAUSE BY CLAUSE: the payer, its file.
  FactsK13's nine   nine_reached (K13NineAtAll.lean: twelve fields of the structure of
                    fold facts, each another file's theorem, called there)
  FactsK13's tenth  fillsK13C_base … .quiet (FillsAtBase.lean), as in the row of K13
  the group         groupIs_field (Johnson/IMR/GroupField.lean), at its written
                    list of places, which is the laws' own by linksW_full
                    (Johnson/LPFK9R/SubsFull.lean); the listed group of segment l is l by unfolding
  the shape         liveShape_field (Johnson/IMR/AtReach.lean)
THE TWO PREMISES THAT COME IN.
  hLT   the places at the two borders of each of the fifty are places of that segment: the very
        statement of link_two (a theorem, by Lean's kernel). It stands in a
        file above the kind's whole law, which is not on this file's ground: so it is handed in.
  hX    the clause on xb, as it stands in hFacts: left to the kind's own law.
Main names.
  factsK13_reached   FactsK13 at the constant, at every reached state without a mark
  live_reached       the two equations on the open segment's own copy, at a place of segment l
  **factsK1_atAll**  hFacts in a form without the table's promise at the border
  **factsK1_atAllQ** hFacts as k01_fifty_atThree has it: behind the table's promise at the border;
                     the promise is spent by nothing here: it is handed on to hX alone

What is not claimed. That hA or hP1 can be met: NO MEMBER. hX. Nothing on soundness.

-/
import Johnson.Desc.AtSeats.K13NineAtAll
import Johnson.IMR.GroupField
import Johnson.IMR.K1Scope
import Johnson.LPFK9R.SubsFull

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K13.Law

open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice OnBytes.Maker OnBytes.Flat KObj Iop Run
open OnBytes.Road OnBytes.RunA
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers start flatPlacesOf endAsks)
open ProofFile (Cl)
open Johnson.Desc.First.Walk.Tied (Reach RchAt RchPub rchAt_raw)
open VerifiableInference.PlanWritten (madePinnedAt)
open IM (k1Ix)

section
variable {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S Cl} {x₀ : First.Look.Place}
  (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
include hA

/-- **FactsK13 at the constant, at every reached state without a mark.** -/
theorem factsK13_reached
    (hP1 : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) (j : ℕ)
    (a : ProofFile.InstPub × S) (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) j a) (hu : a.2.failed = none) :
    FactsK13 (d13 hA.𝔇) d12Full (mgAll hA.𝔇 mgBase) a := by
  obtain ⟨Bs, base, O⟩ := hA.laid.opened
  have hB := IM.sends_pinned_paid O (madeRow_atAll hA hP1)
    (IM.hp_of_planOk hA.scope hA.reads O (IM.blocksOk_of_planOk O hA.laid.planOk))
  have N := nine_reached hA.scope hA.reads hA.laid.value hA.laid.planOk O hB
    (laid_in_scope hA.scope hA.laid.pub hP1) j a hr hu
  rw [msgs_in_scope hA.scope hA.laid.pub hP1] at N
  exact ⟨N.order, N.masks, N.within, N.oneRow, N.weights, N.book, N.seats, N.shapes, N.fits,
    fun q hq => (fillsK13C_base hA.𝔇).quiet q (quietC_of_cA13 q hq) a⟩

/-- **The open segment's own copy, at a place of segment l.** -/
theorem live_reached (j : ℕ) (a : ProofFile.InstPub × S)
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) j a) (hu : a.2.failed = none) {p : Place} {l : ℕ}
    (hp : (flatPlacesOf linksFull true)[j]? = some p) (hl : p.link = some l) :
    ∀ L, a.2.link? = some L →
      L.check.frame.group = hA.𝔇.N.groupAt l ∧ L.check.frame.shape = (d13 hA.𝔇).shape := by
  obtain ⟨Bs, base, O⟩ := hA.laid.opened
  have hpl : ∀ b ∈ cF.blocksInOrder, b.planOk = true := _root_.Meaning.K2.flat_planOk O.desc hA.laid.planOk
  have hFold : ∀ k a, Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k a → ∃ rs cols r q,
      VerifiableInference.Desc.foldBlocks 0 (cF.blocksInOrder.take k) (ProofFile.startS Zp (id a).1) rs cols =
        .ok ((id a).2, r, q) := fun _ _ q => by
    obtain ⟨-, rs, cols, f⟩ := q.fold
    exact ⟨rs, cols, [], [], f⟩
  have hp' : IM.placesW[j]? = some p := by
    unfold IM.placesW
    rw [LPFK9.linksW_full]
    exact hp
  intro L hL
  refine ⟨(_root_.Meaning.K2.groupIs_field hA.scope hA.reads O _ id hFold j a p l L hr hu hp' hl
    hL).2, ?_⟩
  have h0 := _root_.Meaning.K2.liveShape_field hA.scope hA.reads O hpl _ id (fun _ _ q => q) j a hr
    hu
  unfold First.S.live at h0
  rw [show (id a).2.link? = some L from hL] at h0
  exact h0

end

/-- **A form of hFacts of k01_fifty_atThree at the constant**: without the table's
promise at the border. -/
theorem factsK1_atAll {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain S Cl} {x₀ : First.Look.Place}
    (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
    (hP1 : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) (xb : S → Bool)
    (hLT : ∀ l, l < 25 → ∀ d : Bool, ∀ j,
      (j = 14 * l + k1Ix l d + 2 ∨ j = 14 * l + k1Ix l d + 2 + 1) →
      ∃ p, (flatPlacesOf linksFull true)[j]? = some p ∧ p.link = some l)
    (hX : ∀ l, l < 25 → ∀ d : Bool, ∀ j,
      (j = 14 * l + k1Ix l d + 2 ∨ j = 14 * l + k1Ix l d + 2 + 1) →
      ∀ a, RchPub (Str := (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))
          (D.at frS.P.T.a).key₁ 0).E.Str)
        (P5J.F0T OnBytes.secondHashFunction Zp Np cF) typedPub j a → a.1.2.failed = none → xb a.1.2 = true) :
    ∀ l, l < 25 → ∀ d : Bool, ∀ j,
      (j = 14 * l + k1Ix l d + 2 ∨ j = 14 * l + k1Ix l d + 2 + 1) →
      ∀ a, RchPub (Str := (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))
          (D.at frS.P.T.a).key₁ 0).E.Str)
        (P5J.F0T OnBytes.secondHashFunction Zp Np cF) typedPub j a → a.1.2.failed = none →
      FactsK13 (d13 hA.𝔇) d12Full (mgAll hA.𝔇 mgBase) a.1 ∧
        (∀ L, a.1.2.link? = some L → L.check.frame.group = hA.𝔇.N.groupAt l ∧
          L.check.frame.shape = (d13 hA.𝔇).shape) ∧
        xb a.1.2 = true := by
  intro l hl d j hj a hr hu
  obtain ⟨p, hp, hpl⟩ := hLT l hl d j hj
  exact ⟨factsK13_reached hA hP1 j a.1 (rchAt_raw hr.1) hu,
    live_reached hA j a.1 (rchAt_raw hr.1) hu hp hpl, hX l hl d j hj a hr hu⟩

/-- **The same behind the table's promise**: hFacts in the form where the promise at the
border stands as one antecedent more, in the clause on xb too. -/
theorem factsK1_atAllQ {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain S Cl} {x₀ : First.Look.Place}
    (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
    (hP1 : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) (xb : S → Bool)
    (hLT : ∀ l, l < 25 → ∀ d : Bool, ∀ j,
      (j = 14 * l + k1Ix l d + 2 ∨ j = 14 * l + k1Ix l d + 2 + 1) →
      ∃ p, (flatPlacesOf linksFull true)[j]? = some p ∧ p.link = some l)
    (hX : ∀ l, l < 25 → ∀ d : Bool, ∀ j,
      (j = 14 * l + k1Ix l d + 2 ∨ j = 14 * l + k1Ix l d + 2 + 1) →
      ∀ a, RchPub (Str := (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))
          (D.at frS.P.T.a).key₁ 0).E.Str)
        (P5J.F0T OnBytes.secondHashFunction Zp Np cF) typedPub j a →
      onQ hA.𝔇.N (mgAll hA.𝔇 mgBase) linksFull (flatPlacesOf linksFull true) (fun a => a) j a →
      a.1.2.failed = none → xb a.1.2 = true) :
    ∀ l, l < 25 → ∀ d : Bool, ∀ j,
      (j = 14 * l + k1Ix l d + 2 ∨ j = 14 * l + k1Ix l d + 2 + 1) →
      ∀ a, RchPub (Str := (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))
          (D.at frS.P.T.a).key₁ 0).E.Str)
        (P5J.F0T OnBytes.secondHashFunction Zp Np cF) typedPub j a →
      onQ hA.𝔇.N (mgAll hA.𝔇 mgBase) linksFull (flatPlacesOf linksFull true) (fun a => a) j a →
      a.1.2.failed = none →
      FactsK13 (d13 hA.𝔇) d12Full (mgAll hA.𝔇 mgBase) a.1 ∧
        (∀ L, a.1.2.link? = some L → L.check.frame.group = hA.𝔇.N.groupAt l ∧
          L.check.frame.shape = (d13 hA.𝔇).shape) ∧
        xb a.1.2 = true := by
  intro l hl d j hj a hr hq hu
  obtain ⟨p, hp, hpl⟩ := hLT l hl d j hj
  exact ⟨factsK13_reached hA hP1 j a.1 (rchAt_raw hr.1) hu,
    live_reached hA j a.1 (rchAt_raw hr.1) hu hp hpl, hX l hl d j hj a hr hq hu⟩

end VerifiableInference.Desc.K13.Law

#print axioms VerifiableInference.Desc.K13.Law.factsK13_reached
#print axioms VerifiableInference.Desc.K13.Law.live_reached
#print axioms VerifiableInference.Desc.K13.Law.factsK1_atAll
#print axioms VerifiableInference.Desc.K13.Law.factsK1_atAllQ
