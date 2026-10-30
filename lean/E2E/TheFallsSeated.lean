-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/TheFallsSeated.lean: THE RECORDS OF THE FIRST CHAIN'S LIST STAND AT MEMBERS OF THE CHAIN. A fall
at a place where no member stands is never asked, and nothing fails. So two things are stated.

  fallsHead_places       a property of the three written places of a segment's falls and of K4's
                         place holds of every record of the list
  fall_places_written, fall_places_control   the written places are in the chain's written list
  k4Fall_at_member       at each member of K4's kind, the fall at that member's own public data is
                         in the list
  onlineSides_k4Fall     the same at G
  theMarks_164           no mark is dropped
  onlineSides_length     G's first list has its 87 records
  onlineSides_fallsSeated   every fall of G stands at a member of its chain

Limits. Both statements are at the slots with nothing in them, or hold of the first list's full-size
part alone. That a fall is seated says nothing on whether its test is the member's. This file proves
nothing about completeness, soundness or zero knowledge.
-/
import E2E.TheFalls
import Johnson.Desc.ProofFile.Honest.K4.Law.SeatedHead
import Johnson.Desc.ProofFile.Honest.K4.Law.TableFitsMember
import Johnson.P1K8R.Part1Marks
import Johnson.Desc.ProofFile.Honest.K3.Good.MarksHead
import Johnson.Desc.ProofFile.Honest.K5.Law.MarksListLaw

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace AtPublicFiles.TheFalls
open ProofFile.Honest
open VerifiableInference.Desc (Block Chain KindName Place)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- The written places of the falls are places of the chain's written list. -/
theorem fall_places_written : ((List.range 25).all fun l =>
      P5J.At.ps.contains ⟨1, some l, 8 + 2 * oAt l, KindName.K9⟩ &&
        P5J.At.ps.contains ⟨1, some l, 9 + 2 * oAt l, KindName.frame⟩) = true ∧
    ((List.range 12).all fun g =>
      P5J.At.ps.contains ⟨1, some (2 * g), 3, KindName.K4⟩) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
/-- A control: one link on, K4's place is no place of the list. -/
theorem fall_places_control : ((List.range 12).all fun g =>
      P5J.At.ps.contains ⟨1, some (2 * g + 1), 3, KindName.K4⟩) = false := by
  decide +kernel

variable {Zp : ProofFile.Pub} {G₀ : ProofFile.Ground} {cols tau : Nat → Nat} {share notGood : Nat → Odds}
  {r0 : Nat → Nat}

/-- **A property of the written places holds of every record of the list.** -/
theorem fallsHead_places {Q : Place → Prop}
    (hq : ∀ l, l < 25 → ∀ p, IM.k9At Zp l = some p →
      p.chain = 1 ∧ p.link = l ∧ p.piece = 8 + 2 * oAt l)
    (q₁ : ∀ l, l < 25 → Q ⟨1, some l, 8 + 2 * oAt l, KindName.K9⟩)
    (q₂ : ∀ l, l < 25 → Q ⟨1, some l, 9 + 2 * oAt l, KindName.frame⟩)
    (q₃ : ∀ g, g < 12 → Q ⟨1, some (2 * g), 3, KindName.K4⟩) :
    ∀ f ∈ fallsHead Zp G₀ cols tau share notGood r0, Q f.place := by
  intro f hf
  unfold fallsHead at hf
  rcases List.mem_append.1 hf with h | h
  · obtain ⟨l, hl, hF⟩ := List.mem_flatMap.1 h
    have hl' : l < 25 := List.mem_range.1 hl
    unfold linkFalls at hF
    rcases List.mem_append.1 hF with hF | hF
    · rcases List.mem_append.1 hF with hF | hF
      · obtain rfl := List.mem_singleton.1 hF
        exact q₁ l hl'
      · cases hp : IM.k9At Zp l with
        | none =>
          rw [hp] at hF
          cases hF
        | some p =>
          cases hu : VerifiableInference.Desc.K9.testsWhere Zp.p.X l 0 with
          | none =>
            rw [hp, hu] at hF
            cases hF
          | some u =>
            rw [hp, hu] at hF
            obtain rfl := List.mem_singleton.1 hF
            obtain ⟨e₁, e₂, e₃⟩ := hq l hl' p hp
            show Q ⟨p.chain, some p.link, p.piece + 1, KindName.frame⟩
            rw [e₁, e₂, e₃, show 8 + 2 * oAt l + 1 = 9 + 2 * oAt l by omega]
            exact q₂ l hl'
    · cases hX : G₀.built[l]? with
      | none =>
        rw [hX] at hF
        cases hF
      | some Xl =>
        rw [hX] at hF
        obtain rfl := List.mem_singleton.1 hF
        exact q₂ l hl'
  · obtain ⟨g, hg, hF⟩ := List.mem_filterMap.1 h
    cases hh : G₀.W.G[g]? with
    | none =>
      rw [hh] at hF
      cases hF
    | some hp =>
      rw [hh] at hF
      obtain rfl := Option.some.inj hF
      exact q₃ g (List.mem_range.1 hg)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- **Every record of the list of the full size stands at a member of the chain.** -/
theorem fallsFull_at_member (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) :
    ∀ f ∈ fallsFull Zp G₀ noneNotGood (roundsBeforeK4 cF),
      cF.blocksInOrder.any (fun b => b.place == f.place) = true := by
  have hps := places_full h
  have mem : ∀ p : Place, P5J.At.ps.contains p = true →
      cF.blocksInOrder.any (fun b => b.place == p) = true := by
    intro p hc
    obtain ⟨b, hb, e⟩ := List.mem_map.1 (hps ▸ List.contains_iff_mem.1 hc)
    exact List.any_eq_true.2 ⟨b, hb, beq_iff_eq.2 e⟩
  refine fallsHead_places (Q := fun p => cF.blocksInOrder.any (fun b => b.place == p) = true) ?_ ?_ ?_ ?_
  · intro l hl p hp
    obtain ⟨p', u, hp', -, q⟩ := k9At_full h hl
    obtain rfl : p' = p := Option.some.inj (hp'.symm.trans hp)
    exact q
  · intro l hl
    have t := List.all_eq_true.1 fall_places_written.1 l (List.mem_range.2 hl)
    rw [Bool.and_eq_true] at t
    exact mem _ t.1
  · intro l hl
    have t := List.all_eq_true.1 fall_places_written.1 l (List.mem_range.2 hl)
    rw [Bool.and_eq_true] at t
    exact mem _ t.2
  · intro g hg
    exact mem _ (List.all_eq_true.1 fall_places_written.2 g (List.mem_range.2 hg))

/-- **At each member of K4's kind, the fall at that member's own public data is in the list.** -/
theorem k4Fall_at_member (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) (s : FallSlots (ProofFileDesc Zp Np cF))
    {k m : ℕ} {pl : Place}
    (A : OnBytes.Road.K4.AtK4 VerifiableInference.Desc.Sound.linksFull OnBytes.Road.K4.More.PS k m pl) :
    ∃ g x blk, K4.SeatedHead.LaidK4 Zp cF k m g x blk ∧
      K4.k4Fall (K4.k4PubAt cF k x) ∈ theFalls₁ Zp Np cF G₀ s := by
  obtain ⟨g, x, blk, Lh⟩ := K4.SeatedHead.laid_head h A
  obtain ⟨Bs, _, O⟩ := h.laid.opened
  obtain rfl : Bs.G₀ = G₀ := Option.some.inj (O.blank.symm.trans hG)
  have hW : Bs.G₀.W = P5J.At.X Zp := O.W
  have hhp : Bs.G₀.W.G[g]? = some x.2.hp := by
    rw [hW]
    exact Lh.hp
  refine ⟨g, x, blk, Lh, ?_⟩
  have e : K4.k4PubAt cF k x =
      ⟨Bs.G₀.W.layers, x.2.hp, g, 2 * g, 3, roundsBeforeK4 cF g, 2 * g⟩ := by
    rw [K4.pubAt_is Lh, hW, Lh.num]
    rfl
  rw [e]
  exact mem_withSlots (fallsHead_k4 Lh.lt hhp)

/-- **No mark is dropped**: 26, 100, 12, 24 and 2. -/
theorem theMarks_164 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    (theMarks Zp Bs.G₀).length = 164 := by
  unfold theMarks
  simp only [List.length_append]
  rw [P1K8.part1Marks_26 h hB, K3.Good.k3Marks_100 h, K4.k4MarksWide_length (fun _ hg =>
    plan_full h hB hg), K5.k5Marks_length h hB, K6.part4Marks_length]

end AtPublicFiles.TheFalls

namespace AtPublicFiles.AtFiles.HonestTerm
open OnBytes (TableKey)
open VerifiableInference.Desc (Chain Place)
open ProofFile.Honest.Term (OnlineReturn onlineMaker)
open VerifierAndGoals (PublicFiles)
open P5J
open AtPublicFiles.TheSides AtPublicFiles.TheFalls

variable {Z : PublicFiles} (returned : OnlineReturn Z) (places : H2U.Places4)
  (firstChain : Chain TS ProofFile.Cl) (s : FallSlots (ProofFileDesc returned.Z places firstChain))
  (A : Letters (descZ returned.Z places firstChain) returned.B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey
    ProofFile.Honest.Cells Unit Unit) (R : OnlineRows (Z := Z))

/-- **G holds K4's fall at each member of K4's kind.** -/
theorem onlineSides_k4Fall (hM : onlineMaker Z = .ok returned) {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} {xh : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r returned.Z places firstChain xh) {k m : ℕ} {pl : Place}
    (a : OnBytes.Road.K4.AtK4 VerifiableInference.Desc.Sound.linksFull OnBytes.Road.K4.More.PS k m pl) :
    ∃ g x blk, ProofFile.Honest.K4.SeatedHead.LaidK4 returned.Z firstChain k m g x blk ∧
      ProofFile.Honest.K4.k4Fall (ProofFile.Honest.K4.k4PubAt firstChain k x) ∈
        (onlineSides returned places firstChain s A R).falls₁ :=
  k4Fall_at_member h (ProofFile.Honest.atPure_ok hM).2.1 s a

/-- **G's first list has its 87 records**, at the slots with nothing in them. -/
theorem onlineSides_length (hM : onlineMaker Z = .ok returned) {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} {xh : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r returned.Z places firstChain xh) :
    (onlineSides returned places firstChain (FallSlots.nothing _) A R).falls₁.length = 87 := by
  obtain ⟨Bs, _, O⟩ := h.laid.opened
  have e := ground_of_head returned places firstChain hM h O.made
  show (theFalls₁ returned.Z places firstChain returned.G (FallSlots.nothing _)).length = 87
  rw [← e]
  exact theFalls₁_length returned.Z places firstChain h O.made

/-- **Every fall of G stands at a member of its chain**, at the slots with nothing in them. -/
theorem onlineSides_fallsSeated {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {xh : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r returned.Z places firstChain xh) :
    (onlineSides returned places firstChain (FallSlots.nothing _) A R).fallsSeated = true := by
  obtain ⟨e₁, e₂, e₃⟩ := theFalls_nothing returned.Z places firstChain returned.G
  unfold ProofFile.Honest.Sides.fallsSeated
  simp only [Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show (theFalls₁ returned.Z places firstChain returned.G (FallSlots.nothing _)).all _ = true
    rw [e₁]
    exact List.all_eq_true.2 fun f hf => fallsFull_at_member h f hf
  · show (theFalls₂ returned.Z places firstChain (FallSlots.nothing _)).all _ = true
    rw [e₂]
    rfl
  · show (theFalls₃ returned.Z places firstChain (FallSlots.nothing _)).all _ = true
    rw [e₃]
    rfl

end AtPublicFiles.AtFiles.HonestTerm

#print axioms AtPublicFiles.TheFalls.fall_places_written
#print axioms AtPublicFiles.TheFalls.fall_places_control
#print axioms AtPublicFiles.TheFalls.fallsHead_places
#print axioms AtPublicFiles.TheFalls.fallsFull_at_member
#print axioms AtPublicFiles.TheFalls.k4Fall_at_member
#print axioms AtPublicFiles.AtFiles.HonestTerm.onlineSides_k4Fall
#print axioms AtPublicFiles.AtFiles.HonestTerm.onlineSides_length
#print axioms AtPublicFiles.AtFiles.HonestTerm.onlineSides_fallsSeated
#print axioms AtPublicFiles.TheFalls.theMarks_164
