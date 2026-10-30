-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/AttentionLawAtTheTerm.lean: the structure AttentionLaw of E2E/AttentionSimulatorAtTheTerm.lean at
a return of the online maker, under the library's head, and the two sentences on the lot.

  attention_lot_own, attention_lot_in   the lot is the filling's own, read through
  lays_at_base, lays_online             each of the two fillings lays the lot alone
  attention_law                         CONDITIONAL: h; hA: the structure

What the structure says and does not say is in the head of that file. The proof is that of
attention_law_at (Honest/K5/Law/AttentionAtAFilling.lean), which is stated at any filling.
That the premises of attention_law_at_base meet
together is not shown in this file.
No property is claimed. Nothing is claimed on soundness, completeness or hiding.
-/
import E2E.AttentionSimulatorAtTheTerm
import Johnson.Desc.ProofFile.Honest.K5.Law.AttentionAtAFilling
import Johnson.Desc.ProofFile.Honest.Law.FillPairs
import E2E.BaseMaker
import Johnson.Desc.ProofFile.Honest.K5.Law.KindPaysAtTerm

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles.HonestTerm.Attention
open AtPublicFiles.Cut
open ProofFile.Honest ProofFile.Honest.K5
open ProofFile.Honest.Term (OnlineReturn onlineMaker onlineFilling tableCoins matrixInput)
open VerifiableInference.Desc (Chain Place KindName)
open P5J (AtMgA TS)

/-- The filling's own lot of this kind, before it is read through. -/
abbrev baseLot : HLot (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit :=
  k5LotK (W₀ := FullSizeMatrix) (Rc := IndexCommitterCoins) (Xi := ProofFile.Inst) (X := Unit) id openHonest.keyOf

/-- The filling that the online filling reads through. -/
abbrev basePairs := fillPairs matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest

/-- **The lot is the filling's own, read through.** -/
theorem attention_lot_own (files : VerifierAndGoals.PublicFiles) : AttentionLotIsTheFillingsOwn files := by
  unfold AttentionLotIsTheFillingsOwn
  rw [k5SLot_toHLot]
  exact (k5LotK_thru id (tableCoins files) id keyOfK3).symm

theorem basePairs_filter : basePairs.filter (fun r => r.2 == KindName.K5) = [(baseLot, .K5)] := rfl

theorem baseLot_mem : (baseLot, KindName.K5) ∈ basePairs := by
  have h := List.mem_of_mem_filter (p := fun r : _ × KindName => r.2 == KindName.K5)
    (l := basePairs) (a := (baseLot, KindName.K5))
  exact h (by rw [basePairs_filter]; exact List.mem_singleton.2 rfl)

/-- **The lot is a lot of the filling.** -/
theorem attention_lot_in (files : VerifierAndGoals.PublicFiles) : AttentionLotIsInTheFilling files := by
  unfold AttentionLotIsInTheFilling
  rw [attention_lot_own files]
  refine List.mem_map_of_mem ?_
  show baseLot ∈ (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref
    openHonest).lots
  rw [fillPairs_lots]
  exact List.mem_map.2 ⟨_, baseLot_mem, rfl⟩

/-- Of a list of lots by kind, each with sides of its kind alone, the sides of one kind are those of the
lots of that kind. f: a map of lots that keeps the places of the sides. -/
theorem filter_kind_flatMap {V W V' W' X : Type} (f : HLot V W X → HLot V' W' X) (Z : ProofFile.Pub)
    (G : ProofFile.Ground)
    (hf : ∀ L, ∀ q ∈ (f L).halves Z G, ∃ x ∈ L.halves Z G, q.place = x.place)
    (ps : List (HLot V W X × KindName)) (hk : ∀ r ∈ ps, ∀ x ∈ r.1.halves Z G, x.place.kind = r.2) :
    (((ps.map (·.1)).map f).flatMap fun L => L.halves Z G).filter
        (fun h => decide (h.place.kind = KindName.K5)) =
      (((ps.filter fun r => r.2 == KindName.K5).map (·.1)).map f).flatMap
        fun L => L.halves Z G := by
  induction ps with
  | nil => rfl
  | cons r ps ih =>
    have ih' := ih fun q hq => hk q (List.mem_cons_of_mem _ hq)
    have hr := hk r (List.mem_cons_self ..)
    by_cases e : r.2 = KindName.K5
    · have hb : (r.2 == KindName.K5) = true := beq_iff_eq.2 e
      have f1 : (r :: ps).filter (fun r => r.2 == KindName.K5) =
          r :: ps.filter fun r => r.2 == KindName.K5 := List.filter_cons_of_pos hb
      rw [f1]
      simp only [List.map_cons, List.flatMap_cons, List.filter_append]
      rw [ih']
      congr 1
      apply List.filter_eq_self.2
      intro q hq
      obtain ⟨x, hx, ex⟩ := hf r.1 q hq
      exact decide_eq_true (by rw [ex, hr x hx, e])
    · have hb : ¬ (r.2 == KindName.K5) = true := fun h => e (beq_iff_eq.1 h)
      have f1 : (r :: ps).filter (fun r => r.2 == KindName.K5) =
          ps.filter fun r => r.2 == KindName.K5 := List.filter_cons_of_neg hb
      rw [f1]
      simp only [List.map_cons, List.flatMap_cons, List.filter_append]
      rw [ih']
      have hz : ((f r.1).halves Z G).filter
          (fun h => decide (h.place.kind = KindName.K5)) = [] := by
        apply List.filter_eq_nil_iff.2
        intro q hq
        obtain ⟨x, hx, ex⟩ := hf r.1 q hq
        rw [ex, hr x hx]
        simpa using e
      rw [hz, List.nil_append]

/-- **The base filling lays the lot alone.** -/
theorem lays_at_base : LaysTheLotAlone
    (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest) := by
  intro Z G
  have e1 := filter_kind_flatMap id Z G (fun _ q hq => ⟨q, hq, rfl⟩) basePairs
    (fillPairs_kinds matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest Z G)
  rw [basePairs_filter] at e1
  simpa [fillPairs_lots] using e1

/-- **The online filling lays the lot alone.** -/
theorem lays_online (files : VerifierAndGoals.PublicFiles) : LaysTheLotAlone (onlineFilling files) := by
  intro Z G
  have e1 := filter_kind_flatMap (HLot.thru (Local.thru id (tableCoins files))
      (Local.thru id (tableCoins files))) Z G
    (fun L q hq => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hq
      exact ⟨x, hx, rfl⟩) basePairs
    (fillPairs_kinds matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest Z G)
  rw [basePairs_filter] at e1
  refine e1.trans ?_
  have e2 := congrArg (fun L => L.halves Z G) (k5LotK_thru (W₀ := FullSizeMatrix) (W₀' := FullSizeMatrix) (Rc := IndexCommitterCoins)
    (Rc' := (protocolAtFiles files).EncodingRandomness) (Xi := ProofFile.Inst) (X := Unit) id (tableCoins files) id keyOfK3)
  simpa using e2

variable {files : VerifierAndGoals.PublicFiles} {returned : OnlineReturn files}

/-- **The law of the rows at the online prover's return.** CONDITIONAL: h: the library's head at the
return's public part; hA: the maker returns. -/
theorem attention_law {places : H2U.Places4} {firstChain : Chain TS ProofFile.Cl}
    {description : OnBytes.Maker.WholeD} {run : LPFD.Full.RunPF}
    {x : VerifiableInference.Desc.First.Look.Place} (hA : onlineMaker files = .ok returned)
    (h : AtMgA OnBytes.secondHashFunction files description run returned.Z places firstChain x) :
    AttentionLaw returned := by
  have l := attention_law_at h hA (lays_online files)
  refine ⟨⟨fun r hr => ?_, fun q hq hk => ?_⟩, l.count, l.twelve, l.places, l.kindPlaces, l.on,
    l.rows⟩
  · have hm : r.half ∈ (returned.H.first.filter fun h => decide (h.place.kind = .K5)) := by
      rw [l.count]
      exact List.mem_map_of_mem hr
    exact (List.mem_filter.1 hm).1
  · have hm : q ∈ (returned.H.first.filter fun h => decide (h.place.kind = .K5)) :=
      List.mem_filter.2 ⟨hq, decide_eq_true hk⟩
    rw [l.count] at hm
    obtain ⟨r, hr, e⟩ := List.mem_map.1 hm
    exact ⟨r, hr, e.symm⟩

/-- **The same law at the base filling, which the online filling reads through.** CONDITIONAL: h; hA. -/
theorem attention_law_at_base {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} {places : H2U.Places4}
    {firstChain : Chain TS ProofFile.Cl} {description : OnBytes.Maker.WholeD} {run : LPFD.Full.RunPF}
    {x : VerifiableInference.Desc.First.Look.Place}
    (hA : ProofFile.Honest.Term.baseMaker files = .ok A)
    (h : AtMgA OnBytes.secondHashFunction files description run A.Z places firstChain x) : AttentionLawAt A :=
  attention_law_at h hA lays_at_base

end AtPublicFiles.AtFiles.HonestTerm.Attention

#print axioms AtPublicFiles.AtFiles.HonestTerm.Attention.attention_lot_own
#print axioms AtPublicFiles.AtFiles.HonestTerm.Attention.attention_lot_in
#print axioms AtPublicFiles.AtFiles.HonestTerm.Attention.lays_at_base
#print axioms AtPublicFiles.AtFiles.HonestTerm.Attention.lays_online
#print axioms AtPublicFiles.AtFiles.HonestTerm.Attention.attention_law
#print axioms AtPublicFiles.AtFiles.HonestTerm.Attention.attention_law_at_base
