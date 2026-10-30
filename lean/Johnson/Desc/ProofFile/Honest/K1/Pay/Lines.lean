-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K1/Pay/Lines.lean: THE KINDS' LINES OF KindsWhole (SidesWhole.lean) AT
THE BASE PROVER, EACH FROM THE KIND's OWN LAW ON ITS LOT AND A TEST ON THE WRITTEN PLAN.

Limits. Under the head and a return of the maker. A side at a place, nothing on what it sends.
Nothing on any property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K1.Pay.Pays
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.CoverageAtHead
import Johnson.Desc.ProofFile.Honest.K3.Law.CoverageLotsNamed
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten
import Johnson.Desc.ProofFile.Honest.K5.Law.LotFind
import Johnson.Desc.ProofFile.Honest.K5.Law.Member
import Johnson.Desc.ProofFile.Honest.K13.LotKind
import Johnson.Desc.ProofFile.Honest.K11.Plays.LotKind
import Johnson.Desc.ProofFile.Honest.Thread.FirstFillThree
import Johnson.Desc.ProofFile.Honest.Thread.FirstFillK2
import Johnson.Desc.ProofFile.Honest.Thread.HeadFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1.Pay
open VerifiableInference.Desc
open VerifiableInference.Desc (Block FileDescription Place KindName Chain)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS F0T)
open ProofFile.Honest.FirstFill
open P2Law.ProofPlan (WP)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **Every sub-protocol of the kind κ stands at a place of the list.** -/
def kindAt (κ : KindName) (ps : List Place) (l : List PlanB) : Bool :=
  l.all fun y => y.place.kind != κ || ps.contains y.place

theorem kind_place {κ : KindName} {ps : List Place} {l : List PlanB} (ht : kindAt κ ps l = true)
    {y : PlanB} (hy : y ∈ l) (hk : y.place.kind = κ) : y.place ∈ ps := by
  have h := List.all_eq_true.1 ht y hy
  rw [hk] at h
  simpa using h

set_option maxRecDepth 1000000 in
theorem written_kinds :
    kindAt .K7 [⟨1, some 24, 1, .K7⟩] (planOf WP.first.blocksInOrder) = true ∧
    kindAt .K11 [⟨1, some 24, 9, .K11⟩] (planOf WP.first.blocksInOrder) = true ∧
    kindAt .K13 [⟨1, none, 3, .K13⟩] (planOf WP.first.blocksInOrder) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem written_k2 :
    kindAt .K2 (K2.Law.placesW.map (·.place)) (planOf WP.first.blocksInOrder) = true := by decide +kernel

section
variable {W₀ : Type} (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- The plan of the first chain under the head. -/
theorem plan_first (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A) :
    planOf A.F.first.blocksInOrder = planOf WP.first.blocksInOrder := by
  rw [(atPure_at_laid h.laid hA).2]
  exact (planOf_alike (K14.planAlike_at_head h).first).symm

/-- A side of one of the ten lots is a side of the prover. -/
theorem side_in_first (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A)
    {M : HLot (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit}
    (hM : M ∈ (widerFillAt I OnBytes.secondHashFunction S O).lots)
    {g : Placed (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit}
    (hg : g ∈ M.halves A.Z A.G) : g ∈ A.H.first := by
  obtain ⟨-, -, -, -, -, -, -, eH, -⟩ := atPure_ok hA
  rw [eH]
  refine List.mem_flatMap.2 ⟨M, ?_, hg⟩
  rw [widerFillAtCPUOWM_lots]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hM))

theorem any_of_side {a : Place}
    {g : Placed (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit}
    (hm : g ∈ A.H.first) (e : g.place = a) : (A.H.first.any fun h => h.place == a) = true :=
  List.any_eq_true.2 ⟨g, hm, by simp [e]⟩

/-- **K7's line.** -/
theorem line_k7 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A) :
    SidesWhere A.F.first.blocksInOrder A.H.first .K7 := by
  intro b hb hk _
  have hm : b.place ∈ [(⟨1, some 24, 1, .K7⟩ : Place)] :=
    kind_place written_kinds.1 ((plan_first I S O h hA) ▸ mem_planOf hb) hk
  obtain ⟨Bs, base, O'⟩ := h.laid.opened
  obtain ⟨eZ, eG, -⟩ := atPure_at_laid_ground h.laid O'.blank hA
  have hs : A.G.built.size = 25 := by rw [eG]; exact built_25 h O'.blank
  rw [List.mem_singleton.1 hm]
  refine any_of_side (side_in_first I S O hA (M := replyLot) ?_ (List.Mem.head _)) ?_
  · show replyLot ∈ [_, _, _, _, _, _, _, _, _, _]
    exact .tail _ (.tail _ (.head _))
  · simp [replyHalf, hs]

/-- **K11's line.** -/
theorem line_k11 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A) :
    SidesWhere A.F.first.blocksInOrder A.H.first .K11 := by
  intro b hb hk _
  have hm : b.place ∈ [(⟨1, some 24, 9, .K11⟩ : Place)] :=
    kind_place written_kinds.2.1 ((plan_first I S O h hA) ▸ mem_planOf hb) hk
  obtain ⟨Bs, base, O'⟩ := h.laid.opened
  obtain ⟨eZ, eG, -⟩ := atPure_at_laid_ground h.laid O'.blank hA
  rw [List.mem_singleton.1 hm]
  have e := K11.headMergeLot_find Z D r Zp Np cF x h W₀ IndexCommitterCoins Cells Unit Bs O.claims (I.weights Zp)
    O'.made
  have mem := List.mem_of_find?_eq_some e
  have pb := List.find?_some e
  refine any_of_side (side_in_first I S O hA
    (M := HLot.byPub I.weights (LongLots.plain OnBytes.secondHashFunction S O).k11) ?_
    (by rw [eZ, eG]; exact mem)) (eq_of_beq pb)
  show _ ∈ [_, _, _, _, _, _, _, _, _, _]
  exact .tail _ (.tail _ (.tail _ (.head _)))

/-- **K13's line.** -/
theorem line_k13 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A) :
    SidesWhere A.F.first.blocksInOrder A.H.first .K13 := by
  intro b hb hk _
  have hm : b.place ∈ [(⟨1, none, 3, .K13⟩ : Place)] :=
    kind_place written_kinds.2.2 ((plan_first I S O h hA) ▸ mem_planOf hb) hk
  rw [List.mem_singleton.1 hm]
  refine any_of_side (side_in_first I S O hA
    (M := HLot.byPub I.weights (LongLots.plain OnBytes.secondHashFunction S O).k13) ?_
    (g := K13.proverSideOfClaimCombination (I.weights A.Z) (O.pile A.Z A.G) (K13.whereOf A.Z)) (List.Mem.head _)) rfl
  show _ ∈ [_, _, _, _, _, _, _, _, _, _]
  exact .tail _ (.tail _ (.tail _ (.tail _ (.head _))))

/-- **K2's line.** -/
theorem line_k2 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A) :
    SidesWhere A.F.first.blocksInOrder A.H.first .K2 := by
  intro b hb hk _
  have hm : b.place ∈ K2.Law.placesW.map (·.place) :=
    kind_place written_k2 ((plan_first I S O h hA) ▸ mem_planOf hb) hk
  obtain ⟨Bs, base, O'⟩ := h.laid.opened
  obtain ⟨eZ, eG, -⟩ := atPure_at_laid_ground h.laid O'.blank hA
  obtain ⟨p, hp, e⟩ := List.mem_map.1 hm
  have hp' : p ∈ K2.switchPlaces A.Z A.G := by
    rw [eZ, eG, K2.Law.places_at_head h.toAtMg O']
    exact hp
  rw [← e]
  refine any_of_side (side_in_first I S O hA
    (M := HLot.byPub I.weights fun wt => HLot.byRows (widerRows S) fun D =>
      K2.switchLot D fun w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells => ⟨w.trace, wt w.w₀, w.rc⟩) ?_
    (g := k2SideAt (widerRows S A.Z A.G)
      (fun w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells => ⟨w.trace, I.weights A.Z w.w₀, w.rc⟩) A.Z A.G p)
    (List.mem_map.2 ⟨p, hp', rfl⟩)) rfl
  show _ ∈ [_, _, _, _, _, _, _, _, _, _]
  exact .tail _ (.head _)

/-- **K3's line.** -/
theorem line_k3 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A) :
    SidesWhere A.F.first.blocksInOrder A.H.first .K3 := by
  intro b hb hk _
  obtain ⟨G', B', H', rd', rw', rfl⟩ := atPure_is h.laid hA
  have hb' : b ∈ cF.blocksInOrder := hb
  obtain ⟨c, -, -⟩ := K3.Law.AtThr.every_look_has_half_of h
    (HLot.byPub I.weights (LongLots.plain OnBytes.secondHashFunction S O).k3) _ G'
    (K3.Law.rowLotAt_halves _ _ _)
  obtain ⟨hf, hm, e⟩ := c b hb' hk
  refine any_of_side (side_in_first I S O hA
    (M := HLot.byPub I.weights (LongLots.plain OnBytes.secondHashFunction S O).k3) ?_
    hm) e
  show _ ∈ [_, _, _, _, _, _, _, _, _, _]
  exact .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))

end

end ProofFile.Honest.K1.Pay

#print axioms ProofFile.Honest.K1.Pay.written_kinds
#print axioms ProofFile.Honest.K1.Pay.written_k2
#print axioms ProofFile.Honest.K1.Pay.line_k7
#print axioms ProofFile.Honest.K1.Pay.line_k2
