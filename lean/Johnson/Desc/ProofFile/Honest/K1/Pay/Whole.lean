-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K1/Pay/Whole.lean: THE REST OF THE KINDS' LINES, AND SidesAreWhole AT
THE BASE PROVER: halvedAll, rootedAll and sealPlain, under the head and a return of the maker, at the
filling onlineProverPartsInUse at any reader of the index, where the keys of K5 are keyOfK3.

At the shared chain's place 4, the tests on G_u and G_omega, the last chain's test and the first
chain's test a side stands at the place: that is all that is said of them here.

Limits. A side at a place; nothing on what it sends. Nothing on any property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K1.Pay.Lines
import Johnson.Desc.ProofFile.Honest.K4.Law.HalfHead
import Johnson.Desc.ProofFile.Honest.K6.Law.RowsSeatedAtHead
import Johnson.Desc.ProofFile.Honest.K10.SimLot
import Johnson.Desc.ProofFile.Honest.K10.Thr.HalfOfLot
import AtFullSide.K12.FitsAtHeadL
import AtFullSide.K12.SecondMadeW
import AtFullSide.K12.ReturnsAtFillW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1.Pay
open VerifiableInference.Desc
open VerifiableInference.Desc (Block FileDescription Place KindName Chain)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS F0T)
open ProofFile.Honest.FirstFill
open P2Law.ProofPlan (WP)
open VerifiableInference.Desc.K1 (qAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The closing's place at link number l is at this number of the first chain. -/
def closeIx (l : Nat) : Nat := 14 * l + (if l = 24 then 9 else 7) + 5

/-- **Every sub-protocol of the kind K10 stands where a link's closing stands.** -/
def k10Test (l : List PlanB) : Bool :=
  l.all fun y => y.place.kind != .K10 ||
    (List.range 25).any fun j => (l[closeIx j]?.map (·.place)) == some y.place

/-- Of a chain's kind K14 only "SPLIT" is not quiet. -/
def k14Test (l : List PlanB) : Bool :=
  l.all fun y => y.place.kind != .K14 || y.rounds.all quietRound || y.place == K14.place 8

set_option maxRecDepth 1000000 in
theorem written_rest :
    kindAt .K4 ((List.range 12).map IM.k4Place) (planOf WP.first.blocksInOrder) = true ∧
    kindAt .K5 ((List.range 12).map K5.placeOf) (planOf WP.first.blocksInOrder) = true ∧
    kindAt .K6 [IM.k6Place] (planOf WP.first.blocksInOrder) = true ∧
    kindAt .K12 [K12.AtProof.placeL] (planOf WP.first.blocksInOrder) = true ∧
    k10Test (planOf WP.first.blocksInOrder) = true ∧
    k14Test (planOf WP.shared.blocksInOrder) = true ∧
    kindAt .K12 [K12.AtProof.placeU, K12.AtProof.placeO] (planOf WP.shared.blocksInOrder) = true ∧
    kindAt .K12 [K12.AtProof.placeW] (planOf WP.second.blocksInOrder) = true := by decide +kernel

/-- Under the head K4 is laid at each group. -/
theorem laid_g (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {g : Nat} (hg : g < 12) :
    ∃ y blk, K4.SeatedHead.LaidK4 Zp cF (28 * g + 4) (2 * g) g y blk := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, b, y, e1, e2, hx, hla, el, eg, eP, ehp, _, _⟩ := IM.k4_of h.scope h.reads O g hg
  obtain ⟨_, _, epc, enm⟩ := IM.k4_seated_scope h.scope h.reads O.pub O.blank hx
  have hi : IM.flatIx cF (2 * g) 2 = 28 * g + 4 := by
    rw [IM.flatIx_scope h.scope h.reads O (by omega) 2]
    omega
  have hf : cF.blocksInOrder[28 * g + 4]? = some b := by
    rw [← hi]
    exact IM.hear_at_flat e1 e2
  rw [eg] at enm
  rw [O.W] at eP ehp
  exact ⟨y, b, hg, rfl, rfl, hf, hla, ⟨Bs.G₀, O.blank, hx⟩, el, eg, epc, enm, eP, ehp⟩

/-- The eight blocks of the shared chain's plan are made under the head. -/
theorem eight_head (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) :
    ∃ b1 b2 b3 b4 b5 b6 b7 b8, Desc.K14.blocks (qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8] := by
  obtain ⟨_, _, hw⟩ := K12.Light.facts_at_head h
  unfold Desc.K14.blocks
  rw [hw]
  exact ⟨_, _, _, _, _, _, _, _, rfl⟩

section
variable {W₀ : Type} (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

theorem side_of_lot (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A)
    {M : HLot (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit}
    (hM : M ∈ (onlineProverPartsInUse I OnBytes.secondHashFunction S O).lots)
    {g : Placed (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit}
    (hg : g ∈ M.halves A.Z A.G) : g ∈ A.H.first := by
  obtain ⟨-, -, -, -, -, -, -, eH, -⟩ := atPure_ok hA
  rw [eH]
  exact List.mem_flatMap.2 ⟨M, hM, hg⟩

/-- **K4's line.** -/
theorem line_k4 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A) :
    SidesWhere A.F.first.blocksInOrder A.H.first .K4 := by
  intro b hb hk _
  have hm := kind_place written_rest.1 ((plan_first I S O h hA) ▸ mem_planOf hb) hk
  obtain ⟨g, hg, e⟩ := List.mem_map.1 hm
  obtain ⟨y, blk, Lh⟩ := laid_g h (List.mem_range.1 hg)
  obtain ⟨G₀, hG, ef⟩ := K4.lot_half_ground (Rc := IndexCommitterCoins) (X' := Unit) h Lh id (I.weights Zp)
    (fun _ _ => K4.k4LookAt)
  obtain ⟨eZ, eG, -⟩ := atPure_at_laid_ground h.laid hG hA
  have mem := List.mem_of_find?_eq_some ef
  have pb := List.find?_some ef
  have hb₂ : (b.place : Place) = IM.k4Place g := e.symm
  rw [show b.place = IM.k4Place g from hb₂]
  refine any_of_side (side_in_first I S O hA
    (M := HLot.byPub I.weights fun wt => K4.k4HLot id wt fun _ _ => K4.k4LookAt) ?_
    (by rw [eZ, eG]; exact mem)) (eq_of_beq pb)
  show _ ∈ [_, _, _, _, _, _, _, _, _, _]
  exact .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))

/-- **K5's line**, where the keys are keyOfK3. -/
theorem line_k5 (hK : O.keyOf = K5.keyOfK3) (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A) :
    SidesWhere A.F.first.blocksInOrder A.H.first .K5 := by
  intro b hb hk _
  have hm := kind_place written_rest.2.1 ((plan_first I S O h hA) ▸ mem_planOf hb) hk
  obtain ⟨g, hg, e⟩ := List.mem_map.1 hm
  have hg' := List.mem_range.1 hg
  obtain ⟨Bs, base, O'⟩ := h.laid.opened
  obtain ⟨eZ, eG, -⟩ := atPure_at_laid_ground h.laid O'.blank hA
  obtain ⟨blk, a, -, Pl, -⟩ := K5.k5_member h hg'
  have ef := K5.k5LotK_find_K3 (W₀ := W₀) (Rc := IndexCommitterCoins) (X := Unit) h hg' O'.blank id Pl.plan
  have mem := List.mem_of_find?_eq_some ef
  have pb := List.find?_some ef
  have hb₂ : (b.place : Place) = K5.placeOf g := e.symm
  rw [show b.place = K5.placeOf g from hb₂]
  refine any_of_side (side_in_first I S O hA (M := K5.k5LotK id O.keyOf) ?_
    (by rw [eZ, eG, hK]; exact mem)) (eq_of_beq pb)
  show _ ∈ [_, _, _, _, _, _, _, _, _, _]
  exact .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))

/-- **K6's line.** -/
theorem line_k6 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A) :
    SidesWhere A.F.first.blocksInOrder A.H.first .K6 := by
  intro b hb hk _
  have hm := kind_place written_rest.2.2.1 ((plan_first I S O h hA) ▸ mem_planOf hb) hk
  obtain ⟨Bs, base, O'⟩ := h.laid.opened
  obtain ⟨eZ, eG, -⟩ := atPure_at_laid_ground h.laid O'.blank hA
  have hf : K6.headFitsB Zp Bs.G₀ = true := K6.head_fits_at_ground h O'.blank
  obtain ⟨hp, -⟩ := K6.head_lot_under_head h O'.blank
  unfold K6.headLotPlaces at hp
  rw [if_pos hf] at hp
  obtain ⟨c, hc, hcp⟩ := List.map_eq_singleton_iff.1 hp
  have e : (K6.headLot (X := Unit) K6.headFitsB (K6.headWit' id (I.weights Zp)) :
      HLot (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit).halves Zp Bs.G₀ =
      (P4.k6Hear Zp Bs.G₀).map _ := if_pos hf
  have ex : ∃ g ∈ (K6.headLot (X := Unit) K6.headFitsB (K6.headWit' id (I.weights Zp)) :
      HLot (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit).halves Zp Bs.G₀,
      g.place = IM.k6Place := by
    rw [e, hc]
    exact ⟨_, List.Mem.head _, hcp⟩
  obtain ⟨g, hg, ep⟩ := ex
  have hm' : b.place = IM.k6Place := List.mem_singleton.1 hm
  rw [hm']
  refine any_of_side (side_in_first I S O hA
    (M := HLot.byPub I.weights (LongLots.plain OnBytes.secondHashFunction S O).k6) ?_
    (by rw [eZ, eG]; exact hg)) ep
  show _ ∈ [_, _, _, _, _, _, _, _, _, _]
  exact .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))))

/-- **K10's line.** -/
theorem line_k10 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A) :
    SidesWhere A.F.first.blocksInOrder A.H.first .K10 := by
  intro b hb hk _
  have hplan := plan_first I S O h hA
  have h1 := List.all_eq_true.1 written_rest.2.2.2.2.1 _ (hplan ▸ mem_planOf hb)
  dsimp only at h1
  rw [hk] at h1
  rcases Bool.or_eq_true_iff.1 h1 with h0 | h2
  · exact absurd h0 (by decide)
  obtain ⟨j, hj, ej⟩ := List.any_eq_true.1 h2
  obtain ⟨Bs, base, O'⟩ := h.laid.opened
  obtain ⟨eZ, eG, -⟩ := atPure_at_laid_ground h.laid O'.blank hA
  obtain ⟨p, Q, b₂, -, -, hbi, -, hQ, hpl, -, -⟩ :=
    K10.tied_at_scope h.scope h.reads O' j (List.mem_range.1 hj)
  have eF := (atPure_at_laid h.laid hA).2
  have hpl' : (planOf WP.first.blocksInOrder)[closeIx j]?.map (·.place) = some b₂.place := by
    rw [planOf_alike (K14.planAlike_at_head h).first]
    show (planOf cF.blocksInOrder)[closeIx j]?.map (·.place) = _
    have : (planOf cF.blocksInOrder)[closeIx j]? = some ⟨b₂.place, partsCut b₂, b₂.rounds⟩ := by
      unfold planOf
      rw [List.getElem?_map]
      have e3 : cF.blocksInOrder[closeIx j]? = some b₂ := hbi
      rw [e3]
      rfl
    rw [this]
    rfl
  have eq : b.place = K10.closePlace Q := by
    have e4 : some b₂.place = some b.place := hpl'.symm.trans (beq_iff_eq.1 ej)
    rw [← Option.some.inj e4]
    exact hpl
  rw [eq]
  refine any_of_side (side_of_lot I S O hA (M := closeLotAt I S) ?_ (g := K10.lotHalf
      (fun w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells => ⟨w.trace, I.weights A.Z w.w₀, w.rc⟩)
      (widerRows S A.Z A.G) (K10.stAtZero cF.blocksInOrder fun ξ : ProofFile.Inst => ProofFile.startS A.Z ξ.pub)
      A.Z A.G Q) ?_) rfl
  · rw [widerFillAtCPUOWM_lots]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (.head _)))
  · show _ ∈ (match ProofFile.onlineFirstChainAt A.Z with
      | .ok cF =>
        (K10.seatLotC (fun w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells => ⟨w.trace, I.weights A.Z w.w₀, w.rc⟩)
          (widerRows S A.Z A.G) (K10.stAtZero cF.blocksInOrder fun ξ : ProofFile.Inst => ProofFile.startS A.Z ξ.pub)).halves
            A.Z A.G
      | .error _ => [])
    rw [eZ, h.laid.chain]
    exact K10.lotHalf_mem _ _ _ _ _ hQ

/-- **K12's line in the first chain.** -/
theorem line_k12 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A) :
    SidesWhere A.F.first.blocksInOrder A.H.first .K12 := by
  intro b hb hk _
  have hm := kind_place written_rest.2.2.2.1 ((plan_first I S O h hA) ▸ mem_planOf hb) hk
  obtain ⟨Bs, base, O'⟩ := h.laid.opened
  obtain ⟨eZ, eG, -⟩ := atPure_at_laid_ground h.laid O'.blank hA
  obtain ⟨pl, hf, hfit⟩ := K12.AtProof.fitsL_head_L h.toAtMg O'.blank
  have e := proxLotAt_ok (X := Unit) I S Bs.G₀ h.laid.chain (proxPlace_stands h.laid.chain)
    (by rw [proxPlace]; exact beq_self_eq_true _)
  have hm' : b.place = K12.AtProof.placeL := List.mem_singleton.1 hm
  rw [hm']
  have e2 := K12.AtProof.halves_lotAtDoor (V := Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (X := Unit)
    (Tr := Cells) (W₀ := W₀) (Rc := IndexCommitterCoins) (widerRows S)
    (fun Z _ (w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells) => ⟨w.trace, I.weights Z w.w₀, w.rc⟩)
    (fun Z G => K2.lotClosingAt G.first.layout (K2.segmentsOf Z G)) Zp Bs.G₀ pl hf hfit
  have ex : ∃ g ∈ (proxLotAt (X := Unit) I S).halves A.Z A.G, g.place = K12.AtProof.placeL := by
    rw [eZ, eG, e]
    show ∃ g ∈ (proxLotOf (X := Unit) I S).halves Zp Bs.G₀, g.place = K12.AtProof.placeL
    unfold proxLotOf
    rw [e2]
    exact ⟨_, List.Mem.head _, proxPlace Zp⟩
  obtain ⟨g, hg, ep⟩ := ex
  refine any_of_side (side_of_lot I S O hA (M := proxLotAt I S) ?_ hg) ep
  rw [widerFillAtCPUOWM_lots]
  exact List.mem_append_left _ (List.mem_append_right _ (.head _))

/-- **The shared chain's lines.** -/
theorem lines_shared (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A) :
    SidesWhere A.F.shared.blocksInOrder A.H.shared .K14 ∧ SidesWhere A.F.shared.blocksInOrder A.H.shared .K12 := by
  have hplan : planOf A.F.shared.blocksInOrder = planOf WP.shared.blocksInOrder := by
    rw [(atPure_at_laid h.laid hA).2]
    exact (planOf_alike (K14.planAlike_at_head h).shared).symm
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, hb8⟩ := eight_head h.toAtMg
  constructor
  · intro b hb hk hq
    have h1 := List.all_eq_true.1 written_rest.2.2.2.2.2.1 _ (hplan ▸ mem_planOf hb)
    dsimp only at h1
    rw [hk, hq] at h1
    have ep : b.place = K14.place 8 := by simpa using h1
    have hs := (K12.Light.facts_at_head h.toAtMg).1
    rw [ep, shared_list I S O h hA]
    have ex : ∃ g ∈ (K14.proverSidesOfSharedRounds { S := (qAt Zp Np).S, atPoint := 0, atZeta := 6 } (I.weights Zp) :
        List (Placed Empty (Common W₀ IndexCommitterCoins OnBytes.TableKey) Unit)), g.place = K14.place 8 := by
      unfold K14.proverSidesOfSharedRounds
      dsimp only
      rw [if_pos hs]
      exact ⟨_, List.mem_append_right _ (List.Mem.head _), rfl⟩
    obtain ⟨g, hg, eg⟩ := ex
    refine List.any_eq_true.2 ⟨g, ?_, by rw [eg]; exact beq_self_eq_true _⟩
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hg))
  · intro b hb hk _
    have hm := kind_place written_rest.2.2.2.2.2.2.1 (hplan ▸ mem_planOf hb) hk
    have hm' : b.place = K12.AtProof.placeU ∨ b.place = K12.AtProof.placeO := by
      simpa using hm
    rw [shared_list I S O h hA]
    rcases hm' with e | e
    · rw [e]
      have hu := K12.AtProof.halfU_at_head h.toAtMg b1 b2 b3 b4 b5 b6 b7 b8 hb8 (I.weights Zp)
        (fun w => Bind.ForProver.encW Zp (I.weights Zp w))
      have hmem : ∃ g, g ∈ K12.AtProof.halfU (I.weights Zp)
          (fun w => Bind.ForProver.encW Zp (I.weights Zp w)) Zp := by
        rw [hu]
        exact ⟨_, List.Mem.head _⟩
      obtain ⟨g, hg⟩ := hmem
      exact List.any_eq_true.2 ⟨g, List.mem_append_left _ (List.mem_append_right _ hg),
        by rw [AtFullSide.K12.halfU_place _ _ _ g hg]; exact beq_self_eq_true _⟩
    · rw [e]
      obtain ⟨pO, hO⟩ := K12.AtProof.someO_at_head h.toAtMg
      have hu := K12.AtProof.halfO_at_head h.toAtMg b1 b2 b3 b4 b5 b6 b7 b8 hb8 (I.weights Zp) hO
      have hmem : ∃ g, g ∈ K12.AtProof.halfO (I.weights Zp) Zp := by
        rw [hu]
        exact ⟨_, List.Mem.head _⟩
      obtain ⟨g, hg⟩ := hmem
      exact List.any_eq_true.2 ⟨g, List.mem_append_right _ hg,
        by rw [AtFullSide.K12.halfO_place _ _ g hg]; exact beq_self_eq_true _⟩

/-- **The second chain's line.** -/
theorem line_second (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A) :
    SidesWhere A.F.second.blocksInOrder A.H.second .K12 := by
  have hplan : planOf A.F.second.blocksInOrder = planOf WP.second.blocksInOrder := by
    rw [(atPure_at_laid h.laid hA).2]
    exact (planOf_alike (K14.planAlike_at_head h).second).symm
  intro b hb hk _
  have hm := kind_place written_rest.2.2.2.2.2.2.2 (hplan ▸ mem_planOf hb) hk
  obtain ⟨Bs, base, O'⟩ := h.laid.opened
  obtain ⟨eZ, eG, -⟩ := atPure_at_laid_ground h.laid O'.blank hA
  obtain ⟨-, -, -, -, -, -, -, -, -, e2, -⟩ := atPure_ok hA
  obtain ⟨J, hJ, eJ⟩ := AtFullSide.K12.second_made h O' I S O Bs.G₀
  have hm' : b.place = K12.AtProof.placeW := List.mem_singleton.1 hm
  have hw : ∃ g ∈ (secondW I OnBytes.secondHashFunction S O Zp Bs.G₀ : List (Placed _ _ Unit)),
      g.place = K12.AtProof.placeW := by
    rw [secondW_ok I OnBytes.secondHashFunction S O Bs.G₀ (K14.nowSharedBy_at_head h (I.weights Zp))
      h.laid.places h.laid.chain]
    have hl : ∃ g, g ∈ (K12.AtProof.halfW S (P5J.F0T OnBytes.secondHashFunction Zp Np cF)
        VerifiableInference.Desc.K12.Seat.enterOwn O.pile (K1.lotNo OnBytes.secondHashFunction Zp)
        (fun w => ⟨w.trace, I.weights Zp w.w₀, w.rc⟩) (fun w => I.weights Zp w.w₀)
        (fun P w => K12.AtProof.randAt P w.rc) Zp Bs.G₀ :
          List (Placed (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit)) := by
      unfold K12.AtProof.halfW
      rw [hJ]
      exact ⟨_, List.Mem.head _⟩
    obtain ⟨g, hg⟩ := hl
    exact ⟨g, hg, AtFullSide.K12.halfW_place _ _ _ _ _ _ _ _ _ _ g hg⟩
  obtain ⟨g, hg, ep⟩ := hw
  rw [hm', e2, eZ, eG]
  exact List.any_eq_true.2 ⟨g, hg, by rw [ep]; exact beq_self_eq_true _⟩

/-- **WHAT EVERY KIND OWES, PAID**, where the keys of K5 are keyOfK3. -/
theorem kinds_whole (hK : O.keyOf = K5.keyOfK3) (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A) : KindsWhole A.F A.H := by
  obtain ⟨w1, w2⟩ := k1_sidesWhere I S O h hA
  obtain ⟨s14, s12⟩ := lines_shared I S O h hA
  refine ⟨fun κ hκ => ?_, fun κ hκ => ?_, fun κ hκ => ?_⟩
  · simp only [sendsFirst, List.mem_cons, List.not_mem_nil, or_false] at hκ
    rcases hκ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact w1
    · exact line_k2 I S O h hA
    · exact line_k3 I S O h hA
    · exact line_k4 I S O h hA
    · exact line_k5 I S O hK h hA
    · exact line_k6 I S O h hA
    · exact line_k7 I S O h hA
    · exact line_k10 I S O h hA
    · exact line_k11 I S O h hA
    · exact line_k12 I S O h hA
    · exact line_k13 I S O h hA
  · simp only [sendsShared, List.mem_cons, List.not_mem_nil, or_false] at hκ
    rcases hκ with rfl | rfl | rfl
    · exact w2
    · exact s12
    · exact s14
  · simp only [sendsSecond, List.mem_cons, List.not_mem_nil, or_false] at hκ
    subst hκ
    exact line_second I S O h hA

/-- **The first chain's halved at the base prover**: h4 of first_chain_debts_halved. -/
theorem halved_first_base (hK : O.keyOf = K5.keyOfK3) (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A) :
    halved A.F.first.blocksInOrder A.H.first = true := by
  have hq : quietTest sendsFirst (planOf A.F.first.blocksInOrder) = true := by
    rw [plan_first I S O h hA]
    exact written_quiet.1
  exact (whole_of hq (kinds_whole I S O hK h hA).first).1

/-- **T1's SidesAreWhole AT THE BASE PROVER.** -/
theorem sides_are_whole (hK : O.keyOf = K5.keyOfK3) (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A) :
    halvedAll A.F A.H = true ∧ rootedAll A.F A.H = true ∧ sealPlain A.F = true := by
  have hF : PlanAlike WP A.F := by
    rw [(atPure_at_laid h.laid hA).2]
    exact K14.planAlike_at_head h
  obtain ⟨a, b⟩ := sidesWhole_of_kinds hF (kinds_whole I S O hK h hA)
  exact ⟨a, b, sealPlain_alike hF⟩

end

end ProofFile.Honest.K1.Pay

#print axioms ProofFile.Honest.K1.Pay.kinds_whole
#print axioms ProofFile.Honest.K1.Pay.sides_are_whole
#print axioms ProofFile.Honest.K1.Pay.halved_first_base
#print axioms ProofFile.Honest.K1.Pay.written_rest
#print axioms ProofFile.Honest.K1.Pay.line_k4
#print axioms ProofFile.Honest.K1.Pay.line_k5
#print axioms ProofFile.Honest.K1.Pay.line_k6
#print axioms ProofFile.Honest.K1.Pay.line_k10
#print axioms ProofFile.Honest.K1.Pay.line_k12
#print axioms ProofFile.Honest.K1.Pay.lines_shared
#print axioms ProofFile.Honest.K1.Pay.line_second
