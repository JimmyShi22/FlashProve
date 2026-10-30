-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K12/TwiceFirstW.lean: THE PREMISE ht OF `readyTests_fillW` (ReadyTestsW.lean): NO TWO
SIDES OF THE FIRST CHAIN AT ONE PLACE, at the wide filling `onlineProverPartsInUse I o' S O`, under the
library's head.

  `link_flat_nodup`   a list by segments, each segment's sides at its own link, has no double
  `link_map_nodup`, `link_pieces`   the like at one side a segment; a link's two pieces
  `k1_once`, `k2_once`, `k3_once`, `k8_once`   four lots: no double. K2 under the head, from the
                 written table; the others at every public part and ground
  `ten_once`   no double in any of the ten lots (`widerPairs`: H2's list of them with their kinds;
                 that its first column is the filling's ten is `widerFillAt_lots`)
  `ten_apart`, `ten_kinds`   two of the ten share no place: their kinds differ; nor with the
                 closings or L's pair
  `twice_first_fill`, `twice_first_at`   so no double in the whole first chain, at `onlineProverFromPublicFiles`'s prover
  `readyTests_fillW₀`   `readyTests` at one premise: hw: w₀ is in range
  `readyTests_at_head`   under h and hl: `onlineProverFromPublicFiles` returns at `fullIn` and `readyTests` at every
                 index

Limits.
- That no sides stand twice says nothing on what they play; `chainSteps` at the three chains,
  behind `readyTests` in `ready`, is not read.
- The wide filling is defined in Honest/K1/Law/WSideAtFill.lean.
- It moves no count. Nothing on completeness, soundness or hiding.
Terms: Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import AtFullSide.K12.ReadyTestsW
import Johnson.Desc.ProofFile.Honest.Thread.FirstFillAll
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten
import Johnson.Desc.ProofFile.Honest.K2.Law.PublicAtWritten
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.SitesOnce
import Johnson.Desc.ProofFile.Honest.K3.Law.CoverageLotsNamed
import Johnson.Desc.ProofFile.Honest.K4.Law.LotOnce

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K12
open VerifiableInference.Desc (Block Chain Place FileDescription KindName)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof ProofFile.Honest.K5
open ProofFile (Pub Ground SecondHashFunctionArgument)
open P5J (AtMgA TS)

variable {V W X : Type}

/-- **Sides by segments, each at its own link, have no double.** -/
theorem link_flat_nodup {α : Type} (Ls : List α) (f : α × Nat → List (Placed V W X))
    (hl : ∀ y, ∀ x ∈ f y, x.place.link = some y.2)
    (hn : ∀ y, ((f y).map (·.place)).Nodup) :
    ((Ls.zipIdx.flatMap f).map (·.place)).Nodup := by
  rw [List.map_flatMap]
  refine List.nodup_flatMap.2 ⟨fun y _ => hn y, ?_⟩
  have hz : (Ls.zipIdx.map (·.2)).Nodup := by
    rw [List.zipIdx_map_snd]
    exact List.nodup_range'
  refine (List.pairwise_map.1 hz).imp ?_
  intro a b hab p ha hb
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
  obtain ⟨z, hz', e⟩ := List.mem_map.1 hb
  have e1 := hl a x hx
  have e2 := hl b z hz'
  rw [e] at e2
  exact hab (Option.some.inj (e1.symm.trans e2))

/-- The like at one side a segment. -/
theorem link_map_nodup {α : Type} (Ls : List α) (f : α × Nat → Placed V W X)
    (hl : ∀ y, (f y).place.link = some y.2) : ((Ls.zipIdx.map f).map (·.place)).Nodup := by
  have e : Ls.zipIdx.map f = Ls.zipIdx.flatMap fun y => [f y] := by
    generalize Ls.zipIdx = l
    induction l with
    | nil => rfl
    | cons a l ih =>
      rw [List.map_cons, List.flatMap_cons, ih]
      rfl
  rw [e]
  refine link_flat_nodup Ls _ (fun y x hx => ?_) fun y => List.nodup_singleton _
  obtain rfl := List.mem_singleton.1 hx
  exact hl y

/-- A link's two pieces. -/
theorem link_pieces {G : Ground} {Y : OnBytes.Model.Stages.LinkH} {pr pd : Nat}
    {a b : Option (List Nat)}
    (h : VerifiableInference.Desc.K1.linkNumbers G Y = some (pr, pd, a, b)) :
    (pr = 4 ∧ pd = 6) ∨ (pr = 5 ∧ pd = 7) := by
  unfold VerifiableInference.Desc.K1.linkNumbers at h
  split at h
  · obtain ⟨_, -, e⟩ := Option.map_eq_some_iff.1 h
    simp only [Prod.mk.injEq] at e
    exact Or.inl ⟨e.1.symm, e.2.1.symm⟩
  · split at h
    · obtain ⟨_, -, e⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at e
      exact Or.inl ⟨e.1.symm, e.2.1.symm⟩
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact Or.inr ⟨h.1.symm, h.2.1.symm⟩

/-- **K1's lot has no double.** -/
theorem k1_once (S : OnBytes.HonestTrace.Sz) (wit : W → K1.PlaceIn ProofFile.Inst) (o : SecondHashFunctionArgument)
    (Z : Pub) (G : Ground) :
    (((K1.dataSideNo S wit o : HLot V W X).halves Z G).map (·.place)).Nodup := by
  show ((K1.lotHalves wit (K1.lotNo o Z) (K1.lotData S) Z G : List (Placed V W X)).map
    (·.place)).Nodup
  unfold K1.lotHalves
  rw [List.map_cons]
  have hfacts : ∀ y : OnBytes.Model.Stages.LinkH × Nat,
      ∀ x ∈ (match VerifiableInference.Desc.K1.linkNumbers G y.1 with
      | none => ([] : List (Placed V W X))
      | some (pr, pd, _, _) =>
        [K1.placeHalf wit (K1.laterJobAt G.first (VerifiableInference.Desc.K1.gpOf Z) y.2 pr 1
            (K1.lotNo o Z ⟨1, some y.2, pr, .K1⟩) (K1.lotData S Z G)),
         K1.placeHalf wit (K1.laterJobAt G.first (VerifiableInference.Desc.K1.gpOf Z) y.2 pd 2
            (K1.lotNo o Z ⟨1, some y.2, pd, .K1⟩) (K1.lotData S Z G))]),
      x.place.link = some y.2 ∧ x.place.piece ≠ 1 := by
    intro y x hx
    split at hx
    · cases hx
    · rename_i pr pd a b hq
      have hp := link_pieces hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · refine ⟨rfl, ?_⟩
        show pr ≠ 1
        omega
      · refine ⟨rfl, ?_⟩
        show pd ≠ 1
        omega
  refine List.nodup_cons.2 ⟨?_, ?_⟩
  · intro hm
    obtain ⟨x, hx, e⟩ := List.mem_map.1 hm
    obtain ⟨Yl, -, hy⟩ := List.mem_flatMap.1 hx
    have q := (hfacts Yl x hy).2
    rw [e] at q
    exact q rfl
  · refine link_flat_nodup _ _ (fun y x hx => (hfacts y x hx).1) fun y => ?_
    obtain ⟨Y, l⟩ := y
    cases hq : VerifiableInference.Desc.K1.linkNumbers G Y with
    | none =>
      simp only [hq, List.map_nil]
      exact List.nodup_nil
    | some v =>
      obtain ⟨pr, pd, a, b⟩ := v
      have hp := link_pieces hq
      simp only [hq, List.map_cons, List.map_nil]
      refine List.nodup_cons.2 ⟨?_, List.nodup_singleton _⟩
      intro hm
      have e := List.mem_singleton.1 hm
      have e' : pr = pd := congrArg (·.piece) e
      omega

/-- **K8's lot has no double.** -/
theorem k8_once {W₀ Rc Xi Tr : Type} (cells : Tr → Cells)
    (mats : Pub → Ground → OnBytes.Model.Stages.LinkH → Nat → List (Nat × String × Nat))
    (Z : Pub) (G : Ground) :
    (((K8.smallLot cells mats : HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X).halves Z G).map
      (·.place)).Nodup :=
  link_map_nodup _ _ fun _ => rfl

/-- **K3's lot has no double.** -/
theorem k3_once {W₀ Rc Tr : Type} (cells : Tr → Cells) (weights : W₀ → Weights) (Z : Pub)
    (G : Ground) :
    (((K3.theLotInst cells weights :
      HLot (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X).halves Z G).map
      (·.place)).Nodup := by
  show List.Nodup (List.map (fun y : Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X =>
    y.place) (List.map _ (K3.lookSites Z)))
  rw [List.map_map]
  exact K3.Law.AtThr.site_places_once Z

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}

/-- **K2's lot has no double, under the head.** -/
theorem k2_once {W₀ Rc Xi Tr : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (Op : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np))
    (Dd : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers) (G : Ground) :
    (((K2.switchLot Dd readers : HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X).halves Zp G).map
      (·.place)).Nodup := by
  show List.Nodup (List.map (fun y : Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X => y.place)
    (List.map _ (K2.switchPlaces Zp G)))
  rw [List.map_map]
  unfold K2.switchPlaces
  rw [K2.Law.spots_at_head h.toAtMg Op]
  cases hp : P1K2.prepOf Zp G with
  | none => exact List.nodup_nil
  | some P =>
    rw [List.map_map]
    exact K2.Law.spotsW_nodup

/-- **No double in any of the ten lots.** -/
theorem ten_once {W₀ : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (Op : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np))
    (I : WiderIn W₀) (o' : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (G : Ground) :
    ∀ q ∈ widerPairs I o' S O, ((q.1.halves Zp G).map (·.place)).Nodup := by
  intro q hq
  simp only [widerPairs, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact k1_once (V := Local W₀ IndexCommitterCoins ProofFile.Inst Cells) (X := Unit) S
      (fun w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells => ⟨w.x, ⟨w.trace, I.weights Zp w.w₀, w.rc⟩⟩) o' Zp G
  · exact k2_once (X := Unit) h Op (widerRows S Zp G)
      (fun w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells => ⟨w.trace, I.weights Zp w.w₀, w.rc⟩) G
  · exact List.nodup_singleton _
  · exact List.nodup_singleton _
  · exact List.nodup_singleton _
  · exact k3_once (X := Unit) (Rc := IndexCommitterCoins) id (I.weights Zp) Zp G
  · exact K4.k4HLot_places_once id (I.weights Zp) (fun _ _ => K4.k4LookAt) Zp G
  · exact k5LotK_places_once id O.keyOf Zp G
  · show List.Nodup (List.map (fun y : Placed (Local W₀ IndexCommitterCoins ProofFile.Inst Cells)
      (Local W₀ IndexCommitterCoins ProofFile.Inst Cells) Unit => y.place) (if _ then _ else []))
    split
    · rw [List.map_map]
      unfold P4.k6Hear
      cases (P4.headBefore Zp G).bind _ <;> simp
    · exact List.nodup_nil
  · exact k8_once (X := Unit) id (fun _ G _ l => K3.matsOwn G.W l) Zp G

/-- **Two of the ten share no place.** -/
theorem ten_apart {W₀ : Type} (I : WiderIn W₀) (o' : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) (G : Ground) :
    ((widerPairs I o' S O).map (·.1)).Pairwise fun L M =>
      ∀ a ∈ L.halves Zp G, ∀ b ∈ M.halves Zp G, a.place ≠ b.place := by
  have K := FirstFill.widerKinds I o' S O Zp G
  have hp : (widerPairs I o' S O).Pairwise fun q r => q.2 ≠ r.2 :=
    List.pairwise_map.1 widerPairs_nodup
  refine List.pairwise_map.2 (hp.imp_of_mem ?_)
  intro q s hq hs ne a ha b hb e
  have k1 := K.all q hq a ha
  have k2 := K.all s hs b hb
  rw [e, k2] at k1
  exact ne k1.symm

/-- Each of the ten's kinds is neither the closings' nor the test's. -/
theorem ten_kinds {W₀ : Type} (I : WiderIn W₀) (o' : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) : ∀ q ∈ widerPairs I o' S O, q.2 ≠ .K10 ∧ q.2 ≠ .K12 := by
  intro q hq
  have e : (widerPairs I o' S O).map (·.2) = [KindName.K1, .K2, .K7, .K11, .K13, .K3, .K4, .K5,
      .K6, .K8] := rfl
  have hm : q.2 ∈ [KindName.K1, .K2, .K7, .K11, .K13, .K3, .K4, .K5, .K6, .K8] := by
    rw [← e]
    exact List.mem_map_of_mem hq
  generalize q.2 = k at hm
  revert k
  decide

/-- **ht: NO TWO SIDES OF THE FIRST CHAIN AT ONE PLACE.** -/
theorem twice_first_fill {W₀ : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (Op : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np))
    (I : WiderIn W₀) (o' : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (G : Ground) :
    twice (firstOf Zp G (onlineProverPartsInUse I o' S O).lots) = [] := by
  refine twice_firstOf Zp G _ ?_ ?_
  · intro L hL
    rw [widerFillAtCPUOWM_lots] at hL
    simp only [List.mem_append, List.mem_singleton] at hL
    rcases hL with ((h1 | rfl) | rfl) | rfl
    · rw [widerFillAt_lots] at h1
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 h1
      exact ten_once h Op I o' S O G q hq
    · exact closeLotAt_once I S G Op
    · exact proxLotAt_once I S Zp G
    · exact wLot_once I o' O Zp G
  · rw [widerFillAtCPUOWM_lots]
    have hw := wLot_apart I o' S O Zp G
    have hk : ∀ q ∈ widerPairs I o' S O, ∀ a ∈ q.1.halves Zp G, a.place.kind = q.2 :=
      (FirstFill.widerKinds I o' S O Zp G).all
    refine List.pairwise_append.2 ⟨List.pairwise_append.2 ⟨List.pairwise_append.2
      ⟨ten_apart I o' S O G, List.pairwise_singleton _ _, ?_⟩, List.pairwise_singleton _ _, ?_⟩,
      List.pairwise_singleton _ _, ?_⟩
    · intro L hL M hM a ha b hb e
      obtain rfl := List.mem_singleton.1 hM
      rw [widerFillAt_lots] at hL
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hL
      have k1 := hk q hq a ha
      have k2 := closeLotAt_kinds I S Zp G b hb
      rw [e, k2] at k1
      exact (ten_kinds I o' S O q hq).1 k1.symm
    · intro L hL M hM a ha b hb e
      obtain rfl := List.mem_singleton.1 hM
      have k2 := proxLotAt_kinds I S Zp G b hb
      rcases List.mem_append.1 hL with h1 | h1
      · rw [widerFillAt_lots] at h1
        obtain ⟨q, hq, rfl⟩ := List.mem_map.1 h1
        have k1 := hk q hq a ha
        rw [e, k2] at k1
        exact (ten_kinds I o' S O q hq).2 k1.symm
      · obtain rfl := List.mem_singleton.1 h1
        have k1 := closeLotAt_kinds I S Zp G a ha
        rw [e, k2] at k1
        cases k1
    · intro L hL M hM a ha b hb
      obtain rfl := List.mem_singleton.1 hM
      exact hw L hL a ha b hb

/-- **ht AT `onlineProverFromPublicFiles`'s PROVER.** -/
theorem twice_first_at {W₀ : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (I : WiderIn W₀)
    (o' : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I o' S O) = .ok A) :
    twice A.H.first = [] := by
  obtain ⟨Bs', base', Op⟩ := h.laid.opened
  have hZ := (atPure_at_laid h.laid hA).1
  obtain ⟨-, -, -, -, -, -, -, e1, -⟩ := atPure_ok hA
  rw [e1, hZ]
  exact twice_first_fill h Op I o' S O A.G

/-- **`readyTests` RETURNS, AT ONE PREMISE.** hw: w₀ is in range. -/
theorem readyTests_fillW₀ {W₀ : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (I : WiderIn W₀)
    (o' : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I o' S O) = .ok A) {w₀ : W₀}
    (hw : A.H.inRange w₀ = true) : readyTests A.F A.B A.H w₀ = .ok () :=
  readyTests_fillW h I o' S O hA (twice_first_at h I o' S O hA) hw

/-- **UNDER h AND hl: `onlineProverFromPublicFiles` RETURNS AT THE WIDE FILLING, AND AT ITS PROVER `readyTests` RETURNS
AT EVERY INDEX.** At `fullIn` every index is in range. -/
theorem readyTests_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) (o' : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    ∃ A, onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse fullIn o' S O) = .ok A ∧
      ∀ w₀, readyTests A.F A.B A.H w₀ = .ok () := by
  obtain ⟨A, hA, -⟩ := atPure_returns_fillW₀ h hl o' S O
  refine ⟨A, hA, fun w₀ => readyTests_fillW₀ h fullIn o' S O hA ?_⟩
  obtain ⟨-, -, -, -, -, e, -⟩ := atPure_ok hA
  rw [e]
  rfl

end AtFullSide.K12

#print axioms AtFullSide.K12.link_flat_nodup
#print axioms AtFullSide.K12.link_map_nodup
#print axioms AtFullSide.K12.link_pieces
#print axioms AtFullSide.K12.k1_once
#print axioms AtFullSide.K12.k8_once
#print axioms AtFullSide.K12.k3_once
#print axioms AtFullSide.K12.k2_once
#print axioms AtFullSide.K12.ten_once
#print axioms AtFullSide.K12.ten_apart
#print axioms AtFullSide.K12.ten_kinds
#print axioms AtFullSide.K12.twice_first_fill
#print axioms AtFullSide.K12.twice_first_at
#print axioms AtFullSide.K12.readyTests_fillW₀
#print axioms AtFullSide.K12.readyTests_at_head
