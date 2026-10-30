-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- Read whole once, proofs by eye.
/-
AtFullSide/K12/ReturnsAtFillW.lean: THE FRAME's MAKER onlineProverFromPublicFiles RETURNS AT THE WIDE FILLING
`onlineProverPartsInUse fullIn o' S O` (K1/Law/WSideAtFill.lean): with the closings, L's pair, U's, O's
and W's pairs, and W's sender laid: UNDER THE LIBRARY's HEAD AND ITS TEST `protocolDataWellFormed`.


  `four_U`, `four_O`, `four_W`, `halfU_place`, `halfO_place`, `halfW_place`, `wHalf_place`   each
                 pair stands at its test's place, and W's sender at its own, at every public part
  `written_places_all`   the four places stand in the written description's chains, by the kernel
  `makerAsks_fillW`   what `onlineProverFromPublicFiles` asks of the filling holds: by the steps of
                 `makerAsks_ownC_of_own`: L's pair (`proxLotAt_clean`), U's and O's (the shared
                 chain), W's (the last chain), W's sender (the first chain)
  `atPure_returns_fillW`   so `onlineProverFromPublicFiles` returns there, hB a premise, as at its sisters
  `atPure_returns_fillW₀`   hB paid by `bookWhole_returns_written_ahead`: h and hl alone

What it pays. At `Cm.Idx`, `fullIn`, o' := OnBytes.secondHashFunction it is the premise hA of `filling_at_head`,
`half_w_wM` and `ground_at_head`: these stand under h and hl.

By what. `makerAsks_widerC_fullIn` (K5/Law/ReturnsAtWiderCFullIn.lean); `planAlike_at_head`
(K14/WrittenAtHead.lean), so the written places are the description's; `atPure_returns_fill`
(K5/Law/ReturnsFill.lean).

Limits.
- IT IS NOT «second ≠ []». `MakerAsks` forbids halves that stray and asks for none: THIS LAW HOLDS
  ALSO WHERE THE PAIRS ARE NOT LAID: in the six's error arm the shared field is [], and `secondW` is
  [] in its last arm. «second ≠ []» wants behind it: the six made under the head, `filling_at_head`,
  and that `realW` returns (`four`, `sendPub_at_head`, `linMessageW`).
- THAT `ready` RETURNS IS NOT SAID: its own tests are other tests: `readyTests` refuses two halves
  at one place, and behind it `chainSteps` asks the book's rows, names and counts of each half
  (Frame.lean): W's lot adds a half at M:4.
- That `onlineProverFromPublicFiles` returns says nothing on what its prover plays.
- hl and the head are hypotheses. ONE NAMED FILLING, at `fullIn` and `LongLots.plain`.
- The wide filling is defined in Honest/K1/Law/WSideAtFill.lean.
- The full size alone. It moves no count. Nothing on completeness, soundness or hiding.
Terms: Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import AtFullSide.K12.DescAtHeadW
import AtFullSide.K14.BookWholeWritten
import Johnson.Desc.ProofFile.Honest.K5.Law.ReturnsAtWiderCFullIn
import Johnson.Desc.ProofFile.Honest.K14.WrittenAtHead
import Johnson.Desc.ProofFile.Honest.K5.Law.LotClean
import Johnson.Desc.ProofFile.Honest.K10.LotAll
import Johnson.Desc.ProofFile.Honest.AtPureWiderK12Places
import Johnson.AtFull.ProofPlan.PlanAlike

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K12
open VerifiableInference.Desc (Block Chain Place)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof ProofFile.Honest.K5
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)
open P5J (AtMgA TS)
open ProofFile (Pub Ground SecondHashFunctionArgument blankBy pureRoad)
open VerifiableInference.Desc (alike₂_place)

section Places
variable {W₀ : Type}

theorem four_U {Z : Pub} {F : Four} (h : four Z = some F) : F.U.place = placeU := by
  unfold four at h
  split at h
  · obtain rfl := Option.some.inj h
    exact p12At_place _ _
  · cases h

theorem four_O {Z : Pub} {F : Four} {p : VerifiableInference.Desc.K12.P12} (h : four Z = some F)
    (hp : F.O = some p) : p.place = placeO := by
  unfold four at h
  split at h
  · obtain rfl := Option.some.inj h
    obtain ⟨n, -, rfl⟩ := Option.map_eq_some_iff.1 hp
    exact p12At_place _ _
  · cases h

theorem four_W {Z : Pub} {F : Four} (h : four Z = some F) : F.W.place = placeW := by
  unfold four at h
  split at h
  · obtain rfl := Option.some.inj h
    exact p12At_place _ _
  · cases h

/-- **U's pair stands at its place.** -/
theorem halfU_place (wt : W₀ → Weights) (enc : W₀ → IndexCommitterCoins → ℕ → ℕ → Option (List Cb.Gl.F))
    (Z : Pub) : ∀ x ∈ halfU wt enc Z, x.place = placeU := by
  intro x hx
  unfold halfU at hx
  obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hx
  have hJ' : realU wt enc Z = some J := Option.mem_toList.1 hJ
  unfold realU jobRealU at hJ'
  obtain ⟨M, hM, rfl⟩ := Option.map_eq_some_iff.1 hJ'
  obtain ⟨F, hF, hM⟩ := Option.bind_eq_some_iff.1 hM
  obtain ⟨A, -, hM⟩ := Option.bind_eq_some_iff.1 hM
  obtain ⟨bs, -, rfl⟩ := Option.map_eq_some_iff.1 hM
  exact four_U hF

/-- **O's pair stands at its place.** -/
theorem halfO_place (wt : W₀ → Weights) (Z : Pub) : ∀ x ∈ halfO wt Z, x.place = placeO := by
  intro x hx
  unfold halfO at hx
  obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hx
  have hJ' : realO wt Z = some J := Option.mem_toList.1 hJ
  unfold realO jobRealO at hJ'
  obtain ⟨M, hM, rfl⟩ := Option.map_eq_some_iff.1 hJ'
  obtain ⟨F, hF, hM⟩ := Option.bind_eq_some_iff.1 hM
  obtain ⟨p, hp, hM⟩ := Option.bind_eq_some_iff.1 hM
  obtain ⟨A, -, hM⟩ := Option.bind_eq_some_iff.1 hM
  obtain ⟨bs, -, rfl⟩ := Option.map_eq_some_iff.1 hM
  exact four_O hF hp

/-- **W's pair stands at its place.** -/
theorem halfW_place {V Xi Rc Tr X : Type} (S : OnBytes.HonestTrace.Sz)
    (Fd : VerifiableInference.Desc.FileDescription Xi)
    (enter : Fd.S₃ → Except String VerifiableInference.Desc.K12.T12)
    (pile : Pub → Ground → K13.PileOf Xi) (no : Place → Nat)
    (readers : Local W₀ Rc Xi Tr → Readers) (weights : Local W₀ Rc Xi Tr → Weights)
    (rand : Desc.K14.P14 → Local W₀ Rc Xi Tr → TableRand) (Z : Pub) (G : Ground) :
    ∀ x ∈ (halfW S Fd enter pile no readers weights rand Z G :
      List (Placed V (Local W₀ Rc Xi Tr) X)), x.place = placeW := by
  intro x hx
  unfold halfW at hx
  obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hx
  have hJ' : realW S Fd enter pile no readers weights rand Z G = some J := Option.mem_toList.1 hJ
  unfold realW jobRealW at hJ'
  obtain ⟨M, hM, rfl⟩ := Option.map_eq_some_iff.1 hJ'
  obtain ⟨F, hF, hM⟩ := Option.bind_eq_some_iff.1 hM
  obtain ⟨A, -, hM⟩ := Option.bind_eq_some_iff.1 hM
  obtain ⟨msg, -, rfl⟩ := Option.map_eq_some_iff.1 hM
  exact four_W hF

/-- **W's sender stands at its place.** -/
theorem wHalf_place {X : Type} (I : WiderIn W₀) (o : SecondHashFunctionArgument) (O : OnlineProverArguments) (Z : Pub)
    (G : Ground) : ∀ x ∈ (wLotAt (X := X) I o O).halves Z G, x.place = ⟨1, none, 4, .K1⟩ := by
  intro x hx
  rw [wLotAt_halves] at hx
  cases hm : OnBytes.linMessageW Z.first.lin with
  | none =>
    rw [hm] at hx
    cases hx
  | some msg =>
    rw [hm] at hx
    obtain rfl := List.mem_singleton.1 hx
    rfl

end Places

set_option maxRecDepth 1000000 in
/-- The four places stand in the written description's chains. -/
theorem written_places_all :
    (⟨1, none, 4, .K1⟩ : Place) ∈ WP.first.blocksInOrder.map (·.place) ∧
    placeU ∈ WP.shared.blocksInOrder.map (·.place) ∧ placeO ∈ WP.shared.blocksInOrder.map (·.place) ∧
    placeW ∈ WP.second.blocksInOrder.map (·.place) := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **WHAT THE MAKER ASKS, AT THE WIDE FILLING.** CONDITIONAL: h, hl, hB. -/
theorem makerAsks_fillW (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (hB : ∃ B, bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B)
    (o' : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    ∀ G, blankBy pureRoad.links Zp = some G →
      MakerAsks (onlineProverPartsInUse fullIn o' S O) Zp G
        (P5J.F0T OnBytes.secondHashFunction Zp Np cF) := by
  intro G hG
  have a := makerAsks_widerC_fullIn h hl hB o' S O G hG
  obtain ⟨Bs, base, Op⟩ := h.laid.opened
  have pa := ProofFile.Honest.K14.planAlike_at_head h
  obtain ⟨p1, p2, p3, p4⟩ := written_places_all
  have e1 := alike₂_place _ _ pa.first
  have e2 := alike₂_place _ _ pa.shared
  have e3 := alike₂_place _ _ pa.second
  rw [e1] at p1
  rw [e2] at p2 p3
  rw [e3] at p4
  refine ⟨(strays_firstOf_iff _ Zp G _).2 fun M hM => ?_, ?_, ?_, a.range⟩
  · rw [widerFillAtCPUOWM_lots] at hM
    simp only [List.mem_append, List.mem_singleton] at hM
    rcases hM with ((h1 | rfl) | rfl) | rfl
    · exact (strays_firstOf_iff _ Zp G _).1 a.first M
        (List.mem_append_left _ h1)
    · exact (strays_firstOf_iff _ Zp G _).1 a.first _
        (List.mem_append_right _ (List.mem_singleton.2 rfl))
    · exact proxLotAt_clean fullIn S G Op
    · refine K10.strays_nil fun y hy => ?_
      rw [wHalf_place fullIn o' O Zp G y hy]
      exact p1
  · show strays _ (sharedWithUO fullIn Zp) = []
    cases hs : nowSharedBy (fullIn.weights Zp) Zp with
    | error e =>
      rw [sharedWithUO_error fullIn hs]
      rfl
    | ok six =>
      have h6 := a.shared
      have hv : (widerFillAtC fullIn o' S O).shared Zp G = six := by
        show (nowSharedBy (fullIn.weights Zp) Zp).toOption.getD [] = six
        rw [hs]
        rfl
      rw [hv] at h6
      rw [sharedWithUO_ok fullIn hs, sharedWithU_ok fullIn hs, strays_append, strays_append, h6]
      have hu : strays (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder
          (halfU (fullIn.weights Zp)
            (fun w => Bind.ForProver.encW Zp (fullIn.weights Zp w)) Zp) = [] :=
        K10.strays_nil fun y hy => by
          rw [halfU_place _ _ Zp y hy]
          exact p2
      have ho : strays (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder
          (halfO (fullIn.weights Zp) Zp) = [] :=
        K10.strays_nil fun y hy => by
          rw [halfO_place _ Zp y hy]
          exact p3
      rw [hu, ho]
      rfl
  · show strays _ (secondW fullIn o' S O Zp G) = []
    refine K10.strays_nil fun y hy => ?_
    unfold secondW at hy
    split at hy
    · rw [halfW_place _ _ _ _ _ _ _ _ Zp G y hy]
      exact p4
    · cases hy

/-- **onlineProverFromPublicFiles RETURNS AT THE WIDE FILLING.** CONDITIONAL: h, hl, hB. -/
theorem atPure_returns_fillW (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (hB : ∃ B, bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B)
    (o' : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    ∃ A, onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse fullIn o' S O) = .ok A ∧
      A.Z = Zp ∧ A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF ∧ blankBy pureRoad.links Zp = some A.G :=
  atPure_returns_fill h hl hB _ (makerAsks_fillW h hl hB o' S O)

/-- **onlineProverFromPublicFiles RETURNS AT THE WIDE FILLING, hB PAID.** CONDITIONAL: h, hl. -/
theorem atPure_returns_fillW₀ (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (o' : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    ∃ A, onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse fullIn o' S O) = .ok A ∧
      A.Z = Zp ∧ A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF ∧ blankBy pureRoad.links Zp = some A.G := by
  obtain ⟨B, hB, -⟩ := AtFullSide.K14.bookWhole_returns_written_ahead
  exact atPure_returns_fillW h hl ⟨B, hB⟩ o' S O

end AtFullSide.K12

#print axioms AtFullSide.K12.four_U
#print axioms AtFullSide.K12.four_O
#print axioms AtFullSide.K12.four_W
#print axioms AtFullSide.K12.halfU_place
#print axioms AtFullSide.K12.halfO_place
#print axioms AtFullSide.K12.halfW_place
#print axioms AtFullSide.K12.wHalf_place
#print axioms AtFullSide.K12.written_places_all
#print axioms AtFullSide.K12.makerAsks_fillW
#print axioms AtFullSide.K12.atPure_returns_fillW
#print axioms AtFullSide.K12.atPure_returns_fillW₀
