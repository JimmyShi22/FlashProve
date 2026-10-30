-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K11/AtTheTerm.lean: the proofs of K11Five (E2E/K11AtTheTerm.lean), with what they share
with the kind's other statements. It lies in the side library because the book's written entries do.

  k11_hex, k11_ho          the filling's lots hold the kind's halves, and no other lot stands at the
                           kind
  k11_found                at the maker's return, the search at the kind's place finds the kind's
                           side, under the library's head
  k11_rides                the written clauses at border 347, from those at 346 and the merge's clause
  k11_behind               BehindS at 346, with the thread's letter f read at the step
  k11Five                  the five debts
  places_nodup, k11_owns_no_spent_run, k11_unspent   two premises of the simulator's law

Limits. Those of the statements: nothing here says that the thread's sentence holds at any state.
-/
import E2E.K11AtTheTerm
import AtFullSide.K14.MakersBookOne
import AtFullSide.K14.RawEntriesKit
import Johnson.Desc.ProofFile.Honest.K11.Plays.ExchangeByKind
import Johnson.Desc.ProofFile.Honest.K11.Plays.HalfAtAnyFill
import Johnson.Desc.ProofFile.Honest.K11.Plays.FiveAtHead
import Johnson.Desc.ProofFile.Honest.K11.Plays.ClaimsNIs
import Johnson.Desc.ProofFile.Honest.K11.Plays.SeatAtFull
import Johnson.Desc.ProofFile.Honest.K11.Plays.FormsRide
import Johnson.Desc.ProofFile.Honest.K11.Plays.ExchangeWhole
import Johnson.Desc.ProofFile.Honest.K11.Plays.RidesWhole
import Johnson.Desc.ProofFile.Honest.Thread.K11RowPile
import Johnson.Desc.ProofFile.Honest.Thread.K11FormBehind
import Johnson.Desc.ProofFile.Honest.Thread.HeadFacts
import Johnson.Desc.ProofFile.Honest.Thread.FirstFillAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K11
open VerifiableInference.Desc (Chain Place KindName)
open VerifiableInference.Desc.First (Item Here)
open OnBytes.Maker (WholeD)
open OnBytes.Model (WsClaim)
open OnBytes.HonestTrace (Sz)
open P5J (AtMgA TS)
open ProofFile (SecondHashFunctionArgument Pub Ground Inst)
open ProofFile.Honest
open ProofFile.Honest.K11
open ProofFile.Honest.FirstThread
open AtPublicFiles.AtFiles.HonestTerm.K11Term
open Johnson.Desc.First.ForkMerge (HeadMergeP)
open Johnson.Desc.First.ForkMerge.Exchange (headMergeAtFull placeOfLot)
open Johnson.Desc.First.ForkMerge.Returns (K11KeepsYes)

section Lots
variable {W₀ : Type} (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : Sz) (O : OnlineProverArguments) (Zq : Pub) (G : Ground)

/-- The kind's lot is one of the filling's lots. -/
theorem k11_mem_wM :
    (HLot.byPub I.weights (LongLots.plain o S O).k11 :
        HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit) ∈
      (onlineProverPartsInUse I o S O).lots := by
  rw [widerFillAtCPUOWM_lots, widerFillAt_lots]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_map.2 ⟨_, .tail _ (.tail _ (.tail _ (.head _))), rfl⟩)))

/-- **Some lot of the filling has the kind's halves.** -/
theorem k11_hex :
    ∃ M ∈ (onlineProverPartsInUse I o S O).lots, M.halves Zq G =
      (headMergeLot O.claims (I.weights Zq)).halves Zq G :=
  ⟨_, k11_mem_wM I o S O, rfl⟩

/-- Every half of W's lot stands at a place of the kind K1. -/
theorem wLot_kind :
    ∀ y ∈ (wLotAt (X := Unit) I o O).halves Zq G, y.place.kind = KindName.K1 := by
  intro y hy
  rw [wLotAt_halves] at hy
  cases hm : OnBytes.linMessageW Zq.first.lin with
  | none =>
    rw [hm] at hy
    cases hy
  | some msg =>
    rw [hm] at hy
    obtain rfl := List.mem_singleton.1 hy
    rfl

/-- **Every lot of the filling has no half at a place of the kind, or the kind's halves.** -/
theorem k11_ho :
    ∀ M ∈ (onlineProverPartsInUse I o S O).lots,
      (∀ x ∈ M.halves Zq G, x.place.kind ≠ KindName.K11) ∨
        M.halves Zq G = (headMergeLot O.claims (I.weights Zq)).halves Zq G := by
  intro M hM
  have away : ∀ k : KindName, k ≠ KindName.K11 → (∀ y ∈ M.halves Zq G, y.place.kind = k) →
      ∀ x ∈ M.halves Zq G, x.place.kind ≠ KindName.K11 :=
    fun k hk hy x hx e => hk ((hy x hx).symm.trans e)
  rw [widerFillAtCPUOWM_lots] at hM
  simp only [List.mem_append, List.mem_singleton] at hM
  rcases hM with ((h | rfl) | rfl) | rfl
  · rw [widerFillAt_lots] at h
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 h
    by_cases k : q.2 = KindName.K11
    · have e' : q = (HLot.byPub I.weights (LongLots.plain o S O).k11, KindName.K11) :=
        List.inj_on_of_nodup_map widerPairs_nodup hq
          (.tail _ (.tail _ (.tail _ (.head _)))) k
      rw [e']
      exact .inr rfl
    · exact .inl (fun x hx e => k (((FirstFill.widerKinds I o S O Zq G).all q hq x hx).symm.trans e))
  · exact .inl (away KindName.K10 (by decide) (closeLotAt_kinds I S Zq G))
  · exact .inl (away KindName.K12 (by decide) (proxLotAt_kinds I S Zq G))
  · exact .inl (away KindName.K1 (by decide) (wLot_kind I o O Zq G))

end Lots

variable {W₀ : Type} {I : WiderIn W₀} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **At the maker's return, the search at the kind's place finds the kind's side.** -/
theorem k11_found (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} (hM : baseMaker I Z = .ok A) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    (A.H.first.find? fun g => g.place == IM.k11Place) =
      some (headMergeHalf (headClaimsByPlace Zp Bs.G₀) (I.weights Zp)
        (_root_.K11.parOf Zp Bs.G₀)) := by
  obtain ⟨e1, -⟩ := atPure_ok hM
  have eZ : A.Z = Zp := Except.ok.inj (e1.symm.trans h.laid.pub)
  subst eZ
  exact (halfAtAnyFillHead Z D r _ Np cF x h _ _ _ _ _ _ A Bs headClaimsByPlace
    (I.weights A.Z) hB hM (k11_hex I OnBytes.secondHashFunction Sz.ref openHonest A.Z A.G)
    (k11_ho I OnBytes.secondHashFunction Sz.ref openHonest A.Z A.G)).2.2

/-- **The written clauses at border 347**, from those at 346 and the merge's clause. st: stays past
the merge by hst. -/
theorem k11_rides {V : Type} {ν : Nat} {st : Nat → TS → Prop}
    {R : Nat → Option OnBytes.Model.Forest.Heard → Prop} {P : HeadMergeP} {s s' : TS} {v : V}
    (hst : st 24 s → st 24 s') (hK : K11KeepsYes P s s')
    (hr : ridersOf (csHead ν st R) 346 v s) : ridersOf (csHead ν st R) 347 v s' := by
  obtain ⟨⟨⟨a, wo, vv, β, ha, -, -, -, -, -, rfl⟩, -⟩, -⟩ := hK
  intro c hc hlo hhi
  rcases (csHead_mem ν st R c).1 hc with
    ((((rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨l, hl, rfl⟩) | ⟨g, hg, rfl⟩) | ⟨g, hg, rfl⟩)
  · obtain ⟨a', ha', hx⟩ := hr _ hc (by show 342 ≤ 346; omega) (by show 346 ≤ 347; omega)
    obtain rfl : a' = a := Here.head.inj (ha'.symm.trans ha)
    exact ⟨_, rfl, hx⟩
  · obtain ⟨a', ha', hx⟩ := hr _ hc (by show 343 ≤ 346; omega) (by show 346 ≤ 348; omega)
    obtain rfl : a' = a := Here.head.inj (ha'.symm.trans ha)
    exact ⟨_, rfl, hx⟩
  · exact ⟨_, rfl, rfl⟩
  · exact absurd hhi (by show ¬ 347 ≤ 346; omega)
  · exact absurd hhi (by show ¬ 347 ≤ 345; omega)
  · obtain ⟨a', ha', hx⟩ := hr _ hc (by show 346 ≤ 346; omega) (by show 346 ≤ 347; omega)
    obtain rfl : a' = a := Here.head.inj (ha'.symm.trans ha)
    exact ⟨_, rfl, hx⟩
  · exact hst (hr _ hc (by show 346 ≤ 346; omega) (by show 346 ≤ 347; omega))
  · exact absurd hhi (by show ¬ 347 ≤ 14 * l + 9; omega)
  · exact absurd hhi (by show ¬ 347 ≤ 14 * (2 * g + 1) + 9; omega)
  · exact absurd hhi (by show ¬ 347 ≤ 28 * g + 10; omega)

/-- The merge's place at the full size is the written one. -/
theorem ps_k11 : P5J.At.ps[346]? = some IM.k11Place := FirstFill.ps_346

/-- **The five debts at every member of the kind.** -/
theorem k11Five : K11Five := by
  intro W₀ I Z D r Zp Np cF x A Bs hM hB h Q test carryX item n₁ n₂ Vd ν st R f w Said c₀ hS hSc
    hC hf₁ hf₂ hst r2 r3 b q hb hq
  obtain rfl := k11_number hb hq
  have hf := k11_found h hM hB
  rw [headClaimsByPlace_at_head Z D r Zp Np cF x Bs h hB] at hf
  obtain ⟨Bs', _, name, hB', _, _, _, _, hfl, _⟩ := headMergeAtFull Z D r Zp Np cF x h
  obtain rfl : Bs' = Bs := Except.ok.inj (hB'.symm.trans hB)
  have hk : ∀ s s', (baseThread h A Q test carryX item n₁ n₂ Vd ν st R f w).keeps 346 s s' →
      K11KeepsYes (_root_.K11.parOf Zp Bs'.G₀) s s' := fun s s' hK =>
    hf₁ s s' ((head_keeps h A.H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy f) w ps_k11 s s').1 hK)
  have hk' : ∀ s s', (baseThread h A Q test carryX item n₁ n₂ Vd ν st R f w).keeps 346 s s' →
      Johnson.Desc.First.ForkMerge.Returns.K11Keeps (_root_.K11.parOf Zp Bs'.G₀) s s' :=
    fun s s' hK => (hk s s' hK).1
  have hBe : BehindS (baseThread h A Q test carryX item n₁ n₂ Vd ν st R f w) Said 346 := by
    intro blk hblk k s m E ds y cols s' hT _ hSt
    have hK := keepsYes_of_stepped A.B _ _ Unit _
      (baseThread h A Q test carryX item n₁ n₂ Vd ν st R f w) 346 (_root_.K11.parOf Zp Bs'.G₀) name
      IM.k11Place hfl blk k s m E ds y cols s' hblk hSt
    have hF := k11_form_behind h A.H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy f) w hblk
      ⟨hT.1, hS _ _ _ hT.2⟩ hSt
    have hT' := hT.1
    unfold Thr at hT'
    obtain ⟨-, -, -, -, -, hr, -⟩ := hT'
    have h1 : s.out.reply = some m.st.input.x.asked := hr.1 (by omega)
    obtain ⟨⟨l, -, hy⟩, -⟩ := hSt.1
    have h2 : y.2.st.input = m.st.input := (play_mid l ds [] m y hy).1
    refine ⟨⟨hF.1, hF.2⟩, ⟨fun _ => ?_, ?_⟩, ?_⟩
    · obtain ⟨⟨⟨a, wo, v, β, -, -, -, -, -, -, rfl⟩, -⟩, -⟩ := hK
      rw [h2]
      exact h1
    · rw [h2]
      exact k11_rides (hst s s' hK) hK hr.2
    · exact (head_keeps h A.H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy f) w ps_k11 s s').2
        (hf₂ blk k s m E ds y cols s' hT hSt hblk hK)
  have hPl := (plays_at_head Z D r Zp Np cF x h A.B _ _ _ _ _ _ A.H Q test carryX item n₁ n₂ 339 Vd
    (ridersOf (csHead ν st R)) (kpBy f) w Bs' _ (I.weights Zp) hB hf).2 Said
  have hAc := acceptedS_at_head Z D r Zp Np cF x h A.B _ _ _ _ _ _ A.H Q test carryX item n₁ n₂ 339
    Vd (ridersOf (csHead ν st R)) (kpBy f) w Bs' _ (I.weights Zp) hB hf
  obtain ⟨e1, e2⟩ := exchange_at_head Z D r Zp Np cF x h A.B _ _ _ _ _ _ A.H Q test carryX item n₁
    n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy f) w Bs' (I.weights Zp) c₀ hB (by omega) hf hSc hC
  obtain ⟨p1, p2⟩ := k11_pins_again h A.H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy f) w
    (_root_.K11.parOf Zp Bs'.G₀) hk' Said hBe
  have hEx := exchangeS_of_five Z D r Zp Np cF x h A.B _ _ _ _ _ _ A.H Q test carryX item n₁ n₂ 339
    Vd (ridersOf (csHead ν st R)) (kpBy f) w Said
    (fun blk hblk k s m E ds y cols s' hA => e1 blk hblk k s m E ds y cols s' ⟨hA.1, hS _ _ _ hA.2⟩)
    (fun blk hblk k s m E ds y cols s' hA => e2 blk hblk k s m E ds y cols s' ⟨hA.1, hS _ _ _ hA.2⟩)
    (exchangeAtS_of _ Said (exchangeAt_pinW h A.H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy f) w 346))
    (p1 24 0 pinsOpen_at_346.1) (p2 pinsOpen_at_346.2)
  obtain ⟨q1, _, q3⟩ := k11_rides_pins h A.H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy f) w
    (_root_.K11.parOf Zp Bs'.G₀) hk'
  have qr := k11RowsRide Z D r Zp Np cF x h A.B _ _ _ _ _ _ A.H Q test carryX item n₁ n₂ 339 Vd
    (ridersOf (csHead ν st R)) (kpBy f) w (_root_.K11.parOf Zp Bs'.G₀) hk'
  have qf := sixFormsRide_at_head Z D r Zp Np cF x h A.B _ _ _ _ _ _ A.H Q test carryX item n₁ n₂
    339 Vd (ridersOf (csHead ν st R)) (kpBy f) w Bs' hB hk
  have hRi : RidesPastS (baseThread h A Q test carryX item n₁ n₂ Vd ν st R f w) Said 346 := by
    refine ridesPastS_shares _ Said fun i hi h1 h2 => ?_
    have hm := across_at_346 i hi h1 h2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    have down : ∀ {i}, RidesPastAtS (baseThread h A Q test carryX item n₁ n₂ Vd ν st R f w) SaidOk
        346 i → RidesPastAtS (baseThread h A Q test carryX item n₁ n₂ Vd ν st R f w) Said 346 i :=
      fun e k s m E s' ps v hA => e k s m E s' ps v ⟨hA.1, hS _ _ _ hA.2⟩
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    · exact ridesPastAtS_of _ Said q3
    · exact ridesPastAtS_of _ Said (q1 24 1)
    · exact ridesPastAtS_of _ Said (q1 24 2)
    · exact ridesPastAtS_of _ Said (qr 24 .carried)
    · exact ridesPastAtS_of _ Said (qr 24 (.sample 0))
    · exact ridesPastAtS_of _ Said (qr 24 (.sample 1))
    · exact ridesPastAtS_of _ Said (qr 24 (.sample 2))
    · exact ridesPastAtS_of _ Said (qr 24 .position)
    · exact down (qf (3, "objects") (by decide))
    · exact down (qf (3, "planes") (by decide))
    · exact down (qf (4, "join") (by decide))
    · exact down (qf (4, "own") (by decide))
    · exact down (qf (6, "small") (by decide))
    · exact down (qf (8, "objects") (by decide))
    · exact ridesPastAtS_of _ Said
        (k11_rides_pile h A.H Q test carryX item n₁ n₂ 339 Vd (ridersOf (csHead ν st R)) (kpBy f) w _ hk')
    · exact r2
    · exact r3
  exact ⟨hPl,
    fun fall blk hblk k s m E ds y cols hA =>
      hAc fall blk hblk k s m E ds y cols ⟨hA.1, hS _ _ _ hA.2⟩,
    hBe, hEx, hRi⟩

theorem k11Found : K11Found :=
  fun _ _ _ _ _ _ _ _ _ _ _ hM h hB => k11_found h hM hB

/-- The first chain's places stand apart, under the head. -/
theorem places_nodup (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    (cF.blocksInOrder.map (·.place)).Nodup := by
  have hpl := P5J.At.places_paid h.scope h.reads h.laid
  show (VerifiableInference.Desc.First.blockPlaces cF.blocksInOrder).Nodup
  rw [hpl]
  exact ProofFile.Law.flatPlaces_nodup P5J.fullLinks true

/-- The kind's place at the full size. -/
def k11At : Place := ⟨1, some 24, 9, KindName.K11⟩

/-- The test: an entry does not spend a run whose owner stands at the kind's place. -/
def ownsNoSpent (a : Ahead) : Bool := !(a.once && a.owner.place == k11At)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **No entry of the written book that spends names an owner at the kind's place.** -/
theorem k11_owns_no_spent_run : AtFullSide.K14.rawAheadW.all ownsNoSpent = true := by
  refine AtFullSide.K14.rawAll_whole ownsNoSpent (by decide +kernel) ?_ (by decide +kernel)
  unfold AtFullSide.K14.rawSegW segmentCarries linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

/-- No entry of the return's book lets a part spend a coin of a part of this row. -/
theorem k11_unspent (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} (hM : baseMaker I Z = .ok A) {P : HeadMergeP}
    (hp : headMergePlace P = k11At) (j : Nat) (q : Addr) :
    A.B.spentBy ⟨headMergePlace P, j⟩ q = [] := by
  have eA := (AtFullSide.K14.makers_ahead_at_atPure h hM).1
  unfold ProverCoinCounts.spentBy
  rw [List.filter_eq_nil_iff]
  intro e he hb
  simp only [Bool.and_eq_true, beq_iff_eq] at hb
  obtain ⟨⟨ho, -⟩, hon⟩ := hb
  have ht : ownsNoSpent e = true := List.all_eq_true.1 k11_owns_no_spent_run e (eA ▸ he)
  have hpl : e.owner.place = k11At := by
    rw [ho]
    exact hp
  simp [ownsNoSpent, hon, hpl] at ht

end AtFullSide.K11

#print axioms AtFullSide.K11.k11_hex
#print axioms AtFullSide.K11.k11_ho
#print axioms AtFullSide.K11.k11_found
#print axioms AtFullSide.K11.k11_rides
#print axioms AtFullSide.K11.k11Five
#print axioms AtFullSide.K11.places_nodup
#print axioms AtFullSide.K11.k11_owns_no_spent_run
#print axioms AtFullSide.K11.k11_unspent
