-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/KindPaysOnlineForms.lean: more forms beside
Honest/Law/KindPaysOnline.lean, for the kinds that call them. No statement names a kind's laws.

  `lotK1`, `lotK2`, `lotK3`, `lotK4`, `lotK6`, `lotK7`, `lotK8`, `lotK11`, `lotK13`   nine lots of
                              `fillPairs` by name; the other four are `k5LotK`, `closeLotAt`,
                              `proxLotAt` and `wLotAt`
  `onlyK2` and the like    each pair among the first ten is the only one of its kind, in the form
                              `M = L`. K5's is `k5_pair_only` (K5/Law/FindAtBase.lean); K10's and
                              K12's are `close_pair_only`, `prox_pair_only`; K1 has two lots:
                              `k1_pairs` (these three: Honest/Law/FillPairs.lean)
  `kindPays_online_of_base_lot`   **the form for one lot, paid at the base filling's own sides**,
                              with the premise on pairs in the form `M = L`: no equation is asked
  `online_base_return`        a return at the online filling gives a return at the base filling,
                              with the same public part, ground, description and book
  `kindPays_online_shared`, `kindPays_online_second`   the online forms for the other two chains,
                              paid at the base filling's own sides
  `public_part_at_head`       under the head, the return's public part is the head's: the lists
                              below speak at the head's, the forms above at the return's
  `online_shared_list`, `online_second_list`   under the head: what the base filling's shared and
                              second lists are
  `online_shared_K14`, `online_shared_K1`, `online_shared_K12`   under the head: a shared side of
                              one of these kinds lies in that kind's own list
  `kindPays_online_shared_all`, `kindPays_online_second_all`   the kinds with sides there paid, all
                              sixteen pay at that chain
  `online_returns_at_head`, `description_at_return_at_head`   under the head, the two returns that
                              `onlineProver` matches on, and the description beside them

«The head» is `P5J.AtMgA`, the structure that says what the public files make.

Limits.
  * What is paid is that `chainSteps` returns at the members. Nothing here says that a part plays, or
    that a verifier accepts.
  * Every form on payment is conditional on a return of the maker (hA).
  * The statements under the head stand at the full size and the format's second hash function alone.
  * The list bs of members is an argument: a call at a list other than the description's says nothing
    of `ready`.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.KindPaysOnline

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

/-! ## 1 Nine of the thirteen lots, by name -/

namespace ProofFile.Honest
open VerifiableInference.Desc (KindName)

section
variable {W₀ : Type} (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)

/-- K1's own lot. -/
abbrev lotK1 := HLot.byPub I.weights (LongLots.plain (X := Unit) o S O).k1

/-- K2's lot. -/
abbrev lotK2 : HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit :=
  HLot.byPub I.weights fun wt => HLot.byRows (widerRows S) fun D =>
    K2.switchLot D fun w : Local W₀ IndexCommitterCoins Inst Cells => ⟨w.trace, wt w.w₀, w.rc⟩

/-- K7's lot. -/
abbrev lotK7 : HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit := replyLot

/-- K11's lot. -/
abbrev lotK11 := HLot.byPub I.weights (LongLots.plain (X := Unit) o S O).k11

/-- K13's lot. -/
abbrev lotK13 := HLot.byPub I.weights (LongLots.plain (X := Unit) o S O).k13

/-- K3's lot. -/
abbrev lotK3 := HLot.byPub I.weights (LongLots.plain (X := Unit) o S O).k3

/-- K4's lot. -/
abbrev lotK4 : HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit :=
  HLot.byPub I.weights fun wt => K4.k4HLot id wt fun _ _ => K4.k4LookAt

/-- K6's lot. -/
abbrev lotK6 := HLot.byPub I.weights (LongLots.plain (X := Unit) o S O).k6

/-- K8's lot. -/
abbrev lotK8 : HLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit :=
  K8.smallLot id fun _ G _ l => K3.matsOwn G.W l

/-- K2's pair is the only one of its kind. -/
theorem onlyK2 : ∀ M, (M, KindName.K2) ∈ fillPairs I o S O → M = lotK2 I S :=
  pair_only I o S O (by simp [widerPairs]) (by decide)

/-- K7's pair is the only one of its kind. -/
theorem onlyK7 : ∀ M, (M, KindName.K7) ∈ fillPairs I o S O → M = lotK7 :=
  pair_only I o S O (by simp [widerPairs]) (by decide)

/-- K11's pair is the only one of its kind. -/
theorem onlyK11 : ∀ M, (M, KindName.K11) ∈ fillPairs I o S O → M = lotK11 I o S O :=
  pair_only I o S O (by simp [widerPairs]) (by decide)

/-- K13's pair is the only one of its kind. -/
theorem onlyK13 : ∀ M, (M, KindName.K13) ∈ fillPairs I o S O → M = lotK13 I o S O :=
  pair_only I o S O (by simp [widerPairs]) (by decide)

/-- K3's pair is the only one of its kind. -/
theorem onlyK3 : ∀ M, (M, KindName.K3) ∈ fillPairs I o S O → M = lotK3 I o S O :=
  pair_only I o S O (by simp [widerPairs]) (by decide)

/-- K4's pair is the only one of its kind. -/
theorem onlyK4 : ∀ M, (M, KindName.K4) ∈ fillPairs I o S O → M = lotK4 I :=
  pair_only I o S O (by simp [widerPairs]) (by decide)

/-- K6's pair is the only one of its kind. -/
theorem onlyK6 : ∀ M, (M, KindName.K6) ∈ fillPairs I o S O → M = lotK6 I o S O :=
  pair_only I o S O (by simp [widerPairs]) (by decide)

/-- K8's pair is the only one of its kind. -/
theorem onlyK8 : ∀ M, (M, KindName.K8) ∈ fillPairs I o S O → M = lotK8 :=
  pair_only I o S O (by simp [widerPairs]) (by decide)

end

end ProofFile.Honest

/-! ## 2 The online forms -/

namespace ProofFile.Honest.Term
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open VerifiableInference.Desc (Block KindName)

section
variable {files : VerifierAndGoals.PublicFiles} {returned : OnlineReturn files} {S Cl : Type}
  {bs : List (Block S Cl)} {κ : KindName}
  {L : HLot (Local FullSizeMatrix IndexCommitterCoins Inst Cells) (Local FullSizeMatrix IndexCommitterCoins Inst Cells) Unit}

/-- **The form for one lot, paid at the base filling's own sides.** hpay: each side of the lot pays at
the return's book. hu: the lot's pair is the only one of its kind. No equation on a lot read through
is asked. -/
theorem kindPays_online_of_base_lot (hA : onlineMaker files = .ok returned)
    (hpay : ∀ x ∈ L.halves returned.Z returned.G, SidePays returned.B 0 bs x)
    (hu : ∀ M, (M, κ) ∈ onlinePairs → M = L) :
    KindPays returned.B 0 bs returned.H.first κ :=
  kindPays_online_of_sides hA fun M hM x hx => by
    obtain rfl := hu M hM
    exact sidePays_thru _ _ (hpay x hx)

/-- **A return at the online filling gives a return at the base filling**, with the same public part,
ground, description and book. -/
theorem online_base_return (hA : onlineMaker files = .ok returned) :
    ∃ A₀ : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit,
      onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL onlineBase = .ok A₀ ∧
        A₀.Z = returned.Z ∧ A₀.G = returned.G ∧ A₀.F = returned.F ∧ A₀.B = returned.B :=
  atPure_base_of_through id (tableCoins files) matrixInput.dummy hA (K5.parts_of_atPure hA).2.range

/-- **The online form at the shared chain, paid at the base filling's own sides.** -/
theorem kindPays_online_shared (hA : onlineMaker files = .ok returned)
    (H : ∀ x ∈ onlineBase.shared returned.Z returned.G, x.place.kind = κ →
      SidePays returned.B 1 bs x) :
    KindPays returned.B 1 bs returned.H.shared κ :=
  kindPays_shared_of_base_sides id (tableCoins files) matrixInput.dummy hA H

/-- **The online form at the second chain, paid at the base filling's own sides.** -/
theorem kindPays_online_second (hA : onlineMaker files = .ok returned)
    (H : ∀ x ∈ onlineBase.second returned.Z returned.G, x.place.kind = κ →
      SidePays returned.B 2 bs x) :
    KindPays returned.B 2 bs returned.H.second κ :=
  kindPays_second_of_base_sides id (tableCoins files) matrixInput.dummy hA H

/-- **All sixteen pay at the second chain, where K12 pays.** Conditional on a return of the maker and
on K12's payment. -/
theorem kindPays_online_second_all (hA : onlineMaker files = .ok returned)
    (H : KindPays returned.B 2 bs returned.H.second .K12) :
    ∀ k, KindPays returned.B 2 bs returned.H.second k := by
  intro k
  by_cases e : k = .K12
  · rw [e]
    exact H
  · exact kindPays_online_second_none hA e

end

section
variable {W₀ Rc Ky X : Type}

/-- Each side of `K14.proverSidesOfSharedRounds` stands at a place of the kind K14. -/
theorem halves_kind (d : K14.Data) (weights : W₀ → Weights) :
    ∀ x ∈ (K14.proverSidesOfSharedRounds d weights : List (Placed Empty (Common W₀ Rc Ky) X)),
      x.place.kind = .K14 := by
  intro x hx
  unfold K14.proverSidesOfSharedRounds at hx
  rcases List.mem_append.1 hx with h | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> rfl
  · split at h
    · obtain rfl := List.mem_singleton.1 h
      rfl
    · cases h

/-- Each side of `K14.proverSidesOfSharedSendings` stands at a place of the kind K1. -/
theorem sendHalves_kind (A : K14.SendPub) (weights : W₀ → Weights) (rand : Rc → TableRand) :
    ∀ x ∈ (K14.proverSidesOfSharedSendings A weights rand : List (Placed Empty (Common W₀ Rc Ky) X)),
      x.place.kind = .K1 := by
  intro x hx
  unfold K14.proverSidesOfSharedSendings at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl <;> rfl

end

section
variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place} {S Cl : Type} {bs : List (Block S Cl)}

/-- **The two returns on which `onlineProver` matches, under the head.** -/
theorem online_returns_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    {returned : OnlineReturn Z} (hA : onlineMaker Z = .ok returned) :
    H2U.placesOfMade returned.Z.made = .ok Np ∧ ProofFile.onlineFirstChainAt returned.Z = .ok cF := by
  obtain ⟨eZ, -⟩ := atPure_at_laid h.laid hA
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact ⟨atPure_places h.laid hA, eZ ▸ ToldDesc.pureChainAt_of_open O⟩

/-- **Under the head, the description at a return**: the two returns on which `onlineProver` matches,
and that the description which the maker returned is the one at these. -/
theorem description_at_return_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    {returned : OnlineReturn Z} (hA : onlineMaker Z = .ok returned) :
    H2U.placesOfMade returned.Z.made = .ok Np ∧ ProofFile.onlineFirstChainAt returned.Z = .ok cF ∧
      returned.F = descZ returned.Z Np cF := by
  obtain ⟨hP, hC⟩ := online_returns_at_head h hA
  obtain ⟨e1, e2⟩ := online_desc_at_head h hA hP hC
  exact ⟨hP, hC, e2.trans e1.symm⟩

/-- **Under the head, the return's public part is the head's.** -/
theorem public_part_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    {returned : OnlineReturn Z} (hA : onlineMaker Z = .ok returned) : returned.Z = Zp :=
  (atPure_at_laid h.laid hA).1

/-- **What the base filling's shared list is, under the head**: four lists in a row: the sides of kind
K14, the two senders of kind K1, the sides of the test on U, those of the test on Omega. -/
theorem online_shared_list (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) (G : Ground) :
    onlineBase.shared Zp G =
      ((K14.proverSidesOfSharedRounds { S := (VerifiableInference.Desc.K1.qAt Zp Np).S, atPoint := 0, atZeta := 6 }
            (matrixInput.weights Zp) ++
          K14.proverSidesOfSharedSendings { P := VerifiableInference.Desc.K1.qAt Zp Np, atPoint := 0 }
            (matrixInput.weights Zp) (K14.randNow (VerifiableInference.Desc.K1.qAt Zp Np))) ++
        K12.AtProof.halfU (matrixInput.weights Zp)
          (fun w => Bind.ForProver.encW Zp (matrixInput.weights Zp w)) Zp) ++
      K12.AtProof.halfO (matrixInput.weights Zp) Zp := by
  have h6 := K14.nowSharedBy_at_head h (matrixInput.weights Zp)
  show K12.AtProof.sharedWithUO matrixInput Zp = _
  rw [K12.AtProof.sharedWithUO_ok matrixInput h6, sharedWithU_ok matrixInput h6]

/-- **What the base filling's second list is, under the head**: the sides of the last chain's test. -/
theorem online_second_list (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) (G : Ground) :
    onlineBase.second Zp G =
      K12.AtProof.halfW OnBytes.HonestTrace.Sz.ref (P5J.F0T OnBytes.secondHashFunction Zp Np cF)
        VerifiableInference.Desc.K12.Seat.enterOwn openHonest.pile (K1.lotNo OnBytes.secondHashFunction Zp)
        (fun w => ⟨w.trace, matrixInput.weights Zp w.w₀, w.rc⟩)
        (fun w => matrixInput.weights Zp w.w₀) (fun P w => K12.AtProof.randAt P w.rc) Zp G := by
  have h6 := K14.nowSharedBy_at_head h (matrixInput.weights Zp)
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact secondW_ok matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest G h6
    h.laid.places (ToldDesc.pureChainAt_of_open O)

/-- **A shared side of kind K14 lies in that kind's own list.** Under the head. -/
theorem online_shared_K14 (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) (G : Ground) :
    ∀ x ∈ onlineBase.shared Zp G, x.place.kind = .K14 →
      x ∈ K14.proverSidesOfSharedRounds { S := (VerifiableInference.Desc.K1.qAt Zp Np).S, atPoint := 0, atZeta := 6 }
        (matrixInput.weights Zp) := by
  intro x hx hk
  rw [online_shared_list h] at hx
  simp only [List.mem_append] at hx
  rcases hx with ((ha | hb) | hc) | hd
  · exact ha
  · exact absurd ((sendHalves_kind _ _ _ x hb).symm.trans hk) (by decide)
  · rw [AtFullSide.K12.halfU_place _ _ Zp x hc] at hk
    exact absurd hk (by decide)
  · rw [AtFullSide.K12.halfO_place _ Zp x hd] at hk
    exact absurd hk (by decide)

/-- **A shared side of kind K1 lies in that kind's own list there.** Under the head. -/
theorem online_shared_K1 (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) (G : Ground) :
    ∀ x ∈ onlineBase.shared Zp G, x.place.kind = .K1 →
      x ∈ K14.proverSidesOfSharedSendings { P := VerifiableInference.Desc.K1.qAt Zp Np, atPoint := 0 }
        (matrixInput.weights Zp) (K14.randNow (VerifiableInference.Desc.K1.qAt Zp Np)) := by
  intro x hx hk
  rw [online_shared_list h] at hx
  simp only [List.mem_append] at hx
  rcases hx with ((ha | hb) | hc) | hd
  · exact absurd ((halves_kind _ _ x ha).symm.trans hk) (by decide)
  · exact hb
  · rw [AtFullSide.K12.halfU_place _ _ Zp x hc] at hk
    exact absurd hk (by decide)
  · rw [AtFullSide.K12.halfO_place _ Zp x hd] at hk
    exact absurd hk (by decide)

/-- **A shared side of kind K12 lies in one of the two tests' lists.** Under the head. -/
theorem online_shared_K12 (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) (G : Ground) :
    ∀ x ∈ onlineBase.shared Zp G, x.place.kind = .K12 →
      x ∈ K12.AtProof.halfU (matrixInput.weights Zp)
          (fun w => Bind.ForProver.encW Zp (matrixInput.weights Zp w)) Zp ∨
        x ∈ K12.AtProof.halfO (matrixInput.weights Zp) Zp := by
  intro x hx hk
  rw [online_shared_list h] at hx
  simp only [List.mem_append] at hx
  rcases hx with ((ha | hb) | hc) | hd
  · exact absurd ((halves_kind _ _ x ha).symm.trans hk) (by decide)
  · exact absurd ((sendHalves_kind _ _ _ x hb).symm.trans hk) (by decide)
  · exact Or.inl hc
  · exact Or.inr hd

/-- **All sixteen pay at the shared chain, where K14, K1 and K12 pay.** Conditional on the head, on a
return of the maker and on the three kinds' payments. -/
theorem kindPays_online_shared_all (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    {returned : OnlineReturn Z} (hA : onlineMaker Z = .ok returned)
    (H : ∀ k, k = .K14 ∨ k = .K1 ∨ k = .K12 → KindPays returned.B 1 bs returned.H.shared k) :
    ∀ k, KindPays returned.B 1 bs returned.H.shared k := by
  intro k
  by_cases e : k = .K14 ∨ k = .K1 ∨ k = .K12
  · exact H k e
  · exact kindPays_online_shared_none h hA
      ⟨fun q => e (Or.inl q), fun q => e (Or.inr (Or.inl q)), fun q => e (Or.inr (Or.inr q))⟩

end

end ProofFile.Honest.Term

#print axioms ProofFile.Honest.onlyK2
#print axioms ProofFile.Honest.onlyK7
#print axioms ProofFile.Honest.onlyK11
#print axioms ProofFile.Honest.onlyK13
#print axioms ProofFile.Honest.onlyK3
#print axioms ProofFile.Honest.onlyK4
#print axioms ProofFile.Honest.onlyK6
#print axioms ProofFile.Honest.onlyK8
#print axioms ProofFile.Honest.Term.kindPays_online_of_base_lot
#print axioms ProofFile.Honest.Term.online_base_return
#print axioms ProofFile.Honest.Term.kindPays_online_shared
#print axioms ProofFile.Honest.Term.kindPays_online_second
#print axioms ProofFile.Honest.Term.kindPays_online_second_all
#print axioms ProofFile.Honest.Term.online_returns_at_head
#print axioms ProofFile.Honest.Term.halves_kind
#print axioms ProofFile.Honest.Term.sendHalves_kind
#print axioms ProofFile.Honest.Term.description_at_return_at_head
#print axioms ProofFile.Honest.Term.public_part_at_head
#print axioms ProofFile.Honest.Term.online_shared_K14
#print axioms ProofFile.Honest.Term.online_shared_K1
#print axioms ProofFile.Honest.Term.online_shared_K12
#print axioms ProofFile.Honest.Term.online_shared_list
#print axioms ProofFile.Honest.Term.online_second_list
#print axioms ProofFile.Honest.Term.kindPays_online_shared_all
