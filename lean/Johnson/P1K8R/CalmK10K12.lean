-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/CalmK10K12.lean: the closings' lot and the first chain's proximity test's lot have
no first stop (the words Calm, HalfCalm and LotCalm: Johnson/P1K8R/CalmLots.lean).

  val_zero_iff, plus_val_zero   a share has the value 0 just where its numerator is 0; so a sum
  calm_lift, calm_andThen     a lifted part; two parts as one
  lotCalm_byPub, lotCalm_byRows   a lot that depends on a reader of the index or on rows' data
  testHalf_calm                the two parts of a proximity test, for every job
  closeLotAt_calm              the closings
  proxLotAt_calm               the first chain's proximity test

Limits. A statement on the first stops and their stated shares alone. A lot may lay no half: the
statements are then idle there. Nothing is said of what a part sends or whether it plays.
-/
import Johnson.P1K8R.CalmLots
import Johnson.Desc.ProofFile.Honest.AtPureWiderK12
import Johnson.Desc.ProofFile.Honest.K10.Reads.Door

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8.K10K12
open ProofFile ProofFile.Honest

section General
variable {V V' W W' X Y : Type}

/-- A share has the value 0 just where its numerator is 0. -/
theorem val_zero_iff (o : Odds) : o.val = 0 ↔ o.num = 0 := by
  unfold Odds.val
  rw [ENNReal.div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · exact_mod_cast h
    · exact absurd h (ENNReal.natCast_ne_top _)
  · intro h
    left
    simp [h]

/-- The share that a part without a stop states has the value 0. -/
theorem zero_share_val : (⟨0, 1⟩ : Odds).val = 0 := (val_zero_iff _).2 rfl

/-- The sum of two shares of value 0 has the value 0. -/
theorem plus_val_zero {a b : Odds} (ha : a.val = 0) (hb : b.val = 0) : (a.plus b).val = 0 := by
  rw [val_zero_iff] at ha hb ⊢
  show a.num * b.den + b.num * a.den = 0
  simp [ha, hb]

/-- A lifted part is quiet if its source is. -/
theorem calm_lift (see : V → V') (wit : W → W') (get : X → Y) (set : X → Y → X)
    {p : Part V' W' Y} (h : Calm p) : Calm (p.lift see wit get set) :=
  ⟨fun l o => h.1 l o, h.2⟩

/-- Two parts as one are quiet if both are. -/
theorem calm_andThen {p q : Part V W X} (hp : Calm p) (hq : Calm q) : Calm (p.andThen q) :=
  ⟨fun l o => K10.stopBoth_of_none p.moves.length q.moves.length p.bad q.bad
    hp.1 hq.1 l o, plus_val_zero hp.2 hq.2⟩

/-- A lot that depends on a reader of the index is quiet if it is at every reader. -/
theorem lotCalm_byPub {W₀ : Type} (weights : Pub → W₀ → Weights)
    {L : (W₀ → Weights) → HLot V W X} (h : ∀ wt, LotCalm (L wt)) :
    LotCalm (HLot.byPub weights L) :=
  fun Z G x hx => h (weights Z) Z G x hx

/-- A lot that depends on the data of the main rows is quiet if it is at all data. -/
theorem lotCalm_byRows {Xi : Type} (D : Pub → Ground → RowDataOf Xi)
    {L : RowDataOf Xi → HLot V W X} (h : ∀ d, LotCalm (L d)) : LotCalm (HLot.byRows D L) :=
  fun Z G x hx => h (D Z G) Z G x hx

end General

section Closing
variable {V W X : Type}

/-- The round "BAT" of a closing is quiet. -/
theorem closeBatPart_calm : Calm (K10.closeBatPart : Part V W X) :=
  ⟨fun _ _ => rfl, zero_share_val⟩

/-- The fold of a closing is quiet, at every job. -/
theorem foldShellT_calm (tot : Bool) (J : K10.CloseJob W) (F : K10.FoldWords) :
    Calm (K10.foldShellT tot J F : Part V W X) :=
  ⟨fun _ _ => rfl, zero_share_val⟩

/-- A closing's half is quiet if its fold is. -/
theorem closeHalf_calm (fold : K10.ClosePub → Part V W X) (Z : K10.ClosePub)
    (h : Calm (fold Z)) : HalfCalm (K10.closeHalf fold Z) := by
  intro p hp
  have hp' : p ∈ [K10.closePart (fold Z)] := hp
  rw [List.mem_singleton] at hp'
  subst hp'
  exact calm_andThen closeBatPart_calm h

end Closing

section Test
variable {V W X : Type}

/-- The first part of a proximity test is quiet, at every job. -/
theorem firstPart_calm (J : K12.TestJob W X) : Calm (K12.firstPart J : Part V W X) := by
  unfold K12.firstPart
  split <;> exact ⟨fun _ _ => rfl, zero_share_val⟩

/-- The second part of a proximity test is quiet, at every job. -/
theorem restPart_calm (J : K12.TestJob W X) : Calm (K12.restPart J : Part V W X) :=
  ⟨fun _ _ => rfl, zero_share_val⟩

/-- The pair of parts of a proximity test is quiet, at every job. -/
theorem testHalf_calm (J : K12.TestJob W X) : HalfCalm (K12.proverSideOfProximityTest J : Placed V W X) := by
  intro p hp
  have hp' : p ∈ [K12.firstPart J, K12.restPart J] := hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp'
  rcases hp' with rfl | rfl
  · exact firstPart_calm J
  · exact restPart_calm J

/-- A lot of proximity tests is quiet, at every choice of jobs. -/
theorem lotOf_calm (j : Pub → Ground → Option (K12.TestJob W X)) :
    LotCalm (K12.AtProof.lotOf j : HLot V W X) := by
  intro Z G x hx
  have hx' : x ∈ (j Z G).toList.map (K12.proverSideOfProximityTest (V := V)) := hx
  obtain ⟨J, -, rfl⟩ := List.mem_map.1 hx'
  exact testHalf_calm J

end Test

section Lots
variable {W₀ X : Type}

/-- **The closings' lot is quiet.** -/
theorem closeLotAt_calm (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) :
    LotCalm (closeLotAt (X := X) I S) := by
  intro Z G x hx
  cases h : ProofFile.onlineFirstChainAt Z with
  | error e =>
    rw [closeLotAt_error I S G h] at hx
    cases hx
  | ok cF =>
    rw [closeLotAt_ok I S G h, K10.seatLotC_halves] at hx
    obtain ⟨P, -, rfl⟩ := List.mem_map.1 hx
    exact closeHalf_calm _ _ (foldShellT_calm _ _ _)

/-- The proximity test's list at this filling's letters is quiet. -/
theorem proxLotOf_calm (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) :
    LotCalm (proxLotOf (X := X) I S) :=
  lotOf_calm _

/-- **The first chain's proximity test's lot is quiet.** -/
theorem proxLotAt_calm (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) :
    LotCalm (proxLotAt (X := X) I S) := by
  intro Z G x hx
  cases h : ProofFile.onlineFirstChainAt Z with
  | error e =>
    rw [proxLotAt_error I S G h] at hx
    cases hx
  | ok cF =>
    cases hn : (cF.blocksInOrder.any (·.place == K12.AtProof.placeL) &&
        (H2U.p12OfMade Z.made).place == K12.AtProof.placeL) with
    | false =>
      rw [proxLotAt_else I S G h hn] at hx
      cases hx
    | true =>
      obtain ⟨hb, hq⟩ := Bool.and_eq_true_iff.1 hn
      rw [proxLotAt_ok I S G h hb hq] at hx
      exact proxLotOf_calm I S Z G x hx

end Lots

end P1K8.K10K12

#print axioms P1K8.K10K12.val_zero_iff
#print axioms P1K8.K10K12.zero_share_val
#print axioms P1K8.K10K12.plus_val_zero
#print axioms P1K8.K10K12.calm_lift
#print axioms P1K8.K10K12.calm_andThen
#print axioms P1K8.K10K12.lotCalm_byPub
#print axioms P1K8.K10K12.lotCalm_byRows
#print axioms P1K8.K10K12.closeBatPart_calm
#print axioms P1K8.K10K12.foldShellT_calm
#print axioms P1K8.K10K12.closeHalf_calm
#print axioms P1K8.K10K12.firstPart_calm
#print axioms P1K8.K10K12.restPart_calm
#print axioms P1K8.K10K12.testHalf_calm
#print axioms P1K8.K10K12.lotOf_calm
#print axioms P1K8.K10K12.closeLotAt_calm
#print axioms P1K8.K10K12.proxLotOf_calm
#print axioms P1K8.K10K12.proxLotAt_calm
