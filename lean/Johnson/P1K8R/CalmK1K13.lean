-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/CalmK1K13.lean: the five lots K1, K2, K7, K11 and K13 of the first chain are quiet.
Words: Johnson/P1K8R/CalmLots.lean.

  Calm.lift, Calm.andThen     a lifted part, and two parts as one, are quiet if their sources are
  LotCalm.byPub, .byRows       the two forms of a lot keep LotCalm
  calmPart_calm, sumPart_calm, sendPart_calm, switchPart_calm   the parts that these lots use
  dataSideNo_calm, switchLot_calm, headMergeLot_calm, k13Lot_calm, wSide_calm   the lots,
      general in their letters
  k1_calm, k2_calm, k7_calm, k11_calm, k13_calm   the lots as the filling has them
  wider_five_calm   the filling's first five lots, read off the filling itself

Limits. A lot with no half is quiet: nothing here says that any half stands. Nothing is said of a
run or of any property of a prover.
-/
import Johnson.P1K8R.CalmLots
import Johnson.Desc.ProofFile.Honest.AtPureWiderAt
import Johnson.Desc.ProofFile.Honest.K1.PlaceW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open ProofFile ProofFile.Honest
open VerifiableInference.Desc (Place)

variable {V W X Xi W₀ Rc Tr : Type}

/-! ## General lemmas -/

/-- A stated share has the value 0 just where its numerator is 0. -/
theorem odds_val_zero (o : Odds) : o.val = 0 ↔ o.num = 0 := by
  simp [Odds.val, ENNReal.div_eq_zero_iff]

/-- A part is quiet if its first stop gives none and it states the share 0 of 1. -/
theorem calm_stated {p : Part V W X} (h : ∀ l o, p.bad l o = none)
    (hs : p.badShare = ⟨0, 1⟩) : Calm p :=
  ⟨h, by rw [hs]; simp [Odds.val]⟩

/-- A lifted part is quiet if its source is. -/
theorem Calm.lift {V' W' Y : Type} {see : V → V'} {wit : W → W'} {get : X → Y} {put : X → Y → X}
    {p : Part V' W' Y} (h : Calm p) : Calm (p.lift see wit get put) :=
  ⟨fun l o => h.1 l o, h.2⟩

/-- Two parts as one are quiet if both are. -/
theorem Calm.andThen {p q : Part V W X} (hp : Calm p) (hq : Calm q) :
    Calm (p.andThen q) := by
  refine ⟨fun l o => ?_, ?_⟩
  · show stopBoth p.moves.length q.moves.length p.bad q.bad l o = none
    simp [stopBoth, hp.1, hq.1]
  · refine (odds_val_zero _).2 ?_
    show p.badShare.num * q.badShare.den + q.badShare.num * p.badShare.den = 0
    rw [(odds_val_zero _).1 hp.2, (odds_val_zero _).1 hq.2]
    simp

/-- A half of one part is quiet if the part is. -/
theorem halfCalm_one {x : Placed V W X} {p : Part V W X} (hx : x.parts = [p]) (hp : Calm p) :
    HalfCalm x := by
  intro r hr
  rw [hx, List.mem_singleton] at hr
  rw [hr]
  exact hp

/-- A half of two parts is quiet if both are. -/
theorem halfCalm_pair {x : Placed V W X} {p q : Part V W X} (hx : x.parts = [p, q])
    (hp : Calm p) (hq : Calm q) : HalfCalm x := by
  intro r hr
  rw [hx] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp
  · exact hq

/-- A lot whose reader of the index hangs on the public part is quiet if it is at every reader. -/
theorem LotCalm.byPub (weights : Pub → W₀ → Weights) (L : (W₀ → Weights) → HLot V W X)
    (h : ∀ wt, LotCalm (L wt)) : LotCalm (HLot.byPub weights L) :=
  fun Z G x hx => h (weights Z) Z G x hx

/-- A lot whose data of the main rows hangs on the public part and the ground is quiet if it is at
all data. -/
theorem LotCalm.byRows (D : Pub → Ground → RowDataOf Xi) (L : RowDataOf Xi → HLot V W X)
    (h : ∀ d, LotCalm (L d)) : LotCalm (HLot.byRows D L) :=
  fun Z G x hx => h (D Z G) Z G x hx

/-- What lies in the list of an option that has been mapped is a value of the map. -/
theorem mem_toList_map {α β : Type} {o : Option α} {f : α → β} {x : β}
    (h : x ∈ (o.map f).toList) : ∃ a, x = f a := by
  cases o with
  | none => simp at h
  | some a => exact ⟨a, List.mem_singleton.1 h⟩

/-! ## The parts -/

/-- The part of rounds in which nothing is sent. -/
theorem calmPart_calm (n : Nat) : Calm (quietPart n : Part V W X) :=
  calm_stated (fun _ _ => rfl) rfl

/-- The masked sumcheck's part. -/
theorem sumPart_calm (name endName : String) (J : SumJob W X) :
    Calm (sumPart name endName J : Part V W X) :=
  calm_stated (fun _ _ => rfl) rfl

/-- The sending's part. -/
theorem sendPart_calm (J : K1.SendJob W X) : Calm (K1.sendPart J : Part V W X) :=
  calm_stated (fun _ _ => rfl) rfl

/-- The code switch's part. -/
theorem switchPart_calm (Sd : K2.Sender) (Z : VerifiableInference.Desc.K2.Honest.Sizes)
    (others : Array OnBytes.OracleNotice) (k : Nat) (carries : List (String × Due)) :
    Calm (K2.switchPart Sd Z others k carries) :=
  calm_stated (fun _ _ => rfl) rfl

/-! ## K1, and the message W's side -/

/-- The half at a place of the sending. -/
theorem placeHalf_calm (wit : W → K1.PlaceIn Xi) (J : K1.SendJob (K1.PlaceIn Xi) X) :
    HalfCalm (K1.placeHalf (V := V) wit J) :=
  halfCalm_one rfl (sendPart_calm J).lift

/-- The halves at all places of K1's lot. -/
theorem lotHalves_calm (wit : W → K1.PlaceIn Xi) (no : Place → Nat)
    (D : Pub → Ground → RowDataOf Xi) (Z : Pub) (G : Ground) :
    ∀ x ∈ K1.lotHalves (V := V) (X := X) wit no D Z G, HalfCalm x := by
  intro x hx
  unfold K1.lotHalves at hx
  rcases List.mem_cons.1 hx with rfl | hx
  · exact placeHalf_calm _ _
  · obtain ⟨⟨Y, l⟩, -, hy⟩ := List.mem_flatMap.1 hx
    cases h : VerifiableInference.Desc.K1.linkNumbers G Y with
    | none => simp only [h, List.not_mem_nil] at hy
    | some t =>
      obtain ⟨pr, pd, a, b⟩ := t
      simp only [h, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl <;> exact placeHalf_calm _ _

/-- K1's lot at the numbers off the description's own list. -/
theorem dataSideNo_calm (S : OnBytes.HonestTrace.Sz) (wit : W → K1.PlaceIn ProofFile.Inst)
    (o : SecondHashFunctionArgument) : LotCalm (K1.dataSideNo (V := V) (X := X) S wit o) :=
  fun Z G x hx => lotHalves_calm wit (K1.lotNo o Z) (K1.lotData S) Z G x hx

/-- The halves at the message W's place. -/
theorem wHalves_calm (wit : W → K1.PlaceIn Xi) (no : Place → Nat)
    (D : Pub → Ground → RowDataOf Xi) (Z : Pub) (G : Ground) :
    ∀ x ∈ K1.wHalves (V := V) (X := X) wit no D Z G, HalfCalm x := by
  intro x hx
  obtain ⟨m, rfl⟩ := mem_toList_map hx
  exact placeHalf_calm _ _

/-- The lot of the message W's side, at any number. -/
theorem wSide_calm (wit : W → K1.PlaceIn Xi) (no : Place → Nat)
    (D : Pub → Ground → RowDataOf Xi) : LotCalm (K1.wSide (V := V) (X := X) wit no D) :=
  fun Z G x hx => wHalves_calm wit no D Z G x hx

/-! ## K2 -/

/-- The code switch's half at a place. -/
theorem switchHalf_calm (Sd : K2.Sender) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : K2.Closing) (p : K2.SwitchPlace) :
    HalfCalm (K2.switchHalf (X := X) Sd D readers closing p) :=
  halfCalm_one rfl (switchPart_calm _ _ _ _ _).lift

/-- The code switch's halves at all its places. -/
theorem switchHalves_calm (Sd : K2.Sender) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : K2.Closing) (Z : Pub) (G : Ground) :
    ∀ x ∈ K2.switchHalves (X := X) Sd D readers closing Z G, HalfCalm x := by
  intro x hx
  unfold K2.switchHalves at hx
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
  exact switchHalf_calm _ _ _ _ _

/-- The code switch's lot. -/
theorem switchLot_calm (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers) :
    LotCalm (K2.switchLot (X := X) D readers) :=
  fun Z G x hx => switchHalves_calm _ D readers _ Z G x hx

/-! ## K11 and K13 -/

/-- The lot of the merge of the weights' claims. -/
theorem headMergeLot_calm
    (claims : Pub → Ground → Inst → List Fmt.Drawn → List OnBytes.Model.WsClaim)
    (weights : W₀ → Weights) :
    LotCalm (K11.headMergeLot (Rc := Rc) (Tr := Tr) (X := X) claims weights) := by
  intro Z G x hx
  obtain rfl := List.mem_singleton.1 hx
  exact halfCalm_pair rfl (calmPart_calm 1) (sumPart_calm _ _ _).lift

/-- The lot of the members' batching. -/
theorem k13Lot_calm (weights : W₀ → Weights) (pile : Pub → Ground → K13.PileOf Xi) :
    LotCalm (K13.k13Lot (Rc := Rc) (Tr := Tr) (X := X) weights pile) := by
  intro Z G x hx
  obtain rfl := List.mem_singleton.1 hx
  exact halfCalm_pair rfl (calmPart_calm 1) (sumPart_calm _ _ _).lift

/-! ## The five lots as the filling has them -/

/-- **K1.** -/
theorem k1_calm (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    LotCalm (HLot.byPub I.weights (LongLots.plain (X := X) o S O).k1) :=
  LotCalm.byPub _ _ fun _ => dataSideNo_calm S _ o

/-- **K2.** -/
theorem k2_calm (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) :
    LotCalm (HLot.byPub I.weights fun wt => HLot.byRows (widerRows S) fun D =>
      K2.switchLot (X := X) D fun w : Local W₀ IndexCommitterCoins Inst Cells => ⟨w.trace, wt w.w₀, w.rc⟩) :=
  LotCalm.byPub _ _ fun _ => LotCalm.byRows _ _ fun _ => switchLot_calm _ _

/-- **K7.** -/
theorem k7_calm : LotCalm (replyLot : HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X) := by
  intro Z G x hx
  obtain rfl := List.mem_singleton.1 hx
  exact halfCalm_one rfl (calm_stated (fun _ _ => rfl) rfl)

/-- **K11.** -/
theorem k11_calm (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    LotCalm (HLot.byPub I.weights (LongLots.plain (X := X) o S O).k11) :=
  LotCalm.byPub _ _ fun wt => headMergeLot_calm O.claims wt

/-- **K13.** -/
theorem k13_calm (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    LotCalm (HLot.byPub I.weights (LongLots.plain (X := X) o S O).k13) :=
  LotCalm.byPub _ _ fun wt => k13Lot_calm wt O.pile

/-- **The filling's first five lots are quiet.** The list is read off the filling by rfl, so the
five lots above are the filling's own. -/
theorem wider_five_calm (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) : ∀ L ∈ (widerFillAt I o S O).lots.take 5, LotCalm L := by
  intro L hL
  have e : (widerFillAt I o S O).lots.take 5 =
      [HLot.byPub I.weights (LongLots.plain o S O).k1,
       HLot.byPub I.weights fun wt => HLot.byRows (widerRows S) fun D =>
         K2.switchLot D fun w : Local W₀ IndexCommitterCoins Inst Cells => ⟨w.trace, wt w.w₀, w.rc⟩,
       replyLot,
       HLot.byPub I.weights (LongLots.plain o S O).k11,
       HLot.byPub I.weights (LongLots.plain o S O).k13] := rfl
  rw [e] at hL
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with rfl | rfl | rfl | rfl | rfl
  · exact k1_calm I o S O
  · exact k2_calm I S
  · exact k7_calm
  · exact k11_calm I o S O
  · exact k13_calm I o S O

end P1K8

#print axioms P1K8.odds_val_zero
#print axioms P1K8.calm_stated
#print axioms P1K8.Calm.lift
#print axioms P1K8.Calm.andThen
#print axioms P1K8.halfCalm_one
#print axioms P1K8.halfCalm_pair
#print axioms P1K8.LotCalm.byPub
#print axioms P1K8.LotCalm.byRows
#print axioms P1K8.mem_toList_map
#print axioms P1K8.calmPart_calm
#print axioms P1K8.sumPart_calm
#print axioms P1K8.sendPart_calm
#print axioms P1K8.switchPart_calm
#print axioms P1K8.placeHalf_calm
#print axioms P1K8.lotHalves_calm
#print axioms P1K8.dataSideNo_calm
#print axioms P1K8.wHalves_calm
#print axioms P1K8.wSide_calm
#print axioms P1K8.switchHalf_calm
#print axioms P1K8.switchHalves_calm
#print axioms P1K8.switchLot_calm
#print axioms P1K8.headMergeLot_calm
#print axioms P1K8.k13Lot_calm
#print axioms P1K8.k1_calm
#print axioms P1K8.k2_calm
#print axioms P1K8.k7_calm
#print axioms P1K8.k11_calm
#print axioms P1K8.k13_calm
#print axioms P1K8.wider_five_calm
