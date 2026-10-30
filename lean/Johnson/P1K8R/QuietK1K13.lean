-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/QuietK1K13.lean: the five lots K1, K2, K7, K11 and K13 of the first chain are quiet.
Words: Johnson/P1K8R/QuietLots.lean.

  Quiet.lift, Quiet.andThen     a lifted part, and two parts as one, are quiet if their sources are
  LotQuiet.byPub, .byRows       the two forms of a lot keep LotQuiet
  quietPart_quiet, sumPart_quiet, sendPart_quiet, switchPart_quiet   the parts that these lots use
  dataSideNo_quiet, switchLot_quiet, headMergeLot_quiet, k13Lot_quiet, wSide_quiet   the lots,
      general in their letters
  k1_quiet, k2_quiet, k7_quiet, k11_quiet, k13_quiet   the lots as the filling has them
  wider_five_quiet   the filling's first five lots, read off the filling itself

Limits. A lot with no half is quiet: nothing here says that any half stands. Nothing is said of a
run or of any property of a prover.
-/
import Johnson.P1K8R.QuietLots
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

/-- A part is quiet if its second stop gives none and it states the share 0 of 1. -/
theorem quiet_stated {p : Part V W X} (h : ∀ u l o, p.hid u l o = none)
    (hs : p.hidShare = ⟨0, 1⟩) : Quiet p :=
  ⟨h, by rw [hs]; simp [Odds.val]⟩

/-- A lifted part is quiet if its source is. -/
theorem Quiet.lift {V' W' Y : Type} {see : V → V'} {wit : W → W'} {get : X → Y} {put : X → Y → X}
    {p : Part V' W' Y} (h : Quiet p) : Quiet (p.lift see wit get put) :=
  ⟨fun u l o => h.1 (see u) l o, h.2⟩

/-- Two parts as one are quiet if both are. -/
theorem Quiet.andThen {p q : Part V W X} (hp : Quiet p) (hq : Quiet q) :
    Quiet (p.andThen q) := by
  refine ⟨fun u l o => ?_, ?_⟩
  · show stopBoth p.moves.length q.moves.length (p.hid u) (q.hid u) l o = none
    simp [stopBoth, hp.1, hq.1]
  · refine (odds_val_zero _).2 ?_
    show p.hidShare.num * q.hidShare.den + q.hidShare.num * p.hidShare.den = 0
    rw [(odds_val_zero _).1 hp.2, (odds_val_zero _).1 hq.2]
    simp

/-- A half of one part is quiet if the part is. -/
theorem halfQuiet_one {x : Placed V W X} {p : Part V W X} (hx : x.parts = [p]) (hp : Quiet p) :
    HalfQuiet x := by
  intro r hr
  rw [hx, List.mem_singleton] at hr
  rw [hr]
  exact hp

/-- A half of two parts is quiet if both are. -/
theorem halfQuiet_pair {x : Placed V W X} {p q : Part V W X} (hx : x.parts = [p, q])
    (hp : Quiet p) (hq : Quiet q) : HalfQuiet x := by
  intro r hr
  rw [hx] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact hp
  · exact hq

/-- A lot whose reader of the index hangs on the public part is quiet if it is at every reader. -/
theorem LotQuiet.byPub (weights : Pub → W₀ → Weights) (L : (W₀ → Weights) → HLot V W X)
    (h : ∀ wt, LotQuiet (L wt)) : LotQuiet (HLot.byPub weights L) :=
  fun Z G x hx => h (weights Z) Z G x hx

/-- A lot whose data of the main rows hangs on the public part and the ground is quiet if it is at
all data. -/
theorem LotQuiet.byRows (D : Pub → Ground → RowDataOf Xi) (L : RowDataOf Xi → HLot V W X)
    (h : ∀ d, LotQuiet (L d)) : LotQuiet (HLot.byRows D L) :=
  fun Z G x hx => h (D Z G) Z G x hx

/-- What lies in the list of an option that has been mapped is a value of the map. -/
theorem mem_toList_map {α β : Type} {o : Option α} {f : α → β} {x : β}
    (h : x ∈ (o.map f).toList) : ∃ a, x = f a := by
  cases o with
  | none => simp at h
  | some a => exact ⟨a, List.mem_singleton.1 h⟩

/-! ## The parts -/

/-- The part of rounds in which nothing is sent. -/
theorem quietPart_quiet (n : Nat) : Quiet (quietPart n : Part V W X) :=
  quiet_stated (fun _ _ _ => rfl) rfl

/-- The masked sumcheck's part. -/
theorem sumPart_quiet (name endName : String) (J : SumJob W X) :
    Quiet (sumPart name endName J : Part V W X) :=
  quiet_stated (fun _ _ _ => rfl) rfl

/-- The sending's part. -/
theorem sendPart_quiet (J : K1.SendJob W X) : Quiet (K1.sendPart J : Part V W X) :=
  quiet_stated (fun _ _ _ => rfl) rfl

/-- The code switch's part. -/
theorem switchPart_quiet (Sd : K2.Sender) (Z : VerifiableInference.Desc.K2.Honest.Sizes)
    (others : Array OnBytes.OracleNotice) (k : Nat) (carries : List (String × Due)) :
    Quiet (K2.switchPart Sd Z others k carries) :=
  quiet_stated (fun _ _ _ => rfl) rfl

/-! ## K1, and the message W's side -/

/-- The half at a place of the sending. -/
theorem placeHalf_quiet (wit : W → K1.PlaceIn Xi) (J : K1.SendJob (K1.PlaceIn Xi) X) :
    HalfQuiet (K1.placeHalf (V := V) wit J) :=
  halfQuiet_one rfl (sendPart_quiet J).lift

/-- The halves at all places of K1's lot. -/
theorem lotHalves_quiet (wit : W → K1.PlaceIn Xi) (no : Place → Nat)
    (D : Pub → Ground → RowDataOf Xi) (Z : Pub) (G : Ground) :
    ∀ x ∈ K1.lotHalves (V := V) (X := X) wit no D Z G, HalfQuiet x := by
  intro x hx
  unfold K1.lotHalves at hx
  rcases List.mem_cons.1 hx with rfl | hx
  · exact placeHalf_quiet _ _
  · obtain ⟨⟨Y, l⟩, -, hy⟩ := List.mem_flatMap.1 hx
    cases h : VerifiableInference.Desc.K1.linkNumbers G Y with
    | none => simp only [h, List.not_mem_nil] at hy
    | some t =>
      obtain ⟨pr, pd, a, b⟩ := t
      simp only [h, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl <;> exact placeHalf_quiet _ _

/-- K1's lot at the numbers off the description's own list. -/
theorem dataSideNo_quiet (S : OnBytes.HonestTrace.Sz) (wit : W → K1.PlaceIn ProofFile.Inst)
    (o : SecondHashFunctionArgument) : LotQuiet (K1.dataSideNo (V := V) (X := X) S wit o) :=
  fun Z G x hx => lotHalves_quiet wit (K1.lotNo o Z) (K1.lotData S) Z G x hx

/-- The halves at the message W's place. -/
theorem wHalves_quiet (wit : W → K1.PlaceIn Xi) (no : Place → Nat)
    (D : Pub → Ground → RowDataOf Xi) (Z : Pub) (G : Ground) :
    ∀ x ∈ K1.wHalves (V := V) (X := X) wit no D Z G, HalfQuiet x := by
  intro x hx
  obtain ⟨m, rfl⟩ := mem_toList_map hx
  exact placeHalf_quiet _ _

/-- The lot of the message W's side, at any number. -/
theorem wSide_quiet (wit : W → K1.PlaceIn Xi) (no : Place → Nat)
    (D : Pub → Ground → RowDataOf Xi) : LotQuiet (K1.wSide (V := V) (X := X) wit no D) :=
  fun Z G x hx => wHalves_quiet wit no D Z G x hx

/-! ## K2 -/

/-- The code switch's half at a place. -/
theorem switchHalf_quiet (Sd : K2.Sender) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : K2.Closing) (p : K2.SwitchPlace) :
    HalfQuiet (K2.switchHalf (X := X) Sd D readers closing p) :=
  halfQuiet_one rfl (switchPart_quiet _ _ _ _ _).lift

/-- The code switch's halves at all its places. -/
theorem switchHalves_quiet (Sd : K2.Sender) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : K2.Closing) (Z : Pub) (G : Ground) :
    ∀ x ∈ K2.switchHalves (X := X) Sd D readers closing Z G, HalfQuiet x := by
  intro x hx
  unfold K2.switchHalves at hx
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
  exact switchHalf_quiet _ _ _ _ _

/-- The code switch's lot. -/
theorem switchLot_quiet (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers) :
    LotQuiet (K2.switchLot (X := X) D readers) :=
  fun Z G x hx => switchHalves_quiet _ D readers _ Z G x hx

/-! ## K11 and K13 -/

/-- The lot of the merge of the weights' claims. -/
theorem headMergeLot_quiet
    (claims : Pub → Ground → Inst → List Fmt.Drawn → List OnBytes.Model.WsClaim)
    (weights : W₀ → Weights) :
    LotQuiet (K11.headMergeLot (Rc := Rc) (Tr := Tr) (X := X) claims weights) := by
  intro Z G x hx
  obtain rfl := List.mem_singleton.1 hx
  exact halfQuiet_pair rfl (quietPart_quiet 1) (sumPart_quiet _ _ _).lift

/-- The lot of the members' batching. -/
theorem k13Lot_quiet (weights : W₀ → Weights) (pile : Pub → Ground → K13.PileOf Xi) :
    LotQuiet (K13.k13Lot (Rc := Rc) (Tr := Tr) (X := X) weights pile) := by
  intro Z G x hx
  obtain rfl := List.mem_singleton.1 hx
  exact halfQuiet_pair rfl (quietPart_quiet 1) (sumPart_quiet _ _ _).lift

/-! ## The five lots as the filling has them -/

/-- **K1.** -/
theorem k1_quiet (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    LotQuiet (HLot.byPub I.weights (LongLots.plain (X := X) o S O).k1) :=
  LotQuiet.byPub _ _ fun _ => dataSideNo_quiet S _ o

/-- **K2.** -/
theorem k2_quiet (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) :
    LotQuiet (HLot.byPub I.weights fun wt => HLot.byRows (widerRows S) fun D =>
      K2.switchLot (X := X) D fun w : Local W₀ IndexCommitterCoins Inst Cells => ⟨w.trace, wt w.w₀, w.rc⟩) :=
  LotQuiet.byPub _ _ fun _ => LotQuiet.byRows _ _ fun _ => switchLot_quiet _ _

/-- **K7.** -/
theorem k7_quiet : LotQuiet (replyLot : HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X) := by
  intro Z G x hx
  obtain rfl := List.mem_singleton.1 hx
  exact halfQuiet_one rfl (quiet_stated (fun _ _ _ => rfl) rfl)

/-- **K11.** -/
theorem k11_quiet (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    LotQuiet (HLot.byPub I.weights (LongLots.plain (X := X) o S O).k11) :=
  LotQuiet.byPub _ _ fun wt => headMergeLot_quiet O.claims wt

/-- **K13.** -/
theorem k13_quiet (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    LotQuiet (HLot.byPub I.weights (LongLots.plain (X := X) o S O).k13) :=
  LotQuiet.byPub _ _ fun wt => k13Lot_quiet wt O.pile

/-- **The filling's first five lots are quiet.** The list is read off the filling by rfl, so the
five lots above are the filling's own. -/
theorem wider_five_quiet (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) : ∀ L ∈ (widerFillAt I o S O).lots.take 5, LotQuiet L := by
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
  · exact k1_quiet I o S O
  · exact k2_quiet I S
  · exact k7_quiet
  · exact k11_quiet I o S O
  · exact k13_quiet I o S O

end P1K8

#print axioms P1K8.odds_val_zero
#print axioms P1K8.quiet_stated
#print axioms P1K8.Quiet.lift
#print axioms P1K8.Quiet.andThen
#print axioms P1K8.halfQuiet_one
#print axioms P1K8.halfQuiet_pair
#print axioms P1K8.LotQuiet.byPub
#print axioms P1K8.LotQuiet.byRows
#print axioms P1K8.mem_toList_map
#print axioms P1K8.quietPart_quiet
#print axioms P1K8.sumPart_quiet
#print axioms P1K8.sendPart_quiet
#print axioms P1K8.switchPart_quiet
#print axioms P1K8.placeHalf_quiet
#print axioms P1K8.lotHalves_quiet
#print axioms P1K8.dataSideNo_quiet
#print axioms P1K8.wHalves_quiet
#print axioms P1K8.wSide_quiet
#print axioms P1K8.switchHalf_quiet
#print axioms P1K8.switchHalves_quiet
#print axioms P1K8.switchLot_quiet
#print axioms P1K8.headMergeLot_quiet
#print axioms P1K8.k13Lot_quiet
#print axioms P1K8.k1_quiet
#print axioms P1K8.k2_quiet
#print axioms P1K8.k7_quiet
#print axioms P1K8.k11_quiet
#print axioms P1K8.k13_quiet
#print axioms P1K8.wider_five_quiet
