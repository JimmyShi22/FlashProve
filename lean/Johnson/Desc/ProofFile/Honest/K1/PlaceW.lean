-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/PlaceW.lean: THE SHARED "SENDING" (the kind K1) IN THE FRAME FOR
THE HONEST SIDE: W's PLACE ⟨1, none, 4, .K1⟩: THE JOB, THE TABLE THAT RIDES, THE HALF UNDER ITS
LOT's NAME. Definitions with code, statements and proofs.

  wGp           the place's numbers of the group: the lot's own term
  wFold         WHICH TABLE RIDES WITH W: where masks are sent ahead: the fresh mask of the first
                fold of the test on the request's own group: its number in the sending and that
                fold's shape: the very terms of linMessageW and linMaskNotice (OnBytes/Iop/Lin.lean)
  wJobAt        the job: the lot's own call K1.parW, at the fold wFold
  wHalves, wSide   the half, where the shape has such a message; the honest side of the lot that
                seats the place (K13.lot4, Johnson/Desc/ProofFile/Lot/K13At4.lean)
  wSide_name, wSide_places   the name is the lot's own field; the halves' places are the places of
                the lot's own blocks
  parW_sent     the sending holds just the message handed in
  w_rounds      K1's own block at W's place has the rounds, oracle messages and place of the job's P
  w_member      THE LOT's MEMBER, with K13's block joined behind (K13.atM4), has them too: that
                block has no round and no oracle message
  w_says        where linMessageW answers: what wFold is, case by case, and which notice the answer
                holds at wFold's number
  w_rideOwn     AT W's PLACE THE TEST ON THE RIDE HOLDS, at every shape that has the message
  w_ride_iff    at every shape that has the message: a fold is handed in JUST WHERE masks are sent
                ahead

Limits. THE DATA (W's rows) ARE A LETTER D: for other files to fill. wit and no are letters, as in
Honest/K1/PlaceJob.lean. THAT THE PLACE OF THE KIND K12 WHICH TESTS THE REQUEST's OWN GROUP HAS
testOwn's HEAD FOR ITS FIRST STAGE (so that wFold's k is that fold's own) is the plan's matter: not
held here. Where the pile has one row W's place is another piece: not covered.
Nothing is played here. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.PlaceJob
import Johnson.Desc.ProofFile.Lot.K13At4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Params VerifiableInference.Desc

variable {V W X Xi : Type}

/-- The place's numbers of the group: the lot's own term (wBlock, Johnson/Desc/ProofFile/Lot/
K13At4.lean). -/
def wGp (Z : Pub) : _root_.Desc.Plain.GPar := { samples := Z.P.samples, firstTree := Z.P.firstTree }

/-- **WHICH TABLE RIDES WITH W**: where masks are sent ahead the prover's message with W holds,
last, the fresh mask of the first fold of the test on the request's own group (linMessageW and
linMaskNotice, OnBytes/Iop/Lin.lean): its number in the sending (behind W, and behind the split's
message where one is needed) and that fold's shape: THE VERY TERMS OF THESE TWO TEXTS. none: masks
are not sent ahead, or the test has no stage. -/
def wFold (S : LinShape) : Option (Nat × FoldShape) :=
  if S.masksAhead then
    S.testOwn.head?.map fun s =>
      (if S.ownSplitNeeded then 2 else 1, { ioppFoldShape s {} with maskLeafClass := S.wLeafClass })
  else none

/-- The job at W's sending: the lot's own call K1.parW, at the fold wFold. -/
def wJobAt (q : Params.First) (gp : _root_.Desc.Plain.GPar) (piece : Nat)
    (msg : Array OracleNotice) (first : Nat) (D : RowDataOf Xi) : SendJob (PlaceIn Xi) X :=
  placeJob (K1.parW q gp piece msg) first (wFold q.lin) D

/-- The half at W's place, where the shape has such a message: by the lot's own terms. -/
def wHalves (wit : W → PlaceIn Xi) (no : Place → Nat) (D : Pub → Ground → RowDataOf Xi) (Z : Pub)
    (G : Ground) : List (Placed V W X) :=
  ((linMessageW Z.first.lin).map fun msg =>
    placeHalf wit (wJobAt Z.first (wGp Z) 4 msg (no ⟨1, none, 4, .K1⟩) (D Z G))).toList

/-- **The honest side of the lot that seats W's place** (K13.lot4): K1's part alone: the block that
the lot joins behind W's commitment has no round. -/
def wSide (wit : W → PlaceIn Xi) (no : Place → Nat) (D : Pub → Ground → RowDataOf Xi) :
    HLot V W X :=
  { name := "K1 and K13: W's commitment, the request's own group and the row (Eval)"
    halves := wHalves wit no D }

theorem wSide_name (wit : W → PlaceIn Xi) (no : Place → Nat) (D : Pub → Ground → RowDataOf Xi)
    (Z : Pub) : (wSide (V := V) (X := X) wit no D).name = (K13.lot4 Z).name := rfl

theorem wSide_places (wit : W → PlaceIn Xi) (no : Place → Nat) (D : Pub → Ground → RowDataOf Xi)
    (Z : Pub) (G : Ground) :
    ((wSide (V := V) (X := X) wit no D).halves Z G).map (·.place) =
      ((K13.lot4 Z).own G).map (·.place) := by
  show (wHalves (V := V) (X := X) wit no D Z G).map (·.place) =
    ((K13.wBlock Z).toList.map (K13.atM4 (K13.whereOf Z))).map (·.place)
  unfold wHalves K13.wBlock K1.wAt
  cases linMessageW Z.first.lin <;> rfl

/-- The sending holds just the message handed in. -/
theorem parW_sent (q : Params.First) (gp : _root_.Desc.Plain.GPar) (piece : Nat)
    (msg : Array OracleNotice) : (K1.parW q gp piece msg).sent = msg := by
  simp [K1.Par.sent, K1.parW]

theorem w_rounds (q : Params.First) (gp : _root_.Desc.Plain.GPar) (piece first : Nat)
    (msg : Array OracleNotice) (D : RowDataOf Xi) (b : Block First.S Unit)
    (hm : linMessageW q.lin = some msg) (hb : K1.wAt q gp piece = some b) :
    b.rounds = K1.rounds (wJobAt (X := X) q gp piece msg first D).P ∧
      b.oracles = K1.oracles (wJobAt (X := X) q gp piece msg first D).P ∧
      b.place = (wJobAt (X := X) q gp piece msg first D).P.place := by
  unfold K1.wAt at hb
  rw [hm] at hb
  obtain rfl := Option.some.inj hb
  exact ⟨rfl, rfl, rfl⟩

/-- **THE LOT's MEMBER, WITH K13's BLOCK JOINED BEHIND**, has them too: that block has no round and
no oracle message. -/
theorem w_member (q : Params.First) (gp : _root_.Desc.Plain.GPar) (piece first : Nat)
    (msg : Array OracleNotice) (D : RowDataOf Xi) (b : Block First.S Unit) (p : K13.Where)
    (hm : linMessageW q.lin = some msg) (hb : K1.wAt q gp piece = some b) :
    (K13.atM4 p b).rounds = K1.rounds (wJobAt (X := X) q gp piece msg first D).P ∧
      (K13.atM4 p b).oracles = K1.oracles (wJobAt (X := X) q gp piece msg first D).P ∧
      (K13.atM4 p b).place = (wJobAt (X := X) q gp piece msg first D).P.place := by
  obtain ⟨h1, h2, h3⟩ := w_rounds (X := X) q gp piece first msg D b hm hb
  refine ⟨?_, ?_, h3⟩
  · show b.rounds ++ [] = _
    rw [List.append_nil, h1]
  · show b.oracles ++ [] = _
    rw [List.append_nil, h2]

/-- What is held of linMessageW's answer msg: where masks are not sent ahead, wFold is none; where
they are, the test has a first stage, wFold is made off it, and msg holds at wFold's number that
fold's mask's notice (foldMaskNotice). That W stands first and that notice last is linMessageW's
text: not stated here. -/
theorem w_says (S : LinShape) (msg : Array OracleNotice) (h : linMessageW S = some msg) :
    (S.masksAhead = false ∧ wFold S = none) ∨
      ∃ s, S.masksAhead = true ∧ S.testOwn.head? = some s ∧
        wFold S = some (if S.ownSplitNeeded then 2 else 1,
          { ioppFoldShape s {} with maskLeafClass := S.wLeafClass }) ∧
        msg[if S.ownSplitNeeded then 2 else 1]? =
          some (foldMaskNotice { ioppFoldShape s {} with maskLeafClass := S.wLeafClass }) := by
  unfold linMessageW at h
  by_cases hm : S.masksAhead = true
  · right
    simp only [hm, if_true, linMaskNotice] at h
    cases hs : S.testOwn.head? with
    | none =>
      rw [hs] at h
      cases h
    | some s =>
      rw [hs] at h
      refine ⟨s, hm, rfl, by simp only [wFold, hm, if_true, hs, Option.map_some], ?_⟩
      obtain rfl := Option.some.inj h
      by_cases ho : S.ownSplitNeeded = true
      · simp [ho]
      · simp [ho]
  · left
    have hf : S.masksAhead = false := by simpa using hm
    exact ⟨hf, by simp only [wFold, hf, Bool.false_eq_true, if_false]⟩

/-- **AT W's PLACE THE TEST ON THE RIDE HOLDS.** -/
theorem w_rideOwn (q : Params.First) (gp : _root_.Desc.Plain.GPar) (piece : Nat)
    (msg : Array OracleNotice) (h : linMessageW q.lin = some msg) :
    rideOwn (K1.parW q gp piece msg) (wFold q.lin) = true := by
  unfold rideOwn
  rw [parW_sent]
  rcases w_says q.lin msg h with ⟨_, e⟩ | ⟨s, _, _, e, hn⟩
  · rw [e]
    rfl
  · rw [e]
    show (msg[if q.lin.ownSplitNeeded then 2 else 1]? == _) = true
    rw [hn]
    exact beq_self_eq_true _

theorem w_ride_iff (S : LinShape) (msg : Array OracleNotice) (h : linMessageW S = some msg) :
    (wFold S).isSome = S.masksAhead := by
  rcases w_says S msg h with ⟨hm, e⟩ | ⟨s, hm, _, e, _⟩
  · rw [e, hm]
    rfl
  · rw [e, hm]
    rfl

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.wSide_name
#print axioms ProofFile.Honest.K1.wSide_places
#print axioms ProofFile.Honest.K1.parW_sent
#print axioms ProofFile.Honest.K1.w_rounds
#print axioms ProofFile.Honest.K1.w_member
#print axioms ProofFile.Honest.K1.w_says
#print axioms ProofFile.Honest.K1.w_rideOwn
#print axioms ProofFile.Honest.K1.w_ride_iff
#print axioms ProofFile.Honest.K1.wGp
#print axioms ProofFile.Honest.K1.wFold
#print axioms ProofFile.Honest.K1.wJobAt
#print axioms ProofFile.Honest.K1.wHalves
#print axioms ProofFile.Honest.K1.wSide
