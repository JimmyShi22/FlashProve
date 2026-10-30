-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Coin/ErrJBelow.lean: THE JOINT: from "every written round of a place's test has its
count at most b of its written verifier messages" (`H2K.Pub.RoundsBelowAt`,
Johnson/Desc/K12/Law/RoundsAtMade.lean: the kind's own files' form, at the chain that `chainFrom`
makes) to `Err.Below` of the errors at which the game of the proximity test stands at a seat:
(e, `errJ π r dt`) with e the least that the game allows (Johnson/Desc/K12/Coin/GameJ.lean:
`K12GameT`, `K12GameTO`). Definitions, statements and proofs.

Why. The two forms speak of one list of numbers over two shapes: the library's shape of the chain's
own written rounds, and the shape of the stretch of a file's declared rounds with data. Where the
stretch is like the written rounds, each round of the one has as many verifier messages as its
fellow of the other: that number reads a round's entry and kind alone.

Main names:
  `SameChal`, `below_errOfList`: a list of errors that is below b stays below b when it is laid over
    a shape whose rounds have, one by one, as many verifier messages.
  `like_sameChal`, `shapes_same`: a round's data that are like a written round have as many; so
    have the two shapes, round by round.
  `batV0_eq`: the batching's count `batV0 π r` is the Johnson bound's list at the first stage,
    times the place's rows less one: the number in `RoundsBelowAt`.
  `errJ_below`: **the joint**, at radii r by stage.
  `rOf`, `rOf_st`, `errJ_below_rad`: the same from `RoundsBelowAt` at radii by the library's form of
    a stage, as the kind's files state it at the planner's radii.
  `below_of_heq`, `own_below`: the joint where a piece's stretch is dB :: dt by an equation and its
    own errors are the pair by `HEq`: the form in which a row names a block's own errors.
  `errJ_below_atPlace`, `errJ_below_atPlaceOwn`: with "the stretch is like the written rounds" taken
    from `AtPlace` | `AtPlaceOwn`.

Silly members: at b = ⊤ the premise and the conclusion are idle. Where the plan gives no chain
`RoundsBelowAt` is false. Every "there is", walked: the premise's five are used up; none is left.
Limits. A RULE: `RoundsBelowAt` is a premise: that it holds at a place is the kind's files' to show.
A bound on counts: that a count bounds a prover's chance is the game's. One round at a time: no sum.
Nothing on soundness.

-/
import Johnson.Desc.K12.Coin.GameJ
import Johnson.Desc.K12.Law.RoundsAtMade
import OnBytes.Flat.CarrySBelow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open H2K.Pub (sgOf writtenOf WR chainFrom batV0 batAtB v0On RoundsBelowAt)
open OnBytes.Flat (wT toRD card_wT)
open scoped ENNReal

/-- Two rounds have as many verifier messages. -/
def SameChal (r r' : Round) : Prop := Fintype.card r.Chal = Fintype.card r'.Chal

/-- A list of errors below b, laid over a shape whose rounds have as many verifier messages. -/
theorem below_errOfList : ∀ (s t : Shape) (ε : Err s) (b : ℝ≥0∞), List.Forall₂ SameChal s t →
    Err.Below ε b → Err.Below (errOfList t (errList s ε)) b
  | [], [], _, _, _, _ => trivial
  | [], _ :: _, _, _, h, _ => nomatch h
  | _ :: _, [], _, _, h, _ => nomatch h
  | r :: s, r' :: t, (e, ε), b, h, H => by
    cases h with
    | cons h1 h2 =>
      refine ⟨?_, below_errOfList s t ε b h2 H.2⟩
      show (e : ℝ≥0∞) ≤ b * (Fintype.card r'.Chal : ℝ≥0∞)
      rw [← h1]
      exact H.1

theorem like_sameChal {d : RDT} {w : WR} (h : Like d w) : SameChal (wRound w.rd) (wT d) := by
  have e1 : (toRD d).entry = w.rd.entry := h.1
  have e2 : (toRD d).kind = w.rd.kind := h.2.1
  unfold SameChal
  rw [card_wT, card_wRound, card_wRound, e1, e2]

theorem shapes_same : ∀ (dt : List RDT) (l : List WR), List.Forall₂ Like dt l →
    List.Forall₂ SameChal (PQ.uL (ckP .two) (l.map WR.rd)) (uLT (ckP .two) dt)
  | [], [], _ => .nil
  | [], _ :: _, h => nomatch h
  | _ :: _, [], h => nomatch h
  | d :: dt, w :: l, h => by
    cases h with
    | cons h1 h2 =>
      show List.Forall₂ SameChal (wRound w.rd :: PQ.uL (ckP .two) (l.map WR.rd))
        (wT d :: uLT (ckP .two) dt)
      exact .cons (like_sameChal h1) (shapes_same dt l h2)

/-- The batching's count is the number in `RoundsBelowAt`. -/
theorem batV0_eq (π : P12) (r : Fmt.M1.Stage → ℕ) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (w0 : WR) (l : List WR) (hs : π.nums.stages = a :: rest)
    (hw : writtenOf π.nums = some (w0 :: l)) :
    batV0 π r = (sgOf a).lstJ (r (sgOf a).st) * (π.nums.rows - 1) := by
  have hr : w0.entry.rows = π.nums.rows := by
    rw [H2K.Made.written_bat_eq π.nums w0 l hw]
    rfl
  unfold batV0 batAtB
  rw [hs, hw]
  show v0On (sgOf a).st (r (sgOf a).st) w0.entry.rows = _
  rw [hr]
  rfl

/-- **THE JOINT.** -/
theorem errJ_below (π : P12) (r : Fmt.M1.Stage → ℕ) (dB : RDT) (dt : List RDT) (b : ℝ≥0∞)
    (H : RoundsBelowAt π (fun s => r s.st) b)
    (hl : ∃ w0 l, writtenOf π.nums = some (w0 :: l) ∧ List.Forall₂ Like (dB :: dt) (w0 :: l)) :
    Err.Below (s := uLT (ckP .two) (dB :: dt))
      (batV0 π r * (bsRound .two dB.entry dB.kind).w, errJ π r dt) b := by
  obtain ⟨a, rest, w0, l, c, e1, e2, e3, e4, e5, e6⟩ := H
  obtain ⟨w0', l', hw', hlike⟩ := hl
  obtain ⟨rfl, rfl⟩ := List.cons.inj (Option.some.inj (hw'.symm.trans e2))
  cases hlike with
  | cons hB hT =>
    have eJ : errJ π r dt = errOfList (uLT (ckP .two) dt) (errList _ c.errL) := by
      unfold errJ
      rw [e1, e2]
      dsimp only
      rw [e3]
    refine ⟨?_, ?_⟩
    · show ((batV0 π r * (bsRound .two dB.entry dB.kind).w : ℕ) : ℝ≥0∞) ≤
        b * (Fintype.card (wT dB).Chal : ℝ≥0∞)
      rw [batV0_eq π r a rest w0' l' e1 e2, ← like_sameChal hB, hB.1, hB.2.1]
      exact e5
    · rw [eJ]
      refine below_errOfList _ _ c.errL b ?_ (Chain.errL_below c b e6)
      rw [e4]
      exact shapes_same dt l' hT

/-- Radii by stage, of radii by the library's form of a stage. -/
def rOf (rad : Sg → ℕ) (a : Fmt.M1.Stage) : ℕ := rad (sgOf a)

theorem sgOf_stOf (s : Sg) : sgOf s.st = s := by
  cases s with
  | mk C Z h g t =>
    show (⟨C, Z, h, h + g - h, t⟩ : Sg) = ⟨C, Z, h, g, t⟩
    rw [Nat.add_sub_cancel_left]

theorem rOf_st (rad : Sg → ℕ) : (fun s : Sg => rOf rad s.st) = rad := by
  funext s
  show rad (sgOf s.st) = rad s
  rw [sgOf_stOf]

/-- **The joint, from the form at radii by the library's form of a stage.** -/
theorem errJ_below_rad (π : P12) (rad : Sg → ℕ) (dB : RDT) (dt : List RDT) (b : ℝ≥0∞)
    (H : RoundsBelowAt π rad b)
    (hl : ∃ w0 l, writtenOf π.nums = some (w0 :: l) ∧ List.Forall₂ Like (dB :: dt) (w0 :: l)) :
    Err.Below (s := uLT (ckP .two) (dB :: dt))
      (batV0 π (rOf rad) * (bsRound .two dB.entry dB.kind).w, errJ π (rOf rad) dt) b :=
  errJ_below π (rOf rad) dB dt b ((rOf_st rad).symm ▸ H) hl

/-- The bound passes to a list of errors over an equal stretch that is the same list. -/
theorem below_of_heq {ds ds' : List RDT} (h : ds = ds') (ε : Err (uLT (ckP .two) ds))
    (ε' : Err (uLT (ckP .two) ds')) (he : HEq ε ε') (b : ℝ≥0∞) (H : Err.Below ε' b) :
    Err.Below ε b := by
  subst h
  rw [eq_of_heq he]
  exact H

/-- **The joint in the form in which a row's own errors are named**: a piece's stretch ds is
dB :: dt, and its own errors ε are the pair. -/
theorem own_below (π : P12) (r : Fmt.M1.Stage → ℕ) (ds : List RDT) (dB : RDT) (dt : List RDT)
    (ε : Err (uLT (ckP .two) ds)) (hds : ds = dB :: dt)
    (herr : HEq ε ((batV0 π r * (bsRound .two dB.entry dB.kind).w, errJ π r dt) :
      Err (uLT (ckP .two) (dB :: dt)))) (b : ℝ≥0∞)
    (H : RoundsBelowAt π (fun s => r s.st) b)
    (hl : ∃ w0 l, writtenOf π.nums = some (w0 :: l) ∧ List.Forall₂ Like (dB :: dt) (w0 :: l)) :
    Err.Below ε b :=
  below_of_heq hds ε _ herr b (errJ_below π r dB dt b H hl)

section
variable {F : Frame} {π : P12} {num : Fmt.TreeSource → ℕ} {L mC mS mW : Sg → ℕ → ℕ} {rad' : Sg → ℕ}
  {base : ℕ} {dB : RDT} {dt : List RDT} {εt : Err (uLT (ckP .two) dt)}

theorem errJ_below_atPlace (A : AtPlace F π num L mC mS mW rad' base dB dt εt)
    (r : Fmt.M1.Stage → ℕ) (b : ℝ≥0∞) (H : RoundsBelowAt π (fun s => r s.st) b) :
    Err.Below (s := uLT (ckP .two) (dB :: dt))
      (batV0 π r * (bsRound .two dB.entry dB.kind).w, errJ π r dt) b :=
  errJ_below π r dB dt b H A.like

theorem errJ_below_atPlaceOwn (A : AtPlaceOwn F π num L mC mS mW rad' base dB dt εt)
    (r : Fmt.M1.Stage → ℕ) (b : ℝ≥0∞) (H : RoundsBelowAt π (fun s => r s.st) b) :
    Err.Below (s := uLT (ckP .two) (dB :: dt))
      (batV0 π r * (bsRound .two dB.entry dB.kind).w, errJ π r dt) b :=
  errJ_below π r dB dt b H A.like

end

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.below_errOfList
#print axioms VerifiableInference.Desc.K12.Coin.errJ_below
#print axioms VerifiableInference.Desc.K12.Coin.errJ_below_rad
#print axioms VerifiableInference.Desc.K12.Coin.own_below
#print axioms VerifiableInference.Desc.K12.Coin.errJ_below_atPlace
