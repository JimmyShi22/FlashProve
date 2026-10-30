-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/RowSeated.lean: the statement `RowPlaysFull`
(Honest/K3/Law/RowPlays.lean) for the row as it is seated in a chain's letters (`proverSideOfLookupInChainAtOneOwner`,
Honest/K3/Row.lean: every part by `Part.lift`), with its proof. A statement and a theorem.

Terms. Honest/K3/GLOSSARY.md ("course", "half", "play", "reader, readers", "row").

What is shown.
  `RowPlaysSeated`: the statement.
  `rowPlaysSeated`: its proof.
What the statement says. The chain's state in front is t₁, at the chain's input type W₁ and at
whatever the chain's parts hand on (X₁). The course is at the jobs' own input type W, and stands at
the narrowed state: the input read by "wit", the same challenges heard, nothing handed on. Then the
frame's player on the seated row's steps, from t₁ on, goes through and yields the course's rounds.
Behind it the chain's state has heard the lookup's challenges, and what the chain's parts hand on is
as it was: every move of the row hands on what it was given, and the seat's "set" writes nothing.

Hypotheses that remain. `Fit` and `entriesFit`, and that the course stands at the narrowed state,
and no other: no summand is read.

How the proof goes. It rests on Honest/K3/Law/PlayLift.lean (for every part) and on the lemmas of
RowPlays.lean.

Users. This file is imported by Honest/K3/Law/RowParts.lean and Honest/K3/Law/Top.lean.

Limits. As in RowPlays.lean: rounds come, and whose they are; nothing on what they are worth. The
book's lending (`lendRow`) is not spoken of: the row's coins are a letter.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.RowPlays
import Johnson.Desc.ProofFile.Honest.K3.Law.PlayLift

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open VerifiableInference.Desc (Oracle)
open VerifiableInference.Desc.K3 (entriesV entriesFit)

/-- **The seated row plays.** Conditional on nothing but `Fit`, `entriesFit` and that the course
stands at the narrowed state (R.t = t₁.narrow wit …): no summand is read: it holds of whatever
summands the course has. What the chain's parts hand on stays that of t₁, since every move of the
row hands on what it was given and the seat's "set" writes nothing. Behind the row the columns
opened stand as they stood in front. A lemma's statement, none of the library's goals. -/
def RowPlaysSeated : Prop :=
  ∀ (V₁ W₁ X₁ W : Type) (R : Course W) (wit : W₁ → W) (t₁ : State W₁ X₁) (name : String)
    (v : Option V₁) (es : List Fmt.Entry) (loc : List Fmt.Drawn)
    (c : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) ⟨ptsOf, pointsAt⟩ R.J wit R.a).parts),
    R.t = t₁.narrow wit (fun _ => ()) →
    ∃ c' : (s : Stage) → StageCoins R.a s,
      CoinsAre (V := Unit) { R with c := c' }
        (unlift (X := X₁) (fun (_ : V₁) => ()) wit (lookRow ⟨ptsOf, pointsAt⟩ R.J R.a) c) ∧
      (Fit R → entriesFit R.f es = true → ∀ back : List Fmt.RoundView,
        ∃ y x, play (rowSteps name R.a.place v (proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩ R.J wit R.a).parts 0
              (es.map fun e => (declOf e, ([] : List Oracle))) c) R.ds back
              ⟨t₁, loc, R.seen.rounds, R.seen.opened⟩ = .ok y ∧
          ({ R with c := c' } : Course W).rounds = some x ∧ roundsOf y.1 = x ∧
          y.2 = ⟨{ t₁ with heard := t₁.heard ++ R.ds }, loc ++ R.ds, R.seen.rounds ++ x,
            R.seen.opened⟩ ∧
          ∀ q ∈ y.1, q.place = R.a.place ∧ q.told = true ∧ q.tables = [])

/-- **The proof of `RowPlaysSeated`.** -/
theorem rowPlaysSeated : RowPlaysSeated := by
  intro V₁ W₁ X₁ W R wit t₁ name v es loc c hR
  let c₀ : RowCoins (lookRow (V := Unit) Rd R.J R.a) :=
    unlift (X := X₁) (fun (_ : V₁) => ()) wit (lookRow Rd R.J R.a) c
  let g := rowRead _ c₀
  let R' : Course W := { R with c := courseCoins R.a g }
  have hc : CoinsRow R' ((stages R.a.face).zipIdx) c₀ :=
    coinsRow_of_read R' g (fun _ => rfl) (stages R.a.face) 0 c₀
      (fun j _ => by rw [Nat.zero_add]; rfl)
      (fun j hj => by simpa using indexOf_getElem R.a.face j hj)
  refine ⟨courseCoins R.a g, coinsAre R' c₀ hc, fun hfit hes back => ?_⟩
  have h2 := two_le_planes_of_ok _ hfit.ok
  have hlen : R.ds.length = (((stages R.a.face).zipIdx).map fun x => x.1.rounds R.a.face).sum := by
    rw [drawsFit_length _ _ hfit.draws, List.length_map,
      map_zipIdx_fst (fun s => Stage.rounds R.a.face s), rounds_stages _ h2]
  obtain ⟨x, hx⟩ := aloneRow_some R' ((stages R.a.face).zipIdx) c₀ R.t R.seen R.ds hlen
  have hcut : es.map cutOf =
      (((stages R.a.face).zipIdx).flatMap fun x => Stage.entries R.a.face x.1).map cutOf := by
    rw [flatMap_zipIdx_fst (Stage.entries R.a.face), entries_stages _ h2]
    have e : (es.map fun e => { e with work := 0 }) = entriesV R.a.face := eq_of_beq hes
    rw [← e, List.map_map]
    rfl
  have hx' : aloneRow ((lookRow (V := Unit) Rd R.J R.a).map
      (liftU (X := X₁) (fun (_ : V₁) => ()) wit)) c t₁ R.seen R.ds = some x := by
    rw [aloneRow_lift, ← hR]
    exact hx
  obtain ⟨y, hy, hy1, hy2⟩ := play_row name R.a.place v _ 0
    (es.map fun e => (declOf e, ([] : List Oracle))) c R.ds back t₁ loc R.seen x
    (noStops_lift (X := X₁) (fun (_ : V₁) => ()) wit _ (row_noStops R' ((stages R.a.face).zipIdx)))
    (rowFits_lift (fun (_ : V₁) => ()) wit _ _ c (row_fits R' _ es c₀ hcut)) hx'
  refine ⟨y, x, hy, ?_, hy1, ?_, played_row name R.a.place v _ 0 _ c R.ds back _ y hy
    (fun r hr => by
      obtain ⟨_, _, rfl⟩ := List.mem_map.1 hr
      rfl)⟩
  · show R'.run (stages R.a.face) R.t R.seen R.ds = some x
    rw [← hx, aloneRow_run R' _ c₀ _ _ _ hc, map_zipIdx_fst (fun s => s), List.map_id']
  · have he : endRow ((lookRow (V := Unit) Rd R.J R.a).map
        (liftU (X := X₁) (fun (_ : V₁) => ()) wit)) t₁ R.ds =
        { t₁ with heard := t₁.heard ++ R.ds } :=
      endRow_lift_keep _ wit _ t₁ R.ds (by
        rw [lookRow_moves, hlen, map_zipIdx_fst (fun s => Stage.rounds R.a.face s)])
    rw [hy2]
    exact congrArg (fun s => (⟨s, loc ++ R.ds, R.seen.rounds ++ x, R.seen.opened⟩ : Mid W₁ X₁)) he

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.rowPlaysSeated
