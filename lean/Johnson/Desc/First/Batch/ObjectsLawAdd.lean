-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/ObjectsLawAdd.lean: THE JOINT OF (2) AND (3) OF
Johnson/Desc/First/Batch/ObjectsLaw.lean: K9.adds OVER gather IS "made first, then added" AT THE
REAL ADDING. K9.adds adds by the kind's own addList (Johnson/Desc/First/Batch/Add.lean); the laws
speak of Claim.lean's addAll; Johnson/Desc/First/Batch/Law/AddAgrees.lean ties the two:
addList_older (a yes of addList is a yes of addAll, to the same ledger: at all arguments) and
addList_newer (the converse, WHERE THERE IS A MARK: the table of the weights handed out is not
empty). No Mathlib.
  `adds_yes`: a yes of K9.adds over gather is a yes of madeThenAdded, to the same state: no premise
      on marks.
  `adds_is_madeThen`: just if, where there is a mark at the state behind the gathering.
Silly members. At a lens that gives no part K9.adds refuses all: `adds_yes` holds for nothing there.
At a gathering that refuses `MarkedBehind` holds for nothing, and both sides refuse.
Limits: `MarkedBehind` IS A PREMISE THAT NOBODY PAYS YET. It bears load: with no mark and a list
that is not empty the two sides part. K9's draw lays "the draw has run" and the marks in one update,
where the plan has a claim; that every block between the draw and the adding, and every run of the
gathering, keeps "the draw has run, so there is a mark" is a fact on two fields of the kind's part:
owed. It is asked at the state BEHIND the gathering, also where the list gathered is empty (there
both sides say yes without it: a weaker premise would do). A road "a yes gives ..." needs `adds_yes`
alone. Nothing on soundness.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.First.Batch.ObjectsLaw
import Johnson.Desc.First.Batch.Law.AddAgrees

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open VerifiableInference.Desc.K9L (addList_older addList_newer)

variable {T Cl : Type}

/-- There is a mark at the state behind the gathering. -/
def MarkedBehind (X : Lens T) (fs : List (Fn T)) (t : T) : Prop :=
  ∀ (z : List Claim × T) (s : Part), gatherFrom fs 0 t = .ok z → X.get? z.2 = some s →
    s.F.kapMapF.isEmpty = false

/-- The two, behind the gathering: what K9.adds does with the list, and what madeThenAdded does. -/
theorem laid_iff (X : Lens T) (h : LensOk X) (z : List Claim × T) (v : T)
    (hm : ∀ s, X.get? z.2 = some s → s.F.kapMapF.isEmpty = false) :
    ((do
        let s ← X.part z.2
        let F ← addList s.F z.1
        pure (X.set z.2 { s with F := F })) : Except String T) = .ok v ↔
      (match (addsOf X h).add z.2 z.1 with
        | none => (.error "K9.claim-added" : Except String T)
        | some u => .ok u) = .ok v := by
  simp only [addsOf, addAt, Lens.part, bind, Except.bind]
  cases hz : X.get? z.2 with
  | none => simp [there]
  | some s =>
    simp only [there, Option.bind]
    cases ha : addList s.F z.1 with
    | ok G =>
      rw [addList_older _ _ _ ha]
      simp [pure, Except.pure]
    | error e =>
      cases hb : addAll s.F z.1 with
      | none => simp
      | some G =>
        have := addList_newer _ _ _ hb (hm s hz)
        rw [ha] at this
        cases this

/-- One way, without a premise on marks. -/
theorem laid_yes (X : Lens T) (h : LensOk X) (z : List Claim × T) (v : T)
    (hy : ((do
        let s ← X.part z.2
        let F ← addList s.F z.1
        pure (X.set z.2 { s with F := F })) : Except String T) = .ok v) :
    (addsOf X h).add z.2 z.1 = some v := by
  simp only [Lens.part, bind, Except.bind] at hy
  simp only [addsOf, addAt]
  cases hz : X.get? z.2 with
  | none => simp [hz, there] at hy
  | some s =>
    simp only [hz, there] at hy
    cases ha : addList s.F z.1 with
    | error e => simp [ha] at hy
    | ok G =>
      simp only [ha, pure, Except.pure] at hy
      injection hy with hy'
      simp [Option.bind, addList_older _ _ _ ha, hy']

/-- **A yes of K9.adds over gather is a yes of "made first, then added", to the same state.** -/
theorem adds_yes (X : Lens T) (h : LensOk X) (p : Where) (piece : Nat) (what : String)
    (ws : T → List Window) (cut : List (Nat × String)) (runs : List (RunOf T)) (t : T)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (v : T)
    (hy : (adds (Cl := Cl) X p piece what (gather ws cut runs)).decide t rs gs = .ok v) :
    madeThenAdded (addsOf X h) (runs.map (guarded ws cut)) t = .ok v := by
  rw [adds_decide, gather_eq] at hy
  unfold madeThenAdded
  simp only [bind, Except.bind] at hy
  cases h1 : X.part t with
  | error e => simp [h1] at hy
  | ok s₀ =>
    simp only [h1] at hy
    cases h2 : need "K9.draw-has-run" s₀.L.handed with
    | error e => simp [h2] at hy
    | ok _ =>
      simp only [h2] at hy
      cases hg : gatherFrom (runs.map (guarded ws cut)) 0 t with
      | error e => simp [hg] at hy
      | ok z =>
        simp only [hg] at hy
        simp only [laid_yes X h z v hy]

/-- **(4)** Behind K9.adds' two tests in front (a segment is open; the draw has run), and where
there is a mark behind the gathering. -/
theorem adds_is_madeThen (X : Lens T) (h : LensOk X) (p : Where) (piece : Nat) (what : String)
    (ws : T → List Window) (cut : List (Nat × String)) (runs : List (RunOf T)) (t : T)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (s₀ : Part)
    (h0 : X.get? t = some s₀) (hd : s₀.L.handed = true)
    (hm : MarkedBehind X (runs.map (guarded ws cut)) t) (v : T) :
    (adds (Cl := Cl) X p piece what (gather ws cut runs)).decide t rs gs = .ok v ↔
      madeThenAdded (addsOf X h) (runs.map (guarded ws cut)) t = .ok v := by
  rw [adds_decide, gather_eq]
  unfold madeThenAdded
  simp only [Lens.part, h0, there, need, hd, bind, Except.bind, if_true]
  cases hg : gatherFrom (runs.map (guarded ws cut)) 0 t with
  | error e => simp
  | ok z => exact laid_iff X h z v fun s hs => hm z s hg hs

end VerifiableInference.Desc.K9
