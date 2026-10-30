-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Sends/OneOfRuns.lean: sendsFrom's INNER ROUTINE `oneOf` (Johnson/G/SendsListed.lean)
AT A PLAN THAT IS WRITTEN AS RUNS: A TWIN THAT WALKS THE RUNS AND NEVER LAYS THE ROUNDS OUT, and the
equation. General in the written plan; nothing is evaluated.

  `oneOfR`: oneOf's own text with three things exchanged: the array of all rounds is gone; the
    entries "SEND seed" with their numbers are picked by `seedsR`; the round behind each is read by
    `getR` (Johnson/Unfolds/RunsWalk.lean).
  **`oneOf_runs`**: oneOf file ch codes l L.plan = oneOfR file ch codes l (valRuns L.recs L.runs).
  `oneOfN`: the same IN ONE WALK (`seedsN`): each entry "SEND seed" comes with the round behind it,
    where oneOfR reads the round behind each by a walk of its own.
  **`oneOf_walk`**: oneOf file ch codes l L.plan = oneOfN file ch codes l (valRuns L.recs L.runs).
Limits. NO PROGRAM CALLS oneOfR | oneOfN: they stand in statements alone. Nothing on soundness.

-/
import Johnson.G.SendsListed
import Johnson.Unfolds.RunsWalk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G

open OnBytes OnBytes.Params
open Johnson.G.Runs (valRuns unrunG)
open Johnson.Unfolds (seedsR getR seedsN seedsN_zero zipIdx_filter_unrunG getElem?_unrunG)
open VerifiableInference.Number.ByRuns (Lit)

/-- oneOf's text, along the runs. -/
def oneOfR (file : String) (ch : Nat) (codes : Codes) (l : List Listed)
    (vr : List (Nat × PlanRound)) : Except String ChainSends := do
  let seeds := seedsR (fun r : PlanRound => r.entry.name == "SEND seed") 0 vr
  unless seeds.length == l.length do
    throw s!"{file} {ch}: {l.length} sendings listed, {seeds.length} entries SEND seed"
  let out ← (seeds.zip l).mapM fun (r, s) => do
    unless treesOf codes s.sent.toArray == some r.1.entry.roots do
      throw s!"{file} {ch}, entry {r.2 + 1} ({s.label}): the trees are not the entry's roots"
    match getR vr (r.2 + 1) with
    | some b => pure (⟨r.2 + 1, s.label, s.sent, r.1.entry, b.entry⟩ : Sending)
    | none => throw s!"{file} {ch}, entry {r.2 + 1}: no entry behind it"
  pure ⟨file, ch, codes, out⟩

/-- **At a plan written as runs the inner routine is its twin.** -/
theorem oneOf_runs (file : String) (ch : Nat) (codes : Codes) (l : List Listed) (L : Lit) :
    oneOf file ch codes l L.plan = oneOfR file ch codes l (valRuns L.recs L.runs) := by
  unfold oneOf oneOfR
  have e1 : L.plan.rounds.zipIdx.filter (fun r => r.1.entry.name == "SEND seed") =
      seedsR (fun r : PlanRound => r.entry.name == "SEND seed") 0 (valRuns L.recs L.runs) :=
    zipIdx_filter_unrunG (fun r : PlanRound => r.entry.name == "SEND seed") L.recs L.runs 0
  have e2 : ∀ j, L.plan.rounds.toArray[j]? = getR (valRuns L.recs L.runs) j := fun j => by
    rw [List.getElem?_toArray]
    exact getElem?_unrunG L.recs L.runs j
  simp only [e1, e2]
  rfl

/-- oneOf's text, along the runs, IN ONE WALK: each entry "SEND seed" comes with the round behind
it. -/
def oneOfN (file : String) (ch : Nat) (codes : Codes) (l : List Listed)
    (vr : List (Nat × PlanRound)) : Except String ChainSends := do
  let seeds := seedsN (fun r : PlanRound => r.entry.name == "SEND seed") 0 vr
  unless seeds.length == l.length do
    throw s!"{file} {ch}: {l.length} sendings listed, {seeds.length} entries SEND seed"
  let out ← (seeds.zip l).mapM fun (r, s) => do
    unless treesOf codes s.sent.toArray == some r.1.1.entry.roots do
      throw s!"{file} {ch}, entry {r.1.2 + 1} ({s.label}): the trees are not the entry's roots"
    match r.2 with
    | some b => pure (⟨r.1.2 + 1, s.label, s.sent, r.1.1.entry, b.entry⟩ : Sending)
    | none => throw s!"{file} {ch}, entry {r.1.2 + 1}: no entry behind it"
  pure ⟨file, ch, codes, out⟩

theorem mapM_map' {α β γ : Type} (f : α → β) (g : β → Except String γ) : ∀ l : List α,
    (l.map f).mapM g = l.mapM fun a => g (f a)
  | [] => rfl
  | a :: l => by
    rw [List.map_cons, List.mapM_cons, List.mapM_cons, mapM_map' f g l]

theorem oneOfR_walk (file : String) (ch : Nat) (codes : Codes) (l : List Listed)
    (vr : List (Nat × PlanRound)) : oneOfR file ch codes l vr = oneOfN file ch codes l vr := by
  unfold oneOfR oneOfN
  simp only [seedsN_zero, List.length_map, List.zip_map_left, mapM_map']
  rfl

/-- **At a plan written as runs the inner routine is ONE WALK along the runs.** -/
theorem oneOf_walk (file : String) (ch : Nat) (codes : Codes) (l : List Listed) (L : Lit) :
    oneOf file ch codes l L.plan = oneOfN file ch codes l (valRuns L.recs L.runs) :=
  (oneOf_runs file ch codes l L).trans (oneOfR_walk file ch codes l _)

end Johnson.G

#print axioms Johnson.G.oneOfR_walk
#print axioms Johnson.G.oneOf_walk
#print axioms Johnson.G.oneOf_runs
