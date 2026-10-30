-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Peel/FoPlanAtLook.lean.
The library's list of a lookup's rounds, seen as entries and errors, is the list of
OnBytes/Tie/Pv/Lookup/Port/TwPlanLaw.lean.

OnBytes/Params/PlanListsSum.lean describes the rounds that the planner's lookup adds to a plan as a
list of descriptions (lookupList, runs_lookup). OnBytes/Tie/Pv/Lookup/Port/TwPlanLaw.lean and
OnBytes/Tie/Pv/Lookup/Lists/TwPlanOne.lean describe them as a
list of entries with quotients (lookI; in closed form entN and ratN). This file shows that the two
lists are the same rounds, as far as a round's entry and error go. It is an equation of lists: no
run of the planner occurs in it.

* specSeen s c y: the entry and the error of the round that the description y stands for.
* psc_seen, tree_seen, times_seen, each_seen: a sumcheck, a product tree, a list repeated, a list
  for each member.
* look_seen: (lookupList s x).map (specSeen s c) = (lookI ..).map (said s c).
* forestRounds s c fs: the rounds of the lookup of a group of calls, as rounds of a plan.
* forest_entries, forest_errors: at a size ⟨v' + 1, d, sh⟩, that is with at least 2 keys: their
  entries are the shift's entry, if there is one, and entN; their errors are errOf of the shift's
  quotient, if there is one, and of ratN.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Lists.TwPlanOne
import OnBytes.Params.PlanListsSum

set_option autoImplicit false

namespace TwLaw
open OnBytes OnBytes.Params TwPlan TwErr

/-- The entry and the error of the round that a description stands for. -/
def specSeen (s : Setting) (c : Scope) (y : RoundSpec) : Fmt.Entry × Binary := seen (y.round s c)

section
variable (s : Setting) (c : Scope)

theorem psc_seen (x : PscSize) : (pscList s x).map (specSeen s c) =
    (pscI (s.workOf .field c) (x.degree.map (· - 1)) x.withY x.degreeY x.values).map
      (said s c) := by
  cases hY : x.withY <;>
    simp [pscList, pscI, pscEpsilon, pscVariable, pscY, specSeen, seen, said, RoundSpec.round,
      RoundSpec.bound, errOf, rd, rdNone, fieldError, fieldErrorNonzero, hY, Function.comp_def]

theorem line_seen : specSeen s c (lineRound s) = said s c (lineI (s.workOf .field c)) := by
  simp [lineRound, lineI, specSeen, seen, said, RoundSpec.round, RoundSpec.bound, errOf, rd,
    fieldError]

theorem tree_seen (more : Nat) : ∀ fuel l : Nat, (treeList s more fuel l).map (specSeen s c) =
    (levelsI (s.workOf .field c) more fuel l).map (said s c)
  | 0, _ => rfl
  | fuel + 1, l => by
    have hp := psc_seen s c { degree := List.replicate (l + more) 3 }
    rw [show ({ degree := List.replicate (l + more) 3 } : PscSize).degree.map (· - 1) =
      List.replicate (l + more) 2 from rep3 _] at hp
    show (pscList s { degree := List.replicate (l + more) 3 } ++
      (lineRound s :: treeList s more fuel (l + 1))).map (specSeen s c) =
      (pscI (s.workOf .field c) (List.replicate (l + more) 2) true 2 2 ++
        [lineI (s.workOf .field c)] ++ levelsI (s.workOf .field c) more fuel (l + 1)).map (said s c)
    rw [List.map_append, List.map_cons, hp, line_seen, tree_seen more fuel (l + 1),
      List.map_append, List.map_append, List.append_assoc]
    rfl

variable {s c}

theorem times_seen {A : List RoundSpec} {B : List Item}
    (h : A.map (specSeen s c) = B.map (said s c)) : ∀ n : Nat,
    ((List.replicate n A).flatten).map (specSeen s c) = (timesI B n).map (said s c)
  | 0 => rfl
  | n + 1 => by
    show (A ++ (List.replicate n A).flatten).map (specSeen s c) = (B ++ timesI B n).map (said s c)
    rw [List.map_append, List.map_append, h, times_seen h n]

theorem each_seen {F : Nat → List RoundSpec} {G : Nat → List Item}
    (h : ∀ a, (F a).map (specSeen s c) = (G a).map (said s c)) : ∀ l : List Nat,
    ((l.map F).flatten).map (specSeen s c) = (eachI G l).map (said s c)
  | [] => rfl
  | a :: l => by
    show (F a ++ (l.map F).flatten).map (specSeen s c) = (G a ++ eachI G l).map (said s c)
    rw [List.map_append, List.map_append, h a, each_seen h l]

variable (s c)

/-- The library's list of a lookup's rounds is the list of
OnBytes/Tie/Pv/Lookup/Port/TwPlanLaw.lean. -/
theorem look_seen (x : LookupSize) : (lookupList s x).map (specSeen s c) =
    (lookI (s.workOf .field c) x.shifted
      (sumT ((if x.parts.isEmpty then [x.v] else x.parts).map (2 ^ ·)))
      (if x.live != 0 then x.live else 2 ^ min x.mu 6)
      (if x.parts.isEmpty then [x.v] else x.parts) x.d x.mu).map (said s c) := by
  have p1 := psc_seen s c { degreeY := 3, values := 3 }
  have p2 := psc_seen s c { degreeY := 3, values := 2 }
  have p3 := psc_seen s c {}
  have p4 := psc_seen s c
    { degree := List.replicate x.d 3 ++ List.replicate x.mu 2, withY := false }
  have p5 := psc_seen s c { degree := List.replicate (x.mu + x.d) 3, degreeY := 2, values := 1 }
  rw [show ({ degree := List.replicate x.d 3 ++ List.replicate x.mu 2, withY := false } :
      PscSize).degree.map (· - 1) = List.replicate x.d 2 ++ List.replicate x.mu 1 by
    show (List.replicate x.d 3 ++ List.replicate x.mu 2).map (· - 1) = _
    rw [List.map_append, rep3, rep2]] at p4
  rw [show ({ degree := List.replicate (x.mu + x.d) 3, degreeY := 2, values := 1 } :
      PscSize).degree.map (· - 1) = List.replicate (x.mu + x.d) 2 from rep3 _] at p5
  have q1 : specSeen s c (.said "LKP shift" .field (fieldError s (2 ^ x.d))
      { drawE := 1, priced := .callersWord } 0 0 0) = said s c (shiftI (s.workOf .field c) x.d) :=
          by
    simp [shiftI, shiftN, specSeen, seen, said, RoundSpec.round, RoundSpec.bound, errOf, rd,
      fieldError]
  have q2 : ∀ k : Nat, specSeen s c (.said "LKP" .field (Bound.ratio (k - 1) s.cardE)
      { drawE := 1, priced := .callersWord } 0 0 0) =
      said s c (rd (s.workOf .field c) "LKP" 0 1, (k - 1, 1)) := by
    intro k
    simp [specSeen, seen, said, RoundSpec.round, RoundSpec.bound, errOf, rd]
  have q3 : ∀ (name : String) (k : Nat), specSeen s c (.said name .field (fieldError s k)
      { drawE := k, priced := .roundItself } 0 0 0) =
      said s c (rd (s.workOf .field c) name 0 k, (k, 1)) := by
    intro name k
    simp [specSeen, seen, said, RoundSpec.round, RoundSpec.bound, errOf, rd, fieldError]
  unfold lookupList lookI lookupLive lookupParts
  simp only [List.map_append, List.map_cons, List.map_nil]
  rw [q2, q3, q3, p1, times_seen p2, times_seen p3, each_seen (fun v => tree_seen s c 0 v 0),
    tree_seen, p4, p5]
  cases x.shifted with
  | true => simp [q1]
  | false => simp

/-- The rounds of the lookup of a group of calls, as rounds of a plan. -/
def forestRounds (fs : ForestSize) : List PlanRound :=
  (lookupList s { v := fs.v, d := fs.d, mu := 5, shifted := fs.shifted }).map (·.round s c)

theorem forest_seen (v' d : Nat) (sh : Bool) : (forestRounds s c ⟨v' + 1, d, sh⟩).map seen =
    ((if sh then [shiftI (s.workOf .field c) d] else []) ++
      itemsN (s.workOf .field c) v' d 5 30).map (said s c) := by
  have h := look_seen s c { v := v' + 1, d := d, mu := 5, shifted := sh }
  have e := lookI_one (s.workOf .field c) sh 32 v' d 5
  unfold forestRounds
  rw [List.map_map]
  exact h.trans (congrArg (List.map (said s c)) e)

/-- Their entries. -/
theorem forest_entries (v' d : Nat) (sh : Bool) :
    (forestRounds s c ⟨v' + 1, d, sh⟩).map (·.entry) =
      (if sh then [shiftN (s.workOf .field c)] else []) ++ entN (s.workOf .field c) v' d 5 30 := by
  rw [map_entry, forest_seen, said_fst, List.map_append, items_fst]
  cases sh <;> rfl

/-- Their errors. -/
theorem forest_errors (v' d : Nat) (sh : Bool) :
    (forestRounds s c ⟨v' + 1, d, sh⟩).map (·.error) =
      ((if sh then [(2 ^ d, 1)] else []) ++ ratN v' d 5 30).map (errOf s c) := by
  rw [map_error, forest_seen, said_snd, List.map_append, items_snd]
  cases sh <;> rfl

end
end TwLaw
