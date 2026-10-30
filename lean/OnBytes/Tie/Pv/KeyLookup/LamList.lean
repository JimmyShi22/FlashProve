-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/KeyLookup/LamList.lean: the list Λ is, row by row, the list `lookupList` of a
lookup's rounds, for all sizes: a theorem for every public record.

It imports both sides: Cb/Pv/KeyLookup/Lam.lean (no file of the port) and
OnBytes/Params/PlanListsSum.lean. `lookupList s x` is no part of the program: it is a pure list
written for proofs, and that file proves of it (`runs_lookup`) that the planner's routine
`planLookup`, wherever it ends well, adds exactly that list's rounds.

  `specOf s S r`   the port's round (`RoundSpec`: name, kind of error, bound, draws, bytes) of a row
                   r of Λ. WHAT IT READS OF THE ROW, AND NO MORE: the kind, always; the
                   count c at LKP and PSC Y; the column `sent` at PSC round (the port's round of a
                   polynomial of a degree below `sent`) and at PSC values. IT READS THE
                   COLUMN n NOWHERE, and it does not call `LRow.short`: that the port's bytes are 24
                   for each scalar of the row's short form, and its draws the row's n, is
                   no statement of this file (it is tested in a file that is not in this library).
  `sizeOfPub S`    the planner's sizes of the public record.
  `lam_list`       UNDER pl ≠ 0 and parts ≠ [] (public numbers): (Lam q S).map (specOf s S) =
                   lookupList s (sizeOfPub S), for every setting s and every q (q = 0 too: the
                   map does not read n). It pins the list's length, order and kinds, and the columns
                   named above.
                   `sizeOfPub S` writes the live planes as pl; the port's caller writes «all planes
                    live» as 0: the two are one record where pl < 2 ^ mu, as at the key.
  `pairOf`, `spec_bound`, `pair_rule`   THE RULE FOR ERRORS, for every public record: each row's
                    round has the bound `Bound.ratio a b` (none: a silent round), with (a, b) :=
                    `pairOf`, and at
                   q := the setting's |E|: c · b = a · n.
Not claimed: that the chain's own shape is Λ (Cb/Pv/KeyLookup/Lam1Short.lean); that `planLookup`
ends well at any sizes; anything on whether a bound is right; the shift (the list has no row for
it).

-/
import Cb.Pv.KeyLookup.Lam
import OnBytes.Params.PlanListsSum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open OnBytes OnBytes.Params

/-- The port's round of a row. -/
def specOf (s : Setting) (S : Pub) (r : LRow) : RoundSpec :=
  match r.kind with
  | .lkp => .said "LKP" .field (Bound.ratio r.c s.cardE) { drawE := 1, priced := .callersWord } 0 0
      0
  | .eps => pscEpsilon s
  | .var => pscVariable s r.sent
  | .y => pscY s r.c
  | .vals => .silent "PSC values" (24 * r.sent) 0
  | .join => .said "JOIN" .field (fieldError s S.mu) { drawE := S.mu, priced := .roundItself } 0 0 0
  | .line => lineRound s
  | .zero =>
    .said "ZERO" .field (fieldError s (S.mu + S.d)) { drawE := S.mu + S.d, priced := .roundItself }
        0 0 0

/-- The planner's sizes. -/
def sizeOfPub (S : Pub) : LookupSize := { d := S.d, mu := S.mu, live := S.pl, parts := S.parts }

variable (s : Setting) (S : Pub) (q : ℕ)

theorem psc_spec_y (deg : List ℕ) (dY vals : ℕ) :
    (psc q deg (some (dY, vals))).map (specOf s S) =
      pscList s { degree := deg, degreeY := dY, values := vals } := by
  simp [psc, pscList, specOf, List.map_map, Function.comp_def]

theorem psc_spec_none (deg : List ℕ) :
    (psc q deg none).map (specOf s S) = pscList s { degree := deg, withY := false } := by
  simp [psc, pscList, specOf, List.map_map, Function.comp_def]

/-- the port's levels from level l on, as a list over a range -/
theorem treeList_eq (more : ℕ) : ∀ fuel l, treeList s more fuel l =
    (List.range fuel).flatMap fun k =>
      pscList s { degree := List.replicate (l + k + more) 3 } ++ [lineRound s]
  | 0, _ => rfl
  | fuel + 1, l => by
    rw [treeList, treeList_eq more fuel (l + 1), List.range_succ_eq_map, List.flatMap_cons,
      List.flatMap_map]
    simp [Nat.add_assoc, Nat.add_comm 1]

theorem tree_spec (more levels : ℕ) :
    (tree q more levels).map (specOf s S) = treeList s more levels 0 := by
  rw [treeList_eq, tree, List.map_flatMap]
  refine List.flatMap_congr fun l _ => ?_
  rw [List.map_append, psc_spec_y, Nat.zero_add, Nat.add_comm more l]
  rfl

theorem const_flat {α : Type} (n : ℕ) (l : List α) :
    ((List.range n).flatMap fun _ => l) = (List.replicate n l).flatten := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map,
      List.replicate_succ,
      List.flatten_cons]; exact congrArg _ ih

/-- The list is `lookupList`, row by row. -/
theorem lam_list (hp : S.pl ≠ 0) (hm : S.parts ≠ []) :
    (Lam q S).map (specOf s S) = lookupList s (sizeOfPub S) := by
  have e1 : lookupLive (sizeOfPub S) = S.pl := by simp [lookupLive, sizeOfPub, hp]
  have e2 : lookupParts (sizeOfPub S) = S.parts := by simp [lookupParts, sizeOfPub, hm]
  have e3 : sumT (S.parts.map (2 ^ ·)) = S.allKeys := by
    unfold sumT Pub.allKeys
    rw [foldl_add, Nat.zero_add]
  unfold lookupList
  rw [e1, e2, e3]
  simp only [Lam, lamHead, lamParts, lamJoin, lamKeys, lamTable, lamClo, lamZero, lamBits,
      List.map_append,
    List.map_flatMap, psc_spec_y, psc_spec_none, tree_spec, const_flat, List.map_cons, List.map_nil]
  simp [specOf, sizeOfPub, Pub.m, List.flatMap_def, List.append_assoc, psc_spec_y]

/-- The port's pair (a, b) of a row: its round's bound is a / b; none: a silent round. Q: the
setting's number of elements. -/
def pairOf (Q : ℕ) (r : LRow) : Option (ℕ × ℕ) :=
  match r.kind with
  | .vals => none
  | .y => some (r.c, Q - 1)
  | .join => some (S.mu, Q)
  | .zero => some (S.mu + S.d, Q)
  | .var => some (r.sent - 1, Q)
  | .eps | .line => some (1, Q)
  | .lkp => some (r.c, Q)

/-- Each row's round has its pair's ratio as its bound. -/
theorem spec_bound (r : LRow) :
    (match pairOf S s.cardE r with
      | none => ∃ n b a, specOf s S r = .silent n b a
      | some (a, b) => ∃ n w d x y z, specOf s S r = .said n w (Bound.ratio a b) d x y z) := by
  rcases r with ⟨k, sent, n, c⟩
  cases k <;> simp [pairOf, specOf, pscEpsilon, pscVariable, pscY, lineRound, fieldError,
      fieldErrorNonzero]

/-- THE RULE FOR ERRORS: c · b = a · n at every row of the list, at q elements. -/
theorem pair_rule : ∀ r ∈ Lam q S,
    (match pairOf S q r with
      | none => r.n = 1 ∧ r.c = 0
      | some (a, b) => r.c * b = a * r.n) := by
  have hpow : ∀ k, k * q ^ (k - 1) * q = k * q ^ k := by
    intro k
    cases k with
    | zero => simp
    | succ k => rw [Nat.add_sub_cancel, Nat.mul_assoc, ← pow_succ]
  have hpsc : ∀ deg y, ∀ r ∈ psc q deg y,
      (match pairOf S q r with
        | none => r.n = 1 ∧ r.c = 0
        | some (a, b) => r.c * b = a * r.n) := by
    intro deg y r hr
    unfold psc at hr
    rcases List.mem_append.1 hr with hr | hr
    · rcases List.mem_cons.1 hr with rfl | hr
      · simp [pairOf]
      · obtain ⟨g, _, rfl⟩ := List.mem_map.1 hr
        simp [pairOf]
    · rcases y with _ | ⟨dY, vals⟩
      · simp at hr
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
        rcases hr with rfl | rfl <;> simp [pairOf]
  have htree : ∀ more levels, ∀ r ∈ tree q more levels,
      (match pairOf S q r with
        | none => r.n = 1 ∧ r.c = 0
        | some (a, b) => r.c * b = a * r.n) := by
    intro more levels r hr
    obtain ⟨l, _, hr⟩ := List.mem_flatMap.1 hr
    rcases List.mem_append.1 hr with hr | hr
    · exact hpsc _ _ r hr
    · rw [List.mem_singleton.1 hr]
      simp [pairOf]
  intro r hr
  simp only [Lam, lamHead, lamParts, lamJoin, lamKeys, lamTable, lamClo, lamZero, lamBits,
      List.mem_append,
    List.mem_flatMap, List.mem_singleton] at hr
  rcases hr with ((((((((rfl | hr) | ⟨_, _, hr⟩) | ⟨_, _, hr⟩) | rfl) | ⟨_, _, hr⟩) | hr) | hr) |
      rfl) | hr
  · simp [pairOf]
  · exact hpsc _ _ r hr
  · exact hpsc _ _ r hr
  · exact hpsc _ _ r hr
  · simpa [pairOf] using hpow S.mu
  · exact htree _ _ r hr
  · exact htree _ _ r hr
  · exact hpsc _ _ r hr
  · simpa [pairOf] using hpow (S.mu + S.d)
  · exact hpsc _ _ r hr

end Lk6

#print axioms Lk6.lam_list
#print axioms Lk6.spec_bound
#print axioms Lk6.pair_rule
