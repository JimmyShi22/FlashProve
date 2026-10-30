-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/OpensLaw.lean: `Thread.opensAvailable`
(Honest/Thread/OneState.lean) as a test on a list of pairs: of each sub-protocol its rounds and how
many oracle messages it declares; and one pass over that list that gives the test at every border.
General in the thread. Definitions with code, statements and proofs.

  `roundsTrees`   of a sub-protocol: its rounds and the number of its oracle messages
  `handR`, `opensR`   the sources in hand at a border, and the test there, on such a list
  `decls_rounds`, `trees_rounds`   what the test reads of a list of sub-protocols is read off
                 `roundsTrees`
  `opensAvailable_eq`   `opensAvailable` at a thread is `opensR` at its list
  `rounds_alike`   two lists that are alike (`Alike₂`, Johnson/AtFull/ProofPlan/PlanAlike.lean) have
                 one such list
  `handR_mono`   what is in hand at a border is in hand at every later one
  `opensEach`    the one pass: each sub-protocol opens what is in hand behind it
  `opensR_of_each`   the pass gives the test at every border
  `opens_of_alike`   so a thread whose list is alike to a list that passes has `opensAvailable` at
                 every border

Why one pass. Each border is a test of its own: what is in hand grows with the border, and what is
asked grows too. But a tree in hand behind a sub-protocol stays in hand, so a list that passes at
each sub-protocol passes at every border, of which the first chain has some hundreds.

Limits. A test on public lists: no run, no table. It says that a source is in hand, not what its table
holds, and nothing of a table's depth (`DepthsAt`, same file of the library). Nothing on completeness,
on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.Thread.OneState
import Johnson.AtFull.ProofPlan.PlanAlike

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open VerifiableInference.Desc (Block Alike₂)

/-- Of a sub-protocol: its rounds, and how many oracle messages it declares. -/
def roundsTrees {S Cl : Type} (b : Block S Cl) : List Fmt.DeclaredRound × Nat :=
  (b.rounds, (b.oracles.flatMap id).length)

/-- What is in hand at border n: the trees taken over, and the own trees sent in front of it. -/
def handR (taken : List Fmt.TreeSource) (R : List (List Fmt.DeclaredRound × Nat)) (n : Nat) :
    List Fmt.TreeSource :=
  taken ++ (List.range ((R.take n).map (·.2)).sum).map Fmt.TreeSource.own

/-- `Thread.opensAvailable` on a list of these. -/
def opensR (taken : List Fmt.TreeSource) (R : List (List Fmt.DeclaredRound × Nat)) (n : Nat) : Bool :=
  ((R.take n).flatMap (·.1)).all fun d => d.opens.all fun o => decide (o.2 ∈ handR taken R n)

theorem decls_rounds {S Cl : Type} : ∀ (bs : List (Block S Cl)) (n : Nat),
    declsTo bs n = ((bs.map roundsTrees).take n).flatMap (·.1)
  | [], _ => by simp [declsTo]
  | _ :: _, 0 => by simp [declsTo]
  | b :: bs, n + 1 => by
    have ih := decls_rounds bs n
    unfold declsTo at ih ⊢
    simp only [List.map_cons, List.take_succ_cons, List.flatMap_cons]
    rw [ih]
    rfl

theorem trees_rounds {S Cl : Type} : ∀ (bs : List (Block S Cl)) (n : Nat),
    treesTo bs n = (((bs.map roundsTrees).take n).map (·.2)).sum
  | [], _ => by simp [treesTo]
  | _ :: _, 0 => by simp [treesTo]
  | b :: bs, n + 1 => by
    have ih := trees_rounds bs n
    unfold treesTo at ih ⊢
    simp only [List.map_cons, List.take_succ_cons, List.flatMap_cons, List.length_append,
      List.sum_cons]
    rw [ih]
    rfl

/-- **`opensAvailable` at a thread is `opensR` at its list.** -/
theorem opensAvailable_eq {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)
    (n : Nat) : T.opensAvailable n = opensR T.taken (T.bs.map roundsTrees) n := by
  unfold Thread.opensAvailable opensR handR Thread.hand
  rw [decls_rounds, trees_rounds]

/-- Two lists that are alike have one list of rounds and counts. -/
theorem rounds_alike {S Cl S' Cl' : Type} {l : List (Block S Cl)} {l' : List (Block S' Cl')}
    (h : List.Forall₂ Alike₂ l l') : l.map roundsTrees = l'.map roundsTrees := by
  induction h with
  | nil => rfl
  | @cons b b' l l' hb _ ih =>
    simp only [List.map_cons, ih]
    unfold roundsTrees
    rw [hb.2.1, hb.2.2.1]

theorem sum_take_le (f : List Fmt.DeclaredRound × Nat → Nat) :
    ∀ (R : List (List Fmt.DeclaredRound × Nat)) (n n' : Nat), n ≤ n' →
      ((R.take n).map f).sum ≤ ((R.take n').map f).sum
  | [], _, _, _ => by simp
  | _ :: _, 0, n', _ => by simp
  | _ :: _, _ + 1, 0, h => by omega
  | x :: R, n + 1, n' + 1, h => by
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
    have := sum_take_le f R n n' (by omega)
    omega

/-- **What is in hand at a border is in hand at every later one.** -/
theorem handR_mono {taken : List Fmt.TreeSource} {R : List (List Fmt.DeclaredRound × Nat)} {n n' : Nat}
    (h : n ≤ n') {σ : Fmt.TreeSource} (hσ : σ ∈ handR taken R n) : σ ∈ handR taken R n' := by
  unfold handR at hσ ⊢
  rcases List.mem_append.1 hσ with h1 | h1
  · exact List.mem_append_left _ h1
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 h1
    refine List.mem_append_right _ (List.mem_map.2 ⟨i, List.mem_range.2 ?_, rfl⟩)
    exact Nat.lt_of_lt_of_le (List.mem_range.1 hi) (sum_take_le _ R n n' h)

/-- **The one pass**: sub-protocol number j opens what is in hand behind it. -/
def opensEach (taken : List Fmt.TreeSource) (R : List (List Fmt.DeclaredRound × Nat)) : Bool :=
  (List.range R.length).all fun j => (R.getD j ([], 0)).1.all fun d =>
    d.opens.all fun o => decide (o.2 ∈ handR taken R (j + 1))

/-- **The pass gives the test at every border.** -/
theorem opensR_of_each {taken : List Fmt.TreeSource} {R : List (List Fmt.DeclaredRound × Nat)}
    (h : opensEach taken R = true) (n : Nat) : opensR taken R n = true := by
  unfold opensR
  refine List.all_eq_true.2 fun d hd => List.all_eq_true.2 fun o ho => decide_eq_true ?_
  obtain ⟨x, hx, hdx⟩ := List.mem_flatMap.1 hd
  obtain ⟨j, hj, rfl⟩ := List.mem_take_iff_getElem.1 hx
  have hjn : j < n := Nat.lt_of_lt_of_le hj (Nat.min_le_left _ _)
  have hjl : j < R.length := Nat.lt_of_lt_of_le hj (Nat.min_le_right _ _)
  have k := List.all_eq_true.1 h j (List.mem_range.2 hjl)
  rw [List.getD_eq_getElem _ _ hjl] at k
  exact handR_mono hjn (of_decide_eq_true
    (List.all_eq_true.1 (List.all_eq_true.1 k d hdx) o ho))

/-- **A thread whose list is alike to a list that passes has `opensAvailable` at every border.** -/
theorem opens_of_alike {S Cl V W X Pb S' Cl' : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)
    {l : List (Block S' Cl')} (hl : List.Forall₂ Alike₂ l T.bs)
    (h : opensEach T.taken (l.map roundsTrees) = true) (n : Nat) : T.opensAvailable n = true := by
  rw [opensAvailable_eq, ← rounds_alike hl]
  exact opensR_of_each h n

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.opensAvailable_eq
#print axioms ProofFile.Honest.K12.AtFile.rounds_alike
#print axioms ProofFile.Honest.K12.AtFile.handR_mono
#print axioms ProofFile.Honest.K12.AtFile.opensR_of_each
#print axioms ProofFile.Honest.K12.AtFile.opens_of_alike
