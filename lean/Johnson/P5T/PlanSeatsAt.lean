-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5T/PlanSeatsAt.lean: what the maker of the first chain's seats (`planSeats`,
Johnson/P5T/PlanSeats.lean) reads of the public part of the IOP as written in Lean; and the roots in
front of a round by a walk over runs. Definitions and statements with their proofs.

Why. Tests on the list of rounds read numbers that are made of `planSeats Z dl`. To state such a
test at written values, the maker has to stand at letters that written values can fill.

  `rootsIn es k`, `rootsBefore_entries`: of a declared round the maker reads its entry's number of
    roots alone.
  `planSeatsBy rb c S`: the maker's own text at three letters; `planSeatsAt c S es`: at a list of
    entries.
  `planSeats_at`: **the tie**: `planSeats Z dl` is `planSeatsAt` at the first chain's sendings
    (`Z.made.proof.1`), the shape of the request's own rounds (`Z.first.shape`) and the declared
    rounds' entries. Nothing else of Z is read.
  `flatMap_same`, `planSeatsBy_congr`: of rb the values in front of the sendings alone are read.
  `rootsIn_append`, `rootsIn_replicate`; `rootsRuns recs runs k`; `rootsIn_unrun`: where the rounds
    are kept as runs of distinct rounds (`unrunR`, Johnson/G/DryKeyLit.lean), the walk over the runs
    gives what the unrolled list gives. General: nothing is evaluated.
  `rooted recs runs pos`, `sumBelow L b`; `sumBelow_append`, `sumBelow_of_ge`, `sumBelow_range`,
    `rooted_ge`; `rootsRuns_rooted`: the roots in front of a round are those of the rounds with a
    root in front of it: so ONE walk over the runs, which lists these rounds, serves every round.

Limits. The maker swallows faults: a sending whose trees cannot be laid yields no seat, and a label
that is not read yields seats without a role. Nothing here says that this does not happen at a
value. Nothing on soundness.
-/
import Johnson.P5T.PlanSeats
import Johnson.G.DryKeyLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5T
open Johnson.G

/-! ## 1 The three things that the seats' maker reads -/

/-- The roots that the first k of a list of entries declare. -/
def rootsIn (es : List Fmt.Entry) (k : Nat) : Nat := ((es.take k).map (·.roots)).sum

theorem rootsBefore_entries (dl : List Fmt.DeclaredRound) (k : Nat) :
    rootsBefore dl k = rootsIn (dl.map (·.entry)) k := by
  unfold rootsBefore rootsIn
  rw [← List.map_take, List.map_map]
  rfl

/-- `planSeats`' own text, at three letters. rb k: the roots that the first k rounds declare. c: the
first chain's codes and sendings. S: the shape of the request's own rounds. -/
def planSeatsBy (rb : Nat → Nat) (c : ChainSends) (S : OnBytes.Params.ReqShape) : List PSeat :=
  let groups := (OnBytes.reqGroups S).toList
  c.sends.zipIdx.flatMap fun s =>
    match OnBytes.layTrees c.codes s.1.sent.toArray with
    | none => []
    | some lay =>
      let seg := segOf (groups.length + 1) 16 s.1.label
      let roles := match seg with
        | some (l, m) => rolesOf S groups l m
        | none => []
      (List.range s.1.sent.length).map fun i =>
        { label := s.1.label, send := s.2, seg := seg, idx := i,
          j := rb (s.1.entry - 1) + lay.tree.getD i 0, t := lay.part.getD i 0,
          shape := (s.1.sent.getD i default).shape, role := roles.getD i .other }

/-- The same at a list of entries. -/
def planSeatsAt (c : ChainSends) (S : OnBytes.Params.ReqShape) (es : List Fmt.Entry) :
    List PSeat := planSeatsBy (rootsIn es) c S

/-- **The tie**: the seats' maker reads of the public part the first chain's sendings and the shape
of the request's own rounds, and of the declared rounds their entries, alone. -/
theorem planSeats_at (Z : ProofFile.Pub) (dl : List Fmt.DeclaredRound) :
    planSeats Z dl = planSeatsAt Z.made.proof.1 Z.first.shape (dl.map (·.entry)) := by
  unfold planSeats planSeatsAt planSeatsBy
  simp only [rootsBefore_entries]
  rfl

theorem flatMap_same {α β : Type} {f g : α → List β} : ∀ (l : List α),
    (∀ a ∈ l, f a = g a) → l.flatMap f = l.flatMap g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons, h a List.mem_cons_self,
      flatMap_same l fun b hb => h b (List.mem_cons_of_mem a hb)]

/-- Of rb the maker reads the values in front of the sendings alone. -/
theorem planSeatsBy_congr {rb rb' : Nat → Nat} (c : ChainSends) (S : OnBytes.Params.ReqShape)
    (h : ∀ s ∈ c.sends, rb (s.entry - 1) = rb' (s.entry - 1)) :
    planSeatsBy rb c S = planSeatsBy rb' c S := by
  unfold planSeatsBy
  dsimp only
  refine flatMap_same _ fun s hs => ?_
  have a := List.mem_zipIdx hs
  have hm : s.1 ∈ c.sends := by
    rw [a.2.2]
    exact List.getElem_mem _
  rw [h s.1 hm]

/-! ## 2 The roots in front of a round, where the rounds are kept as runs -/

theorem rootsIn_append (a b : List Fmt.Entry) (k : Nat) :
    rootsIn (a ++ b) k = rootsIn a k + rootsIn b (k - a.length) := by
  unfold rootsIn
  rw [List.take_append, List.map_append, List.sum_append]

theorem rootsIn_replicate (n k : Nat) (e : Fmt.Entry) :
    rootsIn (List.replicate n e) k = min k n * e.roots := by
  unfold rootsIn
  rw [List.take_replicate, List.map_replicate, List.sum_replicate_nat]

/-- The roots that the first k rounds declare, by a walk over the runs: none is unrolled. -/
def rootsRuns (recs : List (Fmt.Round × List Fmt.Stored)) : List (Nat × Nat) → Nat → Nat
  | [], _ => 0
  | x :: l, k =>
    match recs[x.2]? with
    | none => rootsRuns recs l k
    | some r => min k x.1 * r.1.entry.roots + rootsRuns recs l (k - x.1)

/-- **The walk over the runs gives what the unrolled list gives.** General: nothing is evaluated. -/
theorem rootsIn_unrun (recs : List (Fmt.Round × List Fmt.Stored)) :
    ∀ (runs : List (Nat × Nat)) (k : Nat),
      rootsIn ((unrunR recs runs).map (·.1.entry)) k = rootsRuns recs runs k
  | [], k => by simp [unrunR, rootsIn, rootsRuns]
  | x :: l, k => by
    have e : unrunR recs (x :: l) =
        (recs[x.2]?).elim [] (List.replicate x.1) ++ unrunR recs l := by
      unfold unrunR
      rw [List.flatMap_cons]
    rw [e, List.map_append, rootsIn_append, rootsIn_unrun recs l, rootsRuns]
    cases h : recs[x.2]? with
    | none => simp [rootsIn]
    | some r => simp [List.map_replicate, rootsIn_replicate]

/-! ## 3 The rounds that declare a root, in one walk over the runs -/

/-- The rounds that declare a root: for each its number, from pos on, and how many it declares. -/
def rooted (recs : List (Fmt.Round × List Fmt.Stored)) : List (Nat × Nat) → Nat → List (Nat × Nat)
  | [], _ => []
  | x :: l, pos =>
    match recs[x.2]? with
    | none => rooted recs l pos
    | some r =>
      (if r.1.entry.roots = 0 then []
        else (List.range x.1).map fun i => (pos + i, r.1.entry.roots)) ++
        rooted recs l (pos + x.1)

/-- The second numbers of the pairs whose first number is below b, added up. -/
def sumBelow (L : List (Nat × Nat)) (b : Nat) : Nat :=
  ((L.filter fun y => decide (y.1 < b)).map (·.2)).sum

theorem sumBelow_append (L M : List (Nat × Nat)) (b : Nat) :
    sumBelow (L ++ M) b = sumBelow L b + sumBelow M b := by
  unfold sumBelow
  rw [List.filter_append, List.map_append, List.sum_append]

theorem sumBelow_of_ge {L : List (Nat × Nat)} {b : Nat} (h : ∀ y ∈ L, b ≤ y.1) :
    sumBelow L b = 0 := by
  unfold sumBelow
  rw [List.filter_eq_nil_iff.2 fun y hy => by simpa using h y hy]
  rfl

theorem sumBelow_range (pos c k : Nat) : ∀ n : Nat,
    sumBelow ((List.range n).map fun i => (pos + i, c)) (pos + k) = min k n * c
  | 0 => by simp [sumBelow]
  | n + 1 => by
    rw [List.range_succ, List.map_append, sumBelow_append, sumBelow_range pos c k n]
    by_cases h : n < k
    · have e : sumBelow ([n].map fun i => (pos + i, c)) (pos + k) = c := by
        simp [sumBelow, h]
      rw [e, Nat.min_eq_right (Nat.le_of_lt h), Nat.min_eq_right h, Nat.succ_mul]
    · have e : sumBelow ([n].map fun i => (pos + i, c)) (pos + k) = 0 := by
        simp [sumBelow, h]
      have hk : k ≤ n := Nat.le_of_not_lt h
      rw [e, Nat.min_eq_left hk, Nat.min_eq_left (Nat.le_succ_of_le hk), Nat.add_zero]

theorem rooted_ge (recs : List (Fmt.Round × List Fmt.Stored)) :
    ∀ (runs : List (Nat × Nat)) (pos : Nat) (y : Nat × Nat), y ∈ rooted recs runs pos → pos ≤ y.1
  | [], _, _, h => by cases h
  | x :: l, pos, y, h => by
    rw [rooted] at h
    cases hr : recs[x.2]? with
    | none =>
      rw [hr] at h
      exact rooted_ge recs l pos y h
    | some r =>
      rw [hr] at h
      rcases List.mem_append.1 h with h1 | h1
      · split at h1
        · cases h1
        · obtain ⟨i, _, rfl⟩ := List.mem_map.1 h1
          exact Nat.le_add_right _ _
      · exact Nat.le_trans (Nat.le_add_right _ _) (rooted_ge recs l (pos + x.1) y h1)

/-- **The roots in front of a round are those of the rounds with a root in front of it.** General:
nothing is evaluated. -/
theorem rootsRuns_rooted (recs : List (Fmt.Round × List Fmt.Stored)) :
    ∀ (runs : List (Nat × Nat)) (pos k : Nat),
      rootsRuns recs runs k = sumBelow (rooted recs runs pos) (pos + k)
  | [], _, _ => rfl
  | x :: l, pos, k => by
    rw [rootsRuns, rooted]
    cases hr : recs[x.2]? with
    | none => exact rootsRuns_rooted recs l pos k
    | some r =>
      show min k x.1 * r.1.entry.roots + rootsRuns recs l (k - x.1) = _
      rw [sumBelow_append, rootsRuns_rooted recs l (pos + x.1) (k - x.1)]
      have t : sumBelow (rooted recs l (pos + x.1)) (pos + x.1 + (k - x.1)) =
          sumBelow (rooted recs l (pos + x.1)) (pos + k) := by
        by_cases hk : x.1 ≤ k
        · rw [show pos + x.1 + (k - x.1) = pos + k by omega]
        · rw [sumBelow_of_ge fun y hy => by
              have := rooted_ge recs l (pos + x.1) y hy
              omega,
            sumBelow_of_ge fun y hy => by
              have := rooted_ge recs l (pos + x.1) y hy
              omega]
      rw [t]
      congr 1
      split
      · rename_i h0
        rw [h0, Nat.mul_zero]
        rfl
      · exact (sumBelow_range pos _ k x.1).symm

end P5T

#print axioms P5T.rootsBefore_entries
#print axioms P5T.planSeats_at
#print axioms P5T.flatMap_same
#print axioms P5T.planSeatsBy_congr
#print axioms P5T.rootsIn_append
#print axioms P5T.rootsIn_replicate
#print axioms P5T.rootsIn_unrun
#print axioms P5T.sumBelow_append
#print axioms P5T.sumBelow_of_ge
#print axioms P5T.sumBelow_range
#print axioms P5T.rooted_ge
#print axioms P5T.rootsRuns_rooted
