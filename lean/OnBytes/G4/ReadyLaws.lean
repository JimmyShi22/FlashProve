-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/G4/ReadyLaws.lean: the public premises of a lookup's run, proved for all public inputs
without a shift.

`Caller.Laws.verify_val` (OnBytes/G4/AnyRun.lean) says what `Lkp.verify` computes at any caller. It
asks facts on the public inputs alone: `Ready S`, and that the plan's entries are `lookupEntries`.
Here these are proved from `S.shifted = false`, `S.ok = true` and `S.mu + S.d ≤ 63`, so that no list
has to be evaluated at a lookup's real size.

Main names:
  `chainEntries_eq`, `treesEntries_eq`, `tieEntries_eq`, `partEntries_eq`: the entries block by
  block are those of the port's rounds.
  `lookupEntries_eq`: the entries of `Lkp.roundsOf`, and then es', are `lookupEntries`.
  `leaves_degrees`: the degrees of the sumcheck on the leaves, in the default order.
  `length_orderBeginning`: an order that begins with different variables below n has length n.
  `ready_of_ok`: `Ready S`, from these three. `small_of_live`: where all planes are real
  (`S.live = 0`) the third follows from `S.ok`.
  `masks_split`: the two ledgers' counts are the port's `Lkp.keyMasks` and `Lkp.allMasks`.
Limits: only lookups without a shift. `lookupEntries_eq` asks 2 ≤ S.planes, which `S.ok` gives
  (`sizes_of_ok`). `S.ok` does NOT give `S.mu + S.d ≤ 63` where not all planes are real: it bounds
  S.d + S.planes, and S.planes is then S.live, which may be as small as 2 at S.mu = 6.


-/
import OnBytes.G4.AnyRun

set_option autoImplicit false

namespace OnBytes.G4

open Blk

/-- The levels l, l + 1, .. of a product tree, n of them: block by block as in the port's rounds. -/
theorem chainEntries_eq (work more : Nat) : ∀ (n l : Nat),
    chainEntries work more l n =
      ((List.range' l n).flatMap fun l =>
        Psc.roundsOf work { degree := List.replicate (l + more) 3 } ++
          [rDraw "LINE" work 1]).map (·.entry)
  | 0, _ => rfl
  | n + 1, l => by
    rw [chainEntries, chainEntries_eq work more n (l + 1), List.range'_succ, List.flatMap_cons,
      List.map_append, List.map_append]
    simp [pscEntries]

/-- A whole product tree. -/
theorem chainEntries_tree (work more levels : Nat) :
    chainEntries work more (levels - levels) levels =
      (Lkp.treeRounds work levels more).map (·.entry) := by
  rw [Nat.sub_self, chainEntries_eq, Lkp.treeRounds, List.range_eq_range']

/-- The key trees of all parts. -/
theorem treesEntries_eq (work : Nat) : ∀ vs : List Nat,
    treesEntries work vs = (vs.flatMap fun v => Lkp.treeRounds work v 0).map (·.entry)
  | [] => rfl
  | v :: vs => by
    rw [treesEntries, treesEntries_eq work vs, chainEntries_tree, List.flatMap_cons,
      List.map_append]

/-- n equal sumchecks in a row. -/
theorem flatMap_const_entries (work : Nat) (x : Psc.Size) (f : Nat → List Fmt.Entry)
    (h0 : f 0 = []) (hs : ∀ n, f (n + 1) = pscEntries work x ++ f n) : ∀ (n l : Nat),
    f n = ((List.range' l n).flatMap fun _ => Psc.roundsOf work x).map (·.entry)
  | 0, _ => h0
  | n + 1, l => by
    rw [hs, flatMap_const_entries work x f h0 hs n (l + 1), List.range'_succ, List.flatMap_cons,
      List.map_append]

/-- The later steps of the tie. -/
theorem tieEntries_eq (work n l : Nat) :
    tieEntries work n = ((List.range' l n).flatMap fun _ =>
      Psc.roundsOf work { degree := [], degreeY := 3, values := 2 }).map (·.entry) :=
  flatMap_const_entries work _ (tieEntries work) rfl (fun _ => rfl) n l

/-- The steps from the product of the parts' roots to each root. -/
theorem partEntries_eq (work n : Nat) :
    partEntries work n = ((List.range n).flatMap fun _ =>
      Psc.roundsOf work { degree := [] }).map (·.entry) := by
  rw [List.range_eq_range']
  exact flatMap_const_entries work _ (partEntries work) rfl (fun _ => rfl) n 0

/-- From the second step on the port's rounds of the tie have two shown values. -/
theorem tieTail_eq (work : Nat) : ∀ (n l : Nat), 1 ≤ l →
    ((List.range' l n).flatMap fun j =>
      Psc.roundsOf work { degree := [], degreeY := 3, values := if j == 0 then 3 else 2 }) =
      (List.range' l n).flatMap fun _ =>
        Psc.roundsOf work { degree := [], degreeY := 3, values := 2 }
  | 0, _, _ => rfl
  | n + 1, l, h => by
    have hl : (l == 0) = false := by
      rw [beq_eq_false_iff_ne]
      omega
    rw [List.range'_succ, List.flatMap_cons, List.flatMap_cons,
      tieTail_eq work n (l + 1) (by omega), hl]
    rfl

/-- The steps of the tie in the port's rounds: the first has three shown values, the others two. -/
theorem tieRounds_eq (work n : Nat) :
    ((List.range (n + 1)).flatMap fun j =>
      Psc.roundsOf work { degree := [], degreeY := 3, values := if j == 0 then 3 else 2 }).map
        (·.entry) =
      pscEntries work { degree := [], withY := true, degreeY := 3, values := 3 } ++
        tieEntries work n := by
  rw [List.range_eq_range', List.range'_succ, List.flatMap_cons, List.map_append,
    tieEntries_eq work n (0 + 1), tieTail_eq work n (0 + 1) (by omega)]
  rfl

/-- The entries of the port's rounds of a lookup without a shift, and then es', block by block. -/
theorem lookupEntries_eq (S : Lkp.Public) (work : Nat) (es' : List Fmt.Entry)
    (hs : S.shifted = false) (hp : 2 ≤ S.planes) :
    (Lkp.roundsOf work S).map (·.entry) ++ es' = lookupEntries S work es' := by
  have e1 : S.planes - 1 = (S.planes - 2) + 1 := by omega
  unfold Lkp.roundsOf lookupEntries
  rw [hs, e1]
  simp only [Bool.false_eq_true, if_false, List.nil_append, List.map_append, List.map_cons,
    tieRounds_eq, ← partEntries_eq, ← treesEntries_eq, ← chainEntries_tree,
    List.append_assoc, List.cons_append, List.nil_append]
  rfl

/-- The degrees of the sumcheck on the leaves of the table's tree, in the default order. -/
theorem leaves_degrees (mu d : Nat) :
    (Lkp.defaultOrder (mu + d)).map (fun t => if t < mu then 2 else 3) =
      List.replicate d 3 ++ List.replicate mu 2 := by
  unfold Lkp.defaultOrder
  induction d with
  | zero =>
    rw [Nat.add_zero, List.replicate_zero, List.nil_append]
    refine List.eq_replicate_iff.2 ⟨by simp, ?_⟩
    intro b hb
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hb
    have : t < mu := List.mem_range.1 (List.mem_reverse.1 ht)
    rw [if_pos this]
  | succ d ih =>
    rw [← Nat.add_assoc, List.range_succ, List.reverse_append, List.reverse_singleton,
      List.singleton_append, List.map_cons, ih, if_neg (by omega), List.replicate_succ,
      List.cons_append]

/-! ## The order of a part's last key level -/

/-- Members that differ two by two. -/
theorem nodup_of_allPairs : ∀ l : List Nat, Lkp.allPairs (fun a b => a != b) l = true → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    rw [Lkp.allPairs, Bool.and_eq_true] at h
    refine List.nodup_cons.2 ⟨fun ha => ?_, nodup_of_allPairs l h.2⟩
    have := List.all_eq_true.1 h.1 a ha
    simp at this

/-- Of the numbers below n, those that a list of different numbers below n does not hold. -/
theorem length_filter_range : ∀ (n : Nat) (first : List Nat), first.Nodup →
    (∀ j ∈ first, j < n) →
    ((List.range n).filter fun j => !first.contains j).length + first.length = n
  | 0, first, _, h => by
    cases first with
    | nil => rfl
    | cons a _ => exact absurd (h a (List.mem_cons_self ..)) (Nat.not_lt_zero _)
  | n + 1, first, hn, h => by
    rw [List.range_succ, List.filter_append, List.length_append]
    by_cases hm : n ∈ first
    · have e1 : ([n].filter fun j => !first.contains j) = [] := by simp [hm]
      have e2 : ((List.range n).filter fun j => !first.contains j) =
          (List.range n).filter fun j => !(first.erase n).contains j := by
        refine List.filter_congr fun j hj => ?_
        have hne : j ≠ n := Nat.ne_of_lt (List.mem_range.1 hj)
        simp [List.mem_erase_of_ne hne]
      have ih := length_filter_range n (first.erase n) (hn.erase n) fun j hj => by
        have h1 : j ∈ first := List.mem_of_mem_erase hj
        have h2 : j ≠ n := fun e => hn.not_mem_erase (e ▸ hj)
        have := h j h1
        omega
      have hl := List.length_erase_of_mem hm
      have hpos : 0 < first.length := List.length_pos_of_mem hm
      rw [e1, e2, List.length_nil]
      omega
    · have e1 : ([n].filter fun j => !first.contains j) = [n] := by simp [hm]
      have ih := length_filter_range n first hn fun j hj => by
        have h2 : j ≠ n := fun e => hm (e ▸ hj)
        have := h j hj
        omega
      rw [e1, List.length_singleton]
      omega

/-- An order that begins with different variables below n names n variables. -/
theorem length_orderBeginning (first : List Nat) (n : Nat) (hn : first.Nodup)
    (h : ∀ j ∈ first, j < n) : (Lkp.orderBeginning first n).length = n := by
  unfold Lkp.orderBeginning Lkp.defaultOrder
  rw [List.length_append, List.filter_reverse, List.length_reverse]
  have := length_filter_range n first hn h
  omega

/-- The least of a list and a start is at most the start and at most each member. -/
theorem foldl_min_le : ∀ (l : List Nat) (a : Nat),
    l.foldl min a ≤ a ∧ ∀ v ∈ l, l.foldl min a ≤ v
  | [], a => ⟨Nat.le_refl a, fun _ h => by cases h⟩
  | b :: l, a => by
    obtain ⟨h1, h2⟩ := foldl_min_le l (min a b)
    refine ⟨Nat.le_trans h1 (Nat.min_le_left a b), fun v hv => ?_⟩
    rcases List.mem_cons.1 hv with rfl | hv'
    · exact Nat.le_trans h1 (Nat.min_le_right a _)
    · exact h2 v hv'

/-! ## `Ready` -/

/-- What `S.ok` says of the sizes, as far as it is used here. -/
theorem sizes_of_ok (S : Lkp.Public) (hok : S.ok = true) :
    S.parts ≠ [] ∧ 1 ≤ S.mu ∧ 2 ≤ S.planes ∧ (∀ v ∈ S.parts, 1 ≤ v) ∧ S.d + S.planes < 64 := by
  simp only [Lkp.Public.ok, Lkp.Public.sizesOK, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff] at hok
  obtain ⟨⟨⟨⟨⟨hz, -⟩, -⟩, -⟩, -⟩, -⟩ := hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hp⟩, hmu⟩, -⟩, -⟩, hpl⟩, -⟩, hall⟩, -⟩, -⟩, hd⟩, -⟩, -⟩ := hz
  exact ⟨hp, hmu, hpl, fun v hv => (hall v hv).1, hd⟩

/-- The public inputs of a lookup without a shift are ready. `S.ok` gives all fields but the last:
where not all planes are real it bounds d + the number of real planes, not mu + d. -/
theorem ready_of_ok (S : Lkp.Public) (hs : S.shifted = false) (hok : S.ok = true)
    (h63 : S.mu + S.d ≤ 63) : Ready S := by
  obtain ⟨hp, hmu, -, -, -⟩ := sizes_of_ok S hok
  have ho : S.orderOK = true := by
    simp only [Lkp.Public.ok, Bool.and_eq_true] at hok
    exact hok.2
  simp only [Lkp.Public.orderOK, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at ho
  refine ⟨hs, hok, hp, fun v hv => ?_, leaves_degrees S.mu S.d, by omega, h63⟩
  refine length_orderBeginning _ _ (nodup_of_allPairs _ ho.2) fun j hj => ?_
  have h1 := ho.1 j hj
  have h2 := (foldl_min_le S.parts S.firstBits).2 v hv
  omega

/-- Where all planes are real, `S.ok` gives the last field too. -/
theorem small_of_live (S : Lkp.Public) (hok : S.ok = true) (hl : S.live = 0) :
    S.mu + S.d ≤ 63 := by
  obtain ⟨-, -, -, -, hd⟩ := sizes_of_ok S hok
  have e : S.planes = 2 ^ S.mu := by simp [Lkp.Public.planes, hl]
  have := Nat.lt_two_pow_self (n := S.mu)
  omega

/-! ## The two ledgers' counts -/

/-- The levels l, l + 1, .. of a tree, n of them, take 2 (l + more) + 5 mask entries each, from the
two ledgers together. -/
theorem chainOwn_add_chainKey (keys : Bool) (more : Nat) : ∀ (n l : Nat),
    chainOwn keys more l n + chainKey keys n =
      ((List.range' l n).map fun k => 2 * (k + more) + 5).sum
  | 0, _ => rfl
  | n + 1, l => by
    have ih := chainOwn_add_chainKey keys more n (l + 1)
    rw [chainOwn, chainKey, List.range'_succ, List.map_cons, List.sum_cons, ← ih]
    cases hk : (keys && n == 0) <;> simp [ownOf, keyOf] <;> omega

/-- A key tree with at least one level takes two entries of the second ledger. -/
theorem chainKey_true : ∀ n, 1 ≤ n → chainKey true n = 2
  | 1, _ => rfl
  | n + 2, _ => by
    have ih := chainKey_true (n + 1) (by omega)
    rw [chainKey, ih]
    simp [keyOf]

/-- The key trees take two entries of the second ledger for each part. -/
theorem treesKey_eq : ∀ vs : List Nat, (∀ v ∈ vs, 1 ≤ v) → treesKey vs = 2 * vs.length
  | [], _ => rfl
  | v :: vs, h => by
    rw [treesKey, chainKey_true v (h v (List.mem_cons_self ..)),
      treesKey_eq vs fun w hw => h w (List.mem_cons_of_mem _ hw), List.length_cons]
    omega

/-- The key trees' mask entries, from the two ledgers together. -/
theorem treesOwn_add_treesKey : ∀ vs : List Nat,
    treesOwn vs + treesKey vs = (vs.map fun v => ((List.range v).map fun k => 2 * k + 5).sum).sum
  | [] => rfl
  | v :: vs => by
    have ih := treesOwn_add_treesKey vs
    have h := chainOwn_add_chainKey true 0 v (v - v)
    rw [Nat.sub_self, ← List.range_eq_range'] at h
    simp only [Nat.add_zero] at h
    rw [treesOwn, treesKey, List.map_cons, List.sum_cons, ← ih, ← h, Nat.sub_self]
    omega

/-- The counts of the two ledgers are the port's numbers of mask entries. -/
theorem masks_split (S : Lkp.Public) (hok : S.ok = true) :
    treesKey S.parts = Lkp.keyMasks S ∧ ownTotal S + treesKey S.parts = Lkp.allMasks S := by
  obtain ⟨-, -, -, hv, -⟩ := sizes_of_ok S hok
  refine ⟨treesKey_eq S.parts hv, ?_⟩
  have h1 := treesOwn_add_treesKey S.parts
  have h2 := chainOwn_add_chainKey false S.mu S.d (S.d - S.d)
  rw [chainKey_false, Nat.add_zero, Nat.sub_self, ← List.range_eq_range'] at h2
  have e : ((List.range S.d).map fun k => 2 * (k + S.mu) + 5) =
      (List.range S.d).map fun l => 2 * (S.mu + l) + 5 :=
    List.map_congr_left fun k _ => by omega
  rw [e] at h2
  unfold ownTotal Lkp.allMasks
  rw [← h1, ← h2, Nat.sub_self]
  omega

end OnBytes.G4

#print axioms OnBytes.G4.lookupEntries_eq
#print axioms OnBytes.G4.ready_of_ok
#print axioms OnBytes.G4.masks_split
