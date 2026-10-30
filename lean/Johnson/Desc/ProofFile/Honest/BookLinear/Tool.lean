-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookLinear/Tool.lean: TWO TESTS ON LISTS OF NUMBERS, EACH A SORT AND
ONE LOOK AT NEIGHBOURS, WITH THEIR LAWS: WHERE nodupN ACCEPTS, NO NUMBER STANDS TWICE IN THE LIST
(nodupN_nodup); WHERE apartN ACCEPTS, NO TWO STRETCHES OF THE LIST MEET, IN THE SENSE OF THE FRAME's
meets (apartN_apart). ONE DIRECTION ALONE: A "NO" MEANS NOTHING: with too few rounds a good list can
be refused. They are meant for tests that run over all pairs of a long list. Definitions with code;
statements with their proofs. Written by the authors of the honest side of the linear claim's shared
rounds (K14), in the frame's folder, not by the frame's authors; Addr and meets (Honest/Frame.lean)
are theirs.

  mergeL, pairUp, roundsL, sortL   a merge sort from below: one-member lists, merged two and two, d
                  rounds; what is left, one behind the other. k bounds one merge's steps. The three
                  that recurse do so structurally, as do risesN and endToEnd
  sortL_perm      **(sortL le d k l).Perm l, at every comparison, every d and every k**
                  (mergeL_perm, pairUp_perm, roundsL_perm, flatten_ones beneath it). THAT IT SORTS
                  IS NOT SHOWN AND NOT WANTED: with too few rounds or too small a bound the list can
                  be left unsorted, and the look at neighbours then refuses
  risesN, nodupN  each member is below the next; sortL, then risesN. d: the rounds; 2 ^ d bounds a
                  merge (enough, by the authors' reckoning, where 2 ^ d is at least the list's
                  length: no law says it)
  nodupN_nodup    **nodupN d l = true → l.Nodup**, at every d: risesN_pairwise, and the sort
                  permutes
  endToEnd, apartN   stretches (begin, length): each ends at or before the next begins; those of
                  length 0 left out, as meets leaves them; sortL by the begins; endToEnd
  apartN_apart    **apartN d l = true → l.Pairwise fun a b => meets a.1 a.2 b.1 b.2 = false**, at
                  every d: endToEnd_pairwise; meets_of_le; meets is symmetric (meets_comm), so the
                  sentence passes along the permutation; a stretch of length 0 meets nothing
                  (meets_zero)
  one_each        from "the values of f are all different" to the form of the second test of
                  ProverCoinCounts.clauses (a part has two rows), of the eleventh (two entries bear one name)
                  and of the tenth's last clause (a cut stands twice): each member's value is had by
                  one member
  all_pairs       from "pairwise", at a symmetric R, to the form of the test "a coin stands in two
                  entries that spend it": over all pairs of positions
  pairwise_of_all   its converse, and without symmetry: from all pairs of positions back to
                  "pairwise"
  Addr.code       an address as one number: chain, link (none: 0; some n: n + 1), piece and part,
                  the four that Addr.words (Honest/ForKinds.lean) prints; told apart, by the
                  authors' reckoning, where link + 1, piece and part are below 2 ^ 20 (no law says
                  it): THE KIND IS LEFT OUT. Nothing here calls it; of the laws that go by it,
                  Seventh.lean's and Eighth.lean's ask only that equal addresses have equal codes;
                  NameKeys.lean's ask that addresses with one spot have one code (code_of_spot):
                  they lean on the kind being left out

No twin of a test of ProverCoinCounts.clauses stands here. Who calls the laws, in this folder: Seventh.lean:
apartN_apart, all_pairs, pairwise_of_all, meets_comm; Eighth.lean: sortL_perm; Eleventh.lean:
one_each; NameKeys.lean: nodupN_nodup.

Kin. The frame's own law on meets: meets_iff (Honest/BookGuard.lean): meets a n b m = true just
where a number lies in both stretches: THE ONE LAW THAT BEARS THE WORDS "A NUMBER IN COMMON":
apartN_apart ends in "meets … = false" and does not call it. meets_comm, meets_of_le and meets_zero
would each follow from it in a line or two; they are had here by unfolding, without that import.
Beside meets_iff, in Honest/BookGuard.lean: runsMeet and CoinRuns.apartB: "no coin lies in both",
over all pairs of two lists. meets_false_of_front and meets_false_of_back (Honest/BookFreeOf.lean,
by authors of this kind): two runs do not meet where one has no number, or the one ends where the
other begins or before: meets_of_le and meets_zero are two of the first's three cases.
Johnson.Unfolds.sortF (Johnson/Unfolds/MergeSort.lean): the core library's List.mergeSort with a
bound in front, and the equation between the two. IT IS NOT CALLED, AND WHY: its merge maps "x :: ·"
over its own call inside an Option, and it reads lengths: by the authors' reading the kernel must
reach a merge's end before it has the first member: a nest as deep as the list. What was seen, once,
on one machine, under Lean's default stack, nothing on memory: a module of three closed facts over
it by decide +kernel (two of "no number twice" at 13,116 and 13,118 shuffled numbers, one of
stretches at 13,116; maxRecDepth raised) ended "Stack overflow detected": at which of the three is
not known; one such fact alone at 6,500: green. Over this file's own texts, one fact a module:
nodupN 20 at 13,116 numbers: green; apartN 20 at 6,816 stretches: green. Compile.pairUp and its pure
form pairUpF (Compile/MerkleM.lean, Compile/MerkleList.lean): "one level up: hash neighbours in
pairs; an odd last entry goes up as it is": pairUp is that text at a merge for the hash. It is not
called: a monad stands between, and its imports. OnBytes.Wf.noGap (OnBytes/Key/Ranges.lean):
stretches sorted by their first rows, then one pass: that they leave no gap.

Limits. Nothing on what an evaluation costs beyond the sentences above. The four closed facts at the
foot are small lists, evaluated in Lean's kernel (decide +kernel). Nothing on any book; nothing on
any property.
-/
import Johnson.Desc.ProofFile.Honest.Frame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

/-! ## 1 The sort -/

/-- Two lists merged. k: a bound on the steps; at 0 the two lists one behind the other: still a
permutation. -/
def mergeL {α : Type} (le : α → α → Bool) : Nat → List α → List α → List α
  | 0, xs, ys => xs ++ ys
  | _ + 1, [], ys => ys
  | _ + 1, x :: xs, [] => x :: xs
  | k + 1, x :: xs, y :: ys =>
    if le x y then x :: mergeL le k xs (y :: ys) else y :: mergeL le k (x :: xs) ys
termination_by structural k => k

/-- Neighbours merged, two and two; an odd one left stays. -/
def pairUp {α : Type} (le : α → α → Bool) (k : Nat) : List (List α) → List (List α)
  | a :: b :: r => mergeL le k a b :: pairUp le k r
  | r => r
termination_by structural l => l

/-- d rounds of pairUp. -/
def roundsL {α : Type} (le : α → α → Bool) (k : Nat) : Nat → List (List α) → List (List α)
  | 0, r => r
  | d + 1, r => roundsL le k d (pairUp le k r)
termination_by structural d => d

/-- d rounds of merging neighbours, from one-member lists; what is left, one behind the other. -/
def sortL {α : Type} (le : α → α → Bool) (d k : Nat) (l : List α) : List α :=
  (roundsL le k d (l.map fun a => [a])).flatten

/-- A merge permutes the two lists laid one behind the other, at every bound. -/
theorem mergeL_perm {α : Type} (le : α → α → Bool) : ∀ (k : Nat) (xs ys : List α),
    (mergeL le k xs ys).Perm (xs ++ ys)
  | 0, xs, ys => by
    rw [mergeL]
  | _ + 1, [], ys => by
    rw [mergeL]
    exact List.Perm.refl _
  | _ + 1, x :: xs, [] => by
    rw [mergeL, List.append_nil]
  | k + 1, x :: xs, y :: ys => by
    rw [mergeL]
    split
    · exact (mergeL_perm le k xs (y :: ys)).cons x
    · exact ((mergeL_perm le k (x :: xs) ys).cons y).trans List.perm_middle.symm

/-- A round keeps the flattened list, up to a permutation. -/
theorem pairUp_perm {α : Type} (le : α → α → Bool) (k : Nat) : ∀ r : List (List α),
    (pairUp le k r).flatten.Perm r.flatten
  | [] => List.Perm.refl _
  | [_] => List.Perm.refl _
  | a :: b :: r => by
    rw [pairUp]
    simp only [List.flatten_cons]
    rw [← List.append_assoc]
    exact (mergeL_perm le k a b).append (pairUp_perm le k r)

/-- So do d rounds. -/
theorem roundsL_perm {α : Type} (le : α → α → Bool) (k : Nat) : ∀ (d : Nat) (r : List (List α)),
    (roundsL le k d r).flatten.Perm r.flatten
  | 0, _ => List.Perm.refl _
  | d + 1, r => by
    rw [roundsL]
    exact (roundsL_perm le k d _).trans (pairUp_perm le k r)

/-- One-member lists, one behind the other, are the list. -/
theorem flatten_ones {α : Type} : ∀ l : List α, (l.map fun a => [a]).flatten = l
  | [] => rfl
  | a :: l => by
    rw [List.map_cons, List.flatten_cons, flatten_ones l]
    rfl

/-- **THE SORT PERMUTES, AT EVERY COMPARISON AND WHATEVER THE TWO BOUNDS ARE.** -/
theorem sortL_perm {α : Type} (le : α → α → Bool) (d k : Nat) (l : List α) :
    (sortL le d k l).Perm l := by
  have h := roundsL_perm le k d (l.map fun a => [a])
  rw [flatten_ones] at h
  exact h

/-! ## 2 The two looks at neighbours, and the two tests -/

/-- Each member is below the next. -/
def risesN : List Nat → Bool
  | a :: b :: l => decide (a < b) && risesN (b :: l)
  | _ => true
termination_by structural l => l

/-- Meant to say: no number twice; where it accepts, that is so (`nodupN_nodup`). d: the sort's
rounds: with too few it can refuse a good list. -/
def nodupN (d : Nat) (l : List Nat) : Bool :=
  risesN (sortL (fun (a b : Nat) => decide (a ≤ b)) d (2 ^ d) l)

/-- Stretches (begin, length): each ends at or before the next begins. -/
def endToEnd : List (Nat × Nat) → Bool
  | a :: b :: l => decide (a.1 + a.2 ≤ b.1) && endToEnd (b :: l)
  | _ => true
termination_by structural l => l

/-- Meant to say: no two stretches have a number in common; where it accepts, no two meet
(`apartN_apart`). Those of length 0 are left out, as `meets` leaves them. With too few rounds it can
refuse a good list. -/
def apartN (d : Nat) (l : List (Nat × Nat)) : Bool :=
  endToEnd (sortL (fun (a b : Nat × Nat) => decide (a.1 ≤ b.1)) d (2 ^ d) (l.filter (·.2 != 0)))

/-- An address as one number, of chain, link, piece and part: THE KIND IS LEFT OUT. -/
def Addr.code (a : Addr) : Nat :=
  ((a.place.chain * 2 ^ 20 + (a.place.link.map (· + 1)).getD 0) * 2 ^ 20 + a.place.piece) * 2 ^ 20 +
    a.part

/-! ## 3 The laws -/

/-- Where each member is below the next, each is below all behind it. -/
theorem risesN_pairwise : ∀ l : List Nat, risesN l = true → l.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    rw [risesN, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := risesN_pairwise (b :: l) h.2
    refine List.pairwise_cons.2 ⟨?_, ih⟩
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · exact Nat.lt_trans h.1 ((List.pairwise_cons.1 ih).1 x hx)

/-- **WHERE nodupN ACCEPTS, NO NUMBER STANDS TWICE**, at every number of rounds. -/
theorem nodupN_nodup {d : Nat} {l : List Nat} (h : nodupN d l = true) : l.Nodup :=
  (sortL_perm _ d (2 ^ d) l).nodup_iff.1 ((risesN_pairwise _ h).imp fun hab => Nat.ne_of_lt hab)

/-- Where each stretch ends at or before the next begins, it ends at or before all behind it. -/
theorem endToEnd_pairwise : ∀ l : List (Nat × Nat), endToEnd l = true →
    l.Pairwise fun a b => a.1 + a.2 ≤ b.1
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    rw [endToEnd, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := endToEnd_pairwise (b :: l) h.2
    refine List.pairwise_cons.2 ⟨?_, ih⟩
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h.1
    · have := (List.pairwise_cons.1 ih).1 x hx
      omega

/-- `meets` is symmetric. -/
theorem meets_comm (a n b m : Nat) : meets a n b m = meets b m a n := by
  unfold meets
  cases (n != 0) <;> cases (m != 0) <;> cases decide (a < b + m) <;> cases decide (b < a + n) <;>
    rfl

/-- A stretch that ends at or before another begins does not meet it. -/
theorem meets_of_le {a n b m : Nat} (h : a + n ≤ b) : meets a n b m = false := by
  unfold meets
  rw [decide_eq_false (Nat.not_lt.2 h), Bool.and_false]

/-- A stretch of length 0 meets nothing. -/
theorem meets_zero (a b m : Nat) : meets a 0 b m = false := rfl

/-- **WHERE apartN ACCEPTS, NO TWO STRETCHES MEET** (`meets`, Honest/Frame.lean), at every d. -/
theorem apartN_apart {d : Nat} {l : List (Nat × Nat)} (h : apartN d l = true) :
    l.Pairwise fun a b => meets a.1 a.2 b.1 b.2 = false := by
  have h1 := (endToEnd_pairwise _ h).imp (S := fun (a b : Nat × Nat) => meets a.1 a.2 b.1 b.2 =
    false)
    fun hab => meets_of_le hab
  have h2 := ((sortL_perm _ d (2 ^ d) (l.filter (·.2 != 0))).pairwise_iff
    (fun {x y} hxy => by rw [meets_comm]; exact hxy)).1 h1
  refine (List.pairwise_filter.1 h2).imp ?_
  intro a b hab
  by_cases ha : a.2 = 0
  · rw [ha]
    exact meets_zero _ _ _
  · by_cases hb : b.2 = 0
    · rw [meets_comm, hb]
      exact meets_zero _ _ _
    · exact hab (bne_iff_ne.2 ha) (bne_iff_ne.2 hb)

/-- **From "the values of f are all different"**: each member's value is had by one member: the form
of the second, the tenth's last and the eleventh test of `ProverCoinCounts.clauses`. -/
theorem one_each {α β : Type} [BEq β] [LawfulBEq β] (f : α → β) (l : List α) (h : (l.map f).Nodup) :
    l.all (fun a => (l.filter fun b => f b == f a).length == 1) = true := by
  rw [List.all_eq_true]
  intro a ha
  have h1 : (l.map f).count (f a) = 1 := List.count_eq_one_of_mem h (List.mem_map_of_mem ha)
  rw [List.count, List.countP_map, List.countP_eq_length_filter] at h1
  exact beq_iff_eq.2 h1

/-- **From "pairwise", at a symmetric R, to all pairs of positions**: the form of the seventh test
of `ProverCoinCounts.clauses`. -/
theorem all_pairs {α : Type} (R : α → α → Bool) (hs : ∀ a b, R a b = R b a) (l : List α)
    (h : l.Pairwise fun a b => R a b = true) :
    l.zipIdx.all (fun p => l.zipIdx.all fun q => p.2 == q.2 || R p.1 q.1) = true := by
  rw [List.all_eq_true]
  intro p hp
  rw [List.all_eq_true]
  intro q hq
  rw [List.mem_zipIdx_iff_getElem?] at hp hq
  obtain ⟨ip, ep⟩ := List.getElem?_eq_some_iff.1 hp
  obtain ⟨iq, eq⟩ := List.getElem?_eq_some_iff.1 hq
  rw [Bool.or_eq_true]
  rcases Nat.lt_trichotomy p.2 q.2 with c | c | c
  · right
    rw [← ep, ← eq]
    exact List.pairwise_iff_getElem.1 h _ _ ip iq c
  · left
    exact beq_iff_eq.2 c
  · right
    rw [hs, ← ep, ← eq]
    exact List.pairwise_iff_getElem.1 h _ _ iq ip c

/-- From all pairs of positions back to "pairwise": the converse of `all_pairs`, and without
  symmetry. -/
theorem pairwise_of_all {α : Type} (R : α → α → Bool) (l : List α)
    (h : l.zipIdx.all (fun p => l.zipIdx.all fun q => p.2 == q.2 || R p.1 q.1) = true) :
    l.Pairwise fun a b => R a b = true := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have h1 := List.all_eq_true.1 h (l[i], i) (List.mem_zipIdx_iff_getElem?.2
    (List.getElem?_eq_getElem hi))
  have h2 := List.all_eq_true.1 h1 (l[j], j) (List.mem_zipIdx_iff_getElem?.2
    (List.getElem?_eq_getElem hj))
  rcases Bool.or_eq_true _ _ ▸ h2 with c | c
  · exact absurd (beq_iff_eq.1 c) (Nat.ne_of_lt hij)
  · exact c

/-! ## 4 Small lists: what each must accept, and what it must refuse -/

/-- It sorts a small list. -/
theorem sortL_small : sortL (fun (a b : Nat) => decide (a ≤ b)) 20 100 [5, 3, 9, 0, 7, 3] =
    [0, 3, 3, 5, 7, 9] := by decide +kernel

/-- nodupN: yes; a number twice: no; too few rounds: no; the empty list and one member: yes. -/
theorem nodupN_small : nodupN 20 [5, 3, 9, 0, 7] = true ∧ nodupN 20 [5, 3, 9, 3, 7] = false ∧
    nodupN 1 [5, 3, 9, 0, 7] = false ∧ nodupN 20 [] = true ∧ nodupN 20 [4] = true := by
  decide +kernel

/-- Too small a bound on a merge's steps, at rounds enough: the list is left unsorted. -/
theorem sortL_short : risesN (sortL (fun (a b : Nat) => decide (a ≤ b)) 20 1 [5, 3, 9, 0, 7]) =
  false := by
  decide +kernel

/-- apartN: yes; two that meet: no; a stretch of length 0 inside another: yes. -/
theorem apartN_small : apartN 20 [(10, 5), (0, 3), (3, 7), (15, 1)] = true ∧
    apartN 20 [(10, 5), (0, 3), (3, 8), (15, 1)] = false ∧
    apartN 20 [(10, 5), (12, 0), (15, 1)] = true := by decide +kernel

end ProofFile.Honest

#print axioms ProofFile.Honest.mergeL_perm
#print axioms ProofFile.Honest.pairUp_perm
#print axioms ProofFile.Honest.roundsL_perm
#print axioms ProofFile.Honest.flatten_ones
#print axioms ProofFile.Honest.sortL_perm
#print axioms ProofFile.Honest.risesN_pairwise
#print axioms ProofFile.Honest.nodupN_nodup
#print axioms ProofFile.Honest.endToEnd_pairwise
#print axioms ProofFile.Honest.meets_comm
#print axioms ProofFile.Honest.meets_of_le
#print axioms ProofFile.Honest.meets_zero
#print axioms ProofFile.Honest.apartN_apart
#print axioms ProofFile.Honest.one_each
#print axioms ProofFile.Honest.all_pairs
#print axioms ProofFile.Honest.pairwise_of_all
#print axioms ProofFile.Honest.sortL_small
#print axioms ProofFile.Honest.nodupN_small
#print axioms ProofFile.Honest.sortL_short
#print axioms ProofFile.Honest.apartN_small
