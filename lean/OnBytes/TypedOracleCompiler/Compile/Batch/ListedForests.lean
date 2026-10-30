-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Compile/Batch/ListedForests.lean: the forests of a proof string's own trees, made along
lists of the read leaves in the place of a walk over all leaves.

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

The verifier of OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean makes, for each tree of each component of
each round, the checks that the read positions call for (checksTrees, forestsB). It walks all
2 ^ depth numbers of leaves of each tree that has a depth and a root, and takes those at which a
read position stands. The routine that makes one tree's checks (checksComp) takes the list that it
walks as an argument. Here it, checksTrees and forestsB are said again with lists in the place of
the test "is this position read": for each round, for each of its two components, for each tree, the
list of the read leaves. So a run makes no set of read positions and asks no membership in one.

Main names.
  readAt posAt isRead j: at the leaf j stands a position, and it is read.
  checksCompL, checksTreesL, forestsBL: checksComp, checksTrees and forestsB along given lists:
    every leaf of a list is taken as read; a leaf at which no position stands is skipped. A round or
    a tree for which rd holds nothing has the empty list. They are computable (Lean makes code for
    them) and do not take the test.
  LeavesT, LeavesOK: the lists are the right ones: each is the list of all numbers below 2 ^ depth,
    rising, at which readAt says yes. Asked of every tree that has a depth, with or without a root.
  checksComp_filter: checksComp skips what readAt refuses. checksCompL_read: on a list of read
    leaves checksCompL is checksComp.
  checksTreesL_eq, forestsBL_eq: under LeavesT and LeavesOK the routines along the lists return what
    checksTrees and forestsB return.
  leavesT_contains, leavesT_contains_getD: under LeavesT a leaf (a number below 2 ^ depth) of a tree
    that has a depth, at which a position stands, is in its tree's list just where the position is
    read.
  rising_ext: two strictly rising lists with the same members are one. rising_eq_filter: so a
    strictly rising list whose members are the numbers below n that pass a test is the filter of
    List.range n by that test: the form in which a caller can show one clause of LeavesT. No lemma
    of this file carries it on to LeavesT.

Limits. That a caller's lists meet LeavesOK is a premise; it is shown of no lists in this file. A
run that calls forestsBL at lists for which LeavesOK is not shown is no run of forestsB.
Which way it errs, as far as forestsBL's own result goes: at lists that leave out a read leaf of a
tree that has a root forestsBL makes fewer checks, and where that leaf's opening is missing it can
return forests where forestsB returns none: a verifier on top can then say yes where the compiled
one says no. A surplus number at which a position stands (also one of 2 ^ depth or more: no bound is
tested here) adds a check in such a tree, or a refusal where its opening is missing. A number that
stands twice gives its check twice; another order of a list gives another order of the checks. What
a verifier on top makes of these three is not looked at: where a tree's leaves are checked in one
walk (pr0, prJ) a further leaf can change which digests of the paths are read.
So a caller must compute rd on the verifier's side, of the instance, the verifier's messages and the
plain parts, and must not take it as a list from the proof's side. Nothing in this file sees to
that.
LeavesOK asks more than the equation needs: the right list also at a tree that has a depth and no
root, which forestsB does not walk; and a list with a surplus number at which no position stands
fails it, though checksCompL skips that number. It does not fix rd's length: lists beyond the depths
or beyond the rounds are read by nothing and bound by nothing.
Still carried as data: W holds each round's wire record WireRB whole, with pt : Round.IsPoint, whose
field finPos : Fintype r.Pos holds the list of all the round's positions. By reading, not by a run:
compiled Lean is strict (Iop/Shape.lean, at finChalT), so a record's fields are built when the
record is built, and whoever builds W builds these lists.
Nothing on the time that a run takes. Nothing on its memory.
readAt stands under the same short name in Compile/Batch/CompleteOpen.lean, LeavesOK in
OnBytes/RunA/ListedOwnLaws.lean, each in another namespace. Nothing on soundness.
The program does not import this file.


-/
import OnBytes.TypedOracleCompiler.Compile.Batch.Verifier

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom
open _root_.Iop hiding BatchProtocol

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- At the leaf j stands a position, and it is read. -/
def readAt {r : Round} (posAt : ℕ → Option r.Pos) (isRead : r.Pos → Bool) (j : ℕ) : Bool :=
  match posAt j with
  | some p => isRead p
  | none => false

/-- checksComp without the test: every leaf of the list is taken as read; a leaf at which no
position stands is skipped; none if an opening is missing. -/
def checksCompL {r : Round} (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body L) (rt : Dig lam)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    List ℕ → Option (List (Check lam L))
  | [] => some []
  | j :: js =>
      match posAt j with
      | some p =>
          match f p, checksCompL posAt depth emb rt f js with
          | some op, some cs => some (⟨⟨emb p op.sym, op.salt⟩, j, op.path, rt, depth⟩ :: cs)
          | _, _ => none
      | none => checksCompL posAt depth emb rt f js

/-- checksTrees along given lists: the first list for tree number k, the next for the next tree. -/
def checksTreesL {r : Round} (posAt : ℕ → ℕ → Option r.Pos)
    (emb : (p : r.Pos) → r.Sym p → Body L)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    ℕ → List ℕ → List (Dig lam) → List (List ℕ) →
      Option (List (ℕ × Dig lam × List (Check lam L)))
  | k, d :: ds, c :: cs, jss =>
      match checksCompL (posAt k) d emb c f (jss.headD []),
        checksTreesL posAt emb f (k + 1) ds cs jss.tail with
      | some a, some b => some ((d, c, a) :: b)
      | _, _ => none
  | _, _, _, _ => some []

/-- forestsB along given lists: for each round the lists of the trees over the shared component and
the lists of the trees over the slot's. -/
def forestsBL :
    (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A →
    ((p : OPos s) → OSym s p → Body L) → RootsOfChain lam s →
    ((p : OPos s) → Option (Opening lam (OSym s p))) →
    List (List (List ℕ) × List (List ℕ)) → Option (List (Forest lam L))
  | [], _, _, _, _, _, _ => some []
  | _ :: s, (_, A), (w, W), emb, (rt, rts), f, rd =>
      match checksTreesL w.posAt0 (fun p => emb (.inl p))
          (fun p => f (.inl p)) 0 w.depth0 (rt.1.getD []) (rd.headD ([], [])).1,
        checksTreesL w.posAtJ (fun p => emb (.inl p))
          (fun p => f (.inl p)) 0 w.depthJ (rt.2.getD []) (rd.headD ([], [])).2,
        forestsBL s A W (fun p => emb (.inr p)) rts (fun p => f (.inr p)) rd.tail with
      | some a, some b, some c => some (forestsT w.pr0 a ++ (forestsT w.prJ b ++ c))
      | _, _, _ => none

/-- The lists of the trees from number k on are the right ones. -/
def LeavesT {r : Round} (posAt : ℕ → ℕ → Option r.Pos) (isRead : r.Pos → Bool) :
    ℕ → List ℕ → List (List ℕ) → Prop
  | k, d :: ds, jss =>
      jss.headD [] = (List.range (2 ^ d)).filter (readAt (posAt k) isRead) ∧
        LeavesT posAt isRead (k + 1) ds jss.tail
  | _, [], _ => True

/-- The lists of all rounds are the right ones. -/
def LeavesOK :
    (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → (OPos s → Bool) →
    List (List (List ℕ) × List (List ℕ)) → Prop
  | [], _, _, _, _ => True
  | _ :: s, (_, A), (w, W), isRead, rd =>
      LeavesT w.posAt0 (fun p => isRead (.inl p)) 0 w.depth0 (rd.headD ([], [])).1 ∧
        LeavesT w.posAtJ (fun p => isRead (.inl p)) 0 w.depthJ (rd.headD ([], [])).2 ∧
        LeavesOK s A W (fun p => isRead (.inr p)) rd.tail

/-! ## The equations -/

/-- checksComp skips what readAt refuses. -/
theorem checksComp_filter {r : Round} (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body L) (rt : Dig lam) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) : ∀ l : List ℕ,
    checksComp posAt depth emb rt isRead f l =
      checksComp posAt depth emb rt isRead f (l.filter (readAt posAt isRead))
  | [] => rfl
  | j :: js => by
    have ih := checksComp_filter posAt depth emb rt isRead f js
    cases hp : posAt j with
    | none =>
      have hq : ¬ readAt posAt isRead j = true := by simp only [readAt, hp, Bool.false_eq_true,
        not_false_eq_true]
      rw [List.filter_cons_of_neg hq, ← ih]
      simp only [checksComp, hp]
    | some p =>
      cases hr : isRead p with
      | false =>
        have hq : ¬ readAt posAt isRead j = true := by simp only [readAt, hp, hr,
          Bool.false_eq_true, not_false_eq_true]
        rw [List.filter_cons_of_neg hq, ← ih]
        simp only [checksComp, hp, hr, Bool.false_eq_true, if_false]
      | true =>
        have hq : readAt posAt isRead j = true := by simp only [readAt, hp, hr]
        rw [List.filter_cons_of_pos hq]
        simp only [checksComp, hp, hr, if_true]
        rw [← ih]

/-- On a list of read leaves checksCompL is checksComp. -/
theorem checksCompL_read {r : Round} (posAt : ℕ → Option r.Pos) (depth : ℕ)
    (emb : (p : r.Pos) → r.Sym p → Body L) (rt : Dig lam) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) : ∀ l : List ℕ,
    (∀ j ∈ l, readAt posAt isRead j = true) →
    checksCompL posAt depth emb rt f l = checksComp posAt depth emb rt isRead f l
  | [], _ => rfl
  | j :: js, h => by
    have ih := checksCompL_read posAt depth emb rt isRead f js
      fun i hi => h i (List.mem_cons_of_mem _ hi)
    have hj := h j List.mem_cons_self
    cases hp : posAt j with
    | none =>
      simp only [checksCompL, checksComp, hp]
      exact ih
    | some p =>
      have hr : isRead p = true := by
        simp only [readAt, hp] at hj
        exact hj
      simp only [checksCompL, checksComp, hp, hr, if_true]
      rw [ih]
      cases f p <;> cases checksComp posAt depth emb rt isRead f js <;> rfl

/-- Along the right lists checksTreesL returns what checksTrees returns. -/
theorem checksTreesL_eq {r : Round} (posAt : ℕ → ℕ → Option r.Pos)
    (emb : (p : r.Pos) → r.Sym p → Body L) (isRead : r.Pos → Bool)
    (f : (p : r.Pos) → Option (Opening lam (r.Sym p))) :
    ∀ (ds : List ℕ) (k : ℕ) (cs : List (Dig lam)) (jss : List (List ℕ)),
      LeavesT posAt isRead k ds jss →
      checksTreesL posAt emb f k ds cs jss = checksTrees posAt emb isRead f k ds cs
  | [], k, cs, jss, _ => by
    simp only [checksTreesL, checksTrees]
  | d :: ds, k, [], jss, _ => by
    simp only [checksTreesL, checksTrees]
  | d :: ds, k, c :: cs, jss, h => by
    have h' : jss.headD [] = (List.range (2 ^ d)).filter (readAt (posAt k) isRead) ∧
        LeavesT posAt isRead (k + 1) ds jss.tail := h
    simp only [checksTreesL, checksTrees]
    rw [h'.1, checksCompL_read (posAt k) d emb c isRead f _ fun j hj => (List.mem_filter.1 hj).2,
      ← checksComp_filter, checksTreesL_eq posAt emb isRead f ds (k + 1) cs jss.tail h'.2]
    cases checksComp (posAt k) d emb c isRead f (List.range (2 ^ d)) <;>
      cases checksTrees posAt emb isRead f (k + 1) ds cs <;> rfl

/-- **Along the right lists forestsBL returns what forestsB returns.** -/
theorem forestsBL_eq :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
      (emb : (p : OPos s) → OSym s p → Body L) (rts : RootsOfChain lam s) (isRead : OPos s → Bool)
      (f : (p : OPos s) → Option (Opening lam (OSym s p)))
      (rd : List (List (List ℕ) × List (List ℕ))), LeavesOK s A W isRead rd →
      forestsBL s A W emb rts f rd = forestsB s A W emb rts isRead f
  | [], _, _, _, _, _, _, _, _ => rfl
  | _ :: s, (_, A), (w, W), emb, (rt, rts), isRead, f, rd, h => by
    have h' : LeavesT w.posAt0 (fun p => isRead (.inl p)) 0 w.depth0 (rd.headD ([], [])).1 ∧
        LeavesT w.posAtJ (fun p => isRead (.inl p)) 0 w.depthJ (rd.headD ([], [])).2 ∧
        LeavesOK s A W (fun p => isRead (.inr p)) rd.tail := h
    simp only [forestsBL, forestsB]
    rw [checksTreesL_eq _ _ _ _ _ _ _ _ h'.1, checksTreesL_eq _ _ _ _ _ _ _ _ h'.2.1,
      forestsBL_eq s A W _ rts _ _ rd.tail h'.2.2]
    generalize checksTrees w.posAt0 _ _ _ 0 w.depth0 _ = a
    generalize checksTrees w.posAtJ _ _ _ 0 w.depthJ _ = b
    generalize forestsB s A W _ rts _ _ = c
    cases a <;> cases b <;> cases c <;> rfl

/-! ## What the premise says of membership -/

/-- A number below n is in the filter of List.range n by a test just where the test says yes. -/
theorem contains_filter_range (n : ℕ) (t : ℕ → Bool) (j : ℕ) (hj : j < n) :
    ((List.range n).filter t).contains j = t j := by
  rw [Bool.eq_iff_iff]
  simp [hj]

/-- In the right lists: a leaf of tree number k at which a position stands is in that tree's list
just where the position is read. -/
theorem leavesT_contains {r : Round} {posAt : ℕ → ℕ → Option r.Pos} {isRead : r.Pos → Bool}
    {k d : ℕ} {ds : List ℕ} {jss : List (List ℕ)} (h : LeavesT posAt isRead k (d :: ds) jss)
    {j : ℕ} {p : r.Pos} (hj : j < 2 ^ d) (hp : posAt k j = some p) :
    (jss.headD []).contains j = isRead p := by
  have h' : jss.headD [] = (List.range (2 ^ d)).filter (readAt (posAt k) isRead) ∧
      LeavesT posAt isRead (k + 1) ds jss.tail := h
  rw [h'.1, contains_filter_range _ _ _ hj]
  simp only [readAt, hp]

/-- The list of tree number k + i, by its place in the list of lists. -/
theorem leavesT_getD {r : Round} (posAt : ℕ → ℕ → Option r.Pos) (isRead : r.Pos → Bool) :
    ∀ (ds : List ℕ) (k : ℕ) (jss : List (List ℕ)), LeavesT posAt isRead k ds jss →
      ∀ i, i < ds.length →
        jss.getD i [] = (List.range (2 ^ ds.getD i 0)).filter (readAt (posAt (k + i)) isRead)
  | [], _, _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | d :: ds, k, jss, h, i, hi => by
    have h' : jss.headD [] = (List.range (2 ^ d)).filter (readAt (posAt k) isRead) ∧
        LeavesT posAt isRead (k + 1) ds jss.tail := h
    cases i with
    | zero =>
      have e : jss.getD 0 [] = jss.headD [] := by cases jss <;> rfl
      rw [e, h'.1]
      rfl
    | succ i =>
      have e : jss.getD (i + 1) [] = jss.tail.getD i [] := by cases jss <;> simp
      have hi' : i < ds.length := Nat.lt_of_succ_lt_succ hi
      rw [e, leavesT_getD posAt isRead ds (k + 1) jss.tail h'.2 i hi', List.getD_cons_succ,
        show k + 1 + i = k + (i + 1) by omega]

/-- The same by the tree's number, for lists that begin at tree number 0. -/
theorem leavesT_contains_getD {r : Round} {posAt : ℕ → ℕ → Option r.Pos} {isRead : r.Pos → Bool}
    {ds : List ℕ} {jss : List (List ℕ)} (h : LeavesT posAt isRead 0 ds jss) {k j : ℕ} {p : r.Pos}
    (hk : k < ds.length) (hj : j < 2 ^ ds.getD k 0) (hp : posAt k j = some p) :
    (jss.getD k []).contains j = isRead p := by
  rw [leavesT_getD posAt isRead ds 0 jss h k hk, contains_filter_range _ _ _ hj, Nat.zero_add]
  simp only [readAt, hp]

/-! ## How a caller can show the premise -/

/-- Two strictly rising lists with the same members are one. -/
theorem rising_ext : ∀ (a b : List ℕ), a.Pairwise (· < ·) → b.Pairwise (· < ·) →
    (∀ j, j ∈ a ↔ j ∈ b) → a = b
  | [], [], _, _, _ => rfl
  | [], y :: _, _, _, h => absurd ((h y).2 List.mem_cons_self) List.not_mem_nil
  | x :: _, [], _, _, h => absurd ((h x).1 List.mem_cons_self) List.not_mem_nil
  | x :: a, y :: b, ha, hb, h => by
    obtain ⟨hx, ha'⟩ := List.pairwise_cons.1 ha
    obtain ⟨hy, hb'⟩ := List.pairwise_cons.1 hb
    have exy : x = y := by
      rcases List.mem_cons.1 ((h x).1 List.mem_cons_self) with e | q
      · exact e
      · rcases List.mem_cons.1 ((h y).2 List.mem_cons_self) with e | q'
        · exact e.symm
        · have h1 := hy x q
          have h2 := hx y q'
          omega
    subst exy
    have e : a = b := rising_ext a b ha' hb' fun j => by
      constructor
      · intro hj
        rcases List.mem_cons.1 ((h j).1 (List.mem_cons_of_mem _ hj)) with e | q
        · have h1 := hx j hj
          omega
        · exact q
      · intro hj
        rcases List.mem_cons.1 ((h j).2 (List.mem_cons_of_mem _ hj)) with e | q
        · have h1 := hy j hj
          omega
        · exact q
    rw [e]

/-- A strictly rising list whose members are the numbers below n that pass a test is the filter of
List.range n by that test. -/
theorem rising_eq_filter {l : List ℕ} {n : ℕ} {t : ℕ → Bool} (hl : l.Pairwise (· < ·))
    (hm : ∀ j, j ∈ l ↔ j < n ∧ t j = true) : l = (List.range n).filter t :=
  rising_ext l _ hl (List.Pairwise.filter _ List.pairwise_lt_range) fun j => by
    rw [hm j, List.mem_filter, List.mem_range]

end TypedOracleCompiler.Compile.Batch
