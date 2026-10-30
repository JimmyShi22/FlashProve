-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Parts/Numbered.lean: the honest side of the kind "lookup" (K3): AT
ANY NUMBER OF PARTS OF KEYS: a course that stands at its place and whose challenges can be sampled
(`Fit R`, Honest/K3/Law/Statements.lean) has its challenges numbered as
Honest/K3/Parts/Lawful.lean's `NumberedP R` says. Theorems with proofs; no definition.

No closed form of the number of rounds in front of a stage is used. ONE FACT DOES THE WORK: a stage
that stands in front of another in the row ends where the other has not begun (`before`), by the
stages' order of ranks (Honest/K3/Law/Steps.lean).

  1  `sum_before`, `before`   a stage in front ends before the other begins
  2  `mem_shift`, `mem_alpha`, `mem_join`, `mem_zero`, `mem_keyLine`, `mem_tabLine`   which quiet
                              stages stand in the row
  3  `theta_cut`, `alpha_cut`, `keyPt_cut`, `rhoT_cut`, `tabPt_cut`, `zeroPt_cut`   a field of the
     points is the same of a list of challenges that is cut behind the rounds which the field reads
  4  `same_cut`, `same_of_fitP`   what a stage's job reads of the challenges in front of the stage
     is what the whole run's points hold
  5  `key_of_fitP`, `numberedP_of_fit`   THE THEOREM: CONDITIONAL ON `Fit R` alone

The other five clauses are called from Honest/K3/Law/SpecNumbered.lean and NumberedOfFit.lean, where
they are shown without a premise on the parts.

Limits. No summand and no input is read. A member: Honest/K3/Parts/Member.lean's course passes the
test for `Fit`.
Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K3.Parts.Course
import Johnson.Desc.ProofFile.Honest.K3.Law.NumberedOfFit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Parts
open OnBytes (E zeroE)
open OnBytes.Model (orderDefault)
open ProofFile.Honest.K3.Law
open ProofFile.Honest.K3.Law.Spec (len_of_fit r_take head_behind tab_of_fit zb0_of_fit zb1_of_fit
  masks_len
  levelCall_len tab_lt)

variable {W : Type}

/-! ## 1 A stage in front ends before the other begins -/

/-- In a list that stands in the order of the ranks: what the members in front of a weigh, and a
itself, is at most what the members in front of s weigh, if a stands in front of s. -/
theorem sum_before (g : Stage → Nat) : ∀ {l : List Stage}, l.Pairwise Fore → ∀ {a s : Stage},
    a ∈ l →
    Fore a s → ((l.take (l.idxOf a)).map g).sum + g a ≤ ((l.take (l.idxOf s)).map g).sum
  | [], _, _, _, ha, _ => by simp at ha
  | x :: t, hp, a, s, ha, hf => by
    have hxs : x ≠ s := by
      rintro rfl
      rcases List.mem_cons.1 ha with rfl | h
      · exact fore_asymm hf hf
      · exact fore_asymm hf ((List.pairwise_cons.1 hp).1 a h)
    rw [List.idxOf_cons_ne _ hxs, List.take_succ_cons, List.map_cons, List.sum_cons]
    by_cases hxa : x = a
    · subst hxa
      rw [List.idxOf_cons_self]
      simp
    · have hat : a ∈ t := by
        rcases List.mem_cons.1 ha with rfl | h
        · exact absurd rfl hxa
        · exact h
      rw [List.idxOf_cons_ne _ hxa, List.take_succ_cons, List.map_cons, List.sum_cons]
      have := sum_before g (List.pairwise_cons.1 hp).2 hat hf
      omega

/-- **A stage of the row that stands in front of another ends where the other has not begun.** -/
theorem before {f : LFace} {a s : Stage} (ha : a ∈ stages f) (hf : Fore a s) :
    firstRound f a + a.rounds f ≤ firstRound f s :=
  sum_before (Stage.rounds f) (stages_sorted f) ha hf

/-! ## 2 Which quiet stages stand in the row -/

theorem mem_shift {f : LFace} (h : f.shifted = true) : Stage.shift ∈ stages f := by
  unfold stages
  simp [h]

theorem mem_alpha (f : LFace) : Stage.alpha ∈ stages f := by
  unfold stages
  simp

theorem mem_join (f : LFace) : Stage.join ∈ stages f := by
  unfold stages
  simp

theorem mem_zero (f : LFace) : Stage.zero ∈ stages f := by
  unfold stages
  simp

theorem mem_keyLine {f : LFace} {y : Nat × Nat} (hy : y ∈ f.parts.zipIdx) {m : Nat} (hm : m < y.1) :
    Stage.keyLine y.2 m ∈ stages f := by
  unfold stages
  simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inr (List.mem_flatMap.2 ⟨y, hy,
    List.mem_flatMap.2 ⟨m, List.mem_range.2 hm, by simp⟩⟩)))

theorem mem_tabLine {f : LFace} {l : Nat} (h : l < f.d) : Stage.tabLine l ∈ stages f := by
  unfold stages
  simp only [List.mem_append]
  exact Or.inl (Or.inr (List.mem_flatMap.2 ⟨l, List.mem_range.2 h, by simp⟩))

/-! ## 3 A field of the points, of a list that is cut -/

section Cut
variable (f : LFace) (front ds : List Fmt.Drawn) {n : Nat}

theorem theta_cut (hn : f.shifted = true → firstRound f .shift + 1 ≤ n) :
    (ptsOf f front.length (front ++ ds.take n)).theta =
      (ptsOf f front.length (front ++ ds)).theta := by
  show (if f.shifted then elemAt (front ++ ds.take n) (roundAt f front.length .shift) else zeroE) =
    (if f.shifted then elemAt (front ++ ds) (roundAt f front.length .shift) else zeroE)
  by_cases hs : f.shifted = true
  · have := hn hs
    rw [if_pos hs, if_pos hs, elemAt_take front ds n _ (by unfold roundAt; omega)]
  · rw [if_neg hs, if_neg hs]

theorem alpha_cut (hn : firstRound f .alpha + 1 ≤ n) :
    (ptsOf f front.length (front ++ ds.take n)).alpha =
      (ptsOf f front.length (front ++ ds)).alpha := by
  show elemAt (front ++ ds.take n) (roundAt f front.length .alpha) =
    elemAt (front ++ ds) (roundAt f front.length .alpha)
  rw [elemAt_take front ds n _ (by unfold roundAt; omega)]

theorem keyPt_cut (i m : Nat) (h1 : firstRound f (.key i m) + (m + 3) ≤ n)
    (h2 : firstRound f (.keyLine i m) + 1 ≤ n) :
    (ptsOf f front.length (front ++ ds.take n)).keyPt i (m + 1) =
      (ptsOf f front.length (front ++ ds)).keyPt i (m + 1) := by
  show behind m (f.orders i m) (varChals f front.length (front ++ ds.take n) (.key i m) m)
      (elemAt (front ++ ds.take n) (roundAt f front.length (.keyLine i m))) =
    behind m (f.orders i m) (varChals f front.length (front ++ ds) (.key i m) m)
      (elemAt (front ++ ds) (roundAt f front.length (.keyLine i m)))
  rw [varChals_take f front ds n _ _ (by omega),
    elemAt_take front ds n _ (by unfold roundAt; omega)]

theorem rhoT_cut (hn : firstRound f .join + 1 ≤ n) :
    (ptsOf f front.length (front ++ ds.take n)).tabPt 0 =
      (ptsOf f front.length (front ++ ds)).tabPt 0 := by
  show (drawsAt (front ++ ds.take n) (roundAt f front.length .join) f.mu).toArray.reverse =
    (drawsAt (front ++ ds) (roundAt f front.length .join) f.mu).toArray.reverse
  rw [drawsAt_take front ds n _ _ (by unfold roundAt; omega)]

theorem tabPt_cut (l : Nat) (h1 : firstRound f (.tab l) + (f.mu + l + 3) ≤ n)
    (h2 : firstRound f (.tabLine l) + 1 ≤ n) :
    (ptsOf f front.length (front ++ ds.take n)).tabPt (l + 1) =
      (ptsOf f front.length (front ++ ds)).tabPt (l + 1) := by
  show behind (f.mu + l) (orderDefault (f.mu + l))
      (varChals f front.length (front ++ ds.take n) (.tab l) (f.mu + l))
      (elemAt (front ++ ds.take n) (roundAt f front.length (.tabLine l))) =
    behind (f.mu + l) (orderDefault (f.mu + l))
      (varChals f front.length (front ++ ds) (.tab l) (f.mu + l))
      (elemAt (front ++ ds) (roundAt f front.length (.tabLine l)))
  rw [varChals_take f front ds n _ _ (by omega),
    elemAt_take front ds n _ (by unfold roundAt; omega)]

theorem zeroPt_cut (hn : firstRound f .zero + 1 ≤ n) :
    (ptsOf f front.length (front ++ ds.take n)).zeroPt =
      (ptsOf f front.length (front ++ ds)).zeroPt := by
  show (drawsAt (front ++ ds.take n) (roundAt f front.length .zero) (f.mu + f.d)).toArray.reverse =
    (drawsAt (front ++ ds) (roundAt f front.length .zero) (f.mu + f.d)).toArray.reverse
  rw [drawsAt_take front ds n _ _ (by unfold roundAt; omega)]

/-! ## 4 What a stage reads in front of it -/

/-- theta and alpha, in front of a stage behind "LKP". -/
theorem two_cut (s : Stage) (h0 : Fore .shift s) (h1 : Fore .alpha s) :
    (ptsOf f front.length (front ++ ds.take (firstRound f s))).theta =
        (ptsOf f front.length (front ++ ds)).theta ∧
      (ptsOf f front.length (front ++ ds.take (firstRound f s))).alpha =
        (ptsOf f front.length (front ++ ds)).alpha :=
  ⟨theta_cut f front ds fun hs => before (mem_shift hs) h0,
    alpha_cut f front ds (before (mem_alpha f) h1)⟩

/-- The table side's point in front of level l, in front of a stage behind
that level's forerunners. -/
theorem tab_cut (s : Stage) (l : Nat) (hl : l ≤ f.d) (hj : Fore .join s)
    (h1 : ∀ k, k + 1 = l → Fore (.tab k) s ∧ Fore (.tabLine k) s) :
    (ptsOf f front.length (front ++ ds.take (firstRound f s))).tabPt l =
      (ptsOf f front.length (front ++ ds)).tabPt l := by
  cases l with
  | zero => exact rhoT_cut f front ds (before (mem_join f) hj)
  | succ k =>
    have a := before (f := f) (mem_tabOf (show k < f.d by omega)) (h1 k rfl).1
    have b := before (f := f) (mem_tabLine (show k < f.d by omega)) (h1 k rfl).2
    rw [rounds_tab] at a
    exact tabPt_cut f front ds k a b

/-- **A stage's job reads the challenges in front of the stage alone**: at any number of parts. -/
theorem same_cut (s : Stage) (hs : s ∈ stages f) :
    SameForP f s (ptsOf f front.length (front ++ ds.take (firstRound f s)))
      (ptsOf f front.length (front ++ ds)) := by
  cases s with
  | tie j => exact two_cut f front ds _ (by simp [Fore, lt3, rank]) (by simp [Fore, lt3, rank])
  | split i => exact two_cut f front ds _ (by simp [Fore, lt3, rank]) (by simp [Fore, lt3, rank])
  | key i m =>
    obtain ⟨a, b⟩ := two_cut f front ds (.key i m) (by simp [Fore, lt3, rank])
      (by simp [Fore, lt3, rank])
    refine ⟨a, b, ?_⟩
    obtain ⟨x, hx, rfl, hm⟩ := ProofFile.Honest.K3.mem_key hs
    cases m with
    | zero => rfl
    | succ k =>
      have c := before (f := f) (mem_keyOf hx (show k < x.1 by omega))
        (s := .key x.2 (k + 1)) (by simp [Fore, lt3, rank])
      have d := before (f := f) (mem_keyLine hx (show k < x.1 by omega))
        (s := .key x.2 (k + 1)) (by simp [Fore, lt3, rank]; omega)
      rw [rounds_key] at c
      exact keyPt_cut f front ds x.2 k c d
  | tab l =>
    obtain ⟨a, b⟩ := two_cut f front ds (.tab l) (by simp [Fore, lt3, rank])
      (by simp [Fore, lt3, rank])
    exact ⟨a, b, tab_cut f front ds _ l (Nat.le_of_lt (tab_lt hs)) (by simp [Fore, lt3, rank])
      fun k hk => by subst hk; exact ⟨by simp [Fore, lt3, rank], by simp [Fore, lt3, rank]⟩⟩
  | leaves =>
    obtain ⟨a, b⟩ := two_cut f front ds .leaves (by simp [Fore, lt3, rank])
      (by simp [Fore, lt3, rank])
    exact ⟨a, b, tab_cut f front ds _ f.d (Nat.le_refl _) (by simp [Fore, lt3, rank])
      fun k _ => ⟨by simp [Fore, lt3, rank], by simp [Fore, lt3, rank]⟩⟩
  | bits =>
    obtain ⟨a, b⟩ := two_cut f front ds .bits (by simp [Fore, lt3, rank])
      (by simp [Fore, lt3, rank])
    exact ⟨a, b, zeroPt_cut f front ds (before (mem_zero f) (by simp [Fore, lt3, rank]))⟩
  | shift => trivial
  | alpha => trivial
  | join => trivial
  | keyLine i m => trivial
  | tabLine l => trivial
  | zero => trivial

end Cut

/-- CONDITIONAL ON `Fit R`: the first clause of `NumberedP`. -/
theorem same_of_fitP (R : Course W) (hF : Fit R) (s : Stage) (hs : s ∈ stages R.f) :
    SameForP R.f s (ptsOf R.f R.a.base (R.front s).heard) R.pts := by
  show SameForP R.f s (ptsOf R.f R.a.base (R.t.heard ++ R.ds.take (firstRound R.f s)))
    (ptsOf R.f R.a.base (R.t.heard ++ R.ds))
  rw [← hF.base]
  exact same_cut R.f R.t.heard R.ds s hs

/-! ## 5 The theorem -/

/-- CONDITIONAL ON `Fit R`: the point behind a level of any part's tree is made of the level's own
challenges and the line's sample. -/
theorem key_of_fitP (R : Course W) (hF : Fit R) {y : Nat × Nat} (hy : y ∈ R.f.parts.zipIdx)
    (m : Nat)
    (hm : m < y.1) : R.pts.keyPt y.2 (m + 1) =
      behind m (R.f.orders y.2 m) ((R.r (.key y.2 m)).take m) (R.xiK y.2 m) := by
  have e : R.pts.keyPt y.2 (m + 1) = behind m (R.f.orders y.2 m)
      (varChals R.f R.a.base (R.t.heard ++ R.ds) (.key y.2 m) m)
      (elemAt (R.t.heard ++ R.ds) (roundAt R.f R.a.base (.keyLine y.2 m))) := rfl
  have ex : R.xiK y.2 m = elemAt (R.t.heard ++ R.ds) (roundAt R.f R.a.base (.keyLine y.2 m)) := by
    show (R.pts.keyPt y.2 (m + 1)).getD 0 zeroE = _
    rw [e, head_behind]
  rw [ex, r_take R hF (mem_keyOf hy hm) (k := levelCall m) rfl (by rw [levelCall_len]), e]

/-- **CONDITIONAL ON `Fit R` ALONE, AT ANY NUMBER OF PARTS: the course's challenges are numbered as
`NumberedP R` says.** A course that passes the test for `Fit`: Honest/K3/Parts/Member.lean. -/
theorem numberedP_of_fit (R : Course W) (hF : Fit R) : NumberedP R where
  same := fun s hs => same_of_fitP R hF s hs
  len := fun s hs => len_of_fit R hF s hs
  key := fun _ hy m hm => key_of_fitP R hF hy m hm
  tab := fun l hl => tab_of_fit R hF l hl
  zb0 := zb0_of_fit R hF
  zb1 := zb1_of_fit R hF
  masks := fun s _ => masks_len R s

#print axioms ProofFile.Honest.K3.Parts.sum_before
#print axioms ProofFile.Honest.K3.Parts.before
#print axioms ProofFile.Honest.K3.Parts.mem_shift
#print axioms ProofFile.Honest.K3.Parts.mem_alpha
#print axioms ProofFile.Honest.K3.Parts.mem_join
#print axioms ProofFile.Honest.K3.Parts.mem_zero
#print axioms ProofFile.Honest.K3.Parts.mem_keyLine
#print axioms ProofFile.Honest.K3.Parts.mem_tabLine
#print axioms ProofFile.Honest.K3.Parts.theta_cut
#print axioms ProofFile.Honest.K3.Parts.alpha_cut
#print axioms ProofFile.Honest.K3.Parts.keyPt_cut
#print axioms ProofFile.Honest.K3.Parts.rhoT_cut
#print axioms ProofFile.Honest.K3.Parts.tabPt_cut
#print axioms ProofFile.Honest.K3.Parts.zeroPt_cut
#print axioms ProofFile.Honest.K3.Parts.two_cut
#print axioms ProofFile.Honest.K3.Parts.tab_cut
#print axioms ProofFile.Honest.K3.Parts.same_cut
#print axioms ProofFile.Honest.K3.Parts.same_of_fitP
#print axioms ProofFile.Honest.K3.Parts.key_of_fitP
#print axioms ProofFile.Honest.K3.Parts.numberedP_of_fit

end ProofFile.Honest.K3.Parts
