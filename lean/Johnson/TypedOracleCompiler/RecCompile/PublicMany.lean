-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/PublicMany.lean: a public algorithm of any number of digests: one answer of
the hash function at a first string, then answers at a list of strings that is made of the first
answer. Under every oracle it returns the oracle's own answers; it tosses no coin, asks public
strings alone, and asks none twice.

Why. `pub_lift` (Johnson/TypedOracleCompiler/RecCompile/PublicLift.lean) lets public digests be answers of the drawn
function at no cost to a bound. It takes the public algorithm as a letter and asks three things of
it: no coins; strings of a set Pt alone; none twice. LinkAnsPublic.lean has one such algorithm,
`pub2`, of two digests. A check on a proof file or a key file has four: the digest of the public
files, and the digests of three chains' parameter bytes, which are made of the first. Here the
number is free.

Two choices. The list hangs on the first answer as a whole (`ss : Dig lam → List (List Bool)`), not
string by string: where no chains can be planned at a drawn digest the list is empty. And the
algorithm keeps what it has asked and does not ask a string again: so "none twice" has no premise.
That the strings of a list are pairwise apart need not be shown, at no digest; where two are one,
both places get the one answer, which is what the oracle would have said.

Main names.
  `askOnce`: asks the strings of a list in turn, none twice.
  `pubN κ s0 ss`: the algorithm: c at s0; the answers at `ss c`; it returns κ of c and these
    answers. κ: into whatever type D of public digests a user has.
  `PtN s0 ss`: the public strings: s0, and every string of `ss c` at every c.
  `pubN_det`: under every oracle g its value is κ of g's own answers. No premise.
  `pubN_noCoin`, `pubN_asksIn`, `pubN_asksIn_of`, `pubN_noRepeat`: the three things that `pub_lift`
    asks. No premise, but for the user's own Pt in the third.
  `pubN_queries`: at most n + 1 strings, if no list is longer than n.
  `pub2_det_pubN`: `pub2` is a case, in its values.

What is not claimed. `PtN` is wide: it holds the strings of `ss c` at EVERY c, not at the digest
that occurs alone: a run can be answered with any c. Whoever uses a bound must show of that whole
set that the verifier asks none of it. No bound is stated here. Nothing on any hash function, format
or file: strings are letters. `pub2_det_pubN` is an equation of values; as trees the two differ
where `s1 c` is s0. Nothing on soundness; no probability.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.LinkAnsPublic

set_option autoImplicit false

namespace TypedOracleCompiler.Compile.Batch.Cms
open Rom
open _root_.Iop (Dig)

/-- Looking a string up behind a new first entry: nothing is found only if the string is another and
nothing was found before. -/
theorem lookup_cons_none {lam : ℕ} {s x : List Bool} {r : Dig lam}
    {seen : List (List Bool × Dig lam)} (h : ((s, r) :: seen).lookup x = none) :
    x ≠ s ∧ seen.lookup x = none := by
  by_cases e : x = s
  · subst e
    simp at h
  · refine ⟨e, ?_⟩
    rw [List.lookup_cons] at h
    have hb : (x == s) = false := by simpa using e
    rw [hb] at h
    exact h

variable {lam : ℕ} {D : Type}

/-- The answer of the oracle g at a string. -/
abbrev answerAt (g : Fam (rom lam)) (s : List Bool) : Dig lam := g () s

/-- Asks the strings of a list in turn, NONE TWICE: a string that stands in `seen` is not asked; its
answer is taken from there. acc: the answers so far, the last one first. At the end: κ of all
answers, in the list's order. -/
def askOnce (κ : List (Dig lam) → D) :
    List (List Bool × Dig lam) → List (Dig lam) → List (List Bool) → OComp (rom lam) D
  | _, acc, [] => .pure (κ acc.reverse)
  | seen, acc, s :: l =>
    match seen.lookup s with
    | some r => askOnce κ seen (r :: acc) l
    | none => .query () s fun r => askOnce κ ((s, r) :: seen) (r :: acc) l

/-- At a string that stands in `seen`: nothing is asked. -/
theorem askOnce_some (κ : List (Dig lam) → D) {seen : List (List Bool × Dig lam)}
    (acc : List (Dig lam)) {s : List Bool} (l : List (List Bool)) {r : Dig lam}
    (h : seen.lookup s = some r) : askOnce κ seen acc (s :: l) = askOnce κ seen (r :: acc) l := by
  rw [askOnce, h]

/-- At a string that does not stand in `seen`: it is asked, and kept. -/
theorem askOnce_none (κ : List (Dig lam) → D) {seen : List (List Bool × Dig lam)}
    (acc : List (Dig lam)) {s : List Bool} (l : List (List Bool)) (h : seen.lookup s = none) :
    askOnce κ seen acc (s :: l) =
      .query () s fun r => askOnce κ ((s, r) :: seen) (r :: acc) l := by
  rw [askOnce, h]

/-- Its value under an oracle g, if `seen` holds g's own answers: κ of g's answers at all strings.
-/
theorem askOnce_det (κ : List (Dig lam) → D) (g : Fam (rom lam)) :
    ∀ (l : List (List Bool)) (seen : List (List Bool × Dig lam)) (acc : List (Dig lam)),
      (∀ s r, seen.lookup s = some r → r = g () s) →
      (askOnce κ seen acc l).det g = κ (acc.reverse ++ l.map (answerAt g))
  | [], seen, acc, _ => by
    rw [askOnce]
    simp [OComp.det]
  | s :: l, seen, acc, h => by
    cases hs : seen.lookup s with
    | some r =>
      rw [askOnce_some κ acc l hs, askOnce_det κ g l seen (r :: acc) h, h s r hs]
      simp
    | none =>
      rw [askOnce_none κ acc l hs]
      show (askOnce κ ((s, g () s) :: seen) (g () s :: acc) l).det g = _
      rw [askOnce_det κ g l _ _ ?_]
      · simp
      · intro x r hx
        by_cases e : x = s
        · subst e
          simp at hx
          exact hx.symm
        · rw [List.lookup_cons] at hx
          have hb : (x == s) = false := by simpa using e
          rw [hb] at hx
          exact h x r hx

/-- It asks strings of the list alone, and none that stands in `seen`. -/
theorem askOnce_asksIn (κ : List (Dig lam) → D) :
    ∀ (l : List (List Bool)) (seen : List (List Bool × Dig lam)) (acc : List (Dig lam)),
      (askOnce κ seen acc l).AsksIn fun _ (x : List Bool) => x ∈ l ∧ seen.lookup x = none
  | [], _, _ => by
    rw [askOnce]
    trivial
  | s :: l, seen, acc => by
    cases hs : seen.lookup s with
    | some r =>
      rw [askOnce_some κ acc l hs]
      exact (askOnce_asksIn κ l seen (r :: acc)).mono
        fun _ x hx => ⟨List.mem_cons_of_mem _ hx.1, hx.2⟩
    | none =>
      rw [askOnce_none κ acc l hs]
      exact ⟨⟨List.mem_cons_self, hs⟩, fun r =>
        (askOnce_asksIn κ l ((s, r) :: seen) (r :: acc)).mono
          fun _ x hx => ⟨List.mem_cons_of_mem _ hx.1, (lookup_cons_none hx.2).2⟩⟩

/-- It asks no string twice. No premise. -/
theorem askOnce_noRepeat (κ : List (Dig lam) → D) :
    ∀ (l : List (List Bool)) (seen : List (List Bool × Dig lam)) (acc : List (Dig lam)),
      NoRepeat (askOnce κ seen acc l)
  | [], _, _ => by
    rw [askOnce]
    trivial
  | s :: l, seen, acc => by
    cases hs : seen.lookup s with
    | some r =>
      rw [askOnce_some κ acc l hs]
      exact askOnce_noRepeat κ l seen (r :: acc)
    | none =>
      rw [askOnce_none κ acc l hs]
      exact fun r => ⟨(askOnce_asksIn κ l ((s, r) :: seen) (r :: acc)).mono
        fun _ x hx => (lookup_cons_none hx.2).1, askOnce_noRepeat κ l ((s, r) :: seen) (r :: acc)⟩

/-- It tosses no coin. -/
theorem askOnce_noCoin (κ : List (Dig lam) → D) :
    ∀ (l : List (List Bool)) (seen : List (List Bool × Dig lam)) (acc : List (Dig lam)),
      (askOnce κ seen acc l).NoCoin
  | [], _, _ => by
    rw [askOnce]
    trivial
  | s :: l, seen, acc => by
    cases hs : seen.lookup s with
    | some r =>
      rw [askOnce_some κ acc l hs]
      exact askOnce_noCoin κ l seen (r :: acc)
    | none =>
      rw [askOnce_none κ acc l hs]
      exact fun r => askOnce_noCoin κ l ((s, r) :: seen) (r :: acc)

/-- It asks at most as many strings as the list has. -/
theorem askOnce_queries (κ : List (Dig lam) → D) :
    ∀ (l : List (List Bool)) (seen : List (List Bool × Dig lam)) (acc : List (Dig lam)),
      (askOnce κ seen acc l).QueryBound l.length
  | [], _, _ => by
    rw [askOnce]
    trivial
  | s :: l, seen, acc => by
    cases hs : seen.lookup s with
    | some r =>
      rw [askOnce_some κ acc l hs]
      exact (askOnce_queries κ l seen (r :: acc)).mono (Nat.le_succ _)
    | none =>
      rw [askOnce_none κ acc l hs]
      exact fun r => askOnce_queries κ l ((s, r) :: seen) (r :: acc)

/-- THE PUBLIC ALGORITHM OF ANY NUMBER OF DIGESTS: c at the string s0; then an answer at each string
of the list `ss c`, which is made of c; a string that was asked before is not asked again. It
returns κ of c and the answers, in the list's order. -/
def pubN (κ : Dig lam → List (Dig lam) → D) (s0 : List Bool) (ss : Dig lam → List (List Bool)) :
    OComp (rom lam) D :=
  .query () s0 fun c => askOnce (κ c) [(s0, c)] [] (ss c)

/-- The public strings: s0, and the strings of `ss c` at every first digest c. -/
def PtN (s0 : List Bool) (ss : Dig lam → List (List Bool)) (s : List Bool) : Prop :=
  s = s0 ∨ ∃ c, s ∈ ss c

variable (κ : Dig lam → List (Dig lam) → D) (s0 : List Bool) (ss : Dig lam → List (List Bool))

/-- UNDER EVERY ORACLE g THE PUBLIC ALGORITHM RETURNS g's OWN ANSWERS: κ of g's answer c at s0 and
of g's answers at the strings of `ss c`. No premise. -/
theorem pubN_det (g : Fam (rom lam)) :
    (pubN κ s0 ss).det g =
      κ (g () s0) ((ss (g () s0)).map (answerAt g)) := by
  show (askOnce (κ (g () s0)) [(s0, g () s0)] [] (ss (g () s0))).det g = _
  rw [askOnce_det (κ (g () s0)) g _ _ _ ?_]
  · simp
  · intro x r hx
    by_cases e : x = s0
    · subst e
      simp at hx
      exact hx.symm
    · rw [List.lookup_cons] at hx
      have hb : (x == s0) = false := by simpa using e
      rw [hb] at hx
      simp at hx

/-- No coin. -/
theorem pubN_noCoin : (pubN κ s0 ss).NoCoin := fun c => askOnce_noCoin (κ c) _ _ _

/-- Public strings alone. -/
theorem pubN_asksIn : (pubN κ s0 ss).AsksIn fun _ (s : List Bool) => PtN s0 ss s :=
  ⟨Or.inl rfl, fun c => (askOnce_asksIn (κ c) (ss c) _ _).mono fun _ _ hx => Or.inr ⟨c, hx.1⟩⟩

/-- Strings of any property Pt that s0 and all strings of all lists have. -/
theorem pubN_asksIn_of (Pt : List Bool → Prop) (h0 : Pt s0) (h1 : ∀ c s, s ∈ ss c → Pt s) :
    (pubN κ s0 ss).AsksIn fun _ (s : List Bool) => Pt s :=
  (pubN_asksIn κ s0 ss).mono fun _ s hs => by
    rcases hs with rfl | ⟨c, hc⟩
    · exact h0
    · exact h1 c s hc

/-- None twice. NO PREMISE: not that the strings are apart. -/
theorem pubN_noRepeat : NoRepeat (pubN κ s0 ss) :=
  fun c => ⟨(askOnce_asksIn (κ c) (ss c) _ _).mono fun _ _ hx => (lookup_cons_none hx.2).1,
    askOnce_noRepeat (κ c) _ _ _⟩

/-- At most n + 1 strings, if no list is longer than n. -/
theorem pubN_queries (n : ℕ) (hn : ∀ c, (ss c).length ≤ n) : (pubN κ s0 ss).QueryBound (n + 1) :=
  fun c => (askOnce_queries (κ c) (ss c) _ _).mono (hn c)

/-- The public algorithm of two digests (`pub2`, LinkAnsPublic.lean) is a case, in its values: under
every oracle it returns what `pubN` returns at the one string `s1 c`. -/
theorem pub2_det_pubN (s1 : Dig lam → List Bool) (g : Fam (rom lam)) :
    (pub2 s0 s1).det g = (pubN (fun c ps => (c, ps.headD c)) s0 fun c => [s1 c]).det g := by
  rw [pubN_det]
  rfl

end TypedOracleCompiler.Compile.Batch.Cms
