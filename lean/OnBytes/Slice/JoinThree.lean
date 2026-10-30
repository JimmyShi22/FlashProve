-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/JoinThree.lean: a part of the join of three checkers, made with the library's
compiler.

OnBytes/Slice/PartO.lean joins three checkers over one random oracle on bit strings. A part there
(`PartO`) holds only what lives over the one oracle, and what is asked of it (`PartO.OK`,
`PartO.Stable`) is a bound, a measurability and a stability. This file wins these three from the
library's compiler: from an interface with its wiring, a compiled verifier as the step to one oracle
uses it (`Judge`, OnBytes/Slice/OneWorldJ.lean), the analysis' conclusion on it, an implementation
of the typed oracles by the one oracle, and a checker that fits.

Main definitions: `Part`, `Part.OK`, `Part.str`, `Part.raw`, `Part.bound`, `Part.lose`, `Part.toO`.
Main theorems.
 `Part.pr_lose`, `Part.measurable_lose`   the part's event is rare (`one_worldJ`), and its
                 probability over the coins is a measurable function of the oracle.
 `Part.toO_ok`   `PartO.OK` of `Part.toO`.
 `Part.toO_stable`   `PartO.Stable` of it, with the bound 2 (tC + 1 + tP)^2 / 2^lam
                 (OnBytes/Slice/OneMaker.lean: `stableLeaf_maker`).
 `Part.toO_lang_one`, `Part.toO_lang_two`   the language on raw strings, at one and at two strings.

The language on raw strings. The judge's language speaks of strings of the interface's own type.
`Part.toO` says it of raw strings: a list of raw strings is in the language if it is the list of
the raw forms of strings that are.

All of this stands over the compiler's types as they are today. A part that is made with another
compiler does not pass through this file.

What is not claimed. That any `Part` meets `Part.OK`.
What a reading is worth is said at `Reading`
(OnBytes/Slice/Reading.lean): with readings that keep nothing, the raw string is a constant and has
nothing to do with any log. What the heads of OnBytes/Slice/PartO.lean and OneWorldJ.lean do not
claim.

-/
import OnBytes.Slice.PartO
import OnBytes.Slice.OneWorldJ
import OnBytes.Slice.SameRead

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Rom Prob Compile Compile.Batch MeasureTheory
open scoped ENNReal

variable {lam : ℕ} {γ Sg : Type}

/-! ## One part: a checker with the analysis of its compiled verifier -/

/-- **One of the three parts of the join, made with the library's compiler**: an interface with its
wiring, a compiled verifier as the step to one oracle uses it (`Judge`), an error e, an
implementation of the typed oracles by one oracle, a checker on the maker's output, the roots that
are read off the maker's output, two counts, and a match of the interface's symbols with a type of
symbols that all parts share. -/
structure Part (lam : ℕ) (γ Sg : Type) where
  /-- the first of the two types over which the interface is stated (indices) -/
  I : Type
  /-- the second (instances) -/
  X : Type
  /-- the interface -/
  L : BatchProtocol I X
  /-- its wiring -/
  W : QueryLayout lam L
  /-- what the checker returns -/
  Out : Type
  /-- the compiled verifier -/
  J : Judge W Out
  /-- the error of its analysis -/
  e : ℝ≥0∞
  /-- the implementation -/
  m : OracleCoding (spec lam W.K L) lam
  /-- the checker -/
  chk : γ → OComp (rom lam) (Option Out)
  /-- the roots, read off the maker's output -/
  rts : γ → List (Dig lam)
  /-- a bound on the checker's queries -/
  tR : ℕ
  /-- a bound on the number of roots -/
  a : ℕ
  /-- the match of symbols -/
  u : L.Symbol ≃ Sg

namespace Part
variable (s : Part lam γ Sg)

/-- What `one_worldJ` asks of a part; and that a leaf's and a vertex's answer is taken as it is:
`join_verify` does not use that; `sameRaw_of` (OnBytes/Slice/SameRawOf.lean) asks it. -/
structure OK : Prop where
  /-- the analysis' conclusion on the compiled verifier -/
  judge : JudgeAt s.W s.J s.e
  /-- a leaf's and a vertex's answer is one block, taken as it is -/
  one : OneBlock s.m
  /-- the checker tosses no coin -/
  noCoin : ∀ x, (s.chk x).NoCoin
  /-- it asks at most tR strings -/
  queries : ∀ x, (s.chk x).QueryBound s.tR
  /-- at most a roots are read off the maker's output -/
  few : ∀ x, (s.rts x).length ≤ s.a
  /-- under every oracle the compiled verifier accepts what the checker returns, under the family
  that is read out of the oracle through m, and that output is `ok` -/
  fit : ∀ (g : Fam (rom lam)) (x : γ) (o : s.Out), (s.chk x).det g = some o →
    (s.J.run o).det (readBlocks s.m g) = true ∧ s.J.ok o
  /-- the roots of what the checker returns are among those read off the maker's output -/
  named : ∀ (g : Fam (rom lam)) (x : γ) (o : s.Out), (s.chk x).det g = some o →
    ∀ r ∈ s.J.roots o, r ∈ s.rts x

/-- The string that the part's reading reads off a log under a root. -/
noncomputable def str (σ : Trace (rom lam)) (cm : Dig lam) : Fin s.L.wordLength → s.L.Symbol :=
  s.J.R.at s.W (singleTr s.m σ) cm

/-- The same as a raw string of the shared symbols. -/
noncomputable def raw (σ : Trace (rom lam)) (cm : Dig lam) : Raw Sg := rawOf s.u (s.str σ cm)

/-- `one_worldJ`'s bound for a maker with at most t queries. -/
noncomputable def bound (t : ℕ) : ℝ≥0∞ :=
  ((t + s.a + s.tR + s.J.tV : ℕ) : ℝ≥0∞) * s.e +
    2 * ((t + s.a + s.tR + s.J.tV + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam

/-- **The part's event**, on the maker's output and log, under the oracle g: the checker returns
something while the strings that are read off the log under its roots are outside the language. -/
def lose (g : Fam (rom lam)) : Set (γ × Trace (rom lam)) :=
  {x | ∃ o, (s.chk x.1).det g = some o ∧ ¬ s.J.Lang o ((s.J.roots o).map (s.str x.2))}

/-- The part's event has probability at most the part's bound, for every maker. -/
theorem pr_lose (hs : s.OK) (A : OComp (rom lam) γ) (t : ℕ) (hA : A.QueryBound t) :
    Rom.Pr A.withTrace s.lose ≤ s.bound t := by
  have h := one_worldJ s.W s.J s.e hs.judge s.m hs.one.leaf1 hs.one.node1 s.chk s.rts s.tR s.a
    hs.noCoin hs.queries hs.few hs.fit hs.named A t hA
  rw [Pr_twoExp_det A s.chk hs.noCoin] at h
  exact h

/-- The probability of the part's event over the maker's coins is a measurable function of the
oracle. -/
theorem measurable_lose (hs : s.OK) (A : OComp (rom lam) γ) :
    Measurable fun g => PrCoins g A.withTrace (s.lose g) :=
  measurable_twoExp_det A s.chk hs.noCoin (winJOne s.W s.m s.J fun _ y => y)

/-! ## The part as it is seen over the one oracle -/

/-- The raw form of a string determines the string. -/
theorem rawOf_injective {n : ℕ} {S : Type} (u : S ≃ Sg) :
    Function.Injective (rawOf u : (Fin n → S) → Raw Sg) := fun y₁ y₂ h =>
  funext fun q => u.injective (((rawOf_eq_iff u u y₁ y₂).1 h).2 q q rfl)

/-- **The part as it is seen over the one oracle.** Its language holds of a list of raw strings if
that is the list of the raw forms of strings of which the judge's language holds. -/
noncomputable def toO : PartO lam γ Sg where
  Out := s.Out
  chk := s.chk
  roots := s.J.roots
  Lang := fun o Ys => ∃ ys, Ys = ys.map (rawOf s.u) ∧ s.J.Lang o ys
  raw := s.raw
  bound := s.bound

/-- The language on raw strings, at one string. -/
theorem toO_lang_one (o : s.Out) (Y : Raw Sg) :
    s.toO.Lang o [Y] ↔ ∃ y, Y = rawOf s.u y ∧ s.J.Lang o [y] := by
  constructor
  · rintro ⟨ys, e, h⟩
    match ys, e, h with
    | [y], e, h => exact ⟨y, (List.cons.inj e).1, h⟩
  · rintro ⟨y, rfl, h⟩
    exact ⟨[y], rfl, h⟩

/-- The language on raw strings, at two strings. -/
theorem toO_lang_two (o : s.Out) (Y₀ Y₁ : Raw Sg) :
    s.toO.Lang o [Y₀, Y₁] ↔
      ∃ y₀ y₁, Y₀ = rawOf s.u y₀ ∧ Y₁ = rawOf s.u y₁ ∧ s.J.Lang o [y₀, y₁] := by
  constructor
  · rintro ⟨ys, e, h⟩
    match ys, e, h with
    | [y₀, y₁], e, h =>
      exact ⟨y₀, y₁, (List.cons.inj e).1, (List.cons.inj (List.cons.inj e).2).1, h⟩
  · rintro ⟨y₀, y₁, rfl, rfl, h⟩
    exact ⟨[y₀, y₁], rfl, h⟩

/-- The two forms of the part's event are one. -/
theorem toO_lose (g : Fam (rom lam)) : s.toO.lose g = s.lose g := by
  ext x
  have e : ∀ o : s.Out, (s.J.roots o).map (s.raw x.2) =
      ((s.J.roots o).map (s.str x.2)).map (rawOf s.u) := fun o => by
    rw [List.map_map]
    rfl
  constructor
  · rintro ⟨o, ho, hn⟩
    exact ⟨o, ho, fun h => hn ⟨_, e o, h⟩⟩
  · rintro ⟨o, ho, hn⟩
    refine ⟨o, ho, ?_⟩
    rintro ⟨ys, hy, h⟩
    have hy' : ((s.J.roots o).map (s.str x.2)).map (rawOf s.u) = ys.map (rawOf s.u) :=
      (e o).symm.trans hy
    rw [← (List.map_injective_iff.2 (rawOf_injective s.u)) hy'] at h
    exact hn h

/-- **What the join asks of every part.** -/
theorem toO_ok (hs : s.OK) : s.toO.OK where
  rare := fun A t hA => by
    have e : s.toO.lose = s.lose := funext s.toO_lose
    rw [e]
    exact s.pr_lose hs A t hA
  meas := fun A => by
    have e : s.toO.lose = s.lose := funext s.toO_lose
    rw [e]
    exact s.measurable_lose hs A

/-- **What the join asks of the first part beside**: what the part reads under a root that the
committer's output and log name does not change as the prover asks on, except with probability at
most 2 (tC + 1 + tP)^2 / 2^lam. -/
theorem toO_stable (hs : s.OK) :
    s.toO.Stable fun tC tP => 2 * ((tC + 1 + tP : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  intro β δ C rt P tC tP hC hP
  refine le_trans (Rom.Pr_mono _ fun _ w hw => ?_)
    (stableLeaf_maker s.m hs.one.leaf1 hs.one.node1 C rt P tC tP hC hP)
  obtain ⟨cm, hrt, hne⟩ := hw
  refine ⟨cm, hrt, s.W.depth, ?_⟩
  by_contra hall
  push Not at hall
  exact hne (congrArg (rawOf s.u) (s.J.R.at_congr hall))

end Part

end OnBytes.Slice
