-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/PartO.lean: three checkers over one random oracle on bit strings, joined: one bound,
with what is proved read off the committer's own log. Stated over the one oracle alone.

This file is made for a run of a verifier that reads three files (a key, an entry, a proof), each
with a checker of its own: the first speaks of the string under a root cm, the second of the strings
under cm and a second root cm', the third of the string under cm'. For each checker a bound is
supposed on the chance that it says yes while its language fails of the strings that are read off
the maker's log. This file adds the three bounds in one experiment.

NOTHING TYPED STANDS HERE. A part (`PartO`) holds only what lives over the one oracle: what its
checker returns, the checker, the roots in what it returns, a language on raw strings, a way to read
a raw string off a log under a root, and a bound. How the bound was won (an interface, a compiled
verifier, its analysis, an implementation of typed oracles by the one oracle) is not seen. So the
three parts may come from different compilers. A part's bound may also pay for events of the part's
own, such as a clash among the strings that its checker asks: nothing here asks that a compiled
verifier accepts what the checker returns under every oracle. OnBytes/Slice/JoinThree.lean makes
such a part from the library's compiler.

The experiment. The oracle is a function from all bit strings to strings of lam bits, each value
drawn uniformly and independently. A committer C asks it at most tC strings and puts out a value. A
prover P, which sees that value and not C's log, asks at most tP strings and puts out a value. Both
may toss coins. The three checkers are not run: the events speak of the one value that each has
under the drawn oracle in the run in which every coin toss yields 0; for a checker without coins
that is its value. An outcome w holds C's output with its log (w.1.1), P's output (w.1.2) and the
whole log (w.2).

`join_verify`, the core. `Yes` is any event, which may depend on the oracle, and may read both logs,
which no verifier sees; X a further event with a bound bX. Asked: outside X no two strings of the
whole log have one answer; and outside X a yes gives (where it may be used that the whole log begins
with C's log) the three checkers' values, the tie between their roots (the root that `rt` reads off
C's output and log is the first checker's root and the second's first; the second's second root is
the third's), and that `Good` of the third checker's value and the raw string that the first part
reads under cm off THE COMMITTER's OWN LOG gives `Fine`. Then "yes and not `Fine`" has probability
at most the sum of the three parts' bounds at t := tC + tP, of the first part's bound for "what it
reads under cm in C's log changes as P asks on" (`PartO.Stable`), and of bX. X is the place for "the
published digest does not lead to the first root".

`join_three`, its instance without a verifier: the tie between the roots STANDS IN THE EVENT, and X
is "two strings of the log have one answer", with the bound (tC + tP)^2 / 2^lam
(OnBytes/Slice/OneMaker.lean: `clash_maker`). No term there stands for "`rt` gives the first
checker's root": such a bound is owed elsewhere.

On "probability". Nothing is asked on the measurability of `Yes` or X. `Rom.Pr` is a lower integral
over the oracle: it is the probability only where the event's probability over the coins is a
measurable function of the oracle. Where X's is not, `hX` asks less than its words and the bound
says less than its words. For a verifier without coins `measurable_twoExp_det`
(OnBytes/Slice/OneLog.lean) gives it for "yes and not `Fine`"; `measurable_yes` gives it from a
condition on `Yes`.

Main definitions: `PartO`, `PartO.lose`, `PartO.OK`, `PartO.Stable`, `SameRaw`.
Main theorems: `PartO.meas_of_noCoin`, `PartO.Stable.of_sameRaw`, `join_verify`, `join_three`,
`measurable_yes`, `measurable_join`.

The hypotheses on the parts. `PartO.OK` of each: its event has probability at most its bound, for
every maker, and that probability over the coins is a measurable function of the oracle.
`PartO.Stable` of the first; it passes along `SameRaw`, at the price of one term more
(`PartO.Stable.of_sameRaw`), so one part's stability serves all. `SameRaw` of the first and second
part and of the second and third: off a log without a clash both read one raw string under every
root: it makes the three parts' readings one. `hpath`: if the three languages hold of one raw
string, of that and a second, and of the second, `Good` holds of the first.

What is not claimed. EVERYTHING IS A VARIABLE HERE: checkers, readings, languages, bounds, `Good`,
`Yes`, `Fine` and X. That any three parts meet the hypotheses is not shown, nor that any verifier's
yes meets `hYes`. All content lies in the three `PartO.OK`, in `hpath`, in `hYes` and `hX`, and in
what `Good` and `Fine` say. With `Fine` always true, or `Yes` empty, the statement is empty. In
`join_three` a run in which the checkers say yes on other roots is not counted, and nothing there
bounds such runs. The three checkers are handed the maker's whole output, in which C's log lies
beside C's and P's values: nothing asks that they do not read it. A checker that stands for a
verifier must not. A way of reading that gives a constant has nothing to do with any log, and meets
`PartO.Stable` and `SameRaw` for free. `Good` reads the third checker's value and the raw string
alone; what ties that value to P's output stands in `hYes`. Nothing says that the checkers ever
return something. Nothing reads bytes. Nothing on the program (the Lean port built from OnBytes/),
on the C++ verifier or on BLAKE2b. The bounds say nothing once they reach 1.

-/
import OnBytes.Slice.OneMaker
import OnBytes.Slice.Raw

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Rom Prob Compile Compile.Batch MeasureTheory
open scoped ENNReal

variable {lam : ℕ} {γ Sg : Type}

/-! ## One part, over the one oracle -/

/-- **One of the three parts of the join, as it is seen over the one oracle.** -/
structure PartO (lam : ℕ) (γ Sg : Type) where
  /-- what the checker returns -/
  Out : Type
  /-- the checker, on the maker's output -/
  chk : γ → OComp (rom lam) (Option Out)
  /-- the roots in what it returns, in order -/
  roots : Out → List (Dig lam)
  /-- the language, of the raw strings under these roots -/
  Lang : Out → List (Raw Sg) → Prop
  /-- the raw string that is read off a log under a root -/
  raw : Trace (rom lam) → Dig lam → Raw Sg
  /-- the bound on the part's event, for a maker with at most t queries -/
  bound : ℕ → ℝ≥0∞

namespace PartO
variable (s : PartO lam γ Sg)

/-- **The part's event**, on the maker's output and log, under the oracle g: the checker returns
something while the raw strings that are read off the log under its roots are outside the
language. -/
def lose (g : Fam (rom lam)) : Set (γ × Trace (rom lam)) :=
  {x | ∃ o, (s.chk x.1).det g = some o ∧ ¬ s.Lang o ((s.roots o).map (s.raw x.2))}

/-- What the join asks of every part. -/
structure OK : Prop where
  /-- the part's event has probability at most the part's bound, for every maker -/
  rare : ∀ (A : OComp (rom lam) γ) (t : ℕ), A.QueryBound t → Rom.Pr A.withTrace s.lose ≤ s.bound t
  /-- its probability over the maker's coins is a measurable function of the oracle -/
  meas : ∀ A : OComp (rom lam) γ, Measurable fun g => PrCoins g A.withTrace (s.lose g)

/-- **What the join asks of the first part beside**: what it reads under a root that the committer's
output and log name does not change as the prover asks on, except with probability at most bS tC tP.
-/
def Stable (bS : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∀ (β δ : Type) (C : OComp (rom lam) β) (rt : β × Trace (rom lam) → Option (Dig lam))
    (P : β → OComp (rom lam) δ) (tC tP : ℕ), C.QueryBound tC → (∀ x, (P x).QueryBound tP) →
    Rom.Pr (twoExp C P).withTrace (fun _ => {w | ∃ cm, rt w.1.1 = some cm ∧
      s.raw w.1.1.2 cm ≠ s.raw w.2 cm}) ≤ bS tC tP

/-- For a checker without coins the second clause of `PartO.OK` holds. -/
theorem meas_of_noCoin (h : ∀ x, (s.chk x).NoCoin) (A : OComp (rom lam) γ) :
    Measurable fun g => PrCoins g A.withTrace (s.lose g) :=
  measurable_twoExp_det A s.chk h
    {z | ∃ o, z.2 = some o ∧ ¬ s.Lang o ((s.roots o).map (s.raw z.1.2))}

end PartO

/-- Two parts read one raw string under every root, off every log in which no two strings have one
answer. It makes the parts' readings one: one length, one filling where nothing is found, one choice
of what is kept. The two may have makers' outputs of different types. -/
def SameRaw {γ' : Type} (s₁ : PartO lam γ Sg) (s₂ : PartO lam γ' Sg) : Prop :=
  ∀ σ : Trace (rom lam), NoClash σ → ∀ cm : Dig lam, s₁.raw σ cm = s₂.raw σ cm

/-- `SameRaw` can be read both ways. -/
theorem SameRaw.symm {γ' : Type} {s₁ : PartO lam γ Sg} {s₂ : PartO lam γ' Sg}
    (h : SameRaw s₁ s₂) : SameRaw s₂ s₁ := fun σ hσ cm => (h σ hσ cm).symm

/-- `SameRaw` passes through a middle part. -/
theorem SameRaw.trans {γ' γ'' : Type} {s₁ : PartO lam γ Sg} {s₂ : PartO lam γ' Sg}
    {s₃ : PartO lam γ'' Sg} (h : SameRaw s₁ s₂) (h' : SameRaw s₂ s₃) : SameRaw s₁ s₃ :=
  fun σ hσ cm => (h σ hσ cm).trans (h' σ hσ cm)

/-- **Stability passes along `SameRaw`**, at the price of the bound on "two strings of the whole log
have one answer". So a first part that reads as another part does has its stability from that
one. -/
theorem PartO.Stable.of_sameRaw {γ' : Type} {K : PartO lam γ Sg} {E : PartO lam γ' Sg}
    {bS : ℕ → ℕ → ℝ≥0∞} (h : SameRaw K E) (hE : E.Stable bS) :
    K.Stable fun tC tP => bS tC tP + (((tC + tP) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ lam := by
  intro β δ C rt P tC tP hC hP
  have h1 := hE β δ C rt P tC tP hC hP
  have h2 := clash_maker C P tC tP hC hP
  refine le_trans ?_ (add_le_add h1 h2)
  refine le_trans ?_ (Pr_union_le _ _ _ (measurable_PrCoins _ _))
  rw [twoExp_withTrace, Rom.Pr_bind_pure, Rom.Pr_bind_pure]
  refine Rom.Pr_mono _ fun _ z hz => ?_
  obtain ⟨cm, hrt, hne⟩ := hz
  by_cases hc : NoClash (z.1.2 ++ z.2.2)
  · refine Or.inl ⟨cm, hrt, ?_⟩
    have hc1 : NoClash z.1.2 := hc.of_subset fun e he => List.mem_append_left _ he
    show E.raw z.1.2 cm ≠ E.raw (z.1.2 ++ z.2.2) cm
    rw [← h _ hc1 cm, ← h _ hc cm]
    exact hne
  · exact Or.inr hc

/-! ## The join -/

section
variable {β δ : Type}
/-- **On the one experiment the whole log begins with the committer's.** An event has the
probability of its part in which the whole log is the committer's log and then a further list. -/
theorem Pr_twoExp_shape (C : OComp (rom lam) β) (P : β → OComp (rom lam) δ)
    (E : Fam (rom lam) → Set (((β × Trace (rom lam)) × δ) × Trace (rom lam))) :
    Rom.Pr (twoExp C P).withTrace E =
      Rom.Pr (twoExp C P).withTrace fun g => {w | w ∈ E g ∧ ∃ τ, w.2 = w.1.1.2 ++ τ} := by
  rw [twoExp_withTrace, Rom.Pr_bind_pure, Rom.Pr_bind_pure]
  refine congrArg _ (funext fun g => Set.ext fun z => ?_)
  exact ⟨fun h => ⟨h, z.2.2, rfl⟩, fun h => h.1⟩

/-- **The join, for any event "yes".** The experiment (see the head): a committer C with at most tC
queries, then a prover P on C's output with at most tP; an outcome w holds C's output with its log
(w.1.1), P's output (w.1.2) and the whole log (w.2). With probability at most the sum of the three
parts' bounds at tC + tP, of bS tC tP and of bX: w lies in `Yes g` and `Fine w` fails. Asked:
`PartO.OK` of the three parts; `PartO.Stable` of the first, with the bound bS; `SameRaw K E`,
`SameRaw E F`; `hpath`; X has probability at most bX (`hX`); outside X no two strings of the whole
log have one answer (`hXc`); outside X, and where the whole log begins with C's log, a yes gives
values oK, oE, oF of the three checkers under g, roots cm, cm' with `rt w.1.1 = some cm` and the
roots of oK, oE, oF equal to [cm], [cm, cm'], [cm'], and `Good oF` of the raw string that K reads
under cm off C's own log gives `Fine w` (`hYes`). All of these are variables or hypotheses.
"Probability" is `Rom.Pr`, a lower integral: see the head. The bound says nothing once it reaches 1.
-/
theorem join_verify (C : OComp (rom lam) β) (P : β → OComp (rom lam) δ) (tC tP : ℕ)
    (hC : C.QueryBound tC) (hP : ∀ b, (P b).QueryBound tP)
    (rt : β × Trace (rom lam) → Option (Dig lam))
    (K E F : PartO lam ((β × Trace (rom lam)) × δ) Sg) (hK : K.OK) (hE : E.OK) (hF : F.OK)
    (bS : ℕ → ℕ → ℝ≥0∞) (hS : K.Stable bS)
    (hKE : SameRaw K E) (hEF : SameRaw E F) (Good : F.Out → Raw Sg → Prop)
    (hpath : ∀ (oK : K.Out) (oE : E.Out) (oF : F.Out) (Y₀ Y₁ : Raw Sg),
      K.Lang oK [Y₀] → E.Lang oE [Y₀, Y₁] → F.Lang oF [Y₁] → Good oF Y₀)
    (X : Fam (rom lam) → Set (((β × Trace (rom lam)) × δ) × Trace (rom lam))) (bX : ℝ≥0∞)
    (hX : Rom.Pr (twoExp C P).withTrace X ≤ bX) (hXc : ∀ g w, w ∉ X g → NoClash w.2)
    (Yes : Fam (rom lam) → Set (((β × Trace (rom lam)) × δ) × Trace (rom lam)))
    (Fine : ((β × Trace (rom lam)) × δ) × Trace (rom lam) → Prop)
    (hYes : ∀ g w, w ∈ Yes g → w ∉ X g → (∃ τ, w.2 = w.1.1.2 ++ τ) → ∃ oK oE oF cm cm',
      (K.chk w.1).det g = some oK ∧ (E.chk w.1).det g = some oE ∧
      (F.chk w.1).det g = some oF ∧ rt w.1.1 = some cm ∧ K.roots oK = [cm] ∧
      E.roots oE = [cm, cm'] ∧ F.roots oF = [cm'] ∧
      (Good oF (K.raw w.1.1.2 cm) → Fine w)) :
    Rom.Pr (twoExp C P).withTrace (fun g => {w | w ∈ Yes g ∧ ¬ Fine w}) ≤
      K.bound (tC + tP) + (E.bound (tC + tP) + (F.bound (tC + tP) + (bS tC tP + bX))) := by
  have hM := queryBound_twoExp C P tC tP hC hP
  set c := (twoExp C P).withTrace with hc
  let E4 : Fam (rom lam) → Set (((β × Trace (rom lam)) × δ) × Trace (rom lam)) := fun _ =>
    {w | ∃ cm, rt w.1.1 = some cm ∧ K.raw w.1.1.2 cm ≠ K.raw w.2 cm}
  have b4 : Rom.Pr c E4 ≤ bS tC tP := hS β δ C rt P tC tP hC hP
  rw [hc, Pr_twoExp_shape, ← hc]
  refine le_trans (Rom.Pr_mono c (F := fun g =>
    K.lose g ∪ (E.lose g ∪ (F.lose g ∪ (E4 g ∪ X g)))) fun g w hw => ?_) ?_
  · obtain ⟨⟨hy, hbad⟩, hsh⟩ := hw
    by_contra hno
    simp only [Set.mem_union, not_or] at hno
    obtain ⟨nK, nE, nF, n4, n5⟩ := hno
    obtain ⟨oK, oE, oF, cm, cm', cK, cE, cF, hrt, rK, rE, rF, hfine⟩ := hYes g w hy n5 hsh
    have lK : K.Lang oK [K.raw w.2 cm] := by
      by_contra h
      exact nK ⟨oK, cK, by rw [rK]; exact h⟩
    have lE : E.Lang oE [E.raw w.2 cm, E.raw w.2 cm'] := by
      by_contra h
      exact nE ⟨oE, cE, by rw [rE]; exact h⟩
    have lF : F.Lang oF [F.raw w.2 cm'] := by
      by_contra h
      exact nF ⟨oF, cF, by rw [rF]; exact h⟩
    have hcl : NoClash w.2 := hXc g w n5
    have hst : K.raw w.1.1.2 cm = K.raw w.2 cm := by
      by_contra h
      exact n4 ⟨cm, hrt, h⟩
    rw [← hKE w.2 hcl cm, hEF w.2 hcl cm'] at lE
    refine hbad (hfine ?_)
    rw [hst]
    exact hpath oK oE oF _ _ lK lE lF
  · refine le_trans (Pr_union_le c _ _ (hK.meas _)) (add_le_add (hK.rare _ _ hM) ?_)
    refine le_trans (Pr_union_le c _ _ (hE.meas _)) (add_le_add (hE.rare _ _ hM) ?_)
    refine le_trans (Pr_union_le c _ _ (hF.meas _)) (add_le_add (hF.rare _ _ hM) ?_)
    exact le_trans (Pr_union_le c _ _ (measurable_PrCoins _ _)) (add_le_add b4 hX)

/-- **Three checkers, one bound.** See the head for the experiment. With probability at most the sum
of the three parts' bounds at tC + tP, of bS tC tP and of (tC + tP)^2 / 2^lam: under the drawn
oracle the three checkers return oK, oE, oF on the committer's and the prover's outputs; `rt` reads
cm off the committer's output and log; the roots of oK, oE, oF are [cm], [cm, cm'], [cm']; and
`Good oF` fails of the raw string that the part K reads under cm off the committer's own log. Asked:
the query bounds tC and tP; `PartO.OK` of all three; `PartO.Stable` of K; `SameRaw K E`,
`SameRaw E F`; `hpath`. All of these are variables or hypotheses: nothing says that any three parts
meet them. The tie between the roots stands in the event, not in the conclusion. The bound says
nothing once it reaches 1. -/
theorem join_three (C : OComp (rom lam) β) (P : β → OComp (rom lam) δ) (tC tP : ℕ)
    (hC : C.QueryBound tC) (hP : ∀ b, (P b).QueryBound tP)
    (rt : β × Trace (rom lam) → Option (Dig lam))
    (K E F : PartO lam ((β × Trace (rom lam)) × δ) Sg) (hK : K.OK) (hE : E.OK) (hF : F.OK)
    (bS : ℕ → ℕ → ℝ≥0∞) (hS : K.Stable bS)
    (hKE : SameRaw K E) (hEF : SameRaw E F) (Good : F.Out → Raw Sg → Prop)
    (hpath : ∀ (oK : K.Out) (oE : E.Out) (oF : F.Out) (Y₀ Y₁ : Raw Sg),
      K.Lang oK [Y₀] → E.Lang oE [Y₀, Y₁] → F.Lang oF [Y₁] → Good oF Y₀) :
    Rom.Pr (twoExp C P).withTrace (fun g => {w | ∃ oK oE oF cm cm',
        (K.chk w.1).det g = some oK ∧ (E.chk w.1).det g = some oE ∧
        (F.chk w.1).det g = some oF ∧ rt w.1.1 = some cm ∧ K.roots oK = [cm] ∧
        E.roots oE = [cm, cm'] ∧ F.roots oF = [cm'] ∧ ¬ Good oF (K.raw w.1.1.2 cm)}) ≤
      K.bound (tC + tP) + (E.bound (tC + tP) + (F.bound (tC + tP) +
        (bS tC tP + (((tC + tP) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ lam))) :=
  join_verify C P tC tP hC hP rt K E F hK hE hF bS hS hKE hEF Good hpath
    (fun _ => {w | ¬ NoClash w.2}) _ (clash_maker C P tC tP hC hP) (fun _ _ h => not_not.1 h)
    (fun g => {w | ∃ oK oE oF cm cm',
      (K.chk w.1).det g = some oK ∧ (E.chk w.1).det g = some oE ∧
      (F.chk w.1).det g = some oF ∧ rt w.1.1 = some cm ∧ K.roots oK = [cm] ∧
      E.roots oE = [cm, cm'] ∧ F.roots oF = [cm'] ∧ ¬ Good oF (K.raw w.1.1.2 cm)})
    (fun _ => False)
    (fun _ _ ⟨oK, oE, oF, cm, cm', cK, cE, cF, hrt, rK, rE, rF, hbad⟩ _ _ =>
      ⟨oK, oE, oF, cm, cm', cK, cE, cF, hrt, rK, rE, rF, hbad⟩) |>.trans' (Rom.Pr_mono _
        fun _ _ hw => ⟨hw, not_false⟩)

/-- If, for each outcome, the oracles under which it lies in `Yes` are a measurable set, the
probability of "yes and not `Fine`" over the coins is a measurable function of the oracle: the bound
of `join_verify` is then on a true average, if X's is one. -/
theorem measurable_yes {α : Type} (c : OComp (rom lam) α) (Yes : Fam (rom lam) → Set α)
    (Fine : α → Prop) (h : ∀ w, MeasurableSet {g | w ∈ Yes g}) :
    Measurable fun g => PrCoins g c {w | w ∈ Yes g ∧ ¬ Fine w} :=
  measurable_PrCoins_dep c _ fun w => by
    by_cases hf : Fine w
    · simp [hf]
    · simpa [hf] using h w

/-- **The probability of `join_three`'s event over the coins is a measurable function of the
oracle**, if the three checkers toss no coins: the bound of `join_three` is then on a true
average. -/
theorem measurable_join (C : OComp (rom lam) β) (P : β → OComp (rom lam) δ)
    (rt : β × Trace (rom lam) → Option (Dig lam))
    (K E F : PartO lam ((β × Trace (rom lam)) × δ) Sg) (hK : ∀ x, (K.chk x).NoCoin)
    (hE : ∀ x, (E.chk x).NoCoin) (hF : ∀ x, (F.chk x).NoCoin)
    (Good : F.Out → Raw Sg → Prop) :
    Measurable fun g => PrCoins g (twoExp C P).withTrace {w | ∃ oK oE oF cm cm',
        (K.chk w.1).det g = some oK ∧ (E.chk w.1).det g = some oE ∧
        (F.chk w.1).det g = some oF ∧ rt w.1.1 = some cm ∧ K.roots oK = [cm] ∧
        E.roots oE = [cm, cm'] ∧ F.roots oF = [cm'] ∧ ¬ Good oF (K.raw w.1.1.2 cm)} := by
  have h := measurable_twoExp_det (twoExp C P)
    (fun x => (K.chk x).bind fun a => (E.chk x).bind fun b => (F.chk x).bind fun c =>
      OComp.pure (a, b, c))
    (fun x => (hK x).bind fun _ => (hE x).bind fun _ => (hF x).bind fun _ => trivial)
    {z | ∃ oK oE oF cm cm', z.2 = (some oK, some oE, some oF) ∧ rt z.1.1.1 = some cm ∧
      K.roots oK = [cm] ∧ E.roots oE = [cm, cm'] ∧ F.roots oF = [cm'] ∧
      ¬ Good oF (K.raw z.1.1.1.2 cm)}
  refine (congrArg Measurable (funext fun g => congrArg _ (Set.ext fun w => ?_))).mp h
  simp only [Set.mem_setOf_eq, OComp.det_bind, OComp.det, Prod.mk.injEq]
  constructor
  · rintro ⟨oK, oE, oF, cm, cm', ⟨cK, cE, cF⟩, r⟩
    exact ⟨oK, oE, oF, cm, cm', cK, cE, cF, r⟩
  · rintro ⟨oK, oE, oF, cm, cm', cK, cE, cF, r⟩
    exact ⟨oK, oE, oF, cm, cm', ⟨cK, cE, cF⟩, r⟩

end

end OnBytes.Slice
