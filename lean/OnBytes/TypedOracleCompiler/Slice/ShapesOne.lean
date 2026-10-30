-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/ShapesOne.lean: the bound for ONE file's part, over one random oracle, said
without the other two files.

`FileSpec.Delivers` (OnBytes/TypedOracleCompiler/Slice/Shapes.lean) lists what is delivered for one file.
`Delivers.ok` reads it as `PartO.OK`: a bound at every pair of tables. This file reads that bound as
a statement on one experiment: a maker asks a uniformly random oracle at most t strings and puts out
five files.

Main definitions.
 `FileSpec.LoseAt T₀ T₁ g` the file's event at two tables: the maker's log shows no clash, the
     checker returns a value, and the strings that the one written reading reads off the log under
     that value's roots are outside the file's language.
 `FileSpec.own₀`, `own₁` the tables that the oracle itself holds: its values at the public strings,
     the default value elsewhere.
 `FileSpec.Lose g`, `LoseAll g` the event IN ONE WORLD: at the oracle's own tables; the second
     without the condition on the log.
Main theorems.
 `Pr_le_of_pinned`, `Pr_le_of_pinned₂` a bound for every maker that answers by a table is a bound
     for the maker that asks: OnBytes/Slice/AtSet.lean's two lemmas, for one maker.
 `Delivers.bound_at` at fixed tables: probability at most b t.
 `Delivers.one_world` in one world: at most b t.
 `Delivers.one_world_all` with no condition on the log: at most b t + t^2 / 2^256.
 `FileSpec.ClashOwn`, `Delivers.one_world_clash` a clash in the checker's OWN log, at the oracle's
     own tables: at most (t + r)^2 / 2^256.

What is asked beside `Delivers`: the written reading does not see the entries at public strings.

What is not claimed. AN IMPLICATION: no `FileSpec` is given that meets `Delivers`. A checker that
never returns has an empty event. Nothing on the program, and nothing on the other files: that the
first string is a key's table, or the second a proof's, is not said here. `Rom.Pr` is a lower
integral; `LoseAt`, `Lose`, `LoseAll` and `ClashOwn` are shown measurable. The bound says nothing
once it reaches 1.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.ShapesFrom

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Rom Prob MeasureTheory
open scoped ENNReal

variable {lam : ℕ} {γ : Type}

/-- A bound for every maker that answers by a table is a bound for the maker that asks:
`Pr_twoExp_le_of_pinned` (OnBytes/Slice/AtSet.lean) for one maker. -/
theorem Pr_le_of_pinned (S : Finset (List Bool)) (A : OComp (rom lam) γ)
    (E : Fam (rom lam) → Set (γ × Trace (rom lam))) (b : ℝ≥0∞)
    (hm : ∀ x, MeasurableSet {g | x ∈ E g})
    (hoff : ∀ g x, x ∈ E g → (x.1, offSet S x.2) ∈ E g)
    (h : ∀ T, Rom.Pr (pinOn S T A).withTrace (fun g => E (over S T g)) ≤ b) :
    Rom.Pr A.withTrace E ≤ b := by
  refine lintegral_le_of_over S _ (measurable_PrCoins_dep _ E hm) b fun T => le_trans ?_ (h T)
  unfold Rom.Pr
  refine lintegral_mono fun g => ?_
  unfold PrCoins
  rw [withTrace_pinOn, pr_map]
  exact pr_mono _ fun x hx => hoff _ x hx

/-- The same in two steps: the strings of the second step may depend on the values at the
first. -/
theorem Pr_le_of_pinned₂ (S₀ : Finset (List Bool))
    (S₁ : (List Bool → Dig lam) → Finset (List Bool)) (A : OComp (rom lam) γ)
    (E : Fam (rom lam) → Set (γ × Trace (rom lam))) (b : ℝ≥0∞)
    (hm : ∀ x, MeasurableSet {g | x ∈ E g})
    (hoff₀ : ∀ g x, x ∈ E g → (x.1, offSet S₀ x.2) ∈ E g)
    (hoff₁ : ∀ T₀ g x, x ∈ E g → (x.1, offSet (S₁ T₀) x.2) ∈ E g)
    (h : ∀ T₀ T₁, Rom.Pr (pinOn (S₁ T₀) T₁ (pinOn S₀ T₀ A)).withTrace
      (fun g => E (over S₀ T₀ (over (S₁ T₀) T₁ g))) ≤ b) :
    Rom.Pr A.withTrace E ≤ b :=
  Pr_le_of_pinned S₀ A E b hm hoff₀ fun T₀ =>
    Pr_le_of_pinned (S₁ T₀) (pinOn S₀ T₀ A) (fun g => E (over S₀ T₀ g)) b
      (measurableSet_over S₀ T₀ E hm) (fun _ x hx => hoff₁ T₀ _ x hx) (h T₀)

namespace Shapes
namespace FileSpec
variable (φ : FileSpec) (S₀ : Finset (List Bool)) (S₁ : Tab → Finset (List Bool))
  (rd : Tab → Tab → Trace (rom 256) → Dig 256 → Raw Run.PQ.SgX)

/-- ONE FILE's EVENT, at two tables, under the oracle g, on a maker's files and log: the log
shows no clash; the file's checker returns a value; and the strings that the one written reading
reads off the log under that value's roots are OUTSIDE THE FILE's LANGUAGE. -/
def LoseAt (T₀ T₁ : Tab) (g : Fam (rom 256)) : Set (Files × Trace (rom 256)) :=
  {x | NoClash x.2 ∧ ∃ o, ((φ.toO S₀ S₁ T₀ T₁).chk x.1).det g = some o ∧
    ¬ (φ.toO S₀ S₁ T₀ T₁).Lang o (((φ.toO S₀ S₁ T₀ T₁).roots o).map (rd T₀ T₁ x.2))}

/-- The first table that the oracle itself holds: its values at the first public strings. -/
def own₀ (g : Fam (rom 256)) : Tab := cutT S₀ (own g)

/-- The second: its values at the second public strings, which hang on the first table. -/
def own₁ (g : Fam (rom 256)) : Tab := cutT (S₁ (own₀ S₀ g)) (own g)

/-- THE SAME EVENT IN ONE WORLD: the tables are the oracle's own values at the public
strings. -/
def Lose (g : Fam (rom 256)) : Set (Files × Trace (rom 256)) :=
  φ.LoseAt S₀ S₁ rd (own₀ S₀ g) (own₁ S₀ S₁ g) g

variable {φ S₀ S₁ rd} {b : ℕ → ℝ≥0∞}

/-- THE BOUND FOR ONE FILE, AT FIXED TABLES: for every maker with at most t queries the file's
event has probability at most b t. -/
theorem Delivers.bound_at (h : φ.Delivers S₀ S₁ rd b) (T₀ T₁ : Tab) (A : OComp (rom 256) Files)
    (t : ℕ) (hA : A.QueryBound t) :
    Rom.Pr A.withTrace (φ.LoseAt S₀ S₁ rd T₀ T₁) ≤ b t := by
  refine le_trans (le_trans (Rom.Pr_mono _ fun g x hx => ?_) ((h.ok T₀ T₁).rare A t hA))
    (h.flat T₀ T₁ t)
  obtain ⟨hn, o, ho, hl⟩ := hx
  refine ⟨o, ho, fun hL => hl ?_⟩
  have e : ((φ.toO S₀ S₁ T₀ T₁).roots o).map ((φ.toO S₀ S₁ T₀ T₁).raw x.2) =
      ((φ.toO S₀ S₁ T₀ T₁).roots o).map (rd T₀ T₁ x.2) :=
    List.map_congr_left fun cm _ => h.reads T₀ T₁ x.2 hn cm
  rw [← e]
  exact hL

/-- At fixed tables the oracles under which an outcome lies in the event are a measurable set. -/
theorem measurableSet_loseAt (T₀ T₁ : Tab) (x : Files × Trace (rom 256)) :
    MeasurableSet {g | x ∈ φ.LoseAt S₀ S₁ rd T₀ T₁ g} :=
  (MeasurableSet.const (NoClash x.2)).inter
    (measurableSet_det ((φ.toO S₀ S₁ T₀ T₁).chk x.1) {a | ∃ o, a = some o ∧
      ¬ (φ.toO S₀ S₁ T₀ T₁).Lang o (((φ.toO S₀ S₁ T₀ T₁).roots o).map (rd T₀ T₁ x.2))})

/-- So they are in one world. -/
theorem measurableSet_lose (x : Files × Trace (rom 256)) :
    MeasurableSet {g | x ∈ φ.Lose S₀ S₁ rd g} := by
  have h := measurableSet_dep (askL S₀.toList)
    (fun T₀ => {g | x ∈ φ.LoseAt S₀ S₁ rd T₀ (cutT (S₁ T₀) (own g)) g}) (fun T₀ => by
      have h' := measurableSet_dep (askL (S₁ T₀).toList)
        (fun T₁ => {g | x ∈ φ.LoseAt S₀ S₁ rd T₀ T₁ g})
        (fun T₁ => measurableSet_loseAt T₀ T₁ x)
      simp only [askL_toList] at h'
      exact h')
  simp only [askL_toList] at h
  exact h

/-- The first table of the oracle with two tables put over it is the first of these, cut. -/
theorem own₀_over (T₀ T₁ : Tab) (g : Fam (rom 256)) :
    own₀ S₀ (over S₀ T₀ (over (S₁ (cutT S₀ T₀)) T₁ g)) = cutT S₀ T₀ := by
  funext s
  unfold own₀ cutT own
  by_cases hs : s ∈ S₀
  · rw [if_pos hs, if_pos hs, over_mem _ _ hs]
  · rw [if_neg hs, if_neg hs]

/-- Its second table is the merge of the two, cut. -/
theorem own₁_over (T₀ T₁ : Tab) (g : Fam (rom 256)) :
    own₁ S₀ S₁ (over S₀ T₀ (over (S₁ (cutT S₀ T₀)) T₁ g)) =
      cutT (S₁ (cutT S₀ T₀)) (mergeT S₀ T₀ T₁) := by
  unfold own₁
  rw [own₀_over]
  funext s
  unfold cutT
  by_cases hs : s ∈ S₁ (fun s => if s ∈ S₀ then T₀ s else default)
  · rw [if_pos hs, if_pos hs]
    unfold own mergeT
    by_cases h0 : s ∈ S₀
    · rw [over_mem _ _ h0, if_pos h0]
    · rw [over_not_mem _ _ h0, over_mem _ _ hs, if_neg h0]
  · rw [if_neg hs, if_neg hs]

/-- That oracle is the oracle with the two cut tables, merged, put over it. -/
theorem over_eq_cut (T₀ T₁ : Tab) (g : Fam (rom 256)) :
    over S₀ T₀ (over (S₁ (cutT S₀ T₀)) T₁ g) = over (S₀ ∪ S₁ (cutT S₀ T₀))
      (mergeT S₀ (cutT S₀ T₀) (cutT (S₁ (cutT S₀ T₀)) (mergeT S₀ T₀ T₁))) g := by
  rw [over_merge]
  refine over_congr _ _ _ g fun s hs => ?_
  unfold mergeT cutT
  by_cases h0 : s ∈ S₀
  · rw [if_pos h0, if_pos h0, if_pos h0]
  · have h1 : s ∈ S₁ (fun s => if s ∈ S₀ then T₀ s else default) :=
      (Finset.mem_union.1 hs).resolve_left h0
    rw [if_neg h0, if_neg h0, if_pos h1]
    show T₁ s = if s ∈ S₀ then T₀ s else T₁ s
    rw [if_neg h0]

/-- THE BOUND FOR ONE FILE, IN ONE WORLD. Over one uniformly random oracle, for every maker with
at most t queries: with probability at most b t the maker's log shows no clash, the file's checker,
AT THE ORACLE's OWN VALUES AT THE PUBLIC STRINGS, returns a value, and the strings that are read off
the maker's log under that value's roots are outside the file's language. Asked beside what is
delivered for the file: the written reading does not see the entries at public strings. -/
theorem Delivers.one_world (h : φ.Delivers S₀ S₁ rd b)
    (hrd : ∀ T₀ T₁ S σ cm, (S = S₀ ∨ ∃ T, S = S₁ T) → rd T₀ T₁ (offSet S σ) cm = rd T₀ T₁ σ cm)
    (A : OComp (rom 256) Files) (t : ℕ) (hA : A.QueryBound t) :
    Rom.Pr A.withTrace (φ.Lose S₀ S₁ rd) ≤ b t := by
  have hoff : ∀ S, (S = S₀ ∨ ∃ T, S = S₁ T) → ∀ g x, x ∈ φ.Lose S₀ S₁ rd g →
      (x.1, offSet S x.2) ∈ φ.Lose S₀ S₁ rd g := by
    rintro S hS g x ⟨hn, o, ho, hl⟩
    refine ⟨hn.of_subset fun e he => (List.mem_filter.1 he).1, o, ho, fun hL => hl ?_⟩
    have e : (((φ.toO S₀ S₁ (own₀ S₀ g) (own₁ S₀ S₁ g)).roots o).map
        (rd (own₀ S₀ g) (own₁ S₀ S₁ g) (offSet S x.2))) =
        ((φ.toO S₀ S₁ (own₀ S₀ g) (own₁ S₀ S₁ g)).roots o).map
          (rd (own₀ S₀ g) (own₁ S₀ S₁ g) x.2) :=
      List.map_congr_left fun cm _ => hrd _ _ S x.2 cm hS
    rw [← e]
    exact hL
  refine Pr_le_of_pinned₂ S₀ (fun T₀ => S₁ (cutT S₀ T₀)) A (φ.Lose S₀ S₁ rd) (b t)
    measurableSet_lose (hoff S₀ (Or.inl rfl)) (fun T₀ => hoff _ (Or.inr ⟨_, rfl⟩))
    fun T₀ T₁ => ?_
  refine le_trans (Rom.Pr_mono _ fun g x hx => ?_)
    (h.bound_at (cutT S₀ T₀) (cutT (S₁ (cutT S₀ T₀)) (mergeT S₀ T₀ T₁)) _ t
      (queryBound_pinOn _ _ _ t (queryBound_pinOn _ _ A t hA)))
  unfold Lose at hx
  rw [own₀_over, own₁_over] at hx
  obtain ⟨hn, o, ho, hl⟩ := hx
  rw [over_eq_cut, φ.toO_deaf] at ho
  exact ⟨hn, o, ho, hl⟩

/-- The file's event at two tables, without the condition on the maker's log. -/
def LoseAllAt (φ : FileSpec) (S₀ : Finset (List Bool)) (S₁ : Tab → Finset (List Bool))
    (rd : Tab → Tab → Trace (rom 256) → Dig 256 → Raw Run.PQ.SgX) (T₀ T₁ : Tab)
    (g : Fam (rom 256)) : Set (Files × Trace (rom 256)) :=
  {x | ∃ o, ((φ.toO S₀ S₁ T₀ T₁).chk x.1).det g = some o ∧
    ¬ (φ.toO S₀ S₁ T₀ T₁).Lang o (((φ.toO S₀ S₁ T₀ T₁).roots o).map (rd T₀ T₁ x.2))}

/-- THE SAME EVENT WITHOUT THE CONDITION ON THE MAKER's LOG: the checker, at the oracle's own
public values, returns a value, and the strings read off the log under its roots are outside the
file's language. -/
def LoseAll (φ : FileSpec) (S₀ : Finset (List Bool)) (S₁ : Tab → Finset (List Bool))
    (rd : Tab → Tab → Trace (rom 256) → Dig 256 → Raw Run.PQ.SgX) (g : Fam (rom 256)) :
    Set (Files × Trace (rom 256)) :=
  φ.LoseAllAt S₀ S₁ rd (own₀ S₀ g) (own₁ S₀ S₁ g) g

/-- THE BOUND FOR ONE FILE, IN ONE WORLD, WITH NO CONDITION ON THE LOG: b t, and t^2 / 2^256 for
two strings with one answer in the maker's log. -/
theorem Delivers.one_world_all (h : φ.Delivers S₀ S₁ rd b)
    (hrd : ∀ T₀ T₁ S σ cm, (S = S₀ ∨ ∃ T, S = S₁ T) → rd T₀ T₁ (offSet S σ) cm = rd T₀ T₁ σ cm)
    (A : OComp (rom 256) Files) (t : ℕ) (hA : A.QueryBound t) :
    Rom.Pr A.withTrace (φ.LoseAll S₀ S₁ rd) ≤ b t + ((t ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  refine le_trans (Rom.Pr_mono _ fun g x hx => ?_)
    (le_trans (Pr_union_le A.withTrace (φ.Lose S₀ S₁ rd) (fun _ => {x | ¬ NoClash x.2})
      (measurable_PrCoins_dep _ _ measurableSet_lose))
      (add_le_add (h.one_world hrd A t hA) (Pr_clash_le A t hA)))
  by_cases hn : NoClash x.2
  · exact Or.inl ⟨hn, hx⟩
  · exact Or.inr hn

/-- The oracles under which an outcome lies in that event are a measurable set. -/
theorem measurableSet_loseAll (x : Files × Trace (rom 256)) :
    MeasurableSet {g | x ∈ φ.LoseAll S₀ S₁ rd g} := by
  have h := measurableSet_dep (askL S₀.toList)
    (fun T₀ => {g | x ∈ φ.LoseAllAt S₀ S₁ rd T₀ (cutT (S₁ T₀) (own g)) g}) (fun T₀ => by
      have h' := measurableSet_dep (askL (S₁ T₀).toList)
        (fun T₁ => {g | x ∈ φ.LoseAllAt S₀ S₁ rd T₀ T₁ g})
        (fun T₁ => measurableSet_det ((φ.toO S₀ S₁ T₀ T₁).chk x.1) {a | ∃ o, a = some o ∧
          ¬ (φ.toO S₀ S₁ T₀ T₁).Lang o (((φ.toO S₀ S₁ T₀ T₁).roots o).map (rd T₀ T₁ x.2))})
      simp only [askL_toList] at h'
      exact h')
  simp only [askL_toList] at h
  exact h

/-- A clash in the checker's own log, at two tables. -/
def ClashOwnAt (φ : FileSpec) (S₀ : Finset (List Bool)) (S₁ : Tab → Finset (List Bool))
    (T₀ T₁ : Tab) (g : Fam (rom 256)) : Set (Files × Trace (rom 256)) :=
  {x | ¬ NoClash ((φ.toO S₀ S₁ T₀ T₁).ownLog g x.1)}

/-- A CLASH IN THE CHECKER's OWN LOG, IN ONE WORLD: under the oracle g two different strings
that the checker, at g's own public values, asks on the maker's files have one answer. -/
def ClashOwn (φ : FileSpec) (S₀ : Finset (List Bool)) (S₁ : Tab → Finset (List Bool))
    (g : Fam (rom 256)) : Set (Files × Trace (rom 256)) :=
  φ.ClashOwnAt S₀ S₁ (own₀ S₀ g) (own₁ S₀ S₁ g) g

/-- The oracles under which an outcome lies in it are a measurable set. -/
theorem measurableSet_clashOwn (x : Files × Trace (rom 256)) :
    MeasurableSet {g | x ∈ φ.ClashOwn S₀ S₁ g} := by
  have h := measurableSet_dep (askL S₀.toList)
    (fun T₀ => {g | x ∈ φ.ClashOwnAt S₀ S₁ T₀ (cutT (S₁ T₀) (own g)) g})
    (fun T₀ => by
      have h' := measurableSet_dep (askL (S₁ T₀).toList)
        (fun T₁ => {g | x ∈ φ.ClashOwnAt S₀ S₁ T₀ T₁ g})
        (fun T₁ => measurableSet_det ((φ.toO S₀ S₁ T₀ T₁).chk x.1).withTrace
          {a | ¬ NoClash a.2})
      simp only [askL_toList] at h'
      exact h')
  simp only [askL_toList] at h
  exact h

/-- ITS BOUND, IN ONE WORLD: (t + r)^2 / 2^256, for a maker with at most t queries, if at all
tables the checker asks at most r strings. -/
theorem Delivers.one_world_clash (h : φ.Delivers S₀ S₁ rd b) (r : ℕ)
    (hr : ∀ T₀ T₁, (φ.part T₀ T₁).tR ≤ r) (A : OComp (rom 256) Files) (t : ℕ)
    (hA : A.QueryBound t) :
    Rom.Pr A.withTrace (φ.ClashOwn S₀ S₁) ≤ (((t + r) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256 := by
  refine Pr_le_of_pinned₂ S₀ (fun T₀ => S₁ (cutT S₀ T₀)) A (φ.ClashOwn S₀ S₁) _
    measurableSet_clashOwn (fun _ _ hx => hx) (fun _ _ _ hx => hx) fun T₀ T₁ => ?_
  refine le_trans (Rom.Pr_mono _ fun g x hx => ?_)
    (PartO.pr_ownClash (φ.toO S₀ S₁ (cutT S₀ T₀) (cutT (S₁ (cutT S₀ T₀)) (mergeT S₀ T₀ T₁)))
      (h.toO_noCoin _ _) r (fun x => (h.toO_queries _ _ x).mono (hr _ _)) _ t
      (queryBound_pinOn _ _ _ t (queryBound_pinOn _ _ A t hA)))
  unfold ClashOwn at hx
  rw [own₀_over, own₁_over] at hx
  have hx' : ¬ NoClash ((φ.toO S₀ S₁ (cutT S₀ T₀)
      (cutT (S₁ (cutT S₀ T₀)) (mergeT S₀ T₀ T₁))).ownLog
        (over S₀ T₀ (over (S₁ (cutT S₀ T₀)) T₁ g)) x.1) := hx
  rw [over_eq_cut, φ.toO_ownLog_deaf] at hx'
  exact hx'

end FileSpec
end Shapes

end OnBytes.Slice
