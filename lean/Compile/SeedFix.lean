-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/SeedFix.lean: lemmas for a prover that derives a part of the committer's run again
(`OComp.derive`, Rom/SpecDerive.lean): what holds of every result of an algorithm; a run that a
table and a record fix; tokens below a bound (words of this library: lean/GLOSSARY.md).

A table is "what lazy sampling has fixed so far" (`Table`, Rom/OSpec.lean); a record is "the record
of the derived answers" (`Derive.Rec`; the run on both: `runRec`, Rom/Derive.lean). A token (`Tok`,
`Step`, Rom/Defer.lean) is, in an erased program (`erase`, Compile/Star.lean), an index into a list
of strings, the store.

  Part 1  `All Q c`: every result of the oracle algorithm c satisfies Q. Rules; `All.of_runRec`: so
          does every result of a run on a table and a record. `all_prefix`: an erased program only
          appends to the store.
  Part 2  `Fixes σ c j T R a`: on every table and record that contain T and R, the run of c from the
          counter j returns a and changes nothing. `fixes_of_mem` ((Use): the label of
          `Derive.runRec_again`, Rom/Derive.lean), `Fixes.mono`, `Fixes.map`. `Fixes.runLazy`: then,
          if c avoids the auxiliary oracle, the derived algorithm returns a on
          `Derive.glue σ s T' R`, for every table T' that contains T. `mem_runRec_bind`: a run of a
          sequence splits (under `Tosses`, Compile/SeedKit.lean).
  Part 3  `ORel.bind_eq`: two algorithms in `ORel`, followed by functions that agree on related
          results, are equal.
  Part 4  `SaltsLt b l`: all tokens of a list of salts are below b; then showing them through
          `Life2.up` at N₀ ≥ b changes nothing (`upTree_of_lt`). `downTree_up`: `down` after `up`
          changes nothing, on trees.
-/
import Compile.SeedPar
import Compile.SeedShape

open Rom Iop

namespace Compile
namespace Seed

variable {S : OSpec} {α β γ : Type}

/-! ## Part 1. Every result -/

/-- every result of the algorithm satisfies Q -/
def All (Q : α → Prop) : OComp S α → Prop
  | .pure a => Q a
  | .query _ _ k => ∀ r, All Q (k r)
  | .sample _ k => ∀ r, All Q (k r)

theorem All.mono {Q Q' : α → Prop} {c : OComp S α} (h : All Q c) (hq : ∀ a, Q a → Q' a) :
    All Q' c := by
  induction c with
  | pure a => exact hq a h
  | query o q k ih => exact fun r => ih r (h r)
  | sample n k ih => exact fun r => ih r (h r)

theorem All.and {Q Q' : α → Prop} {c : OComp S α} (h : All Q c) (h' : All Q' c) :
    All (fun a => Q a ∧ Q' a) c := by
  induction c with
  | pure a => exact ⟨h, h'⟩
  | query o q k ih => exact fun r => ih r (h r) (h' r)
  | sample n k ih => exact fun r => ih r (h r) (h' r)

theorem All.bind {Q : α → Prop} {Q' : β → Prop} {c : OComp S α} {g : α → OComp S β}
    (h : All Q c) (hg : ∀ a, Q a → All Q' (g a)) : All Q' (c.bind g) := by
  induction c with
  | pure a => exact hg a h
  | query o q k ih => exact fun r => ih r (h r)
  | sample n k ih => exact fun r => ih r (h r)

theorem all_tossN {Q : α → Prop} (w : ℕ) :
    ∀ (m : ℕ) (f : (Fin m → Fin (w + 1)) → OComp S α),
      (∀ v, All Q (f v)) → All Q (OComp.tossN w m f)
  | 0, _, h => h _
  | m + 1, _, h => fun _ => all_tossN w m _ fun _ => h _

theorem All.blocks {Q : α → Prop} {c : OComp S α} (h : All Q c) (bk : CoinPlan) :
    All Q (c.blocks bk) := by
  induction c with
  | pure a => exact h
  | query o q k ih => exact fun r => ih r (h r)
  | sample n k ih => exact all_tossN _ _ _ fun v => ih _ (h _)

theorem All.of_runRec (σ : SeedOracle S) {Q : α → Prop} {c : OComp S α} (h : All Q c) :
    ∀ (j : ℕ) (T : Table S) (R : Derive.Rec σ), ∀ x ∈ (Derive.runRec σ c j T R).support, Q x.1 := by
  induction c with
  | pure a =>
    intro j T R x hx
    simp only [Derive.runRec, PMF.support_pure, Set.mem_singleton_iff] at hx
    rw [hx]
    exact h
  | query o q k ih =>
    intro j T R x hx
    cases hT : T o q with
    | some r =>
      simp only [Derive.runRec, hT] at hx
      exact ih r (h r) j T R x hx
    | none =>
      simp only [Derive.runRec, hT, PMF.mem_support_bind_iff] at hx
      obtain ⟨r, -, hx⟩ := hx
      exact ih r (h r) j _ R x hx
  | sample n k ih =>
    intro j T R x hx
    cases hR : R j with
    | some d =>
      simp only [Derive.runRec, hR] at hx
      exact ih _ (h _) (j + 1) T R x hx
    | none =>
      simp only [Derive.runRec, hR, PMF.mem_support_bind_iff] at hx
      obtain ⟨d, -, hx⟩ := hx
      exact ih _ (h _) (j + 1) T _ x hx

/-- an erased program only appends to the store -/
theorem all_prefix {sp : Split S} (c : Step S sp α) :
    ∀ vs : List Bits, All (fun o => vs <+: o.2) (erase c vs) := by
  induction c with
  | pure a => exact fun vs => List.prefix_refl vs
  | sample n k ih => exact fun vs r => ih r vs
  | plain o q k ih => exact fun vs r => ih r vs
  | fresh ℓ k ih => exact fun vs r => (ih _ _).mono fun _ h => (List.prefix_append vs _).trans h
  | marked o t us pt inj k ih => exact fun vs r => (ih _ _ _).mono fun _ h => (List.prefix_append vs _).trans h
  | reveal ts k ih => exact fun vs => ih _ vs

/-! ## Part 2. A run that is fixed -/

section Fix
variable (σ : SeedOracle S)

/-- On every table and record that contain T and R, the run of c from the counter j returns a and
changes nothing. -/
def Fixes (c : OComp S α) (j : ℕ) (T : Table S) (R : Derive.Rec σ) (a : α) : Prop :=
  ∀ T' R', Derive.Sub T T' → Derive.SubR R R' → Derive.runRec σ c j T' R' = PMF.pure (a, T', R')

variable {σ}

/-- (Use) (the label of `Derive.runRec_again`, Rom/Derive.lean): a second run, on any table and
record that contain those which the first run returns, returns the same result and changes
nothing -/
theorem fixes_of_mem {c : OComp S α} {j : ℕ} {T : Table S} {R : Derive.Rec σ}
    {x : α × Table S × Derive.Rec σ} (hx : x ∈ (Derive.runRec σ c j T R).support) :
    Fixes σ c j x.2.1 x.2.2 x.1 := fun T' R' h h' => Derive.runRec_again σ c j T R x hx T' R' h h'

theorem Fixes.mono {c : OComp S α} {j : ℕ} {T T' : Table S} {R R' : Derive.Rec σ} {a : α}
    (h : Fixes σ c j T R a) (hT : Derive.Sub T T') (hR : Derive.SubR R R') :
    Fixes σ c j T' R' a := fun T'' R'' h1 h2 => h T'' R'' (hT.trans h1) (hR.trans h2)

theorem runRec_map (c : OComp S α) (G : α → β) :
    ∀ (j : ℕ) (T : Table S) (R : Derive.Rec σ),
      Derive.runRec σ (c.bind fun a => .pure (G a)) j T R =
        (Derive.runRec σ c j T R).map fun x => (G x.1, x.2) := by
  induction c with
  | pure a =>
    intro j T R
    simp only [OComp.bind, Derive.runRec, PMF.pure_map]
  | query o q k ih =>
    intro j T R
    simp only [OComp.bind, Derive.runRec]
    cases T o q with
    | some r => exact ih r j T R
    | none =>
      simp only [PMF.map_bind]
      exact congrArg _ (funext fun r => ih r j _ R)
  | sample n k ih =>
    intro j T R
    simp only [OComp.bind, Derive.runRec]
    cases R j with
    | some d => exact ih _ (j + 1) T R
    | none =>
      simp only [PMF.map_bind]
      exact congrArg _ (funext fun d => ih _ (j + 1) T _)

theorem Fixes.map {c : OComp S α} {j : ℕ} {T : Table S} {R : Derive.Rec σ} {a : α}
    (h : Fixes σ c j T R a) (G : α → β) :
    Fixes σ (c.bind fun a => .pure (G a)) j T R (G a) := fun T' R' h1 h2 => by
  rw [runRec_map, h T' R' h1 h2, PMF.pure_map]

/-- The derived algorithm, on `Derive.glue` (hypotheses below). -/
theorem Fixes.runLazy {c : OComp S α} {j : ℕ} {T : Table S} {R : Derive.Rec σ}
    {a : α} (h : Fixes σ c j T R a) (hc : c.Avoids σ.o) (s : Fin (σ.sd + 1))
    {T' : Table S} (hT : Derive.Sub T T') :
    (c.derive σ s j).runLazy (Derive.glue σ s T' R) = PMF.pure (a, Derive.glue σ s T' R) := by
  rw [Derive.runLazy_derive σ s c hc, h T' R hT (Derive.SubR.refl _), PMF.pure_map]

/-- a run of a sequence splits (under `Tosses`) -/
theorem mem_runRec_bind {n : ℕ} {c : OComp S α} (hc : Tosses n c) {g : α → OComp S β} {j : ℕ}
    {T : Table S} {R : Derive.Rec σ} {x : β × Table S × Derive.Rec σ}
    (hx : x ∈ (Derive.runRec σ (c.bind g) j T R).support) :
    ∃ y ∈ (Derive.runRec σ c j T R).support,
      x ∈ (Derive.runRec σ (g y.1) (j + n) y.2.1 y.2.2).support := by
  rw [runRec_bind σ hc] at hx
  exact (PMF.mem_support_bind_iff _ _ _).1 hx

end Fix

/-! ## Part 3. The same shape -/

theorem ORel.bind_eq {r : α → β → Prop} {c : OComp S α} {c' : OComp S β} (h : ORel r c c')
    {g : α → OComp S γ} {g' : β → OComp S γ} (hg : ∀ a b, r a b → g a = g' b) :
    c.bind g = c'.bind g' := by
  induction h with
  | pure h => exact hg _ _ h
  | query o q _ ih => exact congrArg _ (funext ih)
  | sample n _ ih => exact congrArg _ (funext ih)

/-! ## Part 4. Tokens -/

section Handles
open Life2 (up down)
variable {I X : Type} {lam K : ℕ}

/-- all tokens of a list of salts are below b -/
def SaltsLt (b : ℕ) (l : List (Option (Tok × Tok))) : Prop :=
  ∀ y : Tok × Tok, some y ∈ l → y.1 < b ∧ y.2 < b

theorem SaltsLt.mono {b b' : ℕ} {l : List (Option (Tok × Tok))} (h : SaltsLt b l) (hb : b ≤ b') :
    SaltsLt b' l :=
  fun y hy => ⟨lt_of_lt_of_le (h y hy).1 hb, lt_of_lt_of_le (h y hy).2 hb⟩

theorem up_of_lt {N₀ δ t : ℕ} (h : t < N₀) : up N₀ δ t = t := by
  unfold up
  rw [if_pos h]

theorem map_upS_of_lt {N₀ δ : ℕ} {l : List (Option (Tok × Tok))} (h : SaltsLt N₀ l) :
    l.map (upS N₀ δ) = l := by
  refine (List.map_congr_left fun x hx => ?_).trans (List.map_id l)
  cases x with
  | none => rfl
  | some y =>
    obtain ⟨h1, h2⟩ := h y hx
    show some (up N₀ δ y.1, up N₀ δ y.2) = some y
    rw [up_of_lt h1, up_of_lt h2]

theorem upTree_of_lt {N₀ δ : ℕ} {t : TreeH lam} (h : SaltsLt N₀ t.salts) : upTree N₀ δ t = t := by
  unfold upTree
  rw [map_upS_of_lt h]

/-- tokens, shown back -/
def downS (N₀ δ : ℕ) : Option (Tok × Tok) → Option (Tok × Tok) :=
  Option.map (Prod.map (down N₀ δ) (down N₀ δ))
def downTree (N₀ δ : ℕ) (t : TreeH lam) : TreeH lam := ⟨t.levels, t.salts.map (downS N₀ δ)⟩

theorem down_up (N₀ δ t : ℕ) : down N₀ δ (up N₀ δ t) = t := by
  unfold down up
  split_ifs <;> omega

theorem downTree_up (N₀ δ : ℕ) (t : TreeH lam) : downTree N₀ δ (upTree N₀ δ t) = t := by
  unfold downTree upTree
  simp only [List.map_map]
  have e : (downS N₀ δ ∘ upS N₀ δ) = id := funext fun x => by
    cases x with
    | none => rfl
    | some y =>
      show some (down N₀ δ (up N₀ δ y.1), down N₀ δ (up N₀ δ y.2)) = some y
      rw [down_up, down_up]
  rw [e, List.map_id]

end Handles

end Seed
end Compile
