-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/Lays.lean: what "SPLIT" lays: where it says yes it has laid just one constraint
more on each of the two groups, and what these two say together of any words is what (fold) says.

Main names: rowsOn_addRowP_same, rowsOn_addRowP_other, rowsOn_takeMaskP, split_inv (what a yes at
"SPLIT" is made of), says_of_add, laysW. The law tried on other functions: not_laysOfW_yes,
laysOfW_no, splitWeak, splitWeak_fails.

What is not claimed. LAYS speaks of a yes alone: a function that says no to all meets it
(laysOfW_no). One direction alone: what the two constraints say together gives what (fold) says.
Two codes are a premise. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.Law

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open OnBytes.Model (Reading)
open OnBytes.Means (Words)
open VerifiableInference.Desc.Ground (addRowP takeMaskP ok rowL takeMaskL)

variable {K : Type} [Field K] (ρ : Reading K)

/-- A constraint more on a group: the group's list has it last. -/
theorem rowsOn_addRowP_same (d d' : St) (g : Nat) (row : Row) (h : addRowP d g row = some d') :
    rowsOn d' g = rowsOn d g ++ [row] := by
  unfold addRowP at h
  split at h
  · rename_i hok
    simp only [Option.some.injEq] at h
    subst h
    simp only [ok, rowL, List.all_cons, Bool.and_eq_true] at hok
    obtain ⟨G, hG⟩ := Option.isSome_iff_exists.1 hok.1
    simp [rowsOn, withRow, Array.getElem?_modify, hG]
  · cases h

/-- A constraint more on a group: every other group's list stays. -/
theorem rowsOn_addRowP_other (d d' : St) (g g' : Nat) (row : Row) (h : addRowP d g row = some d')
    (hne : g ≠ g') : rowsOn d' g' = rowsOn d g' := by
  unfold addRowP at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    simp [rowsOn, withRow, Array.getElem?_modify, hne]
  · cases h

/-- A mask entry taken: every group's list stays. -/
theorem rowsOn_takeMaskP (d d' : St) (o k g : Nat) (h : takeMaskP d o = some (k, d')) :
    rowsOn d' g = rowsOn d g := by
  unfold takeMaskP at h
  split at h
  · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨l, _, _, rfl⟩ := h
    rfl
  · cases h

/-- What a yes at "SPLIT" is made of, where two groups are needed. -/
theorem split_inv (p : Par) (d d' : St) (r : Fmt.RoundView) (hS : p.S.sharedSplitNeeded = true)
    (h : split p d [r] = some d') :
    ∃ (row : Row) (x : _) (G : _) (kappa : Nat) (d₁ d₂ : St),
      fold p.S d.loc (linLayOmega d.st.codes p.S) = some row ∧ r.vals = [.e x] ∧
      d.st.groups[d.loc.gOmega]? = some G ∧ ok (splitL d row) = true ∧
      takeMaskP d d.loc.oSp = some (kappa, d₁) ∧
      addRowP d₁ d.loc.gOmega (onOmega row G.members d.loc.oSp kappa (E.ofTriple x)) = some d₂ ∧
      addRowP d₂ d.loc.gU (onU row G.members d.loc.oSp kappa (E.ofTriple x)) = some d' := by
  unfold split at h
  simp only [hS, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨row, hf, h⟩ := h
  split at h
  · rename_i x hx
    simp only [Option.bind_some, Option.bind_eq_some_iff] at h
    obtain ⟨G, hG, u, hg, ⟨kappa, d₁⟩, hk, d₂, h2, h3⟩ := h
    have hok : ok (splitL d row) = true := by
      by_contra hne
      simp [guard, hne] at hg
    exact ⟨row, x, G, kappa, d₁, d₂, hf, hx, hG, hok, hk, h2, h3⟩
  · simp at h

/-- Two constraints that add up to a third, entry by entry and in the targets: what the two say
together of words, the third says. -/
theorem says_of_add (T : Statement) (a b row : Row)
    (hc : ∀ o pt i, ρ.val (a.coefficient o pt i) + ρ.val (b.coefficient o pt i) =
      ρ.val (row.coefficient o pt i))
    (ht : ρ.val a.target + ρ.val b.target = ρ.val row.target) (m : Words K)
    (ha : Means.Says ρ T a m) (hb : Means.Says ρ T b m) : Means.Says ρ T row m := by
  have key : ∀ o pt, Means.onTable ρ T a m o pt + Means.onTable ρ T b m o pt =
      Means.onTable ρ T row m o pt := by
    intro o pt
    unfold Means.onTable
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hc o pt i]; ring
  unfold Means.Says Means.value at *
  rw [← ht, ← ha, ← hb, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [← key o .main, ← key o .mask]; ring

/-- **LAYS.** -/
theorem laysW : LaysW ρ := by
  intro p d d' r hS h
  obtain ⟨row, x, G, kappa, d₁, d₂, hf, hx, hG, hok, hk, h2, h3⟩ := split_inv p d d' r hS h
  have hne : d.loc.gOmega ≠ d.loc.gU := by
    simp only [ok, splitL, List.all_cons, Bool.and_eq_true, bne_iff_ne] at hok
    exact hok.1
  refine ⟨row, onOmega row G.members d.loc.oSp kappa (E.ofTriple x),
    onU row G.members d.loc.oSp kappa (E.ofTriple x), hf, ?_, ?_, fun T m ha hb =>
    says_of_add ρ T _ _ row (split_coefficient ρ row G.members d.loc.oSp kappa _)
      (split_target ρ row G.members d.loc.oSp kappa _) m ha hb⟩
  · rw [rowsOn_addRowP_other d₂ d' _ _ _ h3 hne.symm, rowsOn_addRowP_same d₁ d₂ _ _ h2,
      rowsOn_takeMaskP d d₁ _ _ _ hk]
  · rw [rowsOn_addRowP_same d₂ d' _ _ h3, rowsOn_addRowP_other d₁ d₂ _ _ _ h2 hne,
      rowsOn_takeMaskP d d₁ _ _ _ hk]

/-- A function that says yes to all and lays nothing does not meet LAYS, if a shape needs two
groups. -/
theorem not_laysOfW_yes (p : Par) (hS : p.S.sharedSplitNeeded = true) (d : St) (r : Fmt.RoundView) :
    ¬ LaysOfW ρ fun _ d _ => some d := by
  intro h
  obtain ⟨_, a, _, _, h1, _⟩ := h p d d r hS rfl
  have := congrArg List.length h1
  simp at this

/-- A function that says no to all meets LAYS: the law speaks of a yes alone. -/
theorem laysOfW_no : LaysOfW ρ fun _ _ _ => none := by
  intro p d d' r _ h
  cases h

/-- A weakened copy of "SPLIT": the constraint on G_u is left out. -/
def splitWeak (p : Par) (d : St) (rs : List Fmt.RoundView) : Option St := do
  let l := d.loc
  let row ← fold p.S l (linLayOmega d.st.codes p.S)
  match p.S.sharedSplitNeeded, rs with
  | false, [] => addRowP d l.gU row
  | true, [r] =>
    let mu ← match r.vals with
      | [.e x] => some (E.ofTriple x)
      | _ => none
    let inOmega := (← d.st.groups[l.gOmega]?).members
    guard (ok (splitL d row))
    let (kappa, d) ← takeMaskP d l.oSp
    addRowP d l.gOmega
      { (part row inOmega true).addUnit l.oSp .mask kappa oneE with target := mu }
  | _, _ => none

/-- At no yes of the weakened copy does LAYS's clause on G_u hold. -/
theorem splitWeak_fails (p : Par) (d d' : St) (r : Fmt.RoundView) (hS : p.S.sharedSplitNeeded = true)
    (h : splitWeak p d [r] = some d') (b : Row) :
    rowsOn d' d.loc.gU ≠ rowsOn d d.loc.gU ++ [b] := by
  unfold splitWeak at h
  simp only [hS, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨row, hf, h⟩ := h
  split at h
  · rename_i x hx
    simp only [Option.bind_some, Option.bind_eq_some_iff] at h
    obtain ⟨G, hG, u, hg, ⟨kappa, d₁⟩, hk, h2⟩ := h
    have hok : ok (splitL d row) = true := by
      by_contra hne
      simp [guard, hne] at hg
    have hne : d.loc.gOmega ≠ d.loc.gU := by
      simp only [ok, splitL, List.all_cons, Bool.and_eq_true, bne_iff_ne] at hok
      exact hok.1
    rw [rowsOn_addRowP_other d₁ d' _ _ _ h2 hne, rowsOn_takeMaskP d d₁ _ _ _ hk]
    intro hh
    have := congrArg List.length hh
    simp at this
  · simp at h

end Desc.K14.Law
