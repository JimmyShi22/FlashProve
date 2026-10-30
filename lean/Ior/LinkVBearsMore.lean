-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ior/LinkVBearsMore.lean: budgets for families of slots: demands put together from parts.

In standard terms: for the sequential composition of interactive oracle reductions on a batch of
instances, how invariants on sets of oracle positions are built from parts.

Definitions, statements (in `Iop.Spec`) and proofs. No protocol occurs here. It builds on
Ior/LinkVBears.lean (`QFam`, `Her`, `BearsV`, its rules for chains) and adds what a chain with
mixed oracles needs.

What a batch link and a slot are: the head of Ior/LinkVBears.lean.

Why: at a joint of a batch chain the oracles stand in nested products in the order of sending,
shared ones and the slots' own mixed. The demand at such a joint is a conjunction: of a slot's own
oracle each slot's set is small; of a shared oracle the union over the slots is small. A link that
a slot runs must carry the union-demands on what it only copies; a link that the shared part runs
the each-demands.

Main names:
  `R.NeedsV A qi qo`: the second half of `BearsV` alone (no budget): whenever the family (U_j) is
    within qo, the family of what is needed of the old implicit instance is within qi.
The rules, each under the hypotheses of its statement:
  `Spec.bearsV_and`: further demands beside: `BearsV bud qi qo` and `NeedsV qi' qo'` give
    `BearsV bud (qi.and qi') (qo.and qo')`.
  `Spec.bearsV_mono`: qi weaker, qo stronger, a weaker budget (compared at executions of the
    batch).
  `Spec.need_union`: unions, at one ρ; `Spec.needsV_union`: unions, at a link under shared
    verifier messages.
  `Spec.bearsV_each`, `Spec.bearsV_union`: the two corollaries of Ior/LinkVBears.lean's
    `bearsV_local`, `bearsV_shared` with "each" on both sides, "union" on both sides.
  `Spec.qfam_her`: `QFam.each`; `QFam.union` of a demand that smaller sets meet; `QFam.and`;
    `QFam.left`, `QFam.right`, `QFam.prod`: all are kept by subsets of J.

Limits: the rules are conditional (but for the first member of `Spec.qfam_her`, on `QFam.each`,
which has no hypothesis); they give no protocol. `NeedsV` of a given link (a sending, a round
without a prover message) is read off that link's own `need` by whoever owns it.

Terms: lean/GLOSSARY.md.
-/
import Ior.LinkVBears
import Ior.BatchSeqZkRules

set_option autoImplicit false

namespace Iop
open Prob

namespace QFam
variable {E E₁ E₂ : ExtSpec} {N : ℕ}

/-- of each slot's set -/
def each (q : Finset E.Pos → Prop) : QFam E N := fun _ Us => ∀ j, q (Us j)

open Classical in
/-- of the union over the slots -/
def union (q : Finset E.Pos → Prop) : QFam E N := fun _ Us => q (Finset.univ.biUnion Us)

def and (q q' : QFam E N) : QFam E N := fun J Us => q J Us ∧ q' J Us

/-- of the families of the left parts, of the right parts -/
def left (q : QFam E₁ N) : QFam (E₁.prod E₂) N := fun J Us => q J fun j => (Us j).toLeft
def right (q : QFam E₂ N) : QFam (E₁.prod E₂) N := fun J Us => q J fun j => (Us j).toRight
def prod (q₁ : QFam E₁ N) (q₂ : QFam E₂ N) : QFam (E₁.prod E₂) N := (left q₁).and (right q₂)

end QFam

/-- What is needed of the old implicit instance, as a family. -/
def IOR.NeedsV {X X' : Type} {Ei Eo : ExtSpec} (R : IOR X Ei X' Eo) (A : RoundSplits R.shape) {N : ℕ}
    (qi : QFam Ei N) (qo : QFam Eo N) : Prop :=
  ∀ (J : Finset (Fin N)) (ρ : BRho N R.shape A) (Us : J → Finset Eo.Pos),
    qo J Us → qi J fun j => R.need (ρ.slot j.1) (Us j)

namespace Spec
open IOR

def needsV_of_bearsV : Prop :=
  ∀ (X X' : Type) (Ei Eo : ExtSpec) (R : IOR X Ei X' Eo) (A : RoundSplits R.shape) (N : ℕ)
      (bud : BudB R.shape N) (qi : QFam Ei N) (qo : QFam Eo N),
    R.BearsV A bud qi qo → R.NeedsV A qi qo

def needsV_seq : Prop :=
  ∀ (X X' X'' : Type) (Ei Eo Eo' : ExtSpec) (R₁ : IOR X Ei X' Eo)
      (R₂ : IOR X' Eo X'' Eo') (A₁ : RoundSplits R₁.shape) (A₂ : RoundSplits R₂.shape) (N : ℕ)
      (qa : QFam Ei N) (qb : QFam Eo N) (qc : QFam Eo' N),
    R₁.NeedsV A₁ qa qb → R₂.NeedsV A₂ qb qc → (R₁.seq R₂).NeedsV (RoundSplits.app A₁ A₂) qa qc

def needsV_and : Prop :=
  ∀ (X X' : Type) (Ei Eo : ExtSpec) (R : IOR X Ei X' Eo) (A : RoundSplits R.shape) (N : ℕ)
      (qi qi' : QFam Ei N) (qo qo' : QFam Eo N),
    R.NeedsV A qi qo → R.NeedsV A qi' qo' → R.NeedsV A (qi.and qi') (qo.and qo')

def needsV_mono : Prop :=
  ∀ (X X' : Type) (Ei Eo : ExtSpec) (R : IOR X Ei X' Eo) (A : RoundSplits R.shape) (N : ℕ)
      (qi qi' : QFam Ei N) (qo qo' : QFam Eo N),
    R.NeedsV A qi qo → (∀ J Vs, qi J Vs → qi' J Vs) →
    (∀ J Us, qo' J Us → qo J Us) → R.NeedsV A qi' qo'

/-- Further demands beside. -/
def bearsV_and : Prop :=
  ∀ (X X' : Type) (Ei Eo : ExtSpec) (R : IOR X Ei X' Eo) (A : RoundSplits R.shape) (N : ℕ)
      (bud : BudB R.shape N) (qi qi' : QFam Ei N) (qo qo' : QFam Eo N),
    R.BearsV A bud qi qo → R.NeedsV A qi' qo' → R.BearsV A bud (qi.and qi') (qo.and qo')

def bearsV_mono : Prop :=
  ∀ (X X' : Type) (Ei Eo : ExtSpec) (R : IOR X Ei X' Eo) (A : RoundSplits R.shape) (N : ℕ)
      (bud bud' : BudB R.shape N) (qi qi' : QFam Ei N) (qo qo' : QFam Eo N),
    R.BearsV A bud qi qo →
    (∀ J (ρ : BRho N R.shape A) Ts,
      bud J (fun j => ρ.slot j.1) Ts → bud' J (fun j => ρ.slot j.1) Ts) →
    (∀ J Vs, qi J Vs → qi' J Vs) → (∀ J Us, qo' J Us → qo J Us) → R.BearsV A bud' qi' qo'

/-- from one instance, slot by slot -/
def needsV_each : Prop :=
  ∀ (X X' : Type) (Ei Eo : ExtSpec) (R : IOR X Ei X' Eo) (A : RoundSplits R.shape) (N : ℕ)
      (qi : Finset Ei.Pos → Prop) (qo : Finset Eo.Pos → Prop),
    (∀ ρ U, qo U → qi (R.need ρ U)) → R.NeedsV A (QFam.each qi : QFam Ei N) (QFam.each qo)

open Classical in
/-- States: what is needed for a union is the union of what is needed, over a family that is not
empty, at one ρ. -/
def need_union : Prop :=
  ∀ (X X' : Type) (Ei Eo : ExtSpec) (R : IOR X Ei X' Eo) (ρ : Rho R.shape) (ι : Type) [Fintype ι]
      [Nonempty ι] (Us : ι → Finset Eo.Pos),
    R.need ρ (Finset.univ.biUnion Us) = Finset.univ.biUnion fun j => R.need ρ (Us j)

/-- States, under the hypotheses below: under shared verifier messages union-demands go to
union-demands. -/
def needsV_union : Prop :=
  ∀ (X X' : Type) (Ei Eo : ExtSpec) (R : IOR X Ei X' Eo) (N : ℕ)
      (qi : Finset Ei.Pos → Prop) (qo : Finset Eo.Pos → Prop),
    (∀ ρ U, qo U → qi (R.need ρ U)) → qi ∅ →
    R.NeedsV (RoundSplits.const (RAnn.ofShared .sh) R.shape) (QFam.union qi : QFam Ei N) (QFam.union qo)

/-- An IOR in every slot: "each" on both sides. -/
def bearsV_each : Prop :=
  ∀ (X X' : Type) (Ei Eo : ExtSpec) (R : IOR X Ei X' Eo) (A : RoundSplits R.shape) (N : ℕ)
      (bud : Rho R.shape → Finset (OPos R.shape) → Prop)
      (qi : Finset Ei.Pos → Prop) (qo : Finset Eo.Pos → Prop),
    R.Bears bud qi qo →
    R.BearsV A (N := N) (fun J ρs Ts => ∀ j : J, bud (ρs j) (Ts j)) (QFam.each qi) (QFam.each qo)

open Classical in
/-- An IOR run by the shared part alone: "union" on both sides. -/
def bearsV_union : Prop :=
  ∀ (X X' : Type) (Ei Eo : ExtSpec) (R : IOR X Ei X' Eo) (N : ℕ)
      (bud : Rho R.shape → Finset (OPos R.shape) → Prop)
      (qi : Finset Ei.Pos → Prop) (qo : Finset Eo.Pos → Prop),
    R.Bears bud qi qo → qi ∅ →
    R.BearsV (RoundSplits.const (RAnn.ofShared .sh) R.shape) (N := N)
      (fun J ρs Ts => ∀ j : J, bud (ρs j) (Finset.univ.biUnion Ts)) (QFam.union qi) (QFam.union qo)

/-- States, under the hypotheses below: all these demands are kept by subsets of J. -/
def qfam_her : Prop :=
  ∀ (E E' : ExtSpec) (N : ℕ),
    (∀ q : Finset E.Pos → Prop, (QFam.each q : QFam E N).Her) ∧
    (∀ q : Finset E.Pos → Prop, (∀ U V, V ⊆ U → q U → q V) → (QFam.union q : QFam E N).Her) ∧
    (∀ q q' : QFam E N, q.Her → q'.Her → (q.and q').Her) ∧
    (∀ q : QFam E N, q.Her → (QFam.left q : QFam (E.prod E') N).Her) ∧
    (∀ q : QFam E' N, q.Her → (QFam.right q : QFam (E.prod E') N).Her) ∧
    ∀ (q : QFam E N) (q' : QFam E' N), q.Her → q'.Her → (QFam.prod q q').Her

end Spec

open IOR

theorem needsV_of_bearsV : Spec.needsV_of_bearsV := fun _ _ _ _ _ _ _ _ _ _ h J ρ Us hU =>
  (h J ρ Us hU).2

theorem needsV_seq : Spec.needsV_seq := by
  intro X X' X'' Ei Eo Eo' R₁ R₂ A₁ A₂ N qa qb qc h₁ h₂ J
    (ρ : BRho N (R₁.shape ++ R₂.shape) (RoundSplits.app A₁ A₂)) Us hU
  have h := h₁ J (BRho.fstA A₁ A₂ ρ) _ (h₂ J (BRho.sndA A₁ A₂ ρ) Us hU)
  simp only [BRho.slot_fstA, BRho.slot_sndA] at h
  have e : (fun j : J => (R₁.seq R₂).need (ρ.slot j.1) (Us j)) =
      fun j : J =>
        R₁.need (Rho.fst (ρ.slot j.1)) (R₂.need (Rho.snd (s := R₁.shape) (ρ.slot j.1)) (Us j)) :=
    funext fun j => need_seq _ _ _ _ _ _ R₁ R₂ (ρ.slot j.1) (Us j)
  exact (congrArg (fun T => qa J T) e).mpr h

theorem needsV_and : Spec.needsV_and := fun _ _ _ _ _ _ _ _ _ _ _ h h' J ρ Us hU =>
  ⟨h J ρ Us hU.1, h' J ρ Us hU.2⟩

theorem needsV_mono : Spec.needsV_mono := fun _ _ _ _ _ _ _ _ _ _ _ h hi ho J ρ Us hU =>
  hi J _ (h J ρ Us (ho J Us hU))

theorem bearsV_and : Spec.bearsV_and := fun _ _ _ _ _ _ _ _ _ _ _ _ h h' J ρ Us hU =>
  ⟨(h J ρ Us hU.1).1, (h J ρ Us hU.1).2, h' J ρ Us hU.2⟩

theorem bearsV_mono : Spec.bearsV_mono := fun _ _ _ _ _ _ _ _ _ _ _ _ _ h hb hi ho J ρ Us hU =>
  ⟨hb J ρ _ (h J ρ Us (ho J Us hU)).1, hi J _ (h J ρ Us (ho J Us hU)).2⟩

theorem needsV_each : Spec.needsV_each := fun _ _ _ _ _ _ _ _ _ h _ ρ Us hU j =>
  h (ρ.slot j.1) (Us j) (hU j)

open Classical in
theorem need_union : Spec.need_union := by
  intro X X' Ei Eo R ρ ι _ hne Us
  obtain ⟨j0⟩ := hne
  ext q
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, mem_need, mem_given]
  constructor
  · rintro ((hq | ⟨p, (hp | ⟨u, ⟨j, hu⟩, hp⟩), hq⟩) | ⟨u, ⟨j, hu⟩, hq⟩)
    · exact ⟨j0, Or.inl (Or.inl hq)⟩
    · exact ⟨j0, Or.inl (Or.inr ⟨p, Or.inl hp, hq⟩)⟩
    · exact ⟨j, Or.inl (Or.inr ⟨p, Or.inr ⟨u, hu, hp⟩, hq⟩)⟩
    · exact ⟨j, Or.inr ⟨u, hu, hq⟩⟩
  · rintro ⟨j, (hq | ⟨p, (hp | ⟨u, hu, hp⟩), hq⟩) | ⟨u, hu, hq⟩⟩
    · exact Or.inl (Or.inl hq)
    · exact Or.inl (Or.inr ⟨p, Or.inl hp, hq⟩)
    · exact Or.inl (Or.inr ⟨p, Or.inr ⟨u, ⟨j, hu⟩, hp⟩, hq⟩)
    · exact Or.inr ⟨u, ⟨j, hu⟩, hq⟩

open Classical in
theorem needsV_union : Spec.needsV_union := by
  intro X X' Ei Eo R N qi qo h h0 J ρ Us hU
  show qi (Finset.univ.biUnion fun j : J => R.need (ρ.slot j.1) (Us j))
  by_cases hJ : Nonempty J
  · obtain ⟨j0⟩ := hJ
    have e : (fun j : J => R.need (ρ.slot j.1) (Us j)) = fun j : J => R.need (ρ.slot j0.1) (Us j) :=
      funext fun j => by rw [BatchSeqZk.slot_eq ρ j.1, BatchSeqZk.slot_eq ρ j0.1]
    haveI : Nonempty J := ⟨j0⟩
    rw [e, ← need_union X X' Ei Eo R (ρ.slot j0.1) J Us]
    exact h _ _ hU
  · have e : (Finset.univ.biUnion fun j : J => R.need (ρ.slot j.1) (Us j)) = ∅ := by
      ext q
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro ⟨j, _⟩
      exact hJ ⟨j⟩
    rw [e]
    exact h0

theorem bearsV_each : Spec.bearsV_each := fun X X' Ei Eo R A N bud qi qo h =>
  bearsV_local X X' Ei Eo R A N bud qi qo (QFam.each qi) (QFam.each qo) h (fun _ _ hU => hU)
    (needsV_each X X' Ei Eo R A N qi qo fun ρ U hU => (h ρ U hU).2)

theorem bearsV_union : Spec.bearsV_union := fun X X' Ei Eo R N bud qi qo h h0 =>
  bearsV_shared X X' Ei Eo R N bud qi qo (QFam.union qi) (QFam.union qo) h (fun _ _ hU => hU)
    (needsV_union X X' Ei Eo R N qi qo (fun ρ U hU => (h ρ U hU).2) h0)

open Classical in
theorem qfam_her : Spec.qfam_her := by
  intro E E' N
  have hand : ∀ {E₀ : ExtSpec} (q q' : QFam E₀ N), q.Her → q'.Her → (q.and q').Her :=
    fun q q' hr hr' J J' h Us hU => ⟨hr J J' h Us hU.1, hr' J J' h Us hU.2⟩
  have hl : ∀ q : QFam E N, q.Her → (QFam.left q : QFam (E.prod E') N).Her :=
    fun q hr J J' h Us hU => hr J J' h _ hU
  have hrr : ∀ q : QFam E' N, q.Her → (QFam.right q : QFam (E.prod E') N).Her :=
    fun q hr J J' h Us hU => hr J J' h _ hU
  refine ⟨fun q J J' h Us hU j => hU ⟨j.1, h j.2⟩, fun q hq J J' h Us hU => hq _ _ ?_ hU,
    hand, hl, hrr, fun q q' h h' => hand _ _ (hl q h) (hrr q' h')⟩
  intro p hp
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.1 hp
  exact Finset.mem_biUnion.2 ⟨⟨j.1, h j.2⟩, Finset.mem_univ _, hj⟩

end Iop
