-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/OmegaCrosses.lean: THE TWO PREMISES ON OMEGA AT THE JOINT OF THE SHARED AND THE LAST CHAIN ((PO→), (PO←) of Johnson/Desc/Sound/BordersLastQ.lean: TieLast), PAID BY MAKE. Two small
lemmas, two statements written as def … : Prop, and their proofs.

At the shared chain a shared item is read at the ACTING PART's value (the chain's own record, the stored table, the chain's own trees that are sent); at the last chain Omega's pin and promise are read at
the whole strings. act_cell, act_col: what an acting part's value shows agrees with the whole strings at the stored table and at every tree from lo to below hi: by the make of the acting part.
  ReadsTree: THE CONDITION ON THE LETTERS: shown, no collision and the pin of a tenant read the oracles through that tenant's tree alone.
  OmegaForward, OmegaBack: under it, with Omega's tree among the shared chain's own trees that are sent at its last border (two comparisons of numbers): (PO→) and (PO←), to the letter.

Limits. ReadsTree at the filled letters (promSigS, meaningSigS: Johnson/Desc/Sound/BordersSharedFill.lean) is owed: small lemmas on the library's notions. At letters it cannot be proved. The two comparisons are tests on the
plan's numbers: not yet run.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.BordersLastQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.Last

/-- What an acting part's value shows of the stored table is what the whole strings show. -/
theorem act_cell {S S₀ : Type} (F : Frame) (get : S → S₀) (lo hi : ℕ) (a : S × F.E.Str) (x : ℕ) :
    (strsOfAct F ((actAt F get lo hi).2 a)).cell x = (strsOf F a.2).cell x := rfl

/-- The like of a tree from lo to below hi. -/
theorem act_col {S S₀ : Type} (F : Frame) (get : S → S₀) (lo hi : ℕ) (a : S × F.E.Str) (j x : ℕ)
    (h₁ : lo ≤ j) (h₂ : j < hi) :
    (strsOfAct F ((actAt F get lo hi).2 a)).col j x = (strsOf F a.2).col j x := by
  show ((if lo ≤ j ∧ j < hi then (posL F.all j x).map a.2.2 else none).getD []) =
    ((posL F.all j x).map a.2.2).getD []
  rw [if_pos ⟨h₁, h₂⟩]

/-- The letters on a tenant read the oracles through the tenant's tree alone. -/
def ReadsTree {S₂ P₁ Wt : Type} (Mg : MeaningS S₂ P₁ Wt) (Pm : PromMeaning S₂) : Prop :=
  (∀ j t (y y' : Strs), (∀ x, y'.col j x = y.col j x) → Pm.shown j t y → Pm.shown j t y') ∧
    (∀ j t s (y y' : Strs), (∀ x, y'.col j x = y.col j x) → Pm.noColl j t s y → Pm.noColl j t s y') ∧
    ∀ j t s (y y' : Strs) w, (∀ x, y'.col j x = y.col j x) → Mg.pin j t s y w → Mg.pin j t s y' w

/-- **(PO→), by make.** -/
def OmegaForward : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (Y P S₁' S₂' S₃' X₁ X₂ Cl Wt : Type)
    (T : Three C D all Y (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') X₁ X₂ Cl Wt) (N : NumbersS)
    (Mg : MeaningS S₂' (P × S₁') Wt) (Pm : PromMeaning S₂'),
    ReadsTree Mg Pm → N.lo ≤ (N.tenant .oOmega).1 →
    (N.tenant .oOmega).1 < hiAt (1 + T.l₂.length) T.p₂ T.l₂ →
    ∀ b : ((P × S₁') × S₂') × (EAll D all).Str,
      (PromS.noColl .oOmega).holds N Pm ((actQ N T.p₂ T.l₂ (1 + T.l₂.length)).2 b).1
        (strsOfAct (frameAt D all D.key₂ T.ft₂) ((actQ N T.p₂ T.l₂ (1 + T.l₂.length)).2 b)) →
      (PromS.noColl .oOmega).holds N Pm b.1.2 (strsOf (frameAt D all D.key₃ T.ft₃) b.2)

/-- **(PO←), by make.** -/
def OmegaBack : Prop :=
  ∀ (C : CK) (D : WholeD) (all : List LeftT) (Y P S₁' S₂' S₃' X₁ X₂ Cl Wt : Type)
    (T : Three C D all Y (P × S₁') ((P × S₁') × S₂') ((P × S₁' × S₂') × S₃') X₁ X₂ Cl Wt) (N : NumbersS)
    (Mg : MeaningS S₂' (P × S₁') Wt) (Pm : PromMeaning S₂'),
    ReadsTree Mg Pm → N.lo ≤ (N.tenant .oOmega).1 →
    (N.tenant .oOmega).1 < hiAt (1 + T.l₂.length) T.p₂ T.l₂ →
    ∀ (b : ((P × S₁') × S₂') × (EAll D all).Str) (w : Wt),
      (ItemS.pin .oOmega).holdsSh N Mg b.1.2 (strsOf (frameAt D all D.key₃ T.ft₃) b.2) w →
      muQ N Mg T.p₂ T.l₂ (.pin .oOmega) (1 + T.l₂.length)
        ((actQ N T.p₂ T.l₂ (1 + T.l₂.length)).2 b) w

theorem omegaForward : OmegaForward := by
  intro C D all Y P S₁' S₂' S₃' X₁ X₂ Cl Wt T N Mg Pm hR h₁ h₂ b h
  have hc : ∀ x, (strsOf (frameAt D all D.key₃ T.ft₃) b.2).col (N.tenant .oOmega).1 x =
      (strsOfAct (frameAt D all D.key₂ T.ft₂)
        ((actQ N T.p₂ T.l₂ (1 + T.l₂.length)).2 b)).col (N.tenant .oOmega).1 x := fun x =>
    (act_col (frameAt D all D.key₂ T.ft₂) Prod.snd N.lo _ b _ x h₁ h₂).symm
  exact ⟨hR.1 _ _ _ _ hc h.1, hR.2.1 _ _ _ _ _ hc h.2⟩

theorem omegaBack : OmegaBack := by
  intro C D all Y P S₁' S₂' S₃' X₁ X₂ Cl Wt T N Mg Pm hR h₁ h₂ b w h
  exact hR.2.2 _ _ _ _ _ w
    (fun x => act_col (frameAt D all D.key₂ T.ft₂) Prod.snd N.lo _ b _ x h₁ h₂) h

#check @OmegaForward
#check @OmegaBack

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.omegaForward
#print axioms VerifiableInference.Desc.Sound.omegaBack
