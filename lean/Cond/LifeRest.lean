-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cond/LifeRest.lean: the bound ζ on privacy of the compiled scheme (`zetaT`, Cond/ObjBounds.lean)
is its overrun term and a rest. The rest at `atLife D p'` (Cond/LifeMono.lean) is at most the rest
at D when leaves are taken away and no salt gets shorter. So ζ at a smaller lifetime is at most that
lifetime's own overrun term and the rest at the larger one.

This is arithmetic on the formula `zetaT`, as in Cond/LifeMono.lean. `atLife D p'` is the data D
with the compiler's parameters p' in place of its own. "A smaller lifetime" is a p' with
p'.M ≤ D.p.M (M: one less than the number of leaves) and no shorter salt. A leaf is a further
encoded index. The overrun term of parameters p is the first summand of `zetaT`,
p.leaves · binTail n' p.leaves p.s1: it bounds the chance that some leaf gets more than s1 of n'
sessions.
One definition, statements and proofs. Nothing is assumed beyond the hypotheses of
the statements and whatever the arguments hold as proofs.

Why: under the three premises below, `life_zeta` of Cond/LifeMono.lean bounds ζ at `atLife D p'` by
the overrun term of p' plus the whole ζ at D. That ζ holds the overrun term of D.p, the larger
lifetime. So a bound carried down by `life_zeta` holds two overrun terms. At few leaves the second
is foreign: a term of another lifetime, D.p, not of p'. At p' = D.p the two are the same term, which
then stands twice in the bound. The proof of `life_zeta` shows more than its statement: the bound
without the second term. `life_zetaR` states it.

Main names:
  `zetaRest P r D κ₀ n o t n'`: the text of `zetaT` without its first summand. What is left: the
    hash terms, the work's term, the hiding errors of the interactive protocol.
  `Spec.zetaT_eq`: zetaT .. t n' = D.p.leaves · binTail n' D.p.leaves D.p.s1 + zetaRest .. t n'.
  `Spec.life_rest`: if p'.M ≤ D.p.M, D.p.sMT ≤ p'.sMT and D.p.sFS ≤ p'.sFS, then `zetaRest` at
    `atLife D p'` is at most `zetaRest` at D.
  `Spec.life_zetaR`: under the same premises,
      zetaT P r (atLife D p') κ₀ n o t n'
        ≤ p'.leaves · binTail n' p'.leaves p'.s1 + zetaRest P r D κ₀ n o t n'.
  `Spec.binTail_ne_top`: if 0 < m, then binTail n m s is finite.
  `Spec.rest_of_zeta`: if zetaT .. t n' ≤ D.p.leaves · binTail n' D.p.leaves D.p.s1 + c, then
    zetaRest .. t n' ≤ c (a finite summand is cancelled). So a bound on ζ whose first summand is the
    overrun term itself gives a bound on the rest, without a new evaluation of ζ.

Notation: `κ₀`: a number; in `FitK.good` (CompileK/Main.lean): the samplers obey their law, with
bias κ₀ a block; `n`, except in `binTail_ne_top`: a number; in `FitK.totLe` (CompileK/Main.lean),
which is `D.dr.TotLe n` (`BatchProtocol.Draws.TotLe`, Iop/BatchWireDraw.lean): a bound on the blocks of all
rounds of one protocol; `o`, of type `Option (S.Wk Nn)`; `S.Wk` (Cond/ObjBits.lean): the
proof of work, by the names of the sub-protocols' rounds; `D.p`, `p'`, of type `Params`
(Compile/Star.lean); in `DataK` (CompileK/Main.lean): salt lengths, number of further encoded
indices, sessions on each.

Limits: this file does not say that ζ bounds anything (the compiler's theorem). It does not say that
the data fit at p'. This file says nothing on the value of any number. Coarse still: the rest on the
right side holds D's larger counts.

Terms: lean/GLOSSARY.md: block, hash term, leaf, overrun term, proof of work (work), sampler,
session.
-/
import Cond.LifeMono

set_option autoImplicit false

noncomputable section

namespace TopC
open Iop Rom ZKCP Compile Compile.Batch Top.Batch Top.ProgDraw Hiop
open scoped ENNReal

/-- ζ without its overrun term. -/
def zetaRest {C : ConfigurationWithOutOfDomainSample} {S : SubsR C} {Nn : Type} [Inhabited Nn] (P : S.Nums) (r : C.Rec) {lam : ℕ}
    (D : DataK (S.obj r) lam) (κ₀ : ℝ≥0∞) (n : ℕ) (o : Option (S.Wk Nn)) :
    ℕ → ℕ → ℝ≥0∞ := fun t n' =>
  ((t : ℝ≥0∞) * muB2 D.W D.p n' + hashSqBG2 D.W D.p n') + workSq r D n' o +
    (κ₀ ^ n * P.wf.pHid + n' * (S.N * ((κ₀ ^ n) ^ S.N * P.req.pHid)))

namespace Spec

def zetaT_eq : Prop :=
  ∀ (Nn : Type) [Inhabited Nn] (C : ConfigurationWithOutOfDomainSample) (S : SubsR C) (P : S.Nums) (r : C.Rec) (lam : ℕ)
      (D : DataK (S.obj r) lam) (κ₀ : ℝ≥0∞) (n : ℕ) (o : Option (S.Wk Nn)) (t n' : ℕ),
    zetaT P r D κ₀ n o t n' = D.p.leaves * binTail n' D.p.leaves D.p.s1 + zetaRest P r D κ₀ n o t n'

def life_rest : Prop :=
  ∀ (Nn : Type) [Inhabited Nn] (C : ConfigurationWithOutOfDomainSample) (S : SubsR C) (P : S.Nums) (r : C.Rec) (lam : ℕ)
      (D : DataK (S.obj r) lam) (p' : Params) (κ₀ : ℝ≥0∞) (n : ℕ) (o : Option (S.Wk Nn)) (t n' : ℕ),
    p'.M ≤ D.p.M → D.p.sMT ≤ p'.sMT → D.p.sFS ≤ p'.sFS →
    zetaRest P r (atLife D p') κ₀ n o t n' ≤ zetaRest P r D κ₀ n o t n'

/-- ζ at a smaller lifetime: its own overrun term and the rest at the larger one. -/
def life_zetaR : Prop :=
  ∀ (Nn : Type) [Inhabited Nn] (C : ConfigurationWithOutOfDomainSample) (S : SubsR C) (P : S.Nums) (r : C.Rec) (lam : ℕ)
      (D : DataK (S.obj r) lam) (p' : Params) (κ₀ : ℝ≥0∞) (n : ℕ) (o : Option (S.Wk Nn)) (t n' : ℕ),
    p'.M ≤ D.p.M → D.p.sMT ≤ p'.sMT → D.p.sFS ≤ p'.sFS →
    zetaT P r (atLife D p') κ₀ n o t n' ≤
      p'.leaves * binTail n' p'.leaves p'.s1 + zetaRest P r D κ₀ n o t n'

def binTail_ne_top : Prop := ∀ n m s : ℕ, 0 < m → binTail n m s ≠ ⊤

/-- From a bound on ζ to a bound on the rest. -/
def rest_of_zeta : Prop :=
  ∀ (Nn : Type) [Inhabited Nn] (C : ConfigurationWithOutOfDomainSample) (S : SubsR C) (P : S.Nums) (r : C.Rec) (lam : ℕ)
      (D : DataK (S.obj r) lam) (κ₀ : ℝ≥0∞) (n : ℕ) (o : Option (S.Wk Nn)) (t n' : ℕ) (c : ℝ≥0∞),
    zetaT P r D κ₀ n o t n' ≤ D.p.leaves * binTail n' D.p.leaves D.p.s1 + c →
    zetaRest P r D κ₀ n o t n' ≤ c

end Spec

theorem zetaT_eq : Spec.zetaT_eq := by
  intro Nn _ C S P r lam D κ₀ n o t n'
  unfold zetaT zetaRest
  simp only [add_assoc]

theorem life_rest : Spec.life_rest := by
  intro Nn _ C S P r lam D p' κ₀ n o t n' h h1 h2
  obtain ⟨m1, m2, m3⟩ := life_hash _ _ lam D.L D.W D.p p' n' h h1 h2
  have hw : workSq r (atLife D p') n' o ≤ workSq r D n' o := by
    cases o with
    | none => exact le_rfl
    | some w => exact m3 Nn w.Dg _ _ _
  have hX : (t : ℝ≥0∞) * muB2 D.W p' n' + hashSqBG2 D.W p' n' ≤
      (t : ℝ≥0∞) * muB2 D.W D.p n' + hashSqBG2 D.W D.p n' :=
    add_le_add (mul_le_mul' le_rfl m1) m2
  show ((t : ℝ≥0∞) * muB2 D.W p' n' + hashSqBG2 D.W p' n') + workSq r (atLife D p') n' o +
      (κ₀ ^ n * P.wf.pHid + n' * (S.N * ((κ₀ ^ n) ^ S.N * P.req.pHid))) ≤
    ((t : ℝ≥0∞) * muB2 D.W D.p n' + hashSqBG2 D.W D.p n') + workSq r D n' o +
      (κ₀ ^ n * P.wf.pHid + n' * (S.N * ((κ₀ ^ n) ^ S.N * P.req.pHid)))
  exact add_le_add (add_le_add hX hw) le_rfl

theorem life_zetaR : Spec.life_zetaR := by
  intro Nn _ C S P r lam D p' κ₀ n o t n' h h1 h2
  rw [zetaT_eq]
  exact add_le_add le_rfl (life_rest Nn C S P r lam D p' κ₀ n o t n' h h1 h2)

theorem binTail_ne_top : Spec.binTail_ne_top := by
  intro n m s hm
  unfold binTail
  refine ENNReal.sum_ne_top.2 fun j _ => ?_
  refine ENNReal.div_ne_top
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)))
    ?_
  exact pow_ne_zero _ (Nat.cast_ne_zero.2 hm.ne')

theorem rest_of_zeta : Spec.rest_of_zeta := by
  intro Nn _ C S P r lam D κ₀ n o t n' c h
  rw [zetaT_eq] at h
  exact (ENNReal.add_le_add_iff_left
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (binTail_ne_top n' D.p.leaves D.p.s1 (Nat.succ_pos _)))).1 h

end TopC
