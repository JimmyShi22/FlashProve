-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cond/LifeMono.lean: the bound ζ on privacy of the compiled scheme (`zetaT`, Cond/ObjBounds.lean)
at a smaller lifetime: all its terms but the overrun term at p' are at most those at p when further
encoded indices ("leaves") are taken away and no salt gets shorter; the overrun term is kept as a
term.

This is arithmetic on the formula `zetaT`: inequalities between its values at two settings p', p of
the compiler's four parameters. "A smaller lifetime" is here a setting p' with p'.M ≤ p.M: not more
leaves, and no salt gets shorter (p.sMT ≤ p'.sMT, p.sFS ≤ p'.sFS); nothing is asked of s1.
One definition, statements and proofs. Generic: any configuration, sub-protocols,
numbers, data. Nothing is assumed beyond the hypotheses of the statements and whatever the arguments
hold as proofs. Many statements of this library are written twice: a definition in the namespace
`Spec` states a proposition, and a theorem of the same name outside that namespace proves it
(lean/GLOSSARY.md).

Main names:
  `atLife D p'`: the data D with the compiler's four parameters p' for its own. The four: lengths of
    the two salts; M: one less than the number of leaves; s1: sessions on a leaf: read by the bound
    ζ and by the simulator; the compiled scheme's C, P, V and the extractor do not read s1.
  `Spec.life_counts`: if p'.M ≤ p.M, then `xTree`, `xFb`, `xFbG`, `xGr` at p' are at most those at p
    (each is a sum in which the number of leaves is a factor).
  `Spec.life_hash`: if p'.M ≤ p.M, p.sMT ≤ p'.sMT and p.sFS ≤ p'.sFS, then `muB2`, `hashSqBG2`, and
    with proof of work `sqWork`, at p' are at most those at p.
  `Spec.life_zeta`: if p'.M ≤ D.p.M, D.p.sMT ≤ p'.sMT and D.p.sFS ≤ p'.sFS, then
      zetaT P r (atLife D p') κ₀ n o t n'
        ≤ p'.leaves · binTail n' p'.leaves p'.s1 + zetaT P r D κ₀ n o t n'.
    A bound on ζ that is shown at one lifetime is carried to every smaller one at the price of that
    lifetime's own overrun term.

Why the overrun term is kept: leaves · binTail n' leaves s1 bounds the chance that some leaf gets
more than s1 of n' sessions: it does not fall with the lifetime as the other terms do (at p' they
are at most those at p): so ζ is not shown monotone in the lifetime. The overrun term is 0 while
n' ≤ s1 (`life_tail0`).

Notation: `κ₀`: a number; in `FitK.good` (CompileK/Main.lean): the samplers obey their law, with
bias κ₀ a block; `n`, in `life_zeta`: a number; in `FitK.totLe` (CompileK/Main.lean), which is
`D.dr.TotLe n` (`BatchProtocol.Draws.TotLe`, Iop/BatchWireDraw.lean): a bound on the blocks of all rounds of
one protocol; `o`, of type `Option (S.Wk Nn)`; `S.Wk` (Cond/ObjBits.lean): the proof of
work, by the names of the sub-protocols' rounds.

Limits: this file does not say that the overrun term rises when leaves are taken away: that is no
theorem: a search found it false of the formula where the formula is at least 1, and no case below
1. When sessions on a leaf (s1) are taken away it does not fall: that is the sum's form. Coarse: the
right side still holds D's own overrun term and D's larger counts (without that term: `life_zetaR`,
Cond/LifeRest.lean). This file does not say that ζ bounds anything (the compiler's theorem). It does
not say that the data fit at p'. It says nothing on numerals.

Terms: lean/GLOSSARY.md.
-/
import Cond.ObjBounds

set_option autoImplicit false

noncomputable section

namespace TopC
open Iop Rom ZKCP Compile Compile.Batch Top.Batch Top.ProgDraw Hiop
open scoped ENNReal

/-- The data with other parameters of the compiler. -/
def atLife {I X : Type} {L : BatchProtocol I X} {lam : ℕ} (D : DataK L lam) (p' : Params) : DataK L lam :=
  { D with p := p' }

namespace Spec

def life_counts : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (p p' : Params) (n : ℕ), p'.M ≤ p.M →
    xTree W p' n ≤ xTree W p n ∧
    xFb (L := L) p' n ≤ xFb (L := L) p n ∧
    xFbG W p' n ≤ xFbG W p n ∧
    xGr W p' n ≤ xGr W p n

def life_hash : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (p p' : Params) (n : ℕ), p'.M ≤ p.M →
    p.sMT ≤ p'.sMT → p.sFS ≤ p'.sFS →
    muB2 W p' n ≤ muB2 W p n ∧
    hashSqBG2 W p' n ≤ hashSqBG2 W p n ∧
    ∀ (Nn : Type) [Inhabited Nn] (Dg : GrData Nn) (gT : GBits L.offline.shape)
        (gL : GBits L.link.shape) (gB : GBits L.onlineBatch.loc.shape),
      Cost.sqWork W Dg gT gL gB p' n ≤ Cost.sqWork W Dg gT gL gB p n

def life_tail0 : Prop := ∀ n m s : ℕ, n ≤ s → binTail n m s = 0

/-- ζ at a smaller lifetime. -/
def life_zeta : Prop :=
  ∀ (Nn : Type) [Inhabited Nn] (C : ConfigurationWithOutOfDomainSample) (S : SubsR C) (P : S.Nums) (r : C.Rec) (lam : ℕ)
    (D : DataK (S.obj r) lam) (p' : Params) (κ₀ : ℝ≥0∞) (n : ℕ) (o : Option (S.Wk Nn)) (t n' : ℕ),
    p'.M ≤ D.p.M → D.p.sMT ≤ p'.sMT → D.p.sFS ≤ p'.sFS →
    zetaT P r (atLife D p') κ₀ n o t n' ≤ p'.leaves * binTail n' p'.leaves p'.s1 + zetaT P r D κ₀ n o t n'

end Spec

theorem life_term {a a' b b' k k' : ℕ} (ha : a' ≤ a) (hb : b' ≤ b) (hk : k ≤ k') :
    (a' : ℝ≥0∞) * (b' : ℕ) / 2 ^ k' ≤ (a : ℝ≥0∞) * (b : ℕ) / 2 ^ k :=
  ENNReal.div_le_div (mul_le_mul' (Nat.cast_le.2 ha) (Nat.cast_le.2 hb))
    (pow_le_pow_right₀ one_le_two hk)

theorem life_term1 {a a' k k' : ℕ} (ha : a' ≤ a) (hk : k ≤ k') :
    (a' : ℝ≥0∞) / 2 ^ k' ≤ (a : ℝ≥0∞) / 2 ^ k :=
  ENNReal.div_le_div (Nat.cast_le.2 ha) (pow_le_pow_right₀ one_le_two hk)

theorem life_counts : Spec.life_counts := by
  intro I X lam L W p p' n h
  have hl : p'.leaves ≤ p.leaves := Nat.succ_le_succ h
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold xTree; gcongr
  · unfold xFb; gcongr
  · unfold xFbG; gcongr
  · unfold xGr; gcongr

theorem life_hash : Spec.life_hash := by
  intro I X lam L W p p' n h h1 h2
  obtain ⟨c1, c2, c3, c4⟩ := life_counts I X lam L W p p' n h
  have hm : min p.sFS lam ≤ min p'.sFS lam := min_le_min_right _ h2
  refine ⟨?_, ?_, fun Nn _ Dg gT gL gB => ?_⟩
  · unfold muB2
    exact max_le_max (life_term1 c1 h1)
      (max_le_max (life_term1 c1 le_rfl) (max_le_max (life_term1 c2 hm) le_rfl))
  · unfold hashSqBG2
    exact add_le_add
      (add_le_add
        (add_le_add (life_term c1 (Nat.add_le_add_left c1 0) h1)
          (life_term c1 (Nat.add_le_add_left c1 0) le_rfl))
        (add_le_add (life_term c2 (Nat.add_le_add_left c2 0) hm) (life_term c4 c3 hm))) le_rfl
  · obtain ⟨-, -, g3, g4⟩ := life_counts I X lam _ (W.grind Dg gT gL gB) p p' n h
    unfold Cost.sqWork
    exact life_term g4 g3 hm

theorem life_tail0 : Spec.life_tail0 := by
  intro n m s h
  unfold binTail
  rw [Finset.Icc_eq_empty (by omega)]
  simp

theorem life_zeta : Spec.life_zeta := by
  intro Nn _ C S P r lam D p' κ₀ n o t n' h h1 h2
  obtain ⟨m1, m2, m3⟩ := life_hash _ _ lam D.L D.W D.p p' n' h h1 h2
  have hw : workSq r (atLife D p') n' o ≤ workSq r D n' o := by
    cases o with
    | none => exact le_rfl
    | some w => exact m3 Nn w.Dg _ _ _
  have hX : (t : ℝ≥0∞) * muB2 D.W p' n' + hashSqBG2 D.W p' n' ≤
      (t : ℝ≥0∞) * muB2 D.W D.p n' + hashSqBG2 D.W D.p n' :=
    add_le_add (mul_le_mul' le_rfl m1) m2
  show (p'.leaves : ℝ≥0∞) * binTail n' p'.leaves p'.s1 +
      ((t : ℝ≥0∞) * muB2 D.W p' n' + hashSqBG2 D.W p' n') + workSq r (atLife D p') n' o +
      (κ₀ ^ n * P.wf.pHid + n' * (S.N * ((κ₀ ^ n) ^ S.N * P.req.pHid))) ≤
    (p'.leaves : ℝ≥0∞) * binTail n' p'.leaves p'.s1 +
      ((D.p.leaves : ℝ≥0∞) * binTail n' D.p.leaves D.p.s1 +
        ((t : ℝ≥0∞) * muB2 D.W D.p n' + hashSqBG2 D.W D.p n') + workSq r D n' o +
        (κ₀ ^ n * P.wf.pHid + n' * (S.N * ((κ₀ ^ n) ^ S.N * P.req.pHid))))
  rw [add_assoc, add_assoc]
  refine add_le_add le_rfl ?_
  rw [← add_assoc]
  exact add_le_add (add_le_add (hX.trans le_add_self) hw) le_rfl

end TopC
