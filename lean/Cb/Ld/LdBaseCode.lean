-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBaseCode.lean: what is proved, with nothing assumed beyond the hypotheses of the statements,
of every code read under a transformation (`Cb.LdCode`) from its laws and its distance alone; and
the base case at radii below a third of the distance.

In standard terms: for every code C with `C.Laws`, mutual correlated agreement on lines holds at
every radius e below a third of the distance D of C under its transformation (`C.Dist D`, 3 e < D),
with at most e + 1 exceptional values (`C.MCAat e (e + 1)`).
Statements and their proofs, in one file.
`LdCode`, `C.Laws`, `C.MCAat`, `C.ListAt`, `C.Transparent` (Cb/Ld/LdRel.lean) and `IOR.GoodT` are
told in the head of Cb/Ld/LdBase.lean.

Main names:
  `Spec.ld_mca_third`: the agreement bound told above. C may be a complex of codes of different
    lengths under a repetition: the bound comes from the distance of the whole, and is not the sum
    over the components (`Spec.ld_mca_pair`, `Spec.ld_mca_fam` of Cb/Ld/LdRel.lean give the sum).
  `Spec.ldBase_good_third`: so, for 3 e < D, the base case of Cb/Ld/LdBase.lean has all its
    properties (`IOR.GoodT`) with the errors (e + 2, (N - e - 1)^t), counts of values of the
    verifier's two messages (there: μ and Q), N the number of long positions, under no hypothesis
    but the laws of the code, its distance, and transparency (and the instance arguments: E is a
    finite field; there are finitely many long positions, at least one). (The list of the code with
    two rows has at most one member: `Spec.ld_list_unique` of Cb/Ld/LdRelJohnson.lean.)
  `Spec.ldBase_good_johnson`: under the laws of the code, its distance and transparency (and the
    instance arguments told in the row above), for every radius e below the distance and below the
    Johnson radius of (N, D): the same with the errors (bad + listMax N D e, (N - e - 1)^t): the
    list of the code with two rows is bounded by the Johnson bound (interleaving keeps the distance;
    `Spec.ld_list_johnson`), and the one hypothesis left is mutual correlated agreement of C at e,
    with the count bad.

Why: the hypotheses `C.MCAat e bad` and `(C.il Bool).ListAt e L2` of `Spec.ldBase_good` can be met
(under `C.Laws` and `C.Dist D`): for all codes at small radii; below the Johnson radius the second
always. Beyond a third of the distance the first is a matter of statements on particular codes that
are taken as hypotheses (Cb/Gen/CodeListRS.lean: the limits in its head), or of the coarse count of
Cb/Ld/LdRelAny.lean.

Limits: this file says nothing on an agreement bound beyond a third of the distance, but that
`Spec.ldBase_good_johnson` takes one as a hypothesis. Instances not below half the distance are in
Cb/Ld/LdBaseTest.lean (there at 2 e = D).
The first statement restates, for fields, a lemma of the paper that this protocol builds on
(lean/CREDITS.md); for interleaved rows of one code it is Code/Third.lean's.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdBaseProofs
import Cb.Ld.LdBaseThird
import Cb.Ld.LdRelProofsCode
import Cb.Ld.LdRelJohnsonProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

namespace Spec
open IOR

def ld_mca_third : Prop :=
  ∀ (E P : Type) [Field E] [Fintype E] [Fintype P] (C : LdCode E P) (D e : ℕ),
    C.Laws → C.Dist D → 3 * e < D → C.MCAat e (e + 1)

def ldBase_good_third : Prop :=
  ∀ (E P : Type) [Field E] [Fintype E] [Fintype P] [Nonempty P] (C : LdCode E P) (St : Type)
      (sl : Slf E St C.J) (t : ℕ) (cov : C.NP → P) (D e : ℕ),
    C.Laws → C.Transparent → C.Dist D → 3 * e < D →
    GoodT (ldBaseIOR C sl t cov) (ldBaseHon C sl t cov) (C.rels sl e fun _ => ()) trivRels
      (ldBaseExt C t D) (ldBaseNums C sl t cov e (e + 1) 1)

def ldBase_good_johnson : Prop :=
  ∀ (E P : Type) [Field E] [Fintype E] [Fintype P] [Nonempty P] (C : LdCode E P) (St : Type)
      (sl : Slf E St C.J) (t : ℕ) (cov : C.NP → P) (D e bad : ℕ),
    C.Laws → C.Transparent → C.Dist D → e < D → InJohnson (Fintype.card P) D e → C.MCAat e bad →
    GoodT (ldBaseIOR C sl t cov) (ldBaseHon C sl t cov) (C.rels sl e fun _ => ()) trivRels
      (ldBaseExt C t D) (ldBaseNums C sl t cov e bad (listMax (Fintype.card P) D e))

end Spec

section
variable {E P : Type} [Field E] [Fintype P] {C : LdCode E P}

/-- Under `hC` (`C.Laws`) and `hD` (`C.Dist D`): two different (message, randomness) have transforms
that differ at D long positions or more. -/
theorem ldCw_dist (hC : C.Laws) {D : ℕ} (hD : C.Dist D) {w w' : C.MR} (hne : w ≠ w') :
    D ≤ cnt fun x => ldCw C w x ≠ ldCw C w' x := by
  have hz : ¬ ((w + (-1 : E) • w').1 = 0 ∧ (w + (-1 : E) • w').2 = 0) := fun h => hne (by
    have h0 : w + (-1 : E) • w' = 0 := Prod.ext h.1 h.2
    rwa [neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] at h0)
  refine (hD _ _ hz).trans (cnt_mono fun x hx heq => hx ?_)
  have h1 := ldCw_lin hC w w' (-1 : E) x
  rw [heq] at h1
  exact h1.trans (by rw [neg_one_smul, add_neg_cancel])

theorem ldCw_apart (hC : C.Laws) {D : ℕ} (hD : C.Dist D) : LdwApart (ldCw C) D :=
  fun _ _ hne => ldCw_dist hC hD fun h => hne (congrArg (ldCw C) h)

end

theorem ld_mca_third : Spec.ld_mca_third := by
  intro E P _ _ _ C D e hC hD h3 f₀ f₁
  refine le_trans (cnt_mono fun _ ⟨S, hS, h1, h2⟩ => ?_)
    (ldw_third E C.MR (C.Aa → E) P (ldCw C) D e (C.T f₀) (C.T f₁)
      (ldCw_lin hC) (ldCw_apart hC hD) h3)
  exact ⟨S, hS, ldwOn_iff.2 h1, fun hb => h2 ⟨ldwOn_iff.1 hb.1, ldwOn_iff.1 hb.2⟩⟩

theorem ldBase_good_third : Spec.ldBase_good_third := by
  intro E P _ _ _ _ C St sl t cov D e hC htr hD h3
  exact ldBase_good E P C St sl t cov D e (e + 1) 1 hC htr
    (by omega) (ld_mca_third E P C D e hC hD h3)
    (ld_list_unique E P (C.il Bool) D e (ld_laws_il E P C Bool hC)
      (ld_dist_il E P C Bool D hD) (by omega))

theorem ldBase_good_johnson : Spec.ldBase_good_johnson := by
  intro E P _ _ _ _ C St sl t cov D e bad hC htr hD hed hJ hm
  exact ldBase_good E P C St sl t cov D e bad _ hC htr hed hm
    (ld_list_johnson E P (C.il Bool) D e (ld_laws_il E P C Bool hC) (ld_dist_il E P C Bool D hD) hJ)

end Cb
