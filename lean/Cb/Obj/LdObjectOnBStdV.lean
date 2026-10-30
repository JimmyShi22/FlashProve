-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectOnBStdV.lean: for toys: the test for linear constraints on the encoded index with
standard parts, for at most N instances: both items of the object's list, under the hypotheses of
`Spec.stdLnB_object_far`.

The test for linear constraints is the interactive oracle proof of proximity (IOPP) for the
constraint relation.

Definitions, statements (`Cb.Spec.stdLnB_one`, `Cb.Spec.stdLnB_honest`, `Cb.Spec.stdLnB_object_far`)
and proofs. A tool for guards against empty theorems; no parameter of a protocol. The second half of
Cb/Obj/LdObjectOnBStd.lean.

Main names:
  `D.cZV N L tW tU tO x₀`: the closing for a batch with its honest side
    (Cb/Ld/LdLinCloseVLin.lean: `T.cZV`) at the standard plan (its two tests:
    Cb/Obj/LdObjectOnBStd.lean, `D.QA`; W, G_u, Ω: Cb/Obj/LdObjectLinStd.lean).
    x₀: fixed values for what a slot owns in the shared part's own statement.
  `D.HypB N L tW tU tO`: the conditions: `D.Hyp` (conditions on codes, sample maps and numbers, one
    instance), and one more number: tb₁ + N · tb₂ ≤ tO:
    Ω, a shared oracle message, lies in the shared test and in the test of each of the N slots: its
    encoding has to hide the positions that all 1 + N tests draw.
    (G_u lies in the first test alone; W is a slot's own: for these `D.Hyp`'s numbers suffice.)
  `Spec.stdLnB_one`: at N = 1 the one more number is `D.Hyp`'s own.
  `Spec.stdLnB_honest`: under the hypotheses of its statement, the closing stands behind every
    chain that ends where the core ends, for sets of slots (`OkFromV`); its annotations are coherent
    (`Coh`); nothing follows (`∀ Jn, (D.QV0 N).VT.q Jn fun _ => ∅`); its annotated links and its
    links are those of the sound side (`D.C.cZA D.QA D.T.fq`) and of one instance
    (`D.C.cZ D.T.Q D.T.fq`).
  `Spec.stdLnB_object_far`: the index code and P have a position (`Nonempty (Fin Cf.C₀.n)`,
    `Nonempty P`), the index code has its distance, e' + eM is below it, the places are distinct,
    `D.HypB`, a value of each of `D.T.St₁ × D.C.S.Smp` (x₀), `(D.C.E₀.prod D.C.S.ext).Str`,
    `D.C.P.Ea.Str` ⇒ `Hiop.LinBListR` ∧ `Hiop.LinBKnowR` of one term (Cb/Obj/LdObjectOnBTerm.lean:
    `O.termT`), in the regime in which the index decodes with its record (`D.O.onDec`).

Limits: this file does not say that `D.HypB` can be met.
The preamble leaves nothing. No splitting, so no masked link.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectOnBStd
import Cb.Ld.LdLinCloseVLinProofs
import Cb.Obj.LdObjectOnBTermProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace StdLn
variable {F E : Type} [Field F] [Field E] [Fintype E] [Algebra F E] {Cf : LdCf F E}
  [Nonempty (Fin Cf.C₀.n)] {P : Type} [Fintype P] [Nonempty P] (D : StdLn Cf P)

/-- the honest side of "nothing is left" -/
def QV0 (N : ℕ) :
    LdTcV N D.rest0 ⟨D.C.P.Sh6, fun _ _ _ _ => True, D.pl.qB₂ N (fun _ => True) fun _ => 0⟩ :=
  LdTcV.nil D.pl.S₂ D.C.E₀ D.C.Wpa (fun a => a.2.elim, ()) _

/-- The closing for a batch, with its honest side. -/
def cZV (N L tW tU tO : ℕ) (x₀ : D.T.St₁ × D.C.S.Smp) :
    ChainV Unit N (D.C.P.V6 (D.Sn L tW tU tO) (fun _ => True) N) (D.QV0 N).VT :=
  D.T.cZV N (fun _ => True) (fun _ => 0) (fun _ _ _ _ => True) D.rest0.cA D.rest0.same
    (D.Sn L tW tU tO) (fun _ => True) x₀ (D.QV0 N)

/-- The conditions for a batch. -/
structure HypB (N L tW tU tO : ℕ) : Prop where
  hyp  : D.Hyp L tW tU tO
  posO : D.tb₁ + N * D.tb₂ ≤ tO

end StdLn

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

def stdLnB_one : Prop :=
  ∀ (Cf : LdCf F E) (P : Type) [Fintype P] (D : StdLn Cf P) (L tW tU tO : ℕ),
    D.Hyp L tW tU tO → D.HypB 1 L tW tU tO

/-- The honest side of a batch. -/
def stdLnB_honest : Prop :=
  ∀ (Cf : LdCf F E) [Nonempty (Fin Cf.C₀.n)] (P : Type) [Fintype P] [Nonempty P] (D : StdLn Cf P)
      (N L tW tU tO : ℕ) (x₀ : D.T.St₁ × D.C.S.Smp) (_ : (D.C.E₀.prod D.C.S.ext).Str),
    D.HypB N L tW tU tO →
    (∀ (Z : Joint Unit) (VZ : JV N Z)
          (c₀ : ChainV Unit N VZ (D.C.P.V6 (D.Sn L tW tU tO) (fun _ => True) N)),
        (D.cZV N L tW tU tO x₀).OkFromV c₀) ∧
    (D.cZV N L tW tU tO x₀).forget.Coh ∧
    (∀ Jn, (D.QV0 N).VT.q Jn fun _ => ∅) ∧
    (D.cZV N L tW tU tO x₀).forget = D.C.cZA D.QA D.T.fq ∧
    (D.cZV N L tW tU tO x₀).forget.forget = D.C.cZ D.T.Q D.T.fq

/-- Both items of the object's list, for at most N instances. -/
def stdLnB_object_far : Prop :=
  ∀ (Cf : LdCf F E) [Nonempty (Fin Cf.C₀.n)] (P : Type) [Fintype P] [Nonempty P] (D : StdLn Cf P)
      (N L tW tU tO : ℕ) (x₀ : D.T.St₁ × D.C.S.Smp) (_ : (D.C.E₀.prod D.C.S.ext).Str) (d : D.C.P.W0)
      (d₀ : D.O.P.W0) (_ : D.C.P.Ea.Str) (d0 : D.O.left.AMsg),
    HasDist Cf.C₀.G Cf.C₀.d → D.e' + Cf.eM < Cf.C₀.d →
    Function.Injective D.py → D.HypB N L tW tU tO →
    LinBListR D.O.left
      (D.O.termT D.O.onDec (D.Sn L tW tU tO) (fun _ => True) 0 N (D.cZV N L tW tU tO x₀) d d₀).Q
      (D.O.termT D.O.onDec (D.Sn L tW tU tO) (fun _ => True) 0 N (D.cZV N L tW tU tO x₀) d d₀).hQ N
      (D.O.termT D.O.onDec (D.Sn L tW tU tO) (fun _ => True) 0 N (D.cZV N L tW tU tO x₀) d d₀).P ∧
    LinBKnowR D.O.left
      (D.O.termT D.O.onDec (D.Sn L tW tU tO) (fun _ => True) 0 N (D.cZV N L tW tU tO x₀) d d₀).Q
      N d0
      (D.O.termT D.O.onDec (D.Sn L tW tU tO) (fun _ => True) 0 N (D.cZV N L tW tU tO x₀) d d₀).P.err

end
end Spec

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

omit [Fintype F] in
theorem stdLnB_one : Spec.stdLnB_one F E := fun _ _ _ _ _ _ _ _ h =>
  ⟨h, by rw [Nat.one_mul]; exact h.pos.2.2⟩

omit [Fintype F] in
theorem stdLnB_honest : Spec.stdLnB_honest F E := by
  intro Cf _ P _ _ D N L tW tU tO x₀ y₀ h
  have hSh := stdLnB_shared F E Cf P D
  refine ldLinVL_all E _ _ _ _ D.C D.pl D.T N (fun _ => True) (fun _ => 0) (fun _ _ _ _ => True)
    D.rest0.cA D.rest0.same x₀ y₀ (D.QV0 N) (D.Sn L tW tU tO) (fun _ => True) (fun a => a.elim) hSh
    (fun _ _ => by simp [Slf.val])
    ⟨fun _ _ _ _ _ => trivial, fun _ _ _ _ _ _ => trivial, fun _ _ _ => trivial⟩ (stdLn_d1 h.hyp)
    (stdLn_d2 h.hyp) ?_ (fun _ _ _ _ => trivial) (fun _ _ => trivial) (fun a => a.elim)
    (fun a => ?_) (fun a => ?_) fun a => ?_
  · refine ldPlanV_nil E D.pl.S₂ D.C.E₀ D.C.Wpa (fun a => a.2.elim, ()) N _ fun Jn => ?_
    exact ldDemandV_empty E D.pl.S₂ D.C.E₀ N _ _ _ (fun _ _ => trivial) Jn
  · refine (ldDemandV_plan E _ _ _ _ D.C D.pl D.T N (fun _ => 0) _ 0 hSh fun _ _ =>
      le_refl 0).trans ?_
    show D.tb₂ + 0 ≤ tW
    have := h.hyp.pos.1
    omega
  · refine (ldDemandV_plan_first E _ _ _ _ D.C D.pl D.T N (fun _ => 0) _ 0
      (fun h₁ => absurd (by cases a; rfl) h₁) fun _ _ => le_refl 0).trans ?_
    show D.tb₁ + 0 ≤ tU
    have := h.hyp.pos.2.1
    omega
  · refine (ldDemandV_plan E _ _ _ _ D.C D.pl D.T N (fun _ => 0) _ 0 hSh fun _ _ =>
      le_refl 0).trans ?_
    show D.tb₁ + N * D.tb₂ + 0 ≤ tO
    exact h.posO

theorem stdLnB_object_far : Spec.stdLnB_object_far F E := by
  intro Cf _ P _ _ D N L tW tU tO x₀ y₀ d d₀ ya d0 hd he hpy h
  obtain ⟨h1, h2, h3, h4, h5⟩ := stdLnB_honest F E Cf P D N L tW tU tO x₀ y₀ h
  have hb := stdLnB_behind F E Cf P D L tW tU tO _ (D.C.P.chain D.O.onDec (D.Sn L tW tU tO) 0) h.hyp
  refine ldOnT_object_far F E D.O (D.Sn L tW tU tO) (fun _ => True) N _ (D.cZV N L tW tU tO x₀)
    ldKeyT d d₀ ya d0 hd he hpy (stdLn_snd D h.hyp.okW h.hyp.okU h.hyp.okO)
    (stdLnB_apart F E Cf P D L tW tU tO) (fun _ _ _ _ => trivial) ?_ ?_ ?_ (h1 _ _ _) h2 h3
  · have h6 := hb.1
    rw [← h5] at h6
    exact h6
  · have h6 := hb.2
    rw [← h5] at h6
    exact h6
  · have h6 := stdLnB_kb F E Cf P D L tW tU tO N h.hyp
    rw [← h4] at h6
    exact h6

end
end Cb
