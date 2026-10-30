-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectOnBStd2.lean: for toys: the test for linear constraints on the encoded index with
standard parts, over a preamble that leaves a family of oracle messages, for at most N instances:
both items of the object's list, under the hypotheses of `Spec.std2B_object_far`.

The test for linear constraints is the interactive oracle proof of proximity (IOPP) for the
constraint relation; it follows a preamble (Hiop/RecSubs.lean, Hiop/RecBuild.lean).

Statements (`Cb.Spec.std2B_apart`, `Cb.Spec.std2B_mono`, `Cb.Spec.std2B_object_far`) and proofs. A
tool for guards against empty theorems; no parameter of a protocol.
It builds on Cb/Obj/LdObjectLinStd2.lean (`D : StdLn2 Cf P`: as the standard test, and the preamble
leaves a family `D.Sa`, which a third test closes) and Cb/Obj/LdObjectOnBStd2Close.lean (the
closing's half for a batch: `D.cZV`, `D.HypB` (conditions on codes, sample maps and numbers), the
six conditions on the closing). The analogue of Cb/Obj/LdObjectOnBStdV.lean, where the preamble
leaves nothing.

Main names:
  `Spec.std2B_apart`: the senders of the second and third family read the vector that they send,
    and nothing else of the witness.
  `Spec.std2B_mono`: the bound on what may be read of the oracles left (at most ba a long positions
    of the member a) is kept by subsets.
  `Spec.std2B_object_far`: the index code and P have a position (`Nonempty (Fin Cf.C₀.n)`,
    `Nonempty P`), the index code has its distance, e' + eM is below it, the places are distinct,
    `D.HypB N L tW tU tO ba`, a value of each of `D.T.St₁ × D.C.S.Smp` (x₀),
    `(D.C.E₀.prod D.C.S.ext).Str`, `D.C.P.Ea.Str` ⇒ `Hiop.LinBListR` ∧ `Hiop.LinBKnowR` of one term
    (Cb/Obj/LdObjectOnBTerm.lean: `O.termT`), in the regime in which the index decodes with its
    record (`D.O.onDec`). The bound on the oracles left is kept (it is not "anything").

Limits: this file does not say that `D.HypB` can be met. No splitting, so no masked link.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectOnBStd2Close
import Cb.Obj.LdObjectOnBTermProofs
import Cb.Ld.LdLinChainFresh

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

def std2B_apart : Prop :=
  ∀ (Cf : LdCf F E) (P : Type) [Fintype P] (D : StdLn2 Cf P) (L tW tU tO : ℕ),
    (D.Sn L tW tU tO).Apart

def std2B_mono : Prop :=
  ∀ (N : Sig E) (E₀ : ExtSpec) (t : N.O → ℕ) (U V : Finset (E₀.prod N.ext).Pos),
    V ⊆ U → N.qFam (fun _ => True) t U → N.qFam (fun _ => True) t V

/-- Both items of the object's list, for at most N instances. -/
def std2B_object_far : Prop :=
  ∀ (Cf : LdCf F E) [Nonempty (Fin Cf.C₀.n)] (P : Type) [Fintype P] [Nonempty P]
      (D : StdLn2 Cf P) (N L tW tU tO : ℕ) (ba : D.Sa.O → ℕ) (x₀ : D.T.St₁ × D.C.S.Smp)
      (_ : (D.C.E₀.prod D.C.S.ext).Str) (d : D.C.P.W0) (d₀ : D.O.P.W0)
      (_ : D.C.P.Ea.Str) (d0 : D.O.left.AMsg),
    HasDist Cf.C₀.G Cf.C₀.d → D.e' + Cf.eM < Cf.C₀.d →
    Function.Injective D.py → D.HypB N L tW tU tO ba →
    LinBListR D.O.left
      (D.O.termT D.O.onDec (D.Sn L tW tU tO) (D.Sa.qFam (E₀ := extNone) (fun _ => True) ba) 0 N
        (D.cZV N L tW tU tO ba x₀) d d₀).Q
      (D.O.termT D.O.onDec (D.Sn L tW tU tO) (D.Sa.qFam (E₀ := extNone) (fun _ => True) ba) 0 N
        (D.cZV N L tW tU tO ba x₀) d d₀).hQ
      N (D.O.termT D.O.onDec (D.Sn L tW tU tO) (D.Sa.qFam (E₀ := extNone) (fun _ => True) ba) 0 N
        (D.cZV N L tW tU tO ba x₀) d d₀).P ∧
    LinBKnowR D.O.left
      (D.O.termT D.O.onDec (D.Sn L tW tU tO) (D.Sa.qFam (E₀ := extNone) (fun _ => True) ba) 0 N
        (D.cZV N L tW tU tO ba x₀) d d₀).Q
      N d0 (D.O.termT D.O.onDec (D.Sn L tW tU tO) (D.Sa.qFam (E₀ := extNone) (fun _ => True) ba) 0 N
        (D.cZV N L tW tU tO ba x₀) d d₀).P.err

end
end Spec

theorem std2B_mono (E : Type) : Spec.std2B_mono E := fun _ _ _ _ _ hVU h =>
  ⟨trivial, fun a => (cnt_mono fun _ hx => hVU hx).trans (h.2 a)⟩

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

omit [Fintype F] in
theorem std2B_apart : Spec.std2B_apart F E := by
  intro Cf P _ D L tW tU tO
  refine ⟨fun w w' k h => funext fun a => funext fun j => ?_,
    fun w w' k h => funext fun a => funext fun j => ?_⟩
  · show Sum.elim (D.datU w') (fun _ => k a) (D.MU.place.symm j) =
      Sum.elim (D.datU w) (fun _ => k a) (D.MU.place.symm j)
    unfold StdLn2.datU
    rw [h]
  · show Sum.elim (D.datO w') (fun _ => k a) (D.MO.place.symm j) =
      Sum.elim (D.datO w) (fun _ => k a) (D.MO.place.symm j)
    unfold StdLn2.datO
    rw [h]

theorem std2B_object_far : Spec.std2B_object_far F E := by
  intro Cf _ P _ _ D N L tW tU tO ba x₀ y₀ d d₀ ya d0 hd he hpy h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := std2B_close F E Cf P D N L tW tU tO ba x₀ y₀ h
  exact ldOnT_object_far F E D.O (D.Sn L tW tU tO) (D.Sa.qFam (E₀ := extNone) (fun _ => True) ba)
    N _ (D.cZV N L tW tU tO ba x₀) ldKeyT d d₀ ya d0 hd he hpy
    (std2_snd D h.hyp.okW h.hyp.okU h.hyp.okO) (std2B_apart F E Cf P D L tW tU tO)
    (std2B_mono E D.Sa extNone ba) (h1 _ _) h2 h3 (h4 _ _ _) h5 h6

end
end Cb
