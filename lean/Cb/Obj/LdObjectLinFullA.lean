-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectLinFullA.lean: the test for linear constraints over the configuration, with a closing
that is in order only behind the test's core: a tail, under the hypotheses of the two statements.

The test for linear constraints is the interactive oracle proof of proximity (IOPP) for the
constraint relation. This file states and proves two statements of Cb/Obj/LdObjectLinFull.lean
anew under a weaker hypothesis on the test's last part, the closing.

Statements (`Cb.Spec.ldOLF_tailA`, `Cb.Spec.ldOLF_tailFA`) and proofs. They are the analogues of
`ldOLF_tail`, `ldOLF_tailF` (Cb/Obj/LdObjectLinFull.lean) for a weaker premise on the closing.

Why: Cb/Obj/LdObjectLinFull.lean's `ldOLF_tail`, `ldOLF_tailF` require of the closing Qt that it is
in order by itself (`Qt.OK`: every link has the whole bundle). A closing that holds a splitting is
not: a splitting is a masked block, honest-verifier zero knowledge only behind the rounds that sent
its mask. The closing of this protocol's technical report (lean/CREDITS.md) holds one
(Cb/Ld/LdLinClosePlanP.lean,
Cb/Ld/LdLinCloseDemandPA.lean: `T.QF`).

Main names:
  `Spec.ldOLF_tailA`, `Spec.ldOLF_tailFA`: the same conclusions, word for word, from `Qt.OkBehind`
    (the core's chain, then the step without rounds) (Cb/Ld/LdLinCloseAlt.lean) in the place of
    `Qt.OK`; the other premises are the same.
    The hypothesis is weaker: a closing that is in order by itself is in order behind every chain
    (`ldAlt_of_ok`).
    Used by the object's record: the clause `plan` of `LdObjT.Hyp` has this form (the head of
    Cb/Obj/LdObjectTerms.lean), and Cb/Obj/LdObjectTermsProofs.lean rests on `ldOLF_tailFA`.

Limits: this file says nothing on the two items of the object's list with such a closing (the twins
of `ldOLF_items`, `ldOLF_lin`).

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectLinFullProofs
import Cb.Ld.LdLinCloseDemandTProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

open Classical in
def ldOLF_tailA : Prop :=
  ∀ (O : LdOL F E) [Nonempty (Fin O.Cf.C₀.n)] (εf : ℕ) (Sn : O.toC.P.Snd)
      (qa : Finset O.toC.P.Ea.Pos → Prop) (Qt : LdTc O.toC.S O.toC.E₀ O.toC.Wpa)
      (fq : O.toC.St6 → Qt.St) (d : O.toC.P.W0) (d₀ : O.P.W0),
    O.toC.P.FoldErr O.on0 εf → Function.Injective O.py → Sn.OK → O.toC.Says Qt.base fq →
    Qt.OkBehind ((O.toC.P.chain O.on0 Sn εf).append (O.toC.chain fq Qt.base)) →
    (∀ V, Qt.q V → O.toC.P.q5 Sn qa (V.biUnion O.toC.toE.src)) →
    TailTr (O.full Sn εf Qt fq d) (O.hFull0 Sn εf Qt fq d) (O.P.j0 O.on0) trivRels
      (O.extF Sn εf Qt fq d d₀) (O.numsF0 Sn εf Qt fq d) (O.P.q0 (O.qaIn qa))

open Classical in
def ldOLF_tailFA : Prop :=
  ∀ (O : LdOL F E) [Nonempty (Fin O.Cf.C₀.n)] (εf : ℕ) (Sn : O.toC.P.Snd)
      (q₀ : Finset extNone.Pos → Prop) (b : O.S.O → ℕ) (Qt : LdTc O.toC.S O.toC.E₀ O.toC.Wpa)
      (fq : O.toC.St6 → Qt.St) (d : O.toC.P.W0) (d₀ : O.P.W0),
    q₀ ∅ → O.toC.P.FoldErr O.on0 εf → Function.Injective O.py → Sn.OK → O.toC.Says Qt.base fq →
    Qt.OkBehind ((O.toC.P.chain O.on0 Sn εf).append (O.toC.chain fq Qt.base)) →
    (∀ V, Qt.q V → O.toC.P.q5 Sn (O.S.qFam (E₀ := extNone) q₀ b) (V.biUnion O.toC.toE.src)) →
    TailTr (O.full Sn εf Qt fq d) (O.hFull0 Sn εf Qt fq d) (O.P.j0 O.on0) trivRels
      (O.extF Sn εf Qt fq d d₀) (O.numsF0 Sn εf Qt fq d)
      (O.S.qFam (E₀ := O.P.ix) (fun V => V.card ≤ O.t) b)

end
end Spec

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

open Classical in
theorem ldOLF_tailA : Spec.ldOLF_tailA F E := by
  intro O _ εf Sn qa Qt fq d d₀ hF hpy hS hSays hQ hq
  exact tailTr_cons Unit _ _ _ _ _ O.enter (O.lkC Sn εf Qt fq d).R _ _ _ O.hEnter
    (O.lkC Sn εf Qt fq d).H _ _ _ _ _ d₀ _ _ _ _ (ldOLF_enter F E O qa)
    (ldLinAlt_tail _ _ _ _ _ O.toC O.on0 εf Sn qa d Qt fq hF hpy hS hSays hQ hq)

open Classical in
theorem ldOLF_tailFA : Spec.ldOLF_tailFA F E := by
  intro O _ εf Sn q₀ b Qt fq d d₀ h0 hF hpy hS hSays hQ hq
  exact tailTr_mono _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (ldOLF_tailA F E O εf Sn _ Qt fq d d₀ hF hpy hS hSays hQ hq)
    fun U hU => (ldOLF_qFam F E O q₀ b U h0).1 hU

end
end Cb
