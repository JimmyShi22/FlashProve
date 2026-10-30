-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpSuppFine.lean: the mask form of the lookup's claim on the keys reads two entries only.
This file is about the support of one linear form: at which entries of the oracle messages the mask
form in a lookup argument's output claim can have a coefficient other than 0.

A definition, statements (in `Cb.Spec`) and proofs.
Cb/Ld/LdLkpSupp.lean states (proofs: Cb/Ld/LdLkpSuppProofs.lean) that rows and mask form of the
assembled lookup's (`LkAsm`, Cb/Ld/LdLkpAsm.lean) output are 0 outside all named places (the bits of
the multiplicities, the own masks of all blocks). For the rows that is what there is to say. The
mask form reads much less: it is, up to the sign, the incoming form of the claim at the top of the
keys' tree, which the last line step (Cb/Ld/LdLine.lean) has made of the two value rows of the last
sumcheck of that tree: so it reads the two inner masks (`TreeP.cAt`, Cb/Ld/LdLkpTreeP.lean) of that
sumcheck and nothing else; no bit, no coefficient of a hiding polynomial (that the named places are
pairwise different is not said: Limits, Cb/Ld/LdLkpSupp.lean).

Main names:
  `A.FormIn G`: G holds of the two places A.cK A.v' false, A.cK A.v' true. A condition on G, none on
    A.
  `tree_slS_succ`: for any product tree: the incoming form of level l + 1 is 0 outside the two inner
    masks of level l.
  `Spec.ldLkpSuppF_form`: `A.FormIn G` ⇒ at every last explicit part the mask form is 0 outside G.
  `Spec.ldLkpSuppF_pull`: so, pulled back along an injective naming whose range holds these two
    places, the masked claim says the same.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpSuppProofs

set_option autoImplicit false

namespace Cb.LdLkp

/-- G holds of the two inner masks of the last sumcheck of the keys' tree. -/
def LkAsm.FormIn {E : Type} [Field E] [Fintype E] (A : LkAsm E) (G : A.J → Prop) : Prop :=
  ∀ b, G (A.cK A.v' b)

end Cb.LdLkp

namespace Cb.Spec
open Cb.LdLkp
variable (E : Type) [Field E] [Fintype E]

def ldLkpSuppF_form : Prop :=
  ∀ (A : LkAsm E) (G : A.J → Prop), A.FormIn G → ∀ o, SuppIn G (A.rd o).2.1.mf

def ldLkpSuppF_pull : Prop :=
  ∀ (A : LkAsm E) (N : Type) [Fintype N] (ι : N → A.J), Function.Injective ι →
    A.FormIn (fun j => j ∈ Set.range ι) →
    ∀ (o : A.Q.XB) (k : ℕ) (f : ℕ → E) (m : A.J → E),
      ((A.rd o).2.1.pull ι).Holds k f (fun n => m (ι n)) ↔ (A.rd o).2.1.Holds k f m

end Cb.Spec

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp

section
variable {E : Type} [Field E] [Fintype E]

theorem tree_cAt_at (D : TreeP E) (G : D.J → Prop) :
    ∀ l, (∀ b, G (D.cAt l b)) → ∀ b, G ((D.lv l).toJ ((D.lv l).T.cAt ((D.lv l).two b)))
  | 0, h, b => h b
  | _ + 1, h, b => h b

/-- the incoming form of level l + 1 is 0 outside the two inner masks of level l -/
theorem tree_slS_succ (D : TreeP E) (G : D.J → Prop) (l : ℕ)
    (hc : ∀ b, G (D.cAt l b)) (s : (D.lv (l + 1)).T.St) :
    SuppIn (fun j => G ((D.lv (l + 1)).toJ j)) ((D.lv (l + 1)).T.slS s) := by
  classical
  intro j hj
  show (D.lv l).T.lst s.1.st ((D.lv l).T.par.hp s.1.st s.1.pt) *
      ((if j = (D.lv l).toJ ((D.lv l).T.cAt ((D.lv l).two false)) then 1 - s.2 else 0) +
        if j = (D.lv l).toJ ((D.lv l).T.cAt ((D.lv l).two true)) then s.2 else 0) = 0
  have h1 : j ≠ (D.lv l).toJ ((D.lv l).T.cAt ((D.lv l).two false)) := fun e =>
    hj (e ▸ tree_cAt_at D G l hc false)
  have h2 : j ≠ (D.lv l).toJ ((D.lv l).T.cAt ((D.lv l).two true)) := fun e =>
    hj (e ▸ tree_cAt_at D G l hc true)
  rw [if_neg h1, if_neg h2]
  simp

end

section
variable (E : Type) [Field E] [Fintype E]

theorem ldLkpSuppF_form : Spec.ldLkpSuppF_form E := by
  intro A G h o j hj
  show - pushJ ((A.IK.setV (A.v' + 1)).DK.lv (A.v' + 1)).toJ
        (((A.IK.setV (A.v' + 1)).DK.lv (A.v' + 1)).T.slS (A.Q.oldT o).2) j = 0
  exact neg_eq_zero.2
    (supp_pushJ _ _ G (tree_slS_succ (A.IK.setV (A.v' + 1)).DK G A.v' h (A.Q.oldT o).2) j hj)

theorem ldLkpSuppF_pull : Spec.ldLkpSuppF_pull E := fun A N _ ι hι h o k f m =>
  ldLkpSupp_cl_pull E A.J N ι hι _ (ldLkpSuppF_form E A _ h o) k f m

end
end Cb
