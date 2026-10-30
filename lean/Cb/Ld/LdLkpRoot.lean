-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpRoot.lean: the point of a forest: claims on the products of all trees into the sum claim
of level 0.
This file is about one step of a product argument: claims on the products of 2^g trees are combined,
at a point that the verifier draws, into one sumcheck claim.

Definitions and statements (the statements in `Cb.Spec`). Proofs: Cb/Ld/LdLkpRootProofs.lean.
A forest of 2^g product trees (Cb/Ld/LdLkpTreeP.lean: `D : TreeP E`; the first g coordinates name
the tree; level 0 holds the products under `D.Step`, a hypothesis, not a field). The claims, one
for each tree θ: (level 0 at θ, `D.U st m 0 θ`: under `D.Step` the product of the tree θ) + <
form_θ, entries > = tgt_θ, with a public target; the form reads masks
(by type any form on the entries `D.J`: no statement here asks that it reads masks).
Forms and targets are read off the state (parameters `form`, `tgt`): whoever has stated the claims
has put them there (a sumcheck's rows on values: the form is a challenge at an inner mask's entry,
the target the value sent; a tree of which the product is claimed in the clear: the form 0).
The step. The prover sends nothing. The verifier sends a point ϱ of g coordinates, from all of E^g,
in a round of its own. The new claim is the sum claim of the sumcheck of level 0 (`D.T0`) at the
state (state, ϱ), with the target ∑_θ eq(ϱ, θ) tgt_θ; the incoming form of level 0 is no part of the
state: it is the forest's reader `D.inc0` of (state, ϱ), which is asked to be ∑_θ eq(ϱ, θ) form_θ
(`R.IncOK`, a hypothesis of the statements, not a field). Under `D.Step` (`Spec.ldLkpP_sum`,
Cb/Ld/LdLkpTreeP.lean) and `R.IncOK` the new claim says:
   (multilinear extension of level 0 at ϱ) + < combined form, entries > = combined target.
It is an instance of the step into a sumcheck of Cb/Ld/LdZero.lean (`PscIn`), with the equality
kernel at a point as evader.

Main names:
  `Spec.ldLkpRoot_link` (under `D.Step` and `R.IncOK`), `Spec.ldLkpRoot_back`, `Spec.ldLkpRoot_ok`:
    the conditions of the step (`PscIn.Link`, `PscIn.Back`, Cb/Ld/LdZero.lean; `Evader.OK`,
    Cb/Gen/BatEvader.lean).
  `Spec.ldLkpRoot_err`: the bound on the number of bad points (`ev.err`): g |E|^(g-1) of |E|^g.
  `Spec.ldLkpRoot_jt`: the output joint is the tree's joint at level 0, with what rode along read at
    the old state.
  `Spec.ldLkpRoot_good`: under `D.Step` and `R.IncOK`, the block at the base `R.rootA` is `Good`
    (`BkA.Good`, Cb/Ld/LdLkpTreeP.lean: `GoodAt` of Cb/Ld/LdSigLift.lean, the identity extracts)
    from the joint (all claims, and R0) to the joint `D.jtAt .. 0`, for any type of tuples:
    perfectly complete, knowledge sound for each fixed tuple with that one error (`ev.err`).
  `Spec.ldLkpRoot_exact`: nothing to simulate.
With g = 0 there is one tree, the point is empty, and no value of the verifier's message is bad: the
step only re-writes the claim, at the price of a round with a verifier message that has one value.
(Without a round: Cb/Ld/LdSigStep.lean.)

Limits: this file does not say who states the claims on the products.
The text that we follow has no round of its own for this point in its counts.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpTreeP

set_option autoImplicit false

namespace Cb.LdLkp
open Iop IOR Hiop Prob

noncomputable section

/-- The parameters: a forest; forms and targets of the claims on its products, read off the
state. -/
structure RootP (E : Type) [Field E] [Fintype E] where
  D : TreeP E
  form : D.St0 → (Fin (D.g + 0) → Bool) → D.J → E
  tgt : D.St0 → (Fin (D.g + 0) → Bool) → E

namespace RootP
variable {E : Type} [Field E] [Fintype E] (R : RootP E)

/-- Beside `D.Step`, the one condition on the parameters: the forest's incoming form at level 0 is
the combination of the forms, with the equality weights at the point. -/
def IncOK : Prop := ∀ st ϱ j, R.D.inc0 st ϱ j = ∑ θ, Alg.eqk ϱ θ * R.form st θ j

/-- The claims: for every tree θ, `D.U st m 0 θ` (under `D.Step` the product of the tree) + form =
target. -/
def Holds (st : R.D.St0) (m : R.D.J → E) : Prop :=
  ∀ θ, R.D.U st m 0 θ + ∑ j, R.form st θ j * m j = R.tgt st θ

/-- The step into the sumcheck of level 0. -/
def toIn : PscIn E where
  T := R.D.T0
  St0 := R.D.St0
  I := Fin (R.D.g + 0) → Bool
  ev := Evader.eqPt E (Fin (R.D.g + 0))
  val := fun st m θ => R.D.U st m 0 θ + ∑ j, R.form st θ j * m j
  tg := R.tgt
  nx := fun st ϱ => (st, ϱ)
  old := fun s => s.1

/-- The block at the base. -/
def rootA (Ex : ExtSpec) (M Wp Kc : Type) : BkA Kc M R.D.St0 (E × (R.D.lv 0).T.St) Ex Wp :=
  ⟨IOR.draw R.toIn.ev.D R.toIn.nxX Ex,
    Honest.draw R.toIn.ev.D R.toIn.nxX Ex (M × Wp),
    Nums.draw Kc R.toIn.ev.D R.toIn.nxX Ex R.toIn.ev.err⟩

end RootP
end
end Cb.LdLkp

namespace Cb.Spec
open Iop IOR Hiop Prob Cb.LdLkp
variable (E : Type) [Field E] [Fintype E]

def ldLkpRoot_link : Prop := ∀ R : RootP E, R.D.Step → R.IncOK → R.toIn.Link
def ldLkpRoot_back : Prop := ∀ R : RootP E, R.toIn.Back
def ldLkpRoot_ok : Prop := ∀ R : RootP E, R.toIn.ev.OK
def ldLkpRoot_err : Prop := ∀ R : RootP E, R.toIn.ev.err = R.D.g * Fintype.card E ^ (R.D.g - 1)

/-- The output joint is the tree's joint at level 0, with what rode along read at the old state. -/
def ldLkpRoot_jt : Prop :=
  ∀ (R : RootP E) (Ex : ExtSpec) (M Wp Kc : Type)
      (R0 : Rels Kc R.D.St0 Ex (M × Wp)) (msg : M → R.D.J → E),
    R.toIn.relsOut R0 msg = R.D.jtAt msg (R.toIn.ride R0) 0

/-- The point of a forest, at the base. -/
def ldLkpRoot_good : Prop :=
  ∀ (R : RootP E) (Ex : ExtSpec) (M Wp Kc : Type)
      (R0 : Rels Kc R.D.St0 Ex (M × Wp)) (msg : M → R.D.J → E),
    R.D.Step → R.IncOK →
    (R.rootA Ex M Wp Kc).Good
      ⟨fun st y w => R0.rel st y w ∧ R.Holds st (msg w.1),
        fun a w => R0.relR a w ∧ R.Holds a.1 (msg w.1),
        R0.on, R0.core⟩
      (R.D.jtAt msg (R.toIn.ride R0) 0)

def ldLkpRoot_exact : Prop :=
  ∀ (R : RootP E) (Ex : ExtSpec) (M Wp Kc : Type) (P : R.D.St0 → Ex.Str → M × Wp → Prop),
    (R.rootA Ex M Wp Kc).H.Exact P fun _ _ => True

end Cb.Spec
