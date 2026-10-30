-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdWfEndThird.lean: the properties asked of the preamble, the reduction from the claim that the
encoded index is well-formed to the claims of the test for linear constraints (`PreListR`,
`PreKnowR`: Hiop/RecSubs.lean; `IOR.Side`: Ior/KnowCollPiece.lean), when every radius is within a
third of the distance. (not all hypotheses are named here: see the statements below)

A parameter list is what is asked of one sub-protocol, in two parts: a record of all items but
round-by-round knowledge soundness (`PreListR`, Hiop/RecSubs.lean), and that item, which is a
definition of its own (`PreKnowR`, Hiop/RecSubs.lean). `Spec.ldWfEnd3` concludes both, under the
hypotheses of its statement (`PreKnowR`: on the statements without a collision, `Z.W.Cf.conf.free`,
and at the errors `Z.G.B.nums.err`, which this file does not evaluate).

`noHid`: the set `H.Hid w x` is empty for all w and x. `noTie`: the set `R.tie ρ p` is empty for all
ρ and p. `R.Bears bud qi qo`: for every ρ and every set U of positions of the new implicit instance
for which qo holds, `bud ρ` holds of the positions `R.srcO ρ q` for q in U, and qi holds of
`R.need ρ U`. Here `Side` (Ior/KnowCollPiece.lean), the conclusion of `Spec.ldWfEnd3_side`, has the
three fields `noHid`, `noTie` and `bears : R.Bears bud qi qo`. (`Bears`, `need`: Ior/Bears.lean)

A definition, statements (in `Cb.Spec`) and proofs.
Of the conditions of Cb/Ld/LdWfEnd.lean (`Z.OK p Lc`) three speak of lists: `conf` (inside it: the
lists of the encoded index at its radius of decoding), `list` and `evades` (the oracle messages that
the preamble sends).

Main names:
  `Z.Third p dS`: `Z.Rest p` (all other clauses, as they stand there), and: the configuration within
    a third (Cb/Obj/LdObjectThirdTests.lean: `Cf.Third`: code, distance, 3 eM below it, sample map,
    model); L a = 1; each oracle message a has distance at least dS a as read (`LdCode.Dist`,
    Cb/Ld/LdRel.lean), and 3 e a < dS a.
    `Z.Third p dS` has no hypothesis on a block (as `item`, `claim` of `LdWfF.OK` are:
    Cb/Ld/LdWfFull.lean) but for six on the sender, no clause on a list (but for `one`: the bound
    L a = 1), none on agreement.
  `Spec.ldWfEnd3_ok`: `Z.Third p dS` gives `Z.OK p 1` (lists of at most one member:
    Cb/Ld/LdWfThird.lean, Cb/Obj/LdObjectThirdTests.lean).
  `Spec.ldWfEnd3`: under `Z.Third p dS`, if p is the characteristic of E (`CharP E p`), the two
    items of the object (`PreListR`, `PreKnowR`) hold.
  `Spec.ldWfEnd3_side`: under the same two, the budgets' half (`Side`) holds.
  `Spec.ldWfEnd3_err`: under `Z.Third p dS`: the sending's error is 0.

Limits: `Z.Rest p` has the six clauses on the sender `Z.D` (Cb/Ld/LdWfEnd.lean: `Rest0`, `Rest1`).
This file does not say that `Z.Third` can be met. It says nothing
beyond a third. Below the Johnson radius: see Cb/Obj/LdObjectJohnTests.lean (`Z.John`).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdWfEnd
import Cb.Ld.LdWfThird
import Cb.Obj.LdObjectThirdTestsProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.LdLkp

/-- The conditions within a third of the distances. -/
structure LdWfE.Third {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]
    (Z : LdWfE F E) (p : ℕ) (dS : Z.W.P.S.O → ℕ) : Prop extends Z.Rest p where
  conf3 : Z.W.Cf.Third
  one   : ∀ a, Z.L a = 1
  dist  : ∀ a, (Z.W.P.S.om a).C.Dist (dS a)
  lt    : ∀ a, 3 * (Z.W.P.S.om a).e < dS a

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

def ldWfEnd3_ok : Prop := ∀ (Z : LdWfE F E) (p : ℕ) (dS : Z.W.P.S.O → ℕ), Z.Third p dS → Z.OK p 1

def ldWfEnd3 : Prop :=
  ∀ (p : ℕ) [CharP E p] (Z : LdWfE F E) (dS : Z.W.P.S.O → ℕ), Z.Third p dS →
    PreListR Z.W.O.left Z.G.B.wf Z.G.B.hWf id id Z.W.Cf.conf.Rwf Z.G.B.nums ∧
    PreKnowR Z.W.O.left Z.G.B.wf Z.W.Cf.conf.free Z.W.Cf.conf.RwfR (fun _ _ _ => ()) Z.G.B.nums.err

def ldWfEnd3_side : Prop :=
  ∀ (p : ℕ) [CharP E p] (Z : LdWfE F E) (dS : Z.W.P.S.O → ℕ) (q : Finset Z.W.Cf.conf.E0.Pos → Prop),
    Z.Third p dS → Side Z.G.B.wf Z.G.B.hWf Z.G.B.nums.bud q (Z.W.P.S.qFam q Z.t)

def ldWfEnd3_err : Prop :=
  ∀ (Z : LdWfE F E) (p : ℕ) (dS : Z.W.P.S.O → ℕ),
    Z.Third p dS → ldSendFamErr Z.W.P.S Z.W.P.Sd Z.L = 0

end
end Spec

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem ldWfEnd3_ok : Spec.ldWfEnd3_ok F E := by
  intro Z p dS h
  have hl : ∀ a, (Z.W.P.S.om a).ListLE 1 := fun a =>
    ldWfThird_list (Z.W.P.S.om a) (dS a) (h.laws a) (h.dist a) (by have := h.lt a; omega)
  exact
    { toRest := h.toRest
      conf := ldT3_conf F E Z.W.Cf h.conf3
      list := fun a => by rw [h.one a]; exact hl a
      evades := fun a => ldWfThird_evades (Z.W.P.S.om a) (hl a) }

theorem ldWfEnd3 : Spec.ldWfEnd3 F E := fun p _ Z dS h => ldWfEnd p Z 1 (ldWfEnd3_ok Z p dS h)

theorem ldWfEnd3_side : Spec.ldWfEnd3_side F E := fun p _ Z dS q h =>
  ldWfEnd_side p Z 1 q (ldWfEnd3_ok Z p dS h)

theorem ldWfEnd3_err : Spec.ldWfEnd3_err F E := fun Z p dS h => by
  have e : Z.L = fun _ => 1 := funext h.one
  rw [e]
  exact ldWfThird_err Z.W.P.S Z.W.P.Sd

end
end Cb
