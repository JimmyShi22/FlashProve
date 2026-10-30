-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectWfRest.lean: assembly of the holographic IOP from its sub-protocols: "restG is rest"
at the object: the mask part of the tensor row that weights-formedness leaves is a linear form on
named places, and so a form on the message of the plan's second group, under the hypotheses below.

Definitions (`LdLinPl.restOf`, `LdOWf.restF`) and statements; the proofs are in
Cb/Obj/LdObjectWfRestProofs.lean.
A form (`Slf E St J`, Cb/Ld/LdRel.lean) is a linear form on vectors with coordinates J whose
coefficients depend on a state. A group (`Grp`, Cb/Ld/LdBatSig.lean) is a set of whole oracle
messages; its message is its members' messages side by side.
The plan is the plan without a splitting, `LdLinPl` (Cb/Ld/LdLinClosePlan.lean: its field `restG`
and the hypothesis "restG is rest" of its theorems). The file also stands on
Cb/Ld/LdLinClosePlanRows.lean (`C.upA`), Cb/Ld/LdBatPeel.lean. `W.O.restM` (Cb/Obj/LdObjectWf.lean):
the two mask terms of the row that the batching of tensor rows leaves. `gC` (Cb/Ld/LdWf.lean):
public supports; every use reads a filed mask form cut to its support. A place is an entry of an
oracle message (`Sig.Ent`, Cb/Ld/LdBatSig.lean); `nAt n` is the place of the named entry n.

Main names:
  `Spec.ldRest_val`: the value of `p.restOf slA` on the second group's message is slA's value on the
    preamble's messages, if every oracle message at which slA has a non-zero coefficient is kept at
    the first bridge (`p.kp₁`) and is a member of the second group (`p.G₂`).
  `Spec.ldRest_is`: so, under the same condition, for a plan whose `restG` is `p.restOf slA` and a
    test whose "rest" is slA's value, restG is rest.
  `W.restF nAt`: the mask part as a form on all entries of the preamble's messages, with the claim
    as its state: the coefficients of the hiding polynomial's form, at the places of that
    polynomial's coefficients; plus eps · ∏ outPt · ∑_q chi_q · (the mask form filed for the claim
    q, cut to its public support `gC q`), at the places of the named entries.
  `Spec.ldOWfRest_val`: under `W.P.EntAt nAt` (Cb/Ld/LdWfMasksBatt.lean), its value on the messages
    is `W.O.restM`.
  `Spec.ldOWfRest_read`: at every state it is non-zero only at the place of a coefficient of the
    hiding polynomial, or at the place of a named entry in some `gC q`.
  `Spec.ldOWfRest_is`: "restG is rest" at `W.O.toC`, for a plan with
    `p.restG = p.restOf (W.restF nAt)`, from `EntAt` and a condition on places: the oracle messages
    of these places are kept at the first bridge and are members of the second group.

Limits: (1) The condition on places is that of this protocol's technical report (lean/CREDITS.md),
read for several oracle messages where the report has one (the instance's message of index masks
holds both kinds of masks and is a member of the instance's group); it is the case of one code in
that group.
(2) How much the condition asks depends on how fine `gC` is. With a finer support for the mask form
alone the statements here hold unchanged and ask less. As the preamble's blocks stand, `gC q` has to
hold two places, `K.cK q (K.v' q) b` (`LdWfP.Lks.OK.supC`, Cb/Ld/LdWfBlocks.lean).
This file does not say that a plan with the condition's places exists at any concrete preamble. It
says nothing on the online side but this: `LdLinPl.restOf`, `Spec.ldRest_val` and `Spec.ldRest_is`
take any test's data `C : LdLinC` and any plan `p : LdLinPl C` (used at the batch test's plan in the
proof of `ldObjR_hyp`, Cb/Obj/LdObjectPlanRows.lean); `W.restF` and `Spec.ldOWfRest_val`, `_read`,
`_is` are on `W : LdOWf` (Cb/Obj/LdObjectWf.lean) alone.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectWfRowsProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR Cb.LdLkp

/-- A form on the entries of what the preamble left, read on the message of the plan's second
group. -/
def LdLinPl.restOf {E ι κ J Y : Type} [Field E] {C : LdLinC E ι κ J Y}
    (p : LdLinPl C) (slA : Slf E C.Sta C.Sa.Ent) : Slf E C.Sta p.G₂.C.J :=
  ((C.upA slA).onSub p.kp₁).onG p.G₂

namespace LdOWf
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (W : LdOWf F E)

/-- The mask part of the tensor row, as a form on all entries of the preamble's messages. -/
def restF (nAt : W.P.N → W.P.S.Ent) : Slf E W.P.Cl W.P.S.Ent :=
  (Slf.push (fun i => nAt (W.P.wAt (pIx W.P.bt.fmt (pdPlains E W.P.bt.n W.P.bt.k) i)))
      fun (z : W.P.Cl) i => hSl (W.P.bt.par.vars z.st) (W.P.bt.par.hp z.st z.pt) i).plus
    (Slf.push nAt fun (z : W.P.Cl) n =>
      z.eps * (∏ i, W.P.bt.outPt z i) *
        ∑ q : Fin (W.P.n + 1), W.P.bt.chi z q * (W.P.clAt q (W.P.stOf z)).mf n)

end LdOWf

namespace Spec

/-- The value on the second group's message. -/
def ldRest_val : Prop :=
  ∀ (E ι κ J Y : Type) [Field E] (C : LdLinC E ι κ J Y)
      (p : LdLinPl C) (slA : Slf E C.Sta C.Sa.Ent),
    (∀ st (a : C.Sa.O) j, slA st ⟨a, j⟩ ≠ 0 → ∃ h : p.kp₁ (.inl (.inl (.inl a))), p.G₂.mem ⟨_, h⟩) →
    ∀ sa (m : C.S.Msg), (p.restOf slA).val sa (p.G₂.msg (C.S.res (T := OMsg.Msg) p.kp₁ m)) =
      slA.val sa (C.Sa.ents (C.aM m))

def ldRest_is : Prop :=
  ∀ (E ι κ J Y : Type) [Field E] (C : LdLinC E ι κ J Y)
      (p : LdLinPl C) (slA : Slf E C.Sta C.Sa.Ent),
    p.restG = p.restOf slA → (∀ sa ma, C.rest sa ma = slA.val sa (C.Sa.ents ma)) →
    (∀ st (a : C.Sa.O) j, slA st ⟨a, j⟩ ≠ 0 → ∃ h : p.kp₁ (.inl (.inl (.inl a))), p.G₂.mem ⟨_, h⟩) →
    ∀ sa m, p.restG.val sa (p.G₂.msg (C.S.res (T := OMsg.Msg) p.kp₁ m)) = C.rest sa (C.aM m)

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- States: under `EntAt`, the form's value is the mask part. -/
def ldOWfRest_val : Prop :=
  ∀ (W : LdOWf F E) (nAt : W.P.N → W.P.S.Ent), W.P.EntAt nAt →
    ∀ (cl : W.P.Cl) (m : W.P.S.Msg), (W.restF nAt).val cl (W.P.S.ents m) = W.O.restM cl m

/-- At every state it is non-zero only at public places. -/
def ldOWfRest_read : Prop :=
  ∀ (W : LdOWf F E) (nAt : W.P.N → W.P.S.Ent) (cl : W.P.Cl) (e : W.P.S.Ent), W.restF nAt cl e ≠ 0 →
    (∃ i, nAt (W.P.wAt (pIx W.P.bt.fmt (pdPlains E W.P.bt.n W.P.bt.k) i)) = e) ∨
    ∃ (q : Fin (W.P.n + 1)) (n : W.P.N), W.P.gC q n ∧ nAt n = e

/-- "restG is rest" at the object. -/
def ldOWfRest_is : Prop :=
  ∀ (W : LdOWf F E) (nAt : W.P.N → W.P.S.Ent) (p : LdLinPl W.O.toC), W.P.EntAt nAt →
    p.restG = p.restOf (W.restF nAt) →
    (∀ i, ∃ h : p.kp₁
          (.inl (.inl (.inl (nAt (W.P.wAt (pIx W.P.bt.fmt (pdPlains E W.P.bt.n W.P.bt.k) i))).1))),
        p.G₂.mem ⟨_, h⟩) →
    (∀ (q : Fin (W.P.n + 1)) n,
      W.P.gC q n → ∃ h : p.kp₁ (.inl (.inl (.inl (nAt n).1))), p.G₂.mem ⟨_, h⟩) →
    ∀ sa m, p.restG.val sa (p.G₂.msg (W.O.toC.S.res (T := OMsg.Msg) p.kp₁ m)) =
      W.O.toC.rest sa (W.O.toC.aM m)

end
end Spec
end Cb
