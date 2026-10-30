-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Part/LdPartHead.lean: one reduction without rounds in the chain of reductions for a request: the
step between the prover's first oracle messages and segment 0.

The preamble of a request (the sub-protocol before the test for linear constraints) is a chain of
interactive oracle reductions, which Cb/Part/ assembles from a partition of the model's conditions
into segments. This file states what is asked of that one step ("the model's one step"): from the
request's relation, read back off the messages just sent, to the entry relation of segment 0. What
is asked of the condition and of the way back (`on`, `bw`) is asked under the premise that the
form's test has passed.
Definitions and one statement (`Cb.Spec.ldPartHead_step`); the proof is in
Cb/Part/LdPartHeadProofs.lean. For arbitrary parameters: no sending occurs; what is used of it is a
record of ties.
The head of a request is the form's test, then the model's step
from the stage after the first sending to "all segments' conditions". The request is built over the
configuration `P.cfB K Bt` (Cb/Part/LdPartCf.lean), whose witness holds the data of all segments as
they will be sent; after the first sending its relation reads layer 0 back off the messages. So the
step is an unfolding: neither "admit" nor "force" of the partition is used.
`StepWOK` (Cb/Ld/LdStepW.lean) is what is asked of a reduction without interaction from a relation
A to a relation A' (two joints): it maps witnesses of the exact relation forward (`fw`, "forth":
completeness), keeps the condition (`on`) and the core, and, where the condition holds, maps
witnesses of the relaxed A' back to witnesses of the relaxed A (`bw`, "the way back": knowledge
soundness). A joint (`IOR.Rels`; with its types, `IOR.Joint`) consists of, for one kind of
statement and of witness: the honest relation; a second relation, called relaxed, of which
round-by-round knowledge soundness speaks; the set of statements of which that soundness speaks;
and a map from a witness to its core. The fields of `IOR.Rels`, in this order: `rel`, `relR`, `on`,
`core` (Ior/Chain.lean). The entry relation of segment k is `P.entry K k ..`
(Cb/Part/LdPartNext.lean), for a partition `P : LdPartD Cf` with its laws `P.Props p`
(Cb/Part/LdPartDef.lean); "index decoded" is `idxAt` (Cb/Ld/LdWfIdx.lean); the request's first
joint is `ldReqRels` (Cb/Obj/LdObjectReq.lean).

Main names:
  `ldPartFirst A ov`: a relation A on the request's witness (prover encoded index, (data, ghost
    (`LdPartGh`, Cb/Part/LdPartRide.lean))), read after the first sending: at the witness with its
    data overwritten by ov of the messages (layer 0 alone, by the ties `ovPk`, `ovBit`).
  `LdPartTie0`: the ties between the reading O' of the messages after the first sending and the
    overwriting ov: those of `LdPartTie` (Cb/Part/LdPartNext.lean), without kept messages.
  `StepWOKg S A A' ok f up dn`: what is asked of a step without a round whose verifier rejects
    unless ok holds of the explicit part: forth; ok holds on the exact relation; the condition and
    the way back under the premise ok; the core is kept (no premise).
  `Spec.ldPartHead_step`: `P.Props p`, the model's conditions on the configuration's data
    (`Cf.ModelOK`; used of it: `held`, an index's body holds it), the ties, a map f of states that
    keeps instance and record ⇒ `StepWOKg` from `ldPartFirst` (the request's first joint at
    `P.cfB`) to (index decoded; entry 0 at O'), with ok := the form of the request; the further
    witness is not touched, no message is read by the step's maps.

Why the premise: the relaxed relation of a request holds the form of the request (in this protocol's
technical report (lean/CREDITS.md) too, by inspection). Were `StepWOK` asked of the model's step at
all states, also where the test fails, its way back would there have to produce the form from
nothing. How the request's term asks the step is not this file's matter.



Limits: the model's duty of the technical report is not in this step. That duty: the constraints
hold exactly if all segments' predicates hold, with the bounds on cells. It stands between `P.cfB`
and the configuration that a user means: Cb/Part/LdPartCf.lean (`Spec.ldPartCf_yes`,
`Spec.ldPartCf_no`, from the partition's admit and force).
This file does not say that the ties hold, or that the stage behind the first sending is
`ldPartFirst (..)`. Nothing on masks.
Terms: lean/GLOSSARY.md.
-/
import Cb.Part.LdPartNext
import Cb.Part.LdPartCf
import Cb.Obj.LdObjectReq

set_option autoImplicit false

namespace Cb

open Iop Prob Hiop Blocks Finset Cb.RngPk IOR

/-- A relation on the request's witness, read after the first sending. -/
def ldPartFirst {E Kc St Pi : Type} [Field E] {E₀ : ExtSpec} {S' : Sig E}
    (A : Rels Kc St E₀ (Pi × (LdPartW E × LdPartGh))) (ov : S'.Msg → LdPartW E → LdPartW E) :
    Rels Kc St E₀ (S'.Msg × (Pi × (LdPartW E × LdPartGh))) where
  rel  := fun st y w => A.rel st y (w.2.1, (ov w.1 w.2.2.1, w.2.2.2))
  relR := fun a w => A.relR a (w.2.1, (ov w.1 w.2.2.1, w.2.2.2))
  on   := A.on
  core := fun w => A.core (w.2.1, (ov w.1 w.2.2.1, w.2.2.2))

/-- The ties after the first sending. -/
structure LdPartTie0 {F E : Type} [Field F] [Fintype F] [Field E] [Algebra F E] {Cf : LdCf F E}
    (P : LdPartD Cf) (K : LdPartPk) {S' : Sig E} (O' : LdPartOut E S')
    (ov : S'.Msg → LdPartW E → LdPartW E) {St' : Type} (x' : St' → Cf.Xm)
    (bitX : ℕ → Cf.Xm → (ℕ → ℕ → F) → LdPartGh → (ℕ → E) → Prop)
    (vld : St' → Cf.conf.Msg × S'.Msg → Prop) : Prop where
  ovPk   : ∀ m w j, j ≠ 0 → (ov m w).pk j = w.pk j
  ovBit  : ∀ m w j, j ≠ 0 → (ov m w).bit j = w.bit j
  pkX    : ∀ m w g, PackBy P.B K.rdx (P.layX K g 0) (P.layW K (ov m w) 0) → O'.pkX m g
  rdX    : ∀ m g,
    O'.pkX m g → ∀ q ∈ (P.seg 0).places, O'.A m q.1 q.2.1 q.2.2 = ((g q.1 q.2.1 q.2.2 : ℤ) : E)
  bits   : ∀ st U m w g, O'.pkX m g → bitX 0 (x' st) (P.matU U) g ((ov m w).bit 0) → vld st (U, m)
  pkR    : ∀ m w, O'.pkR m → Packed K.P (2 * P.D) K.rdx (P.layW K (ov m w) 0)
  rdOwn  : ∀ m w, O'.pkR m →
    ∀ r c, r < 2 ^ (P.seg 0).rowsLog → c < (P.seg 0).cols → O'.A m 0 r c = P.cellsW K (ov m w) 0 r c

/-- What is asked of a step whose verifier rejects unless ok holds. -/
structure StepWOKg {E Kc : Type} [Field E] (S : Sig E) {St St' Wp Wp' : Type} {E₀ : ExtSpec}
    (A : Rels Kc St E₀ (S.Msg × Wp)) (A' : Rels Kc St' E₀ (S.Msg × Wp')) (ok : St → Prop)
    (f : St → St') (up : St → S.Msg × Wp → Wp') (dn : St × E₀.Str → S.Msg × Wp' → Wp) : Prop where
  fw   : ∀ st y w, A.rel st y w → A'.rel (f st) y (w.1, up st w)
  hok  : ∀ st y w, A.rel st y w → ok st
  on   : ∀ st y, A.on (st, y) → ok st → A'.on (f st, y)
  core : ∀ st w, A'.core (w.1, up st w) = A.core w
  bw   : ∀ st y w, A.on (st, y) → ok st → A'.relR (f st, y) w → A.relR (st, y) (w.1, dn (st, y) w)

namespace Spec

/-- The model's one step. -/
def ldPartHead_step : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (Cf : LdCf F E) (P : LdPartD Cf)
      (K : LdPartPk) (Bt : LdPartBits P) (p : ℕ) (S' : Sig E) (O' : LdPartOut E S')
      (ov : S'.Msg → LdPartW E → LdPartW E) (St' : Type) (x' : St' → Cf.Xm)
      (rc' : St' → Cf.conf.Rec) (f : Cf.Xm × Cf.conf.Rec → St')
      (vld : St' → Cf.conf.Msg × S'.Msg → Prop),
    P.Props p → Cf.ModelOK → LdPartTie0 P K O' ov x' Bt.ok vld →
    (∀ st, x' (f st) = st.1) → (∀ st, rc' (f st) = st.2) →
    StepWOKg S' (ldPartFirst (ldReqRels (P.cfB K Bt).conf fun w => w.2.2) ov)
      (idxAt Cf.conf rc' (P.entry K 0 O' x' rc' Bt.ok vld)) (fun st => P.form st.1) f
      (fun _ w => w.2) (fun _ w => w.2)

end Spec

end Cb
