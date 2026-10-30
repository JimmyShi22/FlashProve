-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegNext.lean: under `N.Carried` and `N.Back`, the relation after a segment is: the rows on
the switch's messages, beside one carried predicate, now read on the messages just sent.

Definitions, statements (in `Cb.Spec`) and proofs.
The matter: the output relation of one segment's reduction, which is the input relation of the next.

In this protocol's technical report (lean/CREDITS.md) the relations of consecutive blocks are equal.
After a segment there are: rows on the messages that the switch sent; the tensor rows so far; the
conditions of the next segment, read on the cell messages just sent; the conditions of all later
segments, on cells that are a further part of the witness until they are sent.
Here this is said for the closing of one group (`LdFoldD` D, Cb/Req1/LdSegKit.lean; `LdCloseD` Q,
Cb/Req1/LdSegFit.lean). Behind a sending the exact relation knows of the new messages only what the
old witness, read back off them, says. So what the next segment's first messages hold is in the
further witness up to the closing, with its claim carried.

Main names:
  `Q.kept m`: the kept messages, as they are read after the closing: those that are not held as they
    stand, the held ones off the slots of the cut.
  `LdNextD D Q`: the data. Dt: the data that the next segment's first messages hold; rd: how they
    are read off the messages just sent; dat: where they were in the further witness; rst: the
    further witness that is handed on; Cn: the carried predicate (exact, relaxed, condition, core)
    on (kept messages, data, further witness handed on): all that is claimed beside the segment's
    rows.
  `N.Carried`: see its docstring (what the closing carries: `D.A₀`).
  `N.Back`: the messages just sent give the further witness back: its data are those that they hold;
    the rest is what was handed on.
  `N.behind`: Cn, read at the kept messages, the data that the messages just sent hold, the further
    witness handed on.
  `Spec.ldSegNext_same`: under `N.Carried` and `N.Back`, what else is claimed after the locations
    (`Q.A₁`) is `N.behind`: exact and relaxed relation and condition as equivalences, the core as an
    equation.
  `Spec.ldSegNext_stage`: so, under the same two, the base joint of the segment's last stage is: the
    rows on the switch's messages (`Q.loc.After`), beside `N.behind`.
  `Spec.ldSegNext_step`: under the same two, for any base joint B over the same oracle messages,
    further oracles and further witness, and any map φ of explicit parts: if (rows, beside
    `N.behind`) goes over into B along φ (four clauses: `LdStepOK`), so does the segment's last
    stage: the step has its hypothesis.

Limits: what the step at the head of the next segment still owes (a hypothesis of
`Spec.ldSegNext_step`, beside `N.Carried` and `N.Back`): that "the switch's rows, and Cn at the
data" goes over into the next body's first claim along φ. For a front whose riding joint is defined
so, that is an identity; nothing here shows it for a given front.
Two things that depend on the choice of the data:
(1) In the report the cells stand in the further witness as integer cells, and the
sending needs them as packings (with their multiplicities): under the range predicate a bijection of
witnesses, up to the multiplicities, which the relaxation drops. Here that is a matter of "dat" and
"rd" (Dt may be either form) and of `N.Back`.
(2) A predicate that stands in the exact relation only (as the one on the next segment's
multiplicities does) is a clause of Cn.rel and not of Cn.relR: the two are separate fields of Cn.
That Cn splits into "the tensor rows so far; the next segment's conditions; the conditions of all
later segments" is not said: Cn is one field.
This file does not say that Cn rides through the body before the closing (the body's own clauses).
It says nothing on the first step of a request: from the request's relation to "all segments'
conditions, all cells in the further witness".
"The same oracle messages": in `LdBodyD` and `LdRefD` (Cb/Req1/LdSegRefBody.lean,
Cb/Req1/LdSegRefAll.lean) the signature of a body is a part of its data, so for a list of segments
that is a variable this holds only at instances.




Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegFit
import Cb.Req1.LdSegFrontTab

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Ood IOR

/-- the kept messages, as they are read after the closing -/
def LdCloseD.kept {E Kc : Type} [Field E] [Fintype E] {D : LdFoldD E Kc}
    (Q : LdCloseD D) (m : (D.S₂.sum Q.N).Msg) : D.S₁.Msg :=
  D.rd (D.S₂.left Q.N (T := OMsg.Msg) m) (D.held.msg (Q.cutN (D.S₂.right Q.N (T := OMsg.Msg) m)).1)

/-- What is carried across a closing: the data. -/
structure LdNextD {E Kc : Type} [Field E] [Fintype E] (D : LdFoldD E Kc) (Q : LdCloseD D) :
    Type 1 where
  Dt  : Type
  rd  : Q.N.Msg → Dt
  dat : D.Wp → Dt
  rst : D.Wp → Q.Wp'
  Cn  : Rels Kc D.St₀ D.E₀ ((D.S₁.Msg × Dt) × Q.Wp')

namespace LdNextD
variable {E Kc : Type} [Field E] [Fintype E] {D : LdFoldD E Kc} {Q : LdCloseD D} (N : LdNextD D Q)

/-- What the closing carries is Cn, read at the data in the further witness. -/
structure Carried : Prop where
  rel  : ∀ st y μ wp, D.A₀.rel st y (μ, wp) ↔ N.Cn.rel st y ((μ, N.dat wp), N.rst wp)
  relR : ∀ a μ wp, D.A₀.relR a (μ, wp) ↔ N.Cn.relR a ((μ, N.dat wp), N.rst wp)
  on   : ∀ a, D.A₀.on a ↔ N.Cn.on a
  core : ∀ μ wp, D.A₀.core (μ, wp) = N.Cn.core ((μ, N.dat wp), N.rst wp)

/-- The messages just sent give the further witness back. -/
structure Back : Prop where
  dat : ∀ n w', N.dat (Q.bk₀ n w') = N.rd n
  rst : ∀ n w', N.rst (Q.bk₀ n w') = w'

/-- where Cn is read after the closing -/
def at' (w : (D.S₂.sum Q.N).Msg × Q.Wp') : (D.S₁.Msg × N.Dt) × Q.Wp' :=
  ((Q.kept w.1, N.rd (D.S₂.right Q.N (T := OMsg.Msg) w.1)), w.2)

/-- Cn, read on the messages just sent. -/
def behind : Rels Kc D.St₀ D.E₀ ((D.S₂.sum Q.N).Msg × Q.Wp') :=
  ⟨fun st y w => N.Cn.rel st y (N.at' w), fun a w => N.Cn.relR a (N.at' w),
    N.Cn.on, fun w => N.Cn.core (N.at' w)⟩

end LdNextD

namespace Spec

/-- States: under `N.Carried` and `N.Back`, what else is claimed after the locations (`Q.A₁`) is the
carried predicate, read on the messages just sent (`N.behind`). -/
def ldSegNext_same : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (D : LdFoldD E Kc) (Q : LdCloseD D) (N : LdNextD D Q),
    N.Carried → N.Back →
    (∀ st y w, Q.A₁.rel st y w ↔ N.behind.rel st y w) ∧
    (∀ a w, Q.A₁.relR a w ↔ N.behind.relR a w) ∧
    (∀ a, Q.A₁.on a ↔ N.behind.on a) ∧
    ∀ w, Q.A₁.core w = N.behind.core w

def ldSegNext_stage : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (D : LdFoldD E Kc) (Q : LdCloseD D) (N : LdNextD D Q),
    N.Carried → N.Back →
    (∀ x y w, Q.loc.tgt.A.rel x y w ↔ (claimRels Q.loc.After N.behind).rel x y w) ∧
    (∀ a w, Q.loc.tgt.A.relR a w ↔ (claimRels Q.loc.After N.behind).relR a w) ∧
    (∀ a, Q.loc.tgt.A.on a ↔ (claimRels Q.loc.After N.behind).on a) ∧
    ∀ w, Q.loc.tgt.A.core w = (claimRels Q.loc.After N.behind).core w

/-- The step at the head of the next segment. -/
def ldSegNext_step : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (D : LdFoldD E Kc) (Q : LdCloseD D) (N : LdNextD D Q)
      (St' : Type) (B : Rels Kc St' D.E₀ ((D.S₂.sum Q.N).Msg × Q.Wp')) (φ : Q.loc.tgt.St → St'),
    N.Carried → N.Back → LdStepOK (D.S₂.sum Q.N) (claimRels Q.loc.After N.behind) B φ →
    LdStepOK (D.S₂.sum Q.N) Q.loc.tgt.A B φ ∧ (ldStepF (D.S₂.sum Q.N) Q.loc.tgt.A B φ).Hyp

end Spec

theorem ldSegNext_same : Spec.ldSegNext_same := by
  intro E Kc _ _ D Q N hC hB
  refine ⟨fun st y w => ?_, fun a w => ?_, fun a => hC.on a, fun w => ?_⟩
  · exact (hC.rel st y _ _).trans (by rw [hB.dat, hB.rst]; exact Iff.rfl)
  · exact (hC.relR a _ _).trans (by rw [hB.dat, hB.rst]; exact Iff.rfl)
  · exact (hC.core _ _).trans (by rw [hB.dat, hB.rst]; rfl)

theorem ldSegNext_stage : Spec.ldSegNext_stage := by
  intro E Kc _ _ D Q N hC hB
  obtain ⟨h1, h2, h3, h4⟩ := ldSegNext_same E Kc D Q N hC hB
  exact ⟨fun x y w => and_congr_right fun _ => h1 _ _ _,
    fun a w => and_congr_right fun _ => h2 _ _,
    fun a => h3 _, fun w => h4 w⟩

theorem ldSegNext_step : Spec.ldSegNext_step := by
  intro E Kc _ _ D Q N St' B φ hC hB h
  obtain ⟨h1, h2, h3, h4⟩ := ldSegNext_stage E Kc D Q N hC hB
  have hk : LdStepOK (D.S₂.sum Q.N) Q.loc.tgt.A B φ :=
    ⟨fun st y w hw => h.fw st y w ((h1 st y w).1 hw),
      fun st y ho => h.on st y ((h3 (st, y)).1 ho),
      fun w => (h.core w).trans (h4 w).symm,
      fun st y w ho hw => (h2 (st, y) w).2 (h.bw st y w ((h3 (st, y)).1 ho) hw)⟩
  exact ⟨hk, hk.hyp⟩

end Cb
