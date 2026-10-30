-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectDataRefPl.lean: book-keeping for the hypotheses of a holographic IOP: at the
reference request, four clauses on the plan of the batch test follow from one equation and a
condition on places: what the request's last claims say is proved, not asked.

One statement holds of every request's end; the other is an implication between records of
hypotheses.
Definitions and statements (`Cb.Spec.ldObjRefPl_says`, `Cb.Spec.ldObjRefPl_hyp`); the proofs are in
Cb/Obj/LdObjectDataRefPlProofs.lean. An assembly.
A plan (`LdLinPl`, Cb/Ld/LdLinClosePlan.lean) says how the rows that the test for linear constraints
leaves are tested: two groups of oracle messages, and which messages are kept after each.
Cb/Obj/LdObjectPlanRows.lean's `R.HypPl` (conditions on places, numbers and forms of the two plans)
has four clauses that speak of the request's last claims:
  `abRel`, `abRelR`: what the request leaves says, in the exact and in the relaxed form, exactly
    "the rows rowsB hold";
  `restVal`: the tensor row's mask part "rest" is the value of the form slB;
  `plSB`: at every state the form slB is non-zero only in oracle messages that are kept at the first
    bridge and lie in the second group.
Cb/Obj/LdObjectDataRef.lean puts the reference request into the object and keeps `R.HypPl` whole.
But where the datum "what a request leaves" is read off the final batching
(Cb/Obj/LdObjectReqEnd.lean: `R.O`, for `R : LdORE`, the data of a request's end), the first three
are theorems on that datum, and of the fourth this much: the form is non-zero only at named places
(there: `ldORE_rest`, `ldORE_more`; Cb/Obj/LdObjectPartBatRe.lean: `ldPartBatRe_facts`).

Main names:
  `LdRowsPack F E`: the configuration; the datum "on"; the names of the rows, the rows, their
    targets; the mask part as a form; and a set of places.
  `ldRefRows R`: the same at the end of a request `R : LdORE`: the rows that stay open, each with
    the whole claim as its state; the coefficients `R.restC`; the places: those of the batching's
    own masks (`wAt`) and those at which the pending rows' mask forms are laid (`μAt`).
  `P.Says`: the three clauses, and: at every state the form is non-zero only at the places.
  `Spec.ldObjRefPl_says`: `(ldRefRows R).Says`, for every R.
  `Rr.HypPl₀ plB` (`Rr : LdObjR`; plB: a set of entries): `Rr.HypPl` without the four clauses; in
    their place a condition on places: the oracle message of every entry in plB is kept at the first
    bridge and lies in the second group.
  `Spec.ldObjRefPl_hyp`: one equation that says which terms are in Rr and which set plB is
    (`Rr.rowsPack plB = ldRefRows R`: whoever builds Rr from R and takes that set for plB has it by
    definition; a hypothesis here, as the equations of Cb/Obj/LdObjectData.lean and
    Cb/Obj/LdObjectDataRef.lean) and `Rr.HypPl₀ plB` give `Rr.HypPl`.

Limits: on the rows this is still asked: `plRB` (what a row reads is kept at both bridges), at all
states: the rows that stay open are free fields of R; it holds outright where all that the request
leaves is kept.
This file does not say that the equation and `Rr.HypPl₀` can be met. No instance that meets the
hypotheses of `ldObjRefPl_hyp` is part of this library; as far as the library shows, this theorem
may hold of nothing.
Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectDataRef
import Cb.Obj.LdObjectPartBatRe
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- What the object's data hold of the rows that a request leaves. -/
structure LdRowsPack (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Type 1 where
  Cf   : LdCf F E
  on   : LdOLd Cf
  Rw   : Type
  rows : Rw → Slf E on.ol.toC.Sta on.ol.toC.Sa.Ent
  tg   : on.ol.toC.Sta → Rw → E
  sl   : Slf E on.ol.toC.Sta on.ol.toC.Sa.Ent
  pl   : on.ol.toC.Sa.Ent → Prop

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- What the request's last claims say. -/
structure LdRowsPack.Says (P : LdRowsPack F E) : Prop where
  abRel   : ∀ sa y m wp,
    P.on.ol.toC.Ab.rel sa y (m, wp) ↔ rowsHold P.rows P.tg sa (P.on.ol.toC.Sa.ents m)
  abRelR  : ∀ sa y m wp,
    P.on.ol.toC.Ab.relR (sa, y) (m, wp) ↔ rowsHold P.rows P.tg sa (P.on.ol.toC.Sa.ents m)
  restVal : ∀ sa ma, P.on.ol.toC.rest sa ma = P.sl.val sa (P.on.ol.toC.Sa.ents ma)
  supp    : ∀ st n, P.sl st n ≠ 0 → P.pl n

/-- that part of the object's data, beside a set of entries -/
@[reducible] def LdObjR.rowsPack (Rr : LdObjR F E) (plB : Rr.on.ol.toC.Sa.Ent → Prop) :
    LdRowsPack F E :=
  ⟨Rr.W.Cf, Rr.on, Rr.RwB, Rr.rowsB, Rr.tgB, Rr.slB, plB⟩

/-- At the end of a request. -/
@[reducible] def ldRefRows {Kc : Type} (R : LdORE F E Kc) : LdRowsPack F E :=
  ⟨R.Cf, R.O.d, R.Bn, fun b cl n => R.sl b ((R.X.stOf cl).1.2 b) n, fun cl b => (R.X.stOf cl).1.1 b,
    R.restC, fun n => (∃ i, n = R.wAt i) ∨ ∃ a, n = R.μAt a⟩

/-- `R.HypPl` without the four clauses on the request's last claims; in their place a condition on
places. -/
structure LdObjR.HypPl₀ (R : LdObjR F E) (plB : R.on.ol.toC.Sa.Ent → Prop) : Prop where
  /-- offline -/
  q₀is   : R.q₀ = fun U => U = ∅
  entAt  : R.W.P.EntAt R.nAt
  restIs : R.p.restG = R.p.restOf (R.W.restF R.nAt)
  plW    : ∀ i,
    ∃ h : R.p.kp₁
        (.inl (.inl
            (.inl (R.nAt (R.W.P.wAt (pIx R.W.P.bt.fmt (pdPlains E R.W.P.bt.n R.W.P.bt.k) i))).1))),
      R.p.G₂.mem ⟨_, h⟩
  plC    : ∀ (q : Fin (R.W.P.n + 1)) n,
    R.W.P.gC q n → ∃ h : R.p.kp₁ (.inl (.inl (.inl (R.nAt n).1))), R.p.G₂.mem ⟨_, h⟩
  plR    : ∀ (r : R.W.RB) n,
    R.W.P.gR r.1.1 r.2 n → ∃ h : R.p.kp₁ (.inl (.inl (.inl (R.nAt n).1))), R.p.kp₂ ⟨_, h⟩
  nowX   : ∀ b, R.X.now b
  kpX    : ∀ o, ¬ R.X.kp o
  needA  : ∀ a, R.TP₀.D₁.need (R.TP₀.D₂.need fun _ => R.X.t) (.inl (.inl (.inl a))) ≤ R.Bw.t a
  needW  : ∀ a, R.TP₀.D₁.need (R.TP₀.D₂.need fun _ => R.X.t) (.inl (.inl (.inr a))) ≤ R.Sn.tW a
  needU  : ∀ a, R.TP₀.D₁.need (R.TP₀.D₂.need fun _ => R.X.t) (.inl (.inr a)) ≤ R.Sn.tU a
  needO  : ∀ a, R.TP₀.D₁.need (R.TP₀.D₂.need fun _ => R.X.t) (.inr a) ≤ R.Sn.tO a
  /-- online -/
  shared : R.pB.Shared
  plRB   : ∀ b st (a : R.on.ol.toC.Sa.O) j,
    R.rowsB b st ⟨a, j⟩ ≠ 0 → ∃ h : R.pB.kp₁ (.inl (.inl (.inl a))), R.pB.kp₂ ⟨_, h⟩
  restIsB : R.pB.restG = R.pB.restOf R.slB
  /-- the condition on places -/
  plB₂   : ∀ n, plB n → ∃ h : R.pB.kp₁ (.inl (.inl (.inl n.1))), R.pB.G₂.mem ⟨_, h⟩
  nowXB  : ∀ b, R.XB.now b
  kpXB   : ∀ o, ¬ R.XB.kp o
  q₀Be   : R.q₀B ∅
  qaOK   : ∀ W, R.on.ol.toC.Sa.qFam R.q₀B R.baB W → R.qaB W
  oneN   : 1 ≤ R.N
  needNA : ∀ a,
    R.TB₀.D₁.need (R.TB₀.D₂.needV R.N (fun a => R.on.ol.toC.isSh a.1) (R.XB.bOne R.N))
        (.inl (.inl (.inl a))) ≤ R.baB a
  needNW : ∀ a,
    R.TB₀.D₁.need (R.TB₀.D₂.needV R.N (fun a => R.on.ol.toC.isSh a.1) (R.XB.bOne R.N))
        (.inl (.inl (.inr a))) ≤ R.SnB.tW a
  needNU : ∀ a,
    R.TB₀.D₁.need (R.TB₀.D₂.needV R.N (fun a => R.on.ol.toC.isSh a.1) (R.XB.bOne R.N))
        (.inl (.inr a)) ≤ R.SnB.tU a
  needNO : ∀ a,
    R.TB₀.D₁.need (R.TB₀.D₂.needV R.N (fun a => R.on.ol.toC.isSh a.1) (R.XB.bOne R.N)) (.inr a) ≤
      R.SnB.tO a

end

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- What the last claims of a request say, for every end of a request. -/
def ldObjRefPl_says : Prop := ∀ (Kc : Type) (R : LdORE F E Kc), (ldRefRows R).Says

/-- States: the equation `Rr.rowsPack plB = ldRefRows R` and `Rr.HypPl₀ plB` give `Rr.HypPl`. -/
def ldObjRefPl_hyp : Prop :=
  ∀ (Kc : Type) (Rr : LdObjR F E) (plB : Rr.on.ol.toC.Sa.Ent → Prop) (R : LdORE F E Kc),
    Rr.rowsPack plB = ldRefRows R → Rr.HypPl₀ plB → Rr.HypPl

end
end Spec
end Cb
