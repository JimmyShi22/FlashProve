-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectRefPlan.lean: assembly of the holographic IOP from its sub-protocols: the plan of the
batch test (the test for linear constraints at up to N instances) at the end of a request, as a
term: six clauses on that plan reduce to conditions on places.

Definitions and statements; the proofs are in Cb/Obj/LdObjectRefPlanProofs.lean. An assembly;
groups, kept sets, tests and towers stay parameters.
A plan (`LdLinPl`, Cb/Ld/LdLinClosePlan.lean: the plan without a splitting) fixes how the rows that
the test for linear constraints leaves are closed: the groups of oracle messages, the rows that go
to the test on each group, and the messages kept for later tests. A place is an entry of an oracle
message (`Sig.Ent`, Cb/Ld/LdBatSig.lean).
Why: `Rr.HypPl` (Cb/Obj/LdObjectPlanRows.lean) asks of the plan pB of the batch test, beside choices
and numbers, six clauses that tie it to what a request leaves:
  abRel, abRelR: what the request leaves says, exact and relaxed, exactly "the rows rowsB hold";
  restVal: the tensor row's mask part "rest" is the value of the form slB;
  restIsB: the plan's form restG is slB, read on the second group;
  plSB: at every state slB is non-zero only in oracle messages that are kept at the first bridge and
    lie in the second group;
  plRB: at every state a row is non-zero only in oracle messages that are kept at both bridges.
Cb/Obj/LdObjectDataRefPl.lean removes four of them, with a set of places that the user names. Here
the plan stands in the equation (`Rr.onPack = ldRefOn R p₀`, below) too, so that all six follow and
the conditions are written in the fields of the request's end R and of the plan.

Main names:
  `LdOnPack F E`: what the object's data hold of the batch test's plan and of the rows that a
    request leaves: the configuration; the datum "on"; the plan; the rows' names, the rows, their
    targets; the mask part as a form. `Rr.onPack`: that part of the object's data `Rr : LdObjR`.
  `ldRefOn R p₀`: the same at the end of a request `R : LdORE` (Cb/Obj/LdObjectReqEnd.lean), for any
    plan p₀ over what R leaves: the plan `p₀.setRest R.restC`; the rows that stay open, each with
    the whole claim as its state; the coefficients `R.restC`.
  `P.Six`: the six clauses.
  `R.PlacesOK p₀ plR`: the conditions on places (`plR b`: a public set of entries for the row b):
    own: the oracle message of every place `R.wAt i` of the final batching's own masks is kept at
      p₀'s first bridge and lies in its second group;
    laid: the same for every place `R.μAt a` at which a pending row's mask form is laid;
    off: the row b vanishes outside `plR b`, at every state. `R.sl` is a free field of R: this is a
      condition on it. Where the rows are a segment's rows, laid at named places,
      Cb/Req1/LdSegRefSupp.lean (`ldSegRef_supp`) proves it with no hypothesis beside whatever its
      arguments hold as proofs (in `G : LdGaP`, for one, `G.Q.D.p.neC : Nonempty C`,
      Cb/Ld/LdRng.lean); that `R.sl` is such a family at the reference request is not shown here;
    kept: the oracle message of every entry in `plR b` is kept at both bridges.
  `Spec.ldRefPlan_six`: `R.PlacesOK p₀ plR` ⇒ `(ldRefOn R p₀).Six`.
  `Rr.HypPl₁`: `Rr.HypPl` without the six.
  `Spec.ldRefPlan_hyp`: one equation that says which terms stand in Rr (`Rr.onPack = ldRefOn R p₀`:
    whoever builds Rr from R and p₀ has it by definition; a hypothesis here, as the equations of
    Cb/Obj/LdObjectData.lean, Cb/Obj/LdObjectDataRef.lean), `R.PlacesOK p₀ plR` and `Rr.HypPl₁` give
    `Rr.HypPl`.

Notation: `.inl (.inl (.inl a))`, `.inl (.inl (.inr a))`, `.inl (.inr a)`, `.inr a` (in `LdLinC.S`,
Cb/Ld/LdLinClosePre.lean), in this order: a message that the preamble left, one of W's, of G_u's, of
Ω's family; `kp₁`, `kp₂`: the messages kept at the first, at the second bridge (`LdLinPl`,
Cb/Ld/LdLinClosePlan.lean); `G₂`: the plan's second group (the same structure); `R.Bn`: the names of
the rows that stay open (`LdORE`, Cb/Obj/LdObjectReqEnd.lean).

Limits: what `Rr.HypPl₁` still asks online: all members of the first group are shared; the third
test takes all rows and keeps nothing; the demands; 1 ≤ N; four families of inequalities: choices of
the plan and numbers.
This file does not say that the messages which hold the masks at wAt, μAt are still open at the end
of the request: they are oracle messages of `R.S` by type; that the request's own closings left them
open is the request's. It says nothing on the three tests' own hypotheses. It does not say that the
equation, the places and `Rr.HypPl₁` can be met together. No instance that meets the hypotheses of
`ldRefPlan_hyp` is part of this library; as far as the library shows, this theorem may hold of
nothing. `Z.HypRefT` (Cb/Obj/LdObjectDataRefT.lean) has these three as its clauses onIs, places,
pl₁.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectDataRefPlProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- The plan with its form "rest" overwritten. -/
@[reducible] def LdLinPl.setRest {E ι κ J Y : Type} [Field E] {C : LdLinC E ι κ J Y}
    (p : LdLinPl C) (slA : Slf E C.Sta C.Sa.Ent) : LdLinPl C :=
  { p with restG := p.restOf slA }

/-- What the object's data hold of the batch test's plan and of the rows that a request leaves. -/
structure LdOnPack (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Type 1 where
  Cf   : LdCf F E
  on   : LdOLd Cf
  pB   : LdLinPl on.ol.toC
  Rw   : Type
  rows : Rw → Slf E on.ol.toC.Sta on.ol.toC.Sa.Ent
  tg   : on.ol.toC.Sta → Rw → E
  sl   : Slf E on.ol.toC.Sta on.ol.toC.Sa.Ent

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- The six clauses. -/
structure LdOnPack.Six (P : LdOnPack F E) : Prop where
  abRel   : ∀ sa y m wp,
    P.on.ol.toC.Ab.rel sa y (m, wp) ↔ rowsHold P.rows P.tg sa (P.on.ol.toC.Sa.ents m)
  abRelR  : ∀ sa y m wp,
    P.on.ol.toC.Ab.relR (sa, y) (m, wp) ↔ rowsHold P.rows P.tg sa (P.on.ol.toC.Sa.ents m)
  plRB    : ∀ b st (a : P.on.ol.toC.Sa.O) j,
    P.rows b st ⟨a, j⟩ ≠ 0 → ∃ h : P.pB.kp₁ (.inl (.inl (.inl a))), P.pB.kp₂ ⟨_, h⟩
  restIsB : P.pB.restG = P.pB.restOf P.sl
  restVal : ∀ sa ma, P.on.ol.toC.rest sa ma = P.sl.val sa (P.on.ol.toC.Sa.ents ma)
  plSB    : ∀ st (a : P.on.ol.toC.Sa.O) j,
    P.sl st ⟨a, j⟩ ≠ 0 → ∃ h : P.pB.kp₁ (.inl (.inl (.inl a))), P.pB.G₂.mem ⟨_, h⟩

/-- that part of the object's data -/
@[reducible] def LdObjR.onPack (Rr : LdObjR F E) : LdOnPack F E :=
  ⟨Rr.W.Cf, Rr.on, Rr.pB, Rr.RwB, Rr.rowsB, Rr.tgB, Rr.slB⟩

/-- At the end of a request, for any plan over what it leaves. -/
@[reducible] def ldRefOn {Kc : Type} (R : LdORE F E Kc) (p₀ : LdLinPl R.O.d.ol.toC) :
    LdOnPack F E :=
  ⟨R.Cf, R.O.d, p₀.setRest R.restC, R.Bn, fun b cl n => R.sl b ((R.X.stOf cl).1.2 b) n,
    fun cl b => (R.X.stOf cl).1.1 b, R.restC⟩

/-- The conditions on places. -/
structure LdORE.PlacesOK {Kc : Type} (R : LdORE F E Kc)
    (p₀ : LdLinPl R.O.d.ol.toC) (plR : R.Bn → R.S.Ent → Prop) : Prop where
  own  : ∀ i, ∃ h : p₀.kp₁ (.inl (.inl (.inl (R.wAt i).1))), p₀.G₂.mem ⟨_, h⟩
  laid : ∀ a, ∃ h : p₀.kp₁ (.inl (.inl (.inl (R.μAt a).1))), p₀.G₂.mem ⟨_, h⟩
  off  : ∀ b x n, ¬ plR b n → R.sl b x n = 0
  kept : ∀ b n, plR b n → ∃ h : p₀.kp₁ (.inl (.inl (.inl n.1))), p₀.kp₂ ⟨_, h⟩

/-- `R.HypPl` without the six clauses. -/
structure LdObjR.HypPl₁ (R : LdObjR F E) : Prop where
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
  /-- online: choices of the plan, and numbers -/
  shared : R.pB.Shared
  nowXB  : ∀ b, R.XB.now b
  kpXB   : ∀ o, ¬ R.XB.kp o
  q₀Be   : R.q₀B ∅
  qaOK   : ∀ W, R.on.ol.toC.Sa.qFam R.q₀B R.baB W → R.qaB W
  oneN   : 1 ≤ R.N
  needNA : ∀ a, R.TB₀.D₁.need (R.TB₀.D₂.needV R.N (fun a => R.on.ol.toC.isSh a.1) (R.XB.bOne R.N)) (.inl (.inl (.inl a))) ≤ R.baB a
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

/-- States: the overwritten plan's form is the given one, by definition; `G₁`, `kp₁`, `S₂` are
p's. -/
def ldRefPlan_set : Prop :=
  ∀ (E ι κ J Y : Type) [Field E] (C : LdLinC E ι κ J Y)
      (p : LdLinPl C) (slA : Slf E C.Sta C.Sa.Ent),
    (p.setRest slA).restG = (p.setRest slA).restOf slA ∧
    (p.setRest slA).G₁ = p.G₁ ∧
    (p.setRest slA).kp₁ = p.kp₁ ∧
    (p.setRest slA).S₂ = p.S₂

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- The six clauses, from conditions on places. -/
def ldRefPlan_six : Prop :=
  ∀ (Kc : Type) (R : LdORE F E Kc) (p₀ : LdLinPl R.O.d.ol.toC) (plR : R.Bn → R.S.Ent → Prop),
    R.PlacesOK p₀ plR → (ldRefOn R p₀).Six

/-- States: under the first two hypotheses below, `Rr.HypPl₁` gives `Rr.HypPl`: the six clauses
follow. -/
def ldRefPlan_hyp : Prop :=
  ∀ (Kc : Type) (Rr : LdObjR F E) (R : LdORE F E Kc)
      (p₀ : LdLinPl R.O.d.ol.toC) (plR : R.Bn → R.S.Ent → Prop),
    Rr.onPack = ldRefOn R p₀ → R.PlacesOK p₀ plR → Rr.HypPl₁ → Rr.HypPl

end
end Spec
end Cb
