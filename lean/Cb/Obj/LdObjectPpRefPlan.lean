-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectPpRefPlan.lean: assembly of the holographic IOP from its sub-protocols: the plan of
this protocol's technical report (lean/CREDITS.md) for the batch test at the end of a request, as a
term: six clauses on that plan reduce to conditions on places.

Definitions, statements and proofs. An assembly; groups, kept sets, tests and towers stay
parameters.
A plan (`LdLinPp`, Cb/Ld/LdLinClosePlanP.lean) fixes how the rows that the test for linear
constraints leaves are closed.
Why: `R.HypPl` (Cb/Obj/LdObjectPpRows.lean) asks of the plan pB of the batch test six clauses that
tie it to what a request leaves: abRel, abRelR (what the request leaves says, exact and relaxed,
exactly "the rows rowsB hold"), restVal, restIsB (the tensor row's mask part is the form slB; the
plan's restG is slB read on the instance's group), plSB (slB is non-zero only in oracle messages
kept at both shared bridges that lie in the instance's group), plRB (a row is non-zero only in
oracle messages kept at all three bridges).
The analogue of Cb/Obj/LdObjectRefPlan.lean (the plan without a splitting).

Main names:
  `LdOnPackP F E`: what the object's data hold of the batch test's plan and of the rows that a
    request leaves. `Rr.onPack`: that part of `Rr : LdObjRp`.
  `ldRefOnP R p₀`: the same at the end of a request `R : LdORE` (Cb/Obj/LdObjectReqEnd.lean), for
    any plan `p₀ : LdLinPp` over what R leaves.
  `R.PlacesOKP p₀ plR`: the conditions on places:
    own: the oracle message of every place `R.wAt i` of the final batching's own masks is kept at
      p₀'s two shared bridges and lies in the instance's group;
    laid: the same for every place `R.μAt a` at which a pending row's mask form is laid;
    off: the row b vanishes outside `plR b`, at every state;
    kept: the oracle message of every entry in `plR b` is kept at all three bridges: it goes to the
      fourth test.
  `Spec.ldRefPlanP_six`: `R.PlacesOKP p₀ plR` ⇒ `(ldRefOnP R p₀).Six`.
  `Rr.HypPl₁`: `Rr.HypPl` without the six.
  `Spec.ldRefPlanP_hyp`: `Rr.onPack = ldRefOnP R p₀` (one equation that says which terms stand in
    Rr), `R.PlacesOKP p₀ plR`, `Rr.HypPl₁` ⇒ `Rr.HypPl`.

In the technical report the instance's group is {Ω, W_c, the instance's index-mask message}: "own"
and "laid" say that the messages which hold these masks are members of that group.

Limits: what the head of Cb/Obj/LdObjectRefPlan.lean lists as not said is not said here either: that
these messages are still open at the end of the request is the request's. As there, `R.sl` is a free
field of R (that head, row `off`). No instance here.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectPpRows
import Cb.Obj.LdObjectRefPlanProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- The plan with its form "rest" overwritten. -/
@[reducible] def LdLinPp.setRest {E ι κ J Y : Type} [Field E] {C : LdLinC E ι κ J Y}
    (p : LdLinPp C) (slA : Slf E C.Sta C.Sa.Ent) : LdLinPp C :=
  { p with restG := p.restOf slA }

/-- What the object's data hold of the batch test's plan and of the rows that a request leaves. -/
structure LdOnPackP (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] :
    Type 1 where
  Cf   : LdCf F E
  on   : LdOLd Cf
  pB   : LdLinPp on.ol.toC
  Rw   : Type
  rows : Rw → Slf E on.ol.toC.Sta on.ol.toC.Sa.Ent
  tg   : on.ol.toC.Sta → Rw → E
  sl   : Slf E on.ol.toC.Sta on.ol.toC.Sa.Ent

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- The six clauses. -/
structure LdOnPackP.Six (P : LdOnPackP F E) : Prop where
  abRel   : ∀ sa y m wp,
    P.on.ol.toC.Ab.rel sa y (m, wp) ↔ rowsHold P.rows P.tg sa (P.on.ol.toC.Sa.ents m)
  abRelR  : ∀ sa y m wp,
    P.on.ol.toC.Ab.relR (sa, y) (m, wp) ↔ rowsHold P.rows P.tg sa (P.on.ol.toC.Sa.ents m)
  plRB    : ∀ b st (a : P.on.ol.toC.Sa.O) j, P.rows b st ⟨a, j⟩ ≠ 0 →
    ∃ (h₁ : P.pB.kp₁ (.inl (.inl (.inl a)))) (h₂ : P.pB.kp₂ ⟨_, h₁⟩), P.pB.kp₃ ⟨⟨_, h₁⟩, h₂⟩
  restIsB : P.pB.restG = P.pB.restOf P.sl
  restVal : ∀ sa ma, P.on.ol.toC.rest sa ma = P.sl.val sa (P.on.ol.toC.Sa.ents ma)
  plSB    : ∀ st (a : P.on.ol.toC.Sa.O) j, P.sl st ⟨a, j⟩ ≠ 0 →
    ∃ (h₁ : P.pB.kp₁ (.inl (.inl (.inl a)))) (h₂ : P.pB.kp₂ ⟨_, h₁⟩), P.pB.Gc.mem ⟨⟨_, h₁⟩, h₂⟩

/-- that part of the object's data -/
@[reducible] def LdObjRp.onPack (Rr : LdObjRp F E) : LdOnPackP F E :=
  ⟨Rr.W.Cf, Rr.on, Rr.pB, Rr.RwB, Rr.rowsB, Rr.tgB, Rr.slB⟩

/-- At the end of a request, for any plan over what it leaves. -/
@[reducible] def ldRefOnP {Kc : Type} (R : LdORE F E Kc) (p₀ : LdLinPp R.O.d.ol.toC) :
    LdOnPackP F E :=
  ⟨R.Cf, R.O.d, p₀.setRest R.restC, R.Bn, fun b cl n => R.sl b ((R.X.stOf cl).1.2 b) n,
    fun cl b => (R.X.stOf cl).1.1 b, R.restC⟩

/-- The conditions on places. -/
structure LdORE.PlacesOKP {Kc : Type} (R : LdORE F E Kc)
    (p₀ : LdLinPp R.O.d.ol.toC) (plR : R.Bn → R.S.Ent → Prop) : Prop where
  own  : ∀ i,
    ∃ (h₁ : p₀.kp₁ (.inl (.inl (.inl (R.wAt i).1)))) (h₂ : p₀.kp₂ ⟨_, h₁⟩), p₀.Gc.mem ⟨⟨_, h₁⟩, h₂⟩
  laid : ∀ a,
    ∃ (h₁ : p₀.kp₁ (.inl (.inl (.inl (R.μAt a).1)))) (h₂ : p₀.kp₂ ⟨_, h₁⟩), p₀.Gc.mem ⟨⟨_, h₁⟩, h₂⟩
  off  : ∀ b x n, ¬ plR b n → R.sl b x n = 0
  kept : ∀ b n,
    plR b n → ∃ (h₁ : p₀.kp₁ (.inl (.inl (.inl n.1)))) (h₂ : p₀.kp₂ ⟨_, h₁⟩), p₀.kp₃ ⟨⟨_, h₁⟩, h₂⟩

/-- `R.HypPl` without the six clauses. -/
structure LdObjRp.HypPl₁ (R : LdObjRp F E) : Prop where
  /-- offline -/
  q₀is   : R.q₀ = fun U => U = ∅
  entAt  : R.W.P.EntAt R.nAt
  plain  : R.p.Plain
  kept   : R.p.Kept
  kIs    : (⟨R.p.k₀.o, R.p.k₀.j⟩ : R.W.O.toC.S.Ent) = R.W.O.toC.eO (R.Y.TS.YO.entF R.n₀)
  noPad  : ∀ n, R.p.Rs₀ (R.W.O.toC.eO n) → R.Y.TS.YO.NoPad n
  restIs : R.p.restG = R.p.restOf (R.W.restF R.nAt)
  plW    : ∀ i,
    ∃ (h₁ : R.p.kp₁
          (.inl (.inl (.inl
                (R.nAt (R.W.P.wAt (pIx R.W.P.bt.fmt (pdPlains E R.W.P.bt.n R.W.P.bt.k) i))).1))))
        (h₂ : R.p.kp₂ ⟨_, h₁⟩),
      R.p.Gc.mem ⟨⟨_, h₁⟩, h₂⟩
  plC    : ∀ (q : Fin (R.W.P.n + 1)) n, R.W.P.gC q n →
    ∃ (h₁ : R.p.kp₁ (.inl (.inl (.inl (R.nAt n).1)))) (h₂ : R.p.kp₂ ⟨_, h₁⟩),
      R.p.Gc.mem ⟨⟨_, h₁⟩, h₂⟩
  plR    : ∀ (r : R.W.RB) n, R.W.P.gR r.1.1 r.2 n →
    ∃ (h₁ : R.p.kp₁ (.inl (.inl (.inl (R.nAt n).1)))) (h₂ : R.p.kp₂ ⟨_, h₁⟩), R.p.kp₃ ⟨⟨_, h₁⟩, h₂⟩
  nowX   : ∀ b, R.X.now b
  kpX    : ∀ o, ¬ R.X.kp o
  needA  : ∀ a,
    R.TP₀.D₁.need (R.TP₀.D₂.need (R.TP₀.D₃.need fun _ => R.X.t)) (.inl (.inl (.inl a))) ≤ R.Bw.t a
  needW  : ∀ a,
    R.TP₀.D₁.need (R.TP₀.D₂.need (R.TP₀.D₃.need fun _ => R.X.t)) (.inl (.inl (.inr a))) ≤ R.Y.tW a
  needU  : ∀ a,
    R.TP₀.D₁.need (R.TP₀.D₂.need (R.TP₀.D₃.need fun _ => R.X.t)) (.inl (.inr a)) ≤ R.Y.tU a
  needO  : ∀ a, R.TP₀.D₁.need (R.TP₀.D₂.need (R.TP₀.D₃.need fun _ => R.X.t)) (.inr a) ≤ R.Y.tO a
  /-- online -/
  shared : R.pB.Shared
  plainB : R.pB.Plain
  keptB  : R.pB.Kept
  kIsB   : (⟨R.pB.k₀.o, R.pB.k₀.j⟩ : R.on.ol.toC.S.Ent) = R.on.ol.toC.eO (R.Y.TB.YO.entF R.n₀B)
  noPadB : ∀ n, R.pB.Rs₀ (R.on.ol.toC.eO n) → R.Y.TB.YO.NoPad n
  nowXB  : ∀ b, R.XB.now b
  kpXB   : ∀ o, ¬ R.XB.kp o
  q₀Be   : R.q₀B ∅
  qaOK   : ∀ W, R.on.ol.toC.Sa.qFam R.q₀B R.baB W → R.qaB W
  oneN   : 1 ≤ R.N
  needNA : ∀ a,
    R.TB₀.D₁.need
        (R.TB₀.D₂.need (R.TB₀.D₃.needV R.N (fun a => R.on.ol.toC.isSh a.1.1) (R.XB.bOneP R.N)))
        (.inl (.inl (.inl a))) ≤ R.baB a
  needNW : ∀ a,
    R.TB₀.D₁.need
        (R.TB₀.D₂.need (R.TB₀.D₃.needV R.N (fun a => R.on.ol.toC.isSh a.1.1) (R.XB.bOneP R.N)))
        (.inl (.inl (.inr a))) ≤ R.Y.tWB a
  needNU : ∀ a,
    R.TB₀.D₁.need
        (R.TB₀.D₂.need (R.TB₀.D₃.needV R.N (fun a => R.on.ol.toC.isSh a.1.1) (R.XB.bOneP R.N)))
        (.inl (.inr a)) ≤ R.Y.tUB a
  needNO : ∀ a,
    R.TB₀.D₁.need
        (R.TB₀.D₂.need (R.TB₀.D₃.needV R.N (fun a => R.on.ol.toC.isSh a.1.1) (R.XB.bOneP R.N)))
        (.inr a) ≤ R.Y.tOB a

end

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- The six clauses, from conditions on places. -/
def ldRefPlanP_six : Prop :=
  ∀ (Kc : Type) (R : LdORE F E Kc) (p₀ : LdLinPp R.O.d.ol.toC) (plR : R.Bn → R.S.Ent → Prop),
    R.PlacesOKP p₀ plR → (ldRefOnP R p₀).Six

/-- States: under the first two hypotheses below, `Rr.HypPl₁` gives `Rr.HypPl`: the six clauses
follow. -/
def ldRefPlanP_hyp : Prop :=
  ∀ (Kc : Type) (Rr : LdObjRp F E) (R : LdORE F E Kc)
      (p₀ : LdLinPp R.O.d.ol.toC) (plR : R.Bn → R.S.Ent → Prop),
    Rr.onPack = ldRefOnP R p₀ → R.PlacesOKP p₀ plR → Rr.HypPl₁ → Rr.HypPl

end
end Spec

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem ldRefPlanP_six : Spec.ldRefPlanP_six F E := by
  intro Kc R p₀ plR h
  have hS := ldObjRefPl_says F E Kc R
  refine ⟨hS.abRel, hS.abRelR, fun b st a j hne => ?_, rfl, hS.restVal, fun st a j hne => ?_⟩
  · by_contra hno
    exact hne (h.off b _ ⟨a, j⟩ fun hp => hno (h.kept b ⟨a, j⟩ hp))
  · rcases hS.supp st ⟨a, j⟩ hne with ⟨i, e⟩ | ⟨x, e⟩
    · have ha : a = (R.wAt i).1 := congrArg Sigma.fst e
      subst ha
      exact h.own i
    · have ha : a = (R.μAt x).1 := congrArg Sigma.fst e
      subst ha
      exact h.laid x

theorem ldRefPlanP_hyp : Spec.ldRefPlanP_hyp F E := by
  intro Kc Rr R p₀ plR hIs hP h
  have hS : Rr.onPack.Six := by
    rw [hIs]
    exact ldRefPlanP_six F E Kc R p₀ plR hP
  exact { q₀is := h.q₀is, entAt := h.entAt, plain := h.plain, kept := h.kept, kIs := h.kIs,
          noPad := h.noPad, restIs := h.restIs, plW := h.plW, plC := h.plC, plR := h.plR,
          nowX := h.nowX, kpX := h.kpX, needA := h.needA, needW := h.needW, needU := h.needU,
          needO := h.needO, shared := h.shared, plainB := h.plainB, keptB := h.keptB,
          kIsB := h.kIsB, noPadB := h.noPadB, abRel := hS.abRel, abRelR := hS.abRelR,
          plRB := hS.plRB, restIsB := hS.restIsB, restVal := hS.restVal, plSB := hS.plSB,
          nowXB := h.nowXB, kpXB := h.kpXB, q₀Be := h.q₀Be, qaOK := h.qaOK, oneN := h.oneN,
          needNA := h.needNA, needNW := h.needNW, needNU := h.needNU, needNO := h.needNO }

end
end Cb
