-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdHonPlanEq.lean: two chains of reductions that differ in their lists of errors alone: the
closing of the test for linear constraints at N instances, at the write-up's plan
(`LdLinPpT.cZV`, Cb/Ld/LdLinClosePlanPV.lean; `LdObjPp.cZ`, Cb/Obj/LdObjectPlanPaper.lean), does
not read the errors of its four whole tests but in its links' error lists.

Generic: variable data. Nothing assumed beyond the hypotheses of the statements and whatever the
arguments hold as proofs.
A link's errors are numbers, one for each round (`Err`, Iop/Rbr.lean); the full list (`Err.full`,
Cb/Gen/FullErr.lean) has in each round the number of all values of the verifier message. Chains c,
c' agree off their errors if c.full = c'.full: `ChainV.full` (Cb/Gen/FullErrChainV.lean) overwrites,
in every link, the link's errors and its batch errors by the full list.
With `ldHonB_carry` (Cb/Ld/LdHonOnB.lean): if the test's term at R.fullB's closing is `OK`, the term
at R's own closing has the clauses of `LinBT.OKH`, those that read no error (under the hypotheses of
its statement).

Main names:
  `Spec.ldHonEq_tests`: the three tests overwritten.
  `Spec.ldHonEq_rest`: the fourth test overwritten, the three any: at the rest's own letters, as
    `R.toPp` has them (Q' := (X.one tg w).Q, cA' := (X.oneA w).cA, QV' := X.oneVP N q₀ w,
    b' := X.bOneP N) and at the tie "true"; for another tie it is not stated.
  `Spec.ldHonEq_obj`: all four overwritten, at the object's data.
  `Spec.ldHonEq_tests` and `Spec.ldHonEq_rest` take the type ι of positions nonempty.

Why: both sides are the same chain of seven parts (the step, the front, four tests, the end) whose
joints are indexed by terms in which the tests' data occur whole. These indices are equal by
unfolding, but an equation "by rfl" between them, or between the chains, runs into the time limit
in elaborator and kernel (measured: the comparison of two records that differ deep inside is tried
anew at each level of the plan's nest). So the indices are first rewritten to one form, by the
small equations named ldHq.. (each by unfolding at a variable), and only then are the chains
compared, part by part (`chainVFull_appOf`, `chainVFull_oneOf`); the links of the whole tests alone
differ (`ldRunFull_loV`, `ldRunFull_shV`).

Limits: an equation between terms. This file does not say that either closing is in order. It says
nothing on the chance of a cheating prover, nothing on the offline plan, the link or the request,
and nothing on the value of any number.

Terms: lean/GLOSSARY.md.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
import Cb.Gen.FullErrChainV
import Cb.Ld.LdHonPlanDef

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Cb
open Iop Prob Iop.IOR Hiop

theorem chainVFull_appOf {K : Type} {N : ℕ} {A B C : Joint K} {VA : JV N A} {VB : JV N B}
    {VC : JV N C} {c₁ c₁' : ChainV K N VA VB} {c₂ c₂' : ChainV K N VB VC}
    (h₁ : c₁.full = c₁'.full) (h₂ : c₂.full = c₂'.full) :
    (c₁.append c₂).full = (c₁'.append c₂').full := by
  rw [chainVFull_append, chainVFull_append, h₁, h₂]

theorem chainVFull_oneOf {K : Type} {N : ℕ} {A B : Joint K} {VA : JV N A} {VB : JV N B}
    {v v' : LinkV K N VA VB} (h : v.full = v'.full) :
    (ChainV.one v).full = (ChainV.one v').full := by
  rw [fullV_one, fullV_one, h]

section leaf
variable {E : Type} [Field E] [Fintype E] {S : Sig E} (D : LdRunD S) {St₀ Wp : Type} {E₀ : ExtSpec}
variable (A₀ : IOR.Rels Unit St₀ E₀ ((S.sub D.kp).Msg × Wp))
  (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp) (N : ℕ) (VA : JV N (S.jointCf (D.pre A₀)))

theorem ldRunFull_link : (D.full.link A₀ d d').full = (D.link A₀ d d').full := rfl

theorem ldRunFull_loV
    (tieB : VA.W0 → St₀ × (S.sub D.kp).Smp → (E₀.prod (S.sub D.kp).ext).Str →
      (S.sub D.kp).Wit × Wp → Prop)
    (qB : QFam (E₀.prod (S.sub D.kp).ext) N) :
    (D.full.loV A₀ d d' N VA tieB qB).full = (D.loV A₀ d d' N VA tieB qB).full := rfl

theorem ldRunFull_shV (W0' : Type)
    (tieB : W0' → St₀ × (S.sub D.kp).Smp → (E₀.prod (S.sub D.kp).ext).Str →
      (S.sub D.kp).Wit × Wp → Prop)
    (qB : QFam (E₀.prod (S.sub D.kp).ext) N)
    (rep : VA.W0 → ((((D.B → E) × (∀ b, D.Sb b)) × St₀) × S.Smp) × (S.Wit × Wp))
    (nx : VA.W0 → W0') :
    (D.full.shV A₀ d d' N VA W0' tieB qB rep nx).full =
      (D.shV A₀ d d' N VA W0' tieB qB rep nx).full := rfl
end leaf

namespace Spec

/-- States, of the three tests, for ι nonempty: the closing at `T.full` agrees off its errors with
the closing at T; the rest (Q', cA' with `same'`, QV') is any, and the same on both sides. -/
def ldHonEq_tests : Prop :=
  ∀ (E ι κ J Y : Type) [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J]
      [Fintype Y] (C : LdLinC E ι κ J Y) (p : LdLinPp C) (T : LdLinPpT p) (N : ℕ)
      (q₀ : Finset C.E₀.Pos → Prop) (b' : p.S₃.O → ℕ)
      (tie' : C.P.Sh6 → T.Q'.St × p.S₃.Smp → (C.E₀.prod p.S₃.ext).Str → p.S₃.Wit × C.Wpa → Prop)
      (x₀ : C.S.Smp) (y₀ : C.S.ext.Str) (cA' : ChainA Unit (p.S₃.jointCf T.Q'.base) ldTrivJ)
      (same' : cA'.forget = T.Q'.c) (xB : T.StB) (xC : T.StC) (Sn : C.P.Snd)
      (qa : Finset C.P.Ea.Pos → Prop)
      (QV' : LdTcV N (⟨T.Q', cA', same'⟩ : LdTcA p.S₃ C.E₀ C.Wpa) ⟨C.P.Sh6, tie', T.qB₃ N q₀ b'⟩),
    (T.full.cZV N q₀ b' tie' x₀ y₀ cA' same' xB xC Sn qa QV').full =
      (T.cZV N q₀ b' tie' x₀ y₀ cA' same' xB xC Sn qa QV').full

/-- States, of the rest, one more test X on all that is left (X is any `LdRowsD` over the signature
`p.S₃`), for ι nonempty: the closing with `X.full` agrees off its errors with the closing with X, at
the tie "true" (see the head); the three tests are any, and the same on both sides. -/
def ldHonEq_rest : Prop :=
  ∀ (E ι κ J Y : Type) [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J]
      [Fintype Y] (C : LdLinC E ι κ J Y) (p : LdLinPp C) (T₀ : LdLinPpT p) (B : Type) [Fintype B]
      (rows : B → Slf E C.Sta p.S₃.Ent) (X : LdRowsD p.S₃ C.E₀ C.Wpa rows) (tg : C.Sta → B → E)
      (w : (p.S₃.sub X.kp).Wit × C.Wpa) (N : ℕ) (q₀ : Finset C.E₀.Pos → Prop) (x₀ : C.S.Smp)
      (y₀ : C.S.ext.Str) (xB : (T₀.withRest (X.one tg w)).StB) (xC : (T₀.withRest (X.one tg w)).StC)
      (Sn : C.P.Snd) (qa : Finset C.P.Ea.Pos → Prop),
    ((T₀.withRest (X.full.one tg w)).cZV N q₀ (X.full.bOneP N) (fun _ _ _ _ => True) x₀ y₀
        (X.full.oneA w).cA (X.full.oneA w).same xB xC Sn qa (X.full.oneVP N q₀ w)).full =
      ((T₀.withRest (X.one tg w)).cZV N q₀ (X.bOneP N) (fun _ _ _ _ => True) x₀ y₀ (X.oneA w).cA
        (X.oneA w).same xB xC Sn qa (X.oneVP N q₀ w)).full

/-- States: the closing of the test at N instances, at the object's data with the session's four
tests overwritten (`LdObjRp.fullB`, Cb/Ld/LdHonPlanDef.lean), agrees off its errors with the
object's own. -/
def ldHonEq_obj : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (R : LdObjRp F E),
    R.fullB.toPp.cZ.full = R.toPp.cZ.full

end Spec

section rules
variable {E : Type} [Field E] [Fintype E] {S : Sig E} (D : LdRunD S) {St₀ Wp : Type} {E₀ : ExtSpec}

theorem ldHqD_G : D.full.G = D.G := rfl
theorem ldHqD_kp : D.full.kp = D.kp := rfl
theorem ldHqD_B : D.full.B = D.B := rfl
theorem ldHqD_Sb : D.full.Sb = D.Sb := rfl
theorem ldHqD_sl : D.full.sl = D.sl := rfl
theorem ldHqD_Z : D.full.Z = D.Z := rfl
theorem ldHqD_t : D.full.t = D.t := rfl
theorem ldHqD_L : D.full.L = D.L := rfl
theorem ldHqD_pre (A₀ : IOR.Rels Unit St₀ E₀ ((S.sub D.kp).Msg × Wp)) : D.full.pre A₀ = D.pre A₀ :=
  rfl
theorem ldHqD_outX : (D.full.outX : _ → St₀ × (S.sub D.kp).Smp) = D.outX := rfl
theorem ldHqD_outY : (D.full.outY : (E₀.prod S.ext).Str → _) = D.outY := rfl
theorem ldHqD_outW : (D.full.outW : S.Wit × Wp → _) = D.outW := rfl
theorem ldHqD_need : D.full.need = D.need := rfl
theorem ldHqD_needV : D.full.needV = D.needV := rfl
theorem ldHqC_base (Q : LdTc (S.sub D.kp) E₀ Wp) (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp) :
    (LdTc.cons D Q d d').base = D.pre Q.base := rfl
theorem ldHqC_St (Q : LdTc (S.sub D.kp) E₀ Wp) (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp) :
    (LdTc.cons D Q d d').St = (((D.B → E) × (∀ b, D.Sb b)) × Q.St) := rfl
theorem ldHqC_shQ (QA : LdTcA (S.sub D.kp) E₀ Wp) (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp) :
    (LdTcA.consSh D QA d d').Q = LdTc.cons D QA.Q d d' := rfl
theorem ldHqC_loQ (QA : LdTcA (S.sub D.kp) E₀ Wp) (d : S.Wit × Wp) (d' : LdBrW D.G D.kp Wp) :
    (LdTcA.consLo D QA d d').Q = LdTc.cons D QA.Q d d' := rfl
end rules

section planA
variable {E ι κ J Y : Type} [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J]
  [Fintype Y] {C : LdLinC E ι κ J Y} {p : LdLinPp C} (T : LdLinPpT p)
variable (N : ℕ) (q₀ : Finset C.E₀.Pos → Prop) (b' : p.S₃.O → ℕ)
  (tie' : C.P.Sh6 → T.Q'.St × p.S₃.Smp → (C.E₀.prod p.S₃.ext).Str → p.S₃.Wit × C.Wpa → Prop)
variable (x₀ : C.S.Smp) (y₀ : C.S.ext.Str)
  (cA' : ChainA Unit (p.S₃.jointCf T.Q'.base) ldTrivJ) (same' : cA'.forget = T.Q'.c)

theorem ldHqT_Q' : T.full.Q' = T.Q' := rfl
theorem ldHqT_fa : T.full.fa = T.fa := rfl
theorem ldHqT_d₁ : T.full.d₁ = T.d₁ := rfl
theorem ldHqT_d₁' : T.full.d₁' = T.d₁' := rfl
theorem ldHqT_d₂ : T.full.d₂ = T.d₂ := rfl
theorem ldHqT_d₂' : T.full.d₂' = T.d₂' := rfl
theorem ldHqT_d₃ : T.full.d₃ = T.d₃ := rfl
theorem ldHqT_d₃' : T.full.d₃' = T.d₃' := rfl
theorem ldHqF_D₁ : T.full.D₁ = T.D₁.full := rfl
theorem ldHqF_D₂ : T.full.D₂ = T.D₂.full := rfl
theorem ldHqF_D₃ : T.full.D₃ = T.D₃.full := rfl


theorem ldHqF_fF : T.full.fF = T.fF := rfl
theorem ldHqF_tie₃ : T.full.tie₃ tie' = T.tie₃ tie' := rfl
theorem ldHqF_tie₂ : T.full.tie₂ tie' x₀ y₀ = T.tie₂ tie' x₀ y₀ := rfl
theorem ldHqF_tie₁ : T.full.tie₁ tie' x₀ y₀ = T.tie₁ tie' x₀ y₀ := rfl
theorem ldHqF_tieF : T.full.tieF tie' x₀ y₀ = T.tieF tie' x₀ y₀ := rfl
theorem ldHqF_rep₁ (xB : T.StB) : T.full.rep₁ x₀ xB = T.rep₁ x₀ xB := rfl
theorem ldHqF_rep₂ (xC : T.StC) : T.full.rep₂ x₀ xC = T.rep₂ x₀ xC := rfl
end planA

set_option maxHeartbeats 1000000 in
theorem ldHonEq_tests : Spec.ldHonEq_tests := by
  intro E ι κ J Y _ _ _ _ _ _ _ C p T N q₀ b' tie' x₀ y₀ cA' same' xB xC Sn qa QV'
  dsimp only [LdLinPpT.cZV, LdLinC.cZV, LdLinPpT.QV, LdTcV.front, LdLinPpT.QVt, LdTcV.consSh,
    LdTcV.consLo, LdLinPpT.QA, LdLinPpT.QAt, LdTcA.front, LdTc.front, ldHqC_shQ, ldHqC_loQ,
    ldHqC_base, ldHqC_St, LdLinPpT.Q, LdLinPpT.cVf, LdLinPpT.qB₀, LdLinPpT.qB₁, LdLinPpT.qB₂,
    LdLinPpT.qB₃, LdLinPpT.rd, ldHqF_fF, ldHqF_tie₃, ldHqF_tie₂, ldHqF_tie₁, ldHqF_tieF, ldHqF_rep₁,
    ldHqF_rep₂, ldHqT_Q', ldHqT_fa, ldHqT_d₁, ldHqT_d₁', ldHqT_d₂, ldHqT_d₂', ldHqT_d₃, ldHqT_d₃',
    ldHqF_D₁, ldHqF_D₂, ldHqF_D₃, ldHqD_G, ldHqD_kp, ldHqD_B, ldHqD_Sb, ldHqD_sl, ldHqD_Z, ldHqD_t,
    ldHqD_L, ldHqD_pre, ldHqD_outX, ldHqD_outY, ldHqD_outW, ldHqD_need, ldHqD_needV]
  refine chainVFull_appOf rfl (chainVFull_appOf rfl ?_)
  refine chainVFull_appOf (chainVFull_oneOf (ldRunFull_shV T.D₁ _ _ _ _ _ _ _ _ _ _)) ?_
  refine chainVFull_appOf (chainVFull_oneOf (ldRunFull_shV T.D₂ _ _ _ _ _ _ _ _ _ _)) ?_
  exact chainVFull_appOf (chainVFull_oneOf (ldRunFull_loV T.D₃ _ _ _ _ _ _ _)) rfl

section planB
variable {E ι κ J Y : Type} [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J]
  [Fintype Y] {C : LdLinC E ι κ J Y} {p : LdLinPp C} (T₀ : LdLinPpT p)
variable {B : Type} [Fintype B] {rows : B → Slf E C.Sta p.S₃.Ent} (X : LdRowsD p.S₃ C.E₀ C.Wpa rows)
  (tg : C.Sta → B → E) (w : (p.S₃.sub X.kp).Wit × C.Wpa)
variable (N : ℕ) (q₀ : Finset C.E₀.Pos → Prop) (b' : p.S₃.O → ℕ)
  (tie' : C.P.Sh6 → (X.one tg w).Q.St × p.S₃.Smp → (C.E₀.prod p.S₃.ext).Str →
    p.S₃.Wit × C.Wpa → Prop)
variable (x₀ : C.S.Smp) (y₀ : C.S.ext.Str)

theorem ldHqX_run : X.full.run = X.run.full := rfl
theorem ldHqX_d : X.full.d = X.d := rfl
theorem ldHqX_d' : X.full.d' = X.d' := rfl
theorem ldHqX_kp : X.full.kp = X.kp := rfl
theorem ldHqW_fF : (T₀.withRest (X.full.one tg w)).fF = (T₀.withRest (X.one tg w)).fF := rfl
theorem ldHqW_tie₃ :
    (T₀.withRest (X.full.one tg w)).tie₃ tie' = (T₀.withRest (X.one tg w)).tie₃ tie' := rfl
theorem ldHqW_tie₂ :
    (T₀.withRest (X.full.one tg w)).tie₂ tie' x₀ y₀ = (T₀.withRest (X.one tg w)).tie₂ tie' x₀ y₀ :=
  rfl
theorem ldHqW_tie₁ :
    (T₀.withRest (X.full.one tg w)).tie₁ tie' x₀ y₀ = (T₀.withRest (X.one tg w)).tie₁ tie' x₀ y₀ :=
  rfl
theorem ldHqW_tieF :
    (T₀.withRest (X.full.one tg w)).tieF tie' x₀ y₀ = (T₀.withRest (X.one tg w)).tieF tie' x₀ y₀ :=
  rfl
theorem ldHqW_rep₁ (xB : (T₀.withRest (X.one tg w)).StB) :
    (T₀.withRest (X.full.one tg w)).rep₁ x₀ xB = (T₀.withRest (X.one tg w)).rep₁ x₀ xB := rfl
theorem ldHqW_rep₂ (xC : (T₀.withRest (X.one tg w)).StC) :
    (T₀.withRest (X.full.one tg w)).rep₂ x₀ xC = (T₀.withRest (X.one tg w)).rep₂ x₀ xC := rfl


theorem ldHqR_D₁ {tg : C.Sta → B → E} (Rq : LdRowsQ p.S₃ C.E₀ C.Wpa rows tg) :
    (T₀.withRest Rq).D₁ = T₀.D₁ := rfl
theorem ldHqR_D₂ {tg : C.Sta → B → E} (Rq : LdRowsQ p.S₃ C.E₀ C.Wpa rows tg) :
    (T₀.withRest Rq).D₂ = T₀.D₂ := rfl
theorem ldHqR_D₃ {tg : C.Sta → B → E} (Rq : LdRowsQ p.S₃ C.E₀ C.Wpa rows tg) :
    (T₀.withRest Rq).D₃ = T₀.D₃ := rfl
theorem ldHqO_St : (X.full.one tg w).Q.St = (X.one tg w).Q.St := rfl
theorem ldHqO_base : (X.full.one tg w).Q.base = (X.one tg w).Q.base := rfl
theorem ldHqO_fx : (X.full.one tg w).fx = (X.one tg w).fx := rfl
theorem ldHqO_bOneP : X.full.bOneP N = X.bOneP N := rfl
theorem ldHqO_qEndP : X.full.qEndP N q₀ = X.qEndP N q₀ := rfl

end planB

set_option maxHeartbeats 1000000 in
theorem ldHonEq_rest : Spec.ldHonEq_rest := by
  intro E ι κ J Y _ _ _ _ _ _ _ C p T₀ B _ rows X tg w N q₀ x₀ y₀ xB xC Sn qa
  dsimp only [LdLinPpT.cZV, LdLinC.cZV, LdLinPpT.QV, LdTcV.front, LdLinPpT.QVt, LdTcV.consSh,
    LdTcV.consLo, LdLinPpT.cVf, LdLinPpT.rd, ldHqW_fF, ldHqW_tie₃, ldHqW_tie₂, ldHqW_tie₁,
    ldHqW_tieF, ldHqW_rep₁, ldHqW_rep₂]
  dsimp only [LdLinPpT.QA, LdLinPpT.QAt, LdTcA.front, LdTc.front, ldHqC_shQ, ldHqC_loQ, ldHqC_base,
    ldHqC_St, LdLinPpT.qB₀, LdLinPpT.qB₁, LdLinPpT.qB₂, LdLinPpT.qB₃, ldHqR_D₁, ldHqR_D₂, ldHqR_D₃,
    ldHqO_St, ldHqO_base, ldHqO_fx, ldHqO_bOneP, ldHqO_qEndP, LdRowsD.oneVP, LdTcV.consLo,
    LdTcV.nil, ldHqX_run, ldHqX_d, ldHqX_d', ldHqX_kp, ldHqD_G, ldHqD_kp, ldHqD_B, ldHqD_Sb,
    ldHqD_sl, ldHqD_Z, ldHqD_t, ldHqD_L, ldHqD_pre]
  refine chainVFull_appOf rfl
    (chainVFull_appOf rfl (chainVFull_appOf rfl (chainVFull_appOf rfl (chainVFull_appOf rfl ?_))))
  exact chainVFull_appOf (chainVFull_oneOf (ldRunFull_loV X.run _ _ _ _ _ _ _)) rfl

set_option maxHeartbeats 1000000 in
theorem ldHonEq_obj : Spec.ldHonEq_obj := fun _ E _ _ _ _ _ R =>
  (ldHonEq_tests E _ _ _ _ _ _ (R.TB₀.withRest (R.XB.full.one R.tgB R.wXB)) R.N R.q₀B
      (R.XB.full.bOneP R.N) (fun _ _ _ _ => True) R.x₀ R.y₀ (R.XB.full.oneA R.wXB).cA
      (R.XB.full.oneA R.wXB).same R.xB R.xC R.toPp.D.SnB R.toPp.qaB
      (R.XB.full.oneVP R.N R.q₀B R.wXB)).trans
    (ldHonEq_rest E _ _ _ _ _ _ R.TB₀ _ _ R.XB R.tgB R.wXB R.N R.q₀B R.x₀ R.y₀ R.xB R.xC
      R.toPp.D.SnB R.toPp.qaB)

end Cb
