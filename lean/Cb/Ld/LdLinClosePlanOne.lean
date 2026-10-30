-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinClosePlanOne.lean: book-keeping for the last part of an interactive oracle proof. All
linear constraints (rows) that an earlier sub-protocol (the preamble) has left open, on all oracles
that are still open, are the input of one proximity test (a whole test): the rest of the plan
without a splitting, with one group.
Definitions and statements (in `Cb.Spec`); the proofs are in Cb/Ld/LdLinClosePlanOneProofs.lean.
It uses Cb/Ld/LdLinClosePlanRows.lean (rows sorted into whole tests) and
Cb/Ld/LdLinCloseDemand.lean (the plan's two tests; positions add up; `Spec.ldLinPlan_tail`: the test
for linear constraints with the plan's closing as a tail). By composition only.
What the preamble left is the signature `C.Sa` with its base joint `C.Ab`
(Cb/Ld/LdLinClosePre.lean).
A whole test on a group (`LdRunD`, Cb/Ld/LdLinCloseRuns.lean) runs its bridge and then an end block
on the members' codes side by side; the end block is a parameter, in the protocol a proximity test.
`TailTr`, a tail of a chain, asks of a reduction from a joint to a joint whose statements have no
oracles the bundle `IOR.GoodT` and three further clauses, `noHid`, `tied` and `bears`, which
Cb/Ld/LdTowerKit.lean states (through `IOR.Tied`, Ior/Batch.lean, and `IOR.Bears`, Ior/Bears.lean).
`IOR.GoodT` (likewise `IOR.Good`, Ior/Chain.lean) bundles what is asked of one reduction, with its
honest side, between two joints, at given numbers; among its clauses: completeness between the
honest relations, outside sets of verifier randomness whose probabilities further clauses bound by
the numbers; round-by-round knowledge soundness (`Know`) between the relaxed relations, on the input
joint's set of statements, with a given extractor, at the numbers' list of errors; and one on
honest-verifier zero knowledge.

The case. After the plan's two tests the oracle messages `p.S₂` are left, and a finite family of
rows on what the preamble left. One test X takes all rows (`X.now b` for every b) on a group that
holds all oracle messages that are left, and keeps nothing (`X.kp o` for no o).
In this case "each row reads entries of one group" asks nothing: it holds at every claim, whatever
the rows' coefficients are. So this case also serves a preamble whose rows have coefficients that
are free data of its state.

Main names:
  `Spec.ldRowsOne_three`: the three clauses that a plan asks of "the rest": what is left says Ab
    (`p.SaysA`); the closing `X.one tgA w₀` is in order (`Q.OK`, Cb/Ld/LdLinCloseChain.lean); it
    needs at most `X.t` long positions of each oracle message that is left, and nothing of the
    further oracles. Asked: X takes all rows and keeps nothing; `C.Ab` says, in the exact and in the
    relaxed form, exactly "all rows hold"; every oracle message that a row reads is kept at the
    plan's two bridges; the test's own hypotheses (`X.run.OK`); q₀ holds of the empty set.
  `Spec.ldRowsOne_tail`: so, under the premises of `Spec.ldRowsOne_three` and those of
    `Spec.ldLinPlan_tail` (Cb/Ld/LdLinCloseDemand.lean) that are not on "the rest" (ι not empty
    among them, and that `p.restG` is "rest"), the test for linear constraints with the plan's three
    tests is a tail, from the claim on the encoded index to the trivial statement: no hypothesis on
    "the rest" is left but the third test's own, the other premises of `Spec.ldRowsOne_three`, and
    the inequalities, and whatever the arguments hold as proofs.

Notation: `on0`: a predicate on `C.P.D.X.Row → ι → E` and `C.P.D.X.Rec`; `εf`: a natural number;
`Sn`: the honest senders, and the numbers of the three sendings (`C.P.Snd`, Cb/Ld/LdLin.lean); `qa`,
`q₀`: predicates on finite sets of positions (of `C.P.Ea`, of `C.E₀`); `ba`: a natural number for
each oracle message of `C.Sa`; `d`: a value of `C.P.W0`; `w₀` (in the statements): a value of
`(p.S₂.sub X.kp).Wit × C.Wpa`.

Limits: this file says nothing on several groups (Cb/Ld/LdLinClosePlanRows.lean, with its warning on
`X.Supp` under Limits), and nothing on the batch. It does not say that the hypotheses can be met
together at a concrete code (`ldRowsOne_three` is used in the proof of `stdPO_three`,
Cb/Obj/LdObjectPartPlanProofs.lean).

(1) One group for all that the preamble left is an instance of this protocol's technical report
(lean/CREDITS.md; equal base codes), which has one test for each group.
(2) Rows whose coefficients are free data of the claim are wider than the report's rows (a form
of the configuration at a state, with a public target); here that is harmless, since nothing is
asked of the coefficients but that every oracle message that a row reads is kept at the plan's two
bridges.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLinClosePlanRowsProofs
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

/-- The test X, then nothing. -/
def LdRowsD.one {E : Type} [Field E] [Fintype E] {S : Sig E} {E₀ : ExtSpec}
    {Wp Cl B : Type} [Fintype B] {rows : B → Slf E Cl S.Ent} (X : LdRowsD S E₀ Wp rows)
    (tg : Cl → B → E) (w₀ : (S.sub X.kp).Wit × Wp) :
    LdRowsQ S E₀ Wp rows tg :=
      LdRowsQ.cons X (LdRowsQ.nil (S.sub X.kp) E₀ Wp X.rest (fun cl b => tg cl b.1) w₀)

/-- the data of the plan's tests, with "the rest" := the closing R of the preamble's rows -/
@[reducible] def LdLinPlT.withRest {E ι κ J Y : Type} [Field E]
    [Fintype E] [Fintype Y] [Fintype κ] [Fintype J] {C : LdLinC E ι κ J Y}
    {p : LdLinPl C} (T : LdLinPlT p) {B : Type} {rows : B → Slf E C.Sta p.S₂.Ent}
    {tg : C.Sta → B → E} (R : LdRowsQ p.S₂ C.E₀ C.Wpa rows tg) : LdLinPlT p :=
  { T with Q' := R.Q, fa := R.fx }

namespace Spec
section
variable (E ι κ J Y : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

/-- The three clauses. -/
def ldRowsOne_three : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPl C) (B : Type) [Fintype B] (rowsA : B → Slf E C.Sta C.Sa.Ent)
      (tgA : C.Sta → B → E) (X : LdRowsD p.S₂ C.E₀ C.Wpa (p.rowsL rowsA))
      (w₀ : (p.S₂.sub X.kp).Wit × C.Wpa) (q₀ : Finset C.E₀.Pos → Prop),
    (∀ b, X.now b) → (∀ o, ¬ X.kp o) →
    (∀ sa y m wp, C.Ab.rel sa y (m, wp) ↔ rowsHold rowsA tgA sa (C.Sa.ents m)) →
    (∀ sa y m wp, C.Ab.relR (sa, y) (m, wp) ↔ rowsHold rowsA tgA sa (C.Sa.ents m)) →
    (∀ b st (a : C.Sa.O) j,
      rowsA b st ⟨a, j⟩ ≠ 0 → ∃ h : p.kp₁ (.inl (.inl (.inl a))), p.kp₂ ⟨_, h⟩) →
    X.run.OK → q₀ ∅ →
    p.SaysA (X.one tgA w₀).Q.base (X.one tgA w₀).fx ∧
    (X.one tgA w₀).Q.OK ∧
    ∀ V, (X.one tgA w₀).Q.q V → p.S₂.qFam q₀ (fun _ => X.t) V

/-- States, for ι not empty and under the premises below: the test with the plan's three tests is a
tail. T gives the first two tests; its "rest" is replaced by the one test X. -/
def ldRowsOne_tail : Prop :=
  ∀ (C : LdLinC E ι κ J Y) (p : LdLinPl C) (T : LdLinPlT p) (B : Type) [Fintype B]
      (rowsA : B → Slf E C.Sta C.Sa.Ent) (tgA : C.Sta → B → E)
      (X : LdRowsD p.S₂ C.E₀ C.Wpa (p.rowsL rowsA)) (w₀ : (p.S₂.sub X.kp).Wit × C.Wpa)
      (on0 : (C.P.D.X.Row → ι → E) → C.P.D.X.Rec → Prop) (εf : ℕ) (Sn : C.P.Snd)
      (qa : Finset C.P.Ea.Pos → Prop) (d : C.P.W0) (q₀ : Finset C.E₀.Pos → Prop) (ba : C.Sa.O → ℕ),
    C.P.FoldErr on0 εf → Function.Injective C.P.D.py → Sn.OK →
    (∀ sa m, p.restG.val sa (p.G₂.msg (C.S.res (T := OMsg.Msg) p.kp₁ m)) = C.rest sa (C.aM m)) →
    T.D₁.OK → T.D₂.OK → (∀ b, X.now b) → (∀ o, ¬ X.kp o) →
    (∀ sa y m wp, C.Ab.rel sa y (m, wp) ↔ rowsHold rowsA tgA sa (C.Sa.ents m)) →
    (∀ sa y m wp, C.Ab.relR (sa, y) (m, wp) ↔ rowsHold rowsA tgA sa (C.Sa.ents m)) →
    (∀ b st (a : C.Sa.O) j,
      rowsA b st ⟨a, j⟩ ≠ 0 → ∃ h : p.kp₁ (.inl (.inl (.inl a))), p.kp₂ ⟨_, h⟩) →
    X.run.OK → q₀ ∅ → (∀ W, C.Sa.qFam q₀ ba W → qa W) →
    (∀ a, T.D₁.need (T.D₂.need fun _ => X.t) (.inl (.inl (.inl a))) ≤ ba a) →
    (∀ a, T.D₁.need (T.D₂.need fun _ => X.t) (.inl (.inl (.inr a))) ≤ Sn.tW a) →
    (∀ a, T.D₁.need (T.D₂.need fun _ => X.t) (.inl (.inr a)) ≤ Sn.tU a) →
    (∀ a, T.D₁.need (T.D₂.need fun _ => X.t) (.inr a) ≤ Sn.tO a) →
    TailTr
      (C.P.linC on0 Sn εf (C.cZ (T.withRest (X.one tgA w₀)).Q (T.withRest (X.one tgA w₀)).fq) d).R
      (C.P.linC on0 Sn εf (C.cZ (T.withRest (X.one tgA w₀)).Q (T.withRest (X.one tgA w₀)).fq) d).H
      (C.P.j0 on0) trivRels
      (C.P.linC on0 Sn εf (C.cZ (T.withRest (X.one tgA w₀)).Q (T.withRest (X.one tgA w₀)).fq) d).ext
      (C.P.linC on0 Sn εf (C.cZ (T.withRest (X.one tgA w₀)).Q (T.withRest (X.one tgA w₀)).fq) d).P
      (C.P.q0 qa)

end
end Spec
end Cb
