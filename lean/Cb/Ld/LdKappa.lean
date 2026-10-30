-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdKappa.lean: one number κ above every round-by-round error, as a probability, of the
protocol's sub-protocols (the object's five lists): the record `Z.Kap κ`, and the statement that,
with the request's own clauses "at most κ", it gives "every round's error is at most κ". (not all
hypotheses are named here: see `Spec.ldKappa`)

Two records and one statement (`Cb.Spec.ldKappa`); its proof is in Cb/Ld/LdKappaProofs.lean. Many
statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).
A round's error e is a count of values of its verifier message: how many may let a prover that has
lost escape (`Err`, Iop/Rbr.lean); as a probability it is at most κ if e ≤ κ · v, with v the number
of all values of that message (`Err.Below`, Iop/InteractiveOracleProof.lean). These errors are numbers that the
object lists (`obj.nums`, Cb/Obj/LdObject.lean: a `SubsR.Nums`, Hiop/RecBuild.lean, whose five
entries each have the data field `err`): that a sub-protocol is sound at the numbers that are listed
for it is no statement of this file (the premise `Z.HypRef` asks it of the link that each closing's
fold move holds (`LdFoldD.Hyp.good`, Cb/Req1/LdSegKit.lean): `req.proto.segs`); for the object that
tie is `Spec.ldObj_hyp` (Cb/Obj/LdObject.lean), under `Obj.OK L`, in the sense of `SubsR.HypK`
(Hiop/RecBuild.lean) (that condition itself asks soundness of the parts one level down: the tie
carries soundness, it does not found it).

Why: κ is above the largest round error over five lists:
weights-formedness, the test for linear
constraints at one instance, the link, a request's preamble, the test at N instances. The request's
record has clauses "at most κ" (bFirst, bMore, bSegs, bTail, bLast: Cb/Req1/LdReqRefFinal.lean).

Here they are used, and the like is asked of the
other four lists.


Main names:
  `D.KapT T κ`: one whole test D on a group, with its tower T: the bridge's round: (bound on the
    list of the group's complex) · (the zero-evader's exceptional seeds) ≤ κ · (number of seeds);
    `T.Kap κ`: by recursion on the tower, on numbers: each fold's rounds, each code switch's two
    rounds, the base case's two rounds (Cb/Ld/LdKappaTow.lean).
  `Z.Kap κ`:
    wf: weights-formedness (`B.Kap`, Cb/Ld/LdKappaBat.lean): the sending's number; every round's
      error of each lookup, and of the batching of tensor rows, as a probability, is at most κ:
      these two are clauses on the blocks' lists of errors, not on numbers.
    lin: the core of the test for linear constraints at one instance: six numbers
      (Cb/Ld/LdKappaKit.lean); t₁, t₂, t₃: its closing's three tests.
    link: the link's core: four numbers; tK: its closing's test.
    linB: the core at N instances: six numbers (at the point the term of the polynomial identity
      occurs N times); t₁B, t₂B, t₃B: its closing's three tests, each with the error for one fixed
      instance: no factor N (so does this protocol's technical report (lean/CREDITS.md): shared
      rounds carry the joint error;
      the rounds that belong to a single instance carry that instance's error alone).
  `Spec.ldKappa`: for `more` a list of sendings and steps (`hm`): `Z.HypRef` at κ → `Z.Kap κ` →
    every round's error of the five lists, as a probability, is at most κ (`SubsR.Nums.Below`).
    `Z.HypRef`: conditions on the object at the reference request; at `more` the empty list each of
    `Z.HypRefS`, `Z.HypRefT`, `Z.HypRefA` and, for E of characteristic p, `Z.HypRefU` gives them.
    Used of `Z.HypRef`: the equation reqIs (which request stands in Z); the request's five clauses
    "below κ"; the seven equations "the whole test is its tower". Nothing else.

Notation: `Z`: the object (`LdObjZ`, Cb/Obj/LdObjectData.lean); `Z.HypRef`:
Cb/Obj/LdObjectDataRef.lean.

Limits: it says nothing on the size of κ: κ = ⊤ still meets every clause.
What still speaks of more than numbers. In `Z.Kap`: the lists of weights-formedness' lookups and
batching. In the request's clauses (Cb/Req1/LdReqRefFinal.lean, Cb/Req1/LdSegRefBelow.lean): each
closing's link's list; each body's lookups', sumchecks' and batchings' lists, and the other rounds
of its front (`front` of `LdRefD.Nums` asks `A.V.prog.Below κ`: the front's whole list of moves);
the final batching's list (bLast); the lists of the moves of `more` (bMore). For the group's own
link the list comes down to numbers (Cb/Ld/LdGroupLinkBelow.lean): not put in here.
This file says nothing on work: the bound with proof-of-work bits is not broken down.

(Broken down: `Spec.ldKappaW`, Cb/Ld/LdKappaW.lean.)
This file does not say
that the numbers which stand in the errors (bounds on lists, exceptional points of folds, agreement)
are what the codes have: asked elsewhere. It does not say that the record can be met at a finite κ:
a guard's matter.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdKappaObj
import Cb.Obj.LdObjectDataRef

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain
open scoped ENNReal

/-- One whole test with its tower: its numbers. -/
structure LdRunD.KapT {E : Type} [Field E] [Fintype E] {S : Sig E} (D : LdRunD S)
    (T : D.Tow) (κ : ℝ≥0∞) : Prop where
  bridge : ((D.L * D.Z.err : ℕ) : ℝ≥0∞) ≤ κ * (Fintype.card D.Z.D : ℝ≥0∞)
  tow    : T.Kap κ

section
variable {F E : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

/-- The record: the four lists that are not the request's. -/
structure LdObjZ.Kap (Z : LdObjZ F E) (κ : ℝ≥0∞) : Prop where
  /-- Weights-formedness. -/
  wf   : Z.R.Bw.Kap κ
  /-- The test for linear constraints at one instance. -/
  lin  : Z.R.W.O.toC.P.KapC Z.R.Sn Z.R.εf κ
  t₁   : Z.R.TP₀.D₁.KapT Z.tw₁ κ
  t₂   : Z.R.TP₀.D₂.KapT Z.tw₂ κ
  t₃   : Z.R.X.run.KapT Z.tw₃ κ
  /-- The link. -/
  link : Z.R.K.P.KapC Z.R.Sl Z.R.ε₀ Z.R.ε₁ κ
  tK   : Z.R.Kc.run.KapT Z.twK κ
  /-- The test at N instances. -/
  linB : Z.R.on.ol.toC.P.KapCB Z.R.SnB Z.R.εfB Z.R.N κ
  t₁B  : Z.R.TB₀.D₁.KapT Z.tw₁B κ
  t₂B  : Z.R.TB₀.D₂.KapT Z.tw₂B κ
  t₃B  : Z.R.XB.run.KapT Z.tw₃B κ

end

/-- States: under the hypotheses below (`Z.HypRef` at κ, `Z.Kap κ`), every round's error of the five
lists, as a probability, is at most κ. Limits: the head. -/
def Spec.ldKappa : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (Kc : Type) (p : ℕ)
      (Z : LdObjZ F E) (L : ℕ) (R : LdORE F E Kc) (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
      (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (a₁ : LdStage E Kc)
      (more : LdProg first.tgt a₁) (hm : more.All fun t => t = .send ∨ t = .step) (b : LdStage E Kc)
      (Ls : LdRefL E Kc R.ix a₁ b) (T : LdRefT R b)
      (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
      (q : Finset R.z.J.E.Pos → Prop) (κ : ℝ≥0∞),
    Z.HypRef p L R core first a₁ more hm b Ls T qφ q κ → Z.Kap κ → Z.R.toP.toT.obj.nums.Below κ

end Cb
