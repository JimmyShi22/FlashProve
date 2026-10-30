-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdKappaLeast.lean: nothing is lost by passing from the largest round error to the records "at
most κ": under `Z.HypRef` at any κ', the records hold at κ if and only if every round's error of the
five lists, as a probability, is at most κ. A guard, for every object at once, against records that
would ask more of κ than the round errors do.

Statements (`Cb.Spec.ldKappa_conv`, `Cb.Spec.ldKappa_iff`, `Cb.Spec.ldKappaU_conv`); the proofs are
in Cb/Ld/LdKappaLeastProofs.lean. A round's error e is a count of values of its verifier message:
how many may let a prover that has lost escape (`Err`, Iop/Rbr.lean); as a probability it is at most
κ if e ≤ κ · v, with v the number of all values of that message (`Err.Below`, Iop/InteractiveOracleProof.lean). The
five lists are the errors of the protocol's sub-protocols: weights-formedness, the test for linear
constraints at one instance, the link, a request's preamble, the test at N instances. These errors
are numbers that the object lists (`obj.nums`, Cb/Obj/LdObject.lean: a `SubsR.Nums`,
Hiop/RecBuild.lean, whose five entries each have the data field `err`): that a sub-protocol is sound
at the numbers that are listed for it is no statement of this file (the premise `Z.HypRef` at κ'
asks it of the link that each of the request's fold moves holds (`LdFoldD.Hyp.good`,
Cb/Req1/LdSegKit.lean): `req.proto.segs`; `Spec.ldKappa_conv` and `Spec.ldKappa_iff` hand that
clause on as it is into `Z.HypRef` at κ); for the object that tie is `Spec.ldObj_hyp`
(Cb/Obj/LdObject.lean), under `Obj.OK L`, in the sense of `SubsR.HypK` (Hiop/RecBuild.lean) (that
condition itself asks soundness of the parts one level down: the tie carries soundness, it does not
found it).

Why: Cb/Ld/LdKappa.lean: `Z.HypRef` at κ → `Z.Kap κ` → every round's error of the five lists, as a
probability, is at most κ.
A reader may ask whether the premises can be met at any κ but ⊤. Each clause has the form e ≤ κ · v
with v ≥ 1, or "every round's error of a block's list, as a probability, is at most κ", and each
speaks of rounds that do occur in the five lists. So the way back holds too.
κ can be taken to be exactly the first count without work (`Nums.maxAll` at no work;
`Nums.below_iff`, Cond/ObjQuote.lean). This file does not say that that count is below ⊤. So the
records exclude nothing, and a bound on κ by way of the records is a bound on that count, and
conversely.

Main names:
  `Spec.ldKappa_conv`: `Z.HypRef` at any κ' (for instance ⊤) and every round's error of the five
    lists, as a probability, at most κ ⇒ `Z.HypRef` at κ and `Z.Kap κ`.
  `Spec.ldKappa_iff`: under `Z.HypRef` at κ': (`Z.HypRef` at κ ∧ `Z.Kap κ`) ↔ every round's error of
    the five lists, as a probability, is at most κ.
  `Spec.ldKappaU_conv`: the same way back for the record `Z.HypRefU` on the object
    (Cb/Ld/LdLayDTop.lean), for E of characteristic p.

Used of `Z.HypRef` at κ': all its clauses but the five "below κ'" are handed on as they are; the
equation reqIs and the seven equations "the whole test is its tower" carry the lists.

Notation: `Z`: the object (`LdObjZ`, Cb/Obj/LdObjectData.lean); `Z.HypRef`: `Z.Hyp` at the reference
request (Cb/Obj/LdObjectDataRef.lean); `Z.Kap κ`: the record of Cb/Ld/LdKappa.lean: the four lists
that are not the request's.

Limits: this is a guard in place of a numeral at a toy: it shows that the records can be met
wherever `Z.HypRef` (or `Z.HypRefU`) can; it shows nothing on the size of κ. This file says nothing
on the value of any number. The records on numbers of Cb/Ld/LdKappaList.lean (lookup, sumcheck,
batching) are not under `Z.Kap`, and the lookup's asks slightly more than its list at degenerate
parameters: for it the way back would fail there. This file says nothing on work (proof of work).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdKappa
import Cb.Ld.LdLayDTop

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain
open scoped ENNReal

namespace Spec

def ldKappa_conv : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (Kc : Type) (p : ℕ)
      (Z : LdObjZ F E) (L : ℕ) (R : LdORE F E Kc) (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
      (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (a₁ : LdStage E Kc)
      (more : LdProg first.tgt a₁) (hm : more.All fun t => t = .send ∨ t = .step) (b : LdStage E Kc)
      (Ls : LdRefL E Kc R.ix a₁ b) (T : LdRefT R b)
      (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
      (q : Finset R.z.J.E.Pos → Prop) (κ' κ : ℝ≥0∞),
    Z.HypRef p L R core first a₁ more hm b Ls T qφ q κ' → Z.R.toP.toT.obj.nums.Below κ →
    Z.HypRef p L R core first a₁ more hm b Ls T qφ q κ ∧ Z.Kap κ

def ldKappa_iff : Prop :=
  ∀ (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (Kc : Type) (p : ℕ)
      (Z : LdObjZ F E) (L : ℕ) (R : LdORE F E Kc) (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
      (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (a₁ : LdStage E Kc)
      (more : LdProg first.tgt a₁) (hm : more.All fun t => t = .send ∨ t = .step) (b : LdStage E Kc)
      (Ls : LdRefL E Kc R.ix a₁ b) (T : LdRefT R b)
      (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
      (q : Finset R.z.J.E.Pos → Prop) (κ' κ : ℝ≥0∞),
    Z.HypRef p L R core first a₁ more hm b Ls T qφ q κ' →
    ((Z.HypRef p L R core first a₁ more hm b Ls T qφ q κ ∧ Z.Kap κ) ↔ Z.R.toP.toT.obj.nums.Below κ)

def ldKappaU_conv : Prop :=
  ∀ (F E Fp : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] [Field Fp]
      [Fintype Fp] [Algebra Fp E] (Kc : Type) (p : ℕ) [CharP E p] (Z : LdObjZ F E)
      [∀ b, Fintype (Z.Zw.K.wfI Z.Zw.Rl b → E)] (L : ℕ) (R : LdORE F E Kc)
      (core : R.Cf.conf.PIdx × R.Cf.conf.Cells → Kc)
      (first : LdSendD (LdStage.start E Kc (R.O.jReq core))) (b : LdStage E Kc)
      (Ls : LdRefL E Kc R.ix first.tgt b) (T : LdRefT R b)
      (qφ : Finset (LdStage.start E Kc (R.O.jReq core)).J.E.Pos → Prop)
      (q : Finset R.z.J.E.Pos → Prop) (κ' κ : ℝ≥0∞) (V : Z.Zw.StdW Fp)
      (p₀ : LdLinPl R.O.d.ol.toC) (plR : R.Bn → R.S.Ent → Prop),
    Z.HypRefU p L R core first b Ls T qφ q κ' V p₀ plR → Z.R.toP.toT.obj.nums.Below κ →
    Z.HypRefU p L R core first b Ls T qφ q κ V p₀ plR ∧ Z.Kap κ

end Spec
end Cb
