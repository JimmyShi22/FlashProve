-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/Cpp/AnswersObject.lean: at every three protocols over the configuration with the
written honest side (`codingCells`, Johnson/Flat/CodingCells.lean): the object's out-of-domain (OOD)
answers, spelled, are the answers of the committer that runs. Statements and proofs.
Limits. Values in a field, at the full-size shape. No binding of the commitment (the opening form,
`BindsWith`, VerifiableInference/MoreStatements.lean), no correctness of extraction and no index
privacy is stated here. Nothing on any program.

-/
import Johnson.Bind.Cpp.AnswersFull
import Johnson.Goal.Conditions.DescribeTermsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace Bind.Cpp
open Iop Prob Cb Cb.Ood Blocks Hiop OnBytes.Flat OnBytes.Slice Inst.Model VerifiableInference

/-- **The object's answers, unfolded**: general in the sizes, the claims, the three protocols and
their honest provers: the sample map's values on the messages that hold the matrix. -/
theorem obj_answers (S : Sz) (Z : Sample GE S.En) (cut : ℕ) (N : MatrixNums) {X : Type} (pp : ScalesAndPolicy)
    (req : X → Instance ppref)
    (F : Files (DecR.configurationOfStoredTable (claimsLedgerOnAt (S.toDecR Z cut) N pp req)
      (relationsAndEncodingOfClaims _ (codingCells S Z cut N pp req)))) (P : F.Provers)
    (M : Cells (S.toDecR Z cut) N) (r : (F.withProvers P).EncodingRandomness) (sd : (F.withProvers P).OutOfDomainSeed) :
    ((F.withProvers P).recOf M r sd).2 =
      (S.toDecR Z cut).ix.ZR.val sd (honestMsgs S (cellWords S Z cut N M r.1)) := rfl

end Bind.Cpp

namespace Bind.Cpp
open VerifiableInference VerifiableInference.OnPublicFiles
open OnBytes.Flat OnBytes.Slice Hiop
open Inst.Model (ScalesAndPolicy)

/-- **At every honest side that is the written one.** The pads are handed in twice: as the object
has them, and as the coins' words read in the field. -/
theorem answersAre_of_eq (pp : ScalesAndPolicy)
    (E : Coding (claimsReqAt (frS.toDecR frZ 402653181) numsRef pp))
    (hE : E = codingCells frS frZ 402653181 numsRef pp Subtype.val)
    (F : Files (DecR.configurationOfStoredTable (claimsReqAt (frS.toDecR frZ 402653181) numsRef pp) (relationsAndEncodingOfClaims _ E)))
    (P : F.Provers) (M : Cells (frS.toDecR frZ 402653181) numsRef) (r : (F.withProvers P).EncodingRandomness)
    (sd : (F.withProvers P).OutOfDomainSeed) (x : Coins)
    (hη : HEq r.1 (fun b j => toF (x.pad b.val j.val) : PadsOf frS 402653181)) :
    (OnBytes.K.IdTable.spellAns 11 1 ((F.withProvers P).recOf M r sd).2).map OnBytes.E.triple =
      Bind.Twin.answers shapeFull (x.table (entryOfCells M))
        ((OnBytes.K.IdTable.spellSeedL 29 1 sd).map fun y =>
          (y.1.map OnBytes.E.triple, y.2.triple)) := by
  subst hE
  have hr : r.1 = (fun b j => toF (x.pad b.val j.val) : PadsOf frS 402653181) := eq_of_heq hη
  have e : ((F.withProvers P).recOf M r sd).2 =
      (frS.toDecR frZ 402653181).ix.ZR.val sd
        (honestMsgs frS (cellWords frS frZ 402653181 numsRef M r.1)) :=
    obj_answers frS frZ 402653181 numsRef pp Subtype.val F P M r sd
  rw [e, hr]
  exact answers_full M _ (x.table (entryOfCells M)) (fun _ _ _ => rfl) (fun _ _ _ _ => rfl) sd

end Bind.Cpp

#print axioms Bind.Cpp.obj_answers
#print axioms Bind.Cpp.answersAre_of_eq
