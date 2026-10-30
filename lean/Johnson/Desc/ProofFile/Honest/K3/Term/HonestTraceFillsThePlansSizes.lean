-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT ANY FILLING.
Johnson/Desc/ProofFile/Honest/K3/Term/HonestTraceFillsThePlansSizes.lean: the honest side of the
kind "lookup" (K3), at the lookups on the calls: the two named readings "the messages' cells are the
list's" (MatsAre, Johnson/Desc/First/Look/K3CallerLay.lean; CellsAre, K3CallerAttMeans.lean) can be
met at the lists of the honest trace.

Why it is a question. MatsAre is an equation of whole functions, at all numbers, rows and columns,
and what is read off the messages is 0 outside the sizes of the smallness test's record (szOf: the
record's number of matrices; rows and columns of the entries of its list). The honest trace is 0
outside the shapes of the plans' lists (InShape). The two bounds are one where the record has the
plan's list and its number of matrices is the list's length.

What is defined.
  restrictedToTheSizes: a list of integer matrices, at the places inside given sizes.
  RecordHasThePlansMatrices: the premise on the record. On public data.
What is shown.
  honestTraceIsItsRestrictionToTheSizes: under that premise a link's list in the honest trace is its
    own restriction, laid out again with 0 outside. At every index and request.
  plansOwnRecordHasThePlansMatrices, lookupsRecordHasThePlansMatrices,
  recordAtTheLinkHasThePlansMatrices: in scope the premise holds, for a link below 25, of the record
    of the link's plan under its three names in the library.
  messagesHoldTheTraceWhereTheSymbolsPackIt: MatsAre at the link's list in the honest trace, where
    the committed symbols are the packing of the trace's restriction (BaseAt).
  attentionMessagesHoldTheTraceWhereTheSymbolsPackIt: the same for CellsAre.
  attentionSizesFitAtThePlansShape: in scope AttFits holds at a place whose lookup shape is the
    plan's.

Not claimed: that any committed symbols are that packing; that a verifier's block accepts; anything
on soundness, completeness or zero knowledge.
-/
import Johnson.Goal.HonestTrace.FullInScope
import Johnson.Goal.HonestTrace.FullPlanesInScope
import Johnson.Goal.HonestTrace.PlanMarksInScope
import Johnson.Goal.Meaning.HidPlanNM
import Johnson.Goal.Meaning.AttNumsScope
import Johnson.HonestTrace.PlanLabelsOfMarks
import Johnson.Desc.ProofFile.Honest.K3.Law.TiesSealed
import Johnson.Desc.First.Look.K3CallerLay
import Johnson.Desc.First.Look.K3CallerAttMeans

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open OnBytes (OracleShape)
open OnBytes.Model (HTailF2)
open OnBytes.HonestTrace (theTrace planMats fsAt)
open OnBytes.Model.Verify (publicOf)
open OnBytes.Road (Hd.shapeA)
open OnBytes.Road.L5 (Zs dimOf)
open OnBytes.Road.Rows (callsOf)
open Inst.Model (Instance ppref ScalesAndPolicy)
open Cb.Pv.Tail (Size BaseAt)
open VerifiableInference.Desc.First.Look (Place Sent laySg attSg MatsAre CellsAre szOf zsOf symAt
  sigListCalls seatCalls ownPart lay_mats_cast attCells_cast)

/-- **A list of integer matrices at the places inside given sizes**: matrix, column, row. -/
def restrictedToTheSizes (sizes : Size) (list : Zs) :
    ∀ matrix : Fin sizes.NM, Fin (sizes.k matrix) → Fin (sizes.m matrix) → ℤ :=
  fun matrix column row => list matrix.val row.val column.val

/-- **The record of a smallness test has the list of matrices of the plan of a link, and its
number of matrices is that list's length.** On public data. In scope it holds of the plan's own
record (plansOwnRecordHasThePlansMatrices and its two fellows). -/
structure RecordHasThePlansMatrices (publicRecord : OnBytes.Model.Verify.Public) (link : ℕ)
    (tail : HTailF2) : Prop where
  /-- the record's list is the plan's -/
  sameMatrices : tail.mats = planMats publicRecord link
  /-- the record's number of matrices is the length of its list -/
  numberIsTheListsLength : tail.NM = tail.mats.size

/-- **A link's list in the honest trace is its own restriction to the record's sizes, with 0
outside.** -/
theorem honestTraceIsItsRestrictionToTheSizes (publicRecord : OnBytes.Model.Verify.Public)
    (index : Cm.Idx) (request : Instance ppref) {link : ℕ} {tail : HTailF2}
    (record : RecordHasThePlansMatrices publicRecord link tail) :
    theTrace publicRecord index request link = zsOf (szOf tail)
      (restrictedToTheSizes (szOf tail) (theTrace publicRecord index request link)) := by
  funext matrix row column
  unfold zsOf
  by_cases inside :
      matrix < (szOf tail).NM ∧ column < (szOf tail).k matrix ∧ row < (szOf tail).m matrix
  · rw [dif_pos inside]
    rfl
  · rw [dif_neg inside]
    refine OnBytes.HonestTrace.trFull_out publicRecord _ index request fun inShape => inside ?_
    obtain ⟨matrixIsListed, rowIsInside, columnIsInside⟩ := inShape
    rw [← record.sameMatrices] at matrixIsListed rowIsInside columnIsInside
    refine ⟨?_, columnIsInside, rowIsInside⟩
    show matrix < tail.NM
    rw [record.numberIsTheListsLength]
    exact matrixIsListed

section InScope
variable {files : VerifierAndGoals.PublicFiles} {settings : ScalesAndPolicy} {layout : Option ByteArray}
  {publicRecord : OnBytes.Model.Verify.Public}

/-- In scope: the record of the link's plan, under the name Meaning.tlAt. -/
theorem plansOwnRecordHasThePlansMatrices (filesAreInScope : VerifierAndGoals.InScope files = true)
    (filesAreRead : VerifierAndGoals.readFiles files = .ok settings)
    (publicPartIsRead : publicOf files.pol files.KL layout = .ok publicRecord) {link : ℕ}
    (linkIsSmall : link < 25) :
    RecordHasThePlansMatrices publicRecord link (Meaning.tlAt publicRecord link) :=
  ⟨(OnBytes.HonestTrace.planMats_eq publicRecord link).symm,
    Meaning.nm_of_core publicPartIsRead
      (OnBytes.Road.Hd.core_of_scope filesAreInScope filesAreRead publicPartIsRead) linkIsSmall⟩

/-- In scope the lookups' name of that record and the library's are one. -/
theorem lookupsRecordIsThePlansOwn (filesAreInScope : VerifierAndGoals.InScope files = true)
    (filesAreRead : VerifierAndGoals.readFiles files = .ok settings)
    (publicPartIsRead : publicOf files.pol files.KL layout = .ok publicRecord) {link : ℕ}
    (linkIsSmall : link < 25) :
    tlOf publicRecord link = Meaning.tlAt publicRecord link := by
  have marks := OnBytes.HonestTrace.planMarks_in_scope filesAreInScope filesAreRead publicPartIsRead
  have step := OnBytes.HonestTrace.stepOf_two marks.p4
  have headLink : linkH publicRecord = 24 := by unfold linkH; rw [step, marks.groups]
  unfold tlOf Meaning.tlAt
  rw [headLink, step, if_neg (by omega : ¬ 24 < link)]
  by_cases linkIsTheHeads : link = 24
  · simp [linkIsTheHeads]
  · by_cases linkIsEven : link % 2 = 0 <;> simp [linkIsTheHeads, linkIsEven]

/-- In scope: the same record under the lookups' name tlOf. -/
theorem lookupsRecordHasThePlansMatrices (filesAreInScope : VerifierAndGoals.InScope files = true)
    (filesAreRead : VerifierAndGoals.readFiles files = .ok settings)
    (publicPartIsRead : publicOf files.pol files.KL layout = .ok publicRecord) {link : ℕ}
    (linkIsSmall : link < 25) :
    RecordHasThePlansMatrices publicRecord link (tlOf publicRecord link) := by
  rw [lookupsRecordIsThePlansOwn filesAreInScope filesAreRead publicPartIsRead linkIsSmall]
  exact plansOwnRecordHasThePlansMatrices filesAreInScope filesAreRead publicPartIsRead linkIsSmall

/-- In scope: the same record as the first chain's description finds it at the link. -/
theorem recordAtTheLinkHasThePlansMatrices (filesAreInScope : VerifierAndGoals.InScope files = true)
    (filesAreRead : VerifierAndGoals.readFiles files = .ok settings)
    (publicPartIsRead : publicOf files.pol files.KL layout = .ok publicRecord) {link : ℕ}
    (linkIsSmall : link < 25) {tail : HTailF2}
    (found : VerifiableInference.Desc.First.Look.tlAt publicRecord link = some tail) :
    RecordHasThePlansMatrices publicRecord link tail := by
  have recordsAreOne : tlOf publicRecord link = tail := by
    rw [Ties.tlOf_eq_tlAt publicRecord link, found]
    rfl
  rw [← recordsAreOne]
  exact lookupsRecordHasThePlansMatrices filesAreInScope filesAreRead publicPartIsRead linkIsSmall

/-- **In scope the lookup's record and attention's sizes fit**, at a place whose lookup shape is the
plan's. -/
theorem attentionSizesFitAtThePlansShape (filesAreInScope : VerifierAndGoals.InScope files = true)
    (filesAreRead : VerifierAndGoals.readFiles files = .ok settings)
    (publicPartIsRead : publicOf files.pol files.KL layout = .ok publicRecord) {group : ℕ}
    (groupIsSmall : group < 12) {place : Place}
    (placeHasThePlansShape : place.fs = fsAt publicRecord group) :
    Cb.Rider.AttFits place.fs (dimOf (Hd.shapeA publicRecord group)) (callsOf place.fs) := by
  rw [placeHasThePlansShape]
  exact Meaning.Att.attFits_in_scope filesAreInScope filesAreRead publicPartIsRead groupIsSmall

end InScope

/-- **The messages of a layers' link or of the head's hold the link's list in the honest trace**,
where the committed symbols are the packing of the trace's restriction to the record's sizes. -/
theorem messagesHoldTheTraceWhereTheSymbolsPackIt (publicRecord : OnBytes.Model.Verify.Public)
    (index : Cm.Idx) (request : Instance ppref) {link : ℕ} {tail : HTailF2}
    (record : RecordHasThePlansMatrices publicRecord link tail) (place : Place) (sent : Sent)
    (radius : OracleShape → Nat) (weightsOracle : Cb.OMsg Cb.Gl.E)
    (weightsReading : weightsOracle.Msg → ℕ → ℕ → Cb.Gl.E) (weightRows weightColumns : Nat)
    (messages : (laySg place sent radius weightsOracle).Msg)
    (symbolsPackTheTrace : BaseAt
      (symAt sent.codes (sigListCalls sent radius place.link) (seatCalls sent place.link) tail
        (ownPart messages))
      (restrictedToTheSizes (szOf tail) (theTrace publicRecord index request link))) :
    MatsAre place tail sent radius weightsOracle weightsReading weightRows weightColumns messages
      (theTrace publicRecord index request link) := by
  rw [honestTraceIsItsRestrictionToTheSizes publicRecord index request record]
  exact lay_mats_cast messages _ symbolsPackTheTrace

/-- **The messages of an attention link hold the link's list in the honest trace**, where the
committed symbols are the packing of the trace's restriction to the record's sizes. -/
theorem attentionMessagesHoldTheTraceWhereTheSymbolsPackIt
    (publicRecord : OnBytes.Model.Verify.Public) (index : Cm.Idx) (request : Instance ppref)
    {link : ℕ} {tail : HTailF2} (record : RecordHasThePlansMatrices publicRecord link tail)
    (place : Place) (shape : OnBytes.Attention.Shape) (sent : Sent) (radius : OracleShape → Nat)
    (messages : (attSg place sent radius).Msg)
    (symbolsPackTheTrace : BaseAt
      (symAt sent.codes (sigListCalls sent radius place.link) (seatCalls sent place.link) tail
        messages) (restrictedToTheSizes (szOf tail) (theTrace publicRecord index request link))) :
    CellsAre place shape tail sent radius messages (theTrace publicRecord index request link) := by
  rw [honestTraceIsItsRestrictionToTheSizes publicRecord index request record]
  exact attCells_cast messages _ symbolsPackTheTrace

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.honestTraceIsItsRestrictionToTheSizes
#print axioms ProofFile.Honest.K3.Term.plansOwnRecordHasThePlansMatrices
#print axioms ProofFile.Honest.K3.Term.lookupsRecordIsThePlansOwn
#print axioms ProofFile.Honest.K3.Term.lookupsRecordHasThePlansMatrices
#print axioms ProofFile.Honest.K3.Term.recordAtTheLinkHasThePlansMatrices
#print axioms ProofFile.Honest.K3.Term.attentionSizesFitAtThePlansShape
#print axioms ProofFile.Honest.K3.Term.messagesHoldTheTraceWhereTheSymbolsPackIt
#print axioms ProofFile.Honest.K3.Term.attentionMessagesHoldTheTraceWhereTheSymbolsPackIt
