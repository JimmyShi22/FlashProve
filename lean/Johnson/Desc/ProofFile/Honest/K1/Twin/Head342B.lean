-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Twin/Head342B.lean: MADE BY PROGRAM OFF Johnson/P4R/Head342.lean
UNDER A MAP OF NAMES AND ONE TURN OF THE MEANING: 4 OF ITS DECLARATIONS: sentIs_342_b ·
fresh_342_b · stateIsPlan_342_b · mats_342_b. THE PROOFS ARE COPIES.

This letter is for the honest run's own forms alone: no statement on any other party may take it.
NEVER ON SOUNDNESS's ROAD: at the meaning "honest" the
clauses noColl, shown and decodes are True by definition: a law at that meaning may stand beneath
statements on completeness or zero knowledge only, never beneath a statement on soundness.

The map of names. ReadsFence to ReadsFenceB; each twinned theorem n to n_b; the library's closed
facts at its wider table of names (mwMore) to their likes at mgMore, and its laws on the wider
meaning to their likes on "honest" over mgAll (both in Twin/HonestAt.lean, typed by hand).
The turn of the meaning. Where the elder has the wider meaning (mw1 Dm.N (d13 Dm) dk (mgAll Dm Mg₀),
or plus13 (d13 Dm) dk (mgAll Dm Mg₀)), the twin has honest (mgAll Dm Mg₀) ans test
(Johnson/Desc/ProofFile/Honest/Thread/First.lean): the meaning at which the honest thread's own
promise stands; at the item "tie": mgAll Dm Mg₀. The step down from mw1 to plus13 (inAt_down) falls.
The promise itself is the library's InAt: no new text of a promise.
Laid in, on no line of a statement: the letters ans and test, behind each block of letters: implicit
in the theorems, explicit in the structure ReadsFenceB; "include dk" where the elder's block binds
dk (no twin's statement names it any more; it is kept so that a copied call has the elder's number
of arguments). Kept as they stand in the elder: its namespace, open, variable, section, set_option
and attribute lines, but for one prefix that makes dk implicit (in ArmAtReadsB.lean): there "omit dk
in" stands.
The namespace is the library's, so that a copied proof finds its callees without a sign turned; the
names with the suffix _b are not the library's.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P4R.Head342
import Johnson.Desc.ProofFile.Honest.K1.Twin.HonestAt
import Johnson.Desc.ProofFile.Honest.K1.Twin.OpenAt342

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open ProofFile.Honest.FirstThread (honest)
open VerifiableInference.Desc (Strs Wit)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (CellsQ MsgT mgMore)
open OnBytes.Model (Fork)
open VerifiableInference.Desc.First (S HeadOwn)

end VerifiableInference.Desc.Kinds.Head.Law

namespace VerifiableInference.Desc.Kinds.Head.Law.AtFold

open ProofFile.Honest.FirstThread (honest)
open VerifiableInference.Desc (Strs Wit)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (CellsQ MsgT mgMore)
open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open OnBytes.Params (ReqLayout ReqShape)
open OnBytes.Model.Verify (borderOf)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (S ModelPart Numbers Meaning Pub More pubFit moreItem MoreName
  pubRowM pubRowOf pubStartM pubSets pubStep pubSets_succ FoldData FoldFacts)
open VerifiableInference.Desc.Sound (Frame MsgT onQ pubQ linksFull head_full MgData mgAll)
open VerifiableInference.Desc.Kinds.Head.Law.AtTable (asks_K6)

local notation "PS" => First.flatPlacesOf linksFull true

variable {Xi P Tok : Type} {rows cols nR : ℕ} {Wp : OnBytes.Model.Verify.Public}
  (D : MgData Xi P Tok rows cols nR Wp)
  (Mg : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT)) (lay6 : ReqLayout) (num : ℕ → ℕ → ℕ)
  (Fr : Frame)

variable {ans : ℕ → ℕ → P × S → Strs → Wit (Fin rows → Fin cols → GE) Tok MsgT → Prop} {test : ℕ → S → Option String}
local notation "MGA" => mgAll D Mg

/-- **The open segment's frame's five fields are the public terms, at 342.** -/
theorem sentIs_342_b (hfit : pubFit (honest (mgAll D Mg) ans test).more linksFull PS = true) (a : (P × S) × Fr.E.Str)
    (ha : onQ (Fr := Fr) D.N (honest (mgAll D Mg) ans test) linksFull PS (fun a => a) 342 a) (hm : a.1.2.failed = none) :
    First.FillSent.sentIsB D.pubD.dS 24 a.1.2 = true := by
  have h : (honest (mgAll D Mg) ans test).pub (moreItem (First.FillSent.sentName 24)) a.1 = true :=
    asked_more Fr D.N (honest (mgAll D Mg) ans test) linksFull PS (fun a => a) hfit 342 placeR place_342 a ha hm
      (First.FillSent.sentName 24) (sent_asked_342 D Mg)
  rw [VerifiableInference.Desc.K1.honest_pub_all] at h
  exact (First.pubAll_more_sentIs D.pubD Mg.pub 24 a.1).symm.trans h

/-- **The open segment's list of arrays is the public one, at 342.** -/
theorem fresh_342_b (hfit : pubFit (honest (mgAll D Mg) ans test).more linksFull PS = true) (a : (P × S) × Fr.E.Str)
    (ha : onQ (Fr := Fr) D.N (honest (mgAll D Mg) ans test) linksFull PS (fun a => a) 342 a) (hm : a.1.2.failed = none) :
    VerifiableInference.OnPublicFiles.linkFreshB (D.sent.arrayOf.getD 24 #[]) a.1.2 = true := by
  have h : (honest (mgAll D Mg) ans test).pub (.linkFresh 24) a.1 = true :=
    (Sound.onParts_of_on D.N (honest (mgAll D Mg) ans test) linksFull PS (fun a => a) 342 a ha hm).pub _
      (List.mem_append_left _ (fresh_open_342 (honest (mgAll D Mg) ans test).more hfit))
  exact h

/-- **At 342 itself every reader is a term off the public parameters.** -/
theorem stateIsPlan_342_b (Lp : K12.Door.Laid) (M : List OracleShape)
    (hfit : pubFit (honest (mgAll D Mg) ans test).more linksFull PS = true) (a : (P × S) × Fr.E.Str)
    (ha : onQ (Fr := Fr) D.N (honest (mgAll D Mg) ans test) linksFull PS (fun a => a) 342 a) (hm : a.1.2.failed = none)
    (F : FoldAt Lp M D.cs D.shape lay6 a.1.2) (aK : K9.Part)
    (hK : K9.segAt? a.1.2 = some aK) :
    StateIsPlan lay6 D.cs D.shape D.pubD.dS Lp M (D.sent.arrayOf.getD 24 #[])
      (D.N.msgsAt PS[342]?) a.1.2 aK := by
  have hL := link_of_seg hK
  obtain ⟨hst, hbk⟩ := seg_st_book hK
  have hlive : a.1.2.live = aK.L.check := by
    unfold First.S.live
    rw [hL]
  have hS := sentIs_342_b D Mg Fr hfit a ha hm
  have hfr := fresh_342_b D Mg Fr hfit a ha hm
  have hbo : First.bookAt D.N PS[342]? a.1.2 = true :=
    (Sound.onParts_of_on D.N (honest (mgAll D Mg) ans test) linksFull PS (fun a => a) 342 a ha hm).book
  unfold First.bookAt at hbo
  simp only [Bool.and_eq_true, beq_iff_eq] at hbo
  refine ⟨hK, ?_, ?_, ?_, ?_, arrays_of_fresh hfr hK, ?_, ?_, ?_, ?_, ?_⟩
  · intro born message
    exact First.FillSent.whereIs_of_sentIs hL hS born message
  · exact First.FillSent.link_of_sentIs hL hS
  · rw [← hlive]
    exact F.shape
  · rw [← hlive]
    exact F.layout
  · rw [hst]
    exact F.codes
  · rw [hst]
    exact F.msgs
  · rw [hbk]
    exact F.seats
  · rw [hbk, hbo.1.2, hbo.2]
  · rw [hst, hbo.2]

variable (Rch : ℕ → (P × S) × Fr.E.Str → Prop) (d : FoldData) (reqW : P → Array UInt32)

/-- **The head's matrices are seated, at the reached states at 342 inside the promise at 342.** -/
theorem mats_342_b (hfit : pubFit (honest (mgAll D Mg) ans test).more linksFull PS = true)
    (FF : FoldFacts Rch (fun a => a.1) d reqW linksFull PS)
    (hd : d.sent = D.sent) (hlay : D.layout = lay6)
    (hC : seatsK6C D.arr D.N Wp lay6 num (num 24 0) 0 D.cs D.shape D.pubD.dS d.L d.M
      (D.sent.arrayOf.getD 24 #[]) (D.N.msgsAt PS[342]?) = true) :
    ∀ a, Rch 342 a → onQ (Fr := Fr) D.N (honest (mgAll D Mg) ans test) linksFull PS (fun a => a) 342 a →
      a.1.2.failed = none → ∀ aK, K9.segAt? a.1.2 = some aK →
      MatsSeated (ColFour Wp.hS Wp.HLy (borderOf Wp.y)) D.arr D.N Wp (D.N.sent 24 0) aK num
        lay6 :=
  fun a hr ha hm aK hK =>
    matsSeated_of_C hC
      (stateIsPlan_342_b D Mg lay6 Fr d.L d.M hfit a ha hm
        (foldAt_of_facts D lay6 Fr Rch d reqW FF hd hlay 342 a hr hm) aK hK) _
      (fun x c h => by rcases h with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega)

end VerifiableInference.Desc.Kinds.Head.Law.AtFold

namespace P4

open ProofFile.Honest.FirstThread (honest)
open VerifiableInference.Desc (Strs Wit)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (CellsQ MsgT mgMore)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S hearsReply)
open VerifiableInference.Desc.K8 (ReadsQuiet.tables)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law
open VerifiableInference.Reads.AtSeat (Nums runIs_at_reach dressed_yes)
open Johnson.Desc.First.Walk.Tied (Reach RchAt reach_raw)
open ProofFile (Cl)
open Inst.Model (ScalesAndPolicy)

variable {P : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat} {Str : Type}

end P4

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.sentIs_342_b
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.fresh_342_b
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.stateIsPlan_342_b
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.mats_342_b
