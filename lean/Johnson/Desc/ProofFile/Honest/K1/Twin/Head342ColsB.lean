-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Twin/Head342ColsB.lean: MADE BY PROGRAM OFF
Johnson/P4R/Head342Cols.lean UNDER A MAP OF NAMES AND ONE TURN OF THE MEANING: 2 OF ITS
DECLARATIONS: mats_342_of_b · matsP_342_b. THE PROOFS ARE COPIES.

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
in the theorems, explicit in the structure ReadsFenceB; "include dk" where the original's block
binds dk (no twin's statement names it; it is kept so that a copied call has the original's number
of arguments). Kept as in the original: its namespace, open, variable, section, set_option
and attribute lines, but for one prefix that makes dk implicit (in ArmAtReadsB.lean): there "omit dk
in" stands.
The namespace is the library's, so that a copied proof finds its callees without a sign turned; the
names with the suffix _b are not the library's.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P4R.Head342Cols
import Johnson.Desc.ProofFile.Honest.K1.Twin.Head342B
import Johnson.Desc.ProofFile.Honest.K1.Twin.HonestAt
import Johnson.Desc.ProofFile.Honest.K1.Twin.OpenAt342

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtFold

open ProofFile.Honest.FirstThread (honest)
open VerifiableInference.Desc (Strs Wit)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (CellsQ MsgT mgMore)
open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open OnBytes.Params (ReqLayout ReqShape)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (S Numbers Meaning pubFit flatPlacesOf FoldData FoldFacts)
open VerifiableInference.Desc.Sound (Frame MsgT onQ linksFull MgData mgAll)

/-- **The head's matrices are seated, at any columns below the bound.** -/
theorem mats_342_of_b {Xi P Tok : Type} {rows cols nR : ℕ} {Wp : OnBytes.Model.Verify.Public}
    (D : MgData Xi P Tok rows cols nR Wp)
    (Mg : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT))
    {ans : ℕ → ℕ → P × S → Strs → Wit (Fin rows → Fin cols → GE) Tok MsgT → Prop} {test : ℕ → S → Option String} (lay6 : ReqLayout)
    (num : ℕ → ℕ → ℕ) (Fr : Frame) (Rch : ℕ → (P × S) × Fr.E.Str → Prop) (d : FoldData)
    (reqW : P → Array UInt32)
    (hfit : pubFit (mgAll D Mg).more linksFull (flatPlacesOf linksFull true) = true)
    (FF : FoldFacts Rch (fun a => a.1) d reqW linksFull (flatPlacesOf linksFull true))
    (hd : d.sent = D.sent) (hlay : D.layout = lay6)
    (hC : seatsK6C D.arr D.N Wp lay6 num (num 24 0) 0 D.cs D.shape D.pubD.dS d.L d.M
      (D.sent.arrayOf.getD 24 #[]) (D.N.msgsAt (flatPlacesOf linksFull true)[342]?) = true)
    (Cols : ℕ → ℕ → Prop) (hCols : ∀ a c, Cols a c → a ≤ Wp.hS.NHf + 3) :
    ∀ a, Rch 342 a →
      onQ (Fr := Fr) D.N (honest (mgAll D Mg) ans test) linksFull (flatPlacesOf linksFull true) (fun a => a) 342 a →
      a.1.2.failed = none → ∀ aK, K9.segAt? a.1.2 = some aK →
      MatsSeated Cols D.arr D.N Wp (D.N.sent 24 0) aK num lay6 :=
  fun a hr ha hm aK hK =>
    matsSeated_of_C hC
      (stateIsPlan_342_b D Mg lay6 Fr d.L d.M hfit a ha hm
        (foldAt_of_facts D lay6 Fr Rch d reqW FF hd hlay 342 a hr hm) aK hK) Cols hCols

/-- **At the one matrix NHf + 2.** -/
theorem matsP_342_b {Xi P Tok : Type} {rows cols nR : ℕ} {Wp : OnBytes.Model.Verify.Public}
    (D : MgData Xi P Tok rows cols nR Wp)
    (Mg : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT))
    {ans : ℕ → ℕ → P × S → Strs → Wit (Fin rows → Fin cols → GE) Tok MsgT → Prop} {test : ℕ → S → Option String} (lay6 : ReqLayout)
    (num : ℕ → ℕ → ℕ) (Fr : Frame) (Rch : ℕ → (P × S) × Fr.E.Str → Prop) (d : FoldData)
    (reqW : P → Array UInt32)
    (hfit : pubFit (mgAll D Mg).more linksFull (flatPlacesOf linksFull true) = true)
    (FF : FoldFacts Rch (fun a => a.1) d reqW linksFull (flatPlacesOf linksFull true))
    (hd : d.sent = D.sent) (hlay : D.layout = lay6)
    (hC : seatsK6C D.arr D.N Wp lay6 num (num 24 0) 0 D.cs D.shape D.pubD.dS d.L d.M
      (D.sent.arrayOf.getD 24 #[]) (D.N.msgsAt (flatPlacesOf linksFull true)[342]?) = true) :
    ∀ a, Rch 342 a →
      onQ (Fr := Fr) D.N (honest (mgAll D Mg) ans test) linksFull (flatPlacesOf linksFull true) (fun a => a) 342 a →
      a.1.2.failed = none → ∀ aK, K9.segAt? a.1.2 = some aK →
      MatsSeated (fun μ _ => μ = Wp.hS.NHf + 2) D.arr D.N Wp (D.N.sent 24 0) aK num lay6 :=
  mats_342_of_b D Mg lay6 num Fr Rch d reqW hfit FF hd hlay hC _ (fun a _ h => by omega)

end VerifiableInference.Desc.Kinds.Head.Law.AtFold

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.mats_342_of_b
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.matsP_342_b
