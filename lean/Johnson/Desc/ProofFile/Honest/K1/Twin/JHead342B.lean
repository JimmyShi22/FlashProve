-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Twin/JHead342B.lean: MADE BY PROGRAM OFF
Johnson/Desc/K1/Law/JHead342.lean UNDER A MAP OF NAMES AND ONE TURN OF THE MEANING: 1 OF
ITS DECLARATIONS: jHead3_342_b. THE PROOFS ARE COPIES.

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
in the theorems, explicit in the structure ReadsFenceB; "include dk" where the source's block
binds dk (no twin's statement names it; it is kept so that a copied call has the source's number
of arguments). Kept as they stand in the source: its namespace, open, variable, section, set_option
and attribute lines, but for one prefix that makes dk implicit (in ArmAtReadsB.lean): there "omit dk
in" stands.
The namespace is the library's, so that a copied proof finds its callees without a sign turned; the
names with the suffix _b are not the library's.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K1.Law.JHead342
import Johnson.Desc.ProofFile.Honest.K1.Twin.Head342B
import Johnson.Desc.ProofFile.Honest.K1.Twin.HonestAt
import Johnson.Desc.ProofFile.Honest.K1.Twin.OpenAt342

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1
open ProofFile.Honest.FirstThread (honest)
open VerifiableInference.Desc (Strs Wit)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (CellsQ MsgT mgMore)
open OnBytes OnBytes.Params OnBytes.Model
open OnBytes.Model.Verify (borderOf)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S Numbers Meaning pubFit flatPlacesOf FoldData FoldFacts)
open VerifiableInference.Desc.Sound (Frame MsgT onQ linksFull MgData mgAll)
open VerifiableInference.Desc.Kinds VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law (callKeys)
open VerifiableInference.Desc.Kinds.Head.Law.AtFold (seatsK6C mats_342)
open VerifiableInference.Desc.Kinds.Head.Law.AtFold (mats_342_b)
open VerifiableInference.Reads.AtSeat (Nums)
open Johnson.Desc.First.Walk.Tied (RchAt)
open ProofFile (Cl)

/-- **JHead3 at the reached states at 342, inside the promise at 342.** -/
theorem jHead3_342_b {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Xi Tok : Type}
    {rows cols nR : ℕ} {Wp : OnBytes.Model.Verify.Public}
    (D : MgData Xi ProofFile.InstPub Tok rows cols nR Wp)
    (Mg : Meaning ProofFile.InstPub (Wit (Fin rows → Fin cols → GE) Tok MsgT))
    {ans : ℕ → ℕ → ProofFile.InstPub × S → Strs → Wit (Fin rows → Fin cols → GE) Tok MsgT → Prop} {test : ℕ → S → Option String}
    (lay6 : OnBytes.Params.ReqLayout) (num : ℕ → ℕ → ℕ) (Fr : Frame)
    (Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop) (d : FoldData)
    (reqW : ProofFile.InstPub → Array UInt32)
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    (hWX : Bs.G₀.W = Wp) (hRch : ∀ k a, Rch k a → RchAt (P4.FD Z A B c) k a)
    (hfit : pubFit (mgAll D Mg).more linksFull (flatPlacesOf linksFull true) = true)
    (FF : FoldFacts Rch (fun a => a.1) d reqW linksFull (flatPlacesOf linksFull true))
    (hd : d.sent = D.sent) (hlay : D.layout = lay6)
    (hC : seatsK6C D.arr D.N Wp lay6 num (num 24 0) 0 D.cs D.shape D.pubD.dS d.L d.M
      (D.sent.arrayOf.getD 24 #[]) (D.N.msgsAt (flatPlacesOf linksFull true)[342]?) = true)
    (hJ : ∀ q, q < 6 → (Wp.HLy.calls.getD q default).lJ =
      (letI := Head.sizesOf Wp.hS; lJ (OnBytes.Model.Head.keyFloor Wp.hS) (callKeys q)))
    (Nm : Nums Wp) :
    ∀ a, Rch 342 a →
      onQ (Fr := Fr) D.N (honest (mgAll D Mg) ans test) linksFull (flatPlacesOf linksFull true) (fun a => a) 342 a →
      a.1.2.failed = none → JHead3 Wp (D.N.sent 24 0) D.arr D.N num lay6 a.1.2 := by
  subst hWX
  intro a hr ha hm o aK _ hK
  exact ⟨P4.heard_342 hS hR O hOk a (hRch 342 a hr),
    P4.run_342 hS hR O hOk ⟨1, some 24, 5, .K1⟩ (borderOf Bs.G₀.W.y) hJ Nm a (hRch 342 a hr),
    mats_342_b D Mg lay6 num Fr Rch d reqW hfit FF hd hlay hC a hr ha hm aK hK⟩

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.jHead3_342_b
