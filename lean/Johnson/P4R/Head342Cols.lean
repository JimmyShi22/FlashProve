-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P4R/Head342Cols.lean: `mats_342` (Johnson/P4R/Head342.lean) AT ANY COLUMNS THAT LIE IN THE
HEAD's MATRICES UP TO NUMBER NHf + 3; AND SO AT THE ONE MATRIX NHf + 2. Two theorems: calls.
Why. The run "planes" of the kind K1 asks `MatsSeated` at the matrix NHf + 2 of the same states
(reached at 342, inside the promise at 342). `matsSeated_of_C`
(Johnson/Desc/Kinds/Law/K6SeatsTest.lean) is general in the columns below that bound; `mats_342`
took it at the four ranges alone.
  `mats_342_of`: at every Cols with hCols : ∀ a c, Cols a c → a ≤ Wp.hS.NHf + 3.
  `matsP_342`: at Cols := fun μ _ => μ = Wp.hS.NHf + 2.
Premises, limits: those of `mats_342`, to the letter. No probability: no soundness follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P4R.Head342

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.AtFold

open OnBytes
open OnBytes.Maker OnBytes.Flat Johnson.Pack
open OnBytes.Params (ReqLayout ReqShape)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc.First (S Numbers Meaning pubFit flatPlacesOf FoldData FoldFacts)
open VerifiableInference.Desc.Sound (Frame MsgT onQ linksFull MgData mgAll)

/-- **The head's matrices are seated, at any columns below the bound.** -/
theorem mats_342_of {Xi P Tok : Type} {rows cols nR : ℕ} {Wp : OnBytes.Model.Verify.Public}
    (D : MgData Xi P Tok rows cols nR Wp)
    (Mg : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT)) (lay6 : ReqLayout)
    (num : ℕ → ℕ → ℕ) (Fr : Frame) (Rch : ℕ → (P × S) × Fr.E.Str → Prop) (d : FoldData)
    (reqW : P → Array UInt32)
    (hfit : pubFit (mgAll D Mg).more linksFull (flatPlacesOf linksFull true) = true)
    (FF : FoldFacts Rch (fun a => a.1) d reqW linksFull (flatPlacesOf linksFull true))
    (hd : d.sent = D.sent) (hlay : D.layout = lay6)
    (hC : seatsK6C D.arr D.N Wp lay6 num (num 24 0) 0 D.cs D.shape D.pubD.dS d.L d.M
      (D.sent.arrayOf.getD 24 #[]) (D.N.msgsAt (flatPlacesOf linksFull true)[342]?) = true)
    (Cols : ℕ → ℕ → Prop) (hCols : ∀ a c, Cols a c → a ≤ Wp.hS.NHf + 3) :
    ∀ a, Rch 342 a →
      onQ (Fr := Fr) D.N (mgAll D Mg) linksFull (flatPlacesOf linksFull true) (fun a => a) 342 a →
      a.1.2.failed = none → ∀ aK, K9.segAt? a.1.2 = some aK →
      MatsSeated Cols D.arr D.N Wp (D.N.sent 24 0) aK num lay6 :=
  fun a hr ha hm aK hK =>
    matsSeated_of_C hC
      (stateIsPlan_342 D Mg lay6 Fr d.L d.M hfit a ha hm
        (foldAt_of_facts D lay6 Fr Rch d reqW FF hd hlay 342 a hr hm) aK hK) Cols hCols

/-- **At the one matrix NHf + 2.** -/
theorem matsP_342 {Xi P Tok : Type} {rows cols nR : ℕ} {Wp : OnBytes.Model.Verify.Public}
    (D : MgData Xi P Tok rows cols nR Wp)
    (Mg : Meaning P (Wit (Fin rows → Fin cols → GE) Tok MsgT)) (lay6 : ReqLayout)
    (num : ℕ → ℕ → ℕ) (Fr : Frame) (Rch : ℕ → (P × S) × Fr.E.Str → Prop) (d : FoldData)
    (reqW : P → Array UInt32)
    (hfit : pubFit (mgAll D Mg).more linksFull (flatPlacesOf linksFull true) = true)
    (FF : FoldFacts Rch (fun a => a.1) d reqW linksFull (flatPlacesOf linksFull true))
    (hd : d.sent = D.sent) (hlay : D.layout = lay6)
    (hC : seatsK6C D.arr D.N Wp lay6 num (num 24 0) 0 D.cs D.shape D.pubD.dS d.L d.M
      (D.sent.arrayOf.getD 24 #[]) (D.N.msgsAt (flatPlacesOf linksFull true)[342]?) = true) :
    ∀ a, Rch 342 a →
      onQ (Fr := Fr) D.N (mgAll D Mg) linksFull (flatPlacesOf linksFull true) (fun a => a) 342 a →
      a.1.2.failed = none → ∀ aK, K9.segAt? a.1.2 = some aK →
      MatsSeated (fun μ _ => μ = Wp.hS.NHf + 2) D.arr D.N Wp (D.N.sent 24 0) aK num lay6 :=
  mats_342_of D Mg lay6 num Fr Rch d reqW hfit FF hd hlay hC _ (fun a _ h => by omega)

end VerifiableInference.Desc.Kinds.Head.Law.AtFold

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.mats_342_of
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.matsP_342
