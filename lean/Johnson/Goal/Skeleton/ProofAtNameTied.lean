-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Skeleton/ProofAtNameTied.lean: the structure `P5J.RowsTied`
(Johnson/P5J/SevenOfTied.lean), with the hypotheses listed below, gives `ProofFileAt Z`
(Johnson/Goal/Skeleton/ProofFile.lean) for the description `VerifierAndGoals.theDescription`.

  `proofFileAt_of_tied`: `P5J.rows_of_tied_some` (Johnson/P5J/RowsOfTied.lean) called at the claims,
    coding and data of `dataAtFiles flashProveData Z`, through `proofFileAt_of_rows`
    (Johnson/Goal/Skeleton/ProofAtNameRows.lean). Its hypotheses: Z is in scope; `protocolDataWellFormed` says yes
    at Z; `theProofRun (asDescriptionFiles Z)` is the run of F₀ pulled back along instP; `RowsTied`, at some
    codes and rq; F₀'s test `planOk` says yes; F₀'s data are those of `dataAtFiles flashProveData Z`; each
    chain's blocks are cᵢ :: kᵢ (q₁ to q₃). The caller supplies some d of its type.
All other arguments pass unchanged to `RowsTied` and `rows_of_tied_some`. They are the variables of
Johnson/P5J/RowsOfTied.lean, taken at `numsRef`, `ppAtFiles Z.pol Z.KL` and the coding, data, record
and depth of `dataAtFiles flashProveData Z`.

Limits. This file only combines statements. None of the hypotheses is proved for the protocol's own
description, so nothing here shows that the proof file's protocol is sound. No example is given in
which the hypotheses hold together. That the equation on `theProofRun`
holds is not shown here; where it fails the theorem says nothing.

(Where this and lean/THEOREM.md differ, the page holds.)

-/
import Johnson.P5J.RowsOfTied
import Johnson.Goal.Skeleton.ProofAtNameRows

set_option autoImplicit false
set_option maxRecDepth 100000

/- Remove the default instance `Inst.Model.Scl.ref`: no statement below may pick it up silently. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open OnBytes.Model.Verify (publicOf)
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit)
open VerifiableInference.Desc.First (ModelPart Numbers start)
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Iop (oneExternalString Tr)
open _root_.Iop.Reduction (steps)
open _root_.Run _root_.Run.PQ
open VerifierAndGoals FlashProve FlashProve VerifierAndGoals.AtTheName

/-- The coding of `dataAtFiles flashProveData Z`, with its type written as Johnson/P5J/RowsOfTied.lean writes
it. -/
abbrev codZ (Z : VerifierAndGoals.PublicFiles) :
    Coding (claimsReqAt (frS.toDecR frZ 402653181) numsRef (ppAtFiles Z.pol Z.KL)) :=
  (dataAtFiles flashProveData Z).E

/-- The proof file's data in `dataAtFiles flashProveData Z`, at the depth `frS.P.T.a`. -/
abbrev dAt (Z : VerifierAndGoals.PublicFiles) : WholeD := (dpZ Z).at frS.P.T.a

/-- The type of witnesses of Johnson/P5J/RowsOfTied.lean at `numsRef`. -/
abbrev WitZ (Tok : Type) : Type := Wit (CellsM numsRef) Tok MsgT

/-- The configuration `kcReq` at `numsRef`, `ppAtFiles Z.pol Z.KL` and `codZ Z`. -/
abbrev kcZ (Z : VerifierAndGoals.PublicFiles) : ConfLetters frS.P.T.a :=
  kcReq numsRef (ppAtFiles Z.pol Z.KL) (codZ Z)

variable (Z : VerifierAndGoals.PublicFiles) {lay : Option ByteArray} {X : Model.Verify.Public}
  {XiP : Type} (F₀ : FileDescription XiP)
  (instP : (kcZ Z).conf.X × (kcZ Z).conf.Rec → XiP) {Tok : Type}
  (getS : F₀.S₁ → TS) (reqB : F₀.XiPub → ByteArray)
  (DT : (ℕ → Option (ℕ × List UInt64)) → F₀.XiPub × TS → Option (CellsM numsRef))
  (asked : XiP → OnBytes.E) (d₀ : TReq) (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ)
  (ms : List Mem) (Nn : Numbers) (s : ℕ → Cb.Pv.Tail.Size)
  (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ) (f : Tok → Fin ppref.V)
  (hN : SeatsNamed arr Nn s seat) (hG : GroupsSeated ms Nn)
  (Q₀ : PlacesAt (dAt Z) (allOf (dAt Z)) F₀ (WitZ Tok))
  (Mg : VerifiableInference.Desc.First.Meaning F₀.XiPub (WitZ Tok))
  (ps : List Place)
  (headPart : TPart → Cm.Idx → F₀.XiPub × TS → Strs → WitZ Tok → Prop)
  (digitsPart : ℕ → F₀.XiPub × TS → Strs → WitZ Tok → Prop)
  {Xg : Type} (Gd : FileDescription Xg)
  (smp : F₀.XiPub × TS → (s : Sending) → (i : Fin s.l.length) →
    Option ((Johnson.Pack.sigOf cs s.l).om i).Smp)
  (c₀ : CellsM numsRef) (tokOf : F₀.XiPub × TS → Tok)
  (Ns : NumbersS) (MgS : MeaningS F₀.S₂ (F₀.XiPub × F₀.S₁) (WitZ Tok))
  (ML : MeaningL F₀.S₃ (WitZ Tok)) (Pm : PromMeaning F₀.S₂)
  (PLm : PromMeaningL F₀.S₂ F₀.S₃ (F₀.XiPub × F₀.S₁)) (split : Bool)
  (Q₂ : ℕ → ((F₀.XiPub × F₀.S₁) × F₀.S₂) × (EAll (dAt Z) (allOf (dAt Z))).Str →
    ((F₀.XiPub × F₀.S₁) × F₀.S₂) × (EAll (dAt Z) (allOf (dAt Z))).Str → Prop)
  (c₁ : Block F₀.S₁ F₀.Cl) (k₁ : List (Block F₀.S₁ F₀.Cl)) (c₂ : Block F₀.S₂ F₀.Cl)
  (k₂ : List (Block F₀.S₂ F₀.Cl)) (c₃ : Block F₀.S₃ F₀.Cl) (k₃ : List (Block F₀.S₃ F₀.Cl))
  (e₁ : (i : ℕ) → (ds : List RDT) → (F₀.XiPub × F₀.S₁) ×
      (frameAt (dAt Z) (allOf (dAt Z)) (dAt Z).key₁ 0).E.Str →
      _root_.Iop.Tr (uLT (ckP .two) ds) → WitZ Tok → WitZ Tok)
  (e₂ : (i : ℕ) → (ds : List RDT) → ((F₀.XiPub × F₀.S₁) × F₀.S₂) ×
      (frameAt (dAt Z) (allOf (dAt Z)) (dAt Z).key₂ 0).E.Str →
      _root_.Iop.Tr (uLT (ckP .two) ds) → WitZ Tok → WitZ Tok)
  (e₃ : (i : ℕ) → (ds : List RDT) → ((F₀.XiPub × F₀.S₁ × F₀.S₂) × F₀.S₃) ×
      (frameAt (dAt Z) (allOf (dAt Z)) (dAt Z).key₃
        F₀.lastChainFirstTreeNumber).E.Str →
      _root_.Iop.Tr (uLT (ckP .two) ds) → WitZ Tok → WitZ Tok)
  (dW wEnd : WitZ Tok) (kS₂ : RecFull → F₀.S₂)

/-- **`RowsTied` at the data of `dataAtFiles flashProveData Z`, with the hypotheses below, gives
`ProofFileAt Z`.** -/
theorem proofFileAt_of_tied (hZ : VerifierAndGoals.InScope Z = true) (hl : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (seat_proof_file : theProofRun (asDescriptionFiles Z) = (F₀.pull instP).run) {codes : OnBytes.Codes}
    (rq : F₀.XiPub → Array UInt32)
    (R : RowsTied (Z := Z) (lay := lay) (X := X) numsRef (codZ Z) (dpZ Z) F₀ instP getS reqB DT
      asked d₀ cs arr ms Nn s seat f hN hG Q₀ Mg ps headPart digitsPart Gd smp c₀ tokOf Ns MgS ML Pm
      PLm split Q₂ (depthZ Z) c₁ k₁ c₂ k₂ c₃ k₃ e₁ e₂ e₃ dW wEnd kS₂ codes rq)
    (hp : F₀.planOk = true) (hD : F₀.data "proof file" = .ok ((dpZ Z).at frS.P.T.a))
    (q₁ : F₀.first.blocksInOrder = c₁ :: k₁) (q₂ : F₀.shared.blocksInOrder = c₂ :: k₂)
    (q₃ : F₀.second.blocksInOrder = c₃ :: k₃)
    (d : (F₀.XiPub × F₀.S₁) ×
      (EAll ((dpZ Z).at frS.P.T.a) (allOf ((dpZ Z).at frS.P.T.a))).Str) :
    ProofFileAt Z :=
  proofFileAt_of_rows Z hl F₀ instP seat_proof_file fun early he P Tl => by
    subst he
    obtain ⟨h₁, h₂, h₃, R'⟩ := rows_of_tied_some numsRef (codZ Z) (dpZ Z) F₀ instP getS reqB DT
      asked d₀ cs arr ms Nn s seat f hN hG Q₀ Mg ps headPart digitsPart Gd smp c₀ tokOf Ns MgS ML Pm
      PLm split Q₂ (recZ Z) (depthZ Z) c₁ k₁ c₂ k₂ c₃ k₃ e₁ e₂ e₃ dW wEnd kS₂ hZ rq R hp hD q₁ q₂ q₃
      d hl (runP_the_at Z _ seat_proof_file) Tl
    exact ⟨_, R'⟩

end P5J

#print axioms P5J.proofFileAt_of_tied
