-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/LeadsFirstTiedR.lean: THE FIRST CHAIN'S PREMISE OF THE PLAIN ROAD, SECOND FORM: at the
    table's promise WITH A CONDITION Rch BESIDE IT at every
border (`onR`, Johnson/Desc/Sound/ChainOfPromisesR.lean). LeadsFirstTied.lean's theorem again, over
    `chainOfPromisesR`: every
rule that it calls is general in the promise.
  `eachRep_mono`: the frame fact on the reply at a promise holds at every stronger one.
  **`leads_first_of_tiedR`**: `EachTiedR`, the frame fact on the reply, hc (`HeadCuts`) and htok
      give `EachLeads` at the conjunction.
Limits. General in Rch. A rule over letters: no member.
Limits: that file's. A joining of rules: no member is known. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.LeadsFirst
import Johnson.Desc.Sound.FirstMeansTied
import Johnson.Desc.Sound.TiedR
import Johnson.P5J.LeadsFirstTied

set_option autoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit)
open VerifiableInference.Desc.First (ModelPart Numbers start)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Iop (oneExternalString Tr)
open _root_.Run _root_.Run.PQ

section First

variable {pp : ScalesAndPolicy} {X : Model.Verify.Public} (N : MatrixNums) (DP : WholeD) {Xi : Type}
  (F : FileDescription Xi) (all : List LeftT) {P Cells Tok : Type}
  (H : HidAt X P (Wit Cells Tok MsgT) N.rows (colsAt N)) (get : F.XiPub × F.S₁ → P × TS)
  (repS : F.XiPub × F.S₁ → Option (Fin ppref.V))
  (Q₀ : PlacesAt (DP.at frS.P.T.a) all F (Wit Cells Tok MsgT)) (Nn : Numbers)
  (Mg : VerifiableInference.Desc.First.Meaning P (Wit Cells Tok MsgT)) (ps : List Place)
  (headPart : TPart → Cm.Idx → P × TS → Strs → Wit Cells Tok MsgT → Prop)
  (digitsPart : ℕ → P × TS → Strs → Wit Cells Tok MsgT → Prop)
  (cs : OnBytes.Codes) {Xg : Type} (Gd : FileDescription Xg) (arr : ℕ → ℕ → ℕ)
  (smp : P × TS → (s : Sending) → (i : Fin s.l.length) →
    Option ((Johnson.Pack.sigOf cs s.l).om i).Smp)
  (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → P × TS → Option Cells) (c₀ : Cells)
  (tokOf : P × TS → Tok) (f : Tok → Fin ppref.V) {X₁ X₂ : Type}
  (T : ThreeAt (ckP .two) (DP.at frS.P.T.a) all F X₁ X₂ (Wit Cells Tok MsgT))

set_option quotPrecheck false in
/-- The table's meaning, as in TopTable.lean's plain road. -/
local notation "MQ" => meaningQ putReq H headPart digitsPart
  (meaningSig cs Gd arr smp ms decT Mg)

set_option quotPrecheck false in
/-- The file's conditions and relations: the first chain's from the table. -/
local notation "QO" => placesM (D := DP.at frS.P.T.a) (all := all) T.ft₁ Nn MQ fullLinks ps get
  (firstAt pp putReq H T.ft₁ get) Q₀

set_option quotPrecheck false in
/-- The table's one extractor. -/
local notation "EX" => extQAt (Fr := frameAt (DP.at frS.P.T.a) all (DP.at frS.P.T.a).key₁ T.ft₁) cs
  Gd arr smp ms decT c₀ tokOf Nn fullLinks ps get

/-- Every sub-protocol tied in the second form, and the tie at the chain's start: the first chain's
    premise of the
rule for a file, at the promise with Rch beside it. -/
theorem firstChainMeans_of_tiedR {C : CK} {D : WholeD} {all : List LeftT}
    {Y P S₁ S₂ S₃ X₁ X₂ Cl W : Type} (T : Three C D all Y S₁ S₂ S₃ X₁ X₂ Cl W) (N : Numbers)
    (Mg : VerifiableInference.Desc.First.Meaning P W) (links : List ModelPart) (ps : List Place)
    (get : S₁ → P × VerifiableInference.Desc.First.S)
    (R₀ : S₁ × (EAll D all).Str → W → Prop) (Q : Places D all S₁ S₂ S₃ W)
    (Rch : ℕ → S₁ × (frameAt D all D.key₁ T.ft₁).E.Str → Prop)
    (hT : EachTiedR (Fr := frameAt D all D.key₁ T.ft₁) N Mg links ps get Rch 0 (T.p₁ :: T.l₁))
    (hs : VerifiableInference.Desc.Sound.TieStart T.ft₁ N Mg links ps get R₀) :
    EachGoodIn (fun k a => (placesM T.ft₁ N Mg links ps get R₀ Q).on₁ k a ∧ Rch k a)
      (placesM T.ft₁ N Mg links ps get R₀ Q).R₁ 0 (T.p₁ :: T.l₁) :=
  eachGoodInFront S₁ Cl W C (frameAt D all D.key₁ T.ft₁) _ _ R₀ T.p₁ T.l₁
    (fun a w ha hr => hs a w ha.1 hr)
    (chainOfPromisesR N Mg links ps get Rch (T.p₁ :: T.l₁) 0 hT)

/-- The frame fact on the reply at a promise holds at every stronger one. -/
theorem eachRep_mono {A Cl : Type} {C : CK} {Fr : Frame} {Cells' Tok' P' : Type}
    (tokOf' : P' × TS → Tok') (links : List ModelPart) (ps' : List Place) (get' : A → P' × TS)
    (f' : Tok' → Fin ppref.V) (rep : A × Fr.E.Str → Option (Fin ppref.V))
    (on on' : ℕ → A × Fr.E.Str → Prop) (h : ∀ k a, on' k a → on k a) :
    ∀ (l : List (Piece C Fr A Cl (Wit Cells' Tok' MsgT))) (k : ℕ),
      EachRep tokOf' links ps' get' f' rep on k l → EachRep tokOf' links ps' get' f' rep on' k l
  | [], _, _ => trivial
  | _ :: l, k, hr =>
    ⟨fun a τ b ha hb => hr.1 a τ b (h k a ha) hb,
      eachRep_mono tokOf' links ps' get' f' rep on on' h l (k + 1) hr.2⟩

/-- **THE FIRST CHAIN'S PREMISE, SECOND FORM.** -/
theorem leads_first_of_tiedR
    (Rch : ℕ → (F.XiPub × F.S₁) ×
      (frameAt (DP.at frS.P.T.a) all (DP.at frS.P.T.a).key₁ T.ft₁).E.Str → Prop)
    (hc : HeadCuts pp putReq H headPart)
    (tied₁ : EachTiedR (Fr := frameAt (DP.at frS.P.T.a) all (DP.at frS.P.T.a).key₁ T.ft₁) Nn MQ
      fullLinks ps get Rch 0 (reExt EX 0 (T.p₁ :: T.l₁)))
    (rep₁ : EachRep tokOf fullLinks ps get f (fun b => repS b.1) (QO).on₁ 0 (T.p₁ :: T.l₁))
    (htok : (fun w => (H.hid w).tok) = fun w : Wit Cells Tok MsgT => f w.tok) :
    EachLeads (fun k a => (QO).on₁ k a ∧ Rch k a)
      (QE (F := frameAt (DP.at frS.P.T.a) all (DP.at frS.P.T.a).key₁ T.ft₁)
        (fun k a => (QO).on₁ k a ∧ Rch k a) (QO).R₁ EX
        (TokStep EX (fun w => (H.hid w).tok) fun b => repS b.1)) 0 (T.p₁ :: T.l₁) :=
  eachLeads_of_goodIn_reExt EX (fun k a => (QO).on₁ k a ∧ Rch k a) (QO).R₁ _ (T.p₁ :: T.l₁) 0
    (firstChainMeans_of_tiedR { T with p₁ := T.p₁.withMap (EX 0), l₁ := reExt EX 1 T.l₁ } Nn MQ
      fullLinks ps get _ Q₀ Rch tied₁
      (tieStartQ pp putReq H headPart digitsPart hc Nn (meaningSig cs Gd arr smp ms decT Mg) T.ft₁
        ps get))
    (by
      have hs := eachSure_of_rep
        (Fr := frameAt (DP.at frS.P.T.a) all (DP.at frS.P.T.a).key₁ T.ft₁) cs Gd arr smp ms decT c₀
        tokOf Nn fullLinks ps get f (fun b => repS b.1) (fun k a => (QO).on₁ k a ∧ Rch k a)
        (T.p₁ :: T.l₁) 0
        (eachRep_mono tokOf fullLinks ps get f (fun b => repS b.1) (QO).on₁ _
          (fun _ _ h => h.1) _ 0 rep₁)
      rw [htok]
      exact hs)

end First

#print axioms firstChainMeans_of_tiedR
#print axioms eachRep_mono
#print axioms leads_first_of_tiedR

end P5J
