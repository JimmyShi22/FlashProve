-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/LeadsFirstTied.lean: `leads_first_at_table` (LeadsFirst.lean) WITH `EachTied` IN THE
    PLACE
OF own₁: the first chain's premise of the plain road (`EachLeads`) from the chain of promises. One
theorem; the letters and notations are LeadsFirst.lean's, copied by program. A rule over letters.
Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.LeadsFirst
import Johnson.Desc.Sound.FirstMeansTied

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

/-- **THE FIRST CHAIN'S PREMISE OF THE PLAIN ROAD, AT THE CHAIN'S OWN PIECES.** -/
theorem leads_first_of_tied (hc : HeadCuts pp putReq H headPart)
    (tied₁ : EachTied (Fr := frameAt (DP.at frS.P.T.a) all (DP.at frS.P.T.a).key₁ T.ft₁) Nn MQ
      fullLinks ps get 0 (reExt EX 0 (T.p₁ :: T.l₁)))
    (rep₁ : EachRep tokOf fullLinks ps get f (fun b => repS b.1) (QO).on₁ 0 (T.p₁ :: T.l₁))
    (htok : (fun w => (H.hid w).tok) = fun w : Wit Cells Tok MsgT => f w.tok) :
    EachLeads (QO).on₁
      (QE (F := frameAt (DP.at frS.P.T.a) all (DP.at frS.P.T.a).key₁ T.ft₁) (QO).on₁ (QO).R₁ EX
        (TokStep EX (fun w => (H.hid w).tok) fun b => repS b.1)) 0 (T.p₁ :: T.l₁) :=
  eachLeads_of_goodIn_reExt EX (QO).on₁ (QO).R₁ _ (T.p₁ :: T.l₁) 0
    (firstChainMeans_of_tied { T with p₁ := T.p₁.withMap (EX 0), l₁ := reExt EX 1 T.l₁ } Nn MQ
      fullLinks ps get _ Q₀ tied₁
      (tieStartQ pp putReq H headPart digitsPart hc Nn (meaningSig cs Gd arr smp ms decT Mg) T.ft₁
        ps get))
    (by
      have hs := eachSure_of_rep
        (Fr := frameAt (DP.at frS.P.T.a) all (DP.at frS.P.T.a).key₁ T.ft₁) cs Gd arr smp ms decT c₀
        tokOf Nn fullLinks ps get f (fun b => repS b.1) (QO).on₁ (T.p₁ :: T.l₁) 0 rep₁
      rw [htok]
      exact hs)

end First

#print axioms leads_first_of_tied

end P5J
