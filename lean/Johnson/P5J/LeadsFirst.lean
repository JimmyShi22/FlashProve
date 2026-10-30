-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/LeadsFirst.lean: THE PLAIN ROAD'S PREMISE ON THE FIRST CHAIN, FROM WHAT THE KINDS'
    FILES
OWE AT THE TABLE OF JOINTS, WITH NO PREMISE ON THE PIECES' EXTRACTORS. Two theorems. NO RESULT ON
THE PROTOCOL: rules.

What is said. Johnson/P5J/TopTable.lean gets the first chain's premise (`EachLeads`) from own₁ (the
kinds' laws), rep₁ (the frame fact on the reply) AND extq (every piece has the table's extractor).
The plain form's premise reads no extractor (Johnson/Desc/Sound/ReExt.lean): SO THE KINDS' LAWS ARE
ASKED AT THE SAME PIECES WITH THE TABLE'S EXTRACTOR LAID IN (`reExt`), and extq falls: no reader of
a transcript, no law "the block lays what it hears".
  `eachSure_of_rep`: the frame fact on the reply, block by block, gives what is sure of the token.
  `leads_first_at_table`: **`EachLeads` at the first chain's own pieces**, at the table's promise
    and at "one witness carried by the table's extractor; the token's step": from hc, own₁ at
    `reExt`, rep₁, htok.

Limits: those of TopTable.lean. A kind that has its law in the plain form for every witness enters
by `own_of_leads_map2` (Johnson/Desc/Sound/LeadsBack.lean), its hx by `withMap_ext`.
(`own_of_leads_map2` is declared nowhere in this library, and the library has no file
Johnson/Desc/Sound/LeadsBack.lean.) `Piece.Frames`
at the pieces so turned speaks of the table's extractor. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.TopPlain
import Johnson.Desc.Sound.LeadsQ
import Johnson.Desc.Sound.ReExt

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

/-- The frame fact on the reply, block by block, gives what is sure of the token. -/
theorem eachSure_of_rep (cs : OnBytes.Codes) {Xi P Cells Tok A Cl : Type} (G : FileDescription Xi)
    (arr : ℕ → ℕ → ℕ)
    (smp : P × TS → (s : Sending) → (i : Fin s.l.length) →
      Option ((Johnson.Pack.sigOf cs s.l).om i).Smp)
    (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → P × TS → Option Cells) (c₀ : Cells)
    (tokOf : P × TS → Tok) {C : CK} {Fr : Frame} (N : Numbers) (links : List ModelPart)
    (ps : List Place) (get : A → P × TS) {V : Type} (f : Tok → V) (rep : A × Fr.E.Str → Option V)
    (on : ℕ → A × Fr.E.Str → Prop) :
    ∀ (l : List (Piece C Fr A Cl (Wit Cells Tok MsgT))) (k : ℕ),
      EachRep tokOf links ps get f rep on k l →
      EachSure on (TokStep (extQAt cs G arr smp ms decT c₀ tokOf N links ps get)
        (fun w => f w.tok) rep) k l
  | [], _, _ => trivial
  | _ :: l, k, r =>
    ⟨fun a τ b ha hb =>
      tokStep_of_repFact cs G arr smp ms decT c₀ tokOf N links ps get f rep k a b
        (r.1 a τ b ha hb),
      eachSure_of_rep cs G arr smp ms decT c₀ tokOf N links ps get f rep on l (k + 1) r.2⟩

#print axioms eachSure_of_rep

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
theorem leads_first_at_table (hc : HeadCuts pp putReq H headPart)
    (own₁ : EachOwn
      (onQ (Fr := frameAt (DP.at frS.P.T.a) all (DP.at frS.P.T.a).key₁ T.ft₁) Nn MQ fullLinks ps
        get)
      (meansQ Nn MQ get) (insQ fullLinks ps) (outsQ fullLinks ps) (· ∈ start fullLinks) 0
      (reExt EX 0 (T.p₁ :: T.l₁)))
    (rep₁ : EachRep tokOf fullLinks ps get f (fun b => repS b.1) (QO).on₁ 0 (T.p₁ :: T.l₁))
    (htok : (fun w => (H.hid w).tok) = fun w : Wit Cells Tok MsgT => f w.tok) :
    EachLeads (QO).on₁
      (QE (F := frameAt (DP.at frS.P.T.a) all (DP.at frS.P.T.a).key₁ T.ft₁) (QO).on₁ (QO).R₁ EX
        (TokStep EX (fun w => (H.hid w).tok) fun b => repS b.1)) 0 (T.p₁ :: T.l₁) :=
  eachLeads_of_goodIn_reExt EX (QO).on₁ (QO).R₁ _ (T.p₁ :: T.l₁) 0
    (firstChainMeansQ pp putReq H headPart digitsPart hc Nn (meaningSig cs Gd arr smp ms decT Mg)
      { T with p₁ := T.p₁.withMap (EX 0), l₁ := reExt EX 1 T.l₁ } ps get Q₀ own₁)
    (by
      have hs := eachSure_of_rep
        (Fr := frameAt (DP.at frS.P.T.a) all (DP.at frS.P.T.a).key₁ T.ft₁) cs Gd arr smp ms decT c₀
        tokOf Nn fullLinks ps get f (fun b => repS b.1) (QO).on₁ (T.p₁ :: T.l₁) 0 rep₁
      rw [htok]
      exact hs)

end First

#print axioms leads_first_at_table

end P5J
