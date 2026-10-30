-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/TopTable.lean: THE TWO END THEOREMS OF Johnson/P5J/TopMeans.lean AND TopPlain.lean, FED
    FROM
THE TABLE OF JOINTS. Two theorems, each one call. NO RESULT ON THE PROTOCOL: rules, of whose
premises no description of the protocol is shown to meet one. THEY TAKE THE TABLE AS IT LIES: own₁
is a conjunction over the blocks: AT A VERSION OF THE TABLE AT WHICH ONE ROW'S LAW IS FALSE AT THE
REAL CHAIN BOTH ARE TRUE AND EMPTY THERE. (Known of one version: the row of the switch
with a kept message; the rows in front of the smallness test.) Which version a build stood over is
said by a print that is not in this library.

What turns against the two files beneath, premise by premise:
  LS (what the layers' 24 sub-proofs say): PAID: the theorem `layersSay`
    (Johnson/Goal/Meaning/LayersSay.lean), by import.
  good₁ (`EachGoodIn` at the first chain): IN ITS PLACE WHAT A KIND'S FILES OWE AT THE TABLE: own₁
    (`EachOwn`: from the items that a block closes to those that it opens, and the riding), at the
    full size's list of segments and at the meaning whose parts are the integer model's own clauses
    (`meaningQ`), with the named premise at the head hc (`HeadCuts`): by `firstChainMeansQ`.
  eachE (the plain road): IN ITS PLACE extq (`EachExtQ`: every piece has the table's one extractor
    wherever its block says yes: by the make of the pieces), rep₁ (`EachRep`: the frame fact on the
    reply, block by block) and htok (the token that hid reads is f of the witness's own): by
    `eachE_of_extQ`.

Main theorems:
  `proofSound_of_own`: the road with extractors.
  `proofSound_plain_of_own`: the plain road; the witness is the table's own (`Wit`), the extractor
    the table's (`extQAt`).

WHAT IS STILL A LETTER: all that the two files beneath name; headPart, digitsPart. G (the three
glues) is still a premise on the plain road, glued on the other. The number that the first chain's
frame bears is 0 on the road with extractors, as the maker's cut lays it.

Limits: those of TopMeans.lean, TopPlain.lean, MeansQ.lean, LeadsQ.lean. `F.Hears` (Hr, on the road
with extractors) is a record of data AND FOUR LAWS (the cut at the reply's block; that block lays
what it hears; no later block turns it; the last test's yes gives "heard is asked"): A PREMISE,
though it stands among the letters. ONE DECODER BY TWO LETTERS: `meaningQ` reads "the stored table
decodes" off H.dec, the pin of the stored table off decT: nothing here ties the two. f : Tok → the
model's tokens is total: an element that spells no token goes somewhere; finReply then hides a tie
between the instance's asked reply and the request's own: the description's files' and the map of
instances'. Nothing on completeness; nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.TopMeans
import Johnson.P5J.TopPlain
import Johnson.Goal.Meaning.LayersSay
import Johnson.Desc.Sound.LeadsQ

set_option autoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open OnBytes.Model.Verify (publicOf)
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit)
open VerifiableInference.Desc.First (ModelPart Numbers start)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Iop (oneExternalString Tr)
open _root_.Run _root_.Run.PQ

/-! ## 1 The road with extractors -/

section Top

variable {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : Model.Verify.Public}
  (N : MatrixNums) (E : Coding (claimsReqAt (frS.toDecR frZ 402653181) N pp)) (DK DP : WholeD)
  {TFk TJk T3k TFp TJp T3p : Type} (tFk : TFk) (tJk : TJk) (t3k : T3k) (tFp : TFp) (tJp : TJp)
  (t3p : T3p) (silK : (kcReq N pp E).conf.Rec → TFk → TJk → T3k → Bool)
  (runK : (kcReq N pp E).conf.Rec → PQ.View → PQ.View → PQ.View → Bool)
  (silP : (kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec → TFp → TJp → T3p → Bool)
  (F : FileDescription ((kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec))
  (eL : LinkProtocolWithLeafCoding (kcReq N pp E).conf.Rec frS.P.T.a) (n : ℕ)
  {W : Type} (file : String)
  (b₁ : Block F.S₁ F.Cl) (l₁ : List (Block F.S₁ F.Cl)) (b₂ : Block F.S₂ F.Cl)
  (l₂ : List (Block F.S₂ F.Cl)) (b₃ : Block F.S₃ F.Cl) (l₃ : List (Block F.S₃ F.Cl))
  (rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
    (frameAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (DP.at frS.P.T.a).key₁ 0)
    (F.XiPub × F.S₁) W ds)
  (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
    (frameAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (DP.at frS.P.T.a).key₂ 0)
    ((F.XiPub × F.S₁) × F.S₂) W ds)
  (rest₃ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
    (frameAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (DP.at frS.P.T.a).key₃ F.lastChainFirstTreeNumber)
    ((F.XiPub × F.S₁ × F.S₂) × F.S₃) W ds)
  (d wEnd : W) (g : F.XiPub → F.S₁ → F.S₂ → F.S₃ → Bool)
  (Q₀ : PlacesAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) F W)
  {P : Type} (H : HidAt X P W N.rows (colsAt N)) (Nn : Numbers)
  (Mg : VerifiableInference.Desc.First.Meaning P W) (ps : List Place)
  (get : F.XiPub × F.S₁ → P × TS)
  (headPart : TPart → Cm.Idx → P × TS → Strs → W → Prop)
  (digitsPart : ℕ → P × TS → Strs → W → Prop)
  (rd : List Fmt.RoundView → Option (Fin ppref.V)) (Hr : F.Hears (fun b => dropReq b.1) rd)
  (back : F.XiPub → (kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec)
  (s₂ : (kcReq N pp E).conf.Rec → F.S₂)
  (Pv : (filesOf (kcReq N pp E) .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL n
    reqWithoutReply none).Provers)
  (Tl : InnerCompilerInputFieldsOverThreeProtocols (filesOf (kcReq N pp E) .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run
                                    eL n reqWithoutReply none) Pv)
  (U : SoundnessAnalysisFieldsOverThreeProtocols (filesOf (kcReq N pp E) .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run
                                     eL n reqWithoutReply none) Pv)

set_option quotPrecheck false in
/-- The description's own blocks, cut by the maker, with the ends' part of the last test. -/
local notation "TT" => atDescFin F g
  (piecesAt (ckP .two) F (DP.at frS.P.T.a) b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd)

set_option quotPrecheck false in
/-- The table's meaning, its parts the integer model's own clauses. -/
local notation "MQ" => meaningQ putReq H headPart digitsPart Mg

set_option quotPrecheck false in
/-- The file's conditions and relations: the first chain's from the table of joints at the full
size's segments, with the integer model's relation in front. -/
local notation "QO" => placesM (D := DP.at frS.P.T.a) (all := allOf (DP.at frS.P.T.a)) 0 Nn MQ
  fullLinks ps get (firstAt pp putReq H 0 get) Q₀

/-- **THE PROOF FILE'S NAMED HYPOTHESIS ON SOUNDNESS, AT A DESCRIPTION'S OWN DECISION, FROM WHAT THE
KINDS' FILES OWE AT THE TABLE OF JOINTS**, on the road with extractors. -/
theorem proofSound_of_own (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (A : Hd.PublicCore X.P)
    (hc : HeadCuts pp putReq H headPart)
    (hdata : F.data file = .ok (DP.at frS.P.T.a)) (hseal : F.sealLast = true)
    (e₁ : F.first.blocksInOrder = b₁ :: l₁) (e₂ : F.shared.blocksInOrder = b₂ :: l₂) (e₃ : F.second.blocksInOrder = b₃ :: l₃)
    (hfin : FinGives F g)
    (own₁ : EachOwn
      (onQ (Fr := frameAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (DP.at frS.P.T.a).key₁ 0) Nn
        MQ fullLinks ps get)
      (meansQ Nn MQ get) (insQ fullLinks ps) (outsQ fullLinks ps) (· ∈ start fullLinks) 0
      ((TT).p₁ :: (TT).l₁))
    (lost₂ : EachLostBoth n (QO).on₂ (QO).R₂
      (actsOf Prod.snd (DP.at frS.P.T.a).t₁ (TT).p₂ (TT).l₂) 0 ((TT).p₂ :: (TT).l₂))
    (good₃ : EachGood (QO).on₃ (QO).R₃ 0 ((TT).p₃ :: (TT).l₃))
    (glued : (TT).Glued QO)
    (hext : ExtRowAt (fun w => (H.hid w).tok) rd Hr.pre.length (TT).p₁ (TT).l₁)
    (first_border_on : ∀ (x : (kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec)
      (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str), F.okStart x = true →
      (kcReq N pp E).conf.D y x.2 ≠ none →
      (QO).on₁ 0 ((F.pub x, F.start₁ (F.pub x)), (y, fun _ => [])))
    (hd : ∀ (x : (kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec)
      (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str),
      H.dec (get (F.pub x, F.start₁ (F.pub x)))
        (strsOf (frameAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (DP.at frS.P.T.a).key₁ 0)
          (y, fun _ => [])) = (kcReq N pp E).conf.D y (back (F.pub x)).2)
    (hp : ∀ x, H.req (get (F.pub x, F.start₁ (F.pub x))) = (back (F.pub x)).1)
    (pubEarly : PubEarly (kcReq N pp E) reqWithoutReply F.pub)
    (pubKeeps : PubKeeps (kcReq N pp E) reqWithoutReply F.pub back)
    (oneKey : ∀ x rec, F.start₂ (F.pub (x, rec)) = s₂ rec)
    (opens : ∀ d ∈ (DP.at frS.P.T.a).ds₂, ∀ j ∈ d.opens, (DP.at frS.P.T.a).t₁ ≤ j)
    (below₁ : EachBelow U.εs ((TT).p₁ :: (TT).l₁)) (below₂ : EachBelow U.εs ((TT).p₂ :: (TT).l₂))
    (below₃ : EachBelow U.εs ((TT).p₃ :: (TT).l₃)) :
    CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataOfThreeProtocols (filesOf (kcReq N pp E) .two DK DP tFk tJk t3k tFp tJp t3p silK
                                                               runK silP F.run eL n reqWithoutReply none) Pv Tl U) :=
  proofSound_at_means N E DK DP tFk tJk t3k tFp tJp t3p silK runK silP F eL n file b₁ l₁ b₂ l₂ b₃
    l₃ rest₁ rest₂ rest₃ d wEnd g Q₀ H Nn MQ fullLinks ps get 0 rd Hr back s₂ Pv Tl U layersSay hR
    h A hdata hseal e₁ e₂ e₃ hfin
    (firstChainMeansQ pp putReq H headPart digitsPart hc Nn Mg TT ps get Q₀ own₁)
    lost₂ good₃ glued hext first_border_on hd hp pubEarly pubKeeps oneKey opens below₁ below₂
    below₃

end Top

#print axioms proofSound_of_own

/-! ## 2 The plain road -/

section Plain

variable {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : Model.Verify.Public}
  (N : MatrixNums) (E : Coding (claimsReqAt (frS.toDecR frZ 402653181) N pp)) (DP : WholeD)
  (F : FileDescription ((kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec)) (all : List LeftT)
  {P Cells Tok : Type} (H : HidAt X P (Wit Cells Tok MsgT) N.rows (colsAt N))
  (get : F.XiPub × F.S₁ → P × TS) (repS : F.XiPub × F.S₁ → Option (Fin ppref.V))
  (Q₀ : PlacesAt (DP.at frS.P.T.a) all F (Wit Cells Tok MsgT)) (Nn : Numbers)
  (Mg : VerifiableInference.Desc.First.Meaning P (Wit Cells Tok MsgT)) (ps : List Place)
  (headPart : TPart → Cm.Idx → P × TS → Strs → Wit Cells Tok MsgT → Prop)
  (digitsPart : ℕ → P × TS → Strs → Wit Cells Tok MsgT → Prop)
  (cs : OnBytes.Codes) {Xi : Type} (Gd : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : P × TS → (s : VerifiableInference.Desc.Sound.Sending) → (i : Fin s.l.length) →
    Option ((Johnson.Pack.sigOf cs s.l).om i).Smp)
  (ms : List VerifiableInference.Desc.Sound.Mem)
  (decT : (ℕ → Option (ℕ × List UInt64)) → P × TS → Option Cells) (c₀ : Cells)
  (tokOf : P × TS → Tok) (f : Tok → Fin ppref.V)
  (DK : WholeD) {TFk TJk T3k TFp TJp T3p : Type} (tFk : TFk) (tJk : TJk) (t3k : T3k)
  (tFp : TFp) (tJp : TJp) (t3p : T3p)
  (silK : (kcReq N pp E).conf.Rec → TFk → TJk → T3k → Bool)
  (runK : (kcReq N pp E).conf.Rec → PQ.View → PQ.View → PQ.View → Bool)
  (silP : (kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec → TFp → TJp → T3p → Bool)
  (eL : LinkProtocolWithLeafCoding (kcReq N pp E).conf.Rec frS.P.T.a) (n : ℕ) {X₁ X₂ κ : Type}
  (T : ThreeAt (ckP .two) (DP.at frS.P.T.a) all F X₁ X₂ (Wit Cells Tok MsgT))
  (Pl₀ : PPlaces (DP.at frS.P.T.a) all (F.XiPub × F.S₁) ((F.XiPub × F.S₁) × F.S₂)
    ((F.XiPub × F.S₁ × F.S₂) × F.S₃))
  (h₁ : (rowIOR (atDesc F T).p₁ (atDesc F T).l₁).shape = uLT (ckP .two) (DP.at frS.P.T.a).ds₁)
  (h₂ : (rowIOR (atDesc F T).p₂ (atDesc F T).l₂).shape = uLT (ckP .two) (DP.at frS.P.T.a).ds₂)
  (h₃ : (rowIOR (atDesc F T).p₃ (atDesc F T).l₃).shape = uLT (ckP .two) (DP.at frS.P.T.a).ds₃)
  (L₁ : (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) all).Str → Prop)
  (L₂ : (F.XiPub × F.S₁ × F.S₂) × (EAll (DP.at frS.P.T.a) all).Str → Prop)
  (d : (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) all).Str)
  (key : ℕ → ((F.XiPub × F.S₁) × F.S₂) × (EAll (DP.at frS.P.T.a) all).Str → κ)
  (Pv : (filesOf (kcReq N pp E) .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run eL n
    reqWithoutReply none).Provers)
  (Tl : InnerCompilerInputFieldsOverThreeProtocols (filesOf (kcReq N pp E) .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run
                                    eL n reqWithoutReply none) Pv)
  (U : SoundnessAnalysisFieldsOverThreeProtocols (filesOf (kcReq N pp E) .two DK DP tFk tJk t3k tFp tJp t3p silK runK silP F.run
                                     eL n reqWithoutReply none) Pv)

set_option quotPrecheck false in
/-- The table's meaning: its parts the integer model's own clauses; ITS SIX LETTERS ON THE READING
OF THE ORACLES FILLED AT THE VERY EIGHT LETTERS AT WHICH THE EXTRACTOR DECODES (`meaningSig`). -/
local notation "MQ" => meaningQ putReq H headPart digitsPart
  (meaningSig cs Gd arr smp ms decT Mg)

set_option quotPrecheck false in
/-- The number that the first chain's frame bears, at the filling. -/
local notation "FT" => (atDesc F T).ft₁

set_option quotPrecheck false in
/-- The file's conditions and relations: the first chain's from the table. -/
local notation "QO" => placesM (D := DP.at frS.P.T.a) (all := all) FT Nn MQ fullLinks ps get
  (firstAt pp putReq H FT get) Q₀

set_option quotPrecheck false in
/-- The table's one extractor, as a function of a block's two statements and the witness behind. -/
local notation "EX" => extQAt (Fr := frameAt (DP.at frS.P.T.a) all (DP.at frS.P.T.a).key₁ FT) cs Gd
  arr smp ms decT c₀ tokOf Nn fullLinks ps get

set_option quotPrecheck false in
/-- The relation of a block's two statements, at the table's extractor. -/
local notation "Q1" => QE (F := frameAt (DP.at frS.P.T.a) all (DP.at frS.P.T.a).key₁ FT) (QO).on₁
  (QO).R₁ EX (TokStep EX (fun w => (H.hid w).tok) fun b => repS b.1)

set_option quotPrecheck false in
/-- The plain road's conditions and relations: the first chain's from the table. -/
local notation "PL" => ({ Pl₀ with on₁ := (QO).on₁, Q₁ := Q1 } :
  PPlaces (DP.at frS.P.T.a) all (F.XiPub × F.S₁) ((F.XiPub × F.S₁) × F.S₂)
    ((F.XiPub × F.S₁ × F.S₂) × F.S₃))

/-- **THE PROOF FILE'S NAMED HYPOTHESIS ON SOUNDNESS, AT A DESCRIPTION'S OWN DECISION, FROM WHAT THE
KINDS' FILES OWE AT THE TABLE OF JOINTS**, on the plain road: one witness, carried by the table's
one extractor; the token along the steps. -/
theorem proofSound_plain_of_own (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (A : Hd.PublicCore X.P)
    (hc : HeadCuts pp putReq H headPart)
    (hO : OfDesc F T) (hf : (atDesc F T).Fits) (fit : RowFit (DP.at frS.P.T.a) all all)
    (own₁ : EachOwn
      (onQ (Fr := frameAt (DP.at frS.P.T.a) all (DP.at frS.P.T.a).key₁ FT) Nn MQ fullLinks ps get)
      (meansQ Nn MQ get) (insQ fullLinks ps) (outsQ fullLinks ps) (· ∈ start fullLinks) 0
      ((atDesc F T).p₁ :: (atDesc F T).l₁))
    (extq : EachExtQ cs Gd arr smp ms decT c₀ tokOf Nn fullLinks ps get 0
      ((atDesc F T).p₁ :: (atDesc F T).l₁))
    (rep₁ : EachRep tokOf fullLinks ps get f (fun b => repS b.1) (QO).on₁ 0
      ((atDesc F T).p₁ :: (atDesc F T).l₁))
    (htok : (fun w => (H.hid w).tok) = fun w : Wit Cells Tok MsgT => f w.tok)
    (e₂ : EachLeadsBN key (PL).on₂ (PL).Q₂ n 0 ((atDesc F T).p₂ :: (atDesc F T).l₂))
    (e₃ : EachLeads (PL).on₃ (PL).Q₃ 0 ((atDesc F T).p₃ :: (atDesc F T).l₃))
    (G : Glues (atDesc F T) PL (meansM pp N DP F all H get FT repS) L₁ L₂)
    (first_border_on : ∀ (x : (kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec)
      (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str), F.okStart x = true →
      (kcReq N pp E).conf.D y x.2 ≠ none →
      (QO).on₁ 0 ((F.pub x, F.start₁ (F.pub x)), (y, fun _ => [])))
    (hd : ∀ (x : (kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec)
      (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str),
      H.dec (get (F.pub x, F.start₁ (F.pub x)))
        (strsOf (frameAt (DP.at frS.P.T.a) all (DP.at frS.P.T.a).key₁ FT) (y, fun _ => [])) =
        (kcReq N pp E).conf.D y x.2)
    (hp : ∀ x, H.req (get (F.pub x, F.start₁ (F.pub x))) = reqWithoutReply x.1)
    (pubEarly : ∀ x rec, F.pub (reqWithoutReply x, rec) = F.pub (x, rec))
    (finReply : ∀ x rec s₁ s₂ s₃, F.fin (x, rec) s₁ s₂ s₃ = true →
      repS (F.pub (x, rec), s₁) = some (dropReq x))
    (F₁ : (kcReq N pp E).conf.Rec → (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str → κ)
    (oneKey : ∀ x rec y τ b,
      (plainP (kcReq N pp E) DP tFp tJp t3p F all T PL h₁ h₂ h₃
        (meansM pp N DP F all H get FT repS) L₁ L₂ d).out₁ ((x, rec), y) τ = some b →
      key 0 ((atDesc F T).in₂ b.1, b.2) = F₁ rec y)
    (b₁ : _root_.Iop.Err.Below
      (errOwn (atDesc F T).p₁ (atDesc F T).l₁ (DP.at frS.P.T.a).ds₁ h₁) U.εs)
    (b₂ : _root_.Iop.Err.Below
      (errOwn (atDesc F T).p₂ (atDesc F T).l₂ (DP.at frS.P.T.a).ds₂ h₂) U.εs)
    (b₃ : _root_.Iop.Err.Below
      (errOwn (atDesc F T).p₃ (atDesc F T).l₃ (DP.at frS.P.T.a).ds₃ h₃) U.εs) :
    CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataOfThreeProtocols (filesOf (kcReq N pp E) .two DK DP tFk tJk t3k tFp tJp t3p silK
                                                               runK silP F.run eL n reqWithoutReply none) Pv Tl U) :=
  proofSound_plain_at_means N E DP F all H get FT repS Q₀ Nn MQ fullLinks ps EX DK tFk tJk t3k tFp
    tJp t3p silK runK silP eL n T Pl₀ h₁ h₂ h₃ L₁ L₂ d key Pv Tl U layersSay hR h A hO hf fit
    (firstChainMeansQ pp putReq H headPart digitsPart hc Nn (meaningSig cs Gd arr smp ms decT Mg)
      (atDesc F T) ps get Q₀ own₁)
    (htok ▸ eachE_of_extQ cs Gd arr smp ms decT c₀ tokOf Nn fullLinks ps get f (fun b => repS b.1)
      (QO).on₁ _ 0 extq rep₁)
    e₂ e₃ G first_border_on hd hp pubEarly finReply F₁ oneKey b₁ b₂ b₃

end Plain

#print axioms proofSound_plain_of_own

end P5J
