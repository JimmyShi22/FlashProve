-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/TopMeans.lean: OVER THE JOINT BETWEEN THE TABLE OF JOINTS' FIRST RELATION AND THE RULE
    FOR
A PROOF FILE, THE END THEOREM OVER IT, ON THE ROAD WITH EXTRACTORS. One theorem; the joint itself
stands in Johnson/P5J/TopJoint.lean.
NO RESULT ON THE PROTOCOL: a rule, of whose premises no
description of the protocol is shown to meet one.

WHAT IS STILL A LETTER, FIRST. `H : HidAt` (how a witness of the table is read): hid (what it hides
of the integer model's run), dec (what the stored word decodes to, read off a statement of the
chain), req (the request's public part, read off the record); the table's `Meaning` Mg: the head's
parts and the digits' part among its letters; get (from the chain's record to the table's); back
(from the description's public part to the request with the record); the extractors and errors block
by block (rest₁, rest₂, rest₃). THE TABLE HAS THE FIRST CHAIN ALONE: at the second and the third
chain the conditions and relations are Q₀'s: letters.

What is said. `proofSoundOfData` (Johnson/Flat/ProofOfData.lean) gives the proof
file's named hypothesis on soundness (`CompilerSoundnessConditionStatements.proofSound`) at a description's own decision F.run,
at the rule of composition's own frame: the description's blocks as the maker cuts them (`piecesAt`,
`atDescFin`), conditions and relations Q at the borders. Of the first border it asks two facts. The
second: the relation there tells the object's relation at the request with the witness's token put
in (`firstRel`). The table's first relation is the integer model's `firstMeans` at what the witness
hides (`firstAt`, Johnson/P5J/MeansQ.lean).

Main theorems:
  `firstRel_of_firstAt`: **THE JOINT**: `firstAt` gives `firstRel`, at the full size's frame (`kcReq
    N pp E`), by `frameRel_of_firstMeans` and `inRange_of_letters`
    (Johnson/Goal/Meaning/Row.lean); under two equations on the letters: what dec and req read off
    the chain's
    statement are the decoder's value and the request.
  `proofSound_at_means`: **THE END THEOREM**: `proofSoundOfData` at `kcReq N pp E` and at Q := the
    table's `placesM` with `firstAt` in front: its second fact at the first border PAID by the
    joint, `TieGlue` paid by `glueReq`, `PutEarly` by `putEarlyReq`, and at the first chain
    `EachGoodIn` in `EachGood`'s place (`eachGoodOfGoodIn`): what `firstChainMeansQ` yields from the
    kinds' own laws.

THE PREMISES THAT ARE LEFT, EACH WITH ITS OWNER. LS (what the layers' 24 sub-proofs say): a theorem
of the integer model's files (`layersSay`); not imported here · hR, h, A: the public files are read
and in scope: theirs · hdata, hseal, e₁, e₂, e₃: tests with code on the description · fin: the ends'
part of the last test: the description's files · good₁: THE KINDS' FILES, through the table
(`EachOwn`) · lost₂: the shared chain's files: a law in two parts a block · good₃: the third chain's
files · glued: the relations at the chains' ends fit: this folder's · hext: the token in the
extractors' yield is what the reply's rounds show: this folder's, from the table's one extractor ·
**first_border_on**: where the public tests pass and the word decodes, the table's promise holds at
the start: a row under that name: nobody's · hd, hp: by the
make of dec, req and back: whoever fills H · pubEarly, pubKeeps: the reply's word is no part of what
the chains are started from, and ALL ELSE of the request, with the whole record, can be read back
from it: facts on the description's own `pub`: its files · oneKey: the shared chain's first record
hangs on the record alone · opens: a test on the written lists · below₁, below₂, below₃: numbers.
LAWS THAT STAND INSIDE TWO RECORDS AMONG THE LETTERS: PREMISES TOO. `Hr : F.Hears`: cut (the first
chain's flat list, cut at the reply's block) · lays (that block lays what it hears) · leaves (no
later block turns it) · fins (the last test's yes: what was heard is what is asked) · `H.seams`: the
three seams of the model's relation, at every witness.

Silly members. At H.hid constant the joint still holds, and says what it says of that one run; at a
Q₀ whose conditions never hold lost₂ and good₃ are free and glued cannot be met. At U.εs at least a
round's share of proof of work every law is met by "bad: every challenge that passes the work"
so "paid" means something only with U.εs stated below that.

Limits: those of ProofOfData.lean, MeansQ.lean and Meaning/Row.lean. hext runs over ALL transcripts,
also those that the reply's block refuses: rd has to answer "some" at every one. ft is idle: the
table reads a frame's depth and its list of trees alone. ps is tied to F by nothing: it is meant as
the places of F's own first chain. THAT THE TOP STATEMENTS ARE SPENT AT THIS `filesOf` AT
F.run is said nowhere here. It stands on three other sets of files, taken at the statements cited
alone: the files with `proofSoundOfData`; `paidAtDesc`, which calls itself a trial; the integer
model's files. Nothing on completeness; nothing on hiding.





Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.TopJoint

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
open VerifiableInference.Desc (Block FileDescription Place)
open VerifiableInference.Desc.First (ModelPart Numbers)
open VerifiableInference.Desc.Sound
open _root_.Iop (oneExternalString Tr)
open _root_.Run _root_.Run.PQ

/-! ## 2 The end theorem, on the road with extractors -/

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
  (Mg : VerifiableInference.Desc.First.Meaning P W) (links : List ModelPart) (ps : List Place)
  (get : F.XiPub × F.S₁ → P × TS) (ft : ℕ)
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
/-- The file's conditions and relations: the first chain's from the table of joints, with the
integer model's relation in front. -/
local notation "QM" => placesM (D := DP.at frS.P.T.a) (all := allOf (DP.at frS.P.T.a)) ft Nn Mg
  links ps get (firstAt pp putReq H ft get) Q₀

/-- **THE PROOF FILE'S NAMED HYPOTHESIS ON SOUNDNESS, AT A DESCRIPTION'S OWN DECISION, ITS FIRST
RELATION BEING THE INTEGER MODEL'S.** -/
theorem proofSound_at_means (LS : LayersSay) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (A : Hd.PublicCore X.P)
    (hdata : F.data file = .ok (DP.at frS.P.T.a)) (hseal : F.sealLast = true)
    (e₁ : F.first.blocksInOrder = b₁ :: l₁) (e₂ : F.shared.blocksInOrder = b₂ :: l₂) (e₃ : F.second.blocksInOrder = b₃ :: l₃)
    (hfin : FinGives F g)
    (good₁ : EachGoodIn (QM).on₁ (QM).R₁ 0 ((TT).p₁ :: (TT).l₁))
    (lost₂ : EachLostBoth n (QM).on₂ (QM).R₂
      (actsOf Prod.snd (DP.at frS.P.T.a).t₁ (TT).p₂ (TT).l₂) 0 ((TT).p₂ :: (TT).l₂))
    (good₃ : EachGood (QM).on₃ (QM).R₃ 0 ((TT).p₃ :: (TT).l₃))
    (glued : (TT).Glued QM)
    (hext : ExtRowAt (fun w => (H.hid w).tok) rd Hr.pre.length (TT).p₁ (TT).l₁)
    (first_border_on : ∀ (x : (kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec)
      (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str), F.okStart x = true →
      (kcReq N pp E).conf.D y x.2 ≠ none →
      (QM).on₁ 0 ((F.pub x, F.start₁ (F.pub x)), (y, fun _ => [])))
    (hd : ∀ (x : (kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec)
      (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str),
      H.dec (get (F.pub x, F.start₁ (F.pub x)))
        (strsOf (frameAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (DP.at frS.P.T.a).key₁ ft)
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
  proofSoundOfData (kcReq N pp E) DK DP tFk tJk t3k tFp tJp t3p silK runK silP F eL n
    reqWithoutReply file b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d wEnd g QM dropReq putReq
    (fun w => (H.hid w).tok) rd Hr (fun _ => ()) back s₂ Pv Tl U hdata hseal e₁ e₂ e₃ hfin
    (eachGoodOfGoodIn _ _ _ 0 good₁) lost₂ good₃ glued hext first_border_on
    (fun x y w hw => firstRel_of_firstAt LS hR h A N E DP H ft get _ w (back (F.pub x), y)
      (hd x y) (hp x) hw)
    pubEarly pubKeeps (putEarlyReq N pp E) (glueReq N pp E) oneKey opens below₁ below₂ below₃

end Top

#print axioms proofSound_at_means

end P5J
