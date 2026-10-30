-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/TieStart.lean: THE PROOF FILE'S SIXTH FIELD ("tie") HAS A BILL OF ITS OWN: `TieStart`:
ELEVEN OF
`RowsTied`'S 22 FIELDS (SevenOfTied.lean), TO THE LETTER: THE SCOPE'S TWO AND NINE FACTS ON A START:
NO LAW OF ANY KIND OF BLOCK STANDS AMONG THEM.
  `RowsTied.tieStart`: the eleven out of the 22.
  **`tie_of_start`**: in scope, `TieStart` gives the premise `tie` of the rule `proofSound_at_descB`
    (Johnson/Desc/Plain/BothAtDesc.lean), TO THE LETTER, at F := F₀.pull instP, the maker's cut TP,
    Pl := PL and M := `meansSome` (Johnson/Goal/Meaning/TieAtSome.lean): by
    `tie_of_some` (the same file) at
    `tieOwesSome_at` (MeansSome.lean). From it the structure's field follows by
    `ties_of_tie` (Johnson/Desc/Plain/BothAtDescSteps.lean) under `OfDesc`, `RowFit` and "the public
    part does not read the reply".
  `front_first_full`: the third of the eleven at ps := the driver's flat places at the full size's
    list of segments: by the kernel.
WHAT THE ELEVEN SAY: the public files are read (2) · the list of places begins with the front
block's · the first chain's first record is a first record · a lawful first record is in order ·
every public item that is open at the start holds there, as a Bool and as a sentence · no tree and
no message stand in front of the front block · at an instance the first table's decoder is the
configuration's, the request's bytes and the asked element are the instance's (3) · the last test's
yes asks the asked element.
Limits: that file's. A joining of rules: no member is known. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.SevenOfTied
import Johnson.P5J.MeansSome

set_option autoImplicit false
set_option maxRecDepth 40000

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

variable {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : Model.Verify.Public}
  (N : MatrixNums) (E : Coding (claimsReqAt (frS.toDecR frZ 402653181) N pp)) (DP : WholeD)
  {XiP : Type} (F₀ : FileDescription XiP)
  (instP : (kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec → XiP) {Tok : Type}
  (getS : F₀.S₁ → TS) (reqB : F₀.XiPub → ByteArray) (DT : (ℕ → Option (ℕ × List UInt64)) → F₀.XiPub
  × TS → Option (CellsM N)) (asked : XiP → OnBytes.E) (d₀ : TReq) (cs : OnBytes.Codes) (arr : ℕ → ℕ
  → ℕ) (ms : List Mem) (Nn : Numbers) (s : ℕ → Cb.Pv.Tail.Size)
  (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ) (f : Tok → Fin ppref.V)
  (hN : SeatsNamed arr Nn s seat) (hG : GroupsSeated ms Nn)
  (Q₀ : PlacesAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) F₀ (Wit (CellsM N) Tok MsgT))
  (Mg : VerifiableInference.Desc.First.Meaning F₀.XiPub (Wit (CellsM N) Tok MsgT))
  (ps : List Place)
  (headPart : TPart → Cm.Idx → F₀.XiPub × TS → Strs → Wit (CellsM N) Tok MsgT → Prop)
  (digitsPart : ℕ → F₀.XiPub × TS → Strs → Wit (CellsM N) Tok MsgT → Prop)
  {Xg : Type} (Gd : FileDescription Xg)
  (smp : F₀.XiPub × TS → (s : Sending) → (i : Fin s.l.length) →
    Option ((Johnson.Pack.sigOf cs s.l).om i).Smp)
  (c₀ : CellsM N) (tokOf : F₀.XiPub × TS → Tok)
  (Ns : NumbersS) (MgS : MeaningS F₀.S₂ (F₀.XiPub × F₀.S₁) (Wit (CellsM N) Tok MsgT))
  (ML : MeaningL F₀.S₃ (Wit (CellsM N) Tok MsgT)) (Pm : PromMeaning F₀.S₂)
  (PLm : PromMeaningL F₀.S₂ F₀.S₃ (F₀.XiPub × F₀.S₁)) (split : Bool)
  (Q₂ : ℕ → ((F₀.XiPub × F₀.S₁) × F₀.S₂) × (EAll (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a))).Str →
    ((F₀.XiPub × F₀.S₁) × F₀.S₂) × (EAll (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a))).Str → Prop)
  (rP : RecFull) (depthReq : ℕ)
  (c₁ : Block F₀.S₁ F₀.Cl) (k₁ : List (Block F₀.S₁ F₀.Cl)) (c₂ : Block F₀.S₂ F₀.Cl)
  (k₂ : List (Block F₀.S₂ F₀.Cl)) (c₃ : Block F₀.S₃ F₀.Cl) (k₃ : List (Block F₀.S₃ F₀.Cl))
  (e₁ : (i : ℕ) → (ds : List RDT) → (F₀.XiPub × F₀.S₁) ×
      (frameAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (DP.at frS.P.T.a).key₁ 0).E.Str →
      _root_.Iop.Tr (uLT (ckP .two) ds) → Wit (CellsM N) Tok MsgT → Wit (CellsM N) Tok MsgT)
  (e₂ : (i : ℕ) → (ds : List RDT) → ((F₀.XiPub × F₀.S₁) × F₀.S₂) ×
      (frameAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (DP.at frS.P.T.a).key₂ 0).E.Str →
      _root_.Iop.Tr (uLT (ckP .two) ds) → Wit (CellsM N) Tok MsgT → Wit (CellsM N) Tok MsgT)
  (e₃ : (i : ℕ) → (ds : List RDT) → ((F₀.XiPub × F₀.S₁ × F₀.S₂) × F₀.S₃) ×
      (frameAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (DP.at frS.P.T.a).key₃
        F₀.lastChainFirstTreeNumber).E.Str →
      _root_.Iop.Tr (uLT (ckP .two) ds) → Wit (CellsM N) Tok MsgT → Wit (CellsM N) Tok MsgT)
  (dW wEnd : Wit (CellsM N) Tok MsgT) (kS₂ : RecFull → F₀.S₂)

set_option quotPrecheck false in
/-- Every tree of the file. -/
local notation "AL" => allOf (DP.at frS.P.T.a)

set_option quotPrecheck false in
/-- The three rows of pieces, each with the cap as its errors. -/
local notation "TT" => (piecesAt (ckP .two) F₀ (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ (restCap e₁)
  (restCap e₂) (restCap e₃) dW wEnd)

set_option quotPrecheck false in
/-- The same pieces, at the description laid on the requests. -/
local notation "TP" => (piecesAt (ckP .two) (F₀.pull instP) (DP.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃
  (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)

set_option quotPrecheck false in
/-- The chain's record as the table reads it. -/
local notation "GET" => (fun a : F₀.XiPub × F₀.S₁ => ((a.1, getS a.2) : F₀.XiPub × TS))

set_option quotPrecheck false in
/-- hid, filled. -/
local notation "HH" => (hidAtSeat X cs arr ms Nn s seat f
  (fun a => (backReq (reqB a.1)).getD d₀) (fun a y => DT y.cell a) hN hG :
  HidAt X F₀.XiPub (Wit (CellsM N) Tok MsgT) N.rows (colsAt N))

set_option quotPrecheck false in
/-- The first table's meaning. -/
local notation "MQ" => meaningQ putReq HH headPart digitsPart
  (meaningSig cs Gd arr smp ms DT (withReq reqB Mg))

set_option quotPrecheck false in
/-- The file's conditions and relations: the first chain's from its table. -/
local notation "QO" => placesM (D := DP.at frS.P.T.a) (all := AL) 0 Nn MQ fullLinks ps GET
  (firstAt pp putReq HH 0 GET) Q₀

set_option quotPrecheck false in
/-- The first table's one extractor. -/
local notation "EX" => extQAt (Fr := frameAt (DP.at frS.P.T.a) AL (DP.at frS.P.T.a).key₁ 0) cs Gd
  arr smp ms DT c₀ tokOf Nn fullLinks ps GET

set_option quotPrecheck false in
/-- The last chain's start, as the rule of composition takes it. -/
local notation "ST3" => fun p a b => (F₀.start₃ p a b).toOption

set_option quotPrecheck false in
/-- The plain road's conditions and relations: all three chains' from their tables. -/
local notation "PL" => ({ plTables TT GET Nn MQ fullLinks ps Ns MgS ML Pm PLm split Q₂ with
    on₁ := (QO).on₁
    Q₁ := QE (F := frameAt (DP.at frS.P.T.a) AL (DP.at frS.P.T.a).key₁ 0) (QO).on₁ (QO).R₁ EX
      (TokStep EX (fun w => ((HH).hid w).tok) fun b => repHeard getS b.1) } :
  PPlaces (DP.at frS.P.T.a) AL (F₀.XiPub × F₀.S₁) ((F₀.XiPub × F₀.S₁) × F₀.S₂)
    ((F₀.XiPub × F₀.S₁ × F₀.S₂) × F₀.S₃))

/-- **THE SIXTH FIELD's BILL.** -/
structure TieStart (codes : OnBytes.Codes) (rq : F₀.XiPub → Array UInt32) : Prop where
  /-- the files are read -/
  scope_reads : VerifierAndGoals.readFiles Z = .ok pp
  /-- the program's public record of them -/
  scope_public : publicOf Z.pol Z.KL lay = .ok X
  /-- the list's first place is the front's -/
  front_place_first : ps[0]? = some VerifiableInference.Desc.First.frontPlace
  /-- the first chain's first record is a start at the request's words -/
  start_is_the_requests : ∀ p,
    VerifiableInference.Desc.First.IsStart codes (rq p) (getS (F₀.start₁ p))
  /-- "in order" holds at a first record without a mark -/
  start_in_order : ∀ z, (getS (F₀.start₁ (F₀.pub (instP z)))).failed = none →
    (meaningSig cs Gd arr smp ms DT Mg).inOrder
      (F₀.pub (instP z), getS (F₀.start₁ (F₀.pub (instP z)))) = true
  /-- every public item that is open at the chain's start holds there -/
  start_public_items : ∀ z, (getS (F₀.start₁ (F₀.pub (instP z)))).failed = none →
    ∀ q ∈ VerifiableInference.Desc.First.pubStartM (meaningSig cs Gd arr smp ms DT Mg).more,
      (meaningSig cs Gd arr smp ms DT Mg).pub q
        (F₀.pub (instP z), getS (F₀.start₁ (F₀.pub (instP z)))) = true
  /-- and its sentence, where it has one -/
  start_public_sentences : ∀ z, (getS (F₀.start₁ (F₀.pub (instP z)))).failed = none →
    ∀ q ∈ VerifiableInference.Desc.First.pubStartM (meaningSig cs Gd arr smp ms DT Mg).more,
      (meaningSig cs Gd arr smp ms DT Mg).pubP q
        (F₀.pub (instP z), getS (F₀.start₁ (F₀.pub (instP z))))
  /-- the plan's numbers: no tree and no message stand in front of the front block -/
  front_no_trees : Nn.treesAt (some VerifiableInference.Desc.First.frontPlace) = 0
  front_no_messages : Nn.msgsAt (some VerifiableInference.Desc.First.frontPlace) = 0
  /-- the map from requests to instances gives the key, the request's bytes, the asked reply -/
  requests_to_instances : (∀ (z : (kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec)
      (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str),
      DT (strsOf (frameAt (DP.at frS.P.T.a) AL (DP.at frS.P.T.a).key₁ 0) (y, fun _ => [])).cell
          (F₀.pub (instP z), getS (F₀.start₁ (F₀.pub (instP z)))) =
        (kcReq N pp E).conf.D y z.2) ∧
    (∀ z, reqB (F₀.pub (instP z)) = requestBytesOf z.1.val) ∧
    ∀ z, asked (instP z) =
      OnBytes.Model.ofNat ((OnBytes.Model.Verify.words32 (replyBytesOf z.1.val)).getD 0 0).toNat
  /-- the last test's yes gives that the asked reply was heard -/
  fin_is_canonical : ∀ ξ s₁ s₂ s₃, F₀.fin ξ s₁ s₂ s₃ = true → (getS s₁).finAsked (asked ξ) = true

/-- The eleven out of the 22. -/
theorem RowsTied.tieStart {codes : OnBytes.Codes} {rq : F₀.XiPub → Array UInt32}
    (R : RowsTied (Z := Z) (lay := lay) (X := X) N E DP F₀ instP getS reqB DT asked d₀ cs
      arr ms Nn s seat f hN hG Q₀ Mg ps headPart digitsPart Gd smp c₀ tokOf Ns MgS ML Pm PLm split
      Q₂ depthReq c₁ k₁ c₂ k₂ c₃ k₃ e₁ e₂ e₃ dW wEnd kS₂ codes rq) :
    TieStart (Z := Z) (lay := lay) (X := X) N E DP F₀ instP getS reqB DT asked cs arr ms Nn Mg ps
      Gd smp codes rq :=
  ⟨R.scope_reads, R.scope_public, R.front_place_first, R.start_is_the_requests, R.start_in_order,
    R.start_public_items, R.start_public_sentences, R.front_no_trees, R.front_no_messages,
    R.requests_to_instances, R.fin_is_canonical⟩

set_option maxHeartbeats 4000000 in
/-- **THE RULE's PREMISE "tie", TO THE LETTER, FROM FACTS ON A START.** -/
theorem tie_of_start (hZ : VerifierAndGoals.InScope Z = true) {codes : OnBytes.Codes}
    (rq : F₀.XiPub → Array UInt32)
    (R : TieStart (Z := Z) (lay := lay) (X := X) N E DP F₀ instP getS reqB DT asked cs arr ms Nn Mg
      ps Gd smp codes rq) :
    ∀ x rec (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str)
      (τ : Tr (chainsOf (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty).sh)
      (s₁ : F₀.S₁) (s₂ : F₀.S₂) (s₃ : F₀.S₃) (z : (EAll (DP.at frS.P.T.a) AL).Str),
      (F₀.pull instP).okStart (x, rec) = true →
      silP (x, rec)
        ((chainsOf (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty).msgF τ).2
        ((chainsOf (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty).msgJ τ).2
        ((chainsOf (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP) ByteArray.empty).msg3 τ).2 =
          true →
      (F₀.pull instP).fin (x, rec) s₁ s₂ s₃ = true →
      ((PL).on₁ 0 ((atDesc (F₀.pull instP) TP).in₁ (reqWithoutReply x, rec), (y, fun _ => [])) →
        (meansSome N pp E DP (F₀.pull instP) AL X (repHeard getS)) ((reqWithoutReply x, rec), y)
          (((F₀.pull instP).pub (x, rec), s₁), z)) →
      (kcReq N pp E).conf.D y rec = none ∨
        ∃ i, (kcReq N pp E).conf.D y rec = some i ∧ (kcReq N pp E).conf.Rno i x () :=
  tie_of_some N pp E DP (front₀ rP) (join₀ rP) ByteArray.empty silP (F₀.pull instP) AL TP PL X
    (repHeard getS) hZ R.scope_reads R.scope_public
    (tieOwesSome_at N E DP F₀ instP AL getS reqB DT asked d₀ 0 cs arr ms Nn s seat f hN hG TP
      PL (meaningSig cs Gd arr smp ms DT Mg) headPart digitsPart fullLinks ps rfl
      R.front_place_first rq R.start_is_the_requests R.start_in_order R.start_public_items
      R.start_public_sentences R.front_no_trees R.front_no_messages R.requests_to_instances.1
      R.requests_to_instances.2.1 R.requests_to_instances.2.2 R.fin_is_canonical)

set_option maxRecDepth 1000000 in
/-- `front_place_first` at the full size's written list: by the kernel's evaluation. -/
theorem front_first_full :
    (VerifiableInference.Desc.First.flatPlacesOf fullLinks true)[0]? =
      some VerifiableInference.Desc.First.frontPlace := by decide +kernel

end P5J

#print axioms P5J.front_first_full
#print axioms P5J.RowsTied.tieStart
#print axioms P5J.tie_of_start
