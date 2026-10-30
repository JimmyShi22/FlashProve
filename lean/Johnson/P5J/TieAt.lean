-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/TieAt.lean: THE PLAIN ROAD'S PREMISE "tie" AT A DESCRIPTION OVER ITS OWN TYPE OF
INSTANCES, LAID ON THE REQUESTS ALONG A MAP: WITH hid, THE DECODER, THE TWO READERS OF THE PUBLIC
PART AND THE READER OF THE REPLY FILLED. One abbreviation, one definition, nine theorems. NO RESULT
ON THE PROTOCOL: rules.

The setting. G: a description over instances Xi; instP: the map from (request, record) to Xi; the
description at which the frame's decision stands is `G.pull instP` (Johnson/Desc/Block.lean): ONE
description. Letters: reqB (a reader of G's public part: the request file's bytes); getS: the first
chain's record as the table's; asked: what an instance asks; **DT: THE FIRST TABLE'S DECODER: A
LETTER**, with one premise, asked at instances alone: hdec: at an instance's first
statement DT is the configuration's own decoder at the stored table and the instance's record.
FILLED: reqOf := `backReq` of reqB (Johnson/Meaning/ReqBytes.lean) · decT and H.dec := DT · H :=
`hidAtSeat` · repS := `repHeard getS` (Johnson/P5J/FinReply.lean). `hdec_of_key`: a payer of hdec:
    the
decoder (`decTop` of the frame's own decoder and the record read back off a key),
    under eKey.

WHAT IS ASKED IN THE PLACE OF hd, hp, finReply, h0: FIVE SENTENCES THAT ARE MEANT TO HOLD BY THE
TEXTS OF G AND instP: hdec · eReq, eAsk (the map's two equations, read through G.pub) · hfin (the
last test's yes gives `S.finAsked`'s) · hst (the first chain's first record is a first record).
  `hd_at`, `hp_at`, `finReply_at`, `h0_at`: the four premises, as terms.
  `withReq`, `req_of_inOrder`: THE FENCE OF reqOf's DEFAULT: the table's test "in order" asks as
    well that the bytes are a request's: so at every record without a mark inside the promise req
    reads the request that stands in the bytes.
  `first_border_at`: first_border_on at the table's own promise at border 0 (at `withReq`), from
    hps, hst, hin, hpub, hpp, hbk, hms (seven sentences on the places' list, on G's start and on the
    table's letters: the two public items that are open at the start hold of a lawful first record),
    hdec and eReq.
  `tie_at`: **"tie"** from these, first_border_on and pubEarly: `tie_at_means` called once. (It
    spends four of the five: not hst.)
  `tie_at_table`: the same at the table's own promise at border 0, first_border_on paid.

Limits: those of TopPlain.lean. In `tie_at` first_border_on and pubEarly stay premises. s, seat, cs,
arr, ms, Nn, f and d₀ are letters. WHERE reqB p IS NO REQUEST FILE's BYTES reqOf p IS d₀: FENCED AT
RECORDS WITHOUT A MARK (`req_of_inOrder`); at a marked record the promise asks nothing of the bytes:
there d₀ may be read, and a law must not lean on req. The numerals 29 and 1 at
`recBack` are the full size's cube bits and answers, as the frame's type of records has them. hps
and hin are sentences on the table's letters, not on G's text. Nothing on completeness; nothing on
hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.TopPlain
import Johnson.P5J.FinReply
import Johnson.Goal.Meaning.LayersSay
import Johnson.Meaning.ReqBytes
import Johnson.Desc.Sound.DecTop
import Johnson.Desc.Sound.FirstBorder
import OnBytes.Slice.KeyBack

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

/-- The witness's cells: the matrix that the stored table decodes to. -/
abbrev CellsM (N : MatrixNums) : Type :=
  Fin N.rows → Fin (colsAt N) → VerifiableInference.OnPublicFiles.Flat.GE

section At

variable {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : Model.Verify.Public}
  (N : MatrixNums) (E : Coding (claimsReqAt (frS.toDecR frZ 402653181) N pp)) (DP : WholeD)
  {Xi : Type} (G : FileDescription Xi)
  (instP : (kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec → Xi) (all : List LeftT) {Tok : Type}
  (getS : G.S₁ → TS) (reqB : G.XiPub → ByteArray) (DT : (ℕ → Option (ℕ × List UInt64)) → G.XiPub ×
  TS → Option (CellsM N)) (asked : Xi → OnBytes.E) (d₀ : TReq) (ft : ℕ) (cs : OnBytes.Codes) (arr :
  ℕ → ℕ → ℕ) (ms : List VerifiableInference.Desc.Sound.Mem) (Nn : Numbers) (s : ℕ → Cb.Pv.Tail.Size)
  (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ) (f : Tok → Fin ppref.V)
  (hN : SeatsNamed arr Nn s seat) (hG : GroupsSeated ms Nn)

set_option quotPrecheck false in
/-- The description at which the frame's decision stands. -/
local notation "FF" => G.pull instP

set_option quotPrecheck false in
/-- The chain's record as the table reads it: the public part, and the table's own record. -/
local notation "GET" => (fun a : G.XiPub × G.S₁ => ((a.1, getS a.2) : G.XiPub × TS))

set_option quotPrecheck false in
/-- The request without its reply, read back off the request file's bytes. -/
local notation "REQOF" => (fun p : G.XiPub => (backReq (reqB p)).getD d₀)

set_option quotPrecheck false in
/-- hid, filled. -/
local notation "HH" => (hidAtSeat X cs arr ms Nn s seat f (fun a => REQOF a.1)
  (fun a y => DT y.cell a) hN hG : HidAt X G.XiPub (Wit (CellsM N) Tok MsgT) N.rows (colsAt N))

/-- **hd**: what dec reads off the chain's first record is the frame's decoder's value at the
instance's record. -/
theorem hd_at (hdec : ∀ (z : (kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec)
      (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str),
      DT (strsOf (frameAt (DP.at frS.P.T.a) all (DP.at frS.P.T.a).key₁ ft) (y, fun _ => [])).cell
          (G.pub (instP z), getS (G.start₁ (G.pub (instP z)))) =
        (kcReq N pp E).conf.D y z.2)
    (x : (kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec)
    (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str) :
    (HH).dec (GET ((FF).pub x, (FF).start₁ ((FF).pub x)))
        (strsOf (frameAt (DP.at frS.P.T.a) all (DP.at frS.P.T.a).key₁ ft) (y, fun _ => [])) =
      (kcReq N pp E).conf.D y x.2 :=
  hdec x y

omit DT in
/-- **A PAYER OF hdec**: the decoder made of the configuration's own D and of the record read back
off a table's key (`decTop`, Johnson/Desc/Sound/DecTop.lean), where the key at an instance's public
part is the instance's record's (eKey). -/
theorem hdec_of_key (keyB : G.XiPub → TableKey)
    (eKey : ∀ z, keyB (G.pub (instP z)) = keyOf (fun β : NZ => β.val) z.2)
    (z : (kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec)
    (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str) :
    decTop (P := G.XiPub) (S := TS) (DP.at frS.P.T.a).a (kcReq N pp E).conf.D
        (fun p => (recBack frS.P.v 29 1 (keyB p) : (kcReq N pp E).conf.Rec))
        (strsOf (frameAt (DP.at frS.P.T.a) all (DP.at frS.P.T.a).key₁ ft) (y, fun _ => [])).cell
        (G.pub (instP z), getS (G.start₁ (G.pub (instP z)))) =
      (kcReq N pp E).conf.D y z.2 :=
  (decTop_at (frameAt (DP.at frS.P.T.a) all (DP.at frS.P.T.a).key₁ ft) (kcReq N pp E).conf.D _
    (y, fun _ => []) _).trans (by
      show (kcReq N pp E).conf.D y (recBack frS.P.v 29 1 (keyB (G.pub (instP z)))) = _
      rw [eKey z, recBack_keyOf])

/-- **hp**: what req reads there is the request without its reply. -/
theorem hp_at (eReq : ∀ z, reqB (G.pub (instP z)) = requestBytesOf z.1.val)
    (x : (kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec) :
    (HH).req (GET ((FF).pub x, (FF).start₁ ((FF).pub x))) = reqWithoutReply x.1 := by
  show (backReq (reqB (G.pub (instP x)))).getD d₀ = reqWithoutReply x.1
  rw [eReq x, backReq_bytes]
  rfl

/-- **finReply**: the last test's yes: the reply heard is the request's own. -/
theorem finReply_at
    (hfin : ∀ ξ s₁ s₂ s₃, G.fin ξ s₁ s₂ s₃ = true → (getS s₁).finAsked (asked ξ) = true)
    (eAsk : ∀ z, asked (instP z) =
      OnBytes.Model.ofNat ((OnBytes.Model.Verify.words32 (replyBytesOf z.1.val)).getD 0 0).toNat)
    (x : (kcReq N pp E).conf.X) (rec : (kcReq N pp E).conf.Rec) (s₁ : G.S₁) (s₂ : G.S₂) (s₃ : G.S₃)
    (h : (FF).fin (x, rec) s₁ s₂ s₃ = true) :
    repHeard getS ((FF).pub (x, rec), s₁) = some (dropReq x) :=
  finReply_of_finAsked G getS asked instP hfin
    (fun x rec => (eAsk (x, rec)).trans (congrArg OnBytes.Model.ofNat (asked_word x))) x rec s₁ s₂
    s₃ h

/-- **h0**: at the chain's first record no reply is heard: it is a first record. -/
theorem h0_at {codes : OnBytes.Codes} (rq : G.XiPub → Array UInt32)
    (hst : ∀ p, VerifiableInference.Desc.First.IsStart codes (rq p) (getS (G.start₁ p)))
    (x : (kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec) :
    repHeard getS ((FF).pub x, (FF).start₁ ((FF).pub x)) = none := by
  show ((getS (G.start₁ (G.pub (instP x)))).heardTok?.bind _) = none
  rw [VerifiableInference.Desc.First.S.heardTok?_none _
    (VerifiableInference.Desc.First.isStart_heard (hst _))]
  rfl

/-- **THE FENCE OF THE SILENT DEFAULT**: the table's test "in order", which the promise asks at
every border of every record without a mark, asks as well that the request file's bytes in the
public part ARE a request's. -/
def withReq {P W : Type} (reqB : P → ByteArray) (Mg : VerifiableInference.Desc.First.Meaning P W) :
    VerifiableInference.Desc.First.Meaning P W :=
  { Mg with inOrder := fun a => Mg.inOrder a && (backReq (reqB a.1)).isSome }

/-- So inside that test what req reads is the request that stands in the bytes: d₀ is not reached.
-/
theorem req_of_inOrder
    (Mg : VerifiableInference.Desc.First.Meaning G.XiPub (Wit (CellsM N) Tok MsgT))
    (a : G.XiPub × TS) (h : (withReq reqB Mg).inOrder a = true) :
    backReq (reqB a.1) = some ((HH).req a) := by
  have h' : (Mg.inOrder a && (backReq (reqB a.1)).isSome) = true := h
  have h2 : (backReq (reqB a.1)).isSome = true := (Bool.and_eq_true _ _ ▸ h').2
  show backReq (reqB a.1) = some ((backReq (reqB a.1)).getD d₀)
  cases hb : backReq (reqB a.1) with
  | none =>
    rw [hb] at h2
    cases h2
  | some r => rfl

/-- **first_border_on**: the table's promise at the first chain's first border, at the meaning whose
parts are the integer model's own clauses: from the list of places' head (hps), "the first record is
a first record" (hst), "a lawful first record is in order" (hin) and hdec. -/
theorem first_border_at
    (Mg : VerifiableInference.Desc.First.Meaning G.XiPub (Wit (CellsM N) Tok MsgT))
    (headPart : TPart → Cm.Idx → G.XiPub × TS → Strs → Wit (CellsM N) Tok MsgT → Prop)
    (digitsPart : ℕ → G.XiPub × TS → Strs → Wit (CellsM N) Tok MsgT → Prop) (links : List ModelPart)
    (ps : List Place) (hps : ps[0]? = some VerifiableInference.Desc.First.frontPlace)
    {codes : OnBytes.Codes} (rq : G.XiPub → Array UInt32)
    (hst : ∀ p, VerifiableInference.Desc.First.IsStart codes (rq p) (getS (G.start₁ p)))
    (hin : ∀ z, (getS (G.start₁ (G.pub (instP z)))).failed = none →
      Mg.inOrder (G.pub (instP z), getS (G.start₁ (G.pub (instP z)))) = true)
    (hpub : ∀ z, (getS (G.start₁ (G.pub (instP z)))).failed = none →
      ∀ q ∈ VerifiableInference.Desc.First.pubStartM Mg.more,
        Mg.pub q (G.pub (instP z), getS (G.start₁ (G.pub (instP z)))) = true)
    (hpp : ∀ z, (getS (G.start₁ (G.pub (instP z)))).failed = none →
      ∀ q ∈ VerifiableInference.Desc.First.pubStartM Mg.more,
        Mg.pubP q (G.pub (instP z), getS (G.start₁ (G.pub (instP z)))))
    (hbk : Nn.treesAt (some VerifiableInference.Desc.First.frontPlace) = 0)
    (hms : Nn.msgsAt (some VerifiableInference.Desc.First.frontPlace) = 0)
    (hdec : ∀ (z : (kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec)
      (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str),
      DT (strsOf (frameAt (DP.at frS.P.T.a) all (DP.at frS.P.T.a).key₁ ft) (y, fun _ => [])).cell
          (G.pub (instP z), getS (G.start₁ (G.pub (instP z)))) =
        (kcReq N pp E).conf.D y z.2)
    (eReq : ∀ z, reqB (G.pub (instP z)) = requestBytesOf z.1.val)
    (x : (kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec)
    (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str) (_ : G.okStart (instP x) = true)
    (hne : (kcReq N pp E).conf.D y x.2 ≠ none) :
    onQ (Fr := frameAt (DP.at frS.P.T.a) all (DP.at frS.P.T.a).key₁ ft) Nn
      (meaningQ putReq HH headPart digitsPart (withReq reqB Mg)) links ps GET 0
      ((G.pub (instP x), G.start₁ (G.pub (instP x))), (y, fun _ => [])) :=
  onQ_zero_of_start Nn (meaningQ putReq HH headPart digitsPart (withReq reqB Mg)) links ps GET hps _
    (hst _)
    ((congrArg Option.isSome
      (hd_at N E DP G instP all getS reqB DT d₀ ft cs arr ms Nn s seat f hN hG hdec x y)).trans
      (Option.isSome_iff_ne_none.2 hne))
    (fun hm => by
      show (Mg.inOrder (G.pub (instP x), getS (G.start₁ (G.pub (instP x)))) &&
        (backReq (reqB (G.pub (instP x)))).isSome) = true
      rw [hin x hm, eReq x, backReq_bytes]
      rfl)
    (hpub x) (hpp x) hbk hms

/-- **"tie", AT THE DESCRIPTION'S OWN INSTANCES.** -/
theorem tie_at (hR : VerifierAndGoals.readFiles Z = .ok pp) (h : publicOf Z.pol Z.KL lay = .ok X)
    (A : Hd.PublicCore X.P)
    (on0 : (G.XiPub × G.S₁) × (EAll (DP.at frS.P.T.a) all).Str → Prop)
    (first_border_on : ∀ (x : (kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec)
      (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str), G.okStart (instP x) = true →
      (kcReq N pp E).conf.D y x.2 ≠ none →
      on0 ((G.pub (instP x), G.start₁ (G.pub (instP x))), (y, fun _ => [])))
    (hdec : ∀ (z : (kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec)
      (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str),
      DT (strsOf (frameAt (DP.at frS.P.T.a) all (DP.at frS.P.T.a).key₁ ft) (y, fun _ => [])).cell
          (G.pub (instP z), getS (G.start₁ (G.pub (instP z)))) =
        (kcReq N pp E).conf.D y z.2)
    (eReq : ∀ z, reqB (G.pub (instP z)) = requestBytesOf z.1.val)
    (eAsk : ∀ z, asked (instP z) =
      OnBytes.Model.ofNat ((OnBytes.Model.Verify.words32 (replyBytesOf z.1.val)).getD 0 0).toNat)
    (hfin : ∀ ξ s₁ s₂ s₃, G.fin ξ s₁ s₂ s₃ = true → (getS s₁).finAsked (asked ξ) = true)
    (pubEarly : ∀ x rec, G.pub (instP (reqWithoutReply x, rec)) = G.pub (instP (x, rec)))
    (x : (kcReq N pp E).conf.X) (rec : (kcReq N pp E).conf.Rec)
    (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str) (s₁ : G.S₁) (s₂ : G.S₂) (s₃ : G.S₃)
    (z : (EAll (DP.at frS.P.T.a) all).Str) (hok : G.okStart (instP (x, rec)) = true)
    (hf : G.fin (instP (x, rec)) s₁ s₂ s₃ = true)
    (hM : on0 ((G.pub (instP (reqWithoutReply x, rec)),
        G.start₁ (G.pub (instP (reqWithoutReply x, rec)))), (y, fun _ => [])) →
      meansM pp N DP G all HH GET ft (repHeard getS) (instP (reqWithoutReply x, rec), y)
        ((G.pub (instP (x, rec)), s₁), z)) :
    (kcReq N pp E).conf.D y rec = none ∨
      ∃ i, (kcReq N pp E).conf.D y rec = some i ∧ (kcReq N pp E).conf.Rno i x () :=
  tie_at_means N E DP FF all HH GET ft (repHeard getS) layersSay hR h A on0 first_border_on
    (hd_at N E DP G instP all getS reqB DT d₀ ft cs arr ms Nn s seat f hN hG hdec)
    (hp_at N E G instP getS reqB DT d₀ cs arr ms Nn s seat f hN hG eReq)
    pubEarly (finReply_at N E G instP getS asked hfin eAsk) x rec y s₁ s₂ s₃ z hok hf hM

/-- **"tie" AT THE TABLE'S OWN PROMISE**: `tie_at` with first_border_on paid by `first_border_at`.
-/
theorem tie_at_table (hR : VerifierAndGoals.readFiles Z = .ok pp) (h : publicOf Z.pol Z.KL lay = .ok X)
    (A : Hd.PublicCore X.P)
    (Mg : VerifiableInference.Desc.First.Meaning G.XiPub (Wit (CellsM N) Tok MsgT))
    (headPart : TPart → Cm.Idx → G.XiPub × TS → Strs → Wit (CellsM N) Tok MsgT → Prop)
    (digitsPart : ℕ → G.XiPub × TS → Strs → Wit (CellsM N) Tok MsgT → Prop) (links : List ModelPart)
    (ps : List Place) (hps : ps[0]? = some VerifiableInference.Desc.First.frontPlace)
    {codes : OnBytes.Codes} (rq : G.XiPub → Array UInt32)
    (hst : ∀ p, VerifiableInference.Desc.First.IsStart codes (rq p) (getS (G.start₁ p)))
    (hin : ∀ z, (getS (G.start₁ (G.pub (instP z)))).failed = none →
      Mg.inOrder (G.pub (instP z), getS (G.start₁ (G.pub (instP z)))) = true)
    (hpub : ∀ z, (getS (G.start₁ (G.pub (instP z)))).failed = none →
      ∀ q ∈ VerifiableInference.Desc.First.pubStartM Mg.more,
        Mg.pub q (G.pub (instP z), getS (G.start₁ (G.pub (instP z)))) = true)
    (hpp : ∀ z, (getS (G.start₁ (G.pub (instP z)))).failed = none →
      ∀ q ∈ VerifiableInference.Desc.First.pubStartM Mg.more,
        Mg.pubP q (G.pub (instP z), getS (G.start₁ (G.pub (instP z)))))
    (hbk : Nn.treesAt (some VerifiableInference.Desc.First.frontPlace) = 0)
    (hms : Nn.msgsAt (some VerifiableInference.Desc.First.frontPlace) = 0)
    (hdec : ∀ (z : (kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec)
      (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str),
      DT (strsOf (frameAt (DP.at frS.P.T.a) all (DP.at frS.P.T.a).key₁ ft) (y, fun _ => [])).cell
          (G.pub (instP z), getS (G.start₁ (G.pub (instP z)))) =
        (kcReq N pp E).conf.D y z.2)
    (eReq : ∀ z, reqB (G.pub (instP z)) = requestBytesOf z.1.val)
    (eAsk : ∀ z, asked (instP z) =
      OnBytes.Model.ofNat ((OnBytes.Model.Verify.words32 (replyBytesOf z.1.val)).getD 0 0).toNat)
    (hfin : ∀ ξ s₁ s₂ s₃, G.fin ξ s₁ s₂ s₃ = true → (getS s₁).finAsked (asked ξ) = true)
    (pubEarly : ∀ x rec, G.pub (instP (reqWithoutReply x, rec)) = G.pub (instP (x, rec)))
    (x : (kcReq N pp E).conf.X) (rec : (kcReq N pp E).conf.Rec)
    (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str) (s₁ : G.S₁) (s₂ : G.S₂) (s₃ : G.S₃)
    (z : (EAll (DP.at frS.P.T.a) all).Str) (hok : G.okStart (instP (x, rec)) = true)
    (hf : G.fin (instP (x, rec)) s₁ s₂ s₃ = true)
    (hM : onQ (Fr := frameAt (DP.at frS.P.T.a) all (DP.at frS.P.T.a).key₁ ft) Nn
        (meaningQ putReq HH headPart digitsPart (withReq reqB Mg)) links ps GET 0
        ((G.pub (instP (reqWithoutReply x, rec)),
          G.start₁ (G.pub (instP (reqWithoutReply x, rec)))), (y, fun _ => [])) →
      meansM pp N DP G all HH GET ft (repHeard getS) (instP (reqWithoutReply x, rec), y)
        ((G.pub (instP (x, rec)), s₁), z)) :
    (kcReq N pp E).conf.D y rec = none ∨
      ∃ i, (kcReq N pp E).conf.D y rec = some i ∧ (kcReq N pp E).conf.Rno i x () :=
  tie_at N E DP G instP all getS reqB DT asked d₀ ft cs arr ms Nn s seat f hN hG hR h A _
    (first_border_at N E DP G instP all getS reqB DT d₀ ft cs arr ms Nn s seat f hN hG Mg headPart
      digitsPart links ps hps rq hst hin hpub hpp hbk hms hdec eReq)
    hdec eReq eAsk hfin pubEarly x rec y s₁ s₂ s₃ z hok hf hM

end At

#print axioms hd_at
#print axioms hdec_of_key
#print axioms hp_at
#print axioms finReply_at
#print axioms h0_at
#print axioms req_of_inOrder
#print axioms first_border_at
#print axioms tie_at
#print axioms tie_at_table

end P5J
