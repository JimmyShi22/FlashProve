-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/MeansSome.lean: THIS FOLDER'S SIDE OF THE PROOF FILE'S LETTER M
AS IT IS CHOSEN (
`meansSome`, Johnson/Goal/Meaning/TieAtSome.lean: the integer model's `firstMeans` at SOME hidden
values, with the clause on the token): THREE THEOREMS.
  `meansSome_of_meansM`: `meansM` (TopPlain.lean: "some witness w₀ of the first border's
    relation, whose token is the reply heard"), read at an instance, GIVES `meansSome` (under hdec,
    eReq): h := hid w₀. By `hd_at`,
    `hp_at` (TieAt.lean) and the model's `putReq_early`.
  `first_border_free`: `first_border_at` without its idle premise on the start's test.
  `tieOwesSome_at`: `TieOwesSome` (TieAtSome.lean), both fields: on := the first border; finReply :=
    `finReply_at` with the model's `putReq_back_iff`.
Limits: TieAtSome.lean's. A joining of rules: no member is known. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.TieAt
import Johnson.Goal.Meaning.TieAtSome
import Johnson.Goal.Meaning.RowEarly

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

/-- **`meansM` GIVES THE CHOSEN M.** -/
theorem meansSome_of_meansM
    (hdec : ∀ (z : (kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec)
      (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str),
      DT (strsOf (frameAt (DP.at frS.P.T.a) all (DP.at frS.P.T.a).key₁ ft) (y, fun _ => [])).cell
          (G.pub (instP z), getS (G.start₁ (G.pub (instP z)))) =
        (kcReq N pp E).conf.D y z.2)
    (eReq : ∀ z, reqB (G.pub (instP z)) = requestBytesOf z.1.val)
    (a : ((kcReq N pp E).conf.X × (kcReq N pp E).conf.Rec) ×
      (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str)
    (c : (G.XiPub × G.S₁) × (EAll (DP.at frS.P.T.a) all).Str)
    (h : meansM pp N DP G all HH GET ft (repHeard getS) (instP a.1, a.2) c) :
    meansSome N pp E DP FF all X (repHeard getS) a c := by
  obtain ⟨w₀, hf, ht⟩ := h
  refine ⟨(HH).hid w₀, ?_, ht⟩
  have hf' : firstMeans X pp putReq
      ((HH).dec (GET ((FF).pub a.1, (FF).start₁ ((FF).pub a.1)))
        (strsOf (frameAt (DP.at frS.P.T.a) all (DP.at frS.P.T.a).key₁ ft) (a.2, fun _ => [])))
      ((HH).req (GET ((FF).pub a.1, (FF).start₁ ((FF).pub a.1)))) ((HH).hid w₀) := hf
  rw [hd_at N E DP G instP all getS reqB DT d₀ ft cs arr ms Nn s seat f hN hG hdec a.1 a.2,
    hp_at N E G instP getS reqB DT d₀ cs arr ms Nn s seat f hN hG eReq a.1] at hf'
  intro M i hM hH
  have := hf' M i hM hH
  rwa [Meaning.putReq_early] at this

/-- **first_border_on**: the table's promise at the first chain's first border, at the meaning whose
parts are the integer model's own clauses: from the list of places' head (hps), "the first record is
a first record" (hst), "a lawful first record is in order" (hin) and hdec. -/
theorem first_border_free
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
    (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str)
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

/-- **WHAT THE DESCRIPTION OWES FOR "tie" AT THE CHOSEN M, BOTH FIELDS.** Pl: any places whose first
chain's promise is the table's (hPl). -/
theorem tieOwesSome_at {X₁ X₂ : Type}
    (T : ThreeAt (ckP .two) (DP.at frS.P.T.a) all FF X₁ X₂ (Wit (CellsM N) Tok MsgT))
    (Pl : PPlaces (DP.at frS.P.T.a) all (G.XiPub × G.S₁) ((G.XiPub × G.S₁) × G.S₂)
      ((G.XiPub × G.S₁ × G.S₂) × G.S₃))
    (Mg : VerifiableInference.Desc.First.Meaning G.XiPub (Wit (CellsM N) Tok MsgT))
    (headPart : TPart → Cm.Idx → G.XiPub × TS → Strs → Wit (CellsM N) Tok MsgT → Prop)
    (digitsPart : ℕ → G.XiPub × TS → Strs → Wit (CellsM N) Tok MsgT → Prop) (links : List ModelPart)
    (ps : List Place)
    (hPl : Pl.on₁ = onQ (Fr := frameAt (DP.at frS.P.T.a) all (DP.at frS.P.T.a).key₁ ft) Nn
      (meaningQ putReq HH headPart digitsPart (withReq reqB Mg)) links ps GET)
    (hps : ps[0]? = some VerifiableInference.Desc.First.frontPlace)
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
    (hfin : ∀ ξ s₁ s₂ s₃, G.fin ξ s₁ s₂ s₃ = true → (getS s₁).finAsked (asked ξ) = true) :
    TieOwesSome N pp E DP FF all T Pl (repHeard getS) where
  on := fun x rec y M _ hM => by
    rw [hPl]
    exact first_border_free N E DP G instP all getS reqB DT d₀ ft cs arr ms Nn s seat f hN hG Mg
      headPart digitsPart links ps hps rq hst hin hpub hpp hbk hms hdec eReq
      (reqWithoutReply x, rec) y (by rw [hM]; exact fun e => by cases e)
  finReply := fun x rec s₁ s₂ s₃ _ hf =>
    ⟨dropReq x, finReply_at N E G instP getS asked hfin eAsk x rec s₁ s₂ s₃ hf,
      (putReq_back_iff x (dropReq x)).2 fun _ => rfl⟩

end At

#print axioms meansSome_of_meansM
#print axioms first_border_free
#print axioms tieOwesSome_at

end P5J
