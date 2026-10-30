-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/ExchangeOfB1.lean: CONDITIONAL: on the library's hypothesis h
on the public files and on every hypothesis named. THE FULL SIZE ALONE.

What is here. The thread's debt `ExchangeAtS` at the own item of the member of the feed-forward
layers' own rounds (sub-protocol K4), at the thread with the library's own values (`lettersHead`,
Honest/Thread/FirstHead.lean), WITH `JoinWorth` NO LONGER AMONG THE HYPOTHESES: `k4_exchange_tenth`
(Law/ExchangeTenth.lean) with its hypothesis hJ had from hR by `k4JoinLeft_b1_head`
(Law/JoinLeftAtHead.lean). In hJ's stead stands hR (`K4JoinB1`, Law/W/JoinLeftB1.lean): at every
state behind the member's step, five sentences on what the lookup has heard, one on the rotary
table, and the lookup's own sentence b1. Nothing new is shown: one call.

  `k4_exchange_of_b1`   **`ExchangeAtS T Said k (Item.formsT m 3 "own")`.**

Not shown here. THAT hR HOLDS AT ANY RUN. ITS FIELD b1 HOLDS ALL THE CONTENT THAT IS LEFT OF THE
BATCHED SUMCHECK's OWN CLAIM: the sum over the lookup's eight calls, at the keys' vectors of the
cells and weights, is what the lookup's end claim is worth in the world behind "back". hR is asked
at the one shape s0 of the lookup that the eight public facts fix (their field shape0). Of hR's
seven sentences the one on the rotary table is had under h (`rope_head`, Law/W/RopeHead.lean); it
stands in hR because K4JoinB1 is taken as it lies. `k4JoinB1_head` (Law/JoinB1AtHead.lean) ends in
hR's body wherever the thread stands, from the thread's clause on its open item "keys" and a tie on
the weights: b1 is moved there, not shown; `k4_exchange_of_ties` (Law/ExchangeOfTies.lean) spends
it; the form here is for a caller who has hR by another road. BESIDE hR: hRdIs, Lh, hQ, half, fits,
hb₀, hKp, hx, hMask, hL, hA, hc, hiW, hTokP: each is k4_exchange_tenth's, to the letter; its head
says of each what it asks. hA is an equation of functions on integers and binds the list to 0
outside every size; hc forces that list to stand still inside the sizes. THAT THE THREAD HOLDS AT
ANY RUN, OR THAT ANY STEP OF THE MEMBER ACCEPTS: the conclusion speaks only where `ThrS` stands and
a step accepts; where none does, hR and the conclusion hold emptily. NOT COMPLETENESS. h: the
library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean); the side library AtFullSide proves,
with no hypothesis, that h has a member at one place (AtFullSide.Top.headMember_zFull,
AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it is worth). Of h together with
hRdIs, Lh, hQ, half, fits, hb₀, hKp, hx, hMask, hL, hA, hc, hiW, hTokP, hR no example is known to
us. Every limit of Law/ExchangeTenth.lean's head holds here: the arrow on `Behind`, the clauses of
the thread that are spent, the statements under Johnson/Goal/ on which it rests (here also through
`joinPubLeft_head`, which calls the library's `refPub_in_scope`). No test that can fail stands
beside it. THE FULL SIZE ALONE (the public facts' field floor fails at the small shipped example, by
the library's word: the head of Johnson/Road/K4/PubAt.lean, which has it from LayerEnds34.lean's),
and the format's second hash function alone (`OnBytes.secondHashFunction`). Nothing on soundness or on any other
property.
No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose
name begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…:
it stopped at 81 modules under Johnson/Goal/, at 7 under Johnson/Bridge/ and at 1 that begins
Cb.Bridge; it saw 46 modules whose names hold RecCompile, none under Johnson/D/ or ThirdParty/ and
none of the three names. What lies behind the 89 is not counted: all the numbers are floors.
Through Law/LookPtsHead.lean it imports Honest/K3/Law/Thread/LayersTieHead.lean, and through
Law/RdAtCsHead.lean Honest/Thread/CsHead.lean: files of two other authors. A LAW, NOT A PART: no
file that defines a part of the proof file's description may import this one.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.ExchangeTenth
import Johnson.Desc.ProofFile.Honest.K4.Law.JoinLeftAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open OnBytes.Road (cellsOf cellsAt pt)
open OnBytes.Road.K4 (entryTrue parOf)
open OnBytes.Road.K4.W (OwnBack LookLeft uEOf)
open OnBytes.Desc.First.K4 (Par seatS formsBack)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Maker (WholeD)
open Inst.Model (ppref)
open Inst.Model.All (DF)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (Dim xS embR)
open VerifiableInference.Desc (Place Chain Strs Block Link Claim First.S)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.First.Look (layAt MatsAre)
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ MsgT MsgQ dataQ matsOfData seatTab)
open VerifiableInference.Desc.Plain.K04 (frontRun)
open VerifiableInference.OnPublicFiles (layMs)
open VerifiableInference.OnPublicFiles.Flat (Holds)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K4.SeatedHead (LaidK4 k4Sits_head)
open OnBytes.Desc.First.K4.Total (KeptAsks)
open OnBytes.Road.K4 (StatedAt readsArrayB k4PlaceAt)
open VerifiableInference.Desc.K9 (LinkHoles)
open VerifiableInference.Desc.Sound (Stated second)
open OnBytes.Road.K4.W (K4Plan)
open OnBytes.Model.Layer (ClaimEnv)
open ProofFile.Honest.K4.SeatedHead (pub_of)
open Inst.Model (tbRef)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- CONDITIONAL: on every hypothesis named; the head lists them. **THE EXCHANGE AT THE MEMBER's OWN
ITEM, FROM THE LOOKUP's OWN SENTENCE.** ν, st, R: the parameters of the frame's list `csHead`. xl:
the lookup's place at the segment. -/
theorem k4_exchange_of_b1
    (ν : Nat) (st : Nat → TS → Prop) (R : Nat → Option Forest.Heard → Prop)
    (hRdIs : Rd = ridersOf (csHead ν st R))
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : ProofFile.Inst → Array Nat}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    (hQ : k4PubOf Zp x.2 = some Qp)
    (half : H.first.find? (fun z => z.place == IM.k4Place g) =
      some (k4Half cells weights tokens look Qp))
    (fits : ∀ fr, drawsFit (declsTo cF.blocksInOrder k) fr = true → Vd w₁ →
      k4Fits Qp (look Qp fr) (tokens w₁.x) = true)
    (hb₀ : b₀ ≠ k + 1) (hKp : ∀ s s', K4KeepsM s s' → Kp (k4PlaceAt g) s s')
    {xl : VerifiableInference.Desc.First.Look.Place} (hx : layAt (P5J.At.X Zp) m = some xl)
    (hMask : ∀ c s mm E,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      K4MaskTieAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread cells weights
        tokens look Qp (h.𝔇.N.sent m 0) (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) c s mm)
    (hL : ∀ ξ, LookIsK3 look Qp Zp cF g ξ)
    (hA : ∀ c s mm E,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      ∀ d, MatsAre xl x.2.hp.tl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW h.𝔇.l3.wOf h.𝔇.l3.nr h.𝔇.l3.nc
        (layMs xl h.𝔇.sent h.𝔇.l3.rad h.𝔇.l3.oW (fun j => h.𝔇.l3.seat xl.link false j.1)
          h.𝔇.l3.arr h.𝔇.l3.msgW (Q.wit c mm.st.input (mm.st.heard ++ d)))
        ((h.𝔇.H.hid (Q.wit c mm.st.input (mm.st.heard ++ d))).MG g))
    (hc : ∀ c s mm E,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      ∀ d, CellIsList Qp (k4Wit Qp cells weights tokens (look Qp) mm.st.input)
        ((h.𝔇.H.hid (Q.wit c mm.st.input (mm.st.heard ++ d))).MG g) x.2.hp.tl)
    (hiW : ∀ c s mm E,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      ∃ i : Cm.Idx, Holds (Q.cells mm.st.input) i ∧ (g = 0 →
        embR ppref kRef (wmOf (k4Wit Qp cells weights tokens (look Qp) mm.st.input).w) =
          embR ppref kRef fun a b => ((i.mat a b : ℤ) : Cb.Gl.E)))
    (hTokP : ∀ c s mm E,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k c s mm E →
      g = 0 → TokensArePrompt tokens mm.st.input.x)
    (hR : ∀ s0, JoinPubLeft (Verify.layerShape (P5J.At.X Zp).P) DF Qp
        (Verify.weightShape (P5J.At.X Zp).P (P5J.At.X Zp).y) tbRef s0 →
      K4JoinB1 (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread
        (ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k) k cells
        weights tokens look Qp (fun _ Dt => matsOfData x.2.hp.tl (P5J.At.names3 Zp m) Dt)
        (h.𝔇.N.sent m 0) (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) x.2.hp.tl (parOf x)
        (Verify.layerShape (P5J.At.X Zp).P) DF Inst.Model.Layout.kRef tbRef s0) :
    ExchangeAtS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread Said k
      (Item.formsT m 3 "own") :=
  k4_exchange_tenth h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ ν st R hRdIs Said Lh hQ half fits
    hb₀ hKp hx hMask hL hA hc hiW hTokP
    (k4JoinLeft_b1_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁ ν st R hRdIs Said Lh hQ half
      fits hb₀ hKp hx hMask hL hA hc hR)

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4_exchange_of_b1
