-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerFieldLaid.lean: THE LEDGER's END IN THE FIELD's OWN TEXT
(ledger_whole_fills_field, Johnson/Desc/K14/Law/LedgerByMakeTop.lean: the twelve sub-protocols of
the shared chain, each with its error bound for a batch, at the pieces that the maker cuts out of
the IOP as written in Lean) WITH THE PAYERS THAT ARE HOME LAID IN, AND ITS LETTERS AT THE SHARED
TABLE's CONSTANT (Sh.‹name› at A := ShPlan.mk Q G pLast rad2 rad5 Wr 2 · O := ShOpen.mk arr c₀ get
smp₁ ms₁ decT₁ N₁ links Mg₁ Pw Rend matC held). THE MADE PIECES' LETTERS ARE NO LETTERS ANY MORE:
they are had by ∃ in front of the call. THE SEAT's LETTERS ARE LAID (ch · Q · tests · πA πB · rA rB
· pLast · rad2 rad5 · Pw · arr · Cells · c₀ · matC · held).
THE STATEMENT IS MADE BY PROGRAM: ledger_whole_fills_field's own binders, in its own words, with the
letters of the maps laid in and the paid premises struck; all binders are the theorem's own, sorted
so that each stands behind what its type names; no local notation; 5 SHORT SPELLINGS (abbrev qS · gS
· aS · oS · tS: the parameters · the IOP as written in Lean · the constant's A and O · the maker's
cut) stand for terms that recur. THE PROOF: the lines in front, then ONE CALL of
ledger_whole_fills_field by named arguments.
LETTERS LAID (80): N · decT₂ · Oc · Pm₀ · Mg₀ · MgZ · PmZ · rU · rO · rSp · nU · mem · rd · num ·
memK2 · new2 · memK5 · new5 · rad · work · fl · Y · stOf₁ · tabP₁ · gOf · err₂ · ps · t₁A · Xi · G ·
LA · mCA · mSA · mWA · εtA · eA · LB · mCB · mSB · mWB · εtB · eB · v₀B · r9 · r10 · sentU · layU ·
layO · Ns · xW · rank · M · P · b1 · b2 · b3 · b4 · b5 · b6 · b7 · b8 · R · f · Wr · lo · ch · Q ·
tests · πA · πB · rA · rB · rad2 · rad5 · Pw · arr · Cells · c₀ · matC · held.
PREMISES STRUCK (141): eN · eD · eO · eP · eM₀ · eMZ · ePZ · hn0 · hmU · hmO · hmSp · hrd · hTU ·
hTO · hTS · hms · hoU · hnum · hn1 · hn2 · entry2 · all2 · hno2 · hnew2 · entry5 · all5 · hno5 ·
hnew5 · hNA · hNB · hapSA · hapOA · hapOB · hix · hroom · hS · hUw · hC2 · hC5 · hIx · hKR · hN64 ·
hOB · hsL · hm · hok · hl · hfit9 · hfit10 · hY01 · hY12 · hY10A · hY11B · hst · htab · hg · h2 · hp
· hG · hloG · hdG · hlU · hlO · hbA · heA · ha1A · hpA · h0A · hdsA · hAA · hjA · hb1A · hleA · hoA
· hPA · n2A · n3A · hftA · hbB · heB · ha1B · hpB · h0B · hdsB · hAB · hjB · hPayB · h1B · hlogB ·
hleB · hoB · hPB · n2B · n3B · hftB · herrA · herrB · hw · hi · hbl · fU9 · fO10 · hN · hxW · hsW ·
hsh · nWU · nWS · nIU · nIS · hbook · hloD · ev9 · ev10 · hpin · hwrow · hevalLaid · hwSits · hpile
· hpo · hread · hpf · tU · tO · tS · hb2 · htree2 · htree5 · hFU · hFO · hB9 · hB10 · hloB · hlin ·
hH · hYc9 · hYc10 · hYH · b9 · b10 · hlo.
LETTERS AND PREMISES THAT FALL TOGETHER, BOUND BY THE LINES IN FRONT OF THE CALL (34): base · d ·
ext · err · base2 · d21 · d22 · ex2 · er2 · x3 · base4 · d4 · ex4 · er4 · base5 · d51 · d52 · ex5 ·
er5 · x6 · base7 · d7 · ex7 · er7 · x8 · x9 · x10 · x11 · hlf · hdW · t2 · t4 · t5 · t7.
LETTERS AND PREMISES THAT COME IN (29): x · hx · tA · tB · hI · hV · hGp · NF · TF · Rend · hO · hF
· hJ · hRd · oL · Zs · rP · hZs · hlaid · hTold · Np · nO · pp · E · hpub · hNp · hNO · hpinS ·
hpinF.
PREMISES THAT NAME A BOUND LETTER AND ARE NOT PAID: RESTATED UNDER «∀ ‹the bound letters›, ‹hlf: the
cut's shared row is these pieces› → …» (4): NF · TF · hSh2 · hSh5: hlf fixes the letters, so each
says of the cut's own pieces what it said of the letters.
What is not claimed. EVERY BINDER THAT STANDS IS A PREMISE OR A LETTER STILL. That the premises can
be met together: NO MEMBER IS SHOWN. No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.LedgerByMakeTop
import Johnson.Desc.K14.Law.LedgerMembersOwed
import Johnson.Desc.K14.Law.LedgerReader
import Johnson.Desc.Sound.SharedMembers
import Johnson.Desc.K14.Law.LedgerMembersAt
import Johnson.Desc.K14.Law.LedgerMembers
import Johnson.Desc.Sound.SeamWords
import Johnson.Desc.K14.Law.LedgerTie
import Johnson.Desc.Sound.SeamNumbersSh
import Johnson.Goal.Numbers.K12FitTop
import Johnson.Desc.K14.Law.LedgerSmpPaid
import Johnson.Desc.Sound.LettersFirst
import Johnson.Desc.Sound.AtOcEnd
import Johnson.Desc.K13.Law.OpenAtEnd
import Johnson.Desc.K14.Law.LedgerSeatChain
import Johnson.Desc.Sound.SeamDesc
import Johnson.Goal.Numbers.K14PlanTen
import Johnson.Desc.K12.Coin.NineTenFacts
import Johnson.Desc.K14.Law.LedgerOwnFam
import Johnson.Desc.K14.Law.SharedConst
import Johnson.Desc.K14.Law.SharedConstTests
import Johnson.Desc.K14.Law.SharedConstFold
import Johnson.Desc.K14.Law.SharedConstEv
import Johnson.Desc.K14.Law.SharedConstWalk
import Johnson.Goal.Numbers.K14Radii
import Johnson.Desc.K14.Law.SharedConstJoint
import Johnson.Desc.K14.Law.LedgerRowTiesAtField
import Johnson.Desc.K14.Law.LedgerNumbers
import Johnson.Desc.K14.Law.LedgerMembersTrees
import Johnson.Second.Seam.SeatOfTold
import Johnson.Desc.K14.Law.LedgerToldFitOwed
import Johnson.Desc.K14.Law.LedgerSentBefore
import Johnson.Desc.K14.Law.SharedConstAt
import Johnson.Desc.ProofFile.Lot.K13
import Johnson.P5T.PlanSeats
import Johnson.Desc.Sound.PlanAsk
import Johnson.Goal.Numbers.WrittenInScope
import Johnson.Desc.K14.Law.SharedConstFull
import Johnson.Desc.K14.Law.SharedConstScope
import Johnson.Desc.K14.Law.SharedConstChain
import Johnson.Goal.Numbers.K14RadiiTerms
import Johnson.Desc.K14.Law.SharedConstTopAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open VerifiableInference.Desc.Sound (LettersReadBelow ocEndReadsBelow pinJT)
open VerifiableInference.Desc.K13.Law (WRow evalLaidB wSitsB wSeatB wSitsItem)
open OnBytes.Means (wordsOn)
open VerifiableInference.Desc (Strs)
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words wordsOn)
open Johnson.Pack
open _root_.Run.PQ (CK)
open Cb Cb.Ood Blocks Cb.Pv Cb.Pv.Lin Cb.Bridge
open VerifiableInference.Desc (Block Strs Wit FileDescription First.S Grows)
open VerifiableInference.Desc.ChainEnd (untestedL Exact)
open VerifiableInference.Desc.K1 (sendPiece sampledAt shapeAt shapesOf condPort errPort seedEntry
  seedMaps)
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Pub pubSets openSets start)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts Seat.onGu Seat.onGomega)
open VerifiableInference.Desc.K12.Coin
open Desc.K14.Law.Fence
open H2K.Pin (NTuple)
open H2K.Pub (johOk batV0 PayPub)
open H2K.First (batOneOk)
open VerifiableInference.Desc.K13.Law (EvalAt laidOf wSitsItem wSitsMore)

/-- A name for a term that stands many times below: nothing but a shorter spelling. -/
abbrev qS
    (Zp : ProofFile.Pub)
    (Np : H2U.Places4) :=
  Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)

/-- A name for a term that stands many times below: nothing but a shorter spelling. -/
abbrev gS
    (σ₁ : Type)
    (oH : ProofFile.SecondHashFunctionArgument)
    (mkL : ProofFile.LinksBy)
    (Zp : ProofFile.Pub)
    (lt : String)
    (st₂ : ProofFile.InstPub → St)
    (en₂ : St → Option OnBytes.Proof.SharedEnd)
    (ok₂ : ProofFile.InstPub → Bool)
    (fo₂ : Bool)
    (si₂ : List String)
    (Bs : ProofFile.SecondSeat)
    (getS : σ₁ → VerifiableInference.Desc.First.S)
    (startS : ProofFile.InstPub → σ₁)
    (cF : VerifiableInference.Desc.Chain σ₁ ProofFile.Cl)
    (Np : H2U.Places4) :=
  fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Zp.p.chains (qS Zp Np)
    (VerifiableInference.Desc.K12.Seat.tests Np)

/-- A name for a term that stands many times below: nothing but a shorter spelling. -/
abbrev aS
    (σ₁ : Type)
    (oH : ProofFile.SecondHashFunctionArgument)
    (mkL : ProofFile.LinksBy)
    (Zp : ProofFile.Pub)
    (lt : String)
    (st₂ : ProofFile.InstPub → St)
    (en₂ : St → Option OnBytes.Proof.SharedEnd)
    (ok₂ : ProofFile.InstPub → Bool)
    (fo₂ : Bool)
    (si₂ : List String)
    (Bs : ProofFile.SecondSeat)
    (getS : σ₁ → VerifiableInference.Desc.First.S)
    (startS : ProofFile.InstPub → σ₁)
    (cF : VerifiableInference.Desc.Chain σ₁ ProofFile.Cl)
    (Np : H2U.Places4) :=
  Desc.K14.Law.ShPlan.mk (qS Zp Np) (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
    (VerifiableInference.Desc.Third.p₁₄Z Zp.p.chains.made.sized.proof.set
      Zp.p.chains.made.sized.proof.codes Zp.p.chains.made.sized.proof.batch)
    (Desc.K14.Law.rad2At 2 (qS Zp Np)) (Desc.K14.Law.rad5At 2 (qS Zp Np))
    Johnson.G.dryProofFull.2.1 2

/-- A name for a term that stands many times below: nothing but a shorter spelling. -/
abbrev oS
    (P₀ : Type)
    (Tok : Type)
    (σ₁ : Type)
    (Dw : WholeD)
    (get : (ProofFile.InstPub × σ₁) → P₀ × First.S)
    (ms₁ : List Mem)
    (N₁ : Numbers)
    (links : List ModelPart)
    (Zp : ProofFile.Pub)
    (x : LinSized)
    (hx : VerifiableInference.Desc.K1.realSized = some (x, Johnson.G.codesFull2))
    (Rend : (ProofFile.InstPub × σ₁) → Prop)
    (oL : ProofFile.SecondHashFunctionArgument)
    (Zs : VerifierAndGoals.PublicFiles)
    (rP : LPFD.Full.RunPF)
    (hZs : VerifierAndGoals.InScope Zs = true)
    (hlaid : LPFD.Full.proofDataAndDecisionOfPublicFiles oL Zs.pol Zs.lay Zs.KL = .ok (Dw, rP))
    (Np : H2U.Places4)
    (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option
        ((sigOf (qS Zp Np).codes s.l).om i).Smp)
    (pp : Inst.Model.ScalesAndPolicy)
    (E : Coding (claimsReqAt (frS.toDecR frZ 402653181) numsFull pp))
    (Mg₁ : Meaning P₀
        (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT))
    (hpub : ProofFile.pureRoad.pub oL Zs.pol Zs.lay Zs.KL = .ok Zp)
    (hpinS : VerifiableInference.PlanWritten.sizedPinnedAt Zp.p.X.P Zp.p.chains.made = true)
    (hpinF : VerifiableInference.PlanWritten.firstPinnedAt Zp.p.X.P Zp.first = true) :=
  Desc.K14.Law.ShOpen.mk (P₀ := P₀) (P₁ := ProofFile.InstPub × σ₁)
    (Cells := ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I))
    (Tok := Tok) (Q := (qS Zp Np)) (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)) (fun _ _ => 0) get smp₁
    ms₁ N₁ links Mg₁ (VerifiableInference.Desc.K13.whereOf Zp) Rend
    (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
    (Desc.K14.Law.heldFull (qS Zp Np).par 0 (qS Zp Np).par.S.fold.index.saltBytes
      (Desc.K14.Law.full_index (qS Zp Np).par.S
        (Desc.K14.Law.full_of_shape hx
          (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx).shape))
      OnBytes.Flat.numsFull pp E)

/-- A name for a term that stands many times below: nothing but a shorter spelling. -/
abbrev tS
    (Tok : Type)
    (σ₁ : Type)
    (Dw : WholeD)
    (oH : ProofFile.SecondHashFunctionArgument)
    (mkL : ProofFile.LinksBy)
    (Zp : ProofFile.Pub)
    (lt : String)
    (st₂ : ProofFile.InstPub → St)
    (en₂ : St → Option OnBytes.Proof.SharedEnd)
    (ok₂ : ProofFile.InstPub → Bool)
    (fo₂ : Bool)
    (si₂ : List String)
    (Bs : ProofFile.SecondSeat)
    (getS : σ₁ → VerifiableInference.Desc.First.S)
    (startS : ProofFile.InstPub → σ₁)
    (cF : VerifiableInference.Desc.Chain σ₁ ProofFile.Cl)
    (Np : H2U.Places4)
    (c₁ : Block (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).S₁
        (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).Cl)
    (k₁ : List
        (Block (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).S₁
          (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).Cl))
    (c₂ : Block (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).S₂
        (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).Cl)
    (k₂ : List
        (Block (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).S₂
          (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).Cl))
    (c₃ : Block (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).S₃
        (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).Cl)
    (k₃ : List
        (Block (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).S₃
          (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).Cl))
    (pp : Inst.Model.ScalesAndPolicy)
    (E : Coding (claimsReqAt (frS.toDecR frZ 402653181) numsFull pp))
    (e₁ : (i : ℕ) → (ds : List RDT) →
        ((gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).XiPub ×
          (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).S₁)
        × (frameAt Dw (allOf Dw) Dw.key₁ 0).E.Str → Iop.Tr (uLT (ckP .two) ds) →
        (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT) →
        (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT))
    (e₂ : (i : ℕ) → (ds : List RDT) →
        (((gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).XiPub ×
            (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).S₁)
          × (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).S₂)
        × (frameAt Dw (allOf Dw) Dw.key₂ 0).E.Str → Iop.Tr (uLT (ckP .two) ds) →
        (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT) →
        (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT))
    (e₃ : (i : ℕ) → (ds : List RDT) →
        (((gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).XiPub ×
            (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).S₁ ×
            (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).S₂)
          × (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).S₃)
        ×
        (frameAt Dw (allOf Dw) Dw.key₃
          (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).lastChainFirstTreeNumber).E.Str
        → Iop.Tr (uLT (ckP .two) ds) →
        (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT) →
        (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT))
    (dW : (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT))
    (wEnd : (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT)) :=
  atDesc (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
    (piecesAt (ckP .two) (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) Dw c₁ k₁
      c₂ k₂ c₃ k₃ (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)

/-- **The ledger's top with the payers that are home laid in.** -/
theorem ledger_field_laid
    {P₀ : Type}
    {Tok : Type}
    {σ₁ : Type}
    (Dw : WholeD)
    (get : (ProofFile.InstPub × σ₁) → P₀ × First.S)
    (ms₁ : List Mem)
    (N₁ : Numbers)
    (links : List ModelPart)
    (slots : ℕ)
    (hn : slots ≤ 64)
    (t₂A : ℕ)
    (rdNA : ℕ → ℕ)
    (dBA : RDT)
    (dtA : List RDT)
    (t₂B : ℕ)
    (rdNB : ℕ → ℕ)
    (dBB : RDT)
    (dtB : List RDT)
    (oH : ProofFile.SecondHashFunctionArgument)
    (mkL : ProofFile.LinksBy)
    (Zp : ProofFile.Pub)
    (lt : String)
    (st₂ : ProofFile.InstPub → St)
    (en₂ : St → Option OnBytes.Proof.SharedEnd)
    (ok₂ : ProofFile.InstPub → Bool)
    (fo₂ : Bool)
    (si₂ : List String)
    (Bs : ProofFile.SecondSeat)
    (getS : σ₁ → VerifiableInference.Desc.First.S)
    (startS : ProofFile.InstPub → σ₁)
    (cF : VerifiableInference.Desc.Chain σ₁ ProofFile.Cl)
    (fileN : String)
    (x : LinSized)
    (hx : VerifiableInference.Desc.K1.realSized = some (x, Johnson.G.codesFull2))
    (Rend : (ProofFile.InstPub × σ₁) → Prop)
    (oL : ProofFile.SecondHashFunctionArgument)
    (Zs : VerifierAndGoals.PublicFiles)
    (rP : LPFD.Full.RunPF)
    (hZs : VerifierAndGoals.InScope Zs = true)
    (hlaid : LPFD.Full.proofDataAndDecisionOfPublicFiles oL Zs.pol Zs.lay Zs.KL = .ok (Dw, rP))
    (hTold : ToldFitOwed)
    (Np : H2U.Places4)
    (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option
        ((sigOf (qS Zp Np).codes s.l).om i).Smp)
    (fSp9 : ∀ a₀ rest, (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ Np.U).nums.stages = a₀ :: rest → 0 <
        (qS Zp Np).S.sharedSplit.maskRows ∧ (qS Zp Np).codes.base.size ≤
        (qS Zp Np).S.sharedSplit.code ∧
        ((Desc.K14.Law.Sh.layO
            (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)).shapes.getD
          ((Desc.K14.Law.Sh.layO
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)).tree.getD
            1 0)
          default).logN
        ≤ a₀.Z.a)
    (c₁ : Block (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).S₁
        (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).Cl)
    (k₁ : List
        (Block (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).S₁
          (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).Cl))
    (c₂ : Block (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).S₂
        (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).Cl)
    (k₂ : List
        (Block (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).S₂
          (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).Cl))
    (c₃ : Block (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).S₃
        (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).Cl)
    (k₃ : List
        (Block (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).S₃
          (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).Cl))
    (h₁f : (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).first.blocksInOrder = c₁ :: k₁)
    (h₂f : (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).shared.blocksInOrder = c₂ :: k₂)
    (h₃f : (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).second.blocksInOrder = c₃ :: k₃)
    (hDw : (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).data fileN = .ok Dw)
    (hsl : (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).sealLast = true)
    (tA : FirstTie H2K.Member.setAt H2K.Member.szUFull (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ Np.U)
        H2K.Member.rUFull)
    (hI : N₁.index.1 <
        ((Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))))
    (hV : N₁.w.1 <
        ((Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))))
    (hGp : (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).planOk = true)
    (nO : H2U.PlaceNums)
    (fSp10 : ∀ a₀ rest, (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO).nums.stages = a₀ :: rest → 0 <
        (qS Zp Np).S.sharedSplit.maskRows ∧ (qS Zp Np).codes.base.size ≤
        (qS Zp Np).S.sharedSplit.code ∧
        ((Desc.K14.Law.Sh.layO
            (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)).shapes.getD
          ((Desc.K14.Law.Sh.layO
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)).tree.getD
            1 0)
          default).logN
        ≤ a₀.Z.a)
    (tB : FirstTie H2K.Member.setAt H2K.Member.szOFull (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO)
        H2K.Member.rOFull)
    (pp : Inst.Model.ScalesAndPolicy)
    (E : Coding (claimsReqAt (frS.toDecR frZ 402653181) numsFull pp))
    (Mg₁ : Meaning P₀
        (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT))
    (h3 : wSitsItem ∈
        (pubSets
          Mg₁.more
          links
          (VerifiableInference.Desc.First.flatPlaces
            true links
            true))[(VerifiableInference.Desc.First.flatPlaces true links true).length]?.getD
        [])
    (e₁ : (i : ℕ) → (ds : List RDT) →
        ((gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).XiPub ×
          (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).S₁)
        × (frameAt Dw (allOf Dw) Dw.key₁ 0).E.Str → Iop.Tr (uLT (ckP .two) ds) →
        (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT) →
        (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT))
    (e₂ : (i : ℕ) → (ds : List RDT) →
        (((gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).XiPub ×
            (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).S₁)
          × (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).S₂)
        × (frameAt Dw (allOf Dw) Dw.key₂ 0).E.Str → Iop.Tr (uLT (ckP .two) ds) →
        (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT) →
        (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT))
    (e₃ : (i : ℕ) → (ds : List RDT) →
        (((gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).XiPub ×
            (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).S₁ ×
            (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).S₂)
          × (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).S₃)
        ×
        (frameAt Dw (allOf Dw) Dw.key₃
          (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np).lastChainFirstTreeNumber).E.Str
        → Iop.Tr (uLT (ckP .two) ds) →
        (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT) →
        (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT))
    (dW : (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT))
    (wEnd : (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT))
    (NF : ∀ (base : Nat) (d : RDT)
        (ext : ((ProofFile.InstPub × σ₁) × St) × (frameAt Dw (allOf Dw) Dw.key₂ 0).E.Str → Tr
          (uLT (ckP .two) [d]) → Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT → Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT)
        (err : Err (uLT (ckP .two) [d])) (base2 : ℕ) (d21 : RDT) (d22 : RDT)
        (ex2 : ((ProofFile.InstPub × σ₁) × St) × (frameAt Dw (allOf Dw) Dw.key₂ 0).E.Str → Iop.Tr
          (uLT (ckP .two) [d21, d22]) → Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT → Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT)
        (er2 : Err (uLT (ckP .two) [d21, d22]))
        (x3 : Piece (ckP .two) (frameAt Dw (allOf Dw) Dw.key₂ 0) ((ProofFile.InstPub × σ₁) × St) ProofFile.Cl
          (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT))
        (base4 : ℕ) (d4 : RDT)
        (ex4 : ((ProofFile.InstPub × σ₁) × St) × (frameAt Dw (allOf Dw) Dw.key₂ 0).E.Str → Iop.Tr
          (uLT (ckP .two) [d4]) → Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT → Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT)
        (er4 : Err (uLT (ckP .two) [d4])) (base5 : ℕ) (d51 : RDT) (d52 : RDT)
        (ex5 : ((ProofFile.InstPub × σ₁) × St) × (frameAt Dw (allOf Dw) Dw.key₂ 0).E.Str → Iop.Tr
          (uLT (ckP .two) [d51, d52]) → Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT → Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT)
        (er5 : Err (uLT (ckP .two) [d51, d52]))
        (x6 : Piece (ckP .two) (frameAt Dw (allOf Dw) Dw.key₂ 0) ((ProofFile.InstPub × σ₁) × St) ProofFile.Cl
          (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT))
        (base7 : ℕ) (d7 : RDT)
        (ex7 : ((ProofFile.InstPub × σ₁) × St) × (frameAt Dw (allOf Dw) Dw.key₂ 0).E.Str → Iop.Tr
          (uLT (ckP .two) [d7]) → Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT → Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT)
        (er7 : Err (uLT (ckP .two) [d7]))
        (x8 : Piece (ckP .two) (frameAt Dw (allOf Dw) Dw.key₂ 0) ((ProofFile.InstPub × σ₁) × St) ProofFile.Cl
          (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT))
        (x9 : Piece (ckP .two) (frameAt Dw (allOf Dw) Dw.key₂ 0) ((ProofFile.InstPub × σ₁) × St) ProofFile.Cl
          (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT))
        (x10 : Piece (ckP .two) (frameAt Dw (allOf Dw) Dw.key₂ 0) ((ProofFile.InstPub × σ₁) × St)
          ProofFile.Cl
          (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT))
        (x11 : Piece (ckP .two) (frameAt Dw (allOf Dw) Dw.key₂ 0) ((ProofFile.InstPub × σ₁) × St)
          ProofFile.Cl
          (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT)),
        ((tS Tok σ₁ Dw oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np c₁ k₁ c₂ k₂ c₃
            k₃ pp E e₁ e₂ e₃ dW wEnd).l₂
          =
          ((seatedPiece
              (W := Wit
                ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok
                MsgT)
              (Cl' := ProofFile.Cl) (F := (frameAt Dw (allOf Dw) Dw.key₂ 0))
              (P₁ := (ProofFile.InstPub × σ₁))
              (Desc.K14.Law.Sh.bk
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 0)
              base d ext err))
          ::
          [pc2
            ((Desc.K14.Law.Sh.bk
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 1).retype
              (Cl' := ProofFile.Cl))
            base2 d21 d22 ex2 er2, x3, pc1
            ((Desc.K14.Law.Sh.bk
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 3).retype
              (Cl' := ProofFile.Cl))
            base4 d4 ex4 er4, pc2
            ((Desc.K14.Law.Sh.bk
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 4).retype
              (Cl' := ProofFile.Cl))
            base5 d51 d52 ex5 er5, x6, pc1
            ((Desc.K14.Law.Sh.bk
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 6).retype
              (Cl' := ProofFile.Cl))
            base7 d7 ex7 er7, x8, x9, x10, x11])
        → H2K.JointK.NineFacts (frameAt Dw (allOf Dw) Dw.key₂ 0)
        (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ Np.U) H2K.Member.rUFull
        (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)) t₂A
        (Seat.onGu (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ Np.U) : Block T12 Unit)) x9 dBA dtA)
    (TF : ∀ (base : Nat) (d : RDT)
        (ext : ((ProofFile.InstPub × σ₁) × St) × (frameAt Dw (allOf Dw) Dw.key₂ 0).E.Str → Tr
          (uLT (ckP .two) [d]) → Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT → Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT)
        (err : Err (uLT (ckP .two) [d])) (base2 : ℕ) (d21 : RDT) (d22 : RDT)
        (ex2 : ((ProofFile.InstPub × σ₁) × St) × (frameAt Dw (allOf Dw) Dw.key₂ 0).E.Str → Iop.Tr
          (uLT (ckP .two) [d21, d22]) → Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT → Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT)
        (er2 : Err (uLT (ckP .two) [d21, d22]))
        (x3 : Piece (ckP .two) (frameAt Dw (allOf Dw) Dw.key₂ 0) ((ProofFile.InstPub × σ₁) × St) ProofFile.Cl
          (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT))
        (base4 : ℕ) (d4 : RDT)
        (ex4 : ((ProofFile.InstPub × σ₁) × St) × (frameAt Dw (allOf Dw) Dw.key₂ 0).E.Str → Iop.Tr
          (uLT (ckP .two) [d4]) → Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT → Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT)
        (er4 : Err (uLT (ckP .two) [d4])) (base5 : ℕ) (d51 : RDT) (d52 : RDT)
        (ex5 : ((ProofFile.InstPub × σ₁) × St) × (frameAt Dw (allOf Dw) Dw.key₂ 0).E.Str → Iop.Tr
          (uLT (ckP .two) [d51, d52]) → Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT → Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT)
        (er5 : Err (uLT (ckP .two) [d51, d52]))
        (x6 : Piece (ckP .two) (frameAt Dw (allOf Dw) Dw.key₂ 0) ((ProofFile.InstPub × σ₁) × St) ProofFile.Cl
          (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT))
        (base7 : ℕ) (d7 : RDT)
        (ex7 : ((ProofFile.InstPub × σ₁) × St) × (frameAt Dw (allOf Dw) Dw.key₂ 0).E.Str → Iop.Tr
          (uLT (ckP .two) [d7]) → Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT → Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT)
        (er7 : Err (uLT (ckP .two) [d7]))
        (x8 : Piece (ckP .two) (frameAt Dw (allOf Dw) Dw.key₂ 0) ((ProofFile.InstPub × σ₁) × St) ProofFile.Cl
          (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT))
        (x9 : Piece (ckP .two) (frameAt Dw (allOf Dw) Dw.key₂ 0) ((ProofFile.InstPub × σ₁) × St) ProofFile.Cl
          (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT))
        (x10 : Piece (ckP .two) (frameAt Dw (allOf Dw) Dw.key₂ 0) ((ProofFile.InstPub × σ₁) × St)
          ProofFile.Cl
          (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT))
        (x11 : Piece (ckP .two) (frameAt Dw (allOf Dw) Dw.key₂ 0) ((ProofFile.InstPub × σ₁) × St)
          ProofFile.Cl
          (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT)),
        ((tS Tok σ₁ Dw oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np c₁ k₁ c₂ k₂ c₃
            k₃ pp E e₁ e₂ e₃ dW wEnd).l₂
          =
          ((seatedPiece
              (W := Wit
                ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok
                MsgT)
              (Cl' := ProofFile.Cl) (F := (frameAt Dw (allOf Dw) Dw.key₂ 0))
              (P₁ := (ProofFile.InstPub × σ₁))
              (Desc.K14.Law.Sh.bk
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 0)
              base d ext err))
          ::
          [pc2
            ((Desc.K14.Law.Sh.bk
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 1).retype
              (Cl' := ProofFile.Cl))
            base2 d21 d22 ex2 er2, x3, pc1
            ((Desc.K14.Law.Sh.bk
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 3).retype
              (Cl' := ProofFile.Cl))
            base4 d4 ex4 er4, pc2
            ((Desc.K14.Law.Sh.bk
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 4).retype
              (Cl' := ProofFile.Cl))
            base5 d51 d52 ex5 er5, x6, pc1
            ((Desc.K14.Law.Sh.bk
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 6).retype
              (Cl' := ProofFile.Cl))
            base7 d7 ex7 er7, x8, x9, x10, x11])
        → H2K.JointK.TenFacts (frameAt Dw (allOf Dw) Dw.key₂ 0) (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO)
        H2K.Member.rOFull
        (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)) t₂B
        (Seat.onGomega (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) : Block T12 Unit)) x10 dBB
        dtB)
    (hSh2 : ∀ (base : Nat) (d : RDT)
        (ext : ((ProofFile.InstPub × σ₁) × St) × (frameAt Dw (allOf Dw) Dw.key₂ 0).E.Str → Tr
          (uLT (ckP .two) [d]) → Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT → Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT)
        (err : Err (uLT (ckP .two) [d])) (base2 : ℕ) (d21 : RDT) (d22 : RDT)
        (ex2 : ((ProofFile.InstPub × σ₁) × St) × (frameAt Dw (allOf Dw) Dw.key₂ 0).E.Str → Iop.Tr
          (uLT (ckP .two) [d21, d22]) → Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT → Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT)
        (er2 : Err (uLT (ckP .two) [d21, d22]))
        (x3 : Piece (ckP .two) (frameAt Dw (allOf Dw) Dw.key₂ 0) ((ProofFile.InstPub × σ₁) × St) ProofFile.Cl
          (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT))
        (base4 : ℕ) (d4 : RDT)
        (ex4 : ((ProofFile.InstPub × σ₁) × St) × (frameAt Dw (allOf Dw) Dw.key₂ 0).E.Str → Iop.Tr
          (uLT (ckP .two) [d4]) → Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT → Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT)
        (er4 : Err (uLT (ckP .two) [d4])) (base5 : ℕ) (d51 : RDT) (d52 : RDT)
        (ex5 : ((ProofFile.InstPub × σ₁) × St) × (frameAt Dw (allOf Dw) Dw.key₂ 0).E.Str → Iop.Tr
          (uLT (ckP .two) [d51, d52]) → Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT → Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT)
        (er5 : Err (uLT (ckP .two) [d51, d52]))
        (x6 : Piece (ckP .two) (frameAt Dw (allOf Dw) Dw.key₂ 0) ((ProofFile.InstPub × σ₁) × St) ProofFile.Cl
          (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT))
        (base7 : ℕ) (d7 : RDT)
        (ex7 : ((ProofFile.InstPub × σ₁) × St) × (frameAt Dw (allOf Dw) Dw.key₂ 0).E.Str → Iop.Tr
          (uLT (ckP .two) [d7]) → Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT → Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT)
        (er7 : Err (uLT (ckP .two) [d7]))
        (x8 : Piece (ckP .two) (frameAt Dw (allOf Dw) Dw.key₂ 0) ((ProofFile.InstPub × σ₁) × St) ProofFile.Cl
          (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT))
        (x9 : Piece (ckP .two) (frameAt Dw (allOf Dw) Dw.key₂ 0) ((ProofFile.InstPub × σ₁) × St) ProofFile.Cl
          (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT))
        (x10 : Piece (ckP .two) (frameAt Dw (allOf Dw) Dw.key₂ 0) ((ProofFile.InstPub × σ₁) × St)
          ProofFile.Cl
          (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT))
        (x11 : Piece (ckP .two) (frameAt Dw (allOf Dw) Dw.key₂ 0) ((ProofFile.InstPub × σ₁) × St)
          ProofFile.Cl
          (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT)),
        ((tS Tok σ₁ Dw oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np c₁ k₁ c₂ k₂ c₃
            k₃ pp E e₁ e₂ e₃ dW wEnd).l₂
          =
          ((seatedPiece
              (W := Wit
                ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok
                MsgT)
              (Cl' := ProofFile.Cl) (F := (frameAt Dw (allOf Dw) Dw.key₂ 0))
              (P₁ := (ProofFile.InstPub × σ₁))
              (Desc.K14.Law.Sh.bk
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 0)
              base d ext err))
          ::
          [pc2
            ((Desc.K14.Law.Sh.bk
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 1).retype
              (Cl' := ProofFile.Cl))
            base2 d21 d22 ex2 er2, x3, pc1
            ((Desc.K14.Law.Sh.bk
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 3).retype
              (Cl' := ProofFile.Cl))
            base4 d4 ex4 er4, pc2
            ((Desc.K14.Law.Sh.bk
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 4).retype
              (Cl' := ProofFile.Cl))
            base5 d51 d52 ex5 er5, x6, pc1
            ((Desc.K14.Law.Sh.bk
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 6).retype
              (Cl' := ProofFile.Cl))
            base7 d7 ex7 er7, x8, x9, x10, x11])
        → ∀ x ∈
        (new2 (qS Zp Np)
          (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
          (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
          (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
          (Desc.K14.Law.rad2At 2 (qS Zp Np)) (Desc.K14.Law.rad5At 2 (qS Zp Np))),
        (sendPiece
          (W := Wit
            ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok
            MsgT)
          (F := (frameAt Dw (allOf Dw) Dw.key₂ 0))
          (heldW (U := (ProofFile.InstPub × σ₁))
            ((Desc.K14.Law.Sh.bk
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                1).retype
              (Cl' := ProofFile.Cl)))
          base2 d21 d22
          (parU (qS Zp Np)
            (Desc.K14.Law.Sh.sentU
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
                Np))).coordinates
          (errPort
            (parU (qS Zp Np)
              (Desc.K14.Law.Sh.sentU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)))
            (Desc.K14.Law.rad2At 2 (qS Zp Np)))).ShownAll
        (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) (qS Zp Np).codes x.1.l
        x.1.seat)
    (hSh5 : ∀ (base : Nat) (d : RDT)
        (ext : ((ProofFile.InstPub × σ₁) × St) × (frameAt Dw (allOf Dw) Dw.key₂ 0).E.Str → Tr
          (uLT (ckP .two) [d]) → Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT → Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT)
        (err : Err (uLT (ckP .two) [d])) (base2 : ℕ) (d21 : RDT) (d22 : RDT)
        (ex2 : ((ProofFile.InstPub × σ₁) × St) × (frameAt Dw (allOf Dw) Dw.key₂ 0).E.Str → Iop.Tr
          (uLT (ckP .two) [d21, d22]) → Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT → Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT)
        (er2 : Err (uLT (ckP .two) [d21, d22]))
        (x3 : Piece (ckP .two) (frameAt Dw (allOf Dw) Dw.key₂ 0) ((ProofFile.InstPub × σ₁) × St) ProofFile.Cl
          (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT))
        (base4 : ℕ) (d4 : RDT)
        (ex4 : ((ProofFile.InstPub × σ₁) × St) × (frameAt Dw (allOf Dw) Dw.key₂ 0).E.Str → Iop.Tr
          (uLT (ckP .two) [d4]) → Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT → Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT)
        (er4 : Err (uLT (ckP .two) [d4])) (base5 : ℕ) (d51 : RDT) (d52 : RDT)
        (ex5 : ((ProofFile.InstPub × σ₁) × St) × (frameAt Dw (allOf Dw) Dw.key₂ 0).E.Str → Iop.Tr
          (uLT (ckP .two) [d51, d52]) → Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT → Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT)
        (er5 : Err (uLT (ckP .two) [d51, d52]))
        (x6 : Piece (ckP .two) (frameAt Dw (allOf Dw) Dw.key₂ 0) ((ProofFile.InstPub × σ₁) × St) ProofFile.Cl
          (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT))
        (base7 : ℕ) (d7 : RDT)
        (ex7 : ((ProofFile.InstPub × σ₁) × St) × (frameAt Dw (allOf Dw) Dw.key₂ 0).E.Str → Iop.Tr
          (uLT (ckP .two) [d7]) → Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT → Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT)
        (er7 : Err (uLT (ckP .two) [d7]))
        (x8 : Piece (ckP .two) (frameAt Dw (allOf Dw) Dw.key₂ 0) ((ProofFile.InstPub × σ₁) × St) ProofFile.Cl
          (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT))
        (x9 : Piece (ckP .two) (frameAt Dw (allOf Dw) Dw.key₂ 0) ((ProofFile.InstPub × σ₁) × St) ProofFile.Cl
          (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT))
        (x10 : Piece (ckP .two) (frameAt Dw (allOf Dw) Dw.key₂ 0) ((ProofFile.InstPub × σ₁) × St)
          ProofFile.Cl
          (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT))
        (x11 : Piece (ckP .two) (frameAt Dw (allOf Dw) Dw.key₂ 0) ((ProofFile.InstPub × σ₁) × St)
          ProofFile.Cl
          (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT)),
        ((tS Tok σ₁ Dw oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np c₁ k₁ c₂ k₂ c₃
            k₃ pp E e₁ e₂ e₃ dW wEnd).l₂
          =
          ((seatedPiece
              (W := Wit
                ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok
                MsgT)
              (Cl' := ProofFile.Cl) (F := (frameAt Dw (allOf Dw) Dw.key₂ 0))
              (P₁ := (ProofFile.InstPub × σ₁))
              (Desc.K14.Law.Sh.bk
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 0)
              base d ext err))
          ::
          [pc2
            ((Desc.K14.Law.Sh.bk
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 1).retype
              (Cl' := ProofFile.Cl))
            base2 d21 d22 ex2 er2, x3, pc1
            ((Desc.K14.Law.Sh.bk
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 3).retype
              (Cl' := ProofFile.Cl))
            base4 d4 ex4 er4, pc2
            ((Desc.K14.Law.Sh.bk
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 4).retype
              (Cl' := ProofFile.Cl))
            base5 d51 d52 ex5 er5, x6, pc1
            ((Desc.K14.Law.Sh.bk
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 6).retype
              (Cl' := ProofFile.Cl))
            base7 d7 ex7 er7, x8, x9, x10, x11])
        → ∀ x ∈
        (new5 (qS Zp Np)
          (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
          (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
          (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
          (Desc.K14.Law.rad2At 2 (qS Zp Np)) (Desc.K14.Law.rad5At 2 (qS Zp Np))),
        (sendPiece
          (W := Wit
            ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok
            MsgT)
          (F := (frameAt Dw (allOf Dw) Dw.key₂ 0))
          (heldW (U := (ProofFile.InstPub × σ₁))
            ((Desc.K14.Law.Sh.bk
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                4).retype
              (Cl' := ProofFile.Cl)))
          base5 d51 d52 (parO (qS Zp Np)).coordinates
          (errPort (parO (qS Zp Np)) (Desc.K14.Law.rad5At 2 (qS Zp Np)))).ShownAll
        (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) (qS Zp Np).codes x.1.l
        x.1.seat)
    (hpub : ProofFile.pureRoad.pub oL Zs.pol Zs.lay Zs.KL = .ok Zp)
    (hNp : H2U.placesOfMade Zp.made = .ok Np)
    (hNO : Np.O = some nO)
    (hpinS : VerifiableInference.PlanWritten.sizedPinnedAt Zp.p.X.P Zp.p.chains.made = true)
    (hpinF : VerifiableInference.PlanWritten.firstPinnedAt Zp.p.X.P Zp.first = true)
    (hO : Desc.K14.Law.Sh.TestsO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        (oS P₀ Tok σ₁ Dw get ms₁ N₁ links Zp x hx Rend oL Zs rP hZs hlaid Np smp₁ pp E Mg₁ hpub
          hpinS hpinF)
        ((Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))))
    (hF : Desc.K14.Law.Sh.FoldFacts (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        (oS P₀ Tok σ₁ Dw get ms₁ N₁ links Zp x hx Rend oL Zs rP hZs hlaid Np smp₁ pp E Mg₁ hpub
          hpinS hpinF))
    (hJ : Desc.K14.Law.Sh.Joint (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        (oS P₀ Tok σ₁ Dw get ms₁ N₁ links Zp x hx Rend oL Zs rP hZs hlaid Np smp₁ pp E Mg₁ hpub
          hpinS hpinF))
    (hRd : Desc.K14.Law.Sh.Reads (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        (oS P₀ Tok σ₁ Dw get ms₁ N₁ links Zp x hx Rend oL Zs rP hZs hlaid Np smp₁ pp E Mg₁ hpub
          hpinS hpinF)
        ((Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)))) :
    EachLawsBN
      (keyAt Prod.snd Dw.t₁
        (tS Tok σ₁ Dw oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np c₁ k₁ c₂ k₂ c₃ k₃
          pp E e₁ e₂ e₃ dW wEnd).p₂
        (tS Tok σ₁ Dw oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np c₁ k₁ c₂ k₂ c₃ k₃
          pp E e₁ e₂ e₃ dW wEnd).l₂)
      (onQ₂
        (tiedNumbers N₁
          (Desc.K14.Law.Fence.numbersSh
            (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (Desc.K14.Law.Sh.layU
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (Desc.K14.Law.Sh.layO
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (0, 0) (0, 0)))
        ((pmK (P14.codes (qS Zp Np))
            (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
            (smpSt (P14.codes (qS Zp Np))
              (oNoSh
                (Desc.K14.Law.Sh.sentU
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)).size)
              stSh)
            (msSh (qS Zp Np).S ((Desc.K14.Law.rad2At 2 (qS Zp Np)) 0)
              ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 0) ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 1)
              (Desc.K14.Law.Sh.t₁
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (Desc.K14.Law.Sh.layU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (Desc.K14.Law.Sh.layO
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)))
            (decK (qS Zp Np).par 0 2852142980
              (Desc.K14.Law.Sh.rank
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (Desc.K14.Law.heldFull (qS Zp Np).par 0 (qS Zp Np).par.S.fold.index.saltBytes
                (Desc.K14.Law.full_index (qS Zp Np).par.S
                  (Desc.K14.Law.full_of_shape hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx).shape))
                OnBytes.Flat.numsFull pp E))
            (shiftBook
              (NumbersS.lo
                (tiedNumbers N₁
                  (Desc.K14.Law.Fence.numbersSh
                    (Desc.K14.Law.Sh.t₁
                      (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                    (Desc.K14.Law.Sh.layU
                      (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                    (Desc.K14.Law.Sh.layO
                      (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                    (0, 0) (0, 0)))))
            (pmPoint (qS Zp Np).codes
              (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
              (smpSt (qS Zp Np).codes
                (oNoSh
                  (Desc.K14.Law.Sh.sentU
                    (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)).size)
                stSh)
              (msSh (qS Zp Np).S ((Desc.K14.Law.rad2At 2 (qS Zp Np)) 0)
                ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 0) ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 1)
                (Desc.K14.Law.Sh.t₁
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                (Desc.K14.Law.Sh.layU
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                (Desc.K14.Law.Sh.layO
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)))
              (qS Zp Np).par 0 2852142980
              (Desc.K14.Law.Sh.rank
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (Desc.K14.Law.heldFull (qS Zp Np).par 0 (qS Zp Np).par.S.fold.index.saltBytes
                (Desc.K14.Law.full_index (qS Zp Np).par.S
                  (Desc.K14.Law.full_of_shape hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx).shape))
                OnBytes.Flat.numsFull pp E)
              (fun s : St => s.st)
              (fun s : St => shiftBook
                (tiedNumbers N₁
                  (Desc.K14.Law.Fence.numbersSh
                    (Desc.K14.Law.Sh.t₁
                      (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                    (Desc.K14.Law.Sh.layU
                      (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                    (Desc.K14.Law.Sh.layO
                      (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                    (0, 0) (0, 0))).lo
                s.book)
              (pmZ (qS Zp Np).par Desc.K14.Law.Sh.idleP))
            (FoldeqShape.columns (LinShape.fold (P14.S (qS Zp Np)))) 0
            (Array.size
              (Desc.K14.Law.Sh.sentU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)))
            (qS Zp Np)
            (XK (qS Zp Np)
              (Desc.K14.Law.Sh.sentU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (Desc.K14.Law.Sh.layU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (Desc.K14.Law.Sh.layO
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (shapeAt
                (parU (qS Zp Np)
                  (Desc.K14.Law.Sh.sentU
                    (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)))
                ⟨0,
                  (places (qS Zp Np)
                    (Desc.K14.Law.Sh.sentU
                      (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))).1
                  (Desc.K14.Law.Sh.tests_hUw
                    (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                    (Desc.K14.Law.Sh.tests_at hx
                      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                      (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
                        (Zp.p.chains) (qS Zp Np)
                        (VerifiableInference.Desc.K12.Seat.tests Np))
                      (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂
                        Bs getS startS cF _ _ _ hGp)))⟩,
                shapeAt (parO (qS Zp Np))
                ⟨0,
                  (places (qS Zp Np)
                    (Desc.K14.Law.Sh.sentU
                      (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))).2.1⟩,
                shapeAt (parO (qS Zp Np))
                ⟨1,
                  (places (qS Zp Np)
                    (Desc.K14.Law.Sh.sentU
                      (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))).2.2
                  (Desc.K14.Law.Sh.tests_hS
                    (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                    (Desc.K14.Law.Sh.tests_at hx
                      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                      (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
                        (Zp.p.chains) (qS Zp Np)
                        (VerifiableInference.Desc.K12.Seat.tests Np))
                      (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂
                        Bs getS startS cF _ _ _ hGp)))⟩,
                (smpK (qS Zp Np).codes
                  (shapeAt
                    (parU (qS Zp Np)
                      (Desc.K14.Law.Sh.sentU
                        (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)))
                    ⟨0,
                      (places (qS Zp Np)
                        (Desc.K14.Law.Sh.sentU
                          (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
                            Np))).1
                      (Desc.K14.Law.Sh.tests_hUw
                        (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                        (Desc.K14.Law.Sh.tests_at hx
                          (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx)
                          hNp
                          (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
                            (Zp.p.chains) (qS Zp Np)
                            (VerifiableInference.Desc.K12.Seat.tests Np))
                          (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂
                            si₂ Bs getS startS cF _ _ _ hGp)))⟩)
                  (shapeAt (parO (qS Zp Np))
                    ⟨0,
                      (places (qS Zp Np)
                        (Desc.K14.Law.Sh.sentU
                          (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
                            Np))).2.1⟩)
                  (shapeAt (parO (qS Zp Np))
                    ⟨1,
                      (places (qS Zp Np)
                        (Desc.K14.Law.Sh.sentU
                          (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
                            Np))).2.2
                      (Desc.K14.Law.Sh.tests_hS
                        (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                        (Desc.K14.Law.Sh.tests_at hx
                          (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx)
                          hNp
                          (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
                            (Zp.p.chains) (qS Zp Np)
                            (VerifiableInference.Desc.K12.Seat.tests Np))
                          (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂
                            si₂ Bs getS startS cF _ _ _ hGp)))⟩)
                  (Desc.K14.Law.Sh.sentU
                    (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)).size))
              (Array.size
                (Desc.K14.Law.Sh.sentU
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))))))
        (ocWith
          (ocEnd get N₁ Mg₁ links (VerifiableInference.Desc.First.flatPlaces true links true))
          Rend)
        true
        (tS Tok σ₁ Dw oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np c₁ k₁ c₂ k₂ c₃ k₃
          pp E e₁ e₂ e₃ dW wEnd).p₂
        (tS Tok σ₁ Dw oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np c₁ k₁ c₂ k₂ c₃ k₃
          pp E e₁ e₂ e₃ dW wEnd).l₂)
      (stepAt
        (tiedNumbers N₁
          (Desc.K14.Law.Fence.numbersSh
            (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (Desc.K14.Law.Sh.layU
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (Desc.K14.Law.Sh.layO
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (0, 0) (0, 0)))
        ((mgK (P14.codes (qS Zp Np))
            (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
            (P5T.arrOf (P5T.planSeatsAll Zp Zp.D))
            (smpSt (P14.codes (qS Zp Np))
              (oNoSh
                (Desc.K14.Law.Sh.sentU
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)).size)
              stSh)
            (msSh (qS Zp Np).S ((Desc.K14.Law.rad2At 2 (qS Zp Np)) 0)
              ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 0) ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 1)
              (Desc.K14.Law.Sh.t₁
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (Desc.K14.Law.Sh.layU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (Desc.K14.Law.Sh.layO
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)))
            (decK (qS Zp Np).par 0 2852142980
              (Desc.K14.Law.Sh.rank
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (Desc.K14.Law.heldFull (qS Zp Np).par 0 (qS Zp Np).par.S.fold.index.saltBytes
                (Desc.K14.Law.full_index (qS Zp Np).par.S
                  (Desc.K14.Law.full_of_shape hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx).shape))
                OnBytes.Flat.numsFull pp E))
            (tiedMeaning get Mg₁
              (mgJoint (qS Zp Np).codes
                (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)) get smp₁ ms₁
                (Desc.K14.Law.Sh.xW
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                  (oS P₀ Tok σ₁ Dw get ms₁ N₁ links Zp x hx Rend oL Zs rP hZs hlaid Np smp₁
                    pp E Mg₁ hpub hpinS hpinF))
                (smpSt (qS Zp Np).codes
                  (oNoSh
                    (Desc.K14.Law.Sh.sentU
                      (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)).size)
                  stSh)
                (msSh (qS Zp Np).S ((Desc.K14.Law.rad2At 2 (qS Zp Np)) 0)
                  ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 0)
                  ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 1)
                  (Desc.K14.Law.Sh.t₁
                    (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                  (Desc.K14.Law.Sh.layU
                    (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                  (Desc.K14.Law.Sh.layO
                    (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)))
                (linLayW (qS Zp Np).codes (VerifiableInference.Desc.K13.whereOf Zp).lin)
                (fun q => VerifiableInference.Desc.Sound.stFirst (get q))
                (fun q =>
                  (VerifiableInference.Desc.Sound.tabFirst
                    (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)))
                  (get q))
                (rgOf (qS Zp Np).codes (P5T.arrOf (P5T.planSeatsAll Zp Zp.D))
                  (memK (qS Zp Np).S ((Desc.K14.Law.rad2At 2 (qS Zp Np)) 0)
                    ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 0)
                    ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 1)
                    (Desc.K14.Law.Sh.t₁
                      (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                    (Desc.K14.Law.Sh.layU
                      (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                    (Desc.K14.Law.Sh.layO
                      (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                    (Desc.K14.Law.Sh.sentU
                      (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)).size)
                  (rdK (qS Zp Np).codes))
                (omWK (qS Zp Np).codes (P5T.arrOf (P5T.planSeatsAll Zp Zp.D))
                  (memK (qS Zp Np).S ((Desc.K14.Law.rad2At 2 (qS Zp Np)) 0)
                    ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 0)
                    ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 1)
                    (Desc.K14.Law.Sh.t₁
                      (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                    (Desc.K14.Law.Sh.layU
                      (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                    (Desc.K14.Law.Sh.layO
                      (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                    (Desc.K14.Law.Sh.sentU
                      (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)).size)
                  (rdK (qS Zp Np).codes)
                  (Desc.K14.Law.Sh.sentU
                    (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)).size
                  (qS Zp Np))
                (qS Zp Np).par 2852142980
                (gLaid (VerifiableInference.Desc.K13.whereOf Zp) get) 0 2852142980
                (Desc.K14.Law.Sh.rank
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                (Desc.K14.Law.heldFull (qS Zp Np).par 0
                  (qS Zp Np).par.S.fold.index.saltBytes
                  (Desc.K14.Law.full_index (qS Zp Np).par.S
                    (Desc.K14.Law.full_of_shape hx
                      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx).shape))
                  OnBytes.Flat.numsFull pp E)
                (VerifiableInference.Desc.K13.whereOf Zp)
                (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
                (mgZ (qS Zp Np).codes (P5T.arrOf (P5T.planSeatsAll Zp Zp.D))
                  (memK (qS Zp Np).S ((Desc.K14.Law.rad2At 2 (qS Zp Np)) 0)
                    ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 0)
                    ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 1)
                    (Desc.K14.Law.Sh.t₁
                      (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                    (Desc.K14.Law.Sh.layU
                      (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                    (Desc.K14.Law.Sh.layO
                      (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                    (Desc.K14.Law.Sh.sentU
                      (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)).size)
                  (rdK (qS Zp Np).codes)
                  (numSh
                    (Desc.K14.Law.Sh.sentU
                      (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)).size)
                  Desc.K14.Law.Sh.idleM)))
            (memK (qS Zp Np).S ((Desc.K14.Law.rad2At 2 (qS Zp Np)) 0)
              ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 0) ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 1)
              (Desc.K14.Law.Sh.t₁
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (Desc.K14.Law.Sh.layU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (Desc.K14.Law.Sh.layO
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (Desc.K14.Law.Sh.sentU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)).size)
            (rdK (qS Zp Np).codes) 2852142980
            (FoldeqShape.columns (LinShape.fold (P14.S (qS Zp Np))))
            (Array.size
              (Desc.K14.Law.Sh.sentU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)))
            (qS Zp Np)))
        ((pmK (P14.codes (qS Zp Np))
            (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
            (smpSt (P14.codes (qS Zp Np))
              (oNoSh
                (Desc.K14.Law.Sh.sentU
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)).size)
              stSh)
            (msSh (qS Zp Np).S ((Desc.K14.Law.rad2At 2 (qS Zp Np)) 0)
              ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 0) ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 1)
              (Desc.K14.Law.Sh.t₁
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (Desc.K14.Law.Sh.layU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (Desc.K14.Law.Sh.layO
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)))
            (decK (qS Zp Np).par 0 2852142980
              (Desc.K14.Law.Sh.rank
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (Desc.K14.Law.heldFull (qS Zp Np).par 0 (qS Zp Np).par.S.fold.index.saltBytes
                (Desc.K14.Law.full_index (qS Zp Np).par.S
                  (Desc.K14.Law.full_of_shape hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx).shape))
                OnBytes.Flat.numsFull pp E))
            (shiftBook
              (NumbersS.lo
                (tiedNumbers N₁
                  (Desc.K14.Law.Fence.numbersSh
                    (Desc.K14.Law.Sh.t₁
                      (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                    (Desc.K14.Law.Sh.layU
                      (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                    (Desc.K14.Law.Sh.layO
                      (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                    (0, 0) (0, 0)))))
            (pmPoint (qS Zp Np).codes
              (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
              (smpSt (qS Zp Np).codes
                (oNoSh
                  (Desc.K14.Law.Sh.sentU
                    (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)).size)
                stSh)
              (msSh (qS Zp Np).S ((Desc.K14.Law.rad2At 2 (qS Zp Np)) 0)
                ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 0) ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 1)
                (Desc.K14.Law.Sh.t₁
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                (Desc.K14.Law.Sh.layU
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                (Desc.K14.Law.Sh.layO
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)))
              (qS Zp Np).par 0 2852142980
              (Desc.K14.Law.Sh.rank
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (Desc.K14.Law.heldFull (qS Zp Np).par 0 (qS Zp Np).par.S.fold.index.saltBytes
                (Desc.K14.Law.full_index (qS Zp Np).par.S
                  (Desc.K14.Law.full_of_shape hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx).shape))
                OnBytes.Flat.numsFull pp E)
              (fun s : St => s.st)
              (fun s : St => shiftBook
                (tiedNumbers N₁
                  (Desc.K14.Law.Fence.numbersSh
                    (Desc.K14.Law.Sh.t₁
                      (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                    (Desc.K14.Law.Sh.layU
                      (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                    (Desc.K14.Law.Sh.layO
                      (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                    (0, 0) (0, 0))).lo
                s.book)
              (pmZ (qS Zp Np).par Desc.K14.Law.Sh.idleP))
            (FoldeqShape.columns (LinShape.fold (P14.S (qS Zp Np)))) 0
            (Array.size
              (Desc.K14.Law.Sh.sentU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)))
            (qS Zp Np)
            (XK (qS Zp Np)
              (Desc.K14.Law.Sh.sentU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (Desc.K14.Law.Sh.layU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (Desc.K14.Law.Sh.layO
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (shapeAt
                (parU (qS Zp Np)
                  (Desc.K14.Law.Sh.sentU
                    (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)))
                ⟨0,
                  (places (qS Zp Np)
                    (Desc.K14.Law.Sh.sentU
                      (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))).1
                  (Desc.K14.Law.Sh.tests_hUw
                    (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                    (Desc.K14.Law.Sh.tests_at hx
                      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                      (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
                        (Zp.p.chains) (qS Zp Np)
                        (VerifiableInference.Desc.K12.Seat.tests Np))
                      (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂
                        Bs getS startS cF _ _ _ hGp)))⟩,
                shapeAt (parO (qS Zp Np))
                ⟨0,
                  (places (qS Zp Np)
                    (Desc.K14.Law.Sh.sentU
                      (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))).2.1⟩,
                shapeAt (parO (qS Zp Np))
                ⟨1,
                  (places (qS Zp Np)
                    (Desc.K14.Law.Sh.sentU
                      (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))).2.2
                  (Desc.K14.Law.Sh.tests_hS
                    (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                    (Desc.K14.Law.Sh.tests_at hx
                      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                      (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
                        (Zp.p.chains) (qS Zp Np)
                        (VerifiableInference.Desc.K12.Seat.tests Np))
                      (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂
                        Bs getS startS cF _ _ _ hGp)))⟩,
                (smpK (qS Zp Np).codes
                  (shapeAt
                    (parU (qS Zp Np)
                      (Desc.K14.Law.Sh.sentU
                        (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)))
                    ⟨0,
                      (places (qS Zp Np)
                        (Desc.K14.Law.Sh.sentU
                          (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
                            Np))).1
                      (Desc.K14.Law.Sh.tests_hUw
                        (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                        (Desc.K14.Law.Sh.tests_at hx
                          (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx)
                          hNp
                          (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
                            (Zp.p.chains) (qS Zp Np)
                            (VerifiableInference.Desc.K12.Seat.tests Np))
                          (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂
                            si₂ Bs getS startS cF _ _ _ hGp)))⟩)
                  (shapeAt (parO (qS Zp Np))
                    ⟨0,
                      (places (qS Zp Np)
                        (Desc.K14.Law.Sh.sentU
                          (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
                            Np))).2.1⟩)
                  (shapeAt (parO (qS Zp Np))
                    ⟨1,
                      (places (qS Zp Np)
                        (Desc.K14.Law.Sh.sentU
                          (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
                            Np))).2.2
                      (Desc.K14.Law.Sh.tests_hS
                        (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                        (Desc.K14.Law.Sh.tests_at hx
                          (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx)
                          hNp
                          (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
                            (Zp.p.chains) (qS Zp Np)
                            (VerifiableInference.Desc.K12.Seat.tests Np))
                          (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂
                            si₂ Bs getS startS cF _ _ _ hGp)))⟩)
                  (Desc.K14.Law.Sh.sentU
                    (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)).size))
              (Array.size
                (Desc.K14.Law.Sh.sentU
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))))))
        (ocWith
          (ocEnd get N₁ Mg₁ links (VerifiableInference.Desc.First.flatPlaces true links true))
          Rend)
        true
        (tS Tok σ₁ Dw oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np c₁ k₁ c₂ k₂ c₃ k₃
          pp E e₁ e₂ e₃ dW wEnd).p₂
        (tS Tok σ₁ Dw oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np c₁ k₁ c₂ k₂ c₃ k₃
          pp E e₁ e₂ e₃ dW wEnd).l₂
        (extOf
          (tiedNumbers N₁
            (Desc.K14.Law.Fence.numbersSh
              (Desc.K14.Law.Sh.t₁
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (Desc.K14.Law.Sh.layU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (Desc.K14.Law.Sh.layO
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (0, 0) (0, 0)))
          (tS Tok σ₁ Dw oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np c₁ k₁ c₂ k₂ c₃
            k₃ pp E e₁ e₂ e₃ dW wEnd).p₂
          (tS Tok σ₁ Dw oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np c₁ k₁ c₂ k₂ c₃
            k₃ pp E e₁ e₂ e₃ dW wEnd).l₂
          ((exK (P14.codes (qS Zp Np))
              (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
              (P5T.arrOf (P5T.planSeatsAll Zp Zp.D))
              (smpSt (P14.codes (qS Zp Np))
                (oNoSh
                  (Desc.K14.Law.Sh.sentU
                    (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)).size)
                stSh)
              (msSh (qS Zp Np).S ((Desc.K14.Law.rad2At 2 (qS Zp Np)) 0)
                ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 0) ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 1)
                (Desc.K14.Law.Sh.t₁
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                (Desc.K14.Law.Sh.layU
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                (Desc.K14.Law.Sh.layO
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)))
              (decK (qS Zp Np).par 0 2852142980
                (Desc.K14.Law.Sh.rank
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                (Desc.K14.Law.heldFull (qS Zp Np).par 0
                  (qS Zp Np).par.S.fold.index.saltBytes
                  (Desc.K14.Law.full_index (qS Zp Np).par.S
                    (Desc.K14.Law.full_of_shape hx
                      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx).shape))
                  OnBytes.Flat.numsFull pp E))
              (fun _ _ => 0)
              (tiedNumbers N₁
                (Desc.K14.Law.Fence.numbersSh
                  (Desc.K14.Law.Sh.t₁
                    (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                  (Desc.K14.Law.Sh.layU
                    (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                  (Desc.K14.Law.Sh.layO
                    (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                  (0, 0) (0, 0)))
              (frameAt Dw (allOf Dw) Dw.key₂ 0)))))
      slots 0
      ((tS Tok σ₁ Dw oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np c₁ k₁ c₂ k₂ c₃ k₃
          pp E e₁ e₂ e₃ dW wEnd).p₂
        ::
        (tS Tok σ₁ Dw oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np c₁ k₁ c₂ k₂ c₃ k₃
          pp E e₁ e₂ e₃ dW wEnd).l₂) := by
  obtain ⟨β1, β2, β3, β4, β5, β6, β7, β8, hblβ, base, d, ext, err, base2, d21, d22, ex2, er2, x3,
      base4, d4, ex4, er4, base5, d51, d52, ex5, er5, x6, base7, d7, ex7, er7, x8, x9, x10, x11,
      hlf, htF, hfr, hf0, hr3, hal, hbase, hps, hopAll, hcap, hrowD, h3d, h6d, hdW, t2, t4, t5, t7⟩
      := row_ties_at_field Dw oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Zp.p.chains (qS Zp
      Np) (VerifiableInference.Desc.K12.Seat.tests Np) (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt
      st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)) (Desc.K14.Law.Sh.tests_hUw (aS σ₁ oH mkL Zp lt st₂
      en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) (Desc.K14.Law.Sh.tests_at hx
      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp (fieldF oH mkL Zp lt st₂ en₂
      ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
      (VerifiableInference.Desc.K12.Seat.tests Np)) (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂
      en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _ _ hGp)))
      (by rw [Desc.K14.Law.Sh.tests_two Np nO hNO]; rfl) c₁ k₁ c₂ k₂ c₃ k₃ h₁f h₂f h₃f e₁ e₂ e₃ dW
      wEnd fileN hDw hsl oL Zs rP hZs hlaid
  have hβ := Option.some.inj (hblβ.symm.trans (Desc.K14.Law.Sh.tests_hbl8 (aS σ₁ oH mkL Zp lt st₂
      en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) (Desc.K14.Law.Sh.tests_at hx
      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp (fieldF oH mkL Zp lt st₂ en₂
      ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
      (VerifiableInference.Desc.K12.Seat.tests Np)) (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂
      en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _ _ hGp))))
  simp only [List.cons.injEq, and_true] at hβ
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hβ
  have ht₁ : ((Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)) =
      ((tS Tok σ₁ Dw oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np c₁ k₁ c₂ k₂ c₃ k₃ pp E e₁
      e₂ e₃ dW wEnd).p₂).base) := (Fence.counts_of_planOk (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs
      getS startS cF Np) fileN Dw hGp hDw).1.trans hbase.symm
  have hN' : ((tiedNumbers N₁ (Desc.K14.Law.Fence.numbersSh (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt
      st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)) (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂
      ok₂ fo₂ si₂ Bs getS startS cF Np)) (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂
      si₂ Bs getS startS cF Np)) (0, 0) (0, 0))).tenant = tenantSh ((tS Tok σ₁ Dw oH mkL Zp lt st₂
      en₂ ok₂ fo₂ si₂ Bs getS startS cF Np c₁ k₁ c₂ k₂ c₃ k₃ pp E e₁ e₂ e₃ dW wEnd).p₂).base
      (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
      (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))) := by
    rw [← ht₁]
    exact (show (tiedNumbers N₁ (Desc.K14.Law.Fence.numbersSh (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp
        lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)) (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂
        en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)) (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂
        fo₂ si₂ Bs getS startS cF Np)) (0, 0) (0, 0))).tenant = tenantSh (Desc.K14.Law.Sh.t₁ (aS σ₁
        oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)) (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL
        Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)) (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt
        st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)) from Desc.K14.Law.Sh.paid_hN (aS σ₁ oH mkL Zp lt
        st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) (oS P₀ Tok σ₁ Dw get ms₁ N₁ links Zp x hx Rend oL
        Zs rP hZs hlaid Np smp₁ pp E Mg₁ hpub hpinS hpinF))
  have hNlo : ((tiedNumbers N₁ (Desc.K14.Law.Fence.numbersSh (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt
      st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)) (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂
      ok₂ fo₂ si₂ Bs getS startS cF Np)) (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂
      si₂ Bs getS startS cF Np)) (0, 0) (0, 0))).lo = ((tS Tok σ₁ Dw oH mkL Zp lt st₂ en₂ ok₂ fo₂
      si₂ Bs getS startS cF Np c₁ k₁ c₂ k₂ c₃ k₃ pp E e₁ e₂ e₃ dW wEnd).p₂).base) :=
      ((Desc.K14.Law.Fence.counts_of_planOk (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS
      cF Np) fileN Dw hGp hDw).1).trans hbase.symm
  have hal5 : (∀ p ∈ [(seatedPiece (W := Wit ((VerifiableInference.OnPublicFiles.kcReq
      OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT) (Cl' := ProofFile.Cl) (F := (frameAt Dw (allOf Dw)
            Dw.key₂ 0)) (P₁ := (ProofFile.InstPub × σ₁)) (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂
                  si₂ Bs getS startS cF Np) 0) base d ext err), (pc2 ((Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt
                  st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 1).retype (Cl' := ProofFile.Cl)) base2 d21 d22 ex2 er2),
      x3, (pc1 ((Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
      3).retype (Cl' := ProofFile.Cl)) base4 d4 ex4 er4), (pc2 ((Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt
            st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 4).retype (Cl' := ProofFile.Cl)) base5 d51 d52 ex5 er5)],
      Along (RoundIs (VerifiableInference.Desc.numAt Dw.t₁ Dw.t₂ 1)) p.b.rounds p.ds) := fun p hmem
      => hal p (List.mem_cons_of_mem _ (List.mem_append_left [x6, (pc1 ((Desc.K14.Law.Sh.bk (aS σ₁
      oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 6).retype (Cl' := ProofFile.Cl)) base7 d7 ex7
      er7), x8, x9, x10, x11] hmem))
  have NUM := numbers_of_tiled (qS Zp Np) (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂
      si₂ Bs getS startS cF Np) 0) (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs
      getS startS cF Np) 1) (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
      startS cF Np) 2) (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
      Np) 3) (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 4)
      (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 5)
      (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 6)
      (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 7)
      (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
      (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
      (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
      (Desc.K14.Law.Sh.tests_hbl8 (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
      (Desc.K14.Law.Sh.tests_at hx (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
      (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
      (VerifiableInference.Desc.K12.Seat.tests Np)) (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂
      en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _ _ hGp))) (Desc.K14.Law.Sh.tests_hUw (aS σ₁ oH mkL Zp lt
      st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) (Desc.K14.Law.Sh.tests_at hx
      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp (fieldF oH mkL Zp lt st₂ en₂
      ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
      (VerifiableInference.Desc.K12.Seat.tests Np)) (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂
      en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _ _ hGp))) (Desc.K14.Law.Sh.tests_hlU (aS σ₁ oH mkL Zp lt
      st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) (Desc.K14.Law.Sh.tests_at hx
      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp (fieldF oH mkL Zp lt st₂ en₂
      ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
      (VerifiableInference.Desc.K12.Seat.tests Np)) (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂
      en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _ _ hGp))) (Desc.K14.Law.Sh.tests_hlO (aS σ₁ oH mkL Zp lt
      st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) (Desc.K14.Law.Sh.tests_at hx
      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp (fieldF oH mkL Zp lt st₂ en₂
      ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
      (VerifiableInference.Desc.K12.Seat.tests Np)) (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂
      en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _ _ hGp))) (Desc.K14.Law.Sh.tests_hS (aS σ₁ oH mkL Zp lt
      st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) (Desc.K14.Law.Sh.tests_at hx
      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp (fieldF oH mkL Zp lt st₂ en₂
      ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
      (VerifiableInference.Desc.K12.Seat.tests Np)) (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂
      en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _ _ hGp))) (VerifiableInference.Desc.numAt Dw.t₁ Dw.t₂ 1)
      ((tS Tok σ₁ Dw oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np c₁ k₁ c₂ k₂ c₃ k₃ pp E e₁
      e₂ e₃ dW wEnd).p₂) (seatedPiece (W := Wit ((VerifiableInference.OnPublicFiles.kcReq
      OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT) (Cl' := ProofFile.Cl) (F := (frameAt Dw (allOf Dw)
            Dw.key₂ 0)) (P₁ := (ProofFile.InstPub × σ₁)) (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂
                  si₂ Bs getS startS cF Np) 0) base d ext err) _ x3 _ _ x6 [(pc1 ((Desc.K14.Law.Sh.bk (aS σ₁ oH
                  mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 6).retype (Cl' := ProofFile.Cl)) base7 d7 ex7
                  er7), x8, x9, x10, x11] htF hfr rfl rfl hr3 rfl rfl hal5 (tiedNumbers N₁
                  (Desc.K14.Law.Fence.numbersSh (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs
                  getS startS cF Np)) (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                  startS cF Np)) (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
                  Np)) (0, 0) (0, 0))) hN'
  have a2 : (Along (RoundIs (VerifiableInference.Desc.numAt Dw.t₁ Dw.t₂ 1)) (Desc.K14.Law.Sh.bk (aS
      σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 1).rounds [d21, d22]) := hal _
      (.tail _ (.tail _ (.head _)))
  have a5 : (Along (RoundIs (VerifiableInference.Desc.numAt Dw.t₁ Dw.t₂ 1)) (Desc.K14.Law.Sh.bk (aS
      σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 4).rounds [d51, d52]) := hal _
      (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
  have hBt : (Second.Seam.toldFitB (qS Zp Np).codes (qS Zp Np).S (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL
      Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)) (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂
      en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)) = true) := by
    have h := hTold x hx
    unfold Sh.layU Sh.layO Sh.sentU
    show Second.Seam.toldFitB (qS Zp Np).codes (qS Zp Np).S ((layTrees (qS Zp Np).codes ((withU (qS
        Zp Np).S).getD #[])).getD default) ((layTrees (qS Zp Np).codes (withOmega (qS Zp
        Np).S)).getD default) = true
    rw [(show (qS Zp Np).codes = Johnson.G.codesFull2 from (Desc.K14.Law.written_in_scope hZs hpub
        hpinS hpinF hlaid hx).codes), (show (qS Zp Np).S = x.shape from
        (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx).shape)]
    exact h
  have T1 := htF.2.2.2.2
  have T2 := T1.2.2.2.2
  have T3 := T2.2.2.2.2
  have T4 := T3.2.2.2.2
  have T5 := T4.2.2.2.2
  have l1 : ((seatedPiece (W := Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp
      E).conf.I) Tok MsgT) (Cl' := ProofFile.Cl) (F := (frameAt Dw (allOf Dw) Dw.key₂ 0)) (P₁ :=
            (ProofFile.InstPub × σ₁)) (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS
                  cF Np) 0) base d ext err).ds.length = (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂
                  si₂ Bs getS startS cF Np) 0).rounds.length) := by
    have e := T1.1.1
    rw [T1.2.2.1] at e
    simpa only [List.length_nil, Nat.add_zero] using e
  have l2 : ((pc2 ((Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
      1).retype (Cl' := ProofFile.Cl)) base2 d21 d22 ex2 er2).ds.length = (Desc.K14.Law.Sh.bk (aS σ₁ oH
            mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 1).rounds.length) := by
    have e := T2.1.1
    rw [T2.2.2.1] at e
    simpa only [List.length_nil, Nat.add_zero] using e
  have l3 : (x3.ds.length = (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
      startS cF Np) 2).rounds.length) := by
    have e := T3.1.1
    rw [T3.2.2.1, hr3] at e
    simpa only [List.length_nil, Nat.add_zero] using e
  have l4 : ((pc1 ((Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
      3).retype (Cl' := ProofFile.Cl)) base4 d4 ex4 er4).ds.length = (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp
            lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 3).rounds.length) := by
    have e := T4.1.1
    rw [T4.2.2.1] at e
    simpa only [List.length_nil, Nat.add_zero] using e
  have l5 : ((pc2 ((Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
      4).retype (Cl' := ProofFile.Cl)) base5 d51 d52 ex5 er5).ds.length = (Desc.K14.Law.Sh.bk (aS σ₁ oH
            mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 4).rounds.length) := by
    have e := T5.1.1
    rw [T5.2.2.1] at e
    simpa only [List.length_nil, Nat.add_zero] using e
  have a3 : (Along (RoundIs (VerifiableInference.Desc.numAt Dw.t₁ Dw.t₂ 1)) (Desc.K14.Law.Sh.bk (aS
      σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 2).rounds x3.ds) := by
    rw [← hr3]
    exact hal5 x3 (.tail _ (.tail _ (.head _)))
  have halS : (∀ y ∈ [((seatedPiece (W := Wit ((VerifiableInference.OnPublicFiles.kcReq
      OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT) (Cl' := ProofFile.Cl) (F := (frameAt Dw (allOf Dw)
            Dw.key₂ 0)) (P₁ := (ProofFile.InstPub × σ₁)) (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂
                  si₂ Bs getS startS cF Np) 0) base d ext err), (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂
                  ok₂ fo₂ si₂ Bs getS startS cF Np) 0)), ((pc2 ((Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂
                  ok₂ fo₂ si₂ Bs getS startS cF Np) 1).retype (Cl' := ProofFile.Cl)) base2 d21 d22 ex2 er2),
                  (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 1)), (x3,
                  (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 2)), ((pc1
                  ((Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 3).retype
                  (Cl' := ProofFile.Cl)) base4 d4 ex4 er4), (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂
                        si₂ Bs getS startS cF Np) 3)), ((pc2 ((Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂
                        si₂ Bs getS startS cF Np) 4).retype (Cl' := ProofFile.Cl)) base5 d51 d52 ex5 er5),
                        (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 4))], Along
      (RoundIs (VerifiableInference.Desc.numAt Dw.t₁ Dw.t₂ 1)) y.2.rounds y.1.ds ∧ y.1.ds.length =
      y.2.rounds.length) := List.forall_mem_cons.2 ⟨⟨hal5 _ (.head _), l1⟩, List.forall_mem_cons.2
      ⟨⟨hal5 _ (.tail _ (.head _)), l2⟩, List.forall_mem_cons.2 ⟨⟨a3, l3⟩, List.forall_mem_cons.2
      ⟨⟨hal5 _ (.tail _ (.tail _ (.tail _ (.head _)))), l4⟩, List.forall_mem_cons.2 ⟨⟨hal5 _ (.tail
      _ (.tail _ (.tail _ (.tail _ (.head _))))), l5⟩, List.forall_mem_nil _⟩⟩⟩⟩⟩
  have NF := NF base d ext err base2 d21 d22 ex2 er2 x3 base4 d4 ex4 er4 base5 d51 d52 ex5 er5 x6
      base7 d7 ex7 er7 x8 x9 x10 x11 hlf
  have TF := TF base d ext err base2 d21 d22 ex2 er2 x3 base4 d4 ex4 er4 base5 d51 d52 ex5 er5 x6
      base7 d7 ex7 er7 x8 x9 x10 x11 hlf
  have hSh2 := hSh2 base d ext err base2 d21 d22 ex2 er2 x3 base4 d4 ex4 er4 base5 d51 d52 ex5 er5
      x6 base7 d7 ex7 er7 x8 x9 x10 x11 hlf
  have hSh5 := hSh5 base d ext err base2 d21 d22 ex2 er2 x3 base4 d4 ex4 er4 base5 d51 d52 ex5 er5
      x6 base7 d7 ex7 er7 x8 x9 x10 x11 hlf
  refine ledger_whole_fills_field
    (rU := (Desc.K14.Law.rad2At 2 (qS Zp Np)) 0) (rO := (Desc.K14.Law.rad5At 2 (qS Zp Np)) 0)
    (rSp := (Desc.K14.Law.rad5At 2 (qS Zp Np)) 1)
    (t₁A := Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
    (layU := Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
    (layO := Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
    (sentU := Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
    (Dw := Dw)
    (G := fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Zp.p.chains (qS Zp Np)
        (VerifiableInference.Desc.K12.Seat.tests Np))
    (decT₂ := decK (qS Zp Np).par 0 2852142980
        (Desc.K14.Law.Sh.rank (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.heldFull (qS Zp Np).par 0 (qS Zp Np).par.S.fold.index.saltBytes
          (Desc.K14.Law.full_index (qS Zp Np).par.S
            (Desc.K14.Law.full_of_shape hx
              (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx).shape))
          OnBytes.Flat.numsFull pp E))
    (N := tiedNumbers N₁
        (Desc.K14.Law.Fence.numbersSh
          (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
          (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
          (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
          (0, 0) (0, 0)))
    (Q := Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
    (Pm₀ := pmPoint (qS Zp Np).codes (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        (smpSt (qS Zp Np).codes
          (oNoSh
            (Desc.K14.Law.Sh.sentU
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)).size)
          stSh)
        (msSh (qS Zp Np).S ((Desc.K14.Law.rad2At 2 (qS Zp Np)) 0)
          ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 0) ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 1)
          (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
          (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
          (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)))
        (qS Zp Np).par 0 2852142980
        (Desc.K14.Law.Sh.rank (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.heldFull (qS Zp Np).par 0 (qS Zp Np).par.S.fold.index.saltBytes
          (Desc.K14.Law.full_index (qS Zp Np).par.S
            (Desc.K14.Law.full_of_shape hx
              (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx).shape))
          OnBytes.Flat.numsFull pp E)
        (fun s : St => s.st)
        (fun s : St => shiftBook
          (tiedNumbers N₁
            (Desc.K14.Law.Fence.numbersSh
              (Desc.K14.Law.Sh.t₁
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (Desc.K14.Law.Sh.layU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (Desc.K14.Law.Sh.layO
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (0, 0) (0, 0))).lo
          s.book)
        (pmZ (qS Zp Np).par Desc.K14.Law.Sh.idleP))
    (Oc := ocWith
        (ocEnd get N₁ Mg₁ links (VerifiableInference.Desc.First.flatPlaces true links true)) Rend)
    (nU := 0)
    (b1 := Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 0)
    (b2 := Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 1)
    (b3 := Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 2)
    (b4 := Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 3)
    (b5 := Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 4)
    (b6 := Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 5)
    (b7 := Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 6)
    (b8 := Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 7)
    (hbl := Desc.K14.Law.Sh.tests_hbl8
        (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        (Desc.K14.Law.Sh.tests_at hx
          (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
          (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
            (VerifiableInference.Desc.K12.Seat.tests Np))
          (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _
            _ hGp)))
    (arr := P5T.arrOf (P5T.planSeatsAll Zp Zp.D)) (c₀ := fun _ _ => 0)
    (Mg₀ := tiedMeaning get Mg₁
        (mgJoint (qS Zp Np).codes (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
          (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)) get smp₁ ms₁
          (Desc.K14.Law.Sh.xW (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
            (oS P₀ Tok σ₁ Dw get ms₁ N₁ links Zp x hx Rend oL Zs rP hZs hlaid Np smp₁ pp E Mg₁
              hpub hpinS hpinF))
          (smpSt (qS Zp Np).codes
            (oNoSh
              (Desc.K14.Law.Sh.sentU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)).size)
            stSh)
          (msSh (qS Zp Np).S ((Desc.K14.Law.rad2At 2 (qS Zp Np)) 0)
            ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 0) ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 1)
            (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)))
          (linLayW (qS Zp Np).codes (VerifiableInference.Desc.K13.whereOf Zp).lin)
          (fun q => VerifiableInference.Desc.Sound.stFirst (get q))
          (fun q =>
            (VerifiableInference.Desc.Sound.tabFirst (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)))
            (get q))
          (rgOf (qS Zp Np).codes (P5T.arrOf (P5T.planSeatsAll Zp Zp.D))
            (memK (qS Zp Np).S ((Desc.K14.Law.rad2At 2 (qS Zp Np)) 0)
              ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 0) ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 1)
              (Desc.K14.Law.Sh.t₁
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (Desc.K14.Law.Sh.layU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (Desc.K14.Law.Sh.layO
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (Desc.K14.Law.Sh.sentU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)).size)
            (rdK (qS Zp Np).codes))
          (omWK (qS Zp Np).codes (P5T.arrOf (P5T.planSeatsAll Zp Zp.D))
            (memK (qS Zp Np).S ((Desc.K14.Law.rad2At 2 (qS Zp Np)) 0)
              ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 0) ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 1)
              (Desc.K14.Law.Sh.t₁
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (Desc.K14.Law.Sh.layU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (Desc.K14.Law.Sh.layO
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (Desc.K14.Law.Sh.sentU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)).size)
            (rdK (qS Zp Np).codes)
            (Desc.K14.Law.Sh.sentU
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)).size
            (qS Zp Np))
          (qS Zp Np).par 2852142980 (gLaid (VerifiableInference.Desc.K13.whereOf Zp) get) 0
          2852142980
          (Desc.K14.Law.Sh.rank (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
          (Desc.K14.Law.heldFull (qS Zp Np).par 0 (qS Zp Np).par.S.fold.index.saltBytes
            (Desc.K14.Law.full_index (qS Zp Np).par.S
              (Desc.K14.Law.full_of_shape hx
                (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx).shape))
            OnBytes.Flat.numsFull pp E)
          (VerifiableInference.Desc.K13.whereOf Zp)
          (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
          (mgZ (qS Zp Np).codes (P5T.arrOf (P5T.planSeatsAll Zp Zp.D))
            (memK (qS Zp Np).S ((Desc.K14.Law.rad2At 2 (qS Zp Np)) 0)
              ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 0) ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 1)
              (Desc.K14.Law.Sh.t₁
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (Desc.K14.Law.Sh.layU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (Desc.K14.Law.Sh.layO
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (Desc.K14.Law.Sh.sentU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)).size)
            (rdK (qS Zp Np).codes)
            (numSh
              (Desc.K14.Law.Sh.sentU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)).size)
            Desc.K14.Law.Sh.idleM)))
    (mem := memK (qS Zp Np).S ((Desc.K14.Law.rad2At 2 (qS Zp Np)) 0)
        ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 0) ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 1)
        (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)).size)
    (rd := rdK (qS Zp Np).codes)
    (num := numSh
        (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)).size)
    (get := get) (smp₁ := smp₁) (ms₁ := ms₁)
    (xW := Desc.K14.Law.Sh.xW (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        (oS P₀ Tok σ₁ Dw get ms₁ N₁ links Zp x hx Rend oL Zs rP hZs hlaid Np smp₁ pp E Mg₁ hpub
          hpinS hpinF))
    (stOf₁ := VerifiableInference.Desc.Sound.stFirst)
    (tabP₁ := VerifiableInference.Desc.Sound.tabFirst (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)))
    (base := base) (d := d) (ext := ext) (err := err) (N₁ := N₁)
    (Ns := Desc.K14.Law.Fence.numbersSh
        (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (0, 0) (0, 0))
    (links := links) (ps := VerifiableInference.Desc.First.flatPlaces true links true)
    (gOf := gLaid (VerifiableInference.Desc.K13.whereOf Zp) get)
    (lo := (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)))
    (err₂ := 0)
    (rank := Desc.K14.Law.Sh.rank (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
    (held := Desc.K14.Law.heldFull (qS Zp Np).par 0 (qS Zp Np).par.S.fold.index.saltBytes
        (Desc.K14.Law.full_index (qS Zp Np).par.S
          (Desc.K14.Law.full_of_shape hx
            (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx).shape))
        OnBytes.Flat.numsFull pp E)
    (Pw := VerifiableInference.Desc.K13.whereOf Zp)
    (hlin := (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx).lin.trans
        (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx).shape.symm)
    (matC := Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull) (Mg₁ := Mg₁)
    (MgZ := mgZ (qS Zp Np).codes (P5T.arrOf (P5T.planSeatsAll Zp Zp.D))
        (memK (qS Zp Np).S ((Desc.K14.Law.rad2At 2 (qS Zp Np)) 0)
          ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 0) ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 1)
          (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
          (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
          (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
          (Desc.K14.Law.Sh.sentU
            (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)).size)
        (rdK (qS Zp Np).codes)
        (numSh
          (Desc.K14.Law.Sh.sentU
            (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)).size)
        Desc.K14.Law.Sh.idleM)
    (PmZ := pmZ (qS Zp Np).par Desc.K14.Law.Sh.idleP)
    (hix := Desc.K14.Law.Sh.tests_hix
        (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        (Desc.K14.Law.Sh.tests_at hx
          (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
          (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
            (VerifiableInference.Desc.K12.Seat.tests Np))
          (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _
            _ hGp)))
    (hroom := Desc.K14.Law.Sh.tests_hroom
        (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        (Desc.K14.Law.Sh.tests_at hx
          (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
          (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
            (VerifiableInference.Desc.K12.Seat.tests Np))
          (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _
            _ hGp)))
    (hpin := hJ.pin) (hwrow := hJ.wrow) (hevalLaid := hJ.evalLaid) (hwSits := hJ.wSits)
    (h2 := VerifiableInference.Desc.K13.Law.evalLaid_open_all Mg₁.more links) (h3 := h3)
    (hread := hRd) (hloB := le_of_eq (ht₁.trans NUM.1.symm))
    (hw := Nat.lt_of_lt_of_le hV (le_of_eq (ht₁.trans NUM.1.symm)))
    (hi := Nat.lt_of_lt_of_le hI (le_of_eq (ht₁.trans NUM.1.symm)))
    (hxW := Desc.K14.Law.Sh.paid_hxW (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        (oS P₀ Tok σ₁ Dw get ms₁ N₁ links Zp x hx Rend oL Zs rP hZs hlaid Np smp₁ pp E Mg₁ hpub
          hpinS hpinF)
        ((Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))) hO)
    (hsW := Desc.K14.Law.Sh.paid_hsW (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        (oS P₀ Tok σ₁ Dw get ms₁ N₁ links Zp x hx Rend oL Zs rP hZs hlaid Np smp₁ pp E Mg₁ hpub
          hpinS hpinF)
        ((Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))) hO)
    (hst := Desc.K14.Law.Sh.paid_hst) (R := Rend)
    (hbook := fun p y h hR => Desc.K14.Law.Sh.hbook_own
        (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        (oS P₀ Tok σ₁ Dw get ms₁ N₁ links Zp x hx Rend oL Zs rP hZs hlaid Np smp₁ pp E Mg₁ hpub
          hpinS hpinF)
        hF p y ⟨h, hR⟩)
    (htab := Desc.K14.Law.Sh.paid_htab
        (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        (oS P₀ Tok σ₁ Dw get ms₁ N₁ links Zp x hx Rend oL Zs rP hZs hlaid Np smp₁ pp E Mg₁ hpub
          hpinS hpinF))
    (hsh := Desc.K14.Law.Sh.paid_hsh (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        (oS P₀ Tok σ₁ Dw get ms₁ N₁ links Zp x hx Rend oL Zs rP hZs hlaid Np smp₁ pp E Mg₁ hpub
          hpinS hpinF)
        ((Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))) hO)
    (hg := fun p _ D _ _ hD y _ => gLaid_is (VerifiableInference.Desc.K13.whereOf Zp) get p D hD y)
    (hH := Desc.K14.Law.heldTie_asked (qS Zp Np).par 0
        (Desc.K14.Law.full_of_shape hx
          (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx).shape)
        pp E)
    (hpile := hJ.pile) (hpo := hJ.po) (slots := slots)
    (r9 := ownFam (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ Np.U) H2K.Member.rUFull)
    (r10 := ownFam (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) H2K.Member.rOFull)
    (Y := smpK (qS Zp Np).codes
        (shapeAt
          (parU (qS Zp Np)
            (Desc.K14.Law.Sh.sentU
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)))
          ⟨0,
            (places (qS Zp Np)
              (Desc.K14.Law.Sh.sentU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))).1
            (Desc.K14.Law.Sh.tests_hUw
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
              (Desc.K14.Law.Sh.tests_at hx
                (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                  (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                  startS cF _ _ _ hGp)))⟩)
        (shapeAt (parO (qS Zp Np))
          ⟨0,
            (places (qS Zp Np)
              (Desc.K14.Law.Sh.sentU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))).2.1⟩)
        (shapeAt (parO (qS Zp Np))
          ⟨1,
            (places (qS Zp Np)
              (Desc.K14.Law.Sh.sentU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))).2.2
            (Desc.K14.Law.Sh.tests_hS
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
              (Desc.K14.Law.Sh.tests_at hx
                (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                  (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                  startS cF _ _ _ hGp)))⟩)
        (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)).size)
    (f :=
        (tS Tok σ₁ Dw oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np c₁ k₁ c₂ k₂ c₃ k₃
          pp E e₁ e₂ e₃ dW wEnd).p₂)
    (x3 := x3) (x6 := x6) (x8 := x8) (x9 := x9) (x10 := x10) (x11 := x11) (base2 := base2)
    (d21 := d21) (d22 := d22) (ex2 := ex2) (er2 := er2) (base4 := base4) (d4 := d4) (ex4 := ex4)
    (er4 := er4) (base5 := base5) (d51 := d51) (d52 := d52) (ex5 := ex5) (er5 := er5)
    (base7 := base7) (d7 := d7) (ex7 := ex7) (er7 := er7) (hlo := ?_) (tU := NUM.2.2.2.1)
    (tO := NUM.2.2.2.2.1) (tS := NUM.2.2.2.2.2.1)
    (hS := Desc.K14.Law.Sh.tests_hS (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        (Desc.K14.Law.Sh.tests_at hx
          (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
          (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
            (VerifiableInference.Desc.K12.Seat.tests Np))
          (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _
            _ hGp)))
    (hnum := rfl)
    (hUw := Desc.K14.Law.Sh.tests_hUw
        (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        (Desc.K14.Law.Sh.tests_at hx
          (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
          (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
            (VerifiableInference.Desc.K12.Seat.tests Np))
          (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _
            _ hGp)))
    (hn0 := rfl)
    (hoU := fun z hz hs => memSits (qS Zp Np).S ((Desc.K14.Law.rad2At 2 (qS Zp Np)) 0)
        ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 0) ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 1)
        (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (qS Zp Np).codes
        (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (withOmega (qS Zp Np).S)
        (Desc.K14.Law.Sh.tests_hlU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
          (Desc.K14.Law.Sh.tests_at hx
            (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
            (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
              (VerifiableInference.Desc.K12.Seat.tests Np))
            (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
              _ _ _ hGp)))
        (Desc.K14.Law.Sh.tests_hlO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
          (Desc.K14.Law.Sh.tests_at hx
            (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
            (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
              (VerifiableInference.Desc.K12.Seat.tests Np))
            (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
              _ _ _ hGp)))
        (by
          rw
              [sizeU (qS Zp Np).S
                (Desc.K14.Law.Sh.sentU
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                (Desc.K14.Law.Sh.tests_hUw
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                  (Desc.K14.Law.Sh.tests_at hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                    (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                      (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                    (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                      startS cF _ _ _ hGp)))
                (Desc.K14.Law.Sh.tests_hm
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                  (Desc.K14.Law.Sh.tests_at hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                    (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                      (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                    (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                      startS cF _ _ _ hGp)))]
          decide)
        (by
          rw
              [sizeOmega (qS Zp Np).S
                (Desc.K14.Law.Sh.tests_hS
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                  (Desc.K14.Law.Sh.tests_at hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                    (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                      (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                    (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                      startS cF _ _ _ hGp)))]
          decide)
        (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)).size
        .oU z hz
        (by
          rw
              [(show
                  (tiedNumbers N₁
                    (Desc.K14.Law.Fence.numbersSh
                      (Desc.K14.Law.Sh.t₁
                        (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                      (Desc.K14.Law.Sh.layU
                        (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                      (Desc.K14.Law.Sh.layO
                        (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                      (0, 0) (0, 0))).tenant
                  = tenantSh
                  (Desc.K14.Law.Sh.t₁
                    (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                  (Desc.K14.Law.Sh.layU
                    (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                  (Desc.K14.Law.Sh.layO
                    (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                  from Desc.K14.Law.Sh.paid_hN
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                  (oS P₀ Tok σ₁ Dw get ms₁ N₁ links Zp x hx Rend oL Zs rP hZs hlaid Np smp₁ pp
                    E Mg₁ hpub hpinS hpinF))]
              at hs
          exact hs))
    (rad2 := Desc.K14.Law.rad2At 2 (qS Zp Np))
    (hC2 := Desc.K14.Law.Sh.tests_hC2
        (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        (Desc.K14.Law.Sh.tests_at hx
          (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
          (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
            (VerifiableInference.Desc.K12.Seat.tests Np))
          (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _
            _ hGp)))
    (memK2 := memK2 (qS Zp Np)
        (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.rad2At 2 (qS Zp Np)) (Desc.K14.Law.rad5At 2 (qS Zp Np)))
    (new2 := new2 (qS Zp Np)
        (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.rad2At 2 (qS Zp Np)) (Desc.K14.Law.rad5At 2 (qS Zp Np)))
    (entry2 := entry_two (qS Zp Np)
        (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.rad2At 2 (qS Zp Np)) (Desc.K14.Law.rad5At 2 (qS Zp Np))
        (Desc.K14.Law.Sh.tests_hUw (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
          (Desc.K14.Law.Sh.tests_at hx
            (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
            (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
              (VerifiableInference.Desc.K12.Seat.tests Np))
            (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
              _ _ _ hGp))))
    (all2 := all_two (qS Zp Np)
        (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.rad2At 2 (qS Zp Np)) (Desc.K14.Law.rad5At 2 (qS Zp Np))
        ((places (qS Zp Np)
            (Desc.K14.Law.Sh.sentU
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))).1
          (Desc.K14.Law.Sh.tests_hUw
            (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
            (Desc.K14.Law.Sh.tests_at hx
              (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
              (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
              (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS
                cF _ _ _ hGp))))
        ((sampled (qS Zp Np)
            (Desc.K14.Law.Sh.sentU
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (Desc.K14.Law.Sh.tests_hok
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
              (Desc.K14.Law.Sh.tests_at hx
                (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                  (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                  startS cF _ _ _ hGp)))).1
          (Desc.K14.Law.Sh.tests_hUw
            (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
            (Desc.K14.Law.Sh.tests_at hx
              (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
              (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
              (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS
                cF _ _ _ hGp)))
          _))
    (hno2 := hno_two (qS Zp Np)
        (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.rad2At 2 (qS Zp Np)) (Desc.K14.Law.rad5At 2 (qS Zp Np))
        (Desc.K14.Law.Sh.tests_hUw (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
          (Desc.K14.Law.Sh.tests_at hx
            (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
            (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
              (VerifiableInference.Desc.K12.Seat.tests Np))
            (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
              _ _ _ hGp))))
    (htree2 := htree_two (qS Zp Np)
        (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.rad2At 2 (qS Zp Np)) (Desc.K14.Law.rad5At 2 (qS Zp Np))
        (Desc.K14.Law.Sh.tests_hlU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
          (Desc.K14.Law.Sh.tests_at hx
            (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
            (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
              (VerifiableInference.Desc.K12.Seat.tests Np))
            (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
              _ _ _ hGp)))
        (by
          rw
              [sizeU (qS Zp Np).S
                (Desc.K14.Law.Sh.sentU
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                (Desc.K14.Law.Sh.tests_hUw
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                  (Desc.K14.Law.Sh.tests_at hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                    (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                      (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                    (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                      startS cF _ _ _ hGp)))
                (Desc.K14.Law.Sh.tests_hm
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                  (Desc.K14.Law.Sh.tests_at hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                    (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                      (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                    (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                      startS cF _ _ _ hGp)))]
          decide)
        base2 _ (NUM.2.1.trans ht₁.symm)
        ((seed_trees (qS Zp Np)
            (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
              0)
            (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
              1)
            (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
              2)
            (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
              3)
            (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
              4)
            (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
              5)
            (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
              6)
            (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
              7)
            (Desc.K14.Law.Sh.sentU
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (Desc.K14.Law.Sh.layU
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (Desc.K14.Law.Sh.layO
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (Desc.K14.Law.Sh.tests_hbl8
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
              (Desc.K14.Law.Sh.tests_at hx
                (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                  (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                  startS cF _ _ _ hGp)))
            (Desc.K14.Law.Sh.tests_hUw
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
              (Desc.K14.Law.Sh.tests_at hx
                (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                  (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                  startS cF _ _ _ hGp)))
            (Desc.K14.Law.Sh.tests_hlU
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
              (Desc.K14.Law.Sh.tests_at hx
                (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                  (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                  startS cF _ _ _ hGp)))
            (Desc.K14.Law.Sh.tests_hlO
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
              (Desc.K14.Law.Sh.tests_at hx
                (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                  (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                  startS cF _ _ _ hGp)))
            (VerifiableInference.Desc.numAt Dw.t₁ Dw.t₂ 1) d21 d22).1
          a2))
    (hSh2 := hSh2)
    (hnew2 := hnew_two (qS Zp Np)
        (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.rad2At 2 (qS Zp Np)) (Desc.K14.Law.rad5At 2 (qS Zp Np))
        (tiedNumbers N₁
          (Desc.K14.Law.Fence.numbersSh
            (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (0, 0) (0, 0)))
        (show
          (tiedNumbers N₁
            (Desc.K14.Law.Fence.numbersSh
              (Desc.K14.Law.Sh.t₁
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (Desc.K14.Law.Sh.layU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (Desc.K14.Law.Sh.layO
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (0, 0) (0, 0))).tenant
          = tenantSh
          (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
          (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
          (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
          from Desc.K14.Law.Sh.paid_hN
          (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
          (oS P₀ Tok σ₁ Dw get ms₁ N₁ links Zp x hx Rend oL Zs rP hZs hlaid Np smp₁ pp E Mg₁
            hpub hpinS hpinF))
        (Desc.K14.Law.Sh.tests_hlU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
          (Desc.K14.Law.Sh.tests_at hx
            (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
            (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
              (VerifiableInference.Desc.K12.Seat.tests Np))
            (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
              _ _ _ hGp)))
        (Desc.K14.Law.Sh.tests_hlO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
          (Desc.K14.Law.Sh.tests_at hx
            (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
            (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
              (VerifiableInference.Desc.K12.Seat.tests Np))
            (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
              _ _ _ hGp)))
        (by
          rw
              [sizeU (qS Zp Np).S
                (Desc.K14.Law.Sh.sentU
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                (Desc.K14.Law.Sh.tests_hUw
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                  (Desc.K14.Law.Sh.tests_at hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                    (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                      (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                    (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                      startS cF _ _ _ hGp)))
                (Desc.K14.Law.Sh.tests_hm
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                  (Desc.K14.Law.Sh.tests_at hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                    (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                      (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                    (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                      startS cF _ _ _ hGp)))]
          decide)
        (by
          rw
              [sizeOmega (qS Zp Np).S
                (Desc.K14.Law.Sh.tests_hS
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                  (Desc.K14.Law.Sh.tests_at hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                    (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                      (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                    (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                      startS cF _ _ _ hGp)))]
          decide))
    (rad5 := Desc.K14.Law.rad5At 2 (qS Zp Np))
    (hC5 := Desc.K14.Law.Sh.tests_hC5
        (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        (Desc.K14.Law.Sh.tests_at hx
          (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
          (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
            (VerifiableInference.Desc.K12.Seat.tests Np))
          (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _
            _ hGp)))
    (memK5 := memK5 (qS Zp Np)
        (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.rad2At 2 (qS Zp Np)) (Desc.K14.Law.rad5At 2 (qS Zp Np)))
    (new5 := new5 (qS Zp Np)
        (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.rad2At 2 (qS Zp Np)) (Desc.K14.Law.rad5At 2 (qS Zp Np)))
    (entry5 := entry_five (qS Zp Np)
        (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.rad2At 2 (qS Zp Np)) (Desc.K14.Law.rad5At 2 (qS Zp Np))
        (Desc.K14.Law.Sh.tests_hS (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
          (Desc.K14.Law.Sh.tests_at hx
            (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
            (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
              (VerifiableInference.Desc.K12.Seat.tests Np))
            (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
              _ _ _ hGp))))
    (all5 := all_five (qS Zp Np)
        (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.rad2At 2 (qS Zp Np)) (Desc.K14.Law.rad5At 2 (qS Zp Np))
        (places (qS Zp Np)
          (Desc.K14.Law.Sh.sentU
            (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))).2.1
        ((sampled (qS Zp Np)
            (Desc.K14.Law.Sh.sentU
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (Desc.K14.Law.Sh.tests_hok
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
              (Desc.K14.Law.Sh.tests_at hx
                (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                  (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                  startS cF _ _ _ hGp)))).2.1
          _)
        ((places (qS Zp Np)
            (Desc.K14.Law.Sh.sentU
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))).2.2
          (Desc.K14.Law.Sh.tests_hS
            (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
            (Desc.K14.Law.Sh.tests_at hx
              (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
              (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
              (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS
                cF _ _ _ hGp))))
        ((sampled (qS Zp Np)
            (Desc.K14.Law.Sh.sentU
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (Desc.K14.Law.Sh.tests_hok
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
              (Desc.K14.Law.Sh.tests_at hx
                (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                  (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                  startS cF _ _ _ hGp)))).2.2
          _))
    (hno5 := fun k _ => hno_five (qS Zp Np)
        (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.rad2At 2 (qS Zp Np)) (Desc.K14.Law.rad5At 2 (qS Zp Np))
        (Desc.K14.Law.Sh.tests_hS (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
          (Desc.K14.Law.Sh.tests_at hx
            (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
            (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
              (VerifiableInference.Desc.K12.Seat.tests Np))
            (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
              _ _ _ hGp)))
        k)
    (htree5 := htree_five (qS Zp Np)
        (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.rad2At 2 (qS Zp Np)) (Desc.K14.Law.rad5At 2 (qS Zp Np))
        (Desc.K14.Law.Sh.tests_hS (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
          (Desc.K14.Law.Sh.tests_at hx
            (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
            (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
              (VerifiableInference.Desc.K12.Seat.tests Np))
            (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
              _ _ _ hGp)))
        (Desc.K14.Law.Sh.tests_hlO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
          (Desc.K14.Law.Sh.tests_at hx
            (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
            (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
              (VerifiableInference.Desc.K12.Seat.tests Np))
            (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
              _ _ _ hGp)))
        base5 _ (NUM.2.2.1.trans (by rw [ht₁]))
        ((seed_trees (qS Zp Np)
            (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
              0)
            (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
              1)
            (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
              2)
            (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
              3)
            (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
              4)
            (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
              5)
            (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
              6)
            (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
              7)
            (Desc.K14.Law.Sh.sentU
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (Desc.K14.Law.Sh.layU
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (Desc.K14.Law.Sh.layO
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (Desc.K14.Law.Sh.tests_hbl8
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
              (Desc.K14.Law.Sh.tests_at hx
                (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                  (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                  startS cF _ _ _ hGp)))
            (Desc.K14.Law.Sh.tests_hUw
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
              (Desc.K14.Law.Sh.tests_at hx
                (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                  (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                  startS cF _ _ _ hGp)))
            (Desc.K14.Law.Sh.tests_hlU
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
              (Desc.K14.Law.Sh.tests_at hx
                (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                  (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                  startS cF _ _ _ hGp)))
            (Desc.K14.Law.Sh.tests_hlO
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
              (Desc.K14.Law.Sh.tests_at hx
                (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                  (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                  startS cF _ _ _ hGp)))
            (VerifiableInference.Desc.numAt Dw.t₁ Dw.t₂ 1) d51 d52).2
          a5))
    (hSh5 := hSh5)
    (hnew5 := hnew_five (qS Zp Np)
        (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.rad2At 2 (qS Zp Np)) (Desc.K14.Law.rad5At 2 (qS Zp Np))
        (tiedNumbers N₁
          (Desc.K14.Law.Fence.numbersSh
            (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (0, 0) (0, 0)))
        (show
          (tiedNumbers N₁
            (Desc.K14.Law.Fence.numbersSh
              (Desc.K14.Law.Sh.t₁
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (Desc.K14.Law.Sh.layU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (Desc.K14.Law.Sh.layO
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (0, 0) (0, 0))).tenant
          = tenantSh
          (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
          (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
          (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
          from Desc.K14.Law.Sh.paid_hN
          (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
          (oS P₀ Tok σ₁ Dw get ms₁ N₁ links Zp x hx Rend oL Zs rP hZs hlaid Np smp₁ pp E Mg₁
            hpub hpinS hpinF))
        (Desc.K14.Law.Sh.tests_hlU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
          (Desc.K14.Law.Sh.tests_at hx
            (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
            (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
              (VerifiableInference.Desc.K12.Seat.tests Np))
            (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
              _ _ _ hGp)))
        (Desc.K14.Law.Sh.tests_hlO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
          (Desc.K14.Law.Sh.tests_at hx
            (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
            (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
              (VerifiableInference.Desc.K12.Seat.tests Np))
            (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
              _ _ _ hGp)))
        (by
          rw
              [sizeU (qS Zp Np).S
                (Desc.K14.Law.Sh.sentU
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                (Desc.K14.Law.Sh.tests_hUw
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                  (Desc.K14.Law.Sh.tests_at hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                    (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                      (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                    (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                      startS cF _ _ _ hGp)))
                (Desc.K14.Law.Sh.tests_hm
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                  (Desc.K14.Law.Sh.tests_at hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                    (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                      (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                    (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                      startS cF _ _ _ hGp)))]
          decide)
        (by
          rw
              [sizeOmega (qS Zp Np).S
                (Desc.K14.Law.Sh.tests_hS
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                  (Desc.K14.Law.Sh.tests_at hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                    (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                      (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                    (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                      startS cF _ _ _ hGp)))]
          decide))
    (eN := rfl) (eD := rfl) (eO := rfl) (eP := rfl) (eM₀ := rfl) (M := Desc.K14.Law.Sh.idleM)
    (eMZ := rfl) (P := Desc.K14.Law.Sh.idleP) (ePZ := rfl) (Wr := Johnson.G.dryProofFull.2.1)
    (hIx := Desc.K14.Law.Sh.tests_hIx
        (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        (Desc.K14.Law.Sh.tests_at hx
          (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
          (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
            (VerifiableInference.Desc.K12.Seat.tests Np))
          (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _
            _ hGp)))
    (hdW := hdW) (hn := hn)
    (hKR :=
        (Desc.K14.Law.seat_radii_terms hx
          (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp).binders.hKR)
    (hN64 := Desc.K14.Law.Sh.tests_hN64
        (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        (Desc.K14.Law.Sh.tests_at hx
          (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
          (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
            (VerifiableInference.Desc.K12.Seat.tests Np))
          (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _
            _ hGp)))
    (hOB :=
        (Desc.K14.Law.seat_radii_terms hx
          (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp).binders.hOB)
    (t2 := t2) (t4 := t4) (t5 := t5) (t7 := t7)
    (hsL := Desc.K14.Law.Sh.tests_hsL
        (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        (Desc.K14.Law.Sh.tests_at hx
          (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
          (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
            (VerifiableInference.Desc.K12.Seat.tests Np))
          (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _
            _ hGp)))
    (b9 := ?_) (b10 := ?_)
    (hlU := Desc.K14.Law.Sh.tests_hlU
        (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        (Desc.K14.Law.Sh.tests_at hx
          (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
          (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
            (VerifiableInference.Desc.K12.Seat.tests Np))
          (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _
            _ hGp)))
    (hlO := Desc.K14.Law.Sh.tests_hlO
        (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        (Desc.K14.Law.Sh.tests_at hx
          (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
          (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
            (VerifiableInference.Desc.K12.Seat.tests Np))
          (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _
            _ hGp)))
    (hm := Desc.K14.Law.Sh.tests_hm (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        (Desc.K14.Law.Sh.tests_at hx
          (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
          (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
            (VerifiableInference.Desc.K12.Seat.tests Np))
          (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _
            _ hGp)))
    (hp := Desc.K14.Law.Sh.tests_hp8 (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        (Desc.K14.Law.Sh.tests_at hx
          (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
          (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
            (VerifiableInference.Desc.K12.Seat.tests Np))
          (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _
            _ hGp)))
    (hok := Desc.K14.Law.Sh.tests_hok
        (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        (Desc.K14.Law.Sh.tests_at hx
          (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
          (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
            (VerifiableInference.Desc.K12.Seat.tests Np))
          (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _
            _ hGp)))
    (ch := Zp.p.chains)
    (hY01 := smpK_front_paid (qS Zp Np)
        (shapeAt
          (parU (qS Zp Np)
            (Desc.K14.Law.Sh.sentU
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)))
          ⟨0,
            (places (qS Zp Np)
              (Desc.K14.Law.Sh.sentU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))).1
            (Desc.K14.Law.Sh.tests_hUw
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
              (Desc.K14.Law.Sh.tests_at hx
                (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                  (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                  startS cF _ _ _ hGp)))⟩)
        (shapeAt (parO (qS Zp Np))
          ⟨0,
            (places (qS Zp Np)
              (Desc.K14.Law.Sh.sentU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))).2.1⟩)
        (shapeAt (parO (qS Zp Np))
          ⟨1,
            (places (qS Zp Np)
              (Desc.K14.Law.Sh.sentU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))).2.2
            (Desc.K14.Law.Sh.tests_hS
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
              (Desc.K14.Law.Sh.tests_at hx
                (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                  (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                  startS cF _ _ _ hGp)))⟩)
        (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)))
    (hY12 := fun _ _ _ _ y _ _ => smpK_two_paid (qS Zp Np)
        (shapeAt
          (parU (qS Zp Np)
            (Desc.K14.Law.Sh.sentU
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)))
          ⟨0,
            (places (qS Zp Np)
              (Desc.K14.Law.Sh.sentU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))).1
            (Desc.K14.Law.Sh.tests_hUw
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
              (Desc.K14.Law.Sh.tests_at hx
                (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                  (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                  startS cF _ _ _ hGp)))⟩)
        (shapeAt (parO (qS Zp Np))
          ⟨0,
            (places (qS Zp Np)
              (Desc.K14.Law.Sh.sentU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))).2.1⟩)
        (shapeAt (parO (qS Zp Np))
          ⟨1,
            (places (qS Zp Np)
              (Desc.K14.Law.Sh.sentU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))).2.2
            (Desc.K14.Law.Sh.tests_hS
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
              (Desc.K14.Law.Sh.tests_at hx
                (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                  (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                  startS cF _ _ _ hGp)))⟩)
        (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        y.1.2)
    (hYH := ?_) (hb2 := le_of_eq (NUM.1.trans NUM.2.1.symm))
    (nWU := Desc.K14.Law.Sh.paid_nWU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        (oS P₀ Tok σ₁ Dw get ms₁ N₁ links Zp x hx Rend oL Zs rP hZs hlaid Np smp₁ pp E Mg₁ hpub
          hpinS hpinF)
        ((Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))) hO)
    (nWS := Desc.K14.Law.Sh.paid_nWS (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        (oS P₀ Tok σ₁ Dw get ms₁ N₁ links Zp x hx Rend oL Zs rP hZs hlaid Np smp₁ pp E Mg₁ hpub
          hpinS hpinF)
        ((Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))) hO)
    (nIU := Desc.K14.Law.Sh.paid_nIU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        (oS P₀ Tok σ₁ Dw get ms₁ N₁ links Zp x hx Rend oL Zs rP hZs hlaid Np smp₁ pp E Mg₁ hpub
          hpinS hpinF)
        ((Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))) hO)
    (nIS := Desc.K14.Law.Sh.paid_nIS (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        (oS P₀ Tok σ₁ Dw get ms₁ N₁ links Zp x hx Rend oL Zs rP hZs hlaid Np smp₁ pp E Mg₁ hpub
          hpinS hpinF)
        ((Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))) hO)
    (ev9 := Desc.K14.Law.Sh.evKeptP (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        (oS P₀ Tok σ₁ Dw get ms₁ N₁ links Zp x hx Rend oL Zs rP hZs hlaid Np smp₁ pp E Mg₁ hpub
          hpinS hpinF)
        _ _ _ 9 hJ hF)
    (ev10 := Desc.K14.Law.Sh.evKeptP (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        (oS P₀ Tok σ₁ Dw get ms₁ N₁ links Zp x hx Rend oL Zs rP hZs hlaid Np smp₁ pp E Mg₁ hpub
          hpinS hpinF)
        _ _ _ 10 hJ hF)
    (πA := H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ Np.U) (hbA := NF.alike) (heA := NF.place.early)
    (ha1A := NF.place.answers)
    (hms := hms_sh (qS Zp Np).S ((Desc.K14.Law.rad2At 2 (qS Zp Np)) 0)
        ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 0) ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 1)
        (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)).size
        (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)))
    (t₂A := t₂A) (LA := OnBytes.Slice.Sg.lstJ) (mCA := OnBytes.Slice.Sg.flC)
    (mSA := OnBytes.Slice.Sg.flZ) (mWA := OnBytes.Slice.Sg.flZ) (rdNA := rdNA) (dBA := dBA)
    (dtA := dtA)
    (eA := batV0 (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ Np.U) H2K.Member.rUFull *
        (bsRound .two dBA.entry dBA.kind).w)
    (εtA := errJ (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ Np.U) H2K.Member.rUFull dtA)
    (rA := H2K.Member.rUFull) (h0A := NF.back) (hdsA := NF.ds)
    (herrA := herr_ownFam (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ Np.U) H2K.Member.rUFull NF.ds)
    (hAA := NF.place) (hjA := NF.joh) (hb1A := NF.batOne) (hleA := Nat.le_refl _) (hoA := NF.own)
    (hPA := NF.labels) (n2A := NF.n2) (n3A := NF.n3) (hftA := NF.ft)
    (hl := Desc.K14.Law.Sh.tests_hl (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        (Desc.K14.Law.Sh.tests_at hx
          (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
          (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
            (VerifiableInference.Desc.K12.Seat.tests Np))
          (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _
            _ hGp)))
    (hn1 := rfl) (hn2 := rfl)
    (hNA := Fence.hN_sh (qS Zp Np).S ((Desc.K14.Law.rad2At 2 (qS Zp Np)) 0)
        ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 0) ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 1)
        (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (tiedNumbers N₁
          (Desc.K14.Law.Fence.numbersSh
            (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (0, 0) (0, 0)))
        (P5T.arrOf (P5T.planSeatsAll Zp Zp.D))
        (Desc.K14.Law.Sh.paid_harr (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
          (oS P₀ Tok σ₁ Dw get ms₁ N₁ links Zp x hx Rend oL Zs rP hZs hlaid Np smp₁ pp E Mg₁
            hpub hpinS hpinF)
          ((Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))) hO)
        9)
    (hapSA :=
        (Fence.hap_nine
          (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
          (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
          (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
          (qS Zp Np).codes
          (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
          (withOmega (qS Zp Np).S)
          (Desc.K14.Law.Sh.tests_hlU
            (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
            (Desc.K14.Law.Sh.tests_at hx
              (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
              (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
              (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                startS cF _ _ _ hGp)))
          (Desc.K14.Law.Sh.tests_hlO
            (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
            (Desc.K14.Law.Sh.tests_at hx
              (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
              (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
              (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                startS cF _ _ _ hGp)))
          (by
            rw
                [sizeU (qS Zp Np).S
                  (Desc.K14.Law.Sh.sentU
                    (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                  (Desc.K14.Law.Sh.tests_hUw
                    (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                    (Desc.K14.Law.Sh.tests_at hx
                      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                      (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
                        (Zp.p.chains) (qS Zp Np)
                        (VerifiableInference.Desc.K12.Seat.tests Np))
                      (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs
                        getS startS cF _ _ _ hGp)))
                  (Desc.K14.Law.Sh.tests_hm
                    (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                    (Desc.K14.Law.Sh.tests_at hx
                      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                      (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
                        (Zp.p.chains) (qS Zp Np)
                        (VerifiableInference.Desc.K12.Seat.tests Np))
                      (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs
                        getS startS cF _ _ _ hGp)))]
            decide)
          (by
            rw
                [sizeOmega (qS Zp Np).S
                  (Desc.K14.Law.Sh.tests_hS
                    (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                    (Desc.K14.Law.Sh.tests_at hx
                      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                      (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
                        (Zp.p.chains) (qS Zp Np)
                        (VerifiableInference.Desc.K12.Seat.tests Np))
                      (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs
                        getS startS cF _ _ _ hGp)))]
            decide)
          (tiedNumbers N₁
            (Desc.K14.Law.Fence.numbersSh
              (Desc.K14.Law.Sh.t₁
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (Desc.K14.Law.Sh.layU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (Desc.K14.Law.Sh.layO
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (0, 0) (0, 0)))
          (show
            (tiedNumbers N₁
              (Desc.K14.Law.Fence.numbersSh
                (Desc.K14.Law.Sh.t₁
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                (Desc.K14.Law.Sh.layU
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                (Desc.K14.Law.Sh.layO
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                (0, 0) (0, 0))).tenant
            = tenantSh
            (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (Desc.K14.Law.Sh.layU
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (Desc.K14.Law.Sh.layO
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            from Desc.K14.Law.Sh.paid_hN
            (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
            (oS P₀ Tok σ₁ Dw get ms₁ N₁ links Zp x hx Rend oL Zs rP hZs hlaid Np smp₁ pp E
              Mg₁ hpub hpinS hpinF))
          (P5T.arrOf (P5T.planSeatsAll Zp Zp.D))
          (Desc.K14.Law.Sh.paid_harr
            (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
            (oS P₀ Tok σ₁ Dw get ms₁ N₁ links Zp x hx Rend oL Zs rP hZs hlaid Np smp₁ pp E
              Mg₁ hpub hpinS hpinF)
            ((Desc.K14.Law.Sh.t₁
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)))
            hO)).1)
    (hapOA :=
        (Fence.hap_nine
          (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
          (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
          (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
          (qS Zp Np).codes
          (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
          (withOmega (qS Zp Np).S)
          (Desc.K14.Law.Sh.tests_hlU
            (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
            (Desc.K14.Law.Sh.tests_at hx
              (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
              (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
              (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                startS cF _ _ _ hGp)))
          (Desc.K14.Law.Sh.tests_hlO
            (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
            (Desc.K14.Law.Sh.tests_at hx
              (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
              (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
              (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                startS cF _ _ _ hGp)))
          (by
            rw
                [sizeU (qS Zp Np).S
                  (Desc.K14.Law.Sh.sentU
                    (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                  (Desc.K14.Law.Sh.tests_hUw
                    (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                    (Desc.K14.Law.Sh.tests_at hx
                      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                      (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
                        (Zp.p.chains) (qS Zp Np)
                        (VerifiableInference.Desc.K12.Seat.tests Np))
                      (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs
                        getS startS cF _ _ _ hGp)))
                  (Desc.K14.Law.Sh.tests_hm
                    (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                    (Desc.K14.Law.Sh.tests_at hx
                      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                      (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
                        (Zp.p.chains) (qS Zp Np)
                        (VerifiableInference.Desc.K12.Seat.tests Np))
                      (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs
                        getS startS cF _ _ _ hGp)))]
            decide)
          (by
            rw
                [sizeOmega (qS Zp Np).S
                  (Desc.K14.Law.Sh.tests_hS
                    (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                    (Desc.K14.Law.Sh.tests_at hx
                      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                      (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
                        (Zp.p.chains) (qS Zp Np)
                        (VerifiableInference.Desc.K12.Seat.tests Np))
                      (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs
                        getS startS cF _ _ _ hGp)))]
            decide)
          (tiedNumbers N₁
            (Desc.K14.Law.Fence.numbersSh
              (Desc.K14.Law.Sh.t₁
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (Desc.K14.Law.Sh.layU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (Desc.K14.Law.Sh.layO
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (0, 0) (0, 0)))
          (show
            (tiedNumbers N₁
              (Desc.K14.Law.Fence.numbersSh
                (Desc.K14.Law.Sh.t₁
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                (Desc.K14.Law.Sh.layU
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                (Desc.K14.Law.Sh.layO
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                (0, 0) (0, 0))).tenant
            = tenantSh
            (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (Desc.K14.Law.Sh.layU
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (Desc.K14.Law.Sh.layO
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            from Desc.K14.Law.Sh.paid_hN
            (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
            (oS P₀ Tok σ₁ Dw get ms₁ N₁ links Zp x hx Rend oL Zs rP hZs hlaid Np smp₁ pp E
              Mg₁ hpub hpinS hpinF))
          (P5T.arrOf (P5T.planSeatsAll Zp Zp.D))
          (Desc.K14.Law.Sh.paid_harr
            (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
            (oS P₀ Tok σ₁ Dw get ms₁ N₁ links Zp x hx Rend oL Zs rP hZs hlaid Np smp₁ pp E
              Mg₁ hpub hpinS hpinF)
            ((Desc.K14.Law.Sh.t₁
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)))
            hO)).2)
    (hY10A := fun a τ b ha hout => smpK_ten_paid (qS Zp Np)
        (shapeAt
          (parU (qS Zp Np)
            (Desc.K14.Law.Sh.sentU
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)))
          ⟨0,
            (places (qS Zp Np)
              (Desc.K14.Law.Sh.sentU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))).1
            (Desc.K14.Law.Sh.tests_hUw
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
              (Desc.K14.Law.Sh.tests_at hx
                (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                  (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                  startS cF _ _ _ hGp)))⟩)
        (shapeAt (parO (qS Zp Np))
          ⟨0,
            (places (qS Zp Np)
              (Desc.K14.Law.Sh.sentU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))).2.1⟩)
        (shapeAt (parO (qS Zp Np))
          ⟨1,
            (places (qS Zp Np)
              (Desc.K14.Law.Sh.sentU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))).2.2
            (Desc.K14.Law.Sh.tests_hS
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
              (Desc.K14.Law.Sh.tests_at hx
                (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                  (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                  startS cF _ _ _ hGp)))⟩)
        (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (decK (qS Zp Np).par 0 2852142980
          (Desc.K14.Law.Sh.rank (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
          (Desc.K14.Law.heldFull (qS Zp Np).par 0 (qS Zp Np).par.S.fold.index.saltBytes
            (Desc.K14.Law.full_index (qS Zp Np).par.S
              (Desc.K14.Law.full_of_shape hx
                (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx).shape))
            OnBytes.Flat.numsFull pp E))
        (pmPoint (qS Zp Np).codes (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
          (smpSt (qS Zp Np).codes
            (oNoSh
              (Desc.K14.Law.Sh.sentU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)).size)
            stSh)
          (msSh (qS Zp Np).S ((Desc.K14.Law.rad2At 2 (qS Zp Np)) 0)
            ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 0) ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 1)
            (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)))
          (qS Zp Np).par 0 2852142980
          (Desc.K14.Law.Sh.rank (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
          (Desc.K14.Law.heldFull (qS Zp Np).par 0 (qS Zp Np).par.S.fold.index.saltBytes
            (Desc.K14.Law.full_index (qS Zp Np).par.S
              (Desc.K14.Law.full_of_shape hx
                (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx).shape))
            OnBytes.Flat.numsFull pp E)
          (fun s : St => s.st)
          (fun s : St => shiftBook
            (tiedNumbers N₁
              (Desc.K14.Law.Fence.numbersSh
                (Desc.K14.Law.Sh.t₁
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                (Desc.K14.Law.Sh.layU
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                (Desc.K14.Law.Sh.layO
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                (0, 0) (0, 0))).lo
            s.book)
          (pmZ (qS Zp Np).par Desc.K14.Law.Sh.idleP))
        (qS Zp Np).S.fold.columns 0 (qS Zp Np).codes
        (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        (msSh (qS Zp Np).S ((Desc.K14.Law.rad2At 2 (qS Zp Np)) 0)
          ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 0) ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 1)
          (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
          (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
          (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)))
        (tiedNumbers N₁
          (Desc.K14.Law.Fence.numbersSh
            (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (0, 0) (0, 0)))
        (ocWith
          (ocEnd get N₁ Mg₁ links (VerifiableInference.Desc.First.flatPlaces true links true))
          Rend)
        (oNoSh
          (Desc.K14.Law.Sh.sentU
            (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)).size)
        (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        ((tS Tok σ₁ Dw oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np c₁ k₁ c₂ k₂ c₃
            k₃ pp E e₁ e₂ e₃ dW wEnd).p₂)
        _
        (sizeU (qS Zp Np).S
          (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
          (Desc.K14.Law.Sh.tests_hUw
            (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
            (Desc.K14.Law.Sh.tests_at hx
              (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
              (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
              (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS
                cF _ _ _ hGp)))
          (Desc.K14.Law.Sh.tests_hm
            (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
            (Desc.K14.Law.Sh.tests_at hx
              (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
              (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
              (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS
                cF _ _ _ hGp))))
        (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ Np.U) x9 NF.alike NF.place.early NF.place.answers a τ b ha
        hout)
    (πB := H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) (hbB := TF.alike) (heB := TF.place.early)
    (ha1B := TF.place.answers) (t₂B := t₂B) (rB := H2K.Member.rOFull) (LB := OnBytes.Slice.Sg.lstJ)
    (mCB := OnBytes.Slice.Sg.flC) (mSB := OnBytes.Slice.Sg.flZ) (mWB := OnBytes.Slice.Sg.flZ)
    (rdNB := rdNB) (dBB := dBB) (dtB := dtB)
    (eB := batV0 (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) H2K.Member.rOFull *
        (bsRound .two dBB.entry dBB.kind).w)
    (v₀B := batV0 (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) H2K.Member.rOFull)
    (εtB := errJ (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) H2K.Member.rOFull dtB) (h0B := TF.back)
    (hdsB := TF.ds)
    (herrB := herr_ownFam (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) H2K.Member.rOFull TF.ds)
    (hAB := TF.place) (hPayB := (pays_at_tile ⟨TF.place, TF.small⟩ TF.joh).1)
    (h1B := (pays_at_tile ⟨TF.place, TF.small⟩ TF.joh).2.1)
    (hlogB := (pays_at_tile ⟨TF.place, TF.small⟩ TF.joh).2.2) (hleB := Nat.le_refl _)
    (hoB := TF.own) (hPB := TF.labels) (n2B := TF.n2) (n3B := TF.n3) (hftB := TF.ft)
    (hNB := Fence.hN_sh (qS Zp Np).S ((Desc.K14.Law.rad2At 2 (qS Zp Np)) 0)
        ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 0) ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 1)
        (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (tiedNumbers N₁
          (Desc.K14.Law.Fence.numbersSh
            (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (0, 0) (0, 0)))
        (P5T.arrOf (P5T.planSeatsAll Zp Zp.D))
        (Desc.K14.Law.Sh.paid_harr (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
          (oS P₀ Tok σ₁ Dw get ms₁ N₁ links Zp x hx Rend oL Zs rP hZs hlaid Np smp₁ pp E Mg₁
            hpub hpinS hpinF)
          ((Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))) hO)
        10)
    (hapOB := Fence.hap_ten
        (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (qS Zp Np).codes
        (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (withOmega (qS Zp Np).S)
        (Desc.K14.Law.Sh.tests_hlU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
          (Desc.K14.Law.Sh.tests_at hx
            (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
            (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
              (VerifiableInference.Desc.K12.Seat.tests Np))
            (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
              _ _ _ hGp)))
        (Desc.K14.Law.Sh.tests_hlO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
          (Desc.K14.Law.Sh.tests_at hx
            (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
            (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
              (VerifiableInference.Desc.K12.Seat.tests Np))
            (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
              _ _ _ hGp)))
        (by
          rw
              [sizeU (qS Zp Np).S
                (Desc.K14.Law.Sh.sentU
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                (Desc.K14.Law.Sh.tests_hUw
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                  (Desc.K14.Law.Sh.tests_at hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                    (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                      (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                    (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                      startS cF _ _ _ hGp)))
                (Desc.K14.Law.Sh.tests_hm
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                  (Desc.K14.Law.Sh.tests_at hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                    (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                      (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                    (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                      startS cF _ _ _ hGp)))]
          decide)
        (by
          rw
              [sizeOmega (qS Zp Np).S
                (Desc.K14.Law.Sh.tests_hS
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                  (Desc.K14.Law.Sh.tests_at hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                    (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                      (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                    (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                      startS cF _ _ _ hGp)))]
          decide)
        (tiedNumbers N₁
          (Desc.K14.Law.Fence.numbersSh
            (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (0, 0) (0, 0)))
        (show
          (tiedNumbers N₁
            (Desc.K14.Law.Fence.numbersSh
              (Desc.K14.Law.Sh.t₁
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (Desc.K14.Law.Sh.layU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (Desc.K14.Law.Sh.layO
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
              (0, 0) (0, 0))).tenant
          = tenantSh
          (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
          (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
          (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
          from Desc.K14.Law.Sh.paid_hN
          (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
          (oS P₀ Tok σ₁ Dw get ms₁ N₁ links Zp x hx Rend oL Zs rP hZs hlaid Np smp₁ pp E Mg₁
            hpub hpinS hpinF))
        (P5T.arrOf (P5T.planSeatsAll Zp Zp.D))
        (Desc.K14.Law.Sh.paid_harr (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
          (oS P₀ Tok σ₁ Dw get ms₁ N₁ links Zp x hx Rend oL Zs rP hZs hlaid Np smp₁ pp E Mg₁
            hpub hpinS hpinF)
          ((Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))) hO))
    (hY11B := fun a τ b ha hout => smpK_eleven_paid (qS Zp Np)
        (shapeAt
          (parU (qS Zp Np)
            (Desc.K14.Law.Sh.sentU
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)))
          ⟨0,
            (places (qS Zp Np)
              (Desc.K14.Law.Sh.sentU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))).1
            (Desc.K14.Law.Sh.tests_hUw
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
              (Desc.K14.Law.Sh.tests_at hx
                (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                  (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                  startS cF _ _ _ hGp)))⟩)
        (shapeAt (parO (qS Zp Np))
          ⟨0,
            (places (qS Zp Np)
              (Desc.K14.Law.Sh.sentU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))).2.1⟩)
        (shapeAt (parO (qS Zp Np))
          ⟨1,
            (places (qS Zp Np)
              (Desc.K14.Law.Sh.sentU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))).2.2
            (Desc.K14.Law.Sh.tests_hS
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
              (Desc.K14.Law.Sh.tests_at hx
                (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                  (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                  startS cF _ _ _ hGp)))⟩)
        (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (decK (qS Zp Np).par 0 2852142980
          (Desc.K14.Law.Sh.rank (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
          (Desc.K14.Law.heldFull (qS Zp Np).par 0 (qS Zp Np).par.S.fold.index.saltBytes
            (Desc.K14.Law.full_index (qS Zp Np).par.S
              (Desc.K14.Law.full_of_shape hx
                (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx).shape))
            OnBytes.Flat.numsFull pp E))
        (pmPoint (qS Zp Np).codes (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
          (smpSt (qS Zp Np).codes
            (oNoSh
              (Desc.K14.Law.Sh.sentU
                (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)).size)
            stSh)
          (msSh (qS Zp Np).S ((Desc.K14.Law.rad2At 2 (qS Zp Np)) 0)
            ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 0) ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 1)
            (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)))
          (qS Zp Np).par 0 2852142980
          (Desc.K14.Law.Sh.rank (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
          (Desc.K14.Law.heldFull (qS Zp Np).par 0 (qS Zp Np).par.S.fold.index.saltBytes
            (Desc.K14.Law.full_index (qS Zp Np).par.S
              (Desc.K14.Law.full_of_shape hx
                (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx).shape))
            OnBytes.Flat.numsFull pp E)
          (fun s : St => s.st)
          (fun s : St => shiftBook
            (tiedNumbers N₁
              (Desc.K14.Law.Fence.numbersSh
                (Desc.K14.Law.Sh.t₁
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                (Desc.K14.Law.Sh.layU
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                (Desc.K14.Law.Sh.layO
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                (0, 0) (0, 0))).lo
            s.book)
          (pmZ (qS Zp Np).par Desc.K14.Law.Sh.idleP))
        (qS Zp Np).S.fold.columns 0 (qS Zp Np).codes
        (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        (msSh (qS Zp Np).S ((Desc.K14.Law.rad2At 2 (qS Zp Np)) 0)
          ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 0) ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 1)
          (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
          (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
          (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)))
        (tiedNumbers N₁
          (Desc.K14.Law.Fence.numbersSh
            (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (0, 0) (0, 0)))
        (ocWith
          (ocEnd get N₁ Mg₁ links (VerifiableInference.Desc.First.flatPlaces true links true))
          Rend)
        (oNoSh
          (Desc.K14.Law.Sh.sentU
            (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)).size)
        (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        ((tS Tok σ₁ Dw oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np c₁ k₁ c₂ k₂ c₃
            k₃ pp E e₁ e₂ e₃ dW wEnd).p₂)
        _ (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) x10 TF.alike TF.place.early TF.place.answers a τ b ha
        hout)
    (tests := VerifiableInference.Desc.K12.Seat.tests Np) (hpA := NF.place.planOk)
    (hrd := fun z m part i => Fence.rdK_tabP (qS Zp Np).codes z m part i)
    (hG := told_of_retype (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        Zp.p.chains (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np)
        VerifiableInference.Desc.K12.Seat.last rfl)
    (hloG := rfl)
    (hN := show
        (tiedNumbers N₁
          (Desc.K14.Law.Fence.numbersSh
            (Desc.K14.Law.Sh.t₁
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (Desc.K14.Law.Sh.layU
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (Desc.K14.Law.Sh.layO
              (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (0, 0) (0, 0))).tenant
        = tenantSh
        (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)) from
        Desc.K14.Law.Sh.paid_hN (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        (oS P₀ Tok σ₁ Dw get ms₁ N₁ links Zp x hx Rend oL Zs rP hZs hlaid Np smp₁ pp E Mg₁ hpub
          hpinS hpinF))
    (hdG := Fence.depth_of_planOk (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        fileN Dw hGp hDw Dw.key₂ 0)
    (hFU :=
        (Second.Seam.seatFits_of_told _ (qS Zp Np) _ _ _ Zp.p.chains
          (VerifiableInference.Desc.K12.Seat.tests Np) VerifiableInference.Desc.K12.Seat.last
          (Desc.K14.Law.Sh.tests_hUw
            (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
            (Desc.K14.Law.Sh.tests_at hx
              (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
              (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
              (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                startS cF _ _ _ hGp)))
          rfl
          (told_of_retype _ Zp.p.chains (qS Zp Np)
            (VerifiableInference.Desc.K12.Seat.tests Np)
            VerifiableInference.Desc.K12.Seat.last rfl)
          hBt ((Desc.K14.Law.rad2At 2 (qS Zp Np)) 0) ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 0)
          ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 1)).1)
    (hFO :=
        (Second.Seam.seatFits_of_told _ (qS Zp Np) _ _ _ Zp.p.chains
          (VerifiableInference.Desc.K12.Seat.tests Np) VerifiableInference.Desc.K12.Seat.last
          (Desc.K14.Law.Sh.tests_hUw
            (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
            (Desc.K14.Law.Sh.tests_at hx
              (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
              (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
              (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                startS cF _ _ _ hGp)))
          rfl
          (told_of_retype _ Zp.p.chains (qS Zp Np)
            (VerifiableInference.Desc.K12.Seat.tests Np)
            VerifiableInference.Desc.K12.Seat.last rfl)
          hBt ((Desc.K14.Law.rad2At 2 (qS Zp Np)) 0) ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 0)
          ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 1)).2)
    (hB9 := fun m => sentBefore (qS Zp Np)
        (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 0)
        (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 1)
        (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 2)
        (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 3)
        (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 4)
        (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 5)
        (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 6)
        (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 7)
        (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.tests_hbl8 (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
          (Desc.K14.Law.Sh.tests_at hx
            (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
            (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
              (VerifiableInference.Desc.K12.Seat.tests Np))
            (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
              _ _ _ hGp)))
        (Desc.K14.Law.Sh.tests_hUw (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
          (Desc.K14.Law.Sh.tests_at hx
            (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
            (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
              (VerifiableInference.Desc.K12.Seat.tests Np))
            (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
              _ _ _ hGp)))
        (Desc.K14.Law.Sh.tests_hlU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
          (Desc.K14.Law.Sh.tests_at hx
            (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
            (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
              (VerifiableInference.Desc.K12.Seat.tests Np))
            (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
              _ _ _ hGp)))
        (Desc.K14.Law.Sh.tests_hlO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
          (Desc.K14.Law.Sh.tests_at hx
            (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
            (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
              (VerifiableInference.Desc.K12.Seat.tests Np))
            (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
              _ _ _ hGp)))
        (by
          rw
              [sizeU (qS Zp Np).S
                (Desc.K14.Law.Sh.sentU
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                (Desc.K14.Law.Sh.tests_hUw
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                  (Desc.K14.Law.Sh.tests_at hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                    (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                      (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                    (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                      startS cF _ _ _ hGp)))
                (Desc.K14.Law.Sh.tests_hm
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                  (Desc.K14.Law.Sh.tests_at hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                    (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                      (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                    (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                      startS cF _ _ _ hGp)))]
          decide)
        (by
          rw
              [sizeOmega (qS Zp Np).S
                (Desc.K14.Law.Sh.tests_hS
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                  (Desc.K14.Law.Sh.tests_at hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                    (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                      (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                    (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                      startS cF _ _ _ hGp)))]
          decide)
        (ckP .two) _ _ _ _ _ _ (VerifiableInference.Desc.numAt Dw.t₁ Dw.t₂ 1)
        (tiedNumbers N₁
          (Desc.K14.Law.Fence.numbersSh
            (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (0, 0) (0, 0)))
        ((tS Tok σ₁ Dw oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np c₁ k₁ c₂ k₂ c₃
            k₃ pp E e₁ e₂ e₃ dW wEnd).p₂)
        _ _ _ _ _ _ _ hN' hNlo htF hf0 halS 9 x9 (by decide) rfl m)
    (hTU := Desc.K14.Law.Sh.tests_hTU
        (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        (Desc.K14.Law.Sh.tests_at hx
          (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
          (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
            (VerifiableInference.Desc.K12.Seat.tests Np))
          (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _
            _ hGp)))
    (hTS := Desc.K14.Law.Sh.tests_hTS
        (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        (Desc.K14.Law.Sh.tests_at hx
          (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
          (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
            (VerifiableInference.Desc.K12.Seat.tests Np))
          (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _
            _ hGp)))
    (hmU := memAt (qS Zp Np).S ((Desc.K14.Law.rad2At 2 (qS Zp Np)) 0)
        ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 0) ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 1)
        (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)).size
        (by
          rw
              [sizeU (qS Zp Np).S
                (Desc.K14.Law.Sh.sentU
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                (Desc.K14.Law.Sh.tests_hUw
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                  (Desc.K14.Law.Sh.tests_at hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                    (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                      (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                    (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                      startS cF _ _ _ hGp)))
                (Desc.K14.Law.Sh.tests_hm
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                  (Desc.K14.Law.Sh.tests_at hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                    (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                      (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                    (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                      startS cF _ _ _ hGp)))]
          decide)
        .oU)
    (hmSp := memAt (qS Zp Np).S ((Desc.K14.Law.rad2At 2 (qS Zp Np)) 0)
        ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 0) ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 1)
        (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)).size
        (by
          rw
              [sizeU (qS Zp Np).S
                (Desc.K14.Law.Sh.sentU
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                (Desc.K14.Law.Sh.tests_hUw
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                  (Desc.K14.Law.Sh.tests_at hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                    (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                      (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                    (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                      startS cF _ _ _ hGp)))
                (Desc.K14.Law.Sh.tests_hm
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                  (Desc.K14.Law.Sh.tests_at hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                    (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                      (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                    (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                      startS cF _ _ _ hGp)))]
          decide)
        .oSp)
    (fU9 := Desc.K14.Law.Sh.tests_fU9
        (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        (Desc.K14.Law.Sh.tests_at hx
          (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
          (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
            (VerifiableInference.Desc.K12.Seat.tests Np))
          (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _
            _ hGp)))
    (fSp9 := fSp9)
    (hfit9 :=
        (hfit_at_seat hx
          (Desc.K14.Law.seat_radii_terms hx
            (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp)
          (show (qS Zp Np).S = x.shape from
            (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx).shape)
          (show (qS Zp Np).codes = Johnson.G.codesFull2 from
            (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx).codes)
          tA tB).1)
    (hYc9 := ?_) (hjB := TF.joh) (hpB := TF.place.planOk)
    (hB10 := fun m => sentBefore (qS Zp Np)
        (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 0)
        (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 1)
        (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 2)
        (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 3)
        (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 4)
        (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 5)
        (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 6)
        (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 7)
        (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.tests_hbl8 (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
          (Desc.K14.Law.Sh.tests_at hx
            (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
            (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
              (VerifiableInference.Desc.K12.Seat.tests Np))
            (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
              _ _ _ hGp)))
        (Desc.K14.Law.Sh.tests_hUw (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
          (Desc.K14.Law.Sh.tests_at hx
            (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
            (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
              (VerifiableInference.Desc.K12.Seat.tests Np))
            (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
              _ _ _ hGp)))
        (Desc.K14.Law.Sh.tests_hlU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
          (Desc.K14.Law.Sh.tests_at hx
            (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
            (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
              (VerifiableInference.Desc.K12.Seat.tests Np))
            (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
              _ _ _ hGp)))
        (Desc.K14.Law.Sh.tests_hlO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
          (Desc.K14.Law.Sh.tests_at hx
            (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
            (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
              (VerifiableInference.Desc.K12.Seat.tests Np))
            (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
              _ _ _ hGp)))
        (by
          rw
              [sizeU (qS Zp Np).S
                (Desc.K14.Law.Sh.sentU
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                (Desc.K14.Law.Sh.tests_hUw
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                  (Desc.K14.Law.Sh.tests_at hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                    (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                      (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                    (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                      startS cF _ _ _ hGp)))
                (Desc.K14.Law.Sh.tests_hm
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                  (Desc.K14.Law.Sh.tests_at hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                    (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                      (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                    (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                      startS cF _ _ _ hGp)))]
          decide)
        (by
          rw
              [sizeOmega (qS Zp Np).S
                (Desc.K14.Law.Sh.tests_hS
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                  (Desc.K14.Law.Sh.tests_at hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                    (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                      (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                    (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                      startS cF _ _ _ hGp)))]
          decide)
        (ckP .two) _ _ _ _ _ _ (VerifiableInference.Desc.numAt Dw.t₁ Dw.t₂ 1)
        (tiedNumbers N₁
          (Desc.K14.Law.Fence.numbersSh
            (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
            (0, 0) (0, 0)))
        ((tS Tok σ₁ Dw oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np c₁ k₁ c₂ k₂ c₃
            k₃ pp E e₁ e₂ e₃ dW wEnd).p₂)
        _ _ _ _ _ _ _ hN' hNlo htF hf0 halS 10 x10 (by decide) rfl m)
    (hTO := Desc.K14.Law.Sh.tests_hTO
        (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        (Desc.K14.Law.Sh.tests_at hx
          (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
          (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
            (VerifiableInference.Desc.K12.Seat.tests Np))
          (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _
            _ hGp)))
    (hmO := memAt (qS Zp Np).S ((Desc.K14.Law.rad2At 2 (qS Zp Np)) 0)
        ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 0) ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 1)
        (Desc.K14.Law.Sh.t₁ (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
        (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)).size
        (by
          rw
              [sizeU (qS Zp Np).S
                (Desc.K14.Law.Sh.sentU
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
                (Desc.K14.Law.Sh.tests_hUw
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                  (Desc.K14.Law.Sh.tests_at hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                    (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                      (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                    (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                      startS cF _ _ _ hGp)))
                (Desc.K14.Law.Sh.tests_hm
                  (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
                  (Desc.K14.Law.Sh.tests_at hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
                    (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
                      (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
                    (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
                      startS cF _ _ _ hGp)))]
          decide)
        .oOmega)
    (fO10 := Desc.K14.Law.Sh.tests_fO10
        (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        (Desc.K14.Law.Sh.tests_at hx
          (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
          (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
            (VerifiableInference.Desc.K12.Seat.tests Np))
          (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _
            _ hGp)))
    (fSp10 := fSp10)
    (hfit10 :=
        (hfit_at_seat hx
          (Desc.K14.Law.seat_radii_terms hx
            (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp)
          (show (qS Zp Np).S = x.shape from
            (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx).shape)
          (show (qS Zp Np).codes = Johnson.G.codesFull2 from
            (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx).codes)
          tA tB).2)
    (hYc10 := ?_) (oH := oH) (mkL := mkL) (Zp := Zp) (lt := lt) (st₂ := st₂) (en₂ := en₂)
    (ok₂ := ok₂) (fo₂ := fo₂) (si₂ := si₂) (Bs := Bs) (getS := getS) (startS := startS) (cF := cF)
    (c₁ := c₁) (k₁ := k₁) (c₂ := c₂) (k₂ := k₂) (c₃ := c₃) (k₃ := k₃) (h₁f := h₁f) (h₂f := h₂f)
    (h₃f := h₃f) (e₁ := e₁) (e₂ := e₂) (e₃ := e₃) (dW := dW) (wEnd := wEnd) (fileN := fileN)
    (hDw := hDw) (hsl := hsl)
    (hloD :=
        (Desc.K14.Law.Fence.counts_of_planOk
          (gS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) fileN Dw hGp hDw).1)
    (hpf := rfl) (hlf := hlf)
  · intro m
    rw [hNlo]
    exact NUM.2.2.2.2.2.2 m
  · have key : ∀ (ds : List RDT) (e : Err (uLT (ckP .two) ds)), ds = dBA :: dtA → HEq e (((batV0
      (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ Np.U) H2K.Member.rUFull * (bsRound .two dBA.entry dBA.kind).w),
      errJ (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ Np.U) H2K.Member.rUFull dtA) : Err (uLT (ckP .two) (dBA ::
                          dtA))) → Err.Below e ((2 : ENNReal)⁻¹ ^ 128) := by
      intro ds e h he
      subst h
      rw [eq_of_heq he]
      exact NF.small
    exact key _ _ NF.ds (herr_ownFam (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ Np.U) H2K.Member.rUFull NF.ds)
  · have key : ∀ (ds : List RDT) (e : Err (uLT (ckP .two) ds)), ds = dBB :: dtB → HEq e (((batV0
      (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) H2K.Member.rOFull * (bsRound .two dBB.entry dBB.kind).w),
      errJ (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) H2K.Member.rOFull dtB) : Err (uLT (ckP .two) (dBB ::
                          dtB))) → Err.Below e ((2 : ENNReal)⁻¹ ^ 128) := by
      intro ds e h he
      subst h
      rw [eq_of_heq he]
      exact TF.small
    exact key _ _ TF.ds (herr_ownFam (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO) H2K.Member.rOFull TF.ds)
  · refine smpK_hands_paid (qS Zp Np) (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂
      Bs getS startS cF Np)) (Desc.K14.Law.Sh.layU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
      startS cF Np)) (Desc.K14.Law.Sh.layO (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
      Np)) (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 0)
      (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 1)
      (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 2)
      (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 3)
      (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 4)
      (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 5)
      (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 6)
      (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) 7)
      (Desc.K14.Law.Sh.tests_hbl8 (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
      (Desc.K14.Law.Sh.tests_at hx (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
      (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
      (VerifiableInference.Desc.K12.Seat.tests Np)) (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂
      en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _ _ hGp))) (Desc.K14.Law.Sh.tests_hUw (aS σ₁ oH mkL Zp lt
      st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) (Desc.K14.Law.Sh.tests_at hx
      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp (fieldF oH mkL Zp lt st₂ en₂
      ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
      (VerifiableInference.Desc.K12.Seat.tests Np)) (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂
      en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _ _ hGp))) ((Desc.K14.Law.Sh.tests_hp8 (aS σ₁ oH mkL Zp lt
      st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) (Desc.K14.Law.Sh.tests_at hx
      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp (fieldF oH mkL Zp lt st₂ en₂
      ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
      (VerifiableInference.Desc.K12.Seat.tests Np)) (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂
      en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _ _ hGp))) (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂
      ok₂ fo₂ si₂ Bs getS startS cF Np) 1) (by simp)) ((Desc.K14.Law.Sh.tests_hp8 (aS σ₁ oH mkL Zp
      lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) (Desc.K14.Law.Sh.tests_at hx
      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp (fieldF oH mkL Zp lt st₂ en₂
      ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
      (VerifiableInference.Desc.K12.Seat.tests Np)) (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂
      en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _ _ hGp))) (Desc.K14.Law.Sh.bk (aS σ₁ oH mkL Zp lt st₂ en₂
      ok₂ fo₂ si₂ Bs getS startS cF Np) 4) (by simp)) _ ((places (qS Zp Np) (Desc.K14.Law.Sh.sentU
      (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))).1 (Desc.K14.Law.Sh.tests_hUw
      (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) (Desc.K14.Law.Sh.tests_at hx
      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp (fieldF oH mkL Zp lt st₂ en₂
      ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
      (VerifiableInference.Desc.K12.Seat.tests Np)) (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂
      en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _ _ hGp)))) ((sampled (qS Zp Np) (Desc.K14.Law.Sh.sentU
      (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)) (Desc.K14.Law.Sh.tests_hok (aS
      σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) (Desc.K14.Law.Sh.tests_at hx
      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp (fieldF oH mkL Zp lt st₂ en₂
      ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
      (VerifiableInference.Desc.K12.Seat.tests Np)) (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂
      en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _ _ hGp)))).1 (Desc.K14.Law.Sh.tests_hUw (aS σ₁ oH mkL Zp
      lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) (Desc.K14.Law.Sh.tests_at hx
      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp (fieldF oH mkL Zp lt st₂ en₂
      ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
      (VerifiableInference.Desc.K12.Seat.tests Np)) (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂
      en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _ _ hGp))) ((places (qS Zp Np) (Desc.K14.Law.Sh.sentU (aS
      σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))).1 (Desc.K14.Law.Sh.tests_hUw (aS
      σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) (Desc.K14.Law.Sh.tests_at hx
      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp (fieldF oH mkL Zp lt st₂ en₂
      ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
      (VerifiableInference.Desc.K12.Seat.tests Np)) (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂
      en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _ _ hGp))))) ((places (qS Zp Np) (Desc.K14.Law.Sh.sentU
      (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))).2.1) ((sampled (qS Zp Np)
      (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))
      (Desc.K14.Law.Sh.tests_hok (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
      (Desc.K14.Law.Sh.tests_at hx (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
      (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
      (VerifiableInference.Desc.K12.Seat.tests Np)) (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂
      en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _ _ hGp)))).2.1 (places (qS Zp Np) (Desc.K14.Law.Sh.sentU
      (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))).2.1) ((places (qS Zp Np)
      (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))).2.2
      (Desc.K14.Law.Sh.tests_hS (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
      (Desc.K14.Law.Sh.tests_at hx (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
      (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
      (VerifiableInference.Desc.K12.Seat.tests Np)) (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂
      en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _ _ hGp)))) ((sampled (qS Zp Np) (Desc.K14.Law.Sh.sentU
      (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)) (Desc.K14.Law.Sh.tests_hok (aS
      σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) (Desc.K14.Law.Sh.tests_at hx
      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp (fieldF oH mkL Zp lt st₂ en₂
      ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
      (VerifiableInference.Desc.K12.Seat.tests Np)) (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂
      en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _ _ hGp)))).2.2 ((places (qS Zp Np) (Desc.K14.Law.Sh.sentU
      (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))).2.2 (Desc.K14.Law.Sh.tests_hS
      (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) (Desc.K14.Law.Sh.tests_at hx
      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp (fieldF oH mkL Zp lt st₂ en₂
      ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
      (VerifiableInference.Desc.K12.Seat.tests Np)) (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂
      en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _ _ hGp))))) (Desc.K14.Law.rad2At 2 (qS Zp Np))
      (Desc.K14.Law.rad5At 2 (qS Zp Np)) (Desc.K14.Law.Sh.tests_hC2 (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂
      fo₂ si₂ Bs getS startS cF Np) (Desc.K14.Law.Sh.tests_at hx (Desc.K14.Law.written_in_scope hZs
      hpub hpinS hpinF hlaid hx) hNp (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
      (Zp.p.chains) (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
      (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _ _
      hGp))) (Desc.K14.Law.Sh.tests_hC5 (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
      Np) (Desc.K14.Law.Sh.tests_at hx (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx)
      hNp (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
      (VerifiableInference.Desc.K12.Seat.tests Np)) (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂
      en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _ _ hGp))) ((Desc.K14.Law.Sh.shapes_are (aS σ₁ oH mkL Zp
      lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) (Desc.K14.Law.Sh.tests_hUw (aS σ₁ oH mkL Zp lt
      st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) (Desc.K14.Law.Sh.tests_at hx
      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp (fieldF oH mkL Zp lt st₂ en₂
      ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
      (VerifiableInference.Desc.K12.Seat.tests Np)) (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂
      en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _ _ hGp))) (Desc.K14.Law.Sh.tests_hS (aS σ₁ oH mkL Zp lt
      st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) (Desc.K14.Law.Sh.tests_at hx
      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp (fieldF oH mkL Zp lt st₂ en₂
      ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
      (VerifiableInference.Desc.K12.Seat.tests Np)) (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂
      en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _ _ hGp)))).1.symm ▸ Desc.K14.Law.Sh.tests_pyU (aS σ₁ oH
      mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) (Desc.K14.Law.Sh.tests_at hx
      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp (fieldF oH mkL Zp lt st₂ en₂
      ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
      (VerifiableInference.Desc.K12.Seat.tests Np)) (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂
      en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _ _ hGp))) ((Desc.K14.Law.Sh.shapes_are (aS σ₁ oH mkL Zp
      lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) (Desc.K14.Law.Sh.tests_hUw (aS σ₁ oH mkL Zp lt
      st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) (Desc.K14.Law.Sh.tests_at hx
      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp (fieldF oH mkL Zp lt st₂ en₂
      ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
      (VerifiableInference.Desc.K12.Seat.tests Np)) (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂
      en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _ _ hGp))) (Desc.K14.Law.Sh.tests_hS (aS σ₁ oH mkL Zp lt
      st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) (Desc.K14.Law.Sh.tests_at hx
      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp (fieldF oH mkL Zp lt st₂ en₂
      ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
      (VerifiableInference.Desc.K12.Seat.tests Np)) (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂
      en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _ _ hGp)))).2.1.symm ▸ Desc.K14.Law.Sh.tests_pyO (aS σ₁ oH
      mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) (Desc.K14.Law.Sh.tests_at hx
      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp (fieldF oH mkL Zp lt st₂ en₂
      ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
      (VerifiableInference.Desc.K12.Seat.tests Np)) (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂
      en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _ _ hGp))) ((Desc.K14.Law.Sh.shapes_are (aS σ₁ oH mkL Zp
      lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) (Desc.K14.Law.Sh.tests_hUw (aS σ₁ oH mkL Zp lt
      st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) (Desc.K14.Law.Sh.tests_at hx
      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp (fieldF oH mkL Zp lt st₂ en₂
      ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
      (VerifiableInference.Desc.K12.Seat.tests Np)) (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂
      en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _ _ hGp))) (Desc.K14.Law.Sh.tests_hS (aS σ₁ oH mkL Zp lt
      st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) (Desc.K14.Law.Sh.tests_at hx
      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp (fieldF oH mkL Zp lt st₂ en₂
      ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
      (VerifiableInference.Desc.K12.Seat.tests Np)) (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂
      en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _ _ hGp)))).2.2.symm ▸ Desc.K14.Law.Sh.tests_pyS (aS σ₁ oH
      mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) (Desc.K14.Law.Sh.tests_at hx
      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp (fieldF oH mkL Zp lt st₂ en₂
      ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
      (VerifiableInference.Desc.K12.Seat.tests Np)) (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂
      en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _ _ hGp))) fun k a ha => ?_
    rw [pmK_is] at ha
    obtain ⟨z1, _, z3, _⟩ := beside_of_on _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ k a ha
    simp [XK, z1, z3]
  · intro s h
    have k := smpK_nine_says_paid (qS Zp Np) (shapeAt (parU (qS Zp Np) (Desc.K14.Law.Sh.sentU (aS σ₁
        oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))) ⟨0, (places (qS Zp Np)
        (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))).1
        (Desc.K14.Law.Sh.tests_hUw (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        (Desc.K14.Law.Sh.tests_at hx (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx)
        hNp (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
        (VerifiableInference.Desc.K12.Seat.tests Np)) (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt
        st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _ _ hGp)))⟩) (shapeAt (parO (qS Zp Np)) ⟨0, (places
        (qS Zp Np) (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
        Np))).2.1⟩) (shapeAt (parO (qS Zp Np)) ⟨1, (places (qS Zp Np) (Desc.K14.Law.Sh.sentU (aS σ₁
        oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))).2.2 (Desc.K14.Law.Sh.tests_hS (aS
        σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) (Desc.K14.Law.Sh.tests_at hx
        (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp (fieldF oH mkL Zp lt st₂
        en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
        (VerifiableInference.Desc.K12.Seat.tests Np)) (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt
        st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _ _ hGp)))⟩) (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp
        lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)) s h
    rw [(shapeAtU (qS Zp Np) (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
        startS cF Np)) (Desc.K14.Law.Sh.tests_hUw (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
        startS cF Np) (Desc.K14.Law.Sh.tests_at hx (Desc.K14.Law.written_in_scope hZs hpub hpinS
        hpinF hlaid hx) hNp (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
        (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np)) (Desc.K14.Law.Sh.chainOk_descAt oH
        mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _ _ hGp))) _ : shapeAt (parU (qS Zp Np)
        (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))) ⟨0,
        (places (qS Zp Np) (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
        startS cF Np))).1 (Desc.K14.Law.Sh.tests_hUw (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
        startS cF Np) (Desc.K14.Law.Sh.tests_at hx (Desc.K14.Law.written_in_scope hZs hpub hpinS
        hpinF hlaid hx) hNp (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains)
        (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np)) (Desc.K14.Law.Sh.chainOk_descAt oH
        mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _ _ hGp)))⟩ = (qS Zp Np).S.fold.u),
        (shapeAt_of (k := ⟨1, (places (qS Zp Np) (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂
        ok₂ fo₂ si₂ Bs getS startS cF Np))).2.2 (Desc.K14.Law.Sh.tests_hS (aS σ₁ oH mkL Zp lt st₂
        en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) (Desc.K14.Law.Sh.tests_at hx
        (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp (fieldF oH mkL Zp lt st₂
        en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
        (VerifiableInference.Desc.K12.Seat.tests Np)) (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt
        st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _ _ hGp)))⟩) (o1 (qS Zp Np) "o_omega and o_sp"
        ((places (qS Zp Np) (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
        startS cF Np))).2.2 (Desc.K14.Law.Sh.tests_hS (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs
        getS startS cF Np) (Desc.K14.Law.Sh.tests_at hx (Desc.K14.Law.written_in_scope hZs hpub
        hpinS hpinF hlaid hx) hNp (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
        (Zp.p.chains) (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
        (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _ _
        hGp))))) : shapeAt (parO (qS Zp Np)) ⟨1, (places (qS Zp Np) (Desc.K14.Law.Sh.sentU (aS σ₁ oH
        mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))).2.2 (Desc.K14.Law.Sh.tests_hS (aS σ₁
        oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) (Desc.K14.Law.Sh.tests_at hx
        (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp (fieldF oH mkL Zp lt st₂
        en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
        (VerifiableInference.Desc.K12.Seat.tests Np)) (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt
        st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _ _ hGp)))⟩ = (qS Zp Np).S.sharedSplit)] at k
    exact k
  · intro s h
    have k := smpK_ten_says_paid (qS Zp Np) (shapeAt (parU (qS Zp Np) (Desc.K14.Law.Sh.sentU (aS σ₁
        oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))) ⟨0, (places (qS Zp Np)
        (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))).1
        (Desc.K14.Law.Sh.tests_hUw (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)
        (Desc.K14.Law.Sh.tests_at hx (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx)
        hNp (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
        (VerifiableInference.Desc.K12.Seat.tests Np)) (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt
        st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _ _ hGp)))⟩) (shapeAt (parO (qS Zp Np)) ⟨0, (places
        (qS Zp Np) (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
        Np))).2.1⟩) (shapeAt (parO (qS Zp Np)) ⟨1, (places (qS Zp Np) (Desc.K14.Law.Sh.sentU (aS σ₁
        oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))).2.2 (Desc.K14.Law.Sh.tests_hS (aS
        σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) (Desc.K14.Law.Sh.tests_at hx
        (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp (fieldF oH mkL Zp lt st₂
        en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
        (VerifiableInference.Desc.K12.Seat.tests Np)) (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt
        st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _ _ hGp)))⟩) (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp
        lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np)) s h
    rw [(shapeAt_of (k := ⟨0, (places (qS Zp Np) (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂
        ok₂ fo₂ si₂ Bs getS startS cF Np))).2.1⟩) (o0 (qS Zp Np) "o_omega and o_sp") : shapeAt (parO
        (qS Zp Np)) ⟨0, (places (qS Zp Np) (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂
        fo₂ si₂ Bs getS startS cF Np))).2.1⟩ = (qS Zp Np).S.omega), (shapeAt_of (k := ⟨1, (places
        (qS Zp Np) (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
        Np))).2.2 (Desc.K14.Law.Sh.tests_hS (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS
        cF Np) (Desc.K14.Law.Sh.tests_at hx (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF
        hlaid hx) hNp (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS
        Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np)) (Desc.K14.Law.Sh.chainOk_descAt oH mkL
        Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _ _ hGp)))⟩) (o1 (qS Zp Np) "o_omega and o_sp"
        ((places (qS Zp Np) (Desc.K14.Law.Sh.sentU (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS
        startS cF Np))).2.2 (Desc.K14.Law.Sh.tests_hS (aS σ₁ oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs
        getS startS cF Np) (Desc.K14.Law.Sh.tests_at hx (Desc.K14.Law.written_in_scope hZs hpub
        hpinS hpinF hlaid hx) hNp (fieldF oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF
        (Zp.p.chains) (qS Zp Np) (VerifiableInference.Desc.K12.Seat.tests Np))
        (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _ _
        hGp))))) : shapeAt (parO (qS Zp Np)) ⟨1, (places (qS Zp Np) (Desc.K14.Law.Sh.sentU (aS σ₁ oH
        mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np))).2.2 (Desc.K14.Law.Sh.tests_hS (aS σ₁
        oH mkL Zp lt st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF Np) (Desc.K14.Law.Sh.tests_at hx
        (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp (fieldF oH mkL Zp lt st₂
        en₂ ok₂ fo₂ si₂ Bs getS startS cF (Zp.p.chains) (qS Zp Np)
        (VerifiableInference.Desc.K12.Seat.tests Np)) (Desc.K14.Law.Sh.chainOk_descAt oH mkL Zp lt
        st₂ en₂ ok₂ fo₂ si₂ Bs getS startS cF _ _ _ hGp)))⟩ = (qS Zp Np).S.sharedSplit)] at k
    exact k

end Desc.K14.Law

#print axioms Desc.K14.Law.ledger_field_laid
