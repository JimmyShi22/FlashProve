-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/TieAtStart.lean: THE FACTS ON A START (TieStart: eleven of the proof file's rows, none a law of a kind of block) AT THE SEATED DESCRIPTION's OWN TERM, AT THE CLOSED LETTERS (Johnson/P5J/LettersAt.lean) AND AT THE COMPOSED MEANING "mgAll 𝔇 Mg" (every kind's layer; the small list of extra public tests): NINE OF THE ELEVEN PAID; A WRITTEN STATEMENT. Five theorems.


  start_lawful: where Zp is the plain road's public part: a first state of the term that bears no mark IS the lawful first state (S.firstRecord codes shape layout).withReq ‹the request's words› at the first chain's own codes, shape and layout.
  order_at_start · items_at_start · says_at_start: the three fields on the first meaning at a first state without a mark, each with its statement written out. (WHY THEY ARE NAMED, AND WHY THE LAST THEOREM SAYS beta_reduce: the fields' types, at getS := fun s => s, hold the unreduced "(fun s => s) (start₁ …)"; where a term of the reduced form was laid in such a place Lean ran out of
    memory; with the redex reduced by name first it takes seconds. What Lean does there is not known to us: the place is.)
  tieStart_at_start: **TieStart AT: F₀ := F0T … · instP := the seated map · getS := id · reqB | asked := Johnson/P5J/AtTerm.lean's · DT := At.decT · cs | arr | ms | Nn | ps | smp := At.‹the same› · Gd := the seated description · Mg := mgLetter (At.𝔇At … 𝔇₀) Mg₀, FROM: hpub · fullShapeB · laidThere | SeatsNamed | GroupsSeated (they stand in 𝔇At's type) · THE BASE IS CLOSED
    (inOrder := true · more := {} · its own sentence holds at the two items open at the start) · scope_reads · scope_public.** 𝔇₀ (the fields of the structure of letters that are not closed) is free.
WHO ANSWERS WHAT THE FIRST BORDER READS: the head of Johnson/Desc/Sound/MgAt/Start.lean, item by item, at a version not held against what ships: "in order" is the base's own; two items are open at the start.

Limits. The full size alone. scope_reads | scope_public stay premises (the scope's own). What is cheap here is cheap rightly: the weight of these items lies in their keeping, block by block. NO MEMBER. Nothing on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.LettersRec
import Johnson.Desc.Sound.MgAt.Start

set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 400000

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
open Desc.K14 (St first p14Of beforePointOf)
open Desc.K14.Law (descZ secondAt fullShapeB full_index decShared decK heldFull rankLib hd_at_seat tp_by_make pw_by_make)

open VerifiableInference.Desc.K9 (Readers)
open VerifiableInference.Desc.First (flatPlacesOf frontPlace)

variable {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : Model.Verify.Public}
  (E : Coding (claimsReqAt (frS.toDecR frZ 402653181) numsFull pp)) (DP : WholeD)
  (o : ProofFile.SecondHashFunctionArgument) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
  (hs : fullShapeB (p14Of Zp.p.chains (beforePointOf Np)).par.S = true) 

/-- **A first state of the term without a mark is the lawful first state.** -/
theorem start_lawful {pol lay' KL : ByteArray} (hpub : ProofFile.pubPlain o pol lay' KL = .ok Zp)
    (p : (F0T o Zp Np cF).XiPub) (h : ((F0T o Zp Np cF).start₁ p : TS).failed = none) :
    (F0T o Zp Np cF).start₁ p =
      (VerifiableInference.Desc.First.S.firstRecord Zp.made.p.chains.proof.first.codes
        Zp.made.p.chains.proof.first.shape Zp.made.p.chains.proof.first.layout).withReq
        (OnBytes.Model.Verify.words32 (p : ProofFile.InstPub).request) := by
  have e : Zp.s₀ = VerifiableInference.Desc.First.S.firstRecord Zp.made.p.chains.proof.first.codes
      Zp.made.p.chains.proof.first.shape Zp.made.p.chains.proof.first.layout :=
    VerifiableInference.Desc.First.startP_is (pubBy_start hpub)
  have hs' : (F0T o Zp Np cF).start₁ p =
      (if ((Zp.s₀.withReq (OnBytes.Model.Verify.words32 (p : ProofFile.InstPub).request)).reqOk Zp.p.X.T
          Zp.p.X.P.h.V) = true
        then Zp.s₀.withReq (OnBytes.Model.Verify.words32 (p : ProofFile.InstPub).request)
        else VerifiableInference.Desc.First.S.blank) := rfl
  rw [hs'] at h ⊢
  by_cases hr : ((Zp.s₀.withReq (OnBytes.Model.Verify.words32 (p : ProofFile.InstPub).request)).reqOk Zp.p.X.T
      Zp.p.X.P.h.V) = true
  · rw [if_pos hr, e]
  · rw [if_neg hr] at h
    cases h

/-- **start_in_order at the term and the letters.** -/
theorem order_at_start {pol lay' KL : ByteArray} (hpub : ProofFile.pubPlain o pol lay' KL = .ok Zp)
    (hL : Meaning.laidThere (At.X Zp) (Meaning.sizesOf (At.X Zp)) (At.layout Zp) = true)
    (hN : SeatsNamed (At.arr Zp) (At.N Zp cF) (Meaning.sizesOf (At.X Zp))
      (Meaning.seatBy (Meaning.fLay (At.layout Zp) (At.num Zp)) (At.X Zp) (Meaning.sizesOf (At.X Zp))))
    (hG : GroupsSeated (At.ms Zp lay') (At.N Zp cF)) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp))
    (Mg₀ : VerifiableInference.Desc.First.Meaning ProofFile.InstPub (Wit (CellsM numsFull) At.Tok MsgT)) (b1 : Mg₀.inOrder = fun _ => true)
    (z : (kcReq numsFull pp E).conf.X × (kcReq numsFull pp E).conf.Rec)
    (hz : ((F0T o Zp Np cF).start₁ ((F0T o Zp Np cF).pub (LPFD.Full.instanceAsPlainRecord z)) : TS).failed = none) :
    (meaningSig (At.cs Zp) (F0T o Zp Np cF) (At.arr Zp) (At.smp Zp) (At.ms Zp lay') (At.decT o Zp Np cF E hs)
      (mgLetter (At.𝔇At o Zp Np cF E hs lay' hL hN hG 𝔇₀) Mg₀)).inOrder ((F0T o Zp Np cF).pub (LPFD.Full.instanceAsPlainRecord z), (F0T o Zp Np cF).start₁ ((F0T o Zp Np cF).pub (LPFD.Full.instanceAsPlainRecord z))) = true :=
  start_order (𝔇 := (At.𝔇At o Zp Np cF E hs lay' hL hN hG 𝔇₀)) b1 _

/-- **start_public_items at the term and the letters.** -/
theorem items_at_start {pol lay' KL : ByteArray} (hpub : ProofFile.pubPlain o pol lay' KL = .ok Zp)
    (hL : Meaning.laidThere (At.X Zp) (Meaning.sizesOf (At.X Zp)) (At.layout Zp) = true)
    (hN : SeatsNamed (At.arr Zp) (At.N Zp cF) (Meaning.sizesOf (At.X Zp))
      (Meaning.seatBy (Meaning.fLay (At.layout Zp) (At.num Zp)) (At.X Zp) (Meaning.sizesOf (At.X Zp))))
    (hG : GroupsSeated (At.ms Zp lay') (At.N Zp cF)) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp))
    (Mg₀ : VerifiableInference.Desc.First.Meaning ProofFile.InstPub (Wit (CellsM numsFull) At.Tok MsgT)) (b3 : Mg₀.more = {})
    (z : (kcReq numsFull pp E).conf.X × (kcReq numsFull pp E).conf.Rec)
    (hz : ((F0T o Zp Np cF).start₁ ((F0T o Zp Np cF).pub (LPFD.Full.instanceAsPlainRecord z)) : TS).failed = none) :
    ∀ q ∈ VerifiableInference.Desc.First.pubStartM (meaningSig (At.cs Zp) (F0T o Zp Np cF) (At.arr Zp) (At.smp Zp) (At.ms Zp lay') (At.decT o Zp Np cF E hs)
      (mgLetter (At.𝔇At o Zp Np cF E hs lay' hL hN hG 𝔇₀) Mg₀)).more,
      (meaningSig (At.cs Zp) (F0T o Zp Np cF) (At.arr Zp) (At.smp Zp) (At.ms Zp lay') (At.decT o Zp Np cF E hs)
      (mgLetter (At.𝔇At o Zp Np cF E hs lay' hL hN hG 𝔇₀) Mg₀)).pub q ((F0T o Zp Np cF).pub (LPFD.Full.instanceAsPlainRecord z), (F0T o Zp Np cF).start₁ ((F0T o Zp Np cF).pub (LPFD.Full.instanceAsPlainRecord z))) = true :=
  start_items_at (𝔇 := (At.𝔇At o Zp Np cF E hs lay' hL hN hG 𝔇₀)) b3 rfl _ _ _ _ _ _ (start_lawful o Zp Np cF hpub _ hz)

/-- **start_public_sentences at the term and the letters.** -/
theorem says_at_start {pol lay' KL : ByteArray} (hpub : ProofFile.pubPlain o pol lay' KL = .ok Zp)
    (hL : Meaning.laidThere (At.X Zp) (Meaning.sizesOf (At.X Zp)) (At.layout Zp) = true)
    (hN : SeatsNamed (At.arr Zp) (At.N Zp cF) (Meaning.sizesOf (At.X Zp))
      (Meaning.seatBy (Meaning.fLay (At.layout Zp) (At.num Zp)) (At.X Zp) (Meaning.sizesOf (At.X Zp))))
    (hG : GroupsSeated (At.ms Zp lay') (At.N Zp cF)) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp))
    (Mg₀ : VerifiableInference.Desc.First.Meaning ProofFile.InstPub (Wit (CellsM numsFull) At.Tok MsgT)) (b2 : ∀ a, Mg₀.pubP .unheard a ∧ Mg₀.pubP .noneSent a) (b3 : Mg₀.more = {})
    (z : (kcReq numsFull pp E).conf.X × (kcReq numsFull pp E).conf.Rec)
    (hz : ((F0T o Zp Np cF).start₁ ((F0T o Zp Np cF).pub (LPFD.Full.instanceAsPlainRecord z)) : TS).failed = none) :
    ∀ q ∈ VerifiableInference.Desc.First.pubStartM (meaningSig (At.cs Zp) (F0T o Zp Np cF) (At.arr Zp) (At.smp Zp) (At.ms Zp lay') (At.decT o Zp Np cF E hs)
      (mgLetter (At.𝔇At o Zp Np cF E hs lay' hL hN hG 𝔇₀) Mg₀)).more,
      (meaningSig (At.cs Zp) (F0T o Zp Np cF) (At.arr Zp) (At.smp Zp) (At.ms Zp lay') (At.decT o Zp Np cF E hs)
      (mgLetter (At.𝔇At o Zp Np cF E hs lay' hL hN hG 𝔇₀) Mg₀)).pubP q ((F0T o Zp Np cF).pub (LPFD.Full.instanceAsPlainRecord z), (F0T o Zp Np cF).start₁ ((F0T o Zp Np cF).pub (LPFD.Full.instanceAsPlainRecord z))) :=
  start_says (𝔇 := (At.𝔇At o Zp Np cF E hs lay' hL hN hG 𝔇₀)) b2 b3 _

/-- **THE FACTS ON A START, AT THE TERM, THE CLOSED LETTERS AND THE COMPOSED MEANING.** -/
theorem tieStart_at_start {pol lay' KL : ByteArray} (hpub : ProofFile.pubPlain o pol lay' KL = .ok Zp)
    (hL : Meaning.laidThere (At.X Zp) (Meaning.sizesOf (At.X Zp)) (At.layout Zp) = true)
    (hN : SeatsNamed (At.arr Zp) (At.N Zp cF) (Meaning.sizesOf (At.X Zp))
      (Meaning.seatBy (Meaning.fLay (At.layout Zp) (At.num Zp)) (At.X Zp) (Meaning.sizesOf (At.X Zp))))
    (hG : GroupsSeated (At.ms Zp lay') (At.N Zp cF)) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp))
    (Mg₀ : VerifiableInference.Desc.First.Meaning ProofFile.InstPub (Wit (CellsM numsFull) At.Tok MsgT)) (b1 : Mg₀.inOrder = fun _ => true) (b2 : ∀ a, Mg₀.pubP .unheard a ∧ Mg₀.pubP .noneSent a)
    (b3 : Mg₀.more = {}) (h1 : VerifierAndGoals.readFiles Z = .ok pp) (h2 : publicOf Z.pol Z.KL lay = .ok X) :
    TieStart (Z := Z) (lay := lay) (X := X) numsFull E DP (F0T o Zp Np cF) LPFD.Full.instanceAsPlainRecord (fun s => s)
      (fun q : ProofFile.InstPub => q.request) (dtK E o Zp Np cF hs 0) ProofFile.Inst.asked (At.cs Zp) (At.arr Zp)
      (At.ms Zp lay') (At.N Zp cF) (mgLetter (At.𝔇At o Zp Np cF E hs lay' hL hN hG 𝔇₀) Mg₀) At.ps (F0T o Zp Np cF) (At.smp Zp)
      Zp.made.p.chains.proof.first.codes (fun p : ProofFile.InstPub => OnBytes.Model.Verify.words32 p.request) :=
  tieStart_at_term (Z := Z) (lay := lay) (X := X) E DP o Zp Np cF hs 0 (At.cs Zp) (At.arr Zp) (At.ms Zp lay')
    (At.N Zp cF) (mgLetter (At.𝔇At o Zp Np cF E hs lay' hL hN hG 𝔇₀) Mg₀) At.ps (F0T o Zp Np cF) (At.smp Zp) hpub h1 h2 front_first_full
    (fun z hz => by
      beta_reduce at hz ⊢
      exact order_at_start E o Zp Np cF hs hpub hL hN hG 𝔇₀ Mg₀ b1 z hz)
    (fun z hz => by
      beta_reduce at hz ⊢
      exact items_at_start E o Zp Np cF hs hpub hL hN hG 𝔇₀ Mg₀ b3 z hz)
    (fun z hz => by
      beta_reduce at hz ⊢
      exact says_at_start E o Zp Np cF hs hpub hL hN hG 𝔇₀ Mg₀ b2 b3 z hz)
    (At.front_at Zp cF).1 (At.front_at Zp cF).2

end P5J

#print axioms P5J.start_lawful
#print axioms P5J.order_at_start
#print axioms P5J.items_at_start
#print axioms P5J.says_at_start
#print axioms P5J.tieStart_at_start
