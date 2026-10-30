-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AT ANY FILLING: the prover H, the Script Q, the book Bk and the thread's other letters are variables.
Johnson/Desc/ProofFile/Honest/K3/Term/LookupExchangeFromWitnessFacts.lean: the honest side of the kind
"lookup" (K3): CONDITIONAL: from eleven premises, each under a name, to the shares of the debt
`ExchangeS` (Honest/Thread/PaysS.lean) at the fifty borders in front of a lookup. IT MOVES DEBTS
UNDER NAMES AND PAYS HALF OF THE BUNDLES' CLAUSES; IT DOES NOT SHOW THE DEBT.

The bundles of premises "that speak of a run": `DigitsRunFactsFromSaid`
(Honest/K3/Term/DigitsExchangeFromSaid.lean; thirteen clauses) and `CallsRunHead`
(Honest/K3/Law/Thread/ExchangeOpensCallsAtHead.lean; twelve).
SHOWN, here or beneath, from the head, `ThrS` at a Said that gives `SaidOk`, and the step:
  3 to 7, 10  on the verifier's state behind the step: `verifierStateBehindDigitsLookup`,
              `verifierStateBehindCallsLookup` (Honest/K3/Term/VerifierStateBehindLookup.lean)
  (digits)    two planes or more: `planes_site`
  planesOk    at the calls: `planesOkAtCallsSites` (the same file)
RE-NAMED, NOT SHOWN: each is a premise of every theorem here:
  1, 2   the ask is settled; the relation after the challenge: `LookupDataHoldsAtValidInputs`: on the
         input alone; spent at the thread's own clause "the input is valid". AT A LETTER Vd THAT LETS
         ONE INPUT BY AT WHICH THE ROW's DATA ARE NOT LAWFUL IT IS FALSE, and every theorem here is
         then empty
  8, 9   the book's two tests: `BookLendsTheMaskRowAtEverySite`: on public data
  11     the sender lays the mask row: by `senderLaysFromScript`
         (Honest/K3/Term/MaskRowFromScript.lean) from `ScriptLaysEveryLinksMaskRow`, on the Script, with
         hEnough, and `MaskRowReaderStands`, on the verifier's state behind the step
  12     the premises at one witness: `DigitsWitnessFacts`, `CallsWitnessFacts`
and beside the bundles: hSeat (`SiteRest`) and hHead (`HeadReturns`), on the prover's list and the
thread; hSaid.

  `inputAndChallengesBehindTheStep`             what a play leaves of the input and the challenges
  `digitsRunFactsHold`, `callsRunFactsHold`     the two bundles, from the named premises
  `lookupExchangeSharesFromWitnessFacts`        the shares at the items that a lookup's row OPENS (175
                                                of the 313 that the fifty rows owe), in the form of
                                                the gathering's binder
  `lookupExchangeOfSharesAndWhatIsOwedAgain`    from such shares, `BehindS` and `RidesPastAtS` at what
                                                the row reads and owes again: `ExchangeS` at one border

Limits. Implications from `ThrS` and the member's step: no state is shown to meet these at any of the
fifty borders: there every theorem here holds emptily. That the premises can hold together is shown
nowhere. No theorem here ends in `ExchangeS` at all fifty. The elder row `proverSideOfLookupInChainAtOneOwner`. The full size
alone. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.DigitsExchangeFromSaid
import Johnson.Desc.ProofFile.Honest.K3.Term.VerifierStateBehindLookup
import Johnson.Desc.ProofFile.Honest.K3.Term.MaskRowFromScript

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open OnBytes (E zeroE)
open OnBytes.Model (HTailF2)
open VerifiableInference.Desc (Block Chain FileDescription Place KindName Strs Wit)
open VerifiableInference.Desc.First (ModelPart shift)
open VerifiableInference.Desc.First.Look (Sent digAt planesOk)
open VerifiableInference.Desc.K9 (segAt? Readers formsIn)
open VerifiableInference.Desc.K9L (maskOracle)
open VerifiableInference.Desc.Sound (MsgT MsgQ dataQ tabQ seatTab)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS parts4)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)
open ProofFile.Honest.FirstThread (Letters lettersHead Script WtF)
open ProofFile.Honest.K3.Law
open ProofFile.Honest.K3.Law.AtThr
open ProofFile.Honest.K3.Law.Exchange

local notation "PlaceL" => VerifiableInference.Desc.First.Look.Place
local notation "PartK" => VerifiableInference.Desc.K9.Part
local notation "TableItem" => VerifiableInference.Desc.First.Item

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : PlaceL}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  {W₀' Rc' Xi' Tr' : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (cs : List (RiderCl (Local W₀ Rc ProofFile.Inst Tr) TS))
  (Kp : VerifiableInference.Desc.Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)

local notation "LH" =>
  lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w

/-! ## 1 The premises, by name -/

/-- **ON THE INPUT ALONE: at every valid input, at every lookup, what the row is handed is settled
behind the lookup's first round and meets the specification's relation after the challenge, at all
challenges.** Asked of whoever has the trace's laws. No coin, Script or state stands in it. A
definition, meant as a hypothesis. -/
def LookupDataHoldsAtValidInputs (Zp : ProofFile.Pub) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (wit : Site → Local W₀ Rc ProofFile.Inst Tr → Ask) : Prop :=
  ∀ t, Vd t → ∀ s ∈ lookSites Zp, Ask.Settled s.at_.base (wit s t) ∧
    ∀ heard ds, (siteData s (wit s t) heard ds).Mid

/-- **ON PUBLIC DATA: at every lookup the book's maker finds an owner of the link's mask row, and
the book passes the lookups' two tests at that owner and start.** The end of `k3Fits_at_atPure`
(AtFullSide/Honest/K3/FitsAtPure.lean) less its last clause, at a book Bk. A definition, meant as a
hypothesis. -/
def BookLendsTheMaskRowAtEverySite (Bk : ProverCoinCounts) (Zp : ProofFile.Pub) : Prop :=
  ∀ s ∈ lookSites Zp, ∃ r' : MsgAt,
    ProofFile.Honest.ownerOf maskRowRun WP.first.blocksInOrder proofSendsFull.1
      (WP.second.blocksInOrder.flatMap (·.rounds)) s!"link {s.link}, moment 0" isMaskRowMsg = some r' ∧
    bookFits Bk (Bk.rowsOf 0) (dueAt Bk.first) s.at_ = true ∧
    startsFit Bk s.at_ s.p.first r'.owner r'.base = true

/-- **ON THE VERIFIER's STATE BEHIND THE STEP: the reader of the segment's mask row stands**: the
frame's six facts (`ReaderAt`, Honest/Law/Rule/ReaderAt.lean) at the open segment's part, at the
message's number and up to the lookup's last slot. own: the seats that may be read, by the link. A
definition, meant as the end of a lemma. -/
def MaskRowReaderStands (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (s : Site) (own : Nat → List (Nat × Nat)) (messageNumber : Nat → Nat) : Prop :=
  ∀ blk, (LH).thread.bs[borderOf s.link s.digits]? = some blk → ∀ k st m En ds y cols st',
    ThrS (LH).thread Said (borderOf s.link s.digits) k st m En →
    drawsFit blk.rounds ds = true → (LH).thread.Stepped blk k st m En ds y cols st' →
    ∀ a : PartK, segAt? st' = some a →
      ReaderAt h.𝔇.cs h.𝔇.arr h.𝔇.ms (own s.link) a (messageNumber s.link)
        (s.p.first + s.at_.face.slots)

/-- **AT THE SCRIPT's WITNESS, at a lookup on the digits: the premises at one witness**
(`AtDigits`, Honest/K3/Law/Thread/ExchangeOuts.lean), at every step on the thread, at the open
segment's part behind it and at every continuation of the challenges. A definition, meant as the end
of a lemma. -/
def DigitsWitnessFacts (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (s : Site) (wit : Local W₀ Rc ProofFile.Inst Tr → Ask) (x : PlaceL) (tl : HTailF2) : Prop :=
  ∀ blk, (LH).thread.bs[borderOf s.link s.digits]? = some blk → ∀ k st m En ds y cols st',
    ThrS (LH).thread Said (borderOf s.link s.digits) k st m En →
    drawsFit blk.rounds ds = true → (LH).thread.Stepped blk k st m En ds y cols st' →
    ∀ a : PartK, segAt? st' = some a → ∀ ds',
      AtDigits s h.𝔇.sent h.𝔇.l3 x tl (wit m.st.input)
        (up (ptsOf s.at_.face s.at_.base (m.st.heard ++ ds)).theta) m.st.heard
        (dataQ (h.𝔇.N.group s.link) a
          (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms (Q.wit k m.st.input (m.st.heard ++ ds ++ ds')))).mask
        (Q.wit k m.st.input (m.st.heard ++ ds ++ ds'))

/-- **AT THE SCRIPT's WITNESS, at a lookup on the calls: the premises at one witness** (`AtCalls`,
Honest/K3/Law/Thread/ExchangeOpensCallsAtHead.lean), in the same binders. A definition, meant as the
end of a lemma. -/
def CallsWitnessFacts (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (s : Site) (wit : Local W₀ Rc ProofFile.Inst Tr → Ask) : Prop :=
  ∀ blk, (LH).thread.bs[borderOf s.link s.digits]? = some blk → ∀ k st m En ds y cols st',
    ThrS (LH).thread Said (borderOf s.link s.digits) k st m En →
    drawsFit blk.rounds ds = true → (LH).thread.Stepped blk k st m En ds y cols st' →
    ∀ a : PartK, segAt? st' = some a → ∀ ds',
      AtCalls h s m.st.input st' (wit m.st.input)
        (up (ptsOf s.at_.face s.at_.base (m.st.heard ++ ds)).theta) m.st.heard
        (dataQ (h.𝔇.N.sent s.link 0) a
          (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms (Q.wit k m.st.input (m.st.heard ++ ds ++ ds')))).mask
        (Q.wit k m.st.input (m.st.heard ++ ds ++ ds'))

/-! ## 2 The two bundles -/

/-- What a play leaves of the input and the challenges heard, off the member's step. -/
theorem inputAndChallengesBehindTheStep {blk : Block TS ProofFile.Cl} {k : Coins Bk}
    {st st' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {En : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    (hSt : (LH).thread.Stepped blk k st m En ds y cols st') :
    y.2.st.input = m.st.input ∧ y.2.st.heard = m.st.heard ++ ds := by
  have hS' := hSt
  unfold Thread.Stepped Thread.Moved at hS'
  obtain ⟨⟨⟨l, -, hy⟩, -⟩, -⟩ := hS'
  exact ⟨(play_mid _ _ _ _ _ hy).1, play_heard _ _ _ _ _ hy⟩

/-- **The digits' bundle holds.** Conditional on the head, the site, hSaid and the five named
premises. -/
theorem digitsRunFactsHold (s : Site) (hsite : s ∈ lookSites Zp) (hd : s.digits = true)
    {sub : ModelPart} (hsub : (LH).links[s.link]? = some sub) {x : PlaceL} {tl : HTailF2}
    (wit : Site → Local W₀ Rc ProofFile.Inst Tr → Ask)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    (hData : LookupDataHoldsAtValidInputs Zp Vd wit)
    (hBook : BookLendsTheMaskRowAtEverySite Bk Zp)
    (challengesInFront messageNumber : Nat → Nat)
    (hMaskRows : ScriptLaysEveryLinksMaskRow Q Vd Zp challengesInFront messageNumber)
    (hEnough : challengesInFront s.link ≤
      (LH).thread.front + roundsTo (LH).thread.bs (borderOf s.link s.digits))
    (hReader : MaskRowReaderStands h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w Said s h.𝔇.N.group
      messageNumber)
    (hWitness : DigitsWitnessFacts h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w Said s (wit s) x tl) :
    DigitsRunFactsFromSaid (LH) Said (borderOf s.link s.digits) s (wit s) h.𝔇.sent h.𝔇.l3 x tl
      h.𝔇.Rd h.𝔇.N.group (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) (6 + shift sub) := by
  intro blk hblk k st m En ds y cols st' hA hdr hSt
  have hv : Vd m.st.input :=
    (show m.st.input = w ∧ Vd m.st.input from hA.1.2.2.2.2.2.2).2
  obtain ⟨hSet, hMid⟩ := hData _ hv s hsite
  obtain ⟨a, o, h0, h1, h2, h3, h4, h7, _⟩ :=
    verifierStateBehindDigitsLookup h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w s hsite hd hsub Said
      hSaid blk hblk k st m En ds y cols st' hA hdr hSt
  obtain ⟨r', hr', h5, h6⟩ := hBook s hsite
  obtain ⟨ei, eh⟩ := inputAndChallengesBehindTheStep h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w hSt
  have hlen := (LH).thread.heard_length hA.1.2.1
  refine ⟨hSet, hMid _ _, planes_site Zp s hsite, a, r'.owner, r'.base, o, h0, h1, h2, h3, h4, h5,
    h6, h7, fun ds' => ?_, fun ds' => ?_⟩
  · rw [ei, eh]
    exact (senderLaysFromScript (hMaskRows s hsite r' hr')
      (hReader blk hblk k st m En ds y cols st' hA hdr hSt a h0) (Nat.le_refl _) h7 k
      (named_reads_site Bk k Zp s hsite r'.owner r'.base h5 h6) hv (by
        rw [List.length_append, List.length_append, hlen]
        omega)).1
  · rw [ei, eh]
    exact hWitness blk hblk k st m En ds y cols st' hA hdr hSt a h0 ds'

/-- **The calls' bundle holds.** Conditional on the head, the site, hSaid and the five named
premises. -/
theorem callsRunFactsHold (s : Site) (hsite : s ∈ lookSites Zp) (hd : s.digits = false)
    (wit : Site → Local W₀ Rc ProofFile.Inst Tr → Ask)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    (hData : LookupDataHoldsAtValidInputs Zp Vd wit)
    (hBook : BookLendsTheMaskRowAtEverySite Bk Zp)
    (challengesInFront messageNumber : Nat → Nat)
    (hMaskRows : ScriptLaysEveryLinksMaskRow Q Vd Zp challengesInFront messageNumber)
    (hEnough : challengesInFront s.link ≤
      (LH).thread.front + roundsTo (LH).thread.bs (borderOf s.link s.digits))
    (hReader : MaskRowReaderStands h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w Said s
      (fun i => h.𝔇.N.sent i 0) messageNumber)
    (hWitness : CallsWitnessFacts h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w Said s (wit s)) :
    CallsRunHead h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w Said s (wit s) := by
  intro sub hsub blk hblk k st m En ds y cols st' hA hdr hSt
  have hv : Vd m.st.input :=
    (show m.st.input = w ∧ Vd m.st.input from hA.1.2.2.2.2.2.2).2
  obtain ⟨hSet, hMid⟩ := hData _ hv s hsite
  obtain ⟨a, o, h0, h1, h2, h3, h4, h7, _⟩ :=
    verifierStateBehindCallsLookup h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w s hsite hd hsub Said
      hSaid blk hblk k st m En ds y cols st' hA hdr hSt
  obtain ⟨r', hr', h5, h6⟩ := hBook s hsite
  obtain ⟨ei, eh⟩ := inputAndChallengesBehindTheStep h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w hSt
  have hlen := (LH).thread.heard_length hA.1.2.1
  refine ⟨hSet, hMid _ _, a, r'.owner, r'.base, o, h0, h1, h2, h3, h4, h5, h6, h7,
    fun ds' => ?_, fun ds' => ?_⟩
  · rw [ei, eh]
    exact (senderLaysFromScript (hMaskRows s hsite r' hr')
      (hReader blk hblk k st m En ds y cols st' hA hdr hSt a h0) (Nat.le_refl _) h7 k
      (named_reads_site Bk k Zp s hsite r'.owner r'.base h5 h6) hv (by
        rw [List.length_append, List.length_append, hlen]
        omega)).1
  · rw [ei, eh]
    exact hWitness blk hblk k st m En ds y cols st' hA hdr hSt a h0 ds'

/-! ## 3 The exchange at all fifty -/

/-- **The shares of the exchange at every number of the kind K3, all fifty, in the form of the
gathering's binder.** Conditional on the head and on: hSaid; hSeat and hHead (the seat); hData (the
trace); hBook (public); hMaskRows (the Script) with hEnough; hReader (the state behind the step);
hDigits and hCalls (the Script's witness). The elder row. The full size alone. -/
theorem lookupExchangeSharesFromWitnessFacts (src : Sources W₀' Xi' Tr')
    (wit : Site → Local W₀ Rc ProofFile.Inst Tr → Ask)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said b k m → SaidOk b k m)
    (hSeat : ∀ s ∈ lookSites Zp, ∃ lot : Block TS ProofFile.Cl,
      SiteRest Zp cF H.first s lot ((fastFill (Rc := Rc') src).jobs s).asked (wit s))
    (hHead : ∀ s ∈ lookSites Zp, s.digits = true →
      HeadReturns (LH) (borderOf s.link s.digits) Zp s)
    (hData : LookupDataHoldsAtValidInputs Zp Vd wit)
    (hBook : BookLendsTheMaskRowAtEverySite Bk Zp)
    (challengesInFront messageNumber : Nat → Nat)
    (hMaskRows : ScriptLaysEveryLinksMaskRow Q Vd Zp challengesInFront messageNumber)
    (hEnough : ∀ s ∈ lookSites Zp, challengesInFront s.link ≤
      (LH).thread.front + roundsTo (LH).thread.bs (borderOf s.link s.digits))
    (hReaderDigits : ∀ s ∈ lookSites Zp, s.digits = true →
      MaskRowReaderStands h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w Said s h.𝔇.N.group
        messageNumber)
    (hReaderCalls : ∀ s ∈ lookSites Zp, s.digits = false →
      MaskRowReaderStands h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w Said s
        (fun i => h.𝔇.N.sent i 0) messageNumber)
    (hDigits : ∀ s ∈ lookSites Zp, s.digits = true → ∀ (x : PlaceL) (tl : HTailF2),
      digAt Zp.p.X s.link = some (x, tl) →
      DigitsWitnessFacts h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w Said s (wit s) x tl)
    (hCalls : ∀ s ∈ lookSites Zp, s.digits = false →
      CallsWitnessFacts h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w Said s (wit s)) :
    ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.K3 →
      ∀ j : TableItem, j ∈ ((LH).thread.row b).owes →
      (j ∈ (LH).thread.opened b →
        (∀ m t, j ≠ .pin m t) ∧ j ≠ .pinI ∧ j ≠ .pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ .constr m q) →
      ExchangeAtS (LH).thread Said b j :=
  lookupExchangeByKindFromSaid h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w src wit Said hSeat hHead
    (fun s hs hd _ x tl hsub hx =>
      digitsRunFactsHold h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w s hs hd hsub wit Said hSaid
        hData hBook challengesInFront messageNumber hMaskRows (hEnough s hs)
        (hReaderDigits s hs hd) (hDigits s hs hd x tl hx))
    (planesOkAtCallsSites h)
    (fun s hs hd =>
      callsRunFactsHold h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w s hs hd wit Said hSaid hData
        hBook challengesInFront messageNumber hMaskRows (hEnough s hs) (hReaderCalls s hs hd)
        (hCalls s hs hd))

/-- **From the shares to the debt whole.** What a lookup's row owes and has open in front (what it
reads and owes again) is carried by the frame's `exchangeAtS_again` from `BehindS` and
`RidesPastAtS` at that item; what it owes and has not open in front is a share. General in the
shares' source. -/
theorem lookupExchangeOfSharesAndWhatIsOwedAgain
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) {b : Nat}
    (hShares : ∀ j : TableItem, j ∈ ((LH).thread.row b).owes →
      (j ∈ (LH).thread.opened b →
        (∀ m t, j ≠ .pin m t) ∧ j ≠ .pinI ∧ j ≠ .pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ .constr m q) →
      ExchangeAtS (LH).thread Said b j)
    (hBehind : BehindS (LH).thread Said b)
    (hOwedAgain : ∀ j : TableItem, j ∈ ((LH).thread.row b).owes → j ∈ (LH).thread.opened b →
      RidesPastAtS (LH).thread Said b j) :
    ExchangeS (LH).thread Said b := by
  refine (exchangeS_iff (LH).thread Said).2 fun j hj => ?_
  by_cases ho : j ∈ (LH).thread.opened b
  · exact exchangeAtS_again (LH).thread Said ho hBehind (hOwedAgain j hj ho)
  · exact hShares j hj fun hc => absurd hc ho

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.inputAndChallengesBehindTheStep
#print axioms ProofFile.Honest.K3.Term.digitsRunFactsHold
#print axioms ProofFile.Honest.K3.Term.callsRunFactsHold
#print axioms ProofFile.Honest.K3.Term.lookupExchangeSharesFromWitnessFacts
#print axioms ProofFile.Honest.K3.Term.lookupExchangeOfSharesAndWhatIsOwedAgain
