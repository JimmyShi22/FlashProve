-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AT ANY FILLING: the prover H, the Script Q, the book Bk and the thread's other letters are
variables.
Johnson/Desc/ProofFile/Honest/K3/Term/DigitsExchangeFromSaid.lean: the honest side of the kind
"lookup" (K3): the exchange at the lookups on the digits, asked from `ThrS` (the invariant together
with the letter Said) in place of the invariant alone; and the top by kind with both bundles asked
from `ThrS`.

Why. `DigitsRunAll` (Honest/K3/Law/Thread/ExchangeDigitsAll.lean) binds every state at which the
invariant `Thr` holds. The library's facts "at reached states" are had from `ThrS` at `SaidOk`
(`thrS_reach_below`, Honest/Thread/ReachAtHead.lean), not from `Thr`: so whoever pays the bundle's
clauses on the verifier's state needs the weaker binder. The sister bundle at the calls
(`CallsRunAll`, ExchangeCallsAll.lean) has it already.

  `DigitsRunFactsFromSaid`            `DigitsRunAll`'s text with `ThrS L.thread Said b` for `Thr
  L.thread b`,
                                      and the clause "two planes or more"
  `digitsRunFactsFromSaidOfTheElderBundle`     `DigitsRunAll` gives `DigitsRunFactsFromSaid`
  `digitsRunFactsReadNoDefault`       under the bundle no coin that it names is read by default
  `digitsItemsHoldBehindTheStep`      at every step on the thread the three items hold behind it
  `digitsExchangeAtHeadLetters`       `ExchangeAtS` at each of the three, at the head's letters
  `digitsSharesAtHeadLetters`         in the form of the gathering's binder
  `lookupExchangeByKindFromSaid`      at all fifty borders, at the items that the row OPENS (175 of
  the
                                      313 that the fifty rows owe), both bundles from `ThrS`

Limits. A form; no new content: each proof is that of its fellow (`opens_digits_fast`,
`exchangeAt_headDigits`, `shares_headDigits`, `k3_exchange_by_kind`) with the invariant taken out of
the pair. The bundles are hypotheses: no file shows them. `HeadReturns` is still asked from `Thr`.
The elder row `proverSideOfLookupInChainAtOneOwner`. The full size alone. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeByKind
import Johnson.Desc.ProofFile.Honest.K3.Law.BookFence

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open OnBytes (E zeroE)
open OnBytes.Model (HTailF2)
open VerifiableInference.Desc (Block Chain FileDescription Place KindName Strs Wit)
open VerifiableInference.Desc.First (Item ModelPart shift)
open VerifiableInference.Desc.First.Look (Sent digAt planesOk)
open VerifiableInference.Desc.K9 (segAt? Readers formsIn)
open VerifiableInference.Desc.K9L (maskOracle)
open VerifiableInference.Desc.Sound (MsgT MsgQ dataQ tabQ seatTab digits_row)
open VerifiableInference.Desc.Sound.MgAt (borderOf places_are_k3)
open VerifiableInference.OnPublicFiles (K3At K3Letters)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS parts4)
open ProofFile.Honest.FirstThread (Letters lettersHead Script WtF)
open ProofFile.Honest.K3.Law
open ProofFile.Honest.K3.Law.AtThr
open ProofFile.Honest.K3.Law.Exchange

local notation "FS" => VerifiableInference.Desc.First.S
local notation "PlaceL" => VerifiableInference.Desc.First.Look.Place
local notation "PartK" => VerifiableInference.Desc.K9.Part
local notation "pieceOf" => VerifiableInference.Desc.K3.pieceAt

section general
variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr Xo P Cells Tok W₀' Rc' Xi' Tr' : Type} {D : Sent}
  {Lk : K3Letters Cells Tok} (L : Letters Bk ProofFile.Cl W₀ Rc Xi Tr Xo P Cells Tok MsgT)

/-- **The premises that speak of a run, at a lookup on the digits, asked from `ThrS`.**
`DigitsRunAll`'s text (Honest/K3/Law/Thread/ExchangeDigitsAll.lean) with one binder weakened: the
states bound are those at which the invariant holds together with Said. A definition, meant as a
hypothesis or as the end of a lemma; and with ONE CLAUSE MORE, the fence's third post: the face has
two planes or more. A coin is read by `getD … zeroE`. THE FENCE STANDS IN THIS DEFINITION WHOLE:
that
clause and the two tests `bookFits` and `startsFit` are all that `named_reads`
(Honest/K3/Law/BookFence.lean) asks: under them every index base.e + j with j below s.p.first +
s.at_.face.slots lies inside the owner's coins, so the default is never taken at an entry of which
`SenderLays` speaks here (`digitsRunFactsReadNoDefault`). -/
def DigitsRunFactsFromSaid (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) Xo → Prop) (b : Nat)
    (s : Site) (wit : Local W₀ Rc Xi Tr → Ask) (D : Sent)
    (Lk : K3Letters Cells Tok) (x : PlaceL) (tl : HTailF2) (Rd : Nat → Readers)
    (own : Nat → List (Nat × Nat)) (tabOf : Wit Cells Tok MsgT → Nat × Nat → MsgQ)
    (piece : Nat) : Prop :=
  ∀ blk, L.thread.bs[b]? = some blk → ∀ k st m En ds y cols st',
    ThrS L.thread Said b k st m En →
    drawsFit blk.rounds ds = true → L.thread.Stepped blk k st m En ds y cols st' →
    Ask.Settled s.at_.base (wit m.st.input) ∧ (siteData s (wit m.st.input) m.st.heard ds).Mid ∧
    2 ≤ s.at_.face.planes ∧
    ∃ (a : PartK) (ow : Addr) (base : Due) (o : Nat), segAt? st' = some a ∧
      (∀ g', (seatOf K3Lot.ofForm s.digits).heard st' = some g' →
        (Rd s.link).forms piece "objects" st' = some { forms := g'.rows.toList, late := [] }) ∧
      (Rd s.link).forms piece "guests" st' = some { forms := [], late := [] } ∧
      formsIn (Rd s.link) (own s.link) piece "objects" st' = true ∧
      formsIn (Rd s.link) (own s.link) piece "guests" st' = true ∧
      bookFits Bk (Bk.rowsOf 0) (dueAt Bk.first) s.at_ = true ∧
      startsFit Bk s.at_ s.p.first ow base = true ∧ maskOracle a.L.check.frame = some o ∧
      (∀ ds', SenderLays
        (tabQ (own s.link) a.d.st a.d.book
          (tabOf (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds'))))
        o 1 (s.p.first + s.at_.face.slots) base.e
        (fun i => rd ((coinsE (k.look 0 ow).2).getD i zeroE))) ∧
      ∀ ds', AtDigits s D Lk x tl (wit m.st.input)
        (up (ptsOf s.at_.face s.at_.base (m.st.heard ++ ds)).theta) m.st.heard
        (dataQ (own s.link) a (tabOf (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds')))).mask
        (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds'))

variable {L}

/-- At two planes or more, `DigitsRunAll` gives `DigitsRunFactsFromSaid` at every Said. -/
theorem digitsRunFactsFromSaidOfTheElderBundle
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) Xo → Prop) {b : Nat} {s : Site}
    {wit : Local W₀ Rc Xi Tr → Ask} {x : PlaceL} {tl : HTailF2} {Rd : Nat → Readers}
    {own : Nat → List (Nat × Nat)} {tabOf : Wit Cells Tok MsgT → Nat × Nat → MsgQ} {piece : Nat}
    (twoPlanesOrMore : 2 ≤ s.at_.face.planes)
    (runFacts : DigitsRunAll L b s wit D Lk x tl Rd own tabOf piece) :
    DigitsRunFactsFromSaid L Said b s wit D Lk x tl Rd own tabOf piece :=
  fun blk hblk k st m En ds y cols st' hA hdr hSt =>
    have h := runFacts blk hblk k st m En ds y cols st' hA.1 hdr hSt
    ⟨h.1, h.2.1, twoPlanesOrMore, h.2.2⟩

/-- **Under the bundle no coin of which its clause on the sender speaks is read by default**: at
EVERY owner and start that the test `startsFit` accepts, so at the pair under which the bundle's
clause on the sender speaks, every index lies inside the owner's coins. -/
theorem digitsRunFactsReadNoDefault
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) Xo → Prop} {b : Nat} {s : Site}
    {wit : Local W₀ Rc Xi Tr → Ask} {x : PlaceL} {tl : HTailF2} {Rd : Nat → Readers}
    {own : Nat → List (Nat × Nat)} {tabOf : Wit Cells Tok MsgT → Nat × Nat → MsgQ} {piece : Nat}
    (runFacts : DigitsRunFactsFromSaid L Said b s wit D Lk x tl Rd own tabOf piece) :
    ∀ blk, L.thread.bs[b]? = some blk → ∀ k st m En ds y cols st',
      ThrS L.thread Said b k st m En →
      drawsFit blk.rounds ds = true → L.thread.Stepped blk k st m En ds y cols st' →
      ∀ (ow : Addr) (base : Due), startsFit Bk s.at_ s.p.first ow base = true →
        ∀ j, j < s.p.first + s.at_.face.slots → base.e + j < (coinsE (k.look 0 ow).2).length := by
  intro blk hblk k st m En ds y cols st' hA hdr hSt ow base h6
  obtain ⟨_, _, h2, _, _, _, _, _, _, _, _, _, h5, _⟩ :=
    runFacts blk hblk k st m En ds y cols st' hA hdr hSt
  exact named_reads Bk k s.at_ s.p.first ow base h2 h5 h6

/-- **At every step on the thread, from `ThrS`, the three items that the row opens hold behind the
step.** At the fast summands. `opens_digits_fast` (ExchangeOpensDigits.lean) with the weaker binder
in the premise and in the end. Conditional on the same. -/
theorem digitsItemsHoldBehindTheStep (sources : Sources W₀' Xi' Tr') (olderHash : SecondHashFunctionArgument)
    (policyFile layoutFile keyFile : ByteArray) (description : FileDescription Inst) {Z : Pub} {Bs :
               PureBase}
    (baseBlocks : List (Block FS ProofFile.Cl)) {ch : Chain FS ProofFile.Cl} (sharedSeat : SharedSeat)
        (secondSeat : SecondSeat)
    (descriptionOpens : IM.Open olderHash policyFile layoutFile keyFile description Z Bs baseBlocks
        ch sharedSeat secondSeat) {b : Nat} {s : Site} {lot : Block FS ProofFile.Cl}
    {wit : Local W₀ Rc Xi Tr → Ask}
    (siteStands : SiteAt L b Z Bs ch s lot ((fastFill (Rc := Rc') sources).jobs s).asked wit D Lk)
    (headReturns : HeadReturns L b Z s) (onTheDigits : s.digits = true) {sub : ModelPart}
    (lookupClauseOfTheMeaning : ∀ w, K3At Z.p.X D Lk (L.Mg w)) {x : PlaceL} {tl : HTailF2}
    (digitsPlaceIsRead : digAt Z.p.X s.link = some (x, tl)) (pieceIsTheDigits : pieceOf Z.p.X s.link
        true = 7 + shift sub)
    (runs : Nat → Nat → String → List (Nat × String)) (Rd : Nat → Readers)
    (sent : Nat → Nat → List (Nat × Nat)) (own : Nat → List (Nat × Nat))
    (ah : Nat → String → Bool) (tabOf : Wit Cells Tok MsgT → Nat × Nat → MsgQ)
    (wt : Nat → P × FS → Strs → Wit Cells Tok MsgT → Prop)
    (formsTextHolds : ∀ w, FormsText (L.Mg w) runs Rd sent own ah tabOf wt) (piece : Nat)
    (runsOfObjects : runs s.link (7 + shift sub) "objects" = [(piece, "objects"), (piece,
        "guests")])
    (objectsAreNotAhead : ah piece "objects" = false) (guestsAreNotAhead : ah piece "guests" =
        false)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) Xo → Prop)
    (runFacts : DigitsRunFactsFromSaid L Said b s wit D Lk x tl Rd own tabOf piece) :
    ∀ blk, L.thread.bs[b]? = some blk → ∀ k st m En ds y cols st',
      ThrS L.thread Said b k st m En → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k st m En ds y cols st' →
      L.thread.Items [Item.forms s.link (7 + shift sub) "objects",
        .worth s.link (7 + shift sub) "planes", .worth s.link (7 + shift sub) "keys"] k st' y.2
        (En.add y.1) := by
  intro blk hblk k st m En ds y cols st' hA hdr hSt
  obtain ⟨hSet, hM, _, pa, ow, bs, o', h0, h1, h2, h3, h4, h5, h6, h7, hSd, hW⟩ :=
    runFacts blk hblk k st m En ds y cols st' hA hdr hSt
  exact allOpenings_digitsLookup L Z s siteStands.site lookupClauseOfTheMeaning digitsPlaceIsRead _
      pieceIsTheDigits k blk _ wit st st' m ds y cols En
    (left_thr_fast sources olderHash policyFile layoutFile keyFile description baseBlocks sharedSeat
        secondSeat descriptionOpens siteStands headReturns hblk hA.1 hdr hSt hSet hM)
    ((siteStands.place blk hblk).trans siteStands.lotPlace) (ledger_thr siteStands hA.1) onTheDigits
        runs Rd sent own ah tabOf wt
    (fun w => formsText_gives (formsTextHolds w)) piece runsOfObjects objectsAreNotAhead
        guestsAreNotAhead pa h0 h1 h2 h3 h4 ow bs o' _ h5 h6 h7
    (Nat.le_refl _) hSd hW

end general

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

/-- **The share `ExchangeAtS` at each of the three items that the row opens, at the head's
letters.** `exchangeAt_headDigits` (ExchangeOpensAtHead.lean) with the bundle asked from `ThrS`.
Conditional on the head, the site, R, headReturns and runFacts. At the elder row. -/
theorem digitsExchangeAtHeadLetters (sources : Sources W₀' Xi' Tr') (s : Site)
    (siteOfThePublicPart : s ∈ lookSites Zp)
    (lot : Block TS ProofFile.Cl) (wit : Local W₀ Rc ProofFile.Inst Tr → Ask)
    (R : SiteRest Zp cF H.first s lot ((fastFill (Rc := Rc') sources).jobs s).asked wit)
    (headReturns : HeadReturns (LH) (borderOf s.link s.digits) Zp s) (onTheDigits : s.digits = true)
        {sub : ModelPart}
    (sortOfTheLink : (LH).links[s.link]? = some sub) {x : PlaceL} {tl : HTailF2}
    (digitsPlaceIsRead : digAt Zp.p.X s.link = some (x, tl))
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (runFacts : DigitsRunFactsFromSaid (LH) Said (borderOf s.link s.digits) s wit h.𝔇.sent h.𝔇.l3 x
        tl
      h.𝔇.Rd h.𝔇.N.group (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) (6 + shift sub))
    {j : Item} (itemIsOpened : j ∈ [Item.forms s.link (7 + shift sub) "objects",
      .worth s.link (7 + shift sub) "planes", .worth s.link (7 + shift sub) "keys"]) :
    ExchangeAtS (LH).thread Said (borderOf s.link s.digits) j := by
  obtain ⟨o, pol, lay, KL, Fd, Bs, base, A, B, O, siteStands⟩ :=
    siteAt_lettersHead h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w s siteOfThePublicPart lot _ wit R
  obtain ⟨_, _, e3⟩ := site_border h s siteOfThePublicPart lot R.inLot R.lotPlace
  have hp := (place_at h s siteOfThePublicPart lot R.inLot R.lotPlace).2
  have hpiece : s.at_.place.piece =
      VerifiableInference.Desc.Sound.MgAt.pieceOf s.link s.digits := by
    rw [hp]
    rfl
  obtain ⟨sub', h1, h2⟩ := hsub_at h H.first Q _ _ test carryX item n₁ n₂ _ _ _ s
      siteOfThePublicPart lot
    R.inLot R.lotPlace
  have es : sub' = sub := Option.some.inj (h1.symm.trans sortOfTheLink)
  have hpcT : s.at_.place.piece = 7 + shift sub := by
    rw [h2, es, onTheDigits]
    rfl
  have pieceIsTheDigits : VerifiableInference.Desc.K3.pieceAt Zp.p.X s.link true = 7 + shift sub :=
      by
    rw [← onTheDigits, e3, ← hpiece]
    exact hpcT
  intro blk hblk k st m En ds y cols st' hA hdr hSt ds' i hi
  obtain rfl := List.mem_singleton.1 hi
  exact digitsItemsHoldBehindTheStep sources o pol lay KL Fd base A B O siteStands headReturns
      onTheDigits
    (fun w' => k3At_lettersAt h H.first Q _ _ test carryX item n₁ n₂ _ _ _ w') digitsPlaceIsRead
        pieceIsTheDigits
    h.𝔇.runs h.𝔇.Rd h.𝔇.N.sent h.𝔇.N.group h.𝔇.ah (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) h.𝔇.wt
    (fun w' => formsText_lettersAt h H.first Q _ _ test carryX item n₁ n₂ _ _ _ w')
    (6 + shift sub) (runs_digits h s.link sub sortOfTheLink) (ah_objects h _) (ah_guests h _) Said
        runFacts
    blk hblk k st m En ds y cols st' hA hdr hSt ds' _ itemIsOpened

/-- **The shares in the form of the gathering's binder, at the site's border.**
`shares_headDigits` (ExchangeSharesAtHead.lean) with the bundle asked from `ThrS`. Conditional on
the same. -/
theorem digitsSharesAtHeadLetters (sources : Sources W₀' Xi' Tr') (s : Site)
    (siteOfThePublicPart : s ∈ lookSites Zp)
    (lot : Block TS ProofFile.Cl) (wit : Local W₀ Rc ProofFile.Inst Tr → Ask)
    (R : SiteRest Zp cF H.first s lot ((fastFill (Rc := Rc') sources).jobs s).asked wit)
    (headReturns : HeadReturns (LH) (borderOf s.link s.digits) Zp s) (onTheDigits : s.digits = true)
        {sub : ModelPart}
    (sortOfTheLink : (LH).links[s.link]? = some sub) {x : PlaceL} {tl : HTailF2}
    (digitsPlaceIsRead : digAt Zp.p.X s.link = some (x, tl))
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (runFacts : DigitsRunFactsFromSaid (LH) Said (borderOf s.link s.digits) s wit h.𝔇.sent h.𝔇.l3 x
        tl
      h.𝔇.Rd h.𝔇.N.group (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) (6 + shift sub)) :
    ∀ j : Item, j ∈ ((LH).thread.row (borderOf s.link s.digits)).owes →
      (j ∈ (LH).thread.opened (borderOf s.link s.digits) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS (LH).thread Said (borderOf s.link s.digits) j := by
  intro j itemIsOpened hmid
  obtain ⟨_, hk, _⟩ := site_border h s siteOfThePublicPart lot R.inLot R.lotPlace
  have hpl := (place_at h s siteOfThePublicPart lot R.inLot R.lotPlace).2
  have hl : s.at_.place.link = some s.link := by
    rw [hpl]
  obtain ⟨sub', h1, h2⟩ := hsub_at h H.first Q _ _ test carryX item n₁ n₂ _ _ _ s
      siteOfThePublicPart lot
    R.inLot R.lotPlace
  have es : sub' = sub := Option.some.inj (h1.symm.trans sortOfTheLink)
  have hpcT : s.at_.place.piece = 7 + shift sub := by
    rw [h2, es, onTheDigits]
    rfl
  obtain ⟨_, ho, hc⟩ := digits_row (LH).links s.at_.place s.link sub hl sortOfTheLink hpcT
  rw [owes_at_link (LH) hk hl, ho, hc] at itemIsOpened
  rcases List.mem_append.1 itemIsOpened with h3 | h3
  · exact digitsExchangeAtHeadLetters h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w sources s
      siteOfThePublicPart lot
      wit R headReturns onTheDigits sortOfTheLink digitsPlaceIsRead Said runFacts h3
  · have hopen : j ∈ (LH).thread.opened (borderOf s.link s.digits) :=
      asked_of_fit (LH).thread (n := borderOf s.link s.digits + 1)
        (FirstRows.fwdFit_of_opens ProofFile.Honest.K4.W.onePass_full _) (Nat.lt_succ_self _)
        (by rw [asks_at_link (LH) hk hl, hc]; exact List.mem_append_right _ h3)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h3
    rcases h3 with e | e | e
    · exact absurd e ((hmid hopen).1 _ _)
    · exact absurd e ((hmid hopen).1 _ _)
    · exact absurd e ((hmid hopen).1 _ _)

/-- **The top by kind, both bundles asked from `ThrS`: the shares of the exchange at every number
of the kind K3, all fifty, AT THE ITEMS THAT THE ROW OPENS** (175 of the 313 that the fifty rows
owe:
what a row reads and owes again is excused by the binder). `k3_exchange_by_kind`
(ExchangeByKind.lean) with digitsRunFacts weakened.
Conditional on the head and on: seatAtEverySite at every site; headReturns (it speaks at link 24
alone) and digitsRunFacts at every
site on the digits; packingFits and callsRunFacts at every site on the calls. The elder row. The
full size alone.
-/
theorem lookupExchangeByKindFromSaid (sources : Sources W₀' Xi' Tr')
    (wit : Site → Local W₀ Rc ProofFile.Inst Tr → Ask)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (seatAtEverySite : ∀ s ∈ lookSites Zp, ∃ lot : Block TS ProofFile.Cl,
      SiteRest Zp cF H.first s lot ((fastFill (Rc := Rc') sources).jobs s).asked (wit s))
    (headReturns : ∀ s ∈ lookSites Zp, s.digits = true →
      HeadReturns (LH) (borderOf s.link s.digits) Zp s)
    (digitsRunFacts : ∀ s ∈ lookSites Zp, s.digits = true → ∀ (sub : ModelPart) (x : PlaceL) (tl :
              HTailF2),
      (LH).links[s.link]? = some sub → digAt Zp.p.X s.link = some (x, tl) →
      DigitsRunFactsFromSaid (LH) Said (borderOf s.link s.digits) s (wit s) h.𝔇.sent h.𝔇.l3 x tl
        h.𝔇.Rd h.𝔇.N.group (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) (6 + shift sub))
    (packingFits : ∀ s ∈ lookSites Zp, s.digits = false → planesOk s.shape s.p.lm = true)
    (callsRunFacts : ∀ s ∈ lookSites Zp, s.digits = false →
      CallsRunHead h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w Said s (wit s)) :
    ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.K3 →
      ∀ j : Item, j ∈ ((LH).thread.row b).owes →
      (j ∈ (LH).thread.opened b →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS (LH).thread Said b j := by
  intro b p hb hk
  obtain ⟨l, hl, d, rfl⟩ := k3_number hb hk
  obtain ⟨s, hs, rfl, rfl, _, _⟩ := site_at_all_fifty h l hl d
  obtain ⟨lot, R⟩ := seatAtEverySite s hs
  rcases Bool.eq_false_or_eq_true s.digits with onTheDigits | onTheDigits
  · obtain ⟨sub, sortOfTheLink, _⟩ := hsub_at h H.first Q _ _ test carryX item n₁ n₂ _ _ _ s hs lot
      R.inLot R.lotPlace
    obtain ⟨x, tl, digitsPlaceIsRead⟩ := Q38.digAt_at_head h (Nat.le_of_lt_succ (link_lt_head h s
        hs))
    exact digitsSharesAtHeadLetters h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w sources s hs lot (wit
        s)
      R (headReturns s hs onTheDigits) onTheDigits sortOfTheLink digitsPlaceIsRead Said
          (digitsRunFacts s hs onTheDigits sub x tl sortOfTheLink digitsPlaceIsRead)
  · exact shares_headCalls h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w sources s hs lot (wit s) R
      onTheDigits
      (packingFits s hs onTheDigits) Said (callsRunFacts s hs onTheDigits)

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.digitsRunFactsFromSaidOfTheElderBundle
#print axioms ProofFile.Honest.K3.Term.digitsRunFactsReadNoDefault
#print axioms ProofFile.Honest.K3.Term.digitsItemsHoldBehindTheStep
#print axioms ProofFile.Honest.K3.Term.digitsExchangeAtHeadLetters
#print axioms ProofFile.Honest.K3.Term.digitsSharesAtHeadLetters
#print axioms ProofFile.Honest.K3.Term.lookupExchangeByKindFromSaid
