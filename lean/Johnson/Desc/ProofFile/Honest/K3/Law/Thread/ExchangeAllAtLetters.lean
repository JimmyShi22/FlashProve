-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ExchangeAllAtLetters.lean: the honest side of the kind
"lookup" (K3): `allOpenings_digitsLookup`, `all_attention`, `all_layers` (Honest/K3/Law/Thread/ExchangeAll.lean)
and `all_head` (ExchangeHeadAll.lean) CALLED AT THE FIRST CHAIN'S LETTERS LAID AT THE LIBRARY'S OWN
(`lettersAt`, Honest/Thread/FirstAt.lean), EVERY PREMISE "OF THE FILLING" LAID IN. Theorems with
proofs; no definition.

  `digits_letters`, `attention_letters`, `layers_letters`, `head_letters`

GONE AS PREMISES, each paid by a theorem of Honest/K3/Law/Thread/ExchangeAtLetters.lean or
FormsAtLetters.lean: `K3At` (at the head's calls `HeadSuffices`, with the head's place) at every
input; the text of the field forms or formsT at every input; the list of runs for the name
"objects"; at the digits the rejection of both runs by the text's test on what is ahead; at the
calls "the stated data keep the mask row" (by unfolding: the library's `Stated.of` lays the mask row
as it is).
IN THEIR STEAD: the library's head h, and the sort of the site's segment in the data's list.

WHAT STAYS, by kind, as Honest/K3/Law/Thread/ExchangeAll.lean's head lists it: of the play; public;
of the state left (a segment is open; the readers' two answers; the public test for the promise at
both runs); at each continuation's witness (the
sender's law; the premises at one witness). All now at the letters of the library's own data.

Conditional on the head `P5J.AtMgA`. That it holds at the goals' two named sets of public files is a
sealed theorem (`headMember_named`, AtFullSide/Top/HeadMemberAtGap.lean), with that file's own
limits; this file does not call it.

A coin is read by `getD … zeroE`, in the hypothesis hS. Below s.p.first + s.at_.face.slots entries
the default is never taken where the face has at least two planes and `bookFits` (each entry inside
its owner's coins) and `startsFit` (owner and start) hold: both tests are hypotheses here:
`named_reads` (Honest/K3/Law/BookFence.lean), at a site `named_reads_site`
(Honest/K3/Law/BookFenceSite.lean). n, the number of entries at which hS is asked, has a lower bound
alone.

hS, at every continuation's witness, has the form of the clause on the sender in `DigitsRunAll`
(ExchangeDigitsAll.lean); hW at the digits is that definition's last clause; at the calls hW is the
like structure of the sort (`AtAttention`, `AtLayers`, `AtHead`), which no named debt gathers. All
are equations on the Script's witness and on a run's coins: premises here; this file shows none of
them.

Limits. AT THE FULL SIZE ALONE. The items that the row reads and leaves are not spoken of.
No instance of the hypotheses beside the head is exhibited in this file.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeAtLetters
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeHeadAll
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.FormsAtLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Law.Exchange
open OnBytes (E zeroE)
open OnBytes.Model (Fork HTailF2)
open OnBytes.Slice (GE)
open VerifiableInference.Desc (Block Chain OpenedColumn Strs)
open VerifiableInference.Desc.First (Item ModelPart shift)
open VerifiableInference.Desc.First.Look (digAt attAt layAt pubAt planesOk)
open VerifiableInference.Desc.K9 (segAt? formsIn formsInT)
open VerifiableInference.Desc.K9L (maskOracle)
open VerifiableInference.Desc.Sound (MsgT seatTab dataQ tabQ)
open VerifiableInference.OnPublicFiles (headLink k3SizesAt k3PolicyAt k3AdrAt)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersAt WtF Script)

local notation "PlaceL" => VerifiableInference.Desc.First.Look.Place
local notation "PartK" => VerifiableInference.Desc.K9.Part
local notation "pieceOf" => VerifiableInference.Desc.K3.pieceAt
local notation "stepAt" => VerifiableInference.Desc.First.Look.stepOf

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xH : PlaceL} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xH) {Bk : ProverCoinCounts}
  {W₀ Rc Tr Xo : Type}
  (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Xo))
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
  (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
  (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
  (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (keeps : Nat → TS → TS → Prop)

/-- **CONDITIONAL, as the file's head lists: all that the row of the lookup on the digits opens, at
these letters.** No instance of the hypotheses beside the head is exhibited in this file. -/
theorem digits_letters (s : Site) (hsite : s ∈ lookSites Zp) {x : PlaceL} {tl : HTailF2}
    (hx : digAt Zp.p.X s.link = some (x, tl)) (sub : ModelPart)
    (hsub : h.𝔇.links[s.link]? = some sub) (hpc : pieceOf Zp.p.X s.link true = 7 + shift sub)
    (k : Coins Bk) (blk : Block TS ProofFile.Cl) (J : LookJobs Ask)
    (wit : Local W₀ Rc ProofFile.Inst Tr → Ask) (st st' : TS) (m : Mid (Local W₀ Rc ProofFile.Inst Tr) Xo)
    (ds : List Fmt.Drawn) (y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) Xo) (cols : List OpenedColumn)
    (En : Env) (hA : AtThr.LeftAt 0 k blk Zp s J wit st st' m ds y cols)
    (hp : blk.place = s.at_.place)
    (hLed : ∀ F, (seatOf K3Lot.ofForm s.digits).fork st = some F →
      LedgerIn s.at_.face s.p.first F) (hd : s.digits = true)
    (a : PartK) (hseg : segAt? st' = some a)
    (hRead : ∀ g', (seatOf K3Lot.ofForm s.digits).heard st' = some g' →
      (h.𝔇.Rd s.link).forms (6 + shift sub) "objects" st' =
        some { forms := g'.rows.toList, late := [] })
    (hGuests : (h.𝔇.Rd s.link).forms (6 + shift sub) "guests" st' =
      some { forms := [], late := [] })
    (hin : formsIn (h.𝔇.Rd s.link) (h.𝔇.N.group s.link) (6 + shift sub) "objects" st' = true)
    (hinG : formsIn (h.𝔇.Rd s.link) (h.𝔇.N.group s.link) (6 + shift sub) "guests" st' = true)
    (ow : Addr) (base : Due) (o n : Nat)
    (hb : bookFits Bk (Bk.rowsOf 0) (dueAt Bk.first) s.at_ = true)
    (hst : startsFit Bk s.at_ s.p.first ow base = true)
    (ho : maskOracle a.L.check.frame = some o) (hn : s.p.first + s.at_.face.slots ≤ n)
    (hS : ∀ ds', SenderLays
      (tabQ (h.𝔇.N.group s.link) a.d.st a.d.book
        (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms (Q.wit k y.2.st.input (y.2.st.heard ++ ds'))))
      o 1 n base.e (fun i => rd ((coinsE (k.look 0 ow).2).getD i zeroE)))
    (hW : ∀ ds', AtDigits s h.𝔇.sent h.𝔇.l3 x tl (wit m.st.input)
      (up (ptsOf s.at_.face s.at_.base (m.st.heard ++ ds)).theta) m.st.heard
      (dataQ (h.𝔇.N.group s.link) a
        (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms (Q.wit k y.2.st.input (y.2.st.heard ++ ds')))).mask
      (Q.wit k y.2.st.input (y.2.st.heard ++ ds'))) :
    (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread.Items
      [Item.forms s.link (7 + shift sub) "objects", .worth s.link (7 + shift sub) "planes",
        .worth s.link (7 + shift sub) "keys"] k st' y.2 (En.add y.1) :=
  allOpenings_digitsLookup (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) Zp s hsite
    (fun w => k3At_lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps w) hx _ hpc
    k blk J wit st st' m ds y cols En hA hp hLed hd h.𝔇.runs h.𝔇.Rd h.𝔇.N.sent h.𝔇.N.group h.𝔇.ah
    (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) h.𝔇.wt
    (fun w => formsText_gives
      (formsText_lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps w))
    (6 + shift sub) (runs_digits h s.link sub hsub) (ah_objects h _) (ah_guests h _) a hseg hRead
    hGuests hin hinG ow base o n hb hst ho hn hS hW

/-- **CONDITIONAL, as the file's head lists: all that the row of the lookup on attention's calls
opens, at these letters.** No instance of the hypotheses beside the head is exhibited in this file.
-/
theorem attention_letters (s : Site) (hsite : s ∈ lookSites Zp) {x : PlaceL}
    {A : OnBytes.Attention.Shape} {tl : HTailF2} (hx : attAt Zp.p.X s.link = some (x, A, tl))
    (sub : ModelPart)
    (hsub : h.𝔇.links[s.link]? = some sub) (hpc : pieceOf Zp.p.X s.link false = 2 + shift sub)
    (k : Coins Bk) (blk : Block TS ProofFile.Cl) (J : LookJobs Ask)
    (wit : Local W₀ Rc ProofFile.Inst Tr → Ask) (st st' : TS) (m : Mid (Local W₀ Rc ProofFile.Inst Tr) Xo)
    (ds : List Fmt.Drawn) (y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) Xo) (cols : List OpenedColumn)
    (En : Env) (hA : AtThr.LeftAt 0 k blk Zp s J wit st st' m ds y cols)
    (hp : blk.place = s.at_.place)
    (hLed : ∀ F, (seatOf K3Lot.ofForm s.digits).fork st = some F →
      LedgerIn s.at_.face s.p.first F)
    (hpo : planesOk s.shape s.p.lm = true) (hd : s.digits = false)
    (a : PartK) (hseg : segAt? st' = some a)
    (hRead : ∀ g', (seatOf K3Lot.ofForm s.digits).heard st' = some g' →
      (h.𝔇.Rd s.link).forms (1 + shift sub) "objects" st' =
        some { forms := g'.rows.toList, late := [] })
    (hGuests : (h.𝔇.Rd s.link).forms (1 + shift sub) "guests" st' =
      some { forms := [], late := [] })
    (hin : formsInT (h.𝔇.Rd s.link) (h.𝔇.N.sent s.link 0) (1 + shift sub) "objects" st' = true)
    (hinG : formsInT (h.𝔇.Rd s.link) (h.𝔇.N.sent s.link 0) (1 + shift sub) "guests" st' = true)
    (ow : Addr) (base : Due) (o n : Nat)
    (hb : bookFits Bk (Bk.rowsOf 0) (dueAt Bk.first) s.at_ = true)
    (hst : startsFit Bk s.at_ s.p.first ow base = true)
    (ho : maskOracle a.L.check.frame = some o) (hn : s.p.first + s.at_.face.slots ≤ n)
    (hS : ∀ ds', SenderLays
      (tabQ (h.𝔇.N.sent s.link 0) a.d.st a.d.book
        (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms (Q.wit k y.2.st.input (y.2.st.heard ++ ds'))))
      o 1 n base.e (fun i => rd ((coinsE (k.look 0 ow).2).getD i zeroE)))
    (hW : ∀ ds', AtAttention s h.𝔇.sent h.𝔇.l3 x tl (wit m.st.input)
      (up (ptsOf s.at_.face s.at_.base (m.st.heard ++ ds)).theta) m.st.heard
      (dataQ (h.𝔇.N.sent s.link 0) a
        (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms (Q.wit k y.2.st.input (y.2.st.heard ++ ds')))).mask
      (Q.wit k y.2.st.input (y.2.st.heard ++ ds')) A) :
    (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread.Items
      [Item.formsT s.link (2 + shift sub) "objects", .worth s.link (2 + shift sub) "planes",
        .worth s.link (2 + shift sub) "keys", .worth s.link (2 + shift sub) "rider"] k st' y.2
      (En.add y.1) :=
  all_attention (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) Zp s hsite
    (fun w => k3At_lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps w) hx _
    hpc k blk J wit st st' m ds y cols En hA hp hLed hpo hd h.𝔇.runs h.𝔇.Rd h.𝔇.St
    (fun i => h.𝔇.N.sent i 0) (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) h.𝔇.wt
    (fun w => formsT_lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps w)
    (1 + shift sub) (runs_calls h s.link sub hsub) a hseg hRead hGuests hin hinG (fun _ => rfl) ow
    base o n hb hst ho hn hS hW

/-- **CONDITIONAL, as the file's head lists: all that the row of the lookup on the layers' calls
opens, at these letters.** No instance of the hypotheses beside the head is exhibited in this file.
-/
theorem layers_letters (s : Site) (hsite : s ∈ lookSites Zp) {x : PlaceL} {tl : HTailF2}
    (hna : attAt Zp.p.X s.link = none) (hx : layAt Zp.p.X s.link = some x)
    (ht : VerifiableInference.Desc.First.Look.tlAt Zp.p.X s.link = some tl) (sub : ModelPart)
    (hsub : h.𝔇.links[s.link]? = some sub) (hpc : pieceOf Zp.p.X s.link false = 2 + shift sub)
    (k : Coins Bk) (blk : Block TS ProofFile.Cl) (J : LookJobs Ask)
    (wit : Local W₀ Rc ProofFile.Inst Tr → Ask) (st st' : TS) (m : Mid (Local W₀ Rc ProofFile.Inst Tr) Xo)
    (ds : List Fmt.Drawn) (y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) Xo) (cols : List OpenedColumn)
    (En : Env) (hA : AtThr.LeftAt 0 k blk Zp s J wit st st' m ds y cols)
    (hp : blk.place = s.at_.place)
    (hLed : ∀ F, (seatOf K3Lot.ofForm s.digits).fork st = some F →
      LedgerIn s.at_.face s.p.first F)
    (hpo : planesOk s.shape s.p.lm = true) (hd : s.digits = false)
    (a : PartK) (hseg : segAt? st' = some a)
    (hRead : ∀ g', (seatOf K3Lot.ofForm s.digits).heard st' = some g' →
      (h.𝔇.Rd s.link).forms (1 + shift sub) "objects" st' =
        some { forms := g'.rows.toList, late := [] })
    (hGuests : (h.𝔇.Rd s.link).forms (1 + shift sub) "guests" st' =
      some { forms := [], late := [] })
    (hin : formsInT (h.𝔇.Rd s.link) (h.𝔇.N.sent s.link 0) (1 + shift sub) "objects" st' = true)
    (hinG : formsInT (h.𝔇.Rd s.link) (h.𝔇.N.sent s.link 0) (1 + shift sub) "guests" st' = true)
    (ow : Addr) (base : Due) (o n : Nat)
    (hb : bookFits Bk (Bk.rowsOf 0) (dueAt Bk.first) s.at_ = true)
    (hst : startsFit Bk s.at_ s.p.first ow base = true)
    (ho : maskOracle a.L.check.frame = some o) (hn : s.p.first + s.at_.face.slots ≤ n)
    (hS : ∀ ds', SenderLays
      (tabQ (h.𝔇.N.sent s.link 0) a.d.st a.d.book
        (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms (Q.wit k y.2.st.input (y.2.st.heard ++ ds'))))
      o 1 n base.e (fun i => rd ((coinsE (k.look 0 ow).2).getD i zeroE)))
    (hW : ∀ ds', AtLayers s h.𝔇.sent h.𝔇.l3 x tl (wit m.st.input)
      (up (ptsOf s.at_.face s.at_.base (m.st.heard ++ ds)).theta) m.st.heard
      (dataQ (h.𝔇.N.sent s.link 0) a
        (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms (Q.wit k y.2.st.input (y.2.st.heard ++ ds')))).mask
      (Q.wit k y.2.st.input (y.2.st.heard ++ ds'))
      (pubAt Zp.p.X (s.link / stepAt Zp.p.X))) :
    (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread.Items
      [Item.formsT s.link (2 + shift sub) "objects", .worth s.link (2 + shift sub) "planes",
        .worth s.link (2 + shift sub) "keys", .worth s.link (2 + shift sub) "rider"] k st' y.2
      (En.add y.1) :=
  all_layers (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) Zp s hsite
    (fun w => k3At_lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps w) hna hx
    ht _ hpc k blk J wit st st' m ds y cols En hA hp hLed hpo hd h.𝔇.runs h.𝔇.Rd h.𝔇.St
    (fun i => h.𝔇.N.sent i 0) (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) h.𝔇.wt
    (fun w => formsT_lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps w)
    (1 + shift sub) (runs_calls h s.link sub hsub) a hseg hRead hGuests hin hinG (fun _ => rfl) ow
    base o n hb hst ho hn hS hW

/-- **CONDITIONAL, as the file's head lists: all that the row of the lookup on the head's calls
opens, at these letters.** The sizes, policy, addresses and requests are the library's own. hW takes
the reply's token as the verifier's state has it, 0 where the state has none
(`st'.replyTok?.getD 0`): public; no hypothesis here says that the token is there. No instance of
the hypotheses beside the head is exhibited in this file. -/
theorem head_letters (s : Site) (hsite : s ∈ lookSites Zp) (hl : s.link = headLink Zp.p.X)
    (hsub : h.𝔇.links[s.link]? = some .head)
    (k : Coins Bk) (blk : Block TS ProofFile.Cl) (J : LookJobs Ask)
    (wit : Local W₀ Rc ProofFile.Inst Tr → Ask) (st st' : TS) (m : Mid (Local W₀ Rc ProofFile.Inst Tr) Xo)
    (ds : List Fmt.Drawn) (y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) Xo) (cols : List OpenedColumn)
    (En : Env) (hA : AtThr.LeftAt 0 k blk Zp s J wit st st' m ds y cols)
    (hp : blk.place = s.at_.place)
    (hLed : ∀ F, (seatOf K3Lot.ofForm s.digits).fork st = some F →
      LedgerIn s.at_.face s.p.first F)
    (hpo : planesOk s.shape s.p.lm = true) (hd : s.digits = false)
    (a : PartK) (hseg : segAt? st' = some a)
    (hRead : ∀ g', (seatOf K3Lot.ofForm s.digits).heard st' = some g' →
      (h.𝔇.Rd s.link).forms 2 "objects" st' =
        some { forms := g'.rows.toList, late := [] })
    (hGuests : (h.𝔇.Rd s.link).forms 2 "guests" st' = some { forms := [], late := [] })
    (hin : formsInT (h.𝔇.Rd s.link) (h.𝔇.N.sent s.link 0) 2 "objects" st' = true)
    (hinG : formsInT (h.𝔇.Rd s.link) (h.𝔇.N.sent s.link 0) 2 "guests" st' = true)
    (ow : Addr) (base : Due) (o n : Nat)
    (hb : bookFits Bk (Bk.rowsOf 0) (dueAt Bk.first) s.at_ = true)
    (hst : startsFit Bk s.at_ s.p.first ow base = true)
    (ho : maskOracle a.L.check.frame = some o) (hn : s.p.first + s.at_.face.slots ≤ n)
    (hS : ∀ ds', SenderLays
      (tabQ (h.𝔇.N.sent s.link 0) a.d.st a.d.book
        (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms (Q.wit k y.2.st.input (y.2.st.heard ++ ds'))))
      o 1 n base.e (fun i => rd ((coinsE (k.look 0 ow).2).getD i zeroE)))
    (hW : ∀ ds', @AtHead (k3SizesAt (P5J.At.X Zp)) (k3PolicyAt (P5J.At.X Zp))
      (h.𝔇.rq y.2.st.input.x.pub) _ _ Zp s h.𝔇.sent h.𝔇.l3 (k3AdrAt (P5J.At.X Zp)) xH
      (wit m.st.input) (up (ptsOf s.at_.face s.at_.base (m.st.heard ++ ds)).theta) m.st.heard
      (dataQ (h.𝔇.N.sent s.link 0) a
        (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms (Q.wit k y.2.st.input (y.2.st.heard ++ ds')))).mask
      (st'.replyTok?.getD 0) (Q.wit k y.2.st.input (y.2.st.heard ++ ds'))) :
    (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread.Items
      [Item.formsT s.link 3 "objects", .worth s.link 3 "planes", .worth s.link 3 "keys",
        .worth s.link 3 "rider"] k st' y.2 (En.add y.1) :=
  @all_head (k3SizesAt (P5J.At.X Zp)) (k3PolicyAt (P5J.At.X Zp)) _ _ _ _ _ _ _ _ _ _ _
    (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps) Zp s hsite
    (k3AdrAt (P5J.At.X Zp)) h.𝔇.rq xH h.headAt hl
    (fun w => headSuffices_lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps w)
    k blk J wit st st' m ds y cols En hA hp hLed hpo hd h.𝔇.runs h.𝔇.Rd h.𝔇.St
    (fun i => h.𝔇.N.sent i 0) (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) h.𝔇.wt
    (fun w => formsT_lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps w) 2
    (runs_calls h s.link .head hsub) a hseg hRead hGuests hin hinG (fun _ => rfl) ow base o n hb hst
    ho hn hS hW

#print axioms ProofFile.Honest.K3.Law.Exchange.digits_letters
#print axioms ProofFile.Honest.K3.Law.Exchange.attention_letters
#print axioms ProofFile.Honest.K3.Law.Exchange.layers_letters
#print axioms ProofFile.Honest.K3.Law.Exchange.head_letters

end ProofFile.Honest.K3.Law.Exchange
