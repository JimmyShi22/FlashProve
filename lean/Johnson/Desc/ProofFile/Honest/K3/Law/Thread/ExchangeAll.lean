-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ExchangeAll.lean: the honest side of the kind "lookup"
(K3): WHAT THE LOOKUP'S ROW OPENS, IN THE FIRST CHAIN'S THREAD'S OWN LETTERS, ALL ITEMS OF THE ROW'S
LIST: the thread's sentence "the items hold" (`Thread.Items`) at the state that the sub-protocol
leaves, at every continuation of the challenges heard, THE ITEM "objects" NO LONGER A PREMISE.
Theorems with proofs; no definition.

  `allOpenings_digitsLookup`, `all_attention`, `all_layers`

Each joins, at one continuation: the theorem of its sort in
Honest/K3/Law/Thread/ExchangeWorth.lean (the field worth); `objectsQ_site` or `objectsT_site`
(Honest/K3/Law/Thread/ExchangeObjAt.lean: the run "objects"); `formsQ_none` or `formsTQ_none`
(ExchangeForms.lean: the run "guests"); `forms_field` or `formsT_field` (ExchangeField.lean); and
the honest letters.

ONE WORLD FOR ALL ITEMS, AT EACH CONTINUATION BY ITSELF: the mask row against which the table's own
reading is held, and the tables at which the sender's law is asked, are those that the sentence on
forms reads off that continuation's witness. No mask row is fixed across continuations.

THE PREMISES, BY KIND.
  of the play       `LeftAt` in the first chain; the sub-protocol stands at the site's place; the
                    ledger in front as the lookup's laws ask it
  public            the site is one of the public part's; its sort; what the public data hold at its
                    link is there; the piece's number; at the calls the packing's test; the book
                    fits the row; the row's slots start where the sender's coins for the mask row
                    do; the mask row's message; the room
  of the filling    `K3At` at every input; THE FIELD forms (formsT) HAS THE LIBRARY'S TEXT at every
                    input; the name "objects" stands for the runs "objects" and "guests" of one
                    piece; at the digits: the text's test on what is ahead rejects both
  of the state left a segment is open; the readers' two answers; the public test for the promise at
                    both runs; at the calls: the stated data keep the mask row
  AT EACH CONTINUATION'S WITNESS   the sender's law at the tables read; the premises at one witness
                    (`AtDigits`, `AtAttention`, `AtLayers`, Honest/K3/Law/Thread/ExchangeOuts.lean)

A coin is read by `getD … zeroE`, in the hypothesis hS. Below s.p.first + s.at_.face.slots entries
the default is never taken where the face has at least two planes and `bookFits` (each entry inside
its owner's coins) and `startsFit` (owner and start) hold: both tests are hypotheses here:
`named_reads` (Honest/K3/Law/BookFence.lean), at a site `named_reads_site`
(Honest/K3/Law/BookFenceSite.lean). n, the number of entries at which hS is asked, has a lower bound
alone.

hS, at every continuation's witness, has the form of the clause on the sender in `DigitsRunAll`
(ExchangeDigitsAll.lean); hW at the digits is that definition's last clause; at the calls hW is the
like structure of the sort (`AtAttention`, `AtLayers`), which no named debt gathers. All are
equations on the Script's witness and on a run's coins: premises here; this file shows none of them.

Limits. The lookup on the head's calls is not reached HERE (Honest/K3/Law/Thread/ExchangeHead.lean,
ExchangeHeadAll.lean). The theorem on the digits speaks of every link at which the public data hold
the place, the head's among them. The items that the row reads and leaves are not spoken of.
No instance of these hypotheses is exhibited in this file.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeOuts
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeObjAt
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeField

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Law.Exchange
open OnBytes (E zeroE)
open OnBytes.Model (Fork HTailF2)
open OnBytes.Slice (GE)
open VerifiableInference.Desc (Block OpenedColumn Strs Wit)
open VerifiableInference.Desc.First (Meaning Item)
open VerifiableInference.Desc.First.Look (Sent digAt attAt layAt pubAt planesOk)
open VerifiableInference.Desc.K9 (segAt? Readers formsIn formsInT)
open VerifiableInference.Desc.K9L (maskOracle)
open VerifiableInference.Desc.Sound (formsQ formsTQ formsQA dataQ tabQ Stated MsgQ MsgT)
open VerifiableInference.OnPublicFiles (K3At K3Letters)
open ProofFile.Honest.FirstThread (Letters)

local notation "FS" => VerifiableInference.Desc.First.S
local notation "PlaceL" => VerifiableInference.Desc.First.Look.Place
local notation "PartK" => VerifiableInference.Desc.K9.Part
local notation "pieceOf" => VerifiableInference.Desc.K3.pieceAt
local notation "stepAt" => VerifiableInference.Desc.First.Look.stepOf

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr Xo P Cells Tok : Type} {D : Sent} {Lk : K3Letters Cells Tok}
  (L : Letters Bk ProofFile.Cl W₀ Rc Xi Tr Xo P Cells Tok MsgT)

/-- **CONDITIONAL, as the file's head lists: all that the row of the lookup on the digits opens.**
pc: the piece's number. No instance of these hypotheses is exhibited in this file. -/
theorem allOpenings_digitsLookup (Z : Pub) (s : Site) (hsite : s ∈ lookSites Z)
    (hK : ∀ w, K3At Z.p.X D Lk (L.Mg w)) {x : PlaceL} {tl : HTailF2}
    (hx : digAt Z.p.X s.link = some (x, tl)) (pc : Nat) (hpc : pieceOf Z.p.X s.link true = pc)
    (k : Coins Bk) (blk : Block FS ProofFile.Cl) (J : LookJobs Ask)
    (wit : Local W₀ Rc Xi Tr → Ask) (st st' : FS) (m : Mid (Local W₀ Rc Xi Tr) Xo)
    (ds : List Fmt.Drawn) (y : List Played × Mid (Local W₀ Rc Xi Tr) Xo) (cols : List OpenedColumn)
    (En : Env) (hA : AtThr.LeftAt 0 k blk Z s J wit st st' m ds y cols)
    (hp : blk.place = s.at_.place)
    (hLed : ∀ F, (seatOf K3Lot.ofForm s.digits).fork st = some F →
      LedgerIn s.at_.face s.p.first F) (hd : s.digits = true)
    (runs : Nat → Nat → String → List (Nat × String)) (Rd : Nat → Readers)
    (sent : Nat → Nat → List (Nat × Nat)) (own : Nat → List (Nat × Nat))
    (ah : Nat → String → Bool) (tabOf : Wit Cells Tok MsgT → Nat × Nat → MsgQ)
    (wt : Nat → P × FS → Strs → Wit Cells Tok MsgT → Prop)
    (hT : ∀ w, (L.Mg w).forms = fun i k r a y v =>
      (∀ p ∈ runs i k r,
        if ah p.1 p.2 = true then formsQA (sent i) (own i) (Rd i) p.1 p.2 a.2 (tabOf v)
        else formsQ (Rd i) (own i) p.1 p.2 a.2 (tabOf v)) ∧ (r = "weights" → wt i a y v))
    (piece : Nat) (hr : runs s.link pc "objects" = [(piece, "objects"), (piece, "guests")])
    (ha1 : ah piece "objects" = false) (ha2 : ah piece "guests" = false)
    (a : PartK) (hseg : segAt? st' = some a)
    (hRead : ∀ g', (seatOf K3Lot.ofForm s.digits).heard st' = some g' →
      (Rd s.link).forms piece "objects" st' = some { forms := g'.rows.toList, late := [] })
    (hGuests : (Rd s.link).forms piece "guests" st' = some { forms := [], late := [] })
    (hin : formsIn (Rd s.link) (own s.link) piece "objects" st' = true)
    (hinG : formsIn (Rd s.link) (own s.link) piece "guests" st' = true)
    (ow : Addr) (base : Due) (o n : Nat)
    (hb : bookFits Bk (Bk.rowsOf 0) (dueAt Bk.first) s.at_ = true)
    (hs : startsFit Bk s.at_ s.p.first ow base = true)
    (ho : maskOracle a.L.check.frame = some o) (hn : s.p.first + s.at_.face.slots ≤ n)
    (hS : ∀ ds', SenderLays
      (tabQ (own s.link) a.d.st a.d.book (tabOf (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds'))))
      o 1 n base.e (fun i => rd ((coinsE (k.look 0 ow).2).getD i zeroE)))
    (hW : ∀ ds', AtDigits s D Lk x tl (wit m.st.input)
      (up (ptsOf s.at_.face s.at_.base (m.st.heard ++ ds)).theta) m.st.heard
      (dataQ (own s.link) a (tabOf (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds')))).mask
      (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds'))) :
    L.thread.Items [Item.forms s.link pc "objects", .worth s.link pc "planes",
      .worth s.link pc "keys"] k st' y.2 (En.add y.1) := by
  intro ds'
  obtain ⟨h0, ⟨Lf, hL⟩, hM⟩ := hW ds'
  obtain ⟨w1, w2⟩ := worth_at_digits Z s hsite (AtThr.k3At_honest (hK y.2.st.input) L.ans L.test) hx
    k blk J wit st st' m ds y cols hA hp hLed hd _ h0 Lf hL ow base a.L.check.rows a.L.check.frame
    a.d.st _ o n hb hs ho (hS ds') hn hM (L.pubOf y.2.st.input.x) (L.thread.strs (En.add y.1))
  rw [hpc] at w1 w2
  refine holds_digits L.N (L.mg y.2.st.input) s.link pc _ _ _ ?_ w1 w2
  exact forms_field (L.Mg y.2.st.input) runs Rd sent own ah tabOf wt (hT _) s.link pc piece hr ha1
    ha2 (L.pubOf y.2.st.input.x, st') _ _
    (objectsQ_site k blk Z s J wit st st' m ds y cols hA hp (FastLaw.sites_ok Z s hsite).1
      (Rd s.link) (own s.link) piece _ a hseg hRead hin ow base o n hb hs ho (hS ds') hn)
    (formsQ_none (Rd s.link) (own s.link) piece "guests" st' _ hGuests hinG)

/-- **CONDITIONAL, as the file's head lists: all that the row of the lookup on attention's calls
opens.** No instance of these hypotheses is exhibited in this file. -/
theorem all_attention (Z : Pub) (s : Site) (hsite : s ∈ lookSites Z)
    (hK : ∀ w, K3At Z.p.X D Lk (L.Mg w)) {x : PlaceL} {A : OnBytes.Attention.Shape} {tl : HTailF2}
    (hx : attAt Z.p.X s.link = some (x, A, tl)) (pc : Nat)
    (hpc : pieceOf Z.p.X s.link false = pc)
    (k : Coins Bk) (blk : Block FS ProofFile.Cl) (J : LookJobs Ask)
    (wit : Local W₀ Rc Xi Tr → Ask) (st st' : FS) (m : Mid (Local W₀ Rc Xi Tr) Xo)
    (ds : List Fmt.Drawn) (y : List Played × Mid (Local W₀ Rc Xi Tr) Xo) (cols : List OpenedColumn)
    (En : Env) (hA : AtThr.LeftAt 0 k blk Z s J wit st st' m ds y cols)
    (hp : blk.place = s.at_.place)
    (hLed : ∀ F, (seatOf K3Lot.ofForm s.digits).fork st = some F →
      LedgerIn s.at_.face s.p.first F)
    (hpo : planesOk s.shape s.p.lm = true) (hd : s.digits = false)
    (runs : Nat → Nat → String → List (Nat × String)) (Rd : Nat → Readers) (St : Stated)
    (own : Nat → List (Nat × Nat)) (tabOf : Wit Cells Tok MsgT → Nat × Nat → MsgQ)
    (wt : Nat → P × FS → Strs → Wit Cells Tok MsgT → Prop)
    (hT : ∀ w, (L.Mg w).formsT = fun i k r a y v =>
      (∀ p ∈ runs i k r, formsTQ (Rd i) St (own i) p.1 p.2 a.2 (tabOf v)) ∧
        (r = "weights" → wt i a y v))
    (piece : Nat) (hr : runs s.link pc "objects" = [(piece, "objects"), (piece, "guests")])
    (a : PartK) (hseg : segAt? st' = some a)
    (hRead : ∀ g', (seatOf K3Lot.ofForm s.digits).heard st' = some g' →
      (Rd s.link).forms piece "objects" st' = some { forms := g'.rows.toList, late := [] })
    (hGuests : (Rd s.link).forms piece "guests" st' = some { forms := [], late := [] })
    (hin : formsInT (Rd s.link) (own s.link) piece "objects" st' = true)
    (hinG : formsInT (Rd s.link) (own s.link) piece "guests" st' = true)
    (hAt : ∀ B, (St.at1 st' B).mask = B.mask)
    (ow : Addr) (base : Due) (o n : Nat)
    (hb : bookFits Bk (Bk.rowsOf 0) (dueAt Bk.first) s.at_ = true)
    (hs : startsFit Bk s.at_ s.p.first ow base = true)
    (ho : maskOracle a.L.check.frame = some o) (hn : s.p.first + s.at_.face.slots ≤ n)
    (hS : ∀ ds', SenderLays
      (tabQ (own s.link) a.d.st a.d.book (tabOf (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds'))))
      o 1 n base.e (fun i => rd ((coinsE (k.look 0 ow).2).getD i zeroE)))
    (hW : ∀ ds', AtAttention s D Lk x tl (wit m.st.input)
      (up (ptsOf s.at_.face s.at_.base (m.st.heard ++ ds)).theta) m.st.heard
      (dataQ (own s.link) a (tabOf (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds')))).mask
      (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds')) A) :
    L.thread.Items [Item.formsT s.link pc "objects", .worth s.link pc "planes",
      .worth s.link pc "keys", .worth s.link pc "rider"] k st' y.2 (En.add y.1) := by
  intro ds'
  obtain ⟨h0, ⟨Lf, hL⟩, hM, hC⟩ := hW ds'
  obtain ⟨w1, w2, w3⟩ := worth_at_attention Z s hsite
    (AtThr.k3At_honest (hK y.2.st.input) L.ans L.test) hx
    k blk J wit st st' m ds y cols hA hp hLed hpo hd _ h0 Lf hL ow base a.L.check.rows
    a.L.check.frame a.d.st _ o n hb hs ho (hS ds') hn hM hC (L.pubOf y.2.st.input.x)
    (L.thread.strs (En.add y.1))
  rw [hpc] at w1 w2 w3
  refine holds_calls L.N (L.mg y.2.st.input) s.link pc _ _ _ ?_ w1 w2 w3
  exact formsT_field (L.Mg y.2.st.input) runs Rd St own tabOf wt (hT _) s.link pc piece hr
    (L.pubOf y.2.st.input.x, st') _ _
    (objectsT_site k blk Z s J wit st st' m ds y cols hA hp (FastLaw.sites_ok Z s hsite).1
      (Rd s.link) St (own s.link) piece _ a hseg hRead hin (hAt _) ow base o n hb hs ho (hS ds') hn)
    (formsTQ_none (Rd s.link) St (own s.link) piece "guests" st' _ hGuests hinG)

/-- **CONDITIONAL, as the file's head lists: all that the row of the lookup on the layers' calls
opens.** No instance of these hypotheses is exhibited in this file. -/
theorem all_layers (Z : Pub) (s : Site) (hsite : s ∈ lookSites Z)
    (hK : ∀ w, K3At Z.p.X D Lk (L.Mg w)) {x : PlaceL} {tl : HTailF2}
    (hna : attAt Z.p.X s.link = none) (hx : layAt Z.p.X s.link = some x)
    (ht : VerifiableInference.Desc.First.Look.tlAt Z.p.X s.link = some tl) (pc : Nat)
    (hpc : pieceOf Z.p.X s.link false = pc)
    (k : Coins Bk) (blk : Block FS ProofFile.Cl) (J : LookJobs Ask)
    (wit : Local W₀ Rc Xi Tr → Ask) (st st' : FS) (m : Mid (Local W₀ Rc Xi Tr) Xo)
    (ds : List Fmt.Drawn) (y : List Played × Mid (Local W₀ Rc Xi Tr) Xo) (cols : List OpenedColumn)
    (En : Env) (hA : AtThr.LeftAt 0 k blk Z s J wit st st' m ds y cols)
    (hp : blk.place = s.at_.place)
    (hLed : ∀ F, (seatOf K3Lot.ofForm s.digits).fork st = some F →
      LedgerIn s.at_.face s.p.first F)
    (hpo : planesOk s.shape s.p.lm = true) (hd : s.digits = false)
    (runs : Nat → Nat → String → List (Nat × String)) (Rd : Nat → Readers) (St : Stated)
    (own : Nat → List (Nat × Nat)) (tabOf : Wit Cells Tok MsgT → Nat × Nat → MsgQ)
    (wt : Nat → P × FS → Strs → Wit Cells Tok MsgT → Prop)
    (hT : ∀ w, (L.Mg w).formsT = fun i k r a y v =>
      (∀ p ∈ runs i k r, formsTQ (Rd i) St (own i) p.1 p.2 a.2 (tabOf v)) ∧
        (r = "weights" → wt i a y v))
    (piece : Nat) (hr : runs s.link pc "objects" = [(piece, "objects"), (piece, "guests")])
    (a : PartK) (hseg : segAt? st' = some a)
    (hRead : ∀ g', (seatOf K3Lot.ofForm s.digits).heard st' = some g' →
      (Rd s.link).forms piece "objects" st' = some { forms := g'.rows.toList, late := [] })
    (hGuests : (Rd s.link).forms piece "guests" st' = some { forms := [], late := [] })
    (hin : formsInT (Rd s.link) (own s.link) piece "objects" st' = true)
    (hinG : formsInT (Rd s.link) (own s.link) piece "guests" st' = true)
    (hAt : ∀ B, (St.at1 st' B).mask = B.mask)
    (ow : Addr) (base : Due) (o n : Nat)
    (hb : bookFits Bk (Bk.rowsOf 0) (dueAt Bk.first) s.at_ = true)
    (hs : startsFit Bk s.at_ s.p.first ow base = true)
    (ho : maskOracle a.L.check.frame = some o) (hn : s.p.first + s.at_.face.slots ≤ n)
    (hS : ∀ ds', SenderLays
      (tabQ (own s.link) a.d.st a.d.book (tabOf (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds'))))
      o 1 n base.e (fun i => rd ((coinsE (k.look 0 ow).2).getD i zeroE)))
    (hW : ∀ ds', AtLayers s D Lk x tl (wit m.st.input)
      (up (ptsOf s.at_.face s.at_.base (m.st.heard ++ ds)).theta) m.st.heard
      (dataQ (own s.link) a (tabOf (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds')))).mask
      (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds'))
      (pubAt Z.p.X (s.link / stepAt Z.p.X))) :
    L.thread.Items [Item.formsT s.link pc "objects", .worth s.link pc "planes",
      .worth s.link pc "keys", .worth s.link pc "rider"] k st' y.2 (En.add y.1) := by
  intro ds'
  obtain ⟨h0, ⟨Lf, hL⟩, hM, hC⟩ := hW ds'
  obtain ⟨w1, w2, w3⟩ := worth_at_layers Z s hsite
    (AtThr.k3At_honest (hK y.2.st.input) L.ans L.test) hna hx ht
    k blk J wit st st' m ds y cols hA hp hLed hpo hd _ h0 Lf hL ow base a.L.check.rows
    a.L.check.frame a.d.st _ o n hb hs ho (hS ds') hn hM hC (L.pubOf y.2.st.input.x)
    (L.thread.strs (En.add y.1))
  rw [hpc] at w1 w2 w3
  refine holds_calls L.N (L.mg y.2.st.input) s.link pc _ _ _ ?_ w1 w2 w3
  exact formsT_field (L.Mg y.2.st.input) runs Rd St own tabOf wt (hT _) s.link pc piece hr
    (L.pubOf y.2.st.input.x, st') _ _
    (objectsT_site k blk Z s J wit st st' m ds y cols hA hp (FastLaw.sites_ok Z s hsite).1
      (Rd s.link) St (own s.link) piece _ a hseg hRead hin (hAt _) ow base o n hb hs ho (hS ds') hn)
    (formsTQ_none (Rd s.link) St (own s.link) piece "guests" st' _ hGuests hinG)

#print axioms ProofFile.Honest.K3.Law.Exchange.allOpenings_digitsLookup
#print axioms ProofFile.Honest.K3.Law.Exchange.all_attention
#print axioms ProofFile.Honest.K3.Law.Exchange.all_layers

end ProofFile.Honest.K3.Law.Exchange
