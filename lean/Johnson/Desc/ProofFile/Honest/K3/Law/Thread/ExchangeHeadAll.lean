-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ExchangeHeadAll.lean: the honest side of the kind
"lookup" (K3): THE LOOKUP ON THE HEAD'S CALLS: where the sub-protocol has accepted, in the first
chain: the field worth of the table of joints at the state that it leaves; and ALL THAT THE ROW
OPENS, in the first chain's thread's own letters. A structure of propositions; theorems with proofs.

It is the fourth beside `worth_at_digits`, `worth_at_attention`, `worth_at_layers`
(Honest/K3/Law/Thread/ExchangeWorth.lean) and `allOpenings_digitsLookup`, `all_attention`, `all_layers`
(ExchangeAll.lean). What is other here: the premise on the filling is `HeadSuffices`
(Honest/K3/Law/Thread/ExchangeHead.lean), not `K3At`; three classes on the head's sizes, policy and
request are carried; the table's key vectors and riders are read AT THE TOKEN OF THE REPLY THAT THE
STATE LEFT HOLDS.

  `AtHead`           the premises at one witness, under one name
  `worth_at_head`    the field worth at "planes", "keys", "rider"
  `all_head`         the thread's sentence "the items hold" of the row's list of opened items

The premises, by kind: as Honest/K3/Law/Thread/ExchangeAll.lean's head lists them for the calls; and
the site's link is the head's.

A coin is read by `getD … zeroE`, in the hypothesis hS. Below s.p.first + s.at_.face.slots entries
the default is never taken where the face has at least two planes and `bookFits` (each entry inside
its owner's coins) and `startsFit` (owner and start) hold: both tests are hypotheses here:
`named_reads` (Honest/K3/Law/BookFence.lean), at a site `named_reads_site`
(Honest/K3/Law/BookFenceSite.lean). n, the number of entries at which hS is asked, has a lower bound
alone.

In `all_head` hS, at every continuation's witness, has the form of the clause on the sender in
`DigitsRunAll` (ExchangeDigitsAll.lean); hW is `AtHead`, the like of that definition's last clause
at the head's calls, which no named debt gathers. `worth_at_head` bears both at one table and one
witness. All are equations on a witness and on a run's coins: premises here; this file shows none of
them.

Limits. The items that the row reads and leaves are not spoken of. No instance of these hypotheses
is exhibited in this file. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeAll
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Law.Exchange
open OnBytes (E zeroE)
open OnBytes.Model (Fork)
open OnBytes.Slice (GE)
open VerifiableInference.Desc (Block OpenedColumn Strs Wit)
open VerifiableInference.Desc.First (Meaning Item)
open VerifiableInference.Desc.First.Look (Sent planesOk)
open VerifiableInference.Desc.Kinds.Head (Sizes Policy Request)
open VerifiableInference.Desc.Kinds.Head.Law (HeadAdr headAt headLay headRider)
open VerifiableInference.Desc.K9 (segAt? Readers formsInT)
open VerifiableInference.Desc.K9L (dataOf maskOracle)
open VerifiableInference.Desc.Sound (formsTQ dataQ tabQ Stated MsgQ MsgT)
open VerifiableInference.OnPublicFiles
open ProofFile.Honest.FirstThread (Letters)

local notation "FS" => VerifiableInference.Desc.First.S
local notation "PlaceL" => VerifiableInference.Desc.First.Look.Place
local notation "PartK" => VerifiableInference.Desc.K9.Part

variable [Sizes] [Policy]

/-- **The premises at one witness, at the head's calls.** tok: the token of the reply. -/
structure AtHead [Request] {Cells Tok : Type} (Z : Pub) (s : Site) (D : Sent)
    (Lk : K3Letters Cells Tok) (adr : HeadAdr) (x : PlaceL) (a : Ask) (theta : GE)
    (heard : List Fmt.Drawn) (mask : Nat → GE) (tok : Nat) (v : Wit Cells Tok MsgT) : Prop where
  zero : headNu adr x Z.p.X.H.tl D Lk.rad Lk.oW Lk.wOf Lk.nr Lk.nc
      (fun j => Lk.seat x.link false j.1) Lk.arr Lk.msgW v .zero = 0
  fills : ∃ L, FillsAt s a L
    (Cb.Fo.forK Cb.Gl.E (headLay adr x.fs x.lm x.F.next x.ns Z.p.X.H.tl Lk.nr Lk.nc) tok
      (Cb.Fo.zext (layMu x Z.p.X.H.tl D Lk.rad Lk.oW Lk.wOf Lk.nr Lk.nc
        (fun j => Lk.seat x.link false j.1) Lk.arr Lk.msgW v)))
    (headNu adr x Z.p.X.H.tl D Lk.rad Lk.oW Lk.wOf Lk.nr Lk.nc
      (fun j => Lk.seat x.link false j.1) Lk.arr Lk.msgW v) theta heard
  masks : ∀ j, j < s.p.first + s.at_.face.slots →
    headNu adr x Z.p.X.H.tl D Lk.rad Lk.oW Lk.wOf Lk.nr Lk.nc
      (fun j => Lk.seat x.link false j.1) Lk.arr Lk.msgW v (.mask j) = mask j
  cubes : Cb.Rider.OnCubes
    (headRider adr x Z.p.X.H.tl D Lk.rad Lk.oW Lk.wOf Lk.nr Lk.nc Iop.extNone Unit).g
    (headRider adr x Z.p.X.H.tl D Lk.rad Lk.oW Lk.wOf Lk.nr Lk.nc Iop.extNone Unit).f tok
    (layMs x D Lk.rad Lk.oW (fun j => Lk.seat x.link false j.1) Lk.arr Lk.msgW v)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr Xo P Cells Tok : Type} {D : Sent} {Lk : K3Letters Cells Tok}

/-- **CONDITIONAL, as the file's head lists: the field worth at the head's calls.** R: the request
at the public part z. hW takes the reply's token as the verifier's state has it, 0 where the state
has none (`st'.replyTok?.getD 0`): public; no hypothesis here says that the token is there. No
instance of these hypotheses is exhibited in this file. -/
theorem worth_at_head {Mg : Meaning P (Wit Cells Tok MsgT)} (Z : Pub) (s : Site)
    (hsite : s ∈ lookSites Z) (adr : HeadAdr) (rq : P → Request) {x : PlaceL}
    (hx : headAt Z.p.X = some x) (hl : s.link = headLink Z.p.X)
    (hH : HeadSuffices Z.p.X D Lk adr rq x Mg) (k : Coins Bk) (blk : Block FS ProofFile.Cl)
    (J : LookJobs Ask) (wit : Local W₀ Rc Xi Tr → Ask) (st st' : FS)
    (m : Mid (Local W₀ Rc Xi Tr) Xo) (ds : List Fmt.Drawn)
    (y : List Played × Mid (Local W₀ Rc Xi Tr) Xo) (cols : List OpenedColumn)
    (hA : AtThr.LeftAt 0 k blk Z s J wit st st' m ds y cols) (hp : blk.place = s.at_.place)
    (hLed : ∀ F, (seatOf K3Lot.ofForm s.digits).fork st = some F →
      LedgerIn s.at_.face s.p.first F)
    (hpo : planesOk s.shape s.p.lm = true) (hd : s.digits = false) (v : Wit Cells Tok MsgT)
    (ow : Addr) (base : Due) (Rr : OnBytes.ReqRows) (f : OnBytes.ReqFrame) (S : OnBytes.Statement)
    (tab : Nat → OnBytes.Part → Nat → GE) (o n : Nat)
    (hb : bookFits Bk (Bk.rowsOf 0) (dueAt Bk.first) s.at_ = true)
    (hs : startsFit Bk s.at_ s.p.first ow base = true) (ho : maskOracle f = some o)
    (hS : SenderLays tab o 1 n base.e (fun i => rd ((coinsE (k.look 0 ow).2).getD i zeroE)))
    (hn : s.p.first + s.at_.face.slots ≤ n) (z : P) [R : Request] (hz : rq z = R)
    (hW : AtHead Z s D Lk adr x (wit m.st.input)
      (up (ptsOf s.at_.face s.at_.base (m.st.heard ++ ds)).theta) m.st.heard
      (dataOf Rr f S tab).mask (st'.replyTok?.getD 0) v) (yy : Strs) :
    Mg.worth s.link 3 "planes" (z, st') yy v ∧ Mg.worth s.link 3 "keys" (z, st') yy v ∧
      Mg.worth s.link 3 "rider" (z, st') yy v := by
  subst hz
  letI : Request := rq z
  obtain ⟨h0, ⟨Lf, hL⟩, hM, hC⟩ := hW
  obtain ⟨hsh, hlm, hfirst⟩ := table_head Z s hsite hd hl hx
  obtain ⟨_, w2, w3⟩ := worth_site_dict k blk Z s J wit st st' m ds y cols hA hp
    (FastLaw.sites_ok Z s hsite).1 hLed (FastLaw.sites_ok Z s hsite).2 hpo
    (headNu adr x Z.p.X.H.tl D Lk.rad Lk.oW Lk.wOf Lk.nr Lk.nc
      (fun j => Lk.seat x.link false j.1) Lk.arr Lk.msgW)
    (fun w => Cb.Fo.forK Cb.Gl.E (headLay adr x.fs x.lm x.F.next x.ns Z.p.X.H.tl Lk.nr Lk.nc)
      (st'.replyTok?.getD 0)
      (Cb.Fo.zext (layMu x Z.p.X.H.tl D Lk.rad Lk.oW Lk.wOf Lk.nr Lk.nc
        (fun j => Lk.seat x.link false j.1) Lk.arr Lk.msgW w)))
    v h0 Lf hL ow base Rr f S tab o n hb hs ho hS hn hM
  rw [hd, hsh, hlm, hfirst] at w2 w3
  rw [hl]
  refine ⟨hH "planes" (Or.inl rfl) (z, st') yy v ?_,
    hH "keys" (Or.inr (Or.inl rfl)) (z, st') yy v ?_,
    hH "rider" (Or.inr (Or.inr rfl)) (z, st') yy v ?_⟩
  · show worthHead D Lk adr x Z.p.X.H.tl "planes" st' v False
    unfold worthHead
    rw [if_pos rfl]
    exact w2
  · show worthHead D Lk adr x Z.p.X.H.tl "keys" st' v False
    unfold worthHead
    rw [if_neg (by decide), if_pos rfl]
    exact w3
  · show worthHead D Lk adr x Z.p.X.H.tl "rider" st' v False
    unfold worthHead
    rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
    exact fun g F' _ _ => outRider_of_onCubes _ x.lm x.F.next _ _ hC g F'

/-- **CONDITIONAL, as the file's head lists: all that the row of the lookup on the head's calls
opens.** hW takes the reply's token as the verifier's state has it, 0 where the state has none
(`st'.replyTok?.getD 0`): public; no hypothesis here says that the token is there. No instance of
these hypotheses is exhibited in this file. -/
theorem all_head (L : Letters Bk ProofFile.Cl W₀ Rc Xi Tr Xo P Cells Tok MsgT) (Z : Pub) (s : Site)
    (hsite : s ∈ lookSites Z) (adr : HeadAdr) (rq : P → Request) {x : PlaceL}
    (hx : headAt Z.p.X = some x) (hl : s.link = headLink Z.p.X)
    (hH : ∀ w, HeadSuffices Z.p.X D Lk adr rq x (L.Mg w))
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
    (piece : Nat) (hr : runs s.link 3 "objects" = [(piece, "objects"), (piece, "guests")])
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
    (hW : ∀ ds', letI := rq (L.pubOf y.2.st.input.x)
      AtHead Z s D Lk adr x (wit m.st.input)
        (up (ptsOf s.at_.face s.at_.base (m.st.heard ++ ds)).theta) m.st.heard
        (dataQ (own s.link) a (tabOf (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds')))).mask
        (st'.replyTok?.getD 0) (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds'))) :
    L.thread.Items [Item.formsT s.link 3 "objects", .worth s.link 3 "planes",
      .worth s.link 3 "keys", .worth s.link 3 "rider"] k st' y.2 (En.add y.1) := by
  intro ds'
  letI : Request := rq (L.pubOf y.2.st.input.x)
  obtain ⟨w1, w2, w3⟩ := worth_at_head Z s hsite adr rq hx hl
    (headSuffices_honest (hH y.2.st.input) L.ans L.test) k blk J wit st st' m ds y cols hA hp hLed
    hpo hd _ ow base a.L.check.rows a.L.check.frame a.d.st _ o n hb hs ho (hS ds') hn
    (L.pubOf y.2.st.input.x) rfl (hW ds') (L.thread.strs (En.add y.1))
  refine holds_calls L.N (L.mg y.2.st.input) s.link 3 _ _ _ ?_ w1 w2 w3
  exact formsT_field (L.Mg y.2.st.input) runs Rd St own tabOf wt (hT _) s.link 3 piece hr
    (L.pubOf y.2.st.input.x, st') _ _
    (objectsT_site k blk Z s J wit st st' m ds y cols hA hp (FastLaw.sites_ok Z s hsite).1
      (Rd s.link) St (own s.link) piece _ a hseg hRead hin (hAt _) ow base o n hb hs ho (hS ds') hn)
    (formsTQ_none (Rd s.link) St (own s.link) piece "guests" st' _ hGuests hinG)

#print axioms ProofFile.Honest.K3.Law.Exchange.worth_at_head
#print axioms ProofFile.Honest.K3.Law.Exchange.all_head
#print axioms ProofFile.Honest.K3.Law.Exchange.AtHead

end ProofFile.Honest.K3.Law.Exchange
