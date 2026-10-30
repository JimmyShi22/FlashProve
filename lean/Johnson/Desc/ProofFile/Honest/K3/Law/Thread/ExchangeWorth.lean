-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ExchangeWorth.lean: the honest side of the kind "lookup"
(K3): WHERE THE SUB-PROTOCOL AT A LOOKUP OF A PUBLIC PART HAS ACCEPTED, IN THE FIRST CHAIN: THE
FIELD worth OF THE TABLE OF JOINTS at the state that it leaves, at the names "planes" and "keys", at
every filling of the table that says at the lookups' own pieces what the lookups' layer says
(`K3At`). Theorems with proofs; no definition.

It joins `worth_site_dict` (Honest/K3/Law/Thread/ExchangeDict.lean), taken AT THE TABLE'S OWN
READING AND KEY VECTORS, to `mg_digits`, `mg_attention`, `mg_layers`
(Honest/K3/Law/Thread/ExchangeMg.lean).

  `seat_digits`, `seat_calls`   the two seats' readers are the library's readers of the state
  `worth_at_digits`        at the digits' piece of a segment
  `worth_at_attention`     at the calls' piece of an attention segment, "rider" too
  `worth_at_layers`        at the calls' piece of a layers' segment, "rider" too

Each is CONDITIONAL ON the site being one of the public part's; on what `worth_site_dict` asks, at
nu and Kv the table's own; on `K3At`; on what the public data hold at the site's link being there;
at the calls, for "rider": on the caller's arrays being 0 on their cubes. That the site's shape,
packing and first slot are the table's is no premise (Honest/K3/Law/Thread/ExchangeTable.lean).

AMONG THE PREMISES, AT THE WITNESS v OF WHICH THE ITEM IS SAID: the three sentences on a filling at
the table's own reading and key vectors (their part on bits is the tie of cells; their part on keys
the tie of key vectors), and "the reading's mask entries below s.p.first + s.at_.face.slots are the
world's own" (the tie of masks).
They are plain premises here. Stated under names since: `TiedTo` (ExchangeTies.lean, with
`FillsAt.tied`, `tied_layers`, `tied_attention`, `tied_head`, `tied_digits`); `AtDigits`,
`AtAttention`, `AtLayers` (ExchangeOuts.lean).

A coin is read by `getD … zeroE`, in the hypothesis hS. Below s.p.first + s.at_.face.slots entries
the default is never taken where the face has at least two planes and `bookFits` (each entry inside
its owner's coins) and `startsFit` (owner and start) hold: both tests are hypotheses here:
`named_reads` (Honest/K3/Law/BookFence.lean), at a site `named_reads_site`
(Honest/K3/Law/BookFenceSite.lean). n, the number of entries at which hS is asked, has a lower bound
alone.

Limits. The lookup on the head's calls is not reached HERE (Honest/K3/Law/Thread/ExchangeHead.lean,
ExchangeHeadAll.lean). The theorem on the digits speaks of every link at which the public data hold
the place, the head's among them. No instance of these hypotheses is exhibited in this file.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeDict
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeMg
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeRider
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Law.Exchange
open OnBytes (E zeroE)
open OnBytes.Model (Fork HTailF2)
open OnBytes.Slice (GE)
open VerifiableInference.Desc (Block OpenedColumn Strs Wit)
open VerifiableInference.Desc.First (Meaning)
open VerifiableInference.Desc.First.Look (Sent digAt attAt layAt pubAt planesOk enOf mkOf attLay
  layLay attRider layRider)
open VerifiableInference.Desc.K3 (faceOf)
open VerifiableInference.Desc.K9L (dataOf maskOracle)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.OnPublicFiles

local notation "FS" => VerifiableInference.Desc.First.S
local notation "PlaceL" => VerifiableInference.Desc.First.Look.Place
local notation "pieceOf" => VerifiableInference.Desc.K3.pieceAt
local notation "stepAt" => VerifiableInference.Desc.First.Look.stepOf

/-- The digits' seat's readers are the library's readers of the state. -/
theorem seat_digits : (seatOf K3Lot.ofForm true).fork = forkR ∧
    (seatOf K3Lot.ofForm true).heard = heardD := ⟨rfl, rfl⟩

/-- The calls' seat's readers are the library's readers of the state. -/
theorem seat_calls : (seatOf K3Lot.ofForm false).fork = forkR ∧
    (seatOf K3Lot.ofForm false).heard = heardC := ⟨rfl, rfl⟩

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr Xo P Cells Tok : Type} {D : Sent} {Lk : K3Letters Cells Tok}
  {Mg : Meaning P (Wit Cells Tok MsgT)}

/-- **CONDITIONAL, as the file's head lists: at the digits' piece of a segment.** No instance of
these hypotheses is exhibited in this file. -/
theorem worth_at_digits (Z : Pub) (s : Site) (hsite : s ∈ lookSites Z) (hK : K3At Z.p.X D Lk Mg)
    {x : PlaceL} {tl : HTailF2} (hx : digAt Z.p.X s.link = some (x, tl)) (k : Coins Bk)
    (blk : Block FS ProofFile.Cl)
    (J : LookJobs Ask) (wit : Local W₀ Rc Xi Tr → Ask) (st st' : FS)
    (m : Mid (Local W₀ Rc Xi Tr) Xo) (ds : List Fmt.Drawn)
    (y : List Played × Mid (Local W₀ Rc Xi Tr) Xo) (cols : List OpenedColumn)
    (hA : AtThr.LeftAt 0 k blk Z s J wit st st' m ds y cols) (hp : blk.place = s.at_.place)
    (hLed : ∀ F, (seatOf K3Lot.ofForm s.digits).fork st = some F →
      LedgerIn s.at_.face s.p.first F)
    (hd : s.digits = true) (v : Wit Cells Tok MsgT)
    (h0 : digNu x tl D Lk.rad (fun j => Lk.seat x.link true j.1) Lk.arr v .zero = 0) (L : LookIn)
    (hL : FillsAt s (wit m.st.input) L
      (Cb.Fo.forK Cb.Gl.E
        (OnBytes.DgP.digL5 Cb.Gl.E tl (enOf x.arrays) (mkOf x.arrays) x.F.next Unit) ()
        (Cb.Fo.zext (digMu x D Lk.rad (fun j => Lk.seat x.link true j.1) Lk.arr v)))
      (digNu x tl D Lk.rad (fun j => Lk.seat x.link true j.1) Lk.arr v)
      (up (ptsOf s.at_.face s.at_.base (m.st.heard ++ ds)).theta) m.st.heard)
    (ow : Addr) (base : Due) (Rr : OnBytes.ReqRows) (f : OnBytes.ReqFrame) (S : OnBytes.Statement)
    (tab : Nat → OnBytes.Part → Nat → GE) (o n : Nat)
    (hb : bookFits Bk (Bk.rowsOf 0) (dueAt Bk.first) s.at_ = true)
    (hs : startsFit Bk s.at_ s.p.first ow base = true) (ho : maskOracle f = some o)
    (hS : SenderLays tab o 1 n base.e (fun i => rd ((coinsE (k.look 0 ow).2).getD i zeroE)))
    (hn : s.p.first + s.at_.face.slots ≤ n)
    (hMask : ∀ j, j < s.p.first + s.at_.face.slots →
      digNu x tl D Lk.rad (fun j => Lk.seat x.link true j.1) Lk.arr v (.mask j) =
      (dataOf Rr f S tab).mask j) (z : P) (yy : Strs) :
    Mg.worth s.link (pieceOf Z.p.X s.link true) "planes" (z, st') yy v ∧
      Mg.worth s.link (pieceOf Z.p.X s.link true) "keys" (z, st') yy v := by
  obtain ⟨hsh, hlm, hfirst⟩ := table_digits Z s hsite hd hx
  have hpo : planesOk s.shape s.p.lm = true := by
    rw [hlm]
    simp [planesOk]
  obtain ⟨_, w2, w3⟩ := worth_site_dict k blk Z s J wit st st' m ds y cols hA hp
    (FastLaw.sites_ok Z s hsite).1 hLed (FastLaw.sites_ok Z s hsite).2 hpo
    (digNu x tl D Lk.rad (fun j => Lk.seat x.link true j.1) Lk.arr)
    (fun w => Cb.Fo.forK Cb.Gl.E
      (OnBytes.DgP.digL5 Cb.Gl.E tl (enOf x.arrays) (mkOf x.arrays) x.F.next Unit) ()
      (Cb.Fo.zext (digMu x D Lk.rad (fun j => Lk.seat x.link true j.1) Lk.arr w)))
    v h0 L hL ow base Rr f S tab o n hb hs ho hS hn hMask
  rw [hd, hsh, hlm, hfirst] at w2 w3
  refine mg_digits hK s.link hx (z, st') yy v ?_ ?_
  · unfold worthDig
    rw [if_pos rfl]
    exact w2
  · unfold worthDig
    rw [if_neg (by decide), if_pos rfl]
    exact w3

/-- **CONDITIONAL, as the file's head lists: at the calls' piece of an attention segment.** No
instance of these hypotheses is exhibited in this file. -/
theorem worth_at_attention (Z : Pub) (s : Site) (hsite : s ∈ lookSites Z)
    (hK : K3At Z.p.X D Lk Mg) {x : PlaceL} {A : OnBytes.Attention.Shape} {tl : HTailF2}
    (hx : attAt Z.p.X s.link = some (x, A, tl)) (k : Coins Bk) (blk : Block FS ProofFile.Cl)
    (J : LookJobs Ask) (wit : Local W₀ Rc Xi Tr → Ask) (st st' : FS)
    (m : Mid (Local W₀ Rc Xi Tr) Xo) (ds : List Fmt.Drawn)
    (y : List Played × Mid (Local W₀ Rc Xi Tr) Xo) (cols : List OpenedColumn)
    (hA : AtThr.LeftAt 0 k blk Z s J wit st st' m ds y cols) (hp : blk.place = s.at_.place)
    (hLed : ∀ F, (seatOf K3Lot.ofForm s.digits).fork st = some F →
      LedgerIn s.at_.face s.p.first F)
    (hpo : planesOk s.shape s.p.lm = true)
    (hd : s.digits = false) (v : Wit Cells Tok MsgT)
    (h0 : attNu x A tl D Lk.rad (fun j => Lk.seat x.link false j.1) Lk.arr v .zero = 0) (L : LookIn)
    (hL : FillsAt s (wit m.st.input) L
      (Cb.Fo.forK Cb.Gl.E (attLay A x.fs x.lm x.F.next x.ns tl) ()
        (Cb.Fo.zext (attMu x tl D Lk.rad (fun j => Lk.seat x.link false j.1) Lk.arr v)))
      (attNu x A tl D Lk.rad (fun j => Lk.seat x.link false j.1) Lk.arr v)
      (up (ptsOf s.at_.face s.at_.base (m.st.heard ++ ds)).theta) m.st.heard)
    (ow : Addr) (base : Due) (Rr : OnBytes.ReqRows) (f : OnBytes.ReqFrame) (S : OnBytes.Statement)
    (tab : Nat → OnBytes.Part → Nat → GE) (o n : Nat)
    (hb : bookFits Bk (Bk.rowsOf 0) (dueAt Bk.first) s.at_ = true)
    (hs : startsFit Bk s.at_ s.p.first ow base = true) (ho : maskOracle f = some o)
    (hS : SenderLays tab o 1 n base.e (fun i => rd ((coinsE (k.look 0 ow).2).getD i zeroE)))
    (hn : s.p.first + s.at_.face.slots ≤ n)
    (hMask : ∀ j, j < s.p.first + s.at_.face.slots →
      attNu x A tl D Lk.rad (fun j => Lk.seat x.link false j.1) Lk.arr v (.mask j) =
      (dataOf Rr f S tab).mask j)
    (hCube : Cb.Rider.OnCubes (attRider x A tl D Lk.rad Iop.extNone Unit).g
      (attRider x A tl D Lk.rad Iop.extNone Unit).f ()
      (attMs x D Lk.rad (fun j => Lk.seat x.link false j.1) Lk.arr v)) (z : P) (yy : Strs) :
    Mg.worth s.link (pieceOf Z.p.X s.link false) "planes" (z, st') yy v ∧
      Mg.worth s.link (pieceOf Z.p.X s.link false) "keys" (z, st') yy v ∧
      Mg.worth s.link (pieceOf Z.p.X s.link false) "rider" (z, st') yy v := by
  obtain ⟨hsh, hlm, hfirst⟩ := table_attention Z s hsite hd hx
  obtain ⟨_, w2, w3⟩ := worth_site_dict k blk Z s J wit st st' m ds y cols hA hp
    (FastLaw.sites_ok Z s hsite).1 hLed (FastLaw.sites_ok Z s hsite).2 hpo
    (attNu x A tl D Lk.rad (fun j => Lk.seat x.link false j.1) Lk.arr)
    (fun w => Cb.Fo.forK Cb.Gl.E (attLay A x.fs x.lm x.F.next x.ns tl) ()
        (Cb.Fo.zext (attMu x tl D Lk.rad (fun j => Lk.seat x.link false j.1) Lk.arr w)))
    v h0 L hL ow base Rr f S tab o n hb hs ho hS hn hMask
  rw [hd, hsh, hlm, hfirst] at w2 w3
  refine mg_attention hK s.link hx (z, st') yy v ?_ ?_ ?_
  · unfold worthAtt
    rw [if_pos rfl]
    exact w2
  · unfold worthAtt
    rw [if_neg (by decide), if_pos rfl]
    exact w3
  · unfold worthAtt
    rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
    exact worthRider_of_onCubes forkR heardC _ x.lm x.F.next (fun _ => ()) _ st' v hCube

/-- **CONDITIONAL, as the file's head lists: at the calls' piece of a layers' segment.** No instance
of these hypotheses is exhibited in this file. -/
theorem worth_at_layers (Z : Pub) (s : Site) (hsite : s ∈ lookSites Z) (hK : K3At Z.p.X D Lk Mg)
    {x : PlaceL} {tl : HTailF2} (hna : attAt Z.p.X s.link = none)
    (hx : layAt Z.p.X s.link = some x)
    (ht : VerifiableInference.Desc.First.Look.tlAt Z.p.X s.link = some tl) (k : Coins Bk)
    (blk : Block FS ProofFile.Cl)
    (J : LookJobs Ask) (wit : Local W₀ Rc Xi Tr → Ask) (st st' : FS)
    (m : Mid (Local W₀ Rc Xi Tr) Xo) (ds : List Fmt.Drawn)
    (y : List Played × Mid (Local W₀ Rc Xi Tr) Xo) (cols : List OpenedColumn)
    (hA : AtThr.LeftAt 0 k blk Z s J wit st st' m ds y cols) (hp : blk.place = s.at_.place)
    (hLed : ∀ F, (seatOf K3Lot.ofForm s.digits).fork st = some F →
      LedgerIn s.at_.face s.p.first F)
    (hpo : planesOk s.shape s.p.lm = true)
    (hd : s.digits = false) (v : Wit Cells Tok MsgT)
    (h0 : layNu x (pubAt Z.p.X (s.link / stepAt Z.p.X)) tl D Lk.rad Lk.oW Lk.wOf Lk.nr Lk.nc
      (fun j => Lk.seat x.link false j.1) Lk.arr Lk.msgW v .zero = 0) (L : LookIn)
    (hL : FillsAt s (wit m.st.input) L
      (Cb.Fo.forK Cb.Gl.E
        (layLay (pubAt Z.p.X (s.link / stepAt Z.p.X)) x.fs x.lm x.F.next x.ns tl Lk.nr Lk.nc) ()
        (Cb.Fo.zext (layMu x tl D Lk.rad Lk.oW Lk.wOf Lk.nr Lk.nc
          (fun j => Lk.seat x.link false j.1) Lk.arr Lk.msgW v)))
      (layNu x (pubAt Z.p.X (s.link / stepAt Z.p.X)) tl D Lk.rad Lk.oW Lk.wOf Lk.nr Lk.nc
      (fun j => Lk.seat x.link false j.1) Lk.arr Lk.msgW v)
      (up (ptsOf s.at_.face s.at_.base (m.st.heard ++ ds)).theta) m.st.heard)
    (ow : Addr) (base : Due) (Rr : OnBytes.ReqRows) (f : OnBytes.ReqFrame) (S : OnBytes.Statement)
    (tab : Nat → OnBytes.Part → Nat → GE) (o n : Nat)
    (hb : bookFits Bk (Bk.rowsOf 0) (dueAt Bk.first) s.at_ = true)
    (hs : startsFit Bk s.at_ s.p.first ow base = true) (ho : maskOracle f = some o)
    (hS : SenderLays tab o 1 n base.e (fun i => rd ((coinsE (k.look 0 ow).2).getD i zeroE)))
    (hn : s.p.first + s.at_.face.slots ≤ n)
    (hMask : ∀ j, j < s.p.first + s.at_.face.slots →
      layNu x (pubAt Z.p.X (s.link / stepAt Z.p.X)) tl D Lk.rad Lk.oW Lk.wOf Lk.nr Lk.nc
      (fun j => Lk.seat x.link false j.1) Lk.arr Lk.msgW v (.mask j) =
      (dataOf Rr f S tab).mask j)
    (hCube : Cb.Rider.OnCubes
      (layRider x (pubAt Z.p.X (s.link / stepAt Z.p.X)) tl D Lk.rad Lk.oW Lk.wOf Lk.nr Lk.nc
        Iop.extNone Unit).g
      (layRider x (pubAt Z.p.X (s.link / stepAt Z.p.X)) tl D Lk.rad Lk.oW Lk.wOf Lk.nr Lk.nc
        Iop.extNone Unit).f ()
      (layMs x D Lk.rad Lk.oW (fun j => Lk.seat x.link false j.1) Lk.arr Lk.msgW v)) (z : P)
    (yy : Strs) :
    Mg.worth s.link (pieceOf Z.p.X s.link false) "planes" (z, st') yy v ∧
      Mg.worth s.link (pieceOf Z.p.X s.link false) "keys" (z, st') yy v ∧
      Mg.worth s.link (pieceOf Z.p.X s.link false) "rider" (z, st') yy v := by
  obtain ⟨hsh, hlm, hfirst⟩ := table_layers Z s hsite hd hx
  obtain ⟨_, w2, w3⟩ := worth_site_dict k blk Z s J wit st st' m ds y cols hA hp
    (FastLaw.sites_ok Z s hsite).1 hLed (FastLaw.sites_ok Z s hsite).2 hpo
    (layNu x (pubAt Z.p.X (s.link / stepAt Z.p.X)) tl D Lk.rad Lk.oW Lk.wOf Lk.nr Lk.nc
      (fun j => Lk.seat x.link false j.1) Lk.arr Lk.msgW)
    (fun w => Cb.Fo.forK Cb.Gl.E
        (layLay (pubAt Z.p.X (s.link / stepAt Z.p.X)) x.fs x.lm x.F.next x.ns tl Lk.nr Lk.nc) ()
        (Cb.Fo.zext (layMu x tl D Lk.rad Lk.oW Lk.wOf Lk.nr Lk.nc
          (fun j => Lk.seat x.link false j.1) Lk.arr Lk.msgW w)))
    v h0 L hL ow base Rr f S tab o n hb hs ho hS hn hMask
  rw [hd, hsh, hlm, hfirst] at w2 w3
  refine mg_layers hK s.link hna hx ht (z, st') yy v ?_ ?_ ?_
  · unfold worthLay
    rw [if_pos rfl]
    exact w2
  · unfold worthLay
    rw [if_neg (by decide), if_pos rfl]
    exact w3
  · unfold worthLay
    rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
    exact worthRider_of_onCubes forkR heardC _ x.lm x.F.next (fun _ => ()) _ st' v hCube

#print axioms ProofFile.Honest.K3.Law.Exchange.seat_digits
#print axioms ProofFile.Honest.K3.Law.Exchange.seat_calls
#print axioms ProofFile.Honest.K3.Law.Exchange.worth_at_digits
#print axioms ProofFile.Honest.K3.Law.Exchange.worth_at_attention
#print axioms ProofFile.Honest.K3.Law.Exchange.worth_at_layers

end ProofFile.Honest.K3.Law.Exchange
