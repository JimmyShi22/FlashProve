-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ExchangeDict.lean: the honest side of the kind "lookup"
(K3): `worth_site_fill` (Honest/K3/Law/Thread/ExchangeFill.lean) WITH ITS PREMISE ON THE DICTIONARY
PAID by `dictAt` (Honest/K3/Law/Thread/DictAt.lean), in the first chain. One theorem with its
proof; no definition.

  `worth_site_dict`   CONDITIONAL ON `LeftAt` in the first chain; the sub-protocol stands at the
                      site's place; the ledger in front as the lookup's laws ask it; public
                      tests; the three sentences on a filling (`FillsAt`,
                      Honest/K3/Law/Thread/ExchangeFillAt.lean) at nu w and Kv w; nu w reads 0 at
                      the place "zero"; AND, FOR THE DICTIONARY: the book fits the row; the
                      row's slots start where the sender's coins for the mask row do; the sender
                      lays its coins as the mask row's entries; nu w's mask entries below
                      s.p.first + s.at_.face.slots are those of the world's data: at the state
                      st' that the sub-protocol leaves:
                      `K3Objects`, `K3WorthPlanes`, `K3WorthKeys`

The sender's law is asked at all entries below n, and reads a coin beyond the sender's own as 0: so
whoever pays it must bound n by the sender's coins. The stretches that the book lends the lookup's
row lie inside their owner's coins: that is a clause of the book's test.

A coin is read by `getD … zeroE`, in the hypothesis hS. Below s.p.first + s.at_.face.slots entries
the default is never taken where the face has at least two planes and `bookFits` (each entry inside
its owner's coins) and `startsFit` (owner and start) hold: both tests are hypotheses here:
`named_reads` (Honest/K3/Law/BookFence.lean), at a site `named_reads_site`
(Honest/K3/Law/BookFenceSite.lean). n, the number of entries at which hS is asked, has a lower bound
alone.

Limits. The three premises on the book and the sender are paid at no proof file's description. That
the table of joints' own reading and key vectors are nu w and Kv w as asked is shown nowhere here.
No instance of these hypotheses is exhibited in this file.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeFillAt
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.DictAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.Exchange
open OnBytes (E zeroE)
open OnBytes.Model (Fork)
open OnBytes.Slice (GE)
open VerifiableInference.Desc (Block OpenedColumn)
open VerifiableInference.Desc.K3 (faceOf)
open VerifiableInference.Desc.K9L (dataOf maskOracle)
open VerifiableInference.Desc.First.Look (planesOk)
open VerifiableInference.OnPublicFiles (K3Objects K3WorthPlanes K3WorthKeys)

local notation "FS" => VerifiableInference.Desc.First.S

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr Xo Wt : Type}

/-- **CONDITIONAL, as the file's head lists: where the sub-protocol at a lookup of a public part has
accepted, in the first chain, at the state that it leaves: the three items of the library's row
out, the dictionary paid from the book's lending.** No instance of these hypotheses is exhibited in
this file. -/
theorem worth_site_dict (k : Coins Bk) (blk : Block FS ProofFile.Cl) (Z : Pub) (s : Site)
    (J : LookJobs Ask) (wit : Local W₀ Rc Xi Tr → Ask) (st st' : FS)
    (m : Mid (Local W₀ Rc Xi Tr) Xo) (ds : List Fmt.Drawn)
    (y : List Played × Mid (Local W₀ Rc Xi Tr) Xo) (cols : List OpenedColumn)
    (hA : AtThr.LeftAt 0 k blk Z s J wit st st' m ds y cols) (hp : blk.place = s.at_.place)
    (hf : s.at_.face = faceOf s.shape)
    (hLed : ∀ F, (seatOf K3Lot.ofForm s.digits).fork st = some F →
      LedgerIn s.at_.face s.p.first F)
    (hok : FoNums.ok s.shape = true) (hpo : planesOk s.shape s.p.lm = true)
    (nu : Wt → _root_.Fo.Pl → GE) (Kv : Wt → Nat → Nat → GE) (w : Wt)
    (h0 : nu w .zero = 0) (L : LookIn)
    (hL : FillsAt s (wit m.st.input) L (Kv w) (nu w)
      (up (ptsOf s.at_.face s.at_.base (m.st.heard ++ ds)).theta) m.st.heard)
    (ow : Addr) (base : Due) (Rr : OnBytes.ReqRows) (f : OnBytes.ReqFrame) (S : OnBytes.Statement)
    (tab : Nat → OnBytes.Part → Nat → GE) (o n : Nat)
    (hb : bookFits Bk (Bk.rowsOf 0) (dueAt Bk.first) s.at_ = true)
    (hs : startsFit Bk s.at_ s.p.first ow base = true) (ho : maskOracle f = some o)
    (hS : SenderLays tab o 1 n base.e (fun i => rd ((coinsE (k.look 0 ow).2).getD i zeroE)))
    (hn : s.p.first + s.at_.face.slots ≤ n)
    (hν : ∀ j, j < s.p.first + s.at_.face.slots → nu w (.mask j) = (dataOf Rr f S tab).mask j) :
    K3Objects (seatOf K3Lot.ofForm s.digits).fork (seatOf K3Lot.ofForm s.digits).heard s.shape
        s.p.lm s.p.first nu st' w ∧
      K3WorthPlanes (seatOf K3Lot.ofForm s.digits).fork (seatOf K3Lot.ofForm s.digits).heard
        s.shape s.p.lm s.p.first nu st' w ∧
      K3WorthKeys (seatOf K3Lot.ofForm s.digits).fork (seatOf K3Lot.ofForm s.digits).heard
        s.shape s.p.lm s.p.first nu Kv st' w :=
  worth_site_fill 0 k blk Z s J wit st st' m ds y cols hA hf hLed hok hpo nu Kv w h0 L hL.reads
    hL.keys hL.bits fun c c' hl hc =>
      dictAt Bk _ _ _ _ s.at_ J wit s.p.first k m ds c' c ow base Rr f S tab o n (nu w)
        (by rw [← hp]; exact hl) hc (by rw [hf]; exact (by decide : 2 ≤ 32)) hb hs ho hS hn hν

#print axioms ProofFile.Honest.K3.Law.Exchange.worth_site_dict

end ProofFile.Honest.K3.Law.Exchange
