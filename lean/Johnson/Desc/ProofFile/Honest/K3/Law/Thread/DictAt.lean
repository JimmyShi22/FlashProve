-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/DictAt.lean: the honest side of the kind "lookup" (K3):
FROM THE FIRST CHAIN's LENDING TO THE DICTIONARY (Exchange.Dict,
Honest/K3/Law/Thread/ExchangeRows.lean): under the lookup's slots the mask entries of the world in
which the library reads a segment's forms are the coins that the course's stages spent. Two
statements and their proofs.

  DictAt, dictAt       **the statement and its proof**, at a lookup's public data
  left_dict            the same behind the member's acceptance at a lookup of a public part: it
                       opens LeftAt (Honest/K3/Law/Thread/LeftThr.lean) and hands out, at ONE
                       course, the hearing, the tie of the state behind to it, Left
                       and the dictionary

The road. The lending is a function, so the coins that the thread's run was lent are those of which
Honest/K3/Law/RowLends.lean speaks (rowLendsFirst); a seated row's parts spend what the row's parts
spend (rowSpent_unlift); then Honest/K3/Law/MasksWorld.lean (masksWorldBook).

A coin is read by `getD … zeroE`, in the hypothesis hS. Below s.p.first + s.at_.face.slots entries
the default is never taken where the face has at least two planes and `bookFits` (each entry inside
its owner's coins) and `startsFit` (owner and start) hold: both tests are hypotheses here:
`named_reads` (Honest/K3/Law/BookFence.lean), at a site `named_reads_site`
(Honest/K3/Law/BookFenceSite.lean). n, the number of entries at which hS is asked, has a lower bound
alone.

Limits. CONDITIONAL ON bookFits, startsFit (tests with code on a book that another hand makes) AND
SenderLays at one mask row (the law of the part that sends the mask rows). THE TWO TESTS ARE PAID BY
NO THEOREM: Honest/K3/Law/BookAtSites.lean [not in this library] lays them at a book that other
writers' maker makes of a description, for a program to evaluate. SenderLays IS NOT SHOWN HERE, nor
that the book's base.e is the number at which the sender lays the row. Instances of each by itself,
on made-up data: Honest/K3/Law/RowLendsToy.lean [not in this library], MasksBookToy.lean
[not in this library], MaskTests.lean [not in this library]; no instance of all hypotheses together
is exhibited in this file or these. That the table tab is what the sender holds as sent, and that a
reading's mask entries below first + a.face.slots are the world's own, are premises.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.MasksWorld
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.LeftThr
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes (E zeroE)
open OnBytes.Slice (GE)
open OnBytes.Model (Fork)
open VerifiableInference.Desc (Block OpenedColumn)
open VerifiableInference.Desc.K3 (HeardV hearV)
open VerifiableInference.Desc.K9L (dataOf maskOracle)

/-- **CONDITIONAL ON bookFits, startsFit AND SenderLays AT ONE MASK ROW: FROM THE FIRST CHAIN's
LENDING TO THE DICTIONARY.** a, J, wit, first: a lookup's public data, summands, reader of the
input, first slot. c: coins that the book has lent the seated row in the first chain, at a run's
coins k. c': coins by stage that are the row's (CoinsAre, as the laws on the play give them). ow,
base: the part that sends the segment's mask row, and where among its coins that row's entries
begin, in both fields' counts; ITS COINS ARE LOOKED UP IN THE FIRST CHAIN's OWN PURSE: a part of
another chain has none there. tab, o, n: the tables of which the world's data are made; the
segment's first message with mask rows; for how many entries the sender's law is at hand. ν: a
reading whose mask entries are the world's own at every j below first + a.face.slots: `MasksAre`
reads no slot from there on (`masksAre_congr`). Then the dictionary holds of the course that the
play is. THE THREE TESTS AND LAWS NAMED FIRST ARE PREMISES THAT OTHER HANDS PAY: the two tests
by no theorem: only where a program evaluates them at a description's book
(Honest/K3/Law/BookAtSites.lean [not in this library]); SenderLays: not shown here. A lemma's
statement, none of the library's goals. -/
def DictAt : Prop :=
  ∀ (Bk : ProverCoinCounts) (V₁ W₁ X₁ W : Type) (a : At) (J : LookJobs W) (wit : W₁ → W) (first : Nat)
    (k : Coins Bk) (m : Mid W₁ X₁) (ds : List Fmt.Drawn) (c' : (t : Stage) → StageCoins a t)
    (c : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) ⟨ptsOf, pointsAt⟩ J wit a).parts)
    (ow : Addr) (base : Due) (Rr : OnBytes.ReqRows) (f : OnBytes.ReqFrame) (S : OnBytes.Statement)
    (tab : Nat → OnBytes.Part → Nat → GE) (o n : Nat) (ν : _root_.Fo.Pl → GE),
    lendRow Bk (Bk.rowsOf 0) (k.look 0) a.place
      (proverSideOfLookupInChainAtOneOwner (V₁ := V₁) (X₁ := X₁) ⟨ptsOf, pointsAt⟩ J wit a).parts 0 = .ok c →
    CoinsAre (V := Unit) (courseAt a J first wit m ds c')
      (unlift (X := X₁) (fun (_ : V₁) => ()) wit (lookRow ⟨ptsOf, pointsAt⟩ J a) c) →
    2 ≤ a.face.planes →
    bookFits Bk (Bk.rowsOf 0) (dueAt Bk.first) a = true → startsFit Bk a first ow base = true →
    maskOracle f = some o →
    SenderLays tab o 1 n base.e (fun i => rd ((coinsE (k.look 0 ow).2).getD i zeroE)) →
    first + a.face.slots ≤ n →
    (∀ j, j < first + a.face.slots → ν (.mask j) = (dataOf Rr f S tab).mask j) →
    Exchange.Dict (courseAt a J first wit m ds c') ν

/-- **DictAt.** -/
theorem dictAt : DictAt := by
  intro Bk V₁ W₁ X₁ W a J wit first k m ds c' c ow base Rr f S tab o n ν hl hc h2 hb hs ho hS hn hν
  obtain ⟨c₀, h0, hsp⟩ := rowLendsFirst V₁ W₁ X₁ W J wit a Bk hb k
  obtain rfl : c₀ = c := Except.ok.inj (h0.symm.trans hl)
  have e : (fun x => (k.look 0 x).1) = dueAt Bk.first := funext (look_due_first Bk k)
  have hm := masksWorldBook W (courseAt a J first wit m ds c') Bk (Bk.rowsOf 0) (k.look 0) ow base
    (unlift (X := X₁) (fun (_ : V₁) => ()) wit (lookRow ⟨ptsOf, pointsAt⟩ J a) c₀) Rr f S tab o n h2
    (by rw [e]; exact hb) hs
    ((rowSpent_unlift (X := X₁) (fun (_ : V₁) => ()) wit (lookRow ⟨ptsOf, pointsAt⟩ J a) c₀).trans
      hsp) hc ho hS hn
  show MasksAre _ fun j => ν (.mask j)
  exact masksAre_congr (courseAt a J first wit m ds c') h2 (dataOf Rr f S tab).mask _ hν hm

section
local notation "FS" => VerifiableInference.Desc.First.S

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr Xo : Type}

/-- **CONDITIONAL ON THE SAME THREE: behind the member's acceptance at a lookup of a public part**,
in the first chain: at ONE course: the hearing has returned on the played rounds, the state that the
member's step leaves is tied to what was heard (OneQ), Left holds, and the dictionary holds. c: what
the book lends the seated row at the run's own coins (`lendRow`'s return); `CoinsAre` holds of the
course at c: both clauses are LeftAt's own. It opens LeftAt; hp: the member stands at the site's
place. No instance of these hypotheses is exhibited in this file. -/
theorem left_dict (k : Coins Bk) (blk : Block FS ProofFile.Cl) (Z : Pub) (s : Site) (J : LookJobs Ask)
    (wit : Local W₀ Rc Xi Tr → Ask) (st st' : FS) (m : Mid (Local W₀ Rc Xi Tr) Xo)
    (ds : List Fmt.Drawn) (y : List Played × Mid (Local W₀ Rc Xi Tr) Xo) (cols : List OpenedColumn)
    (h : AtThr.LeftAt 0 k blk Z s J wit st st' m ds y cols) (hp : blk.place = s.at_.place)
    (ow : Addr) (base : Due) (Rr : OnBytes.ReqRows) (f : OnBytes.ReqFrame) (S : OnBytes.Statement)
    (tab : Nat → OnBytes.Part → Nat → GE) (o n : Nat) (ν : _root_.Fo.Pl → GE)
    (h2 : 2 ≤ s.at_.face.planes)
    (hb : bookFits Bk (Bk.rowsOf 0) (dueAt Bk.first) s.at_ = true)
    (hs : startsFit Bk s.at_ s.p.first ow base = true) (ho : maskOracle f = some o)
    (hS : SenderLays tab o 1 n base.e (fun i => rd ((coinsE (k.look 0 ow).2).getD i zeroE)))
    (hn : s.p.first + s.at_.face.slots ≤ n)
    (hν : ∀ j, j < s.p.first + s.at_.face.slots → ν (.mask j) = (dataOf Rr f S tab).mask j) :
    ∃ (c : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := Local W₀ Rc Xi Tr)
      (X₁ := Xo) ⟨ptsOf, pointsAt⟩ J wit s.at_).parts)
      (F : Fork) (g : HeardV) (G : Fork) (c' : (t : Stage) → StageCoins s.at_ t),
      lendRow Bk (Bk.rowsOf 0) (k.look 0) s.at_.place
        (proverSideOfLookupInChainAtOneOwner (V₁ := Local W₀ Rc Xi Tr) (X₁ := Xo) ⟨ptsOf, pointsAt⟩ J wit s.at_).parts 0 =
          .ok c ∧
      CoinsAre (V := Unit) (courseAt s.at_ J s.p.first wit m ds c')
        (unlift (X := Xo) (fun (_ : Local W₀ Rc Xi Tr) => ()) wit
          (lookRow ⟨ptsOf, pointsAt⟩ J s.at_) c) ∧
      (seatOf K3Lot.ofForm s.digits).fork st = some F ∧
      hearV s.at_.face F (roundsOf y.1) = some (g, G) ∧
      OneQ K3Lot.ofForm Z.p.X s.link s.digits s.shape st st' g G ∧
      Left (courseAt s.at_ J s.p.first wit m ds c')
        (Spec.planesOf (siteData s (wit m.st.input) m.st.heard ds))
        (Spec.keysOf (siteData s (wit m.st.input) m.st.heard ds)) g G ∧
      Exchange.Dict (courseAt s.at_ J s.p.first wit m ds c') ν := by
  obtain ⟨_, _, c, F, g, G, c', hl, hF, hh, hQ, hc, _, _, _, hLeft⟩ := h
  rw [hp] at hl
  exact ⟨c, F, g, G, c', hl, hc, hF, hh, hQ, hLeft,
    dictAt Bk _ _ _ _ s.at_ J wit s.p.first k m ds c' c ow base Rr f S tab o n ν hl hc h2 hb hs ho
      hS hn hν⟩

end

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.dictAt
#print axioms ProofFile.Honest.K3.Law.left_dict
#print axioms ProofFile.Honest.K3.Law.DictAt
