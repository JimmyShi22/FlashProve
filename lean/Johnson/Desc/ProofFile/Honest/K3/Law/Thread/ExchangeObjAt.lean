-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ExchangeObjAt.lean: the honest side of the kind "lookup"
(K3): WHERE THE SUB-PROTOCOL AT A LOOKUP OF A PUBLIC PART HAS ACCEPTED, IN THE FIRST CHAIN: THE
LIBRARY'S SENTENCE ON THE FORMS OF THE RUN "objects" AT THE STATE THAT IT LEAVES, in both of the
table of joints' forms. Theorems with proofs; no definition.

It joins `LeftAt` (Honest/K3/Law/Thread/LeftThr.lean) to `objects_of_left` and `objectsQ_of_left`
(Honest/K3/Law/Thread/ExchangeObjects.lean, ExchangeForms.lean), and pays their premise on the
dictionary by `dictAt` (Honest/K3/Law/Thread/DictAt.lean) AT THE SENTENCE'S OWN MASK ROW: the mask
row of the data that the sentence reads off the witness's tables.

  `segAt_fork`      the ledger of the open segment's part is the state's own
  `left_objects`    what both theorems spend of `LeftAt`: at one course: `Left`; the state left
                    holds the heard rows and a ledger later than the one behind the hearing; the
                    dictionary at a mask row that the sender's law names
  `objectsT_site`   in front of the segment's second sending (the lookup on the calls)
  `objectsQ_site`   behind it (the lookup on the digits)

Each of the last two is CONDITIONAL ON `LeftAt` in the first chain; the sub-protocol stands at the
site's place; the site's face is its shape's; a segment is open at the state left; THE READER
ANSWERS WITH THE ROWS OF THE HEARD STRUCTURE THAT THE STATE HOLDS, AND NO LATE SLOT; the public test
for the promise; the book fits the row; the row's slots start where the sender's coins for the mask
row do; THE SENDER LAYS ITS COINS AS THE MASK ROW'S ENTRIES OF THE TABLES THAT THE SENTENCE READS;
in front of the second sending: the stated data keep the mask row.

A coin is read by `getD … zeroE`, in the hypothesis hS. Below s.p.first + s.at_.face.slots entries
the default is never taken where the face has at least two planes and `bookFits` (each entry inside
its owner's coins) and `startsFit` (owner and start) hold: both tests are hypotheses here:
`named_reads` (Honest/K3/Law/BookFence.lean), at a site `named_reads_site`
(Honest/K3/Law/BookFenceSite.lean). n, the number of entries at which hS is asked, has a lower bound
alone.

The table is read through the library's `tabQ` (Johnson/Desc/Sound/FormsQ.lean), which is 0 where
`seatAt own book o` finds no seat: no hypothesis here names `seatAt`; the public test on forms
(`formsIn`, `formsInT`) is what stands beside it.

Limits. The run "guests" is not spoken of here (`formsTQ_none`, `formsQ_none`). No instance of these
hypotheses is exhibited in this file. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeForms
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeReading
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeSite
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.DictAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.Exchange
open OnBytes (E zeroE)
open OnBytes.Model (Fork)
open OnBytes.Slice (GE)
open OnBytes.PscRun (Later)
open VerifiableInference.Desc (Block OpenedColumn)
open VerifiableInference.Desc.K3 (HeardV faceOf)
open VerifiableInference.Desc.K9 (segAt? Readers formsIn formsInT)
open VerifiableInference.Desc.K9L (dataOf maskOracle)
open VerifiableInference.Desc.Sound (formsQ formsTQ dataQ tabQ Stated MsgQ)

local notation "FS" => VerifiableInference.Desc.First.S
local notation "PartK" => VerifiableInference.Desc.K9.Part

/-- The ledger of the open segment's part is the state's own. -/
theorem segAt_fork {s : FS} {a : PartK} (h : segAt? s = some a) : s.fork? = some a.F := by
  unfold segAt? at h
  cases hL : s.link? with
  | none => simp [hL] at h
  | some Lc =>
    cases hF : s.fork? with
    | none => simp [hL, hF] at h
    | some F =>
      cases ht : s.tl? with
      | none => simp [hL, hF, ht] at h
      | some tl =>
        simp only [hL, hF, ht, bind, Option.bind, pure, Option.some.injEq] at h
        rw [← h]

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr Xo : Type}

/-- **What the two theorems below spend of `LeftAt`.** CONDITIONAL ON `LeftAt` in the first chain,
the place, the face, and the three premises on the book and the sender. c: what the book lends the
seated row at the run's own coins (`lendRow`'s return); `CoinsAre` holds of the course at c: both
clauses are LeftAt's own. gV and G stand under "∃" without `hearV`'s return, which LeftAt has:
beside `Left`, which holds of both, gV is pinned in its rows alone and G by the state's ledger up to
planClaimsF. No instance of these hypotheses is exhibited in this file. -/
theorem left_objects (k : Coins Bk) (blk : Block FS ProofFile.Cl) (Z : Pub) (s : Site)
    (J : LookJobs Ask) (wit : Local W₀ Rc Xi Tr → Ask) (st st' : FS)
    (m : Mid (Local W₀ Rc Xi Tr) Xo) (ds : List Fmt.Drawn)
    (y : List Played × Mid (Local W₀ Rc Xi Tr) Xo) (cols : List OpenedColumn)
    (hA : AtThr.LeftAt 0 k blk Z s J wit st st' m ds y cols) (hp : blk.place = s.at_.place)
    (hf : s.at_.face = faceOf s.shape) (ow : Addr) (base : Due) (Rr : OnBytes.ReqRows)
    (f : OnBytes.ReqFrame) (S : OnBytes.Statement) (tab : Nat → OnBytes.Part → Nat → GE)
    (o n : Nat) (hb : bookFits Bk (Bk.rowsOf 0) (dueAt Bk.first) s.at_ = true)
    (hs : startsFit Bk s.at_ s.p.first ow base = true) (ho : maskOracle f = some o)
    (hS : SenderLays tab o 1 n base.e (fun i => rd ((coinsE (k.look 0 ow).2).getD i zeroE)))
    (hn : s.p.first + s.at_.face.slots ≤ n) :
    ∃ (c : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := Local W₀ Rc Xi Tr)
      (X₁ := Xo) ⟨ptsOf, pointsAt⟩ J wit s.at_).parts)
      (c' : (t : Stage) → StageCoins s.at_ t) (gV : HeardV) (G : Fork)
      (g' : OnBytes.Model.Forest.Heard) (cn : Nat),
      lendRow Bk (Bk.rowsOf 0) (k.look 0) s.at_.place
        (proverSideOfLookupInChainAtOneOwner (V₁ := Local W₀ Rc Xi Tr) (X₁ := Xo) ⟨ptsOf, pointsAt⟩ J wit s.at_).parts 0 =
          .ok c ∧
      CoinsAre (V := Unit) (courseAt s.at_ J s.p.first wit m ds c')
        (unlift (X := Xo) (fun (_ : Local W₀ Rc Xi Tr) => ()) wit
          (lookRow ⟨ptsOf, pointsAt⟩ J s.at_) c) ∧
      Left (courseAt s.at_ J s.p.first wit m ds c')
        (Spec.planesOf (siteData s (wit m.st.input) m.st.heard ds))
        (Spec.keysOf (siteData s (wit m.st.input) m.st.heard ds)) gV G ∧
      (seatOf K3Lot.ofForm s.digits).heard st' = some g' ∧ g'.rows = gV.rows ∧
      st'.fork? = some { G with planClaimsF := cn } ∧
      MasksAre (courseAt s.at_ J s.p.first wit m ds c') (dataOf Rr f S tab).mask := by
  obtain ⟨_, _, c, F, g, G, c', hlend, _, _, hQ, hc, _, _, _, hLeft⟩ := hA
  obtain ⟨g', cn, hg, hheard, hfork, _⟩ := oneQ_hands K3Lot.ofForm hQ
  obtain ⟨_, _, _, _, hrows, _⟩ := toHeard_parts hg
  refine ⟨c, c', g, G, g', cn, by rw [← hp]; exact hlend, hc, hLeft, hheard, hrows, ?_, ?_⟩
  · cases hd : s.digits <;> rw [hd] at hfork <;> exact hfork
  · exact (dict_withMasks _ (fun _ => 0) _).1
      (dictAt Bk _ _ _ _ s.at_ J wit s.p.first k m ds c' c ow base Rr f S tab o n
        (withMasks (fun _ => 0) (dataOf Rr f S tab).mask) (by rw [← hp]; exact hlend) hc
        (by rw [hf]; exact (by decide : 2 ≤ 32)) hb hs ho hS hn fun _ _ => rfl)

/-- **CONDITIONAL, as the file's head lists: the forms of the run "objects" are worth 0, in front of
the segment's second sending.** No instance of these hypotheses is exhibited in this file. -/
theorem objectsT_site (k : Coins Bk) (blk : Block FS ProofFile.Cl) (Z : Pub) (s : Site)
    (J : LookJobs Ask) (wit : Local W₀ Rc Xi Tr → Ask) (st st' : FS)
    (m : Mid (Local W₀ Rc Xi Tr) Xo) (ds : List Fmt.Drawn)
    (y : List Played × Mid (Local W₀ Rc Xi Tr) Xo) (cols : List OpenedColumn)
    (hA : AtThr.LeftAt 0 k blk Z s J wit st st' m ds y cols) (hp : blk.place = s.at_.place)
    (hf : s.at_.face = faceOf s.shape) (Rd : Readers) (St : Stated) (own : List (Nat × Nat))
    (piece : Nat) (rd' : Nat × Nat → MsgQ) (a : PartK) (hseg : segAt? st' = some a)
    (hRead : ∀ g', (seatOf K3Lot.ofForm s.digits).heard st' = some g' →
      Rd.forms piece "objects" st' = some { forms := g'.rows.toList, late := [] })
    (hin : formsInT Rd own piece "objects" st' = true)
    (hAt : (St.at1 st' (dataQ own a rd')).mask = (dataQ own a rd').mask) (ow : Addr) (base : Due)
    (o n : Nat) (hb : bookFits Bk (Bk.rowsOf 0) (dueAt Bk.first) s.at_ = true)
    (hs : startsFit Bk s.at_ s.p.first ow base = true)
    (ho : maskOracle a.L.check.frame = some o)
    (hS : SenderLays (tabQ own a.d.st a.d.book rd') o 1 n base.e
      (fun i => rd ((coinsE (k.look 0 ow).2).getD i zeroE)))
    (hn : s.p.first + s.at_.face.slots ≤ n) :
    formsTQ Rd St own piece "objects" st' rd' := by
  obtain ⟨_, c', gV, G, g', cn, _, _, hLeft, hheard, hrows, hfork, hM⟩ :=
    left_objects k blk Z s J wit st st'
    m ds y cols hA hp hf ow base a.L.check.rows a.L.check.frame a.d.st _ o n hb hs ho hS hn
  have hF : a.F = { G with planClaimsF := cn } :=
    Option.some.inj ((segAt_fork hseg).symm.trans hfork)
  refine objects_of_left _ _ _ gV G hLeft Rd St own piece st' rd' a hseg
    (by rw [hF]; exact plan_later G cn) (by rw [← hrows]; exact hRead g' hheard) hin ?_
  rw [hAt]
  exact hM

/-- **CONDITIONAL, as the file's head lists: the forms of the run "objects" are worth 0, behind the
segment's second sending.** No instance of these hypotheses is exhibited in this file. -/
theorem objectsQ_site (k : Coins Bk) (blk : Block FS ProofFile.Cl) (Z : Pub) (s : Site)
    (J : LookJobs Ask) (wit : Local W₀ Rc Xi Tr → Ask) (st st' : FS)
    (m : Mid (Local W₀ Rc Xi Tr) Xo) (ds : List Fmt.Drawn)
    (y : List Played × Mid (Local W₀ Rc Xi Tr) Xo) (cols : List OpenedColumn)
    (hA : AtThr.LeftAt 0 k blk Z s J wit st st' m ds y cols) (hp : blk.place = s.at_.place)
    (hf : s.at_.face = faceOf s.shape) (Rd : Readers) (own : List (Nat × Nat)) (piece : Nat)
    (rd' : Nat × Nat → MsgQ) (a : PartK) (hseg : segAt? st' = some a)
    (hRead : ∀ g', (seatOf K3Lot.ofForm s.digits).heard st' = some g' →
      Rd.forms piece "objects" st' = some { forms := g'.rows.toList, late := [] })
    (hin : formsIn Rd own piece "objects" st' = true) (ow : Addr) (base : Due) (o n : Nat)
    (hb : bookFits Bk (Bk.rowsOf 0) (dueAt Bk.first) s.at_ = true)
    (hs : startsFit Bk s.at_ s.p.first ow base = true)
    (ho : maskOracle a.L.check.frame = some o)
    (hS : SenderLays (tabQ own a.d.st a.d.book rd') o 1 n base.e
      (fun i => rd ((coinsE (k.look 0 ow).2).getD i zeroE)))
    (hn : s.p.first + s.at_.face.slots ≤ n) :
    formsQ Rd own piece "objects" st' rd' := by
  obtain ⟨_, c', gV, G, g', cn, _, _, hLeft, hheard, hrows, hfork, hM⟩ :=
    left_objects k blk Z s J wit st st'
    m ds y cols hA hp hf ow base a.L.check.rows a.L.check.frame a.d.st _ o n hb hs ho hS hn
  have hF : a.F = { G with planClaimsF := cn } :=
    Option.some.inj ((segAt_fork hseg).symm.trans hfork)
  exact objectsQ_of_left _ _ _ gV G hLeft Rd own piece st' rd' a hseg
    (by rw [hF]; exact plan_later G cn) (by rw [← hrows]; exact hRead g' hheard) hin hM

#print axioms ProofFile.Honest.K3.Law.Exchange.segAt_fork
#print axioms ProofFile.Honest.K3.Law.Exchange.left_objects
#print axioms ProofFile.Honest.K3.Law.Exchange.objectsT_site
#print axioms ProofFile.Honest.K3.Law.Exchange.objectsQ_site

end ProofFile.Honest.K3.Law.Exchange
