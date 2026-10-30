-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ExchangeCallsAll.lean: the honest side of the kind
"lookup" (K3): THE PREMISES THAT SPEAK OF A RUN, at a lookup on the calls, UNDER ONE NAME: what
`all_attention`, `all_layers` (ExchangeAll.lean) and `all_head` (ExchangeHeadAll.lean) ask of the
state that the member leaves, of the book and of the Script's witness, and what `left_thr_fast`
(LeftThr.lean) asks of the input: asked at every step on the first chain's thread at a number b. One
definition; one theorem. The first chain's letters are a variable.

NOT IN FRONT OF A LAW OVER COINS. The definition binds a run's coins k inside, behind `ThrS` and the
member's step, with Said a letter for a predicate on the coins: a condition on the run's coins. Its
clauses say what the Script's witness and the hidden input are at these coins.

Why. The frame asks a house for shares of the exchange item by item, at every step on the thread
(`ExchangeAtS`, Honest/Thread/SharesS.lean). The three laws named above speak at one step. At the
digits `DigitsRunAll` (ExchangeDigitsAll.lean) gathers the like premises. This is its fellow at the
calls.

What is shown.
  `CallsRunAll`: (definition) the text of `DigitsRunAll` with four turns. It is asked from `ThrS`,
    the invariant together with a family Said (Honest/Thread/Said.lean), not from `Thr` alone: the
    weaker premise. The public test on forms is `formsInT`. The letters D, Lk, x, tl are gone. The
    last clause is a letter, At: the premises at one witness; it is handed the input and the state
    that the member leaves too, which the clause at the head's calls reads.
  `CallsRunAll.imp`: the definition goes along an implication between two such letters.

The twelve clauses, and the binder of the three laws that each is. Two of `left_thr_fast`: hSet (the
input no longer moves), hM (the relation after the challenge). Ten of the three laws, in their
order: hseg (a segment is open), hRead and hGuests (the readers' two answers), hin and hinG (the
public test at both runs), hb and hs (two tests on the book), ho (the mask row's message), hS (the
sender's law, at each continuation's tables), hW (At, at each continuation's witness).
`SenderLays` is asked at s.p.first + s.at_.face.slots entries: no more.

Hypotheses that remain. `CallsRunAll.imp`: the bundle at At, and the implication.

Imported. ExchangeAll.lean in this folder; Honest/Thread/Said.lean, of the frame's authors.

Users. ExchangeOpensCallsAtHead.lean in this folder.

Limits. A definition, meant as a hypothesis. Every clause is a premise of a law of this folder,
moved under a name: none is shown of any run, Script or prover. Nothing shows that the twelve can
hold together at a step, or that the thread holds at any run: where `ThrS` and the step are never
met the definition holds emptily.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeAll
import Johnson.Desc.ProofFile.Honest.Thread.Said

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Law.Exchange
open OnBytes (zeroE)
open OnBytes.Slice (GE)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.K9 (segAt? Readers formsInT)
open VerifiableInference.Desc.K9L (maskOracle)
open VerifiableInference.Desc.Sound (MsgT MsgQ dataQ tabQ)
open ProofFile.Honest.FirstThread (Letters)
open ProofFile.Honest.K3.Law.AtThr

local notation "FS" => VerifiableInference.Desc.First.S
local notation "PartK" => VerifiableInference.Desc.K9.Part

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr Xo P Cells Tok : Type}
  (L : Letters Bk ProofFile.Cl W₀ Rc Xi Tr Xo P Cells Tok MsgT)

/-- **THE PREMISES THAT SPEAK OF A RUN**, at every run that the frame's share binds at the member
number b, at a lookup on the calls. A definition, meant as a hypothesis: no file shows it of any
run, Script or prover. It is asked from `ThrS`: the invariant together with the family Said. Rd,
own, tabOf: the readers, the seats and the tables of the field's text. piece: the number under which
the two runs stand. At: the premises at one witness, by the sort of the link; it is handed the input
and the state that the member leaves too. ow and base stand under "there are": whichever owner and
start the test `startsFit` accepts; the test holds them against the book's own entries at the row's
parts; no lemma says that it accepts one pair alone. `SenderLays` is asked at s.p.first +
s.at_.face.slots entries: no more. A coin is read by `getD … zeroE`. Three things together bar the
default at these entries: s is one of `lookSites`, whence its face has two planes or more
(`planes_site`); `bookFits` (each entry inside its owner's coins); `startsFit` (owner and start):
`named_reads_site` (Honest/K3/Law/BookFenceSite.lean), over `named_reads` and `tests_fence`
(BookFence.lean). THE TWO TESTS ARE CLAUSES OF THIS DEFINITION: asked with the rest, not taken as
shown. THE MEMBERSHIP IS NO CLAUSE OF IT: s is any `Site` here; the laws that take the definition
ask it of their own (hsite). The table is read through the library's `tabQ`
(Johnson/Desc/Sound/FormsQ.lean), which is 0 where `seatAt own book o` finds no seat: no clause here
names `seatAt`; the public test on forms (`formsInT`) is what stands beside it. Read, not shown in
this file: at such a state the clause SenderLays can hold only where the
first + slots coins that it names all read 0: it is then paid at no honest run. THE ROW: this
definition names no row of the prover's; the laws that take it stand at the row `proverSideOfLookupInChainAtOneOwner`
(the field half of `SiteRest`; `LeftAt`), not at a row that passes its tables on. -/
def CallsRunAll (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) Xo → Prop) (b : Nat) (s : Site)
    (wit : Local W₀ Rc Xi Tr → Ask) (Rd : Nat → Readers) (own : Nat → List (Nat × Nat))
    (tabOf : Wit Cells Tok MsgT → Nat × Nat → MsgQ) (piece : Nat)
    (At : Local W₀ Rc Xi Tr → FS → Ask → GE → List Fmt.Drawn → (Nat → GE) →
      Wit Cells Tok MsgT → Prop) : Prop :=
  ∀ blk, L.thread.bs[b]? = some blk → ∀ k st m En ds y cols st',
    ThrS L.thread Said b k st m En →
    drawsFit blk.rounds ds = true → L.thread.Stepped blk k st m En ds y cols st' →
    Ask.Settled s.at_.base (wit m.st.input) ∧ (siteData s (wit m.st.input) m.st.heard ds).Mid ∧
    ∃ (a : PartK) (ow : Addr) (base : Due) (o : Nat), segAt? st' = some a ∧
      (∀ g', (seatOf K3Lot.ofForm s.digits).heard st' = some g' →
        (Rd s.link).forms piece "objects" st' = some { forms := g'.rows.toList, late := [] }) ∧
      (Rd s.link).forms piece "guests" st' = some { forms := [], late := [] } ∧
      formsInT (Rd s.link) (own s.link) piece "objects" st' = true ∧
      formsInT (Rd s.link) (own s.link) piece "guests" st' = true ∧
      bookFits Bk (Bk.rowsOf 0) (dueAt Bk.first) s.at_ = true ∧
      startsFit Bk s.at_ s.p.first ow base = true ∧ maskOracle a.L.check.frame = some o ∧
      (∀ ds', SenderLays
        (tabQ (own s.link) a.d.st a.d.book
          (tabOf (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds'))))
        o 1 (s.p.first + s.at_.face.slots) base.e
        (fun i => rd ((coinsE (k.look 0 ow).2).getD i zeroE))) ∧
      ∀ ds', At y.2.st.input st' (wit m.st.input)
        (up (ptsOf s.at_.face s.at_.base (m.st.heard ++ ds)).theta) m.st.heard
        (dataQ (own s.link) a (tabOf (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds')))).mask
        (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds'))

variable {L}

/-- The bundle goes along an implication between two letters for the premises at one witness. -/
theorem CallsRunAll.imp {Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr) Xo → Prop} {b : Nat}
    {s : Site} {wit : Local W₀ Rc Xi Tr → Ask} {Rd : Nat → Readers}
    {own : Nat → List (Nat × Nat)} {tabOf : Wit Cells Tok MsgT → Nat × Nat → MsgQ} {piece : Nat}
    {At At' : Local W₀ Rc Xi Tr → FS → Ask → GE → List Fmt.Drawn → (Nat → GE) →
      Wit Cells Tok MsgT → Prop}
    (hRun : CallsRunAll L Said b s wit Rd own tabOf piece At)
    (hi : ∀ w' t a θ hd mk v, At w' t a θ hd mk v → At' w' t a θ hd mk v) :
    CallsRunAll L Said b s wit Rd own tabOf piece At' := by
  intro blk hblk k st m En ds y cols st' hA hdr hSt
  obtain ⟨hSet, hM, a, ow, base, o, h0, h1, h2, h3, h4, h5, h6, h7, hS, hW⟩ :=
    hRun blk hblk k st m En ds y cols st' hA hdr hSt
  exact ⟨hSet, hM, a, ow, base, o, h0, h1, h2, h3, h4, h5, h6, h7, hS,
    fun ds' => hi _ _ _ _ _ _ _ (hW ds')⟩

end ProofFile.Honest.K3.Law.Exchange

#print axioms ProofFile.Honest.K3.Law.Exchange.CallsRunAll.imp
