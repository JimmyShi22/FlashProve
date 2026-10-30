-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/Law/MaskAtHead.lean: THE OUTPUT HEAD'S OWN ROUNDS: THE FIELD
maskTie OF K6Script (Law/OutAtThread.lean) FROM THE FRAME'S OWN LEMMA ON THE MASK'S TIE, AT A THREAD
AND AT THE FIRST CHAIN'S THREAD AT THE LIBRARY'S HEAD, BORDER 341.
WHAT IT IS NOT. CONDITIONAL ON EIGHT PREMISES. SEVEN ARE OTHER AUTHORS': h2, ho, hin, hS, hF and
hfree as they stand in Honest/Law/Rule/TiesFree.lean's maskTieOn_whole_free, and h3 IN A WEAKER FORM
THAN THERE: asked at the numbers below the free entries AND below a further letter lim. THE EIGHTH
IS NEW HERE: hlim: the member's slots lie below lim. WHY: a reader that is cut (the library's reads
0 from the head's plan's own number of entries on) could meet h3 at every number below the free
entries only where the sender's coins beyond the cut read as 0; so the lemma called is one that
takes a predicate on the numbers (Honest/Law/Rule/TiesLen.lean:
maskTieOn_whole), at "below free and below lim"; h2 and hin go down to it (SenderLaysOwn.mono);
hfree and hlim together pay its last binder. The first theorem has a ninth premise (on the ledger's
next number, in another form of the same authors'); at the library's head that one is paid, under
the hypothesis h: the last theorem has the eight and h. NONE IS SHOWN HERE OF ANY THREAD. What their
authors say of the seven, one by one (in the words of the page that went out with TiesFree.lean): h3
(ReaderReads: what the reader reads off the thread's witness under a number is the mask row's
entry): "NOT TYPED"; hS (oneStretch: what the row's parts spend is one stretch of one sender's
coins): lemmas compiled, the tests' answers "PRINTED AT BOTH SIZES": no theorem states the answer;
in hS's letters the stretch begins at base + the ledger's number: at this segment base is printed
from the book's side alone, and the sender's own base against it is "NOBODY's"; hfree (the member's
slots lie below the mask row's free entries: the fence): a lemma at one stretch is compiled; that a
member's stretch is made of stretches that the test has seen: "NOT SHOWN" (TiesFree.lean's own
Limits say the same); "PRINTED AT BOTH SIZES"; h2 and hin (SenderLaysOwn): the sender's authors':
typed, at this segment under a test on the sending that is shown at no code switch (evaluated at two
sizes: it accepts; not proved); called by no file yet; ho (OwnIs): by a lemma of the frame's
authors'; hF: the book's own test, "evaluated". THE NUMBER OF A MASK ENTRY in h2, hin and hfree is
the format's (place times the number of mask rows, plus the row); a reader that takes the library's
index (row plus place times 2 ^ rowBits) agrees with it just where the number of mask rows is a
power of two: whoever types h3 carries that as a premise [the same authors' later word on their own
lemmas]. The place at_ and the reader cut stay letters in both: a caller lays the member's place and
its own reader; at another place hS may have no answer of that form: then nothing is said. A
joining: calls alone: no new mathematics. No prover, no coin is read here. Nothing on whether the
verifier accepts, on soundness, on completeness or on what a proof hides. No example.
  maskTie_of_ledger   at any thread T, sentence Said, border b, place at_ and reader cut: the eight
                      premises, at the reader (cut w v).2 read in the field, and "the ledger's next
                      number in front is nu0" in the frame's own form (LedgerIs at the open
                      segment's part) give the field, to the letter.
  ledgerIs_k6_closed  the frame's ledgerIs_k6 (Law/Rule/LedgerLeft.lean) with its two premises on
                      the public parameters paid by the library's calls_place
                      (Johnson/Desc/Kinds/Law/K6PubInScope.lean): the place's first slot is 0 and
                      its shape the public parameters' own: so nu0 is a closed term: the number of
                      scalars of the lookup on the head's calls. (The same authors' later file on
                      the ledger's numbers from h alone names the lookups on the calls, two callers
                      and the lookups on the digits; at border 341 it leaves the two premises.)
  maskTie_at_head     at the first chain's thread at the library's head, border 341: the eight
                      premises at that nu0, and h.
CALLED: maskTieOn_whole (Law/Rule/TiesLen.lean), SenderLaysOwn.mono (Law/Rule/TiesFree.lean),
ledger_fork, ledgerIs_thrS (Law/Rule/LedgerMore.lean), ledgerIs_k6, calls_place.

-/
import Johnson.Desc.ProofFile.Honest.K6.Law.OutAtThread
import Johnson.Desc.ProofFile.Honest.Law.Rule.TiesFree
import Johnson.Desc.ProofFile.Honest.Law.Rule.LedgerMore
import Johnson.Desc.ProofFile.Honest.Law.Rule.LedgerLeft
import Johnson.Desc.Kinds.Law.K6PubInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6

open OnBytes (E zeroE)
open OnBytes.Model (Fork)
open VerifiableInference.Desc (Chain Strs Place Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Kinds.Head (parOf)
open VerifiableInference.Desc.Kinds.Head.Law (rd workOf Pinned)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead ledgerIs_k6)

variable {Bk : ProverCoinCounts} {W₀ Rc Tr X Pb : Type}

/-- **THE FIELD maskTie, AT ANY THREAD**, from the frame's premises and its sentence on the ledger's
next number. lim: the number from which on the caller's reader no longer reads the witness: the
reader's sentence h3 is asked below the free entries AND below lim; hlim: the member's slots lie
below lim. -/
theorem maskTie_of_ledger
    {T : Thread Bk S Claim (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Pb}
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Inst Tr) X → Prop) {b : Nat}
    (W : OnBytes.Model.Verify.Public) (wit : Local W₀ Rc Inst Tr → HeadAsk) (at_ : Place)
    (cut : Local W₀ Rc Inst Tr → T.Wt → Pinned) {o : Addr} {d : Due} {rowOf : Cs d → Nat → E}
    {own : Coins Bk → Cs d} {base ν₀ cnt free lim : Nat}
    (h2 : SenderLaysOwn rowOf base (· < free)) (ho : OwnIs Bk T.chain o d own)
    (hin : ∀ ν, ν < free → base + ν < d.e)
    (h3 : ReaderReads T (ThrS T Said b) (fun s : S => s.fork?)
      (fun (_ : Fork) (_ : S) w v ν => rd ((cut w v).2 ν)) rd
      (fun k _ _ ν => rowOf (own k) ν) (fun ν => ν < free ∧ ν < lim))
    (h1 : LedgerIs (Thr T b) segAt? (fun a => a.F.next) ν₀)
    (hS : oneStretch (rowEntries Bk at_
      (headRow (X := X) wit (parOf W.hS (workOf W)) at_).length 0) = some (o, base + ν₀, cnt))
    (hF : ∀ k : Coins Bk, base + ν₀ + cnt ≤ (k.look T.chain o).1.e)
    (hfree : ν₀ + cnt ≤ free) (hlim : ν₀ + cnt ≤ lim) :
    MaskTieOn T (ThrS T Said b) at_ (headRow (X := X) wit (parOf W.hS (workOf W)) at_)
      (fun s => s.fork?) (fun F _ w v j => rd ((cut w v).2 (F.next + j))) rd (spentOf _)
      (fun n j => j < n) :=
  maskTieOn_whole (N := fun ν => ν < free ∧ ν < lim)
    (maskOf := fun (_ : Fork) (_ : S) w v ν => rd ((cut w v).2 ν))
    (slot := fun F : Fork => F.next) (SenderLaysOwn.mono (fun _ hν => hν.1) h2) ho
    (fun ν hν => hin ν hν.1) h3
    (fun _ _ _ _ hT _ hF => ledger_fork (ledgerIs_thrS Said h1) hT hF) hS hF
    (fun j hj => by
      show ν₀ + j < free ∧ ν₀ + j < lim
      omega)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Ky X₀ : Type}

/-- **THE LEDGER'S NEXT NUMBER IN FRONT OF THE MEMBER IS A CLOSED TERM OF THE PUBLIC PARAMETERS**:
the number of scalars of the lookup on the head's calls. CONDITIONAL on the one hypothesis. -/
theorem ledgerIs_k6_closed (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc ProofFile.Inst Tr) :
    LedgerIs (Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 341) segAt?
      (fun a => a.F.next) (OnBytes.Model.Forest.elems (P5J.At.X Zp).HLy.fs) := by
  obtain ⟨p, hp, hs, h0, -⟩ :=
    VerifiableInference.Desc.Kinds.Head.Law.InScope.calls_place h.scope h.pubOne
  have e := ledgerIs_k6 h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hp hs
  rw [h0, Nat.zero_add] at e
  exact e

/-- **THE FIELD maskTie AT THE FIRST CHAIN'S THREAD AT THE LIBRARY'S HEAD, BORDER 341.** -/
theorem maskTie_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc ProofFile.Inst Tr)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (wit : Local W₀ Rc ProofFile.Inst Tr → HeadAsk) (at_ : Place)
    (cut : Local W₀ Rc ProofFile.Inst Tr →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Wt → Pinned)
    {o : Addr} {d : Due} {rowOf : Cs d → Nat → E} {own : Coins Bk → Cs d}
    {base cnt free lim : Nat}
    (h2 : SenderLaysOwn rowOf base (· < free))
    (ho : OwnIs Bk (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.chain o d own)
    (hin : ∀ ν, ν < free → base + ν < d.e)
    (h3 : ReaderReads (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341)
      (fun s : S => s.fork?) (fun (_ : Fork) (_ : S) w' v ν => rd ((cut w' v).2 ν)) rd
      (fun k _ _ ν => rowOf (own k) ν) (fun ν => ν < free ∧ ν < lim))
    (hS : oneStretch (rowEntries Bk at_
      (headRow (X := X) wit (parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) at_).length 0) =
        some (o, base + OnBytes.Model.Forest.elems (P5J.At.X Zp).HLy.fs, cnt))
    (hF : ∀ k : Coins Bk, base + OnBytes.Model.Forest.elems (P5J.At.X Zp).HLy.fs + cnt ≤
      (k.look (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.chain o).1.e)
    (hfree : OnBytes.Model.Forest.elems (P5J.At.X Zp).HLy.fs + cnt ≤ free)
    (hlim : OnBytes.Model.Forest.elems (P5J.At.X Zp).HLy.fs + cnt ≤ lim) :
    MaskTieOn (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said 341) at_
      (headRow (X := X) wit (parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) at_)
      (fun s => s.fork?) (fun F _ w' v j => rd ((cut w' v).2 (F.next + j))) rd (spentOf _)
      (fun n j => j < n) :=
  maskTie_of_ledger Said (P5J.At.X Zp) wit at_ cut h2 ho hin h3
    (ledgerIs_k6_closed h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hS hF hfree hlim

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.maskTie_of_ledger
#print axioms ProofFile.Honest.K6.ledgerIs_k6_closed
#print axioms ProofFile.Honest.K6.maskTie_at_head
