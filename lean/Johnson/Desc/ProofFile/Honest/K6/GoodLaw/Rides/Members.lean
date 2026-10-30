-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/GoodLaw/Rides/Members.lean: THE INVARIANT `K6GoodAt`
(Honest/K6/GoodLaw/Runs.lean) RIDES THE FIVE MEMBERS BETWEEN THE OUTPUT HEAD's OWN ROUNDS AND THE
HEAD's BATCHING: where it stands in front of an accepting step of one of them, it stands behind.
Five lemmas, by calls. None of the library's goals.

  `k6GoodAt_opened`   a state with the invariant stands in the head's segment, opened, and its
                    ledger has its sizes
  `k6GoodAt_of_frontLater`   **the invariant rides along `FrontLater`**
                    (Johnson/Desc/First/Link/Law/K6HeardAtBatch.lean)
  `five_step_frontLater`   an accepting step of each member 342 to 346 gives `FrontLater`, under
                    the one hypothesis h
  `good_rides_member`   **so the invariant rides each of the five**
  `good_rides_thread`   the same at a step of the first chain's thread at the library's own letters

Why forward, step by step. The invariant holds that three tests accept the very samples that made
the head's hearing. So it cannot stand "at every state reached in front of the batching": a state
reached over a sample that reads as 0 is reached too. What can be had is what a walker of a run can
call: five times, from border 342 to border 347.

Limits. IMPLICATIONS: THAT THE INVARIANT STANDS AT ANY STATE IS NOT SHOWN HERE (`good_at_head`,
Honest/K6/GoodLaw/AtHead.lean, has it right behind the member, from the mark's silence, at the
thread, under a premise on the lookup's form). THAT THE FIVE CALLS ARE LAID TOGETHER ALONG A RUN IS
NOT SHOWN: no file walks the thread from 342 to 347. NOT ACROSS THE BATCHING's OWN SAMPLE, AND NOT
ACROSS THE RUNS OF CLAIMS: so the invariant is still not shown at the states at which the claims are
gathered. THE FULL SIZE AND THE FORMAT's EARLIER HASH ALONE from the third lemma on, as h :
`P5J.AtMgA`. (The library has a member of that hypothesis under four premises on the three public
files: `P5J.head_exists_at_name`, Johnson/P5J/HeadExistsAtName.lean; nothing here calls that.) b and
e, the window's two ends, are letters. In `good_rides_thread` nothing of the thread's sentence is
spent: the step alone. Called: `five_decide_frontLater` (Johnson/Desc/Kinds/Law/K6FiveFront.lean),
`alikeFront_of_later` (K6HeardAtBatch.lean), `k6GoodAt_front`, `k6GoodAt_head` (Runs.lean),
`Came.given_ok` (Johnson/Desc/Kinds/Law/FromGiven.lean), `sized_of_wellLaid` (HeardBack.lean there),
`Came.wellLaid_later` (RowPromise.lean there), `keeps_hear` (KeepsHear.lean there),
`Came.step_decide` (RowPins.lean there), `P5J.flat_ok` (Johnson/P5J/FoldJ1.lean). The lines for "its
ledger has its sizes" follow the library's proof of `k6HeardAt_347` (K6HeardAtBatch.lean).
Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K6.GoodLaw.AtHead
import Johnson.Desc.Kinds.Law.K6FiveFront
import Johnson.Desc.Kinds.Law.FromGiven

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace ProofFile.Honest.K6.GoodLaw
open VerifiableInference.Desc (Block Chain Claim OpenedColumn Place Strs)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head (parOf seatAt)
open VerifiableInference.Desc.Kinds.Head.Law (workOf)
open VerifiableInference.Desc.LinkJoin (FrontLater)
open OnBytes.PscRun (Sized)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)

/-- A state with the invariant stands in the head's segment, opened, and its ledger has its
sizes. -/
theorem k6GoodAt_opened {h : OnBytes.Model.Head.Shape} {iU3 : Nat} {p : Head.Par} {b e : Nat}
    {s : S} (k : K6GoodAt h iU3 p b e s) :
    ∃ o, s.here = .head o ∧ o.opened = true ∧ Sized o.F := by
  obtain ⟨o, ho⟩ := k6GoodAt_head k
  obtain ⟨⟨g, H, F0, G, rs, hg, hH, hW, hh, hL, _⟩, _⟩ := k
  obtain ⟨z, y, hz, _⟩ := Head.Law.Came.given_ok p (seatAt h iU3) s g hg
  have hop : o.opened = true := by
    have hz' : (s.lookHeard?.map fun g => (g.zx, fun c => g.zk.getD c #[])) = some z := hz
    by_contra hn
    have e0 : s.lookHeard? = none := by simp [S.lookHeard?, ho, hn]
    rw [e0] at hz'
    simp at hz'
  have e : (seatAt h iU3).ledger s = o.F := by
    show s.fork?.getD {} = o.F
    simp [S.fork?, ho, hop]
  rw [e] at hL
  exact ⟨o, ho, hop, Head.Law.sized_of_wellLaid (Head.Law.Came.wellLaid_later
    (Head.Law.Came.wellLaid_later hW (Head.Law.keeps_hear _ _ _ _ _ hh)) hL)⟩

/-- **THE INVARIANT RIDES ALONG `FrontLater`** (Johnson/Desc/First/Link/Law/K6HeardAtBatch.lean):
what `AlikeFront` compares stays, and the ledger is a later one. -/
theorem k6GoodAt_of_frontLater {h : OnBytes.Model.Head.Shape} {iU3 : Nat} {p : Head.Par}
    {b e : Nat} {s s' : S} (q : FrontLater s s') (k : K6GoodAt h iU3 p b e s) :
    K6GoodAt h iU3 p b e s' := by
  obtain ⟨o, ho, hop, hz⟩ := k6GoodAt_opened k
  exact k6GoodAt_front h iU3 p
    (VerifiableInference.Desc.LinkJoin.alikeFront_of_later q ho hop hz) k

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **AN ACCEPTING STEP OF EACH OF THE FIVE MEMBERS BETWEEN THE HEAD's OWN ROUNDS AND THE
HEAD's BATCHING (numbers 342 to 346 of the first chain's list) GIVES `FrontLater`**, under the one
hypothesis h. -/
theorem five_step_frontLater (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {i : Nat} (h1 : 342 ≤ i)
    (h2 : i < 347) {blk : Block S Claim} (hb : cF.blocksInOrder[i]? = some blk) {ft n : Nat} {s s' : S}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} (hs : blk.step ft s rs cols = .ok (s', n)) :
    FrontLater s s' := by
  obtain ⟨Bs, base, O⟩ := h.toAtMg.laid.opened
  obtain ⟨gs, hd⟩ := Head.Law.Came.step_decide ft blk s rs cols s' n hs
  exact Head.Law.Five.five_decide_frontLater h.scope h.reads O
    (P5J.flat_ok h.toAtMg) h1 h2 hb s _ gs s' hd

/-- **SO THE INVARIANT RIDES EACH OF THE FIVE.** b and e are letters. -/
theorem good_rides_member (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {i : Nat} (h1 : 342 ≤ i)
    (h2 : i < 347) {blk : Block S Claim} (hb : cF.blocksInOrder[i]? = some blk) {ft n : Nat} {s s' : S}
    {rs : List Fmt.RoundView} {cols : List OpenedColumn} (hs : blk.step ft s rs cols = .ok (s', n)) {b e : Nat}
    (k : K6GoodAt (P5J.At.X Zp).hS (Head.Law.readsOf (P5J.At.X Zp))
      (parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) b e s) :
    K6GoodAt (P5J.At.X Zp).hS (Head.Law.readsOf (P5J.At.X Zp))
      (parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) b e s' :=
  k6GoodAt_of_frontLater (five_step_frontLater h h1 h2 hb hs) k

/-- **AT THE FIRST CHAIN's THREAD AT THE LIBRARY's OWN LETTERS**: behind a step of the thread at one
of the five members the invariant stands where it stood in front. Nothing of the thread's
sentence is spent: the step alone. -/
theorem good_rides_thread (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ b₀ : Nat)
    (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop) (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (Kp : Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr) {i : Nat} (h1 : 342 ≤ i)
    (h2 : i < 347) (b e : Nat) :
    ∀ blk k s m E ds y cols s',
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs[i]? = some blk →
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Stepped blk k s m E ds y
        cols s' →
      K6GoodAt (P5J.At.X Zp).hS (Head.Law.readsOf (P5J.At.X Zp))
        (parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) b e s →
      K6GoodAt (P5J.At.X Zp).hS (Head.Law.readsOf (P5J.At.X Zp))
        (parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) b e s' := by
  intro blk k s m E ds y cols s' hblk hS hk
  have hblk' : cF.blocksInOrder[i]? = some blk := hblk
  exact good_rides_member h h1 h2 hblk' hS.2 hk

#print axioms k6GoodAt_opened
#print axioms k6GoodAt_of_frontLater
#print axioms five_step_frontLater
#print axioms good_rides_member
#print axioms good_rides_thread

end ProofFile.Honest.K6.GoodLaw
