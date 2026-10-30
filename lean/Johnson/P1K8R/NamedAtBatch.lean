-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P1K8R/NamedAtBatch.lean: TWO OF THE FORMS THAT A LOOKUP HEARS (cEnd, leaves.start) NAME NO
ENTRY, IN FRONT OF THE BATCHING: OF WHAT THE LOOKUP ON THE DIGITS HAS HEARD, AT THE 24 SEGMENTS IN
FRONT OF THE HEAD's; OF WHAT THE LOOKUP ON THE CALLS HAS HEARD, AT THE HEAD's. AT STATES THAT THE
FIRST CHAIN's OWN BLOCKS REACH; UNDER THE SCOPE, THE FILES READ, IM.Open AND THE DESCRIPTION's TEST
ON ITS PLAN. Lemmas; none of the library's goals. No prover stands in them; nothing on completeness,
soundness or hiding.

  `heard_named`   at any seat that reads back what it lays (K3.SeatReads,
      Johnson/Desc/First/Look/K3SeatLaw.lean), behind a yes of K3.block, from a ledger with its
      sizes: OnPublicFiles.decide_named (Johnson/Top/H/Keep/K3Named.lean); Fo.Tp.PadNames, bare_ents
      (PadNamed.lean). OnPublicFiles.k3_calls_leavesBare (Johnson/Desc/First/Look/K3LeftItem.lean) goes so
      at the calls' seat, for one of the two forms: its proof's first six lines stand here, with the
      seat a letter
  `stated_digits_named`   behind a yes of the seated lookup on the digits:
      OnPublicFiles.theStated_yes_digits (K3DigitsSeatedYes.lean); the step without a round by
      quietAt_frame (K3StatedSteps.lean), seatOf_putFork, seatOf_headClaim (K03RowsBare.lean)
  **`digitsLeft_at_batch`**   LinkJoin.back_of (Johnson/Desc/First/Link/Law/StretchBack.lean) at
      that one block (the proof's first seven lines are those of `look_back_digits`,
      Johnson/P1K8R/LookAtBatch.lean); the ledger's sizes in front of it by OnPublicFiles.sized_upTo
      (K03RowsBare.lean). The fields cEnd and leaves of `StillFront`
      (Johnson/P1K8R/BehindAtReach.lean), at these 24 segments
  `callsLeft_341`, **`callsLeft_head`**   the first: ITS FIVE LINES ARE THE FIRST FIVE OF THE PROOF
      OF P4.bare_341 (Johnson/P4R/BareAt341.lean), with `heard_named` in the stead of
      OnPublicFiles.calls_rowsBare; the second by `look_back_head` (Johnson/P1K8R/LookAtBatchAll.lean).
      The fields cEnd and leaves of `StillHead`
The like elsewhere: at the layers' segments, for the calls' lookup, at 28 g + 4 and 28 g + 5:
pad_behind_look, pad_front_reads (Johnson/Desc/AtSeats/PadAtRch.lean); at the digits' lookup's
decision, under a condition on the plan: OnPublicFiles.digits_heard_facts
(Johnson/Top/H/Keep/DigitsHeardFacts.lean).
Limits. Nothing on what the head's lookup on the digits has heard. Nothing on whether any state is
reached.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P1K8R.LookAtBatchAll
import Johnson.Top.H.Keep.K3Named
import Johnson.Top.H.Keep.PadNamed
import Johnson.Desc.First.Look.K3SeatLaw
import Johnson.Desc.First.Look.K3DigitsSeatedYes
import Johnson.Desc.First.Look.K3StatedSteps
import Johnson.Desc.First.Look.K03RowsBare

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Reach)

/-- **What a yes of a lookup's own block leaves as heard: two of its forms name no entry**, at any
seat that reads back what it lays, from a ledger with its sizes: OnPublicFiles.decide_named
(Johnson/Top/H/Keep/K3Named.lean). The proof's first six lines are those of
OnPublicFiles.k3_calls_leavesBare (Johnson/Desc/First/Look/K3LeftItem.lean), with the seat a letter. -/
theorem heard_named {T Cl : Type} (seat : K3.Seat T Cl) (hr : K3.SeatReads seat) (piece : ℕ)
    (laid : Array Nat) (before : List (ℕ × ℕ)) (p : First.Look.P)
    (guests : List (First.Look.Guest T Cl)) (s s' : T) (rs : List Fmt.RoundView)
    (cols : List (List (ℕ × List UInt64)))
    (hd : (K3.block seat piece laid before p guests).decide s rs cols = .ok s') {F : Fork}
    (hF : seat.fork s = some F) (hz : PscRun.Sized F) :
    ∃ g, seat.heard s' = some g ∧ g.cEnd.ents = #[] ∧ g.leaves.start.ents = #[] := by
  obtain ⟨F1, x, hF1, hn, e, hN⟩ := OnPublicFiles.decide_named seat piece laid before p guests s s' rs
    cols hd
  obtain rfl : F = F1 := Option.some.inj (hF.symm.trans hF1)
  have hsome : (seat.fork s).isSome = true := by
    rw [hF1]
    rfl
  refine ⟨x.1, ?_, Fo.Tp.bare_ents (hN hz).cEnd.1, Fo.Tp.bare_ents (hN hz).start.1⟩
  rw [e]
  exact hr _ _ _ hsome hn

/-- **The like behind a yes of the seated lookup on the digits**: the step without a round that may
stand behind the rounds leaves what was heard. -/
theorem stated_digits_named {Cl : Type} (claim : Aff → Cl) (readers : ℕ → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place) (B : Block S Cl)
    (h : K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true) (i : ℕ)
    (hi : a.link = some i) (hpc : a.piece = K3.pieceAt X i true) (s c : S) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) (hd : B.decide s rs gs = .ok c) {F : Fork}
    (hF : s.fork? = some F) (hz : PscRun.Sized F) :
    ∃ g, c.tl?.bind (·.heard) = some g ∧ g.cEnd.ents = #[] ∧ g.leaves.start.ents = #[] := by
  obtain ⟨P', sent, laid, n, gs', s', -, hyes, hstep⟩ :=
    OnPublicFiles.theStated_yes_digits claim readers X codes shape a B h hOk i hi hpc s c rs gs hd
  obtain ⟨g, hg, h1, h2⟩ := heard_named (K3.seatDigits claim) (K3.seatDigits_reads claim) a.piece
    laid sent P' [] s s' _ gs' hyes hF hz
  rcases hstep with rfl | ⟨f, hf, hfs⟩
  · exact ⟨g, hg, h1, h2⟩
  · exact ⟨g, (OnPublicFiles.quietAt_frame (OnPublicFiles.seatOf claim true).heard
      (OnPublicFiles.seatOf_putFork claim true) (OnPublicFiles.seatOf_headClaim claim true) X i true f hf s' c
      hfs).1 g hg, h1, h2⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **IN FRONT OF THE BATCHING, AT THE 24 SEGMENTS IN FRONT OF THE HEAD's: THE LOOKUP ON THE DIGITS
HAS HEARD SOMETHING, AND THE TWO FORMS NAME NO ENTRY.** -/
theorem digitsLeft_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 24) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + 9) (z, s)) :
    ∃ g, s.tl?.bind (·.heard) = some g ∧ g.cEnd.ents = #[] ∧ g.leaves.start.ents = #[] := by
  obtain ⟨Lk, b, b', e1, e2, e3, e4⟩ := IM.k3_of hS hR O l (by omega) true
  obtain ⟨b'', e3', hk⟩ := OnPublicFiles.k03_const_ok hS hR O hOk l (by omega) true
  obtain rfl : b' = b'' := Option.some.inj (e3.symm.trans e3')
  have i3 : IM.k3Ix l true = 6 := by
    show (if true = true then 6 else 1) + (if l = 24 then 1 else 0) = 6
    rw [if_pos rfl, if_neg (by omega)]
  rw [i3] at e2
  obtain ⟨s8, r8, k8⟩ := LinkJoin.back_of
    (R := fun u t => ∀ G, u.fork? = some G → PscRun.Sized G →
      ∃ g, t.tl?.bind (·.heard) = some g ∧ g.cEnd.ents = #[] ∧ g.leaves.start.ents = #[])
    hS hR O (l := l) (i := 6) (by omega) e1 e2 e4 (fun q => nomatch q)
    (fun u rs gs t hd G hG hz => stated_digits_named _ _ _ _ _ _ b' e3 hk l rfl
      (K3Lot.k03_place _ _ _ _ _ l true b' e3).1 u t rs gs hd hG hz) h
  obtain ⟨-, rs, cols, f⟩ := Johnson.Desc.First.Walk.Tied.reach_fold.1 r8
  obtain ⟨G, hG, hz⟩ := OnPublicFiles.sized_upTo hS hR O hOk l hl 5 (by omega) f
  exact k8 G hG hz

/-- **Behind the lookup on the calls of the head's segment: it has heard something, and the two
forms name no entry.** Its five lines are the first five of the proof of P4.bare_341
(Johnson/P4R/BareAt341.lean), as in `callsRows_341` (Johnson/P1K8R/LookAtBatchAll.lean), with
`heard_named` at the calls' seat in the stead of OnPublicFiles.calls_rowsBare. -/
theorem callsLeft_341 {Q : Type} {start : Q → S} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {z : Q} {s : S} (h : Reach 0 c.blocksInOrder start 341 (z, s)) :
    ∃ k, s.lookHeard? = some k ∧ k.cEnd.ents = #[] ∧ k.leaves.start.ents = #[] := by
  obtain ⟨_, _, s340, -, -, ⟨p, n, HP, rs, gs, a2⟩, b3, Qp, sent, laid, rs3, gs3, f3, hv, hp⟩ :=
    P4.back_341 hS hR O h
  obtain ⟨G, hG, hs, -, -⟩ := Kinds.Head.Law.placeH2_free a2
  exact heard_named (K3.seatCalls K3Lot.ofForm) (K3.seatCalls_reads K3Lot.ofForm) 3 laid sent Qp []
    s340 s rs3 gs3 (K3.Law.blockVia_decide (hp (P4.plan_at O hOk 340 b3 f3)) hv) hG hs

/-- **So, at the head's segment, in front of the batching.** -/
theorem callsLeft_head {Q : Type} {start : Q → S} (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {z : Q} {s : S} (h : Reach 0 c.blocksInOrder start 347 (z, s)) :
    ∃ k, s.lookHeard? = some k ∧ k.cEnd.ents = #[] ∧ k.leaves.start.ents = #[] := by
  obtain ⟨s1, r1, e⟩ := look_back_head hS hR O hOk h
  obtain ⟨k, hk, hb⟩ := callsLeft_341 hS hR O hOk r1
  exact ⟨k, e k hk, hb⟩

end

end P1K8

#print axioms P1K8.heard_named
#print axioms P1K8.stated_digits_named
#print axioms P1K8.digitsLeft_at_batch
#print axioms P1K8.callsLeft_341
#print axioms P1K8.callsLeft_head
