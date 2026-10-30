-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/TailClaims/BehindSeat.lean: two premises of behind_returns and behind₃_returns
(Johnson/Desc/First/TailClaims/BehindChain.lean, BehindLayers.lean), paid where a link is the
driver's and the smallness test's sub-protocol stands seated in it. General laws; nothing is
evaluated.

  `order_attention`, `order_head`, `order_layers`: a link that is "the segment number l of the sort
    sub" (SegAt, Johnson/Desc/First/Link/Law/LinkJoinRuns.lean) has the order of runs behind the
    batching that the two laws ask, with the smallness test at number 4 (the head's link: 5).
  `bind_seatSame_iff`: a run followed by the wrapper's comparison accepts just where both accept.
  **`k8Runs_seated`**: where the list states at number i the term "K8.whole p as it stands in the
    first chain, alone" (IM.seatedAs, Johnson/IMR/SeatForm.lean), there are r₁, r₂ with
    K8Runs bs i p same r₁ r₂.
  **`behind_seated`**: the two joined with behind_returns and sameReply_k8set (BehindSame.lean): at
    an attention link or the head's link of the driver, with K8.whole p seated under the proof
    file's own comparison: behindG returns at the state's shape · the link's tests accept wherever
    gT and vT accept (A PREMISE) · vT accepts · the smallness test's tests on values accept behind
    "K8.lsTail": then the sub-protocol's decision accepts.

Limits. That a description's chain has such links and such a seated term is the library's law
IM.k8_alone (Johnson/IMR/K8Seat.lean) and the head's own (P5J), not joined here. The link's tests
behind the adding stay a premise. No law here joins anything to behind₃_returns. The three order
laws have no caller, and bear the short names of three laws of the library on another order
(orderOf: Johnson/Desc/First/Link/Law/LinkJoinPay.lean). Nothing on soundness, completeness or
hiding.
-/
import Johnson.Desc.First.TailClaims.BehindLayers
import Johnson.Desc.First.TailClaims.BehindSame
import Johnson.Desc.First.Link.Law.LinkJoinRuns
import Johnson.IMR.SeatForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.TailClaims.Law.Tests
open OnBytes OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.Shape (ChainSh chainSh)
open VerifiableInference.Desc.LinkJoin (SegAt)

/-! ## 1 The orders -/

section Orders
variable {T Cl : Type} {l : Nat} {L : Link T Cl}

theorem order_attention (h : SegAt l .attention L) :
    L.orderAfter = [(4, "K8.lsTail"), (4, "K8.tests")] := h.orderAfter

theorem order_head (h : SegAt l .head L) :
    L.orderAfter = [(5, "K8.lsTail"), (5, "K8.tests")] := h.orderAfter

theorem order_layers (h : SegAt l .layers L) :
    L.orderAfter = [(4, "K8.lsTail"), (2, "free-slot"), (4, "K8.tests")] := h.orderAfter

end Orders

/-! ## 2 The seated runs -/

theorem bind_seatSame_iff (same : S → S → Bool) (u : S → Except String S) (t y : S) :
    (u t).bind (seatSame same t) = .ok y ↔ u t = .ok y ∧ same t y = true := by
  cases hc : u t with
  | error e => exact ⟨fun hy => (nomatch hy), fun hy => (nomatch hy.1)⟩
  | ok y0 =>
    show seatSame same t y0 = .ok y ↔ _
    unfold seatSame
    by_cases hs : same t y0 = true
    · rw [if_pos hs]
      constructor
      · intro hy
        obtain rfl := Except.ok.inj hy
        exact ⟨rfl, hs⟩
      · rintro ⟨hy, -⟩
        exact hy
    · rw [if_neg hs]
      constructor
      · intro hy
        exact nomatch hy
      · rintro ⟨hy, h2⟩
        obtain rfl := Except.ok.inj hy
        exact absurd h2 hs

/-- The bare run that K8.whole states for a run at the part. -/
def bareRun (f : K8Part → Except String K8Part) (s : S) : Except String S :=
  (K8.atRecord (fun q => (f q).map fun q' => ((), q')) s).map (·.2)

theorem after_whole (p : K8.ParW) : (K8.whole p).after =
    [("K8.lsTail", bareRun k8LsTail.2), ("K8.tests", bareRun (k8Tests p.nU).2)] := rfl

/-- **The seated term states K8.whole p's two runs, each with the wrapper's comparison.** -/
theorem k8Runs_seated {bs : List (Block S Claim)} {i : Nat} {p : K8.ParW} {same : S → S → Bool}
    {name : String} {a : Place} (h : bs[i]? = some (IM.seatedAs same (K8.whole p) name a)) :
    K8Runs bs i p same (fun t => (bareRun k8LsTail.2 t).bind (seatSame same t))
      (fun t => (bareRun (k8Tests p.nU).2 t).bind (seatSame same t)) := by
  have ea : (IM.seatedAs same (K8.whole p) name a).after =
      [("K8.lsTail", fun t => (bareRun k8LsTail.2 t).bind (seatSame same t)),
        ("K8.tests", fun t => (bareRun (k8Tests p.nU).2 t).bind (seatSame same t))] := rfl
  refine ⟨?_, ?_, ⟨bareRun k8LsTail.2, ?_, bind_seatSame_iff same _⟩,
    ⟨bareRun (k8Tests p.nU).2, ?_, bind_seatSame_iff same _⟩⟩
  · rw [h]
    show (IM.seatedAs same (K8.whole p) name a).after.lookup "K8.lsTail" = _
    rw [ea]
    simp [List.lookup]
  · rw [h]
    show (IM.seatedAs same (K8.whole p) name a).after.lookup "K8.tests" = _
    rw [ea]
    simp [List.lookup]
  · rw [after_whole]
    exact List.mem_cons_self
  · rw [after_whole]
    exact List.mem_cons_of_mem _ List.mem_cons_self

/-! ## 3 Joined -/

/-- **THE SUB-PROTOCOL "BEHIND THE BATCHING" ACCEPTS**, at a link whose order names the smallness
test's two runs alone, with K8.whole p seated under the proof file's own comparison. -/
theorem behind_seated {L : Link S Claim} {i : Nat} {p : K8.ParW} {name : String} {a : Place}
    (ho : L.orderAfter = [(i, "K8.lsTail"), (i, "K8.tests")])
    (h : L.hear[i]? = some (IM.seatedAs ProofFile.sameReply (K8.whole p) name a))
    {gT : ChainSh → Bool} {vT : S → Bool}
    (hT : ∀ s, gT (chainSh s) = true → vT s = true → L.tests s = .ok ()) (s : S) (t : ChainSh)
    (hg : behindG gT p.nU (chainSh s) = .ok t) (hv : vT s = true)
    (hv₂ : ∀ s₁, bareRun k8LsTail.2 s = .ok s₁ → valsS p.nU s₁ = true) :
    ∃ s', L.runBehind s = .ok s' ∧ chainSh s' = t := by
  have K := k8Runs_seated h
  obtain ⟨s', hs'⟩ := behind_returns ho K hT sameReply_k8set s t hg hv
    fun s₁ h₁ => hv₂ s₁ ((bind_seatSame_iff _ _ s s₁).1 h₁).1
  exact ⟨s', hs', (behind_carries ho K s s' t hs' hg).symm⟩

end VerifiableInference.Desc.First.TailClaims.Law.Tests

#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.order_attention
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.order_head
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.order_layers
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.k8Runs_seated
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.behind_seated
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.bind_seatSame_iff
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.bareRun
#print axioms VerifiableInference.Desc.First.TailClaims.Law.Tests.after_whole
