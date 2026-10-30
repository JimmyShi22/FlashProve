-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No state of the verifier is shown at which the kind's decide accepts.
Johnson/Desc/First/Look/K3CallsKept.lean: the lookup on a link's CALLS: THREE PUBLIC TESTS OF OTHER
KINDS THAT ARE OPEN ON BOTH SIDES OF THE LOOKUP ON THE CALLS STAY TRUE OVER AN ACCEPT OF THE KIND's
decide, with no premise on the rounds' words: "K5.liveReq" (liveReqB,
Johnson/Desc/First/Att/K05DoorB.lean: it reads the open link's context alone), "K5.readsThere"
(readsThereB, Johnson/Desc/First/Att/Door/ReadsThereB.lean: the open link's context, the ledger's
list of arrays, the book), at attention; tokenSmall (tokenHeardB, Johnson/Stored/FillK6K7.lean: the
reply), at the head. By an evaluation of the table of joints (the items printed at seven of the 25
segments, the numbers of items at all) these three, with what rides by the rule of footprints and
what reads the ledger, are what is open on both sides there: evidence, no proof. Ties of texts: no
error term. NO SOUNDNESS IS CLAIMED.

OBJECT: Desc.K3.block's decide at Desc.K3.seatCalls claim; the three tests.
USER: Johnson/Desc/Sound/MgAt/K3CallsOthers.lean, K3HeadBehindAt.lean.
  Meant: the kind's debt at a step on the state.
LETTERS: those of K3CallsMade.lean.

Main names: `liveReq_kept` · `readsThere_kept` · `tokenSmall_kept`; and two that the row's own field
  wants at the piece: `sentIs_kept`, `treesAre_kept` ("frame.sentIs", "ledger.treesAre":
  Johnson/Desc/First/FillSent.lean).

Limits. These five tests alone.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallsMade
import Johnson.Desc.First.Look.K3CallsTurns
import Johnson.Desc.First.Att.K05DoorB
import Johnson.Desc.First.Att.Door.ReadsThereB
import Johnson.Desc.First.FillSent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.PscRun
open VerifiableInference.Desc.K3 (k3OnIn)
open VerifiableInference.Desc.First.Look

section
variable {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
  (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest Desc.First.S Cl))
  {h : Forest.Shape} (s s' : Desc.First.S) (rs : List Fmt.RoundView)
  (cols : List (List (ℕ × List UInt64)))

/-- **"K5.liveReq" stays.** -/
theorem liveReq_kept
    (hd : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before p guests).decide s rs cols =
      .ok s') (born : Array (ℕ × ℕ)) (h0 : Desc.First.Att.P.liveReqB born s = true) :
    Desc.First.Att.P.liveReqB born s' = true := by
  unfold Desc.First.Att.P.liveReqB at h0 ⊢
  rw [(k3_calls_sameBut claim piece laid before p guests s s' rs cols hd).link]
  exact h0

/-- **tokenSmall stays.** -/
theorem tokenSmall_kept
    (hd : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before p guests).decide s rs cols =
      .ok s') (hS : Head.Shape) (iU3 : ℕ) (h0 : Desc.Kinds.Head.tokenHeardB hS iU3 s = true) :
    Desc.Kinds.Head.tokenHeardB hS iU3 s' = true := by
  have e : s'.out = s.out := (k3_calls_sameBut claim piece laid before p guests s s' rs cols hd).out
  have e2 : Desc.Kinds.Reply.token (Desc.Kinds.Head.seatAt hS iU3).toSeat s' =
      Desc.Kinds.Reply.token (Desc.Kinds.Head.seatAt hS iU3).toSeat s := by
    unfold Desc.Kinds.Reply.token
    show Option.map _ s'.out.reply = Option.map _ s.out.reply
    rw [e]
  unfold Desc.Kinds.Head.tokenHeardB at h0 ⊢
  rw [e2]
  exact h0

/-- **"frame.sentIs" stays**: it reads the open link's context alone. -/
theorem sentIs_kept
    (hd : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before p guests).decide s rs cols =
      .ok s') (d : Desc.First.FillSent.SentData) (m : ℕ)
    (h0 : Desc.First.FillSent.sentIsB d m s = true) :
    Desc.First.FillSent.sentIsB d m s' = true := by
  unfold Desc.First.FillSent.sentIsB at h0 ⊢
  rw [(k3_calls_sameBut claim piece laid before p guests s s' rs cols hd).link]
  exact h0

/-- **"ledger.treesAre" stays**: the accept leaves the ledger's list of arrays. -/
theorem treesAre_kept (hs : p.shape = some h)
    (hd : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before p guests).decide s rs cols =
      .ok s') (hIn : k3OnIn p s = true) (d : Desc.First.FillSent.SentData) (m : ℕ)
    (h0 : Desc.First.FillSent.treesAreB d m s = true) :
    Desc.First.FillSent.treesAreB d m s' = true := by
  obtain ⟨F, F', g, rs', hF, -, -, -, -, -, hF', -, L, -⟩ :=
    k3_calls_made claim piece laid before p guests s s' rs cols hs hd hIn
  unfold Desc.First.FillSent.treesAreB at h0 ⊢
  rw [hF] at h0
  rw [hF']
  simp only [Option.any_some] at h0 ⊢
  rw [L.padLeft.rest.1]
  exact h0

/-- **"K5.readsThere" stays.** -/
theorem readsThere_kept (hs : p.shape = some h)
    (hd : (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before p guests).decide s rs cols =
      .ok s') (hIn : k3OnIn p s = true) (W : Verify.Public) (own : List (ℕ × ℕ))
    (h0 : H2K5.Door.readsThereB W own s = true) : H2K5.Door.readsThereB W own s' = true := by
  obtain ⟨F, F', g, rs', hF, -, hn0, -, -, e, -, -, L, -⟩ :=
    k3_calls_made claim piece laid before p guests s s' rs cols hs hd hIn
  have hbk : s'.book = s.book :=
    (k3_calls_sameBut claim piece laid before p guests s s' rs cols hd).book
  unfold H2K5.Door.readsThereB at h0 ⊢
  cases hh : s.here with
  | att a =>
    rw [hh] at h0
    have eF : a.F = F := by simpa [Desc.First.S.fork?, hh] using hF
    rw [hbk, e, put_att g F' hh hn0]
    show ((W.A[a.L.link / 2]?).any fun q => H2K5.Door.readsAtB own q.iU3 q.nW a.L F' s.book) = true
    have h1 : ((W.A[a.L.link / 2]?).any fun q =>
        H2K5.Door.readsAtB own q.iU3 q.nW a.L a.F s.book) = true := h0
    rw [eF] at h1
    have e3 : ∀ q : Attention.Plan, H2K5.Door.readsAtB own q.iU3 q.nW a.L F' s.book =
        H2K5.Door.readsAtB own q.iU3 q.nW a.L F s.book := by
      intro q
      unfold H2K5.Door.readsAtB
      rw [L.padLeft.rest.1]
    simp only [e3]
    exact h1
  | between => rw [hh] at h0; cases h0
  | fin _ => rw [hh] at h0; cases h0
  | mem _ => rw [hh] at h0; cases h0
  | lay _ => rw [hh] at h0; cases h0
  | head _ => rw [hh] at h0; cases h0

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.liveReq_kept
#print axioms VerifiableInference.OnPublicFiles.tokenSmall_kept
#print axioms VerifiableInference.OnPublicFiles.readsThere_kept
#print axioms VerifiableInference.OnPublicFiles.sentIs_kept
#print axioms VerifiableInference.OnPublicFiles.treesAre_kept
