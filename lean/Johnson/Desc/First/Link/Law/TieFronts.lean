-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/TieFronts.lean: TWO PREMISES OF THE TIES t3_eq (TieThreeEq.lean) AND
t4_batch (TieFourBatch.lean), PAID OR BROUGHT DOWN. Theorems.

What is said.
  `step_of_out`: **hstep of t3_eq, PAID**: where the piece holds "below b₃" and a yes of b₃'s step
    is
    a yes of the one equation's (the law's own hpe and hb₃, LinkJoin.lean's JoinAsks), the piece's
    yes from a to b is a yes of the one equation's step from a.1 to b.1: by
    Piece.out_below and fold_one (Johnson/Desc/LinkLaw3.lean), as in Cores.lean's core3.
  `FrameFull`: the frame of the link's check stands between a link's messages and its closing, and
    holds a number for every oracle message of the open link.
  `ahead_none`: **hno of t4_batch, BROUGHT DOWN TO FrameFull**: where the frame is full no array
    is "ahead" (K9.aheadIn, Johnson/Desc/First/Batch/Ahead.lean), at any sent and own: by the text
    of K9.aheadOf and of the frame's whereIs (OnBytes/Iop/Req.lean).

Limits. FrameFull IS A PREMISE: SHOWN AT NO STATE HERE. (K9's draw asks "K9.link-ready": all of the
link's moments are heard; that the frame then holds a number for each of its messages is a fact
along the run of the frame's own steps: nobody's yet.) Nothing on soundness.

-/
import Johnson.Desc.LinkLaw3
import Johnson.Desc.First.Batch.Ahead
import Johnson.Desc.First.Batch.Law.Cores

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (atS Where)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open _root_.Run.PQ (CK)

/-- **The piece's yes is the one equation's step's.** -/
theorem step_of_out {C : CK} {F : Frame} {W : Type} (pw : Where) (b₃ : Block S Claim)
    (hb₃ : ∀ ft s rs cols x, b₃.step ft s rs cols = .ok x →
      (K9.oneEquation (Cl := Claim) atS pw).step ft s rs cols = .ok x)
    (pe : Piece C F S Claim W) (hpe : pe.b = below b₃) :
    ∀ a τ b, pe.ior.red.out a τ = some b → ∃ p ft rs cols n,
      (K9.oneEquation (Cl := Claim) atS p).step ft a.1 rs cols = .ok (b.1, n) := by
  intro a τ b hout
  obtain ⟨_, _, hfold⟩ := Piece.out_below hpe hout
  obtain ⟨j, hstep⟩ := fold_one hfold
  exact ⟨pw, _, _, _, j, hb₃ _ _ _ _ _ hstep⟩

/-- **The frame holds a number for every oracle message of the open link.** -/
structure FrameFull (f : ReqFrame) : Prop where
  /-- it stands between a link's messages and its closing -/
  next : f.next = .laterOrClose
  /-- as many numbers as the open link has oracle messages, or more -/
  all : ∀ ms, (f.shape.link[f.link]?).map (·.messages) = some ms → ms.length ≤ f.own.size

/-- **WHERE THE FRAME IS FULL NOTHING IS AHEAD.** -/
theorem ahead_none (sent : ℕ → List (ℕ × ℕ)) (own : List (ℕ × ℕ)) (a : K9.Part)
    (h : FrameFull a.L.check.frame) : ∀ b, K9.aheadIn sent own a b = none := by
  intro b
  have h0 : K9.aheadOf sent a b = none := by
    unfold K9.aheadOf
    split
    · rename_i hb
      have hb' : b.1 = a.L.check.frame.link := by simpa using hb
      refine Option.bind_eq_none_iff.2 fun A _ => ?_
      split
      · rfl
      · rename_i hw
        refine Option.bind_eq_none_iff.2 fun ms hm => ?_
        refine Option.bind_eq_none_iff.2 fun M hM => ?_
        exfalso
        have hlt : A.message < ms.length := (List.getElem?_eq_some_iff.1 hM).1
        have hle := h.all ms (by rw [← hb']; exact hm)
        unfold ReqFrame.whereIs at hw
        rw [h.next, if_neg (by decide), if_pos hb] at hw
        have := Array.getElem?_eq_none_iff.1 hw
        omega
    · rfl
  unfold K9.aheadIn
  rw [h0]
  rfl

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.step_of_out
#print axioms VerifiableInference.Desc.LinkJoin.ahead_none
