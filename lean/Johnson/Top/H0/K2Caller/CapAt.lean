-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/CapAt.lean: the code switch: THE LAW's ERROR BOUNDS AGAINST THE CAP. The
pieces of a file's real rows carry the cap as their error bounds (`Err.cap 128`, Iop/ErrCap.lean: at
each round the number of the round's challenges / 2 ^ 128); the law of the code switch stands at the
library's own counts, read along the two written rounds. One theorem.

Main names:
  `k2_err_cap`: where the typed structure r passes its two tests with code and its target is 128,
    and the two written rounds are the typed ones (`K2Wr`): the error bounds of `k2Piece`
    (PieceAt.lean) are, round by round, at most the cap's. By `switch_written` and
    `Err.le_cap_of_below_inv`.
Limits. OF THE 128 BITS SOME ARE PROOF OF WORK: in WrittenMeets.lean's words, at the written records
the round LOC "is at most 2 ^ -108 as a share of its typed values, and the other 20 bits are work,
counted as the written round counts it"; "That work is worth its bits is not said. A bound on each
round, not on a sum over rounds."
It says nothing on whether 128 bits a round are enough for a whole; the premises are paid
elsewhere (at the written entries by Lean's kernel). It is no soundness of the protocol. On hiding
nothing.

-/
import Johnson.Top.H0.K2Caller.PieceAt
import Iop.ErrCap

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop Cb
open Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch
open VerifiableInference.Desc.Sound (Frame Piece)
open VerifiableInference.Desc.First.K2Hands
open _root_.Run (ckP)
open scoped ENNReal

variable {F : Frame} {W : Type}

/-- **THE LAW's ERROR BOUNDS ARE AT MOST THE CAP OF 128 BITS A ROUND**, where the typed structure's
target is 128: round by round at most (the number of the round's challenges) / 2 ^ 128. -/
theorem k2_err_cap {r : SwRow} (h : r.ok = true) (hW : r.writtenOK = true)
    (ht : r.set.target = 128) (X : Letters r (r.ok_says h))
    (iJ : ((rowsAt r (r.ok_says h) X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.J → (sigOf r.cs r.l).Ent)
    (iQ : ((rowsAt r (r.ok_says h) X.t₀ X.oM X.oZ).keep r.kp).Sh.Cf.Q → (sigOf r.cs r.l).Ent)
    (d₁ d₂ : RDT) (ρ : WordsOf (selZ X iJ iQ) d₁) (w : K2Wr r d₁ d₂) (p : K2.P2) (base : ℕ)
    (ext : Rec × F.E.Str → Tr (uLT (ckP .two) [d₁, d₂]) → W → W) :
    Err.le (k2Piece (W := W) X iJ iQ d₁ d₂ ρ p base ext).err
      (Err.cap 128 (uLT (ckP .two) [d₁, d₂])) := by
  have hb := switch_written h hW (X.withSel iJ iQ) d₁ d₂ ρ w
  rw [ht] at hb
  exact Err.le_cap_of_below_inv 128 _ hb

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.k2_err_cap
