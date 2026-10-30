-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/RecOfHist.lean: A RECORD OF
THE KEY FILE'S FIRST CHAIN THAT WAS REACHED HAS THE RECORD'S HALF OF THE LINKS' ROWS: the induction
over fk_walk (WalkAtFK.lean) along the history (LPFD.Hist₁ := Reached at the
description's own blocks as a piece holds them, from the description's start:
Johnson/Top/Fire/Code/RowsWoven.lean, Reached.lean).

Main names:
  rec_of_hist: Hist₁ (Key.descriptionFromSource X N P) D k a ⊢ RecAt X k a.2, for k up to 2 + 6 · (the number of
    lookups).

Object: Key.descriptionFromSource X N P's first chain's flat list and start₁, through Hist₁.
User: TiePromise.lean, others (meant: the promises' ties at the fields r1_4 | r1_5 | r1_10 | r1_11).
Letters: X, N, P, D. Premises: those of fk_walk.

Limits. Nothing on the decoder's condition or on the rows' relations. Nothing on soundness.

-/
import Johnson.RunOne.Law.WalkAtFK
import Johnson.Top.Fire.Code.RowsWoven

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.RecOfHist
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K3.KeyLaw
open VerifiableInference.Desc.Key (FirstState Claim Source)
open Johnson.RunOne.Sound (FK)
open Johnson.RunOne.Law.WalkAtFK
open LPFD (Hist₁ Reached)

variable {X : Source} {N : H2U.PlaceNums} {P : VerifiableInference.Desc.Key.LaterPlaces}

/-- **A record that was reached has the record's half.** -/
theorem rec_of_hist (D : WholeD) (y : (frameAt D (allOf D) D.key₁ 0).E.Str)
    (hp : (FK X N P).planOk = true)
    (hR : RoomFor X.Y.k.oneTime.ranges (Wf.matrixOf X.Y.k.oneTime.lin) X.Y.k.oneTime.codes
      X.Y.k.oneTime.indexMasks.shape)
    (ha : X.Y.k.oneTime.ranges.message.shape.answers ≠ 0) :
    ∀ (k : ℕ), k ≤ 2 + 6 * X.Y.k.oneTime.ranges.lookups.length →
      ∀ a, Hist₁ (VerifiableInference.Desc.Key.descriptionFromSource X N P) D k a → RecAt X k a.2
  | 0, _, a, h => by
    have h' : a.2 = (VerifiableInference.Desc.Key.descriptionFromSource X N P).start₁ a.1 := h
    exact h'
  | k + 1, hk, a, h => by
    obtain ⟨a', b, rs, cols, hr, hb, hd, hf⟩ := Reached.last h
    rw [List.getElem?_map] at hb
    obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 hb
    exact fk_walk (N := N) (P := P) y hp hR ha k (by omega) b₀ hb₀ a'.2 a.2 rs _ hf
      (rec_of_hist D y hp hR ha k (by omega) a' hr) (VerifiableInference.Desc.Plain.held_decide b₀
          a' _ _ a hd).2

end Johnson.RunOne.Law.RecOfHist

#print axioms Johnson.RunOne.Law.RecOfHist.rec_of_hist
