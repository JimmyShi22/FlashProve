-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/PosAt.lean: two facts on the reading of the positions at the readings of
ReadingRd.lean, in the words in which the tie of the code switch's law asks them
(Johnson/Top/H0/K2Hands/TiePaid.lean: the clauses `len` and `reads` of `PlanAt`).

  len_at: what a kind is shown of the second written round has just the plan's number of positions
  reads_at: where the positions have a reading Qs, position number i of Qs is the drawn position
      number i modulo 2 ^ p.logN, p the place's numbers under `P2At`
  pass_of_pos: and there the round's test of work has passed
Limits: those of ReadingRd.lean and P2At.lean. Nothing on soundness. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.LawAt
import Johnson.Top.H0.K2Caller.P2At

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.Flat OnBytes.Maker Iop
open OnBytes.Tie.Pv.Row (rvOne)

variable {r : SwRow} (d₁ d₂ : RDT)

theorem len_at (w : K2Wr r d₁ d₂) (m : (wT d₂).Msg) (c : (wT d₂).Chal) :
    (vN d₂ m c).drawn.poss.length = baseCount r.set .request r.g :=
  poss_len d₁ d₂ w m c

/-- Where the positions have a reading, the round's test of work has passed. -/
theorem pass_of_pos (a t : ℕ) (m : (wT d₂).Msg) (c : (wT d₂).Chal) (Qs : Fin t → Fin (2 ^ a))
    (h : posOfD a t (shownW d₂ (voidP t) m c).drawn = some Qs) : passOf d₂ c = true := by
  by_contra hp
  have hp' : ¬ GChal.pass (b := d₂.entry.work) (c : (wRound (toRD d₂)).Chal) = true := hp
  unfold shownW at h
  rw [if_neg hp'] at h
  have h' : posOfL a t (List.replicate (t + 1) 0) = some Qs := h
  unfold posOfL at h'
  rw [if_neg (by simp)] at h'
  cases h'

theorem reads_at {p : K2.P2} (hp : P2At r p) (t : ℕ) (m : (wT d₂).Msg) (c : (wT d₂).Chal)
    (Qs : Fin t → Fin (2 ^ r.g.main.logN))
    (h : posOfD r.g.main.logN t (shownW d₂ (voidP t) m c).drawn = some Qs) (i : Fin t) :
    (Qs i).val = (vN d₂ m c).drawn.poss.getD i.val 0 % 2 ^ p.logN := by
  have q := pass_of_pos d₂ _ t m c Qs h
  rw [shownW_pass d₂ _ m c q] at h
  have h' : posOfL r.g.main.logN t (rvOne d₂ m c).drawn.poss = some Qs := h
  unfold posOfL at h'
  split at h'
  · have e := Option.some.inj h'
    rw [← e, hp.logN]
    rfl
  · cases h'

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.len_at
#print axioms VerifiableInference.Desc.First.K2Caller.pass_of_pos
#print axioms VerifiableInference.Desc.First.K2Caller.reads_at
