-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Tie/Sample.lean: the left-hand side, on words, of an answer's equation
(K1.sampleRow, Johnson/Desc/K1/Own.lean) is K1's closed form K1.Msg.form on the oracle message's own
two tables, under three premises; and what an entry of a pad adds to it.
Terms: Johnson/SendSim/Defs.lean, "Terms of the model"; Johnson/SendSim/At/Sim.lean, "Terms". Limits
of the folder: Johnson/SendSim/Defs.lean.

As in Johnson/SendSim/Tie/Value.lean, an equation is OnBytes.Row, and words give a value to each
index of each table of each oracle message, as K1 indexes them. sampleRow m o z β i y is the
equation of answer i of oracle message o at the seed with the point z and the factor β; m holds the
oracle message's public numbers (Msg.of).

What this file proves, for every statement S, oracle message, seed and words, by algebra on finite
sums. The three premises: S has the oracle message o; it has a main or a mask table; the point z has
at least the m.v coordinates that the oracle message reads.
  value_sampleRow      Under the three premises, the left-hand side of sampleRow m o z β i y on the
                       words w is m.form (readL z) (readE β) i (w o), a linear form only in the two
                       tables of o.
  coef_sampleRow_pad   Under the last two premises, if the pads fit into their row of the table
                       (padFits), k is an answer and t < m.e: the equation's coefficient at entry t
                       of the pad of answer k is the seed's factor times θ^t if k = i, and 0
                       otherwise.
  value_sampleRow_pad  Under all these premises, adding s at that entry adds that coefficient times
                       s to the left-hand side. So the pad of answer k changes only the equation of
                       answer k.

Limits. No lemma here requires that a factor is not 0.

How it fits. value_stAt (Johnson/SendSim/At/Stat.lean) applies value_sampleRow to the honest
sender's answers; that serves rowsExact and rowsFresh through ans_tie
(Johnson/SendSim/At/Answers.lean). No other file of Johnson/SendSim/ applies the two lemmas on the
pad: they state in the library's own terms what "pad" means (Johnson/SendSim/At/Sim.lean, "answer,
pad"), and the proofs at the instance use Msg.weight_pad directly. Msg.form is in
Johnson/Desc/K1/Law/Law.lean. The proof of value_sampleRow follows that of K1.says_iff
(Johnson/Desc/K1/Law/SaysTie.lean), which contains the equation. It rests on K1.meansLaw
(Johnson/Desc/K1/Law/Means2.lean), Msg.weight_pad and Msg.padIdx_lt_size
(Johnson/Desc/K1/Law/Catches.lean) and tableSize_eq (Johnson/Desc/K1/Law/SaysTie.lean).

The other names.
  lt_size_of_get   the number of an oracle message that the statement has is below the statement's
                   number of oracle messages.
-/
import Johnson.Desc.K1.Law.SaysTie
import Johnson.SendSim.Tie.Value

set_option autoImplicit false

namespace OnBytes.SendSim
open OnBytes OnBytes.Slice VerifiableInference.Desc VerifiableInference.Desc.K1

/-- If the statement has an oracle message at the number o, then o is below the statement's number
of oracle messages. -/
theorem lt_size_of_get (S : Statement) (o : ℕ) (x : OnBytes.Oracle)
    (hx : S.oracles[o]? = some x) : o < S.oracles.size := by
  by_contra h
  rw [Array.getElem?_eq_none (Nat.le_of_not_lt h)] at hx
  cases hx

/-- If the statement has the oracle message o, it has a main or a mask table, and z has at least the
coordinates that it reads, then the left-hand side of the equation of answer i on the words w is
K1's closed form Msg.form on the two tables w o. -/
theorem value_sampleRow (S : Statement) (o : ℕ) (x : OnBytes.Oracle)
    (hx : S.oracles[o]? = some x) (z : List E) (β : E) (i : ℕ) (y : E) (w : Means.Words GE)
    (hne : ((Msg.of S.codes x.shape).K != 0 || (Msg.of S.codes x.shape).Kzk != 0) = true)
    (hz : (Msg.of S.codes x.shape).v ≤ z.length) :
    Means.value rdE S (sampleRow (Msg.of S.codes x.shape) o z β i y) w =
      (Msg.of S.codes x.shape).form (readL z) (readE β) i (w o) := by
  obtain ⟨_, _, h0, hc⟩ := meansLaw (Msg.of S.codes x.shape) o z β i y hne hz
  have ho := lt_size_of_get S o x hx
  have hT : ∀ part, Means.onTable rdE S (sampleRow (Msg.of S.codes x.shape) o z β i y) w o part =
      ∑ j ∈ Finset.range ((Msg.of S.codes x.shape).size part),
        (Msg.of S.codes x.shape).weight (readL z) (readE β) i part j * w o part j := fun part => by
    unfold Means.onTable
    rw [tableSize_eq S o x hx part]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← hc part j (Msg.lt_of_size _ part j (Finset.mem_range.1 hj))]
    rfl
  unfold Means.value
  rw [Finset.sum_eq_single o, hT, hT]
  · rfl
  · intro o' _ hne'
    have hz0 : ∀ part, Means.onTable rdE S (sampleRow (Msg.of S.codes x.shape) o z β i y) w o'
        part = 0 := fun part => by
      unfold Means.onTable
      refine Finset.sum_eq_zero fun j _ => ?_
      have := h0 o' part j hne'
      unfold coefAt at this
      rw [rdE_val, this, zero_mul]
    rw [hz0, hz0, add_zero]
  · intro h
    exact absurd (Finset.mem_range.2 ho) h

/-- If the oracle message has a table, z has at least the coordinates that it reads, the pads fit
(padFits), k is an answer and t < m.e, then the coefficient of the equation of answer i at entry t
of the pad of answer k is the seed's factor times θ^t if k = i, and 0 otherwise. -/
theorem coef_sampleRow_pad (m : Msg) (o : ℕ) (z : List E) (β : E) (i : ℕ) (y : E) (k t : ℕ)
    (hne : (m.K != 0 || m.Kzk != 0) = true) (hz : m.v ≤ z.length) (hf : m.padFits = true)
    (hk : k < m.answers) (ht : t < m.e) :
    rdE.val ((sampleRow m o z β i y).coefficient o m.padPart (m.padIdx k t)) =
      if k = i then readE β * readE (thetaE t) else 0 := by
  obtain ⟨_, _, _, hc⟩ := meansLaw m o z β i y hne hz
  have h := hc m.padPart (m.padIdx k t)
    (Msg.lt_of_size _ _ _ (m.padIdx_lt_size hne hf k t hk ht))
  rw [m.weight_pad (readL z) (readE β) i k t hk ht] at h
  exact h

/-- Under the premises of value_sampleRow and coef_sampleRow_pad, adding s to the words at entry t
of the pad of answer k adds that coefficient times s to the left-hand side of the equation of answer
i. -/
theorem value_sampleRow_pad (S : Statement) (o : ℕ) (x : OnBytes.Oracle)
    (hx : S.oracles[o]? = some x) (z : List E) (β : E) (i : ℕ) (y : E) (w : Means.Words GE)
    (k t : ℕ) (s : GE)
    (hne : ((Msg.of S.codes x.shape).K != 0 || (Msg.of S.codes x.shape).Kzk != 0) = true)
    (hz : (Msg.of S.codes x.shape).v ≤ z.length) (hf : (Msg.of S.codes x.shape).padFits = true)
    (hk : k < (Msg.of S.codes x.shape).answers) (ht : t < (Msg.of S.codes x.shape).e) :
    Means.value rdE S (sampleRow (Msg.of S.codes x.shape) o z β i y)
        (w + oneAt o (Msg.of S.codes x.shape).padPart
          ((Msg.of S.codes x.shape).padIdx k t) s) =
      Means.value rdE S (sampleRow (Msg.of S.codes x.shape) o z β i y) w +
        (if k = i then readE β * readE (thetaE t) else 0) * s := by
  rw [value_add_oneAt rdE S _ w o _ _ s (lt_size_of_get S o x hx)
    (by rw [tableSize_eq S o x hx]; exact Msg.padIdx_lt_size _ hne hf k t hk ht),
    coef_sampleRow_pad _ o z β i y k t hne hz hf hk ht]

end OnBytes.SendSim

#print axioms OnBytes.SendSim.value_sampleRow
#print axioms OnBytes.SendSim.coef_sampleRow_pad
#print axioms OnBytes.SendSim.value_sampleRow_pad
