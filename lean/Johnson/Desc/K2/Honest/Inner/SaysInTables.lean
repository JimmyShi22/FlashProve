-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K2/Honest/Inner/SaysInTables.lean: WHAT A ROW THAT A CODE SWITCH MAKES SAYS OF WORDS
HANGS ON THE WORDS AT THE CARRYING MESSAGE AND THE COPIES, INSIDE THEIR TABLES AND OFF THE NEW PADS'
PLACES. One statement with its proof; no definition. No coin, no round, no frame.

  `says_inTables` `says_offPads` (Inner/SaysOffPads.lean) with less asked: the two words need be one
                    only at an index i BELOW THE TABLE's SIZE at the statement St at which the row
                    speaks (`tableSize`, Johnson/Desc/Means/Says.lean)

WHY. `Says` sums over a table's indices alone. Beyond a row's length the test `padB`
(Johnson/Desc/SeatAt.lean) says yes in the last main row at every place, while the list `padPlaces`
(OnBytes/Iop/Cs.lean) has no such place: so whoever knows a witness's table only where `padB` says
no cannot pay `says_offPads`' premise at such an index. Inside a main table each place lies below
the row's length, where the codes' lengths are powers of two (`Statement.placeBits`,
`Codes.lengthsOk`, OnBytes/Iop/Ground.lean).

How. `says_offPads`' own proof, with the index's bound carried along. That law follows from this
one; it has been handed in and stays as it is. Kin, not called: the library's `says_agree_in`
(Johnson/Desc/Means/ItemsLen.lean): what a row says reads the words below the tables' sizes alone,
for a row that is `RowIn` a group, at the group's members: no pad is spared there.

Limits. Those of SaysOffPads.lean. Nothing on any property.
-/
import Johnson.Desc.K2.Honest.Inner.SaysOffPads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest
open OnBytes
open OnBytes.Slice (GE rdE coefAt)
open OnBytes.Means (Words Says value onTable tableSize)

/-- **What such a row says hangs on the words inside the tables, off the new pads' places.** -/
theorem says_inTables (St S : Statement) (T : SwitchTarget) (r : OnBytes.Row) (g : Nat)
    (an : Array Nat) (m m' : Words GE) (hOn : OnNew g an (coefAt r))
    (hSp : Spares S T g an (coefAt r))
    (hcov : ∀ o ∈ an.toList, ∃ (a : Nat) (k : KeptTarget),
      T.kept[a]? = some k ∧ an.getD a noId = o)
    (hG : ∀ part i, i < tableSize St g part →
      (∀ p ∈ padPlaces S.codes T.shape, p.part = part → p.index ≠ i) → m g part i = m' g part i)
    (hA : ∀ (a : Nat) (k : KeptTarget), T.kept[a]? = some k → ∀ part i,
      i < tableSize St (an.getD a noId) part →
      (∀ p ∈ padPlaces S.codes k.shape, p.part = part → p.index ≠ i) →
      m (an.getD a noId) part i = m' (an.getD a noId) part i) :
    Says rdE St r m ↔ Says rdE St r m' := by
  have key : ∀ o part, onTable rdE St r m o part = onTable rdE St r m' o part := by
    intro o part
    unfold onTable
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    by_cases e : o = g
    · rw [e] at hi' ⊢
      by_cases hp : ∀ p ∈ padPlaces S.codes T.shape, p.part = part → p.index ≠ i
      · rw [hG part i hi' hp]
      · push Not at hp
        obtain ⟨p, hpm, h1, h2⟩ := hp
        have z : rdE.val (r.coefficient g part i) = 0 := by
          have h0 := hSp.1 p hpm
          rw [h1, h2] at h0
          exact h0
        rw [z, zero_mul, zero_mul]
    · by_cases e' : o ∈ an.toList
      · obtain ⟨a, k, hk, rfl⟩ := hcov o e'
        by_cases hp : ∀ p ∈ padPlaces S.codes k.shape, p.part = part → p.index ≠ i
        · rw [hA a k hk part i hi' hp]
        · push Not at hp
          obtain ⟨p, hpm, h1, h2⟩ := hp
          have z : rdE.val (r.coefficient (an.getD a noId) part i) = 0 := by
            have h0 := hSp.2 a k hk p hpm
            rw [h1, h2] at h0
            exact h0
          rw [z, zero_mul, zero_mul]
      · have z : rdE.val (r.coefficient o part i) = 0 := hOn o e e' part i
        rw [z, zero_mul, zero_mul]
  unfold Says value
  simp only [key]

end VerifiableInference.Desc.K2.Honest

#print axioms VerifiableInference.Desc.K2.Honest.says_inTables
