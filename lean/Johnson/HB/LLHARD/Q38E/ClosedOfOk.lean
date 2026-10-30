-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/Q38E/ClosedOfOk.lean: three general laws for the closed side of `DigAheadOk`
(Johnson/Desc/First/Look/K3DigitsAhead.lean): at every cell of the digits' array in the range of
which that condition speaks, the lookups' condition on public data `DigOK` and the test
`DgP.colsTest` give a seat, that the seat lies in its table, and that what the messages hold at the
cell is the caller's reading there: for every tuple of messages.

Row or tool. Tools: general in all letters; no scope, nothing evaluated. For the law on the digits
of the sub-protocol K8: the condition `DigAheadOk` at the state behind the draw of the approximate
range proof.

What it spends. No row of the entry tests and no field of the head.

What is here (namespace Q38).
  `zzCol_at`: the column of the digits' array at matrix μ, plane b and row i of cells is `b * tl.mz
    + (DgP.offOf tl μ + i)`. An unfolding of `HTailF2.zzCol` (OnBytes/Model/Tail.lean).
  `reads_range`: under `colsTest`, that cell is among the addresses that the digits' lookup reads
    (`ReadsDig`, Johnson/Desc/First/Look/K3Caller.lean): by `DgP.dgP_col_lt`
    (OnBytes/Tie/Pv/Lookup/Digits/PortCols.lean).
  `closed_of_ok`: so `DigOK.resolves` gives the seat and that it fits, and `msgAt_val`
    (Johnson/Desc/First/Look/K3CallerBase.lean) the equation of the two readings.

Limits. `DigOK` and `colsTest` are premises. Nothing on soundness.


-/
import Johnson.Desc.First.Look.K3Caller
import OnBytes.Tie.Pv.Lookup.Digits.PortCols

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Q38
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Look

/-- **The column of a digit.** -/
theorem zzCol_at (tl : HTailF2) {μ b i : ℕ} (hμ : μ < tl.NM) (hb : b < 2)
    (hi : i < (tl.mats.getD μ {}).m) :
    (tl.zzCol μ b 0).getD 0 + i = b * tl.mz + (DgP.offOf tl μ + i) := by
  have hc : (decide (μ < tl.NM) && decide (b ≤ 1) && decide (0 < (tl.mats.getD μ {}).m)) =
      true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hμ, by omega⟩, by omega⟩
  unfold HTailF2.zzCol DgP.offOf
  rw [if_pos hc, Option.getD_some]
  omega

/-- **The cell is among the addresses that the digits' lookup reads.** -/
theorem reads_range (tl : HTailF2) (first : ℕ) (hc : DgP.colsTest tl = true) {μ u i b : ℕ}
    (hμ : μ < tl.NM) (hu : u < tl.tau) (hi : i < (tl.mats.getD μ {}).m) (hb : b < 2) :
    ReadsDig tl first (.cell tl.ix.ZZ u ((tl.zzCol μ b 0).getD 0 + i)) := by
  rw [zzCol_at tl hμ hb hi]
  have hlt : DgP.offOf tl μ + i < tl.mz := DgP.dgP_col_lt hc hμ hi
  rcases Nat.lt_succ_iff_lt_or_eq.1 hb with hb0 | rfl
  · obtain rfl : b = 0 := Nat.lt_one_iff.1 hb0
    rw [Nat.zero_mul, Nat.zero_add]
    exact ReadsDig.low (⟨_, hlt⟩, ⟨u, hu⟩)
  · rw [Nat.one_mul]
    exact ReadsDig.high (⟨_, hlt⟩, ⟨u, hu⟩)

/-- **The seat, that it fits, and the equation of the two readings, for every tuple of messages.**
-/
theorem closed_of_ok {set : Params.Setting} {x : Place} {tl : HTailF2} {D : Sent}
    {rad : OracleShape → ℕ} {pp : ℕ} (H : DigOK set x tl D rad pp)
    (hc : DgP.colsTest tl = true) {μ u i b : ℕ} (hμ : μ < tl.NM) (hu : u < tl.tau)
    (hi : i < (tl.mats.getD μ {}).m) (hb : b < 2) :
    ∃ z, seatOf D x.link (.cell tl.ix.ZZ u ((tl.zzCol μ b 0).getD 0 + i)) = some z ∧
      z.Fits D.codes (digList x D rad) ∧
      ∀ m : (digSg x D rad).Msg,
        digVal x D rad m (.cell tl.ix.ZZ u ((tl.zzCol μ b 0).getD 0 + i)) =
          some (digMsg x D rad m (enOf x.arrays (tl.ix.ZZ, u, (tl.zzCol μ b 0).getD 0 + i))) := by
  have hr := reads_range tl x.F.next hc hμ hu hi hb
  obtain ⟨-, z, h2, h3⟩ := H.resolves _ hr
  exact ⟨z, h2, h3, fun m => msgAt_val _ _ _ H.resolves hr m⟩

end Q38


#print axioms Q38.zzCol_at
#print axioms Q38.reads_range
#print axioms Q38.closed_of_ok
