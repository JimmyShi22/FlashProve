-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/CountsBchks.lean: under the library's statement on Reed-Solomon codes as a hypothesis:
the count of exceptional points for a main row of a stage at a radius below the Johnson radius.

OnBytes/Slice/BlocksJohnson.lean takes off the blocks of a proximity test below the Johnson radius
under a hypothesis of its own, `Sg.CountsAt`: two numbers bound the exceptional points of a line,
one for a main row, one for a repeated mask row. This file leads the first of the two back to the
library's statement on codes, in its form at one pair of fields (`Cb.BCHKS46At`,
Cb/Gen/CodeListRSAt.lean; where it is proved and where not: "Not claimed" below): a bound,
`bchksBound n k e`, on the
exceptional points of a line through two words for a Reed-Solomon code of n distinct points and
degree at most k (k is the bound on the degree: the code has k + 1 coefficients), at radii e with n
k < (n - e)^2. A main row of a stage is a word of such a code (`onCode_iff_onRS`,
OnBytes/Slice/NumbersHalf.lean). The proof is that of `mca_half_self` there, with the statement
on codes in the place of the theorem within half the distance. The second number is a theorem where
2 e is below the repeated mask code's own distance (`Sg.countsAt_of_main`). So at such a stage and
radius `Sg.CountsAt` follows from the statement on codes. That reaches little: the mask code's
distance is at most the number of positions n, so nothing here on the mask row reaches a radius of
n/2 or more, while the Johnson radius of a main code of rate below 1/4 lies above n/2; and at a
stage whose mask code has the main code's rate nothing here reaches beyond half the distance.
Elsewhere the mask row's number is not had in this file: OnBytes/Slice/MaskBchks.lean has it, from
the same assumed statement, at the price of a list. The main row's number follows at every radius
below the Johnson radius (`mca_bchks_self` asks nothing of the mask code).

Main theorems.
 `mca_bchks_self`     one row read at the code's own positions: at most b exceptional points, for
                      every whole number b that is at least `bchksBound`.
 `Sg.countsAt_bchks`  `Sg.CountsAt` at b and the mask row's count by source.
 `mixed_countsAt`     the conditions on sizes and radius are met together beyond half the distance,
                      at a stage made by hand.

Not claimed. This is no proof of soundness at the Johnson radius. `Cb.BCHKS46At` is a hypothesis of
every theorem here; no theorem of this file has a proof of it laid in. Cb/Bridge/
proves it from the files under ThirdParty/, adapted from ArkLib and Mathlib
(`bchks46At`, Cb/Bridge/CodeListRSProved.lean; lean/LIMITS.md, L15). By the
library's own comments it restates a theorem that a public preprint states with an
outline of a proof (IACR ePrint 2025/2055, Theorem 4.6, at M = 1); for this
library no full proof of it on paper was checked; that the Lean text says what the
preprint's theorem says rests on a reading outside this file, which is not
machine-checked: this file does not compare the two. It
speaks of all lengths, degree bounds, radii and sets of points in GF: one false instance would empty
every theorem here. Nothing where 2 e is not below the repeated mask code's own distance.
`bchksBound` is a real number that is evaluated nowhere here: no number is stated. That it is the
planner's `johnsonCount` (OnBytes/Params/Distance.lean) is not shown; by a reading the two are one
formula only where the setting reads the theorem's m as printed. There, for 3 ≤ m, k > 0 and a
radius e ≤ (1 - a) n, for an agreement a that is at least the one which belongs to m as printed, it
is at most the formula that the planner's count encloses, at a rate and a distance that its
arguments enclose (`bchksBound_le_countAt`, OnBytes/Params/LibraryJohnson.lean;
`enclR_johnsonCount`, OnBytes/Params/JohnsonLaws.lean). Nothing on the batching, a stored table, its
link, a record, a proof or a file.

-/
import Cb.Gen.CodeListRSAt
import OnBytes.Slice.BlocksJohnson

set_option autoImplicit false

namespace OnBytes.Slice
open Cb Prob Polynomial
open Cb.CodeListRS

/-- Under the statement on codes: one row read at the code's own positions, at a radius e other than
0 with n k < (n - e)^2, where n = 2^a and k, the number of coefficients less one, is not 0. A line
has at most b exceptional points, for every whole number b that is at least `bchksBound n k e`. -/
theorem mca_bchks_self (hA : BCHKS46At GF GE) (Cd : Fmt.M1.Code) (ha : Cd.a ≤ 32)
    (hk : 0 < Cd.r + Cd.l - 1) (e : ℕ) (he : 0 < e)
    (hj : 2 ^ Cd.a * (Cd.r + Cd.l - 1) < (2 ^ Cd.a - e) ^ 2) (b : ℕ)
    (hb : bchksBound (2 ^ Cd.a) (Cd.r + Cd.l - 1) e ≤ (b : ℝ)) : (ldOf Cd Cd.a).MCAat e b := by
  intro f₀ f₁
  have hK : 0 < Cd.r + Cd.l := by omega
  have h := hA (2 ^ Cd.a) (Cd.r + Cd.l - 1) e (ptOf Cd.a) (ptOf_inj Cd.a ha) hk he hj
    (fun x => (ldOf Cd Cd.a).T f₀ x ()) (fun x => (ldOf Cd Cd.a).T f₁ x ())
  have h2 := h.trans hb
  refine le_trans (cnt_mono fun θ hθ => ?_) (Nat.cast_le.1 h2)
  obtain ⟨S, hS, h1, hn⟩ := hθ
  rw [Fintype.card_fin] at hS
  exact ⟨S, hS, (onCode_iff_onRS Cd hK _ S).1 h1, fun hc =>
    hn ⟨(onCode_iff_onRS Cd hK _ S).2 hc.1, (onCode_iff_onRS Cd hK _ S).2 hc.2⟩⟩

namespace Sg
variable {s : Sg}

/-- **From the library's assumed statement to the named hypothesis**, at a radius e other than 0,
below the Johnson radius of the stage, with 2 e below the repeated mask code's own distance, for a
main code with at least two coefficients. -/
theorem countsAt_bchks (hA : BCHKS46At GF GE) (h : s.Sized) (hp : s.Pos)
    (hk : 0 < s.C.r + s.C.l - 1) {e : ℕ} (he : 0 < e) (hj : s.InJ e) (h2 : 2 * e < s.dZ) (b : ℕ)
    (hb : bchksBound (2 ^ s.C.a) (s.C.r + s.C.l - 1) e ≤ (b : ℝ)) :
    s.CountsAt e b (s.cntZ e) := by
  refine countsAt_of_main h hp h2 (mca_bchks_self hA s.C h.small hk e he ?_ b hb)
  have h1 : s.d ≤ s.dC := min_le_left _ _
  have h3 := h.roomC
  have h4 : s.C.r + s.C.l - 1 ≤ 2 ^ s.C.a - s.d := by
    unfold Sg.dC at h1
    omega
  exact lt_of_le_of_lt (Nat.mul_le_mul_left _ h4) hj.2

end Sg

/-- The conditions on sizes and radius are met together beyond half the distance: at the stage made
by hand `mixedSg` (no file's) and the radius 2,400,000 the named hypothesis follows from the
statement on codes alone, at every whole number b that is at least `bchksBound`. -/
theorem mixed_countsAt (hA : BCHKS46At GF GE) (b : ℕ)
    (hb : bchksBound (2 ^ mixedSg.C.a) (mixedSg.C.r + mixedSg.C.l - 1) 2400000 ≤ (b : ℝ)) :
    mixedSg.CountsAt 2400000 b (mixedSg.cntZ 2400000) :=
  Sg.countsAt_bchks hA mixed_sizes.1 mixed_sizes.2.1 (by decide +kernel) (by decide) mixed_inJ.1
    mixed_inJ.2.2.2 b hb

end OnBytes.Slice
