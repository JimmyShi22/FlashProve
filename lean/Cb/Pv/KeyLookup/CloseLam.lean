-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/CloseLam.lean: the join point, the closing, the zero point and the test of the bits,
gathered for the chain: all four `Know`, and their shares of the list of rounds.

It imports Join.lean, Bits.lean and Cb/Pv/KeyLookup/Lam.lean; no file of the port.

The four blocks, each a `BkK A.XS A.XS Ex`: `A.joinK Ex`, `A.closeK P SK`, `A.zeroK Ex`,
`A.bitsK P SK` (P: the places of the masks; SK: the sumcheck as a letter).
  `four_know_lib` all four at the library's verifier are `Know` between their joints, if pl ≤ 2^mu.
  `join_lam`, `zero_lam`   errors (`Err.toList`) and numbers of values (`Shape.chalList`) are the
                  columns c and n of `lamJoin`, `lamZero`; q := the number of elements of E.
  `clo_lam`, `bits_lam`   the same for `lamClo`, `lamBits`, at the library's verifier.
  `clo_e`, `bits_e`   for any letter SK the block's errors and shape are the letter's at that
                  sumcheck: steps without rounds add none.
  `join_small`, `zero_small`   if mu < q (mu + d < q) the count of bad values is below the number of
                  values (`Err.Small`). No clause of `Pub.Adm` bounds mu from above, so this is a
                  condition of its own.

-/
import Cb.Pv.KeyLookup.Join
import Cb.Pv.KeyLookup.Bits
import Cb.Pv.KeyLookup.Lam

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Iop IOR Hiop Prob Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn

/-- g q^(g − 1) is below q^g if g is below q. -/
theorem Clo.point_small (g q : ℕ) (h : g < q) : g * q ^ (g - 1) < q ^ g := by
  cases g with
  | zero => simp
  | succ g =>
    have hp : 0 < q ^ g := Nat.pow_pos (by omega)
    rw [Nat.add_sub_cancel, pow_succ, Nat.mul_comm (q ^ g) q]
    exact (Nat.mul_lt_mul_right hp).2 h

namespace Dat
variable {E : Type} [Field E] [Fintype E] (A : Dat E) (P : ClPl A) (Ex : ExtSpec)

/-- At the two points: if mu < q (mu + d < q) the count of bad values is below the number of values
(the library's `Err.Small`). -/
theorem join_small (h : A.mu < Fintype.card E) : (A.joinK Ex).e.Small := by
  refine ⟨?_, trivial⟩
  show A.mu * Fintype.card E ^ (A.mu - 1) < Fintype.card (Fin A.mu → E)
  rw [Fintype.card_fun, Fintype.card_fin]
  exact Clo.point_small _ _ h

theorem zero_small (h : A.mu + A.d < Fintype.card E) : (A.zeroK Ex).e.Small := by
  refine ⟨?_, trivial⟩
  show (A.mu + A.d) * Fintype.card E ^ (A.mu + A.d - 1) < Fintype.card (Fin (A.mu + A.d) → E)
  rw [Fintype.card_fun, Fintype.card_fin]
  exact Clo.point_small _ _ h

/-- All four at the library's verifier. -/
theorem four_know_lib (hr : A.pl ≤ 2 ^ A.mu) (Kc M Wp : Type) (R0 : Rels Kc A.St Ex (M × Wp))
    (msg : M → A.J → E) (Mu : A.St → (A.J → E) → Prop) :
    (A.joinK Ex).Know (A.jt R0 msg Mu A.Roots) (A.jt R0 msg Mu A.Joined) ∧
    (A.closeK P (PscLtK.lib E Ex)).Know (A.jt R0 msg Mu fun x μ => A.Table x μ A.d)
      (A.jt R0 msg Mu A.Closed) ∧
    (A.zeroK Ex).Know (A.jt R0 msg Mu A.Closed) (A.jt R0 msg Mu A.Zero) ∧
    (A.bitsK P (PscLtK.lib E Ex)).Know (A.jt R0 msg Mu A.Zero) (A.jt R0 msg Mu A.Bitten) :=
  ⟨A.join_know hr Ex Kc M Wp R0 msg Mu,
    A.close_know P Kc M Wp _ R0 msg Mu (A.close_lib P Kc M Wp _),
    A.zero_know Ex Kc M Wp R0 msg Mu,
    A.bits_know P Kc M Wp _ R0 msg Mu (A.bits_lib P Kc M Wp _)⟩

theorem clo_e (SK : PscLtK E Ex) :
    (A.closeK P SK).e.toList = (SK.core (A.En P).par).e.toList ∧
    (A.closeK P SK).R.shape = (SK.core (A.En P).par).R.shape := ⟨rfl, rfl⟩

theorem bits_e (SK : PscLtK E Ex) :
    (A.bitsK P SK).e.toList = (SK.full (A.BT P).par).e.toList ∧
    (A.bitsK P SK).R.shape = (SK.full (A.BT P).par).R.shape := ⟨rfl, rfl⟩

theorem join_lam :
    (A.joinK Ex).e.toList = (lamJoin (Fintype.card E) A.toPub).map (·.c) ∧
    (A.joinK Ex).R.shape.chalList = (lamJoin (Fintype.card E) A.toPub).map (·.n) := A.join_errs Ex

theorem zero_lam :
    (A.zeroK Ex).e.toList = (lamZero (Fintype.card E) A.toPub).map (·.c) ∧
    (A.zeroK Ex).R.shape.chalList = (lamZero (Fintype.card E) A.toPub).map (·.n) := A.zero_errs Ex

theorem clo_lam :
    (A.closeK P (PscLtK.lib E Ex)).e.toList = (lamClo (Fintype.card E) A.toPub).map (·.c) ∧
    (A.closeK P (PscLtK.lib E Ex)).R.shape.chalList =
      (lamClo (Fintype.card E) A.toPub).map (·.n) := by
  have h := A.close_errs P (Ex := Ex)
  refine ⟨h.1.trans ?_, h.2.trans ?_⟩
  · simp [lamClo, psc]
  · simp [lamClo, psc, Nat.add_comm]

theorem bits_lam :
    (A.bitsK P (PscLtK.lib E Ex)).e.toList = (lamBits (Fintype.card E) A.toPub).map (·.c) ∧
    (A.bitsK P (PscLtK.lib E Ex)).R.shape.chalList =
      (lamBits (Fintype.card E) A.toPub).map (·.n) := by
  have h := A.bits_errs P (Ex := Ex)
  refine ⟨h.1.trans ?_, h.2.trans ?_⟩
  · simp [lamBits, psc, pscErrs]
  · simp [lamBits, psc, pscVals]

end Dat
end Lk6

#print axioms Lk6.Dat.join_know
#print axioms Lk6.Dat.close_know
#print axioms Lk6.Dat.zero_know
#print axioms Lk6.Dat.bits_know
#print axioms Lk6.Dat.four_know_lib
#print axioms Lk6.Dat.en_holds
#print axioms Lk6.Dat.bt_sum
#print axioms Lk6.Dat.plane_dead
#print axioms Lk6.Dat.join_small
#print axioms Lk6.Dat.zero_small
#print axioms Lk6.Dat.join_lam
#print axioms Lk6.Dat.clo_lam
#print axioms Lk6.Dat.zero_lam
#print axioms Lk6.Dat.bits_lam
#print axioms Lk6.Dat.en_vars_at
#print axioms Lk6.Dat.en_Y
#print axioms Lk6.Dat.bt_vars_at
