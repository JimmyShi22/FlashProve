-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/Mid/CloseStd.lean: at the standard places of
Cb/Pv/KeyLookup/PlStd.lean, the course over the field goes with the plain functions of the closing
and of the test of the bits; no condition on places is left.

The course over the field is our text of the program's lookup, over the field
(Johnson/Desc/First/Look/KeyLaw/Mid/Course.lean). That the program's run, read in the field, is this
course is shown in files that are not in this library yet.

It imports CloseGoesD.lean and Cb/Pv/KeyLookup/PlStd.lean (`ClPl.std`, `pNum`, the bases
`Pub.bParts`, `bKeys`, `bTable`, `bClo`, `bBits`, `ownMasks`); `Lev.offW`, `Lev.grp`, `Lev.partSum`
are those of Cb/Pv/KeyLookup/LevStd.lean, `ownAt` that of
Johnson/Desc/First/Look/KeyLaw/Mid/Relation.lean.
Main names:
  `bParts_own`, `bKeys_own`, `bTable_own`, `bClo_own`, `bBits_own`, `ownMasks_own` where a
  stretch's entries begin by PlStd.lean is how many entries the course has taken up to that seam by
    Relation.lean.
  `pNum_portIdx`, `offW_portIdx` the three numberings of the names of a hiding polynomial's
    coefficients agree.
  `clo_goes_std`, `bits_goes_std` `clo_goes` and `bits_goes` at `ClPl.std A ms`, if ms n is the
    place of the ledger's entry number own + n.
Limits: nothing on the program's blocks on machine words; not shown that the places are apart.

-/
import Johnson.Desc.First.Look.KeyLaw.Mid.CloseGoesD
import Cb.Pv.KeyLookup.PlStd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.Mid.Clo
open Lk6.PortSim Lk6.Clo

open OnBytes OnBytes.Slice Flat Cb Cb.LdLkp Finset Lk6.PortSim

/-! ### the bases -/

theorem ownAt_1 (S : Pub) : ownAt S 1 = 7 + 6 * (S.pl - 2) := by
  first | rfl | simp [ownAt]
theorem ownAt_2 (S : Pub) : ownAt S 2 = ownAt S 1 + 5 * (S.m - 1) := by
  first | rfl | simp [ownAt]
theorem ownAt_4 (S : Pub) : ownAt S 4 = ownAt S 3 +
    (S.parts.map fun v => ((List.range v).map fun l => 2 * l + 5).sum - 2).sum := by
  first | rfl | simp [ownAt]
theorem ownAt_5 (S : Pub) : ownAt S 5 = ownAt S 4 +
    ((List.range S.d).map fun l => 2 * (S.mu + l) + 5).sum := by
  first | rfl | simp [ownAt]

theorem map_range_getD (l : List ℕ) (f : ℕ → ℕ) :
    (List.range l.length).map (fun a => f (l.getD a 0)) = l.map f := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    have hi : i < l.length := by simpa using h1
    simp [List.getD_eq_getElem?_getD, hi]

theorem bParts_own (S : Pub) : S.bParts = ownAt S 1 := (ownAt_1 S).symm

theorem bKeys_own (S : Pub) : S.bKeys = ownAt S 2 := by
  rw [ownAt_2, ← bParts_own]
  rfl

theorem bTable_own (S : Pub) : S.bTable = ownAt S 4 := by
  rw [ownAt_4, ownAt_3, ← bKeys_own]
  show S.bKeys + ((List.range S.parts.length).map fun a =>
    ((List.range (S.parts.getD a 0)).map fun t => 2 * (0 + t) + 5).sum - 2).sum = _
  rw [map_range_getD S.parts fun v => ((List.range v).map fun t => 2 * (0 + t) + 5).sum - 2]
  simp

theorem bClo_own (S : Pub) : S.bClo = ownAt S 5 := by
  rw [ownAt_5, ← bTable_own]
  rfl

theorem bBits_own (S : Pub) : S.bBits = ownAt S 7 := by
  rw [ownAt_7, ownAt_6, ← bClo_own]
  rfl

theorem ownMasks_own (S : Pub) : S.ownMasks = ownAt S 8 := by
  rw [ownAt_8, ← bBits_own]
  show S.bBits + (2 * (S.mu + S.d) + 4) = _
  omega

/-! ### the numberings of names -/

theorem pNum_portIdx {E : Type} [Field E] [Fintype E] : ∀ (l : List (PFmt E)) (i : PIdx l),
    pNum l i = Cf.portIdx l i
  | [], _ => rfl
  | [_], .inl _ => rfl
  | [_], .inr _ => rfl
  | _ :: _ :: _, .inl _ => rfl
  | f :: g :: l, .inr i => congrArg (f.n + ·) (pNum_portIdx (g :: l) i)

theorem offW_portIdx : ∀ (k : ℕ) (i : PIdx (Lev.lk GE k)),
    Lev.offW k i = Cf.portIdx (Lev.lk GE k) i
  | 0, .inl _ => rfl
  | 0, .inr _ => rfl
  | k + 1, .inl t => (portIdx_inl (pfCube GE 2) _ (lk_ne k) t).symm
  | k + 1, .inr i => by
    show 2 + Lev.offW k i = Cf.portIdx (pfCube GE 2 :: Lev.lk GE k) (.inr i)
    rw [portIdx_inr _ _ (lk_ne k), offW_portIdx k i]

/-! ### the two sumchecks at the standard places -/

variable (A : Dat GE) (sl : Slot → A.J) (st : A.St) (own idx : ℕ)

theorem clo_goes_std (ms : ℕ → A.J) (D : Dt) (hD : D.S = A.toPub) (hk : 0 < A.mu + A.d)
    (hr : A.pl ≤ 2 ^ A.mu)
    (hT : ∀ p : Fin A.d → GE,
      D.tabAt (List.ofFn p) = Alg.mle (fun r : Fin A.d → Bool => A.tab st (numLE r)) p)
    (hms : ∀ n, ms n = sl (D.ms (own + n))) :
    Goes (Sim A sl st own idx 5) (Sim A sl st own idx 6) (cClo D) (A.closeRun (ClPl.std A ms))
      A.fmClo :=
  clo_goes A sl st own idx (ClPl.std A ms) D hD hk hr hT fun i => by
    show ms (A.toPub.bClo + pNum _ i) = _
    rw [hms, bClo_own, pNum_portIdx, Nat.add_assoc]

theorem bits_goes_std (ms : ℕ → A.J) (D : Dt) (hD : D.S = A.toPub) (hr : A.pl ≤ 2 ^ A.mu)
    (hms : ∀ n, ms n = sl (D.ms (own + n))) :
    Goes (Sim A sl st own idx 7) (Sim A sl st own idx 8) (cBits D) (A.bitsRun (ClPl.std A ms))
      A.fmBits :=
  bits_goes A sl st own idx (ClPl.std A ms) D hD hr
    (fun i => by
      show ms (A.toPub.bBits + Lev.offW (A.mu + A.d) i) = _
      rw [hms, bBits_own, offW_portIdx, Nat.add_assoc])
    (by
      show ms (A.toPub.bBits + (2 * (A.mu + A.d) + 3)) = _
      rw [hms, bBits_own, Nat.add_assoc]
      have e : 2 * (A.mu + A.d) + 3 = 1 + 2 * (A.mu + A.d) + 2 := by omega
      rw [e])

end Lk6.Mid.Clo

#print axioms Lk6.Mid.Clo.ownMasks_own
#print axioms Lk6.Mid.Clo.pNum_portIdx
#print axioms Lk6.Mid.Clo.offW_portIdx
#print axioms Lk6.Mid.Clo.clo_goes_std
#print axioms Lk6.Mid.Clo.bits_goes_std
