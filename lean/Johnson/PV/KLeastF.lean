-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/KLeastF.lean: Johnson/PV/KLeast.lean AT THE FULL SIZE's VALUE: LPFD.Full.KF DK DP
  (FastFull.lean: max
  (PV.Front.KFull DK DP) 139):
  **KF_is : LPFD.Full.KF DK DP = W4N.kLeast .two DK OnBytes.Slice.frD.ds DP (seedBS recLg recS).b**:
    the
    floor 139 IS the seed's need less one (seedBS_b_full, OnBytes/Slice/SeedBias.lean)
  **KF_serves | KF_least**: it serves every round of the three files and the seed, and no lesser
    number does
  fitF_iff: the front's row «every round's blocks, and the seed's, fit K» (PV.Front.blocksFitFullB)
    says yes exactly where K serves.
SO «K» IS A VALUE WITH ITS LAW: no reading, no choice.


-/
import Johnson.PV.KLeast
import Johnson.Top.Fire.Code.Vals.FastFull
import Johnson.Top.Fire.Code.PvFront

set_option autoImplicit false

namespace W4N
open OnBytes.Flat OnBytes.Slice OnBytes.Maker _root_.Run _root_.Run.PQ

variable (DK DP : WholeD)

theorem KF_is : LPFD.Full.KF DK DP = kLeast .two DK OnBytes.Slice.frD.ds DP (seedBS recLg recS).b :=
    by
  unfold LPFD.Full.KF kLeast PV.Front.KFull
  rw [seedBS_b_full]

theorem KF_serves : Serves .two DK OnBytes.Slice.frD.ds DP (seedBS recLg recS).b (LPFD.Full.KF DK
    DP) :=
    by
  rw [KF_is]
  exact kLeast_serves ..

theorem KF_least {K : ℕ} (h : Serves .two DK OnBytes.Slice.frD.ds DP (seedBS recLg recS).b K) :
    LPFD.Full.KF DK DP ≤ K := by
  rw [KF_is]
  exact kLeast_least _ _ _ _ _ h

theorem fitF_iff (K : ℕ) : PV.Front.blocksFitFullB DK DP K = true ↔ Serves .two DK
    OnBytes.Slice.frD.ds DP (seedBS recLg recS).b K := by
  unfold PV.Front.blocksFitFullB
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq, PV.Front.seedBlocksFull_eq]
  constructor
  · rintro ⟨a, b⟩
    exact ⟨fun d hd => Nat.le_trans (kThree_key _ _ _ _ d hd) a, fun d hd => Nat.le_trans
        (kThree_entry _ _ _ _ d hd) a,
      fun d hd => Nat.le_trans (kThree_proof _ _ _ _ d hd) a, b⟩
  · intro h
    exact ⟨kThree_le _ _ _ _ _ h, h.seed⟩

end W4N

#print axioms W4N.KF_is
#print axioms W4N.KF_serves
#print axioms W4N.KF_least
#print axioms W4N.fitF_iff
