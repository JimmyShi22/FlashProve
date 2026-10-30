-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hears/CheckSkel.lean: the code switch: TWO SMALL CARRIAGES FOR THE TIES
THAT HAVE AN ACCEPTANCE IN HAND.
  check_skel         the program's test on the public sizes says yes AT THE FRONT's SKELETON (the
                     front's statement with the switch's notices received: K2.skelOf, at which the
                     frame is made and KeptFactsOf.lean asks the test) where it says yes at the
                     front's own statement and each message that takes a kept member has a main row
                     (KeptPos). By check_congr (Johnson/Top/H/SwitchPads.lean),
                     K2Hands/AtYes.lean's keptOld_of and the library's stSent_old
  check_skel_atYes   so at AtYes, whose field check has the test at the front's own statement
  listed_of_drawn    a round that draws a position lists one. By the library's ofDraws_index
                     (OnBytes/Slice/BaseYields.lean)
WHY KeptPos. Without it a kept number beyond the front's statement would name the blank message
there and a new message at the skeleton: the two tests could part.
LIMITS. KeptPos is a premise: a clause on the target, which is public. No soundness is claimed.

-/
import Johnson.Top.H0.K2Hears.ThereAtYes
import Johnson.Top.H0.K2Hands.AtYes
import OnBytes.Slice.BaseYields

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model OnBytes.Slice Desc.Plain

theorem check_skel (x : _root_.Tw.K2.Front)
    (hc : switchTargetCheck x.st x.f.rows x.T = true) (hp : KeptPos x.T) :
    switchTargetCheck (skelOf x) x.f.rows x.T = true :=
  (Johnson.Top.H.check_congr x.st (skelOf x) x.f.rows rfl (fun o ho => by
    unfold skelOf
    rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
      stSent_old _ _ _ (keptOld_of hc hp o ho)]) x.T).trans hc

theorem check_skel_atYes {p : P2} {s s' : S} {r₁ r₂ : Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {x : _root_.Tw.K2.Front} {y : _root_.Tw.K2.Sent}
    {S3 : Statement} {Y : Array E} {rows : List OnBytes.Row} {G : Group} {c : Code}
    (A : AtYes p s s' r₁ r₂ gs x y S3 Y rows G c) (hp : KeptPos x.T) :
    switchTargetCheck (skelOf x) x.f.rows x.T = true := check_skel x A.check hp

theorem listed_of_drawn (logN : Nat) (poss : List Nat) (h : poss ≠ []) :
    0 < (Positions.ofDraws logN poss).all.size := by
  obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil h
  obtain ⟨k, hk, -⟩ := ofDraws_index logN (a :: l) a (List.mem_cons_self ..)
  exact Nat.lt_of_le_of_lt (Nat.zero_le k) hk

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.check_skel_atYes
#print axioms VerifiableInference.Desc.First.K2.listed_of_drawn
