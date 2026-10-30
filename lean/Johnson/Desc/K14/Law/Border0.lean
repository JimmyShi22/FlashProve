--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/Border0.lean: the promise at border 0 of the row of the eight blocks (PrmD,
Johnson/Desc/K14/Law/FencedRow.lean) can be met.

  strOf, tabOf_strOf   the oracles' string of a frame that holds a given stored table, and empty
                       columns at every tree.
  prm0_member          at every frame whose stored table has the code's depth, at strOf of tabOfRows
                       of rows before encoding, at a record: from two tests with code on the record
                       (the fence: fenceB, Johnson/Desc/Sound/Fence.lean; the key fits) and a radius
                       below the code's distance.

The library has a stored table made of messages and tails, honestTab (OnBytes/Slice/Honest.lean),
and honest_decodes (OnBytes/K/Oracle/Decodes.lean). No tie from tabOfRows to honestTab is stated
here.

What is not claimed. That the two tests say yes anywhere. That strOf's string is a run's own: it has
no tree, so no decoder can read a message's code word off it. Nothing on the row's pin. Nothing on
soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K14.Law.TabOfRows
import Johnson.Desc.K14.Law.HonestColl
import Johnson.Desc.K14.Law.FencedRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open VerifiableInference.Desc.Sound (Frame fenceB fenceB_iff)

/-- The oracles' string that holds the stored table tab, and empty columns at every tree: as it is
in front of a chain's first block where no tree of the frame's list has been sent. -/
def strOf (F : Frame) (tab : Nat → List UInt64) : F.E.Str :=
  (fun x => (0, tab x.val), fun _ => [])

theorem tabOf_strOf (F : Frame) (tab : Nat → List UInt64) (x : Nat) (h : x < 2 ^ F.a) :
    tabOf (strOf F tab) x = tab x := by
  unfold tabOf
  rw [dif_pos h]
  rfl

/-- **THE PROMISE AT BORDER 0 OF THE ROW OF THE EIGHT IS MET**: at every frame whose stored table
has the code's depth, at the string that holds tabOfRows of rows RwF, at a record d: FROM TWO TESTS
WITH CODE on the record: the fence, and that the key fits. That no seed has a collision is a law at
such a table, for every radius below the code's distance. -/
theorem prm0_member (F : Frame) (lo : Nat) (low : OnBytes.Tree → Option Nat) (P : P14)
    (err eM : Nat)
    (rank : ((Fin P.par.S.fold.index.v → Bool) →
      Fin (P.par.S.fold.index.code.r + P.par.S.fold.index.code.ell) → GE) → Nat)
    (B0 tU tO : Nat) (RwF : Nat → Nat → UInt64) (d : St)
    (hF : F.a = P.par.S.fold.index.code.logN)
    (ha : P.par.S.fold.index.code.logN ≤ 32)
    (hk : P.par.S.fold.index.code.r + P.par.S.fold.index.code.ell ≤
      2 ^ P.par.S.fold.index.code.logN)
    (he : eM < 2 ^ P.par.S.fold.index.code.logN -
      (P.par.S.fold.index.code.r + P.par.S.fold.index.code.ell) + 1)
    (T1 : fenceB lo low B0 d.st d.book d.roots = true)
    (T2 : d.loc.key.fits P.par.S.fold.index = true) :
    PrmD lo low P err eM rank B0 tU tO 0 (d, strOf F (tabOfRows P.par.S.fold RwF)) := by
  refine ⟨(fenceB_iff lo low B0 (fun d : St => d.st) (fun d => d.book) (fun d => d.roots)
    (d, strOf F (tabOfRows P.par.S.fold RwF))).1 T1, ?_, T2⟩
  refine honest_notColl P.par err eM rank _
    (rowsOf P.par.S.fold fun n k => OnBytes.Model.Reading.gl.val (OnBytes.ofF (RwF n k))) ha hk he
    (htab_of_cols P.par _ _ ha fun x hx n hn => ?_) _
  rw [tabOf_strOf F _ x (by rw [hF]; exact hx)]
  exact tabOfRows_col P.par.S.fold RwF x n hn

end Desc.K14.Law
