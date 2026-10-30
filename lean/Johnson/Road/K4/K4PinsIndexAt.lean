-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsIndexAt.lean: THE VALUE's ENTRY v7 OF THE INDEX MASKS, AT THE FILLED SEAT: the
premise that the last tie of the line wo asks of the value's letter idxAt
(Johnson/Road/K4/WoMaskTie.lean, its premise hidx), in that premise's own form; AND A FILLING OF THE
LETTER posI AT WHICH THAT TIE's CONDITION ON THE PLACE IS ONE EQUATION OF NUMBERS. Calls of
`idx_of_fit` (Johnson/Road/K4/K4PinsIndex.lean), and unfolding. No draw, no count.

  **`idx_at_v7`**: under `IndexFit` at n > v7: there is the member u at `N.index` with: at every
    witness w: the value's idxAt, at the pinned part of w and at the value's own v7, is
    `memTab cs arr w u` at posI v7. The value: `(A.seatN …).atRec X p hg`, as in `k4_own_end`.
  `posFree mr`: THE FILLING: entry j lies in the mask table at the library's own `Fmt.Places.freeAt
    mr j` (Fmt/Places.lean: the j-th free entry of a mask table of mr rows: row j % mr, place j /
    mr).
  `posFree_at`: at v7 = k: `posFree mr v7 = (true, k % mr, k / mr)`: the tie's field place.
  **`indexFit_free`**: `IndexFit cs (posFree mr) ms N n`, from: a member u sits at `N.index` · it
    has mr mask rows, and mr is not 0 · n ≤ mr · the length of its mask rows.

OBJECT: none of its own. USER: none yet; meant: the payer of the line wo. LETTERS: those of
K4PinsIndex.lean and of the seat.

Limits. K04_law IS NOT PROVED BY THIS. THAT THE PROGRAMS LAY INDEX MASK j AT THE j-TH FREE ENTRY IS
NOT SHOWN HERE: `posFree` is a filling that makes the two readers of the line wo meet where v7 is
the number of entries taken in front: THAT EQUATION (a group at a time) STAYS A CONDITION ON PUBLIC
LETTERS. A group that is not the first.
-/
import Johnson.Road.K4.K4PinsIndex
import Johnson.Road.K4.K4PinsPlanes
import Fmt.Places

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Road.K4
open Johnson.Pack
open OnBytes.Model (HTailF2)
open OnBytes.Model.Layer (Lay)
open OnBytes.Model.Verify (Public)
open OnBytes.Desc.First.K4 (Par)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.Sound (Mem MsgT InMsg memTab)
open Inst.Model (Scl)

/-- **The value's entry v7 of the index masks is an entry of the witness's own table.** -/
theorem idx_at_v7 [scl : Scl] {Cells Tok : Type} (A : PinPlan Cells) (n' : ℕ) (N : Numbers)
    (tl : HTailF2) (y : Lay) (nM nR nC n0 ns nx v7 : ℕ) (X : Public) (p : Par) (hg : p.g < 12)
    (arr : ℕ → ℕ → ℕ) (ms : List Mem) (m n : ℕ) (cs : OnBytes.Codes)
    (h : IndexFit cs A.posI ms N n) (hv : v7 < n) :
    ∃ u, memAt ms N.index = some u ∧ ∀ w : Wit Cells Tok MsgT,
      ((A.seatN n' N tl y nM nR nC n0 ns nx v7).atRec X p hg).toL.plan.idxAt
          (partOf cs arr ms N m w)
          ((A.seatN n' N tl y nM nR nC n0 ns nx v7).atRec X p hg).toL.plan.v7 =
        memTab cs arr w u (A.posI v7).1 (A.posI v7).2.1 (A.posI v7).2.2 := by
  obtain ⟨u, hu, H⟩ := idx_of_fit (Tok := Tok) A arr ms N m n cs h
  exact ⟨u, hu, fun w => H w v7 hv⟩

/-- **A filling of posI**: the j-th free entry of a mask table of mr rows: the library's own
`Fmt.Places.freeAt` (Fmt/Places.lean: row j % mr, place j / mr), in the mask table. -/
def posFree (mr j : ℕ) : Bool × ℕ × ℕ := (true, Fmt.Places.freeAt mr j)

/-- At v7 = k it is the place that the last tie of the line wo asks. -/
theorem posFree_at {mr v7 k : ℕ} (h : v7 = k) : posFree mr v7 = (true, k % mr, k / mr) := by
  rw [h]
  rfl

/-- **`IndexFit` at that filling.** -/
theorem indexFit_free {cs : OnBytes.Codes} {ms : List Mem} {N : Numbers} {n mr : ℕ} {u : Mem}
    (hu : memAt ms N.index = some u) (hr : (u.1.l.get u.2).1.maskRows = mr) (h0 : 0 < mr)
    (hn : n ≤ mr * (pMask cs (u.1.l.get u.2).1).ell) : IndexFit cs (posFree mr) ms N n := by
  refine ⟨u, hu, fun j hj => ?_⟩
  unfold InMsg
  rw [if_pos (show (posFree mr j).1 = true from rfl)]
  refine ⟨?_, ?_⟩
  · show j % mr < _
    rw [hr]
    exact Nat.mod_lt _ h0
  · show j / mr < _
    exact Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_le hj hn)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.idx_at_v7
#print axioms OnBytes.Road.K4.posFree_at
#print axioms OnBytes.Road.K4.indexFit_free
