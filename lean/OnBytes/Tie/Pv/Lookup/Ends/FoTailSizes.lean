-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoTailSizes.lean.
The sizes of the calls' points in the record of a smallness test's lookup.

kf_ext and tail_four_law (OnBytes/Tie/Pv/Lookup/Ends/FoTailKf.lean,
OnBytes/Tie/Pv/Lookup/Ends/FoTailLaw.lean) ask that the point of call q in the record has as many
coordinates as the key numbers of the call (tl.zOf q).call have bits. This file gets that premise
from a run of Forest.pad, which tests the points' sizes against the calls of its shape, and from a
test of public numbers that can be run.

* pad_zk_size: in a run of Forest.pad that returns, cut by
  OnBytes/Tie/Pv/Lookup/Forest/FoPadCut.lean (the premise is PadCut, which pad_cut there gives of
  such a run), the point of call k in the record has the number of coordinates that call k of the
  shape says, for k below the shape's number of calls.
* callsTest tl: the two calls of the smallness test's shape say the numbers of its records z1, z2.
* tail_zk_size: so the premise of tail_four_law holds, where the shape of the run is tl.f9 and has
  two calls, and callsTest tl is true.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoPadCut
import OnBytes.Model.Tail

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

/-- The point of call k in the record has the size that the shape's call says. -/
theorem pad_zk_size {calls : Array Call} {pub : Array Nat} {lid : ℕ} {F F' : Fork} {c c' : Ctx}
    {g : Forest.Heard} {M : PadMid} (hc : PadCut calls pub lid F c g F' c' M) (k : ℕ)
    (hk : k < (M.h pub).NC) :
    (g.zk.getD k #[]).size = (((M.h pub).calls[k]?).map (·.n)).getD 0 := by
  have h1 := List.all_eq_true.1 hc.point k (List.mem_range.2 hk)
  rw [hc.heard]
  exact beq_iff_eq.1 h1

/-- The shape's two calls say the numbers of the smallness test's own records. -/
def callsTest (tl : HTailF2) : Bool :=
  [0, 1].all fun q => ((tl.f9.calls[q]?).map (·.n)).getD 0 == (tl.zOf q).call.n

/-- The premise of tail_four_law on the points' sizes. -/
theorem tail_zk_size {calls : Array Call} {pub : Array Nat} {lid : ℕ} {F F' : Fork} {c c' : Ctx}
    {g : Forest.Heard} {M : PadMid} (hc : PadCut calls pub lid F c g F' c' M) (tl : HTailF2)
    (hs : M.h pub = tl.f9) (h2 : tl.f9.NC = 2) (ht : callsTest tl = true) :
    ∀ q < 2, (g.zk.getD q #[]).size = (tl.zOf q).call.n := by
  intro q hq
  have h1 := pad_zk_size hc q (by rw [hs, h2]; exact hq)
  have h3 : (((tl.f9.calls[q]?).map (·.n)).getD 0 == (tl.zOf q).call.n) = true :=
    List.all_eq_true.1 ht q (by
      rcases Nat.lt_succ_iff_lt_or_eq.1 hq with h | h
      · obtain rfl : q = 0 := by omega
        simp
      · subst h
        simp)
  rw [h1, hs]
  exact beq_iff_eq.1 h3

end Fo
