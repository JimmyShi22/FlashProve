-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/PointsAtReach.lean: THE SMALLNESS TEST: THE VERIFIER's TEST `pointsHeld`
(OnBytes/Model/Tail.lean: the lookup's weights of the two calls and the calls' points are those of a
second computation) FROM THE LIBRARY's PROMISE ON WHAT THE DIGITS' LOOKUP HAS HEARD (`K3Left`,
Johnson/Top/H/K3LeftStatement.lean), THE PUBLIC TEST `heldPubB`
(Johnson/Desc/K8/Honest/HeldPublic.lean) AND ONE SENTENCE ON THE TWO WEIGHTS. The half on the calls'
points is shown; the half on the weights is a premise. Lemmas; none of the library's goals.

  `pub_more` the public test ⊢ f9.rK = io + 1 · f9.iota = #[io, io], with io the number that the
                   tests' text reckons
  `point_at`   a call's point, coordinate by coordinate
  **`points_zk`** K3Left … tl.f9 … g · the public test · two calls ⊢ each call's point is (zy_1, ..,
                   zy_io | zx)
  **`pointsHeld_of_weights`** these, and: each call's weight is the second computation's ⊢
                   pointsHeld tl g = true
WRITTEN A FURTHER TIME: `point_at` is another house's `zk_getD`, and the last proof's closing lines
`pointsHeld_of` (Johnson/Desc/ProofFile/Honest/K3/Law/DigitsPoints.lean: no part of the library)
, which goes from what the lookup's maker of the structure returns; here from the
library's promise at a state.
Limits. THE SENTENCE ON THE WEIGHTS IS A PREMISE HERE; it is shown in
Johnson/Desc/K8/Honest/WeightsAtReach.lean where the words of the key point's coordinate zy_0 lie
below the prime. No state stands in this file. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.HeldPublic
import Johnson.Top.H.K3LeftStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.OnPublicFiles (K3Left)

/-- Two more numbers of the shape, off the public test. -/
theorem pub_more {tl : HTailF2} (hP : heldPubB tl = true) :
    tl.f9.rK = tl.z1.call.n - min tl.z1.call.n tl.lidb + 1 ∧
      tl.f9.iota = #[tl.z1.call.n - min tl.z1.call.n tl.lidb,
        tl.z1.call.n - min tl.z1.call.n tl.lidb] := by
  unfold heldPubB at hP
  rw [Bool.and_eq_true] at hP
  have p1 := hP.1
  simp only [HTailF2.forestHeld, Bool.and_eq_true, beq_iff_eq] at p1
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, q5⟩, q6⟩, -⟩, -⟩, -⟩, -⟩ := p1
  exact ⟨q5, q6⟩

/-- A call's point, coordinate by coordinate. -/
theorem point_at (zy zx : Array E) (io : Nat) (hy : zy.size = io + 1) (i : Nat) :
    (zy.extract 1 zy.size ++ zx).getD i zeroE =
      if i < io then zy.getD (1 + i) zeroE else zx.getD (i - io) zeroE := by
  have hsz : (zy.extract 1 zy.size).size = io := by
    simp only [Array.size_extract]
    omega
  simp only [Array.getD_eq_getD_getElem?]
  by_cases hi : i < io
  · rw [if_pos hi, Array.getElem?_append_left (by rw [hsz]; exact hi), Array.getElem?_extract]
    simp [hy, hi]
  · rw [if_neg hi, Array.getElem?_append_right (by rw [hsz]; omega), hsz]

/-- **Each call's point is the second computation's.** -/
theorem points_zk {tl : HTailF2} {g : Forest.Heard} {lm : Nat} {F₀ F' : Fork}
    {rs : TwV.Rounds Cb.Gl.E} (K : K3Left Reading.gl tl.f9 lm F₀ F' g rs)
    (hP : heldPubB tl = true) (nc : tl.f9.NC = 2) (q : Nat) (hq : q < 2) (i : Nat) :
    (g.zk.getD q #[]).getD i zeroE =
      if i < tl.z1.call.n - min tl.z1.call.n tl.lidb then g.zy.getD (1 + i) zeroE
      else g.zx.getD (i - (tl.z1.call.n - min tl.z1.call.n tl.lidb)) zeroE := by
  obtain ⟨n1, n2⟩ := pub_more hP
  have hy : g.zy.size = tl.z1.call.n - min tl.z1.call.n tl.lidb + 1 := K.zy.trans n1
  have hi : tl.f9.iota.getD q 0 = tl.z1.call.n - min tl.z1.call.n tl.lidb := by
    rw [n2]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hq with h | h
    · obtain rfl : q = 0 := by omega
      rfl
    · subst h
      rfl
  have k := (K.zkRaw q (by omega)).2
  rw [hi, n1, Nat.add_sub_cancel_left] at k
  rw [k]
  exact point_at _ _ _ hy i

/-- **The test, from the weights.** -/
theorem pointsHeld_of_weights {tl : HTailF2} {g : Forest.Heard} {lm : Nat} {F₀ F' : Fork}
    {rs : TwV.Rounds Cb.Gl.E} (K : K3Left Reading.gl tl.f9 lm F₀ F' g rs)
    (hP : heldPubB tl = true) (nc : tl.f9.NC = 2)
    (he : ∀ q, q < 2 → g.e.getD q zeroE = callWeightAgain g q) : tl.pointsHeld g = true := by
  unfold HTailF2.pointsHeld
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, List.all_eq_true,
    beq_iff_eq]
  exact ⟨⟨he 0 (by omega), fun i _ => points_zk K hP nc 0 (by omega) i⟩,
    he 1 (by omega), fun i _ => points_zk K hP nc 1 (by omega) i⟩

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.pub_more
#print axioms VerifiableInference.Desc.First.K8.Honest.point_at
#print axioms VerifiableInference.Desc.First.K8.Honest.points_zk
#print axioms VerifiableInference.Desc.First.K8.Honest.pointsHeld_of_weights
