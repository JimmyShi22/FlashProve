-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/SumSize.lean: how many challenges a masked sumcheck of the output head's
place hands back: as many as its point has coordinates. An equality; Law/HeardBack.lean's
sumcheck_back has the upper bound alone.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law; the last three in Came).
  sumcheck_size: where "sumcheck z n" returns and leaves no round, from a well laid ledger: the
      returned sum's list of challenges has z.size members.
  hear_sizes: where the block's one hearing returns: normed.r has as many members as zt, and
      logits.r as many as zt and lPd more.
  rH_size, rs_size: so, where zt has lt coordinates: rH has lt, and rs has lPd.

Every letter under "there is": none.
What it does not say. THAT zt HAS lt COORDINATES: zt is the end of the lookup's point: that this
point is long enough is a law on the lookup's hearing, not shown here. Nothing on the
normalization's own three sums. Nothing on chance. Nothing on soundness.
-/
import Mathlib
import Johnson.Desc.Kinds.Law.HeardEnds
import Johnson.Desc.Kinds.Law.Cut

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE)
open OnBytes.Model (Fork)
open Part.MaskedSum (readAll Var)
open Norm (lt lPd)

/-- **A masked sumcheck hands back as many challenges as its point has coordinates.** -/
theorem sumcheck_size {z : Point} {n : Nat} {F0 F1 : Fork} {t : List Fmt.RoundView} {S : Sum}
    (hW : WellLaid F0) (h : sumcheck z n F0 t = some (S, F1, [])) : S.r.size = z.size := by
  obtain ⟨c0, R, T, _, hread, _, _, _, hr, _⟩ := sumcheck_ends hW h (fun _ => 0)
  obtain ⟨_, _, _, _, _, _, _, a4, _⟩ := Part.MaskedSum.readAll_spec
    (show readAll ⟨1, z.toList.map (Var.point · 3), some ⟨2, n⟩⟩ t = some R from hread)
  have hlen : R.rounds.length = (z.toList.map (Var.point · 3) ++ [Var.point zeroE 3]).length :=
    (Part.MaskedSum.VarsRead.length a4).2
  rw [hr, List.size_toArray]
  show ((R.rounds.map (·.2)).take (z.toList.map (Var.point · 3)).length).length = z.size
  rw [List.length_take, List.length_map, List.length_map, hlen]
  simp

namespace Came

variable [Sizes] [FinalNorm.In]

/-- **Where the block's one hearing returns: the two sums' numbers of challenges.** -/
theorem hear_sizes {F G : Fork} {rv left : List Fmt.RoundView} {H : HeardAll} (hW : WellLaid F)
    (h : hear F rv = some (H, G, left)) :
    H.2.1.normed.r.size = (FinalNorm.zt).size ∧
      H.2.2.logits.r.size = (FinalNorm.zt).size + lPd := by
  obtain ⟨Fa, Fb, l1, _, wa, wb, hN, hL, _⟩ := hear_parts hW h
  refine ⟨sumcheck_size wa hN, ?_⟩
  rw [sumcheck_size wb hL]
  simp [halves]

/-- Where zt has lt coordinates, the logits' challenges on the position are lt. -/
theorem rH_size {F G : Fork} {rv left : List Fmt.RoundView} {H : HeardAll} (hW : WellLaid F)
    (h : hear F rv = some (H, G, left)) (hzt : (FinalNorm.zt).size = lt) :
    let _ : Heard := H.2.2
    (rH : Point).size = lt := by
  intro _
  have e := (hear_sizes hW h).2
  show (H.2.2.logits.r.extract 0 lt).size = lt
  rw [Array.size_extract, e, hzt]
  omega

/-- And its challenges on the feature are lPd. -/
theorem rs_size {F G : Fork} {rv left : List Fmt.RoundView} {H : HeardAll} (hW : WellLaid F)
    (h : hear F rv = some (H, G, left)) (hzt : (FinalNorm.zt).size = lt) :
    let _ : Heard := H.2.2
    (rs : Point).size = lPd := by
  intro _
  have e := (hear_sizes hW h).2
  show (H.2.2.logits.r.extract lt (lt + lPd)).size = lPd
  rw [Array.size_extract, e, hzt]
  omega

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.sumcheck_size
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.hear_sizes
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.rH_size
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.rs_size
