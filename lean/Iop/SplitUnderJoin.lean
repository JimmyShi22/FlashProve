-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/SplitUnderJoin.lean: lemmas on annotations of lists of rounds.

In a protocol with slots (Iop/Batch.lean) every round has an annotation (`RAnn`; for a list of
rounds `RoundSplits`) with its kind, local or shared; a phase (`FPhase`, Iop/BatchFmt.lean) says where a
round is in the pattern of local and shared rounds.
  `RoundSplits.const_app`: the same rule of annotation in every round (`RoundSplits.const f`), on s ++ t, is
      `RoundSplits.app` of the annotations of s and of t
  `RoundSplits.endPhase_allLo`: after a non-empty list of local rounds that begins in the phase ph, the
      phase is `ph.afterLo`
  `RoundSplits.endPhase_allSh`: after shared rounds that begin in the phase `.shr`, the phase is `.shr`
The plans for a split after a merge are not in this file (splits of a merged round: `RCut.unJoin`,
`ACut.unJoin`, Iop/RecutKit.lean).
-/
import Iop.JoinKit
import Iop.SplitData

namespace Iop

/-! ## 3. Lemmas -/

/-- `RoundSplits.const f` on s ++ t is `RoundSplits.app` of those on s and t. -/
theorem RoundSplits.const_app (f : ∀ r : Round, RAnn r) :
    ∀ s t : Shape, RoundSplits.const f (s ++ t) = RoundSplits.app (RoundSplits.const f s) (RoundSplits.const f t)
  | [], _ => rfl
  | r :: s, t => congrArg (Prod.mk (f r)) (RoundSplits.const_app f s t)

theorem RoundSplits.endPhase_allLo :
    ∀ {s : Shape} (A : RoundSplits s) (ph : FPhase),
      s ≠ [] → RoundSplits.AllKind .lo A → RoundSplits.endPhase A ph = ph.afterLo
  | [], _, _, h, _ => absurd rfl h
  | [_], (a, _), ph, _, hA => by
      show FPhase.after a.kind ph = ph.afterLo
      rw [hA.1]
      rfl
  | _ :: r' :: s, (a, A), ph, _, hA => by
      show RoundSplits.endPhase A (FPhase.after a.kind ph) = ph.afterLo
      rw [hA.1, RoundSplits.endPhase_allLo (s := r' :: s) A _ (List.cons_ne_nil _ _) hA.2]
      cases ph <;> rfl

theorem RoundSplits.endPhase_allSh :
    ∀ {s : Shape} (A : RoundSplits s), RoundSplits.AllKind .sh A → RoundSplits.endPhase A .shr = .shr
  | [], _, _ => rfl
  | _ :: _, (a, A), hA => by
      show RoundSplits.endPhase A (FPhase.after a.kind .shr) = .shr
      rw [hA.1]
      exact RoundSplits.endPhase_allSh A hA.2


end Iop
