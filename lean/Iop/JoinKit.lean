-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/JoinKit.lean: auxiliary definitions and lemmas for plans that merge rounds (merging:
Iop/Join.lean, Iop/BatchJoin.lean; plans: Iop/Recut.lean, Iop/BatchRecut.lean). (Words of this
library: lean/GLOSSARY.md.)

  `RoundSplits.AllKind k A`       all rounds have the kind k (`RoundSplits.allKind_const`)
  `FPhase.after_after_of_fitMsg`
                           where `FPhase.fitMsg` allows a merge by (J1), the phase (`FPhase`,
                           Iop/BatchFmt.lean) after the two rounds is the phase after the second
                           only
  `Shape.restW`            the argument of `XPlan.maxRunFrom` with which Q begins in `XPlan.app P Q`
                           (Iop/RecutKit.lean: the plan P, then the plan Q)
Notation: `Kind` (Iop/Batch.lean): a round is called shared (`sh`) or local (`lo`) after its
verifier message; `A : RoundSplits s` (there): the annotation of a shape; `FPhase` (Iop/BatchFmt.lean): the
phase of a round: before the first round; in the local rounds before the shared ones; in the shared
rounds; in the local rounds after them; `FPhase.after k ph : FPhase` (Iop/BatchSplit.lean): the
phase after a round of the kind k that has a format in the phase ph; `FPhase.fitMsg k1 k2 ph : Prop`
(Iop/BatchJoin.lean): for (J1): may a round of the kind k1 in the phase ph be merged with the next,
of the kind k2; (J1) (`Round.joinMsg`, Iop/Join.lean): two prover messages as one; the challenge of
the second round; `P : XPlan s` (Iop/Recut.lean): a plan of splits and merges for the list of rounds
s, the original list; `P.maxRunFrom w : ℕ` (there): the largest number of old rounds whose errors
are in a new round, if the first round already counts for w old rounds; `Shape.restW s w : ℕ`, for
`s : Shape`, `w : ℕ`: in `XPlan.maxRunFrom_app` (Iop/RecutKit.lean) it occurs as `s.restW w` for
`P : XPlan s`.
Limits: nothing is said on the protocols of an instance.
-/
import Iop.BatchJoin
import Iop.SplitKit

namespace Iop








/-! ## 1. Kinds -/

/-- All rounds have the kind k. -/
def RoundSplits.AllKind (k : Kind) : {s : Shape} → RoundSplits s → Prop
  | [], _ => True
  | _ :: _, (a, A) => a.kind = k ∧ RoundSplits.AllKind k A

theorem RoundSplits.allKind_const (k : Kind) (f : ∀ r : Round, RAnn r) (hf : ∀ r, (f r).kind = k) :
    ∀ s : Shape, RoundSplits.AllKind k (RoundSplits.const f s)
  | [] => trivial
  | r :: s => ⟨hf r, RoundSplits.allKind_const k f hf s⟩



/-! ## 2. The pattern `RoundSplits.Fmt` (Iop/BatchFmt.lean: the pattern of local and shared rounds that the
compiled scheme supports): one lemma on its phases (`FPhase`) -/


theorem FPhase.after_after_of_fitMsg {k1 k2 : Kind} {ph : FPhase} (h : FPhase.fitMsg k1 k2 ph) :
    FPhase.after k2 (FPhase.after k1 ph) = FPhase.after k2 ph := by
  cases k1 <;> cases k2 <;> cases ph <;> first | rfl | exact h.elim


/-! ## 2a. The largest number of old rounds in a new one (`XPlan.maxRunFrom`, Iop/Recut.lean): one
definition for it -/


/-- the argument w of `XPlan.maxRunFrom` with which Q begins in `XPlan.app P Q`: w itself if P has
no round, else 1 -/
def Shape.restW : Shape → ℕ → ℕ
  | [], w => w
  | _ :: _, _ => 1






end Iop
