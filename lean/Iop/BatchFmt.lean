-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/BatchFmt.lean: the pattern of local and shared rounds that the compiled scheme supports.
Definition (`RoundSplits.Fmt`), and the case of local rounds only. (Words of this library:
lean/GLOSSARY.md.)

The compiled verifier of one slot (Compile/Batch/Verifier.lean) goes through the rounds with a
phase. Kind and phase fix the format of the Fiat-Shamir query, and with it which components of the
prover message are sent:
  a local round                                  the slot's component only
  the first shared round (the joining round)     both components
  a later shared round                           the shared component only
  a shared round at the start, or after the local rounds that follow the shared ones: no format;
  the verifier rejects.
For a component that is not sent, the verifier uses the fixed symbol (`Round.IsPoint.zero`) at its
oracle positions and the plain part of the round's fixed message (`Round.dPlain`). So completeness
needs such a component to be empty: it has no oracle position, and only one value. `RoundSplits.Fmt` says
this, and that every round has a format: the kinds run lo+ sh* lo* (or there is no round at all).

Comparison with `RoundSplits.OneBlock` (Iop/Batch.lean), the pattern (Sh). `Fmt` does not ask for a shared
round, so an ordinary IOP (local rounds only) has it (`RoundSplits.fmt_allLocal`). It asks in addition that
an unsent component has no oracle position (`own`), which `OneBlock` does not ask.
-/
import Iop.Batch

namespace Iop

/-- the phase of a round: before the first round; in the local rounds before the shared ones; in the
shared rounds; in the local rounds after them -/
inductive FPhase
  | first
  | loc
  | shr
  | aft
  deriving DecidableEq

/-- the phase after a local round -/
def FPhase.afterLo : FPhase → FPhase
  | .first => .loc
  | .loc => .loc
  | .shr => .aft
  | .aft => .aft

/-- the shared component of the round is empty: no oracle position, one value -/
def RAnn.NoShared {r : Round} (a : RAnn r) : Prop := (∀ p, a.own p = true) ∧ Subsingleton a.M0

/-- the slot's component of the round is empty -/
def RAnn.NoSlot {r : Round} (a : RAnn r) : Prop := (∀ p, a.own p = false) ∧ Subsingleton a.Mj

/-- From the phase ph on, every round has a format, and a component that is not sent is empty. -/
def RoundSplits.FmtFrom : (s : Shape) → RoundSplits s → FPhase → Prop
  | [], _, _ => True
  | _ :: s, (a, A), ph =>
      match a.kind, ph with
      | .lo, ph => a.NoShared ∧ RoundSplits.FmtFrom s A ph.afterLo
      | .sh, .loc => RoundSplits.FmtFrom s A .shr
      | .sh, .shr => a.NoSlot ∧ RoundSplits.FmtFrom s A .shr
      | .sh, .first => False
      | .sh, .aft => False

/-- Every round has a format; an unsent component is empty. -/
def RoundSplits.Fmt {s : Shape} (A : RoundSplits s) : Prop := RoundSplits.FmtFrom s A .first

theorem RAnn.noShared_ofSlot (k : Kind) (r : Round) : (RAnn.ofSlot k r).NoShared :=
  ⟨fun _ => rfl, inferInstanceAs (Subsingleton Unit)⟩

theorem RAnn.noSlot_ofShared (k : Kind) (r : Round) : (RAnn.ofShared k r).NoSlot :=
  ⟨fun _ => rfl, inferInstanceAs (Subsingleton Unit)⟩

theorem RoundSplits.fmtFrom_allLocal : ∀ (s : Shape) (ph : FPhase), RoundSplits.FmtFrom s (RoundSplits.allLocal s) ph
  | [], _ => trivial
  | r :: s, ph => ⟨RAnn.noShared_ofSlot .lo r, RoundSplits.fmtFrom_allLocal s ph.afterLo⟩

/-- An ordinary IOP, with local rounds only, satisfies `RoundSplits.Fmt`. -/
theorem RoundSplits.fmt_allLocal (s : Shape) : (RoundSplits.allLocal s).Fmt := RoundSplits.fmtFrom_allLocal s .first

end Iop
