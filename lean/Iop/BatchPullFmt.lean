-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/BatchPullFmt.lean: the pattern of rounds `RoundSplits.Fmt` (Iop/BatchFmt.lean) is preserved when
challenges are computed from other uniform strings: the pull-back (Iop/BatchPull.lean) changes
neither the kinds nor the components of the prover messages. (Words of this library:
lean/GLOSSARY.md.)

Notation: `FPhase` (Iop/BatchFmt.lean), with the values `first`, `loc`, `shr`, `aft`: the phase of a
round: before the first round; in the local rounds before the shared ones; in the shared rounds; in
the local rounds after them; `Kind` (Iop/Batch.lean): a round is called shared (`sh`) or local
(`lo`) after its verifier message.
-/
import Iop.BatchFmt
import Iop.BatchPull

namespace Iop

theorem RoundSplits.fmtFrom_pull :
    ∀ {s : Shape} (σ : Samplers s) (A : RoundSplits s) (ph : FPhase),
      RoundSplits.FmtFrom s A ph → RoundSplits.FmtFrom (s.pull σ) (A.pull σ) ph
  | [], _, _, _, _ => trivial
  | _ :: _, (_, σs), (⟨.lo, _, _, _, _, _, _, _, _, _⟩, A), ph, h => ⟨h.1, RoundSplits.fmtFrom_pull σs A ph.afterLo h.2⟩
  | _ :: _, (_, σs), (⟨.sh, _, _, _, _, _, _, _, _, _⟩, A), .loc, h => RoundSplits.fmtFrom_pull σs A .shr h
  | _ :: _, (_, σs), (⟨.sh, _, _, _, _, _, _, _, _, _⟩, A), .shr, h => ⟨h.1, RoundSplits.fmtFrom_pull σs A .shr h.2⟩
  | _ :: _, (_, _), (⟨.sh, _, _, _, _, _, _, _, _, _⟩, _), .first, h => h
  | _ :: _, (_, _), (⟨.sh, _, _, _, _, _, _, _, _, _⟩, _), .aft, h => h

/-- `RoundSplits.Fmt` is preserved by the pull-back. -/
theorem RoundSplits.Fmt.pull {s : Shape} {A : RoundSplits s} (h : A.Fmt) (σ : Samplers s) : (A.pull σ).Fmt :=
  RoundSplits.fmtFrom_pull σ A .first h

end Iop
