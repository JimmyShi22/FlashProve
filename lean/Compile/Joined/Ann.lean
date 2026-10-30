-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Joined/Ann.lean: in a file with three joined hash chains every round has a format of the
compiled scheme, and a component that is not sent is empty.

A second form of the compiler's verifier side, beside the library's own. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.

Compile/Joined/Types.lean lays three chains in a row as one batch protocol, with the annotation
`Chains.ann`: front and chain 1 local, the joining round, chain 2 shared, seam and chain 3 local.
Iop/BatchFmt.lean says which patterns of local and shared rounds the compiled verifier has a format
for (`RoundSplits.Fmt`): local rounds, then shared ones, then local ones.

Main names:
  `Chains.ann_fmt`     the annotation of a file has `RoundSplits.Fmt`, if the joining round is shared
  `fmtFrom_local_app`, `fmtFrom_shared_app`   local rounds, or shared rounds in which the shared
                       part alone is sent, before what follows

Limits: nothing on the verifier of a file, and nothing on soundness. Of the joining round
`RoundSplits.Fmt` asks only its kind: both its components are sent.
No other file of the library uses a name of this file yet; OnBytes/TypedOracleCompiler/Joined/Clauses.lean imports
it.

Terms: lean/GLOSSARY.md.

-/
import Compile.Joined.Types
import Iop.BatchFmt

set_option autoImplicit false

namespace Compile.Joined
open Iop

/-- local rounds before what follows, from a phase that a local round does not change -/
theorem fmtFrom_local_app {t : Shape} (B : RoundSplits t) (ph : FPhase) (hph : ph.afterLo = ph) :
    ∀ s : Shape, RoundSplits.FmtFrom t B ph → RoundSplits.FmtFrom (s ++ t) (RoundSplits.app (RoundSplits.allLocal s) B) ph
  | [], h => h
  | r :: s, h =>
    ⟨RAnn.noShared_ofSlot .lo r, hph.symm ▸ fmtFrom_local_app B ph hph s h⟩

/-- shared rounds in which the shared part alone is sent, before what follows -/
theorem fmtFrom_shared_app {t : Shape} (B : RoundSplits t) :
    ∀ s : Shape, RoundSplits.FmtFrom t B .shr →
      RoundSplits.FmtFrom (s ++ t) (RoundSplits.app (RoundSplits.const (RAnn.ofShared .sh) s) B) .shr
  | [], h => h
  | r :: s, h => ⟨RAnn.noSlot_ofShared .sh r, fmtFrom_shared_app B s h⟩

namespace Chains
variable (G : Chains)

/-- from the joining round on -/
theorem annJ_fmt (h : G.Laws) : RoundSplits.FmtFrom G.shJ G.annJ .loc := by
  have h2 : RoundSplits.FmtFrom (G.s₂ ++ G.sh₃)
      (RoundSplits.app (RoundSplits.const (RAnn.ofShared .sh) G.s₂) G.ann₃) .shr :=
    fmtFrom_shared_app G.ann₃ G.s₂ (RoundSplits.fmtFrom_allLocal G.sh₃ .shr)
  unfold annJ RoundSplits.FmtFrom
  rw [h.kindJ]
  exact h2

/-- Every round of a file has a format, and a component that is not sent is empty, if the joining
round is shared. -/
theorem ann_fmt (h : G.Laws) : G.ann.Fmt :=
  ⟨RAnn.noShared_ofSlot .lo G.rF, fmtFrom_local_app G.annJ .loc rfl G.s₁ (G.annJ_fmt h)⟩

end Chains

end Compile.Joined
