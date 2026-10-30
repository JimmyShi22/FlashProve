-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/Head/TraceN.lean: the head's identities, with the final normalisation as a parameter.

In the implementation the three numbers of the final normalisation are lines of the parameter file,
with a valid range. Here they are an argument np.
  `N.idn np`      the 17 identities at position i; they read M and ϵ of np
The valid range of np is `NormPar.OK` of Inst/Model/Program.lean (1 ≤ ϵ < 2^48, 24 ≤ M ≤ 47, 17 ≤ K
≤ 32, M − 14 ≤ K). It is a hypothesis of `N.adm` (Inst/Model/Head/NoWrapN.lean) and of
Inst/Model/Head/HonestN.lean (the field `N.HonIn.nf`; `N.honIn_stream`), not of this file.

Notation:
  the head: of the model: its last segment, with the final normalisation and the logits
    (lean/GLOSSARY.md).
Limits: nothing here is about the larger library's chain of stages for the head (the chain's file is
not in this repository), which takes the normalisation from `[scl : Scl]` (`Scl.nf`); that is
`ppref.nf` at the default instance `Scl.ref` (Inst/Model/Scl.lean).
One definition.
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Inst.Model.Head.Trace

set_option autoImplicit false

namespace Inst.Model.Head.N

section Arrays
variable {K : Type} [CommRing K] (np : NormPar) (t : Cells K) (H : ℕ → ℕ → K) (y : Req)

/-- The 17 identities at position i: (JH1) for s = k < 9; k = 9..16: (JH2) to (JH9). M and ϵ are
those of np. -/
def idn (i k : ℕ) : K := Ledger.idn np (Ledger.Wsum nD fun l j => bl t l j i) (fun n => Dv t n i) k

end Arrays

end Inst.Model.Head.N
