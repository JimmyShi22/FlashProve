-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/ChainList.lean: the numbers of a preamble, read off the numbers of a chain of IORs.

In standard terms: book-keeping for the sequential composition of interactive oracle reductions.



Definitions. A preamble starts at the encoded index alone and leaves the
encoded index, unchanged, beside a function of the oracles that its prover sent.
A chain is a sequential composition (`IOR.seq`) of
interactive oracle reductions (`IOR`, Ior/Ior.lean).


Main name: `preNums`: see its doc comment.








Limits: this file gives no protocol.

Terms: lean/GLOSSARY.md.
-/
import Hiop.Chain
import Hiop.ListNums
import Ior.ChainProofs

set_option autoImplicit false

namespace Hiop
open Iop Prob IOR
open scoped ENNReal

/-! ## The numbers of a preamble -/

/-- The numbers of a preamble, read off the numbers of a chain. -/
def preNums {K Xi Xo : Type} {Ei Eo : ExtSpec} {F : IOR Xi Ei Xo Eo} (P : IOR.Nums K F) :
    PreNums F :=
  ⟨P.err, P.pBad, P.pHid, P.bud⟩

end Hiop
