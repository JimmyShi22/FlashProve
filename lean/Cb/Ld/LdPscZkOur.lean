-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdPscZkOur.lean: the item "masked messages" (`Iop.IOR.Honest.MM`, Ior/Masked.lean) for the
instance with the dummy last variable (`PscOur`, Cb/Ld/LdPsc.lean): the proofs of
`Spec.psc_our_own` and `Spec.psc_our_mm` of Cb/Ld/LdPscZk.lean.
-/
import Cb.Ld.LdPscZkProofs
import Cb.Ld.LdPscProofsOur

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

variable (E : Type) [Field E] [Fintype E]

theorem psc_our_own : Spec.psc_our_own E := psc_our_own_of E (psc_our_sum E)

theorem psc_our_mm : Spec.psc_our_mm E := fun T Ex Wt msg Rd hV hD hO =>
  psc_mm E T.par Ex Wt msg (T.own Rd) ((psc_our_ok E T).1 hV) hD (psc_our_own E T Rd hO)

end Cb
