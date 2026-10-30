-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/Ent/CdNums.lean: one number: the factors of a sample's pad.


Main names: `card_units_GE`.



Terms: lean/GLOSSARY.md.
-/
import Cb.Ref.GlRefNum
import Cb.Ld.LdKappaWorkRef
import Cb.Ld.LdKappaList
import Cb.Ent.EntPar
import Cb.Ent.CdCodes

set_option autoImplicit false

namespace Cb.Ent
open Iop Prob Cb Cb.Ood Cb.Gl.Ref

/-- There are as many factors as field elements other than 0. -/
theorem card_units_GE : Fintype.card GEˣ = Fintype.card GE - 1 := by
  classical
  convert Fintype.card_units (α := GE)

end Cb.Ent
