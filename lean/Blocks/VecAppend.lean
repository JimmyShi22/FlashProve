-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/VecAppend.lean: what a vector keeps when two lists of rounds are concatenated.

`vL` and `vR` (Blocks/BlockFront.lean) send a vector of the rounds s, or of the rounds t, to the
same vector among those of s ++ t. It keeps its number of positions read (`vq`), its role (`vrole`:
tested, promised or pad) and its field (`vover`: over F, else over E), as `vcode_vL`, `vrows_vL`, ..
of Blocks/BlockFront.lean say for code and rows.
-/
import Blocks.BlockFront

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Blocks
open Iop

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem vq_vL :
    ∀ {s t : Shape} (d : EncData F E s) (d' : EncData F E t) (v : VIdx s d),
      vq _ (d.app d') (vL d d' v) = vq s d v
  | _ :: _, _, (_, _), _, .inl _ => rfl
  | _ :: _, _, (_, d), d', .inr v => vq_vL d d' v

theorem vq_vR :
    ∀ {s t : Shape} (d : EncData F E s) (d' : EncData F E t) (v : VIdx t d'),
      vq _ (d.app d') (vR d d' v) = vq t d' v
  | [], _, _, _, _ => rfl
  | _ :: _, _, (_, d), d', v => vq_vR d d' v

theorem vrole_vL :
    ∀ {s t : Shape} (d : EncData F E s) (d' : EncData F E t) (v : VIdx s d),
      vrole _ (d.app d') (vL d d' v) = vrole s d v
  | _ :: _, _, (_, _), _, .inl _ => rfl
  | _ :: _, _, (_, d), d', .inr v => vrole_vL d d' v

theorem vrole_vR :
    ∀ {s t : Shape} (d : EncData F E s) (d' : EncData F E t) (v : VIdx t d'),
      vrole _ (d.app d') (vR d d' v) = vrole t d' v
  | [], _, _, _, _ => rfl
  | _ :: _, _, (_, d), d', v => vrole_vR d d' v

theorem vover_vL :
    ∀ {s t : Shape} (d : EncData F E s) (d' : EncData F E t) (v : VIdx s d),
      vover _ (d.app d') (vL d d' v) = vover s d v
  | _ :: _, _, (_, _), _, .inl _ => rfl
  | _ :: _, _, (_, d), d', .inr v => vover_vL d d' v

theorem vover_vR :
    ∀ {s t : Shape} (d : EncData F E s) (d' : EncData F E t) (v : VIdx t d'),
      vover _ (d.app d') (vR d d' v) = vover t d' v
  | [], _, _, _, _ => rfl
  | _ :: _, _, (_, d), d', v => vover_vR d d' v

end Blocks
