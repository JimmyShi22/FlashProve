/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
/-
Adapted from Mathlib (https://github.com/leanprover-community/mathlib4), file
Mathlib/RingTheory/Ideal/UFD.lean, commit 5ed2965256430c3649e86755f9576b54eca72435 (v4.34.0), lines
61-65. Licence: Apache-2.0, see ThirdParty/MathlibBackport/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* Only the declarations below are taken over. This Mathlib does not have them.
* The namespace and variable lines around them are written anew, and this is an ordinary Lean file,
  not one of Lean's module system.
-/

import ThirdParty.MathlibBackport.RingTheory.Ideal.Height

variable {R : Type*} [CommRing R] [IsDomain R]
namespace UniqueFactorizationMonoid

theorem isPrincipal_of_height_eq_one [UniqueFactorizationMonoid R]
    {p : Ideal R} [p.IsPrime] (hph : p.height = 1) : p.IsPrincipal := by
  have hpn : p ≠ ⊥ := p.ne_bot_of_height_eq_one hph
  obtain ⟨x, hxmem, hxp⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot ‹_› hpn
  exact ⟨x, p.eq_span_singleton_of_height_eq_one hph hxmem hxp⟩

end UniqueFactorizationMonoid
