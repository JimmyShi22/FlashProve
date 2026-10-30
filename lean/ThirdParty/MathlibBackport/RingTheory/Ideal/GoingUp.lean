/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Yongle Hu
-/
/-
Adapted from Mathlib (https://github.com/leanprover-community/mathlib4), file
Mathlib/RingTheory/Ideal/GoingUp.lean, commit 5ed2965256430c3649e86755f9576b54eca72435 (v4.34.0),
lines 238-241. Licence: Apache-2.0, see ThirdParty/MathlibBackport/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* Only the declarations below are taken over. This Mathlib does not have them.
* The namespace and variable lines around them are written anew, and this is an ordinary Lean file,
  not one of Lean's module system.
* Proof changed, IsIntegral.under_lt_under: one lemma is called by its name in this Mathlib.
-/

import Mathlib.RingTheory.Ideal.GoingUp

namespace Ideal
variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Algebra R A] [Algebra.IsIntegral R A]

theorem IsIntegral.under_lt_under {I J : Ideal A} [I.IsPrime] (I_lt_J : I < J) :
    I.under R < J.under R :=
  let ⟨I_le_J, x, hxJ, hxI⟩ := SetLike.lt_iff_le_and_exists.mp I_lt_J
  comap_lt_comap_of_integral_mem_sdiff I_le_J ⟨hxJ, hxI⟩ (Algebra.IsIntegral.isIntegral x)

end Ideal
