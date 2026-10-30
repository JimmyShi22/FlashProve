-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/StaysBehind.lean: every block's stage leaves the strings as Stays says
(Stays.lean), at the number of the first tree that the stretch sends: by cellStays and colStays
(Johnson/Desc/Sound/StringsStay.lean).

  stays_behind

No soundness statement.

-/
import Johnson.Top.H0.Walk.Stays
import Johnson.Desc.Sound.StringsStay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open OnBytes.Maker
open _root_.Run.PQ (CK)
open VerifiableInference.Desc.Sound

theorem stays_behind (C : CK) (F : Frame) (b : Nat) (ds : List RDT) (y : F.E.Str)
    (τ : Iop.Tr (uLT C ds)) : Stays b (strsOf F y) (strsOf F (behind C F b ds y τ)) :=
  ⟨fun x => cellStays C F b ds y τ x, fun j x hj => colStays C F b ds y τ j x hj⟩

#print axioms stays_behind

end Johnson.Desc.First.Walk.Tied
