-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/ReachLinks.lean: "REACHED" FROM ONE CHAIN's LAST BORDER TO THE NEXT CHAIN's
FIRST (ReachThree.lean): what rchAt₂_zero and rchAt₃_zero take is what the chain in front hands out
at its last border.

  endAt₁_of         RchAt at the first chain's last border is EndAt₁
  endAt₂_of         RchAt₂ at the shared chain's last border is EndAt₂, at the statement re-nested
  rchAt₂_start, rchAt₃_start   so: from the last border of the chain in front to border 0

No soundness statement.

-/
import Johnson.Top.H0.Walk.ReachThree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open VerifiableInference.Desc (FileDescription)

section
variable {Xi Str Str' : Type} {F : FileDescription Xi}

theorem endAt₁_of {a : (F.XiPub × F.S₁) × Str} (h : RchAt F F.first.blocksInOrder.length a) :
    EndAt₁ F a.1 := h

theorem endAt₂_of {a : ((F.XiPub × F.S₁) × F.S₂) × Str}
    (h : RchAt₂ F F.shared.blocksInOrder.length a) : EndAt₂ F (a.1.1.1, a.1.1.2, a.1.2) := ⟨h.1, h.2⟩

theorem rchAt₂_start {a : (F.XiPub × F.S₁) × Str} (h : RchAt F F.first.blocksInOrder.length a) (y : Str') :
    RchAt₂ F 0 ((a.1, F.start₂ a.1.1), y) := rchAt₂_zero a.1 y (endAt₁_of h)

theorem rchAt₃_start {a : ((F.XiPub × F.S₁) × F.S₂) × Str}
    (h : RchAt₂ F F.shared.blocksInOrder.length a) {s : F.S₃}
    (hs : F.start₃ a.1.1.1 a.1.1.2 a.1.2 = .ok s) (y : Str') :
    RchAt₃ F 0 (((a.1.1.1, a.1.1.2, a.1.2), s), y) := rchAt₃_zero _ s y hs (endAt₂_of h)

end

#print axioms rchAt₂_start
#print axioms rchAt₃_start

end Johnson.Desc.First.Walk.Tied
