-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/Pub/Skel.lean: FIVE RELATIONS: what of a panel, of a list of panels
and of the weight claims' environment a return of the sub-protocol K4's pure functions can hang on
(OnBytes/Model/LayerPanels.lean). Definitions, and that each relation holds of a thing and itself.

Limits. THAT A RETURN HANGS ON NO MORE THAN THESE FIELDS IS NOT SHOWN HERE: the choice of the fields
is by reading the text of stackEndOf, facRs, facEw, claim, headWeights and claimE; Panels.lean,
End.lean and Claims.lean show it, function by function. No function is shown to return at any plan.
No property is claimed.

  SideSkel    two sides of a panel: both are absent, or both are forms that are there at the same
              rows and columns.
  BlkSkel     two panels: the flag, the numbers and the two sides. NOT in it, since they are read
              for elements alone: claim, ec, wt, sl, xx.
  PanSkel     two lists of panels, member by member, and the number of the next weight claim.
  EndSkel     two states of the batched sumcheck's end: the bits of the down product's panel.
  ClaimSkel   two environments of the weight claims: the layout, the group, the weights' layout, the
              number of challenges, the size of each call's point. NOT in it: rt, rope, v.sc, v.tab,
              v.K3, v.iU3.
-/
import OnBytes.Flat.LinksFreeLayer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.RtPub
open OnBytes OnBytes.Model OnBytes.Model.Layer
open OnBytes.Flat (All2 OptRel)

/-- Two sides of a panel: both are absent, or both are forms that are there at the same rows and
columns. -/
def SideSkel (A A₀ : Option (Nat → Nat → Option Aff)) : Prop :=
  OptRel (fun f f₀ => ∀ i yv, (f i yv).isSome = (f₀ i yv).isSome) A A₀

/-- Two panels: what the end of the batched sumcheck reads of a panel before it returns. -/
structure BlkSkel (b b₀ : SBlk) : Prop where
  tri : b.tri = b₀.tri
  v0 : b.v0 = b₀.v0
  ni : b.ni = b₀.ni
  ny : b.ny = b₀.ny
  wy : b.wy = b₀.wy
  w : b.w = b₀.w
  off : b.off = b₀.off
  virt : b.virt = b₀.virt
  A : SideSkel b.A b₀.A
  B : SideSkel b.B b₀.B

/-- Two lists of panels, member by member, and the number of the next weight claim. -/
structure PanSkel (s s₀ : Panels) : Prop where
  bl : All2 BlkSkel s.bl.toList s₀.bl.toList
  nextV : s.nextV = s₀.nextV

/-- Two states of the batched sumcheck's end: the bits of the down product's panel. -/
def EndSkel (s s₀ : StackEnd) : Prop := s.wD = s₀.wD

/-- Two environments of the weight claims: what a claim's return and its factors' sizes read. -/
structure ClaimSkel (c c₀ : ClaimEnv) : Prop where
  y : c.v.y = c₀.v.y
  g : c.v.g = c₀.v.g
  lay : c.wsLay = c₀.wsLay
  rs : c.rs.size = c₀.rs.size
  zk : ∀ q, (c.v.zk.getD q #[]).size = (c₀.v.zk.getD q #[]).size

theorem SideSkel.refl (A : Option (Nat → Nat → Option Aff)) : SideSkel A A :=
  OptRel.refl (fun _ _ _ => rfl) A

theorem BlkSkel.refl (b : SBlk) : BlkSkel b b :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, SideSkel.refl _, SideSkel.refl _⟩

theorem PanSkel.refl (s : Panels) : PanSkel s s := ⟨All2.refl BlkSkel.refl _, rfl⟩

theorem EndSkel.refl (s : StackEnd) : EndSkel s s := rfl

theorem ClaimSkel.refl (c : ClaimEnv) : ClaimSkel c c := ⟨rfl, rfl, rfl, rfl, fun _ => rfl⟩

/-- The empty list of panels. -/
theorem PanSkel.nil : PanSkel {} {} := PanSkel.refl _

end OnBytes.Desc.First.K4.RtPub

#print axioms OnBytes.Desc.First.K4.RtPub.SideSkel.refl
#print axioms OnBytes.Desc.First.K4.RtPub.BlkSkel.refl
#print axioms OnBytes.Desc.First.K4.RtPub.PanSkel.refl
#print axioms OnBytes.Desc.First.K4.RtPub.EndSkel.refl
#print axioms OnBytes.Desc.First.K4.RtPub.ClaimSkel.refl
#print axioms OnBytes.Desc.First.K4.RtPub.PanSkel.nil
