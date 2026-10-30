-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Thin/Kinds/BatSplitStep.lean.
A KNOW-ONLY LEMMA FOR EACH KIND OF MOVE. THE KINDS «bat», «split», «step».
K2 LdBatD.goodK: the premise is the library's own (D.Z.OK: on the coefficients): a projection out of
LdBatD.goodT.
K3 LdSplD.goodK: NO PREMISE: the base of the library's ldSpl_good (Cb/Ld/LdSplitProofs.lean:121-131)
reads none of D.Hyp's five: its seven lines are repeated here.
K6 ldMvK_step: three of StepT's five (D2), through G6.
NO THIN DEFINITION OR PREMISE names a bundle, an honest side, a joint's exact relation or core. THE
CONTROLS AND EXAMPLES DO.

-/
import Cb.Thin.Kinds.Rules
import Cb.Req1.LdSegProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Ood IOR IOR.Chain

/-- K2. -/
theorem LdBatD.goodK {E Kc : Type} [Field E] (D : LdBatD E Kc) (h : D.Z.OK) : D.link.GoodK :=
  goodK_of_goodT _ (D.goodT h)

/-- K3: NO PREMISE. -/
theorem LdSplD.goodK {E Kc : Type} [Field E] [Fintype E] (D : LdSplD E Kc) : D.link.GoodK := by
  refine goodK_of_goodB _ (goodB_cf _ _ _ _ _ _ _ _ _ _ _ _ _
    (ldSpl_say Kc _ _ (D.S.Wit × D.Wp) E 0 (splitNx D.S D.St₁ D.St₂ D.St₀) (D.E₀.prod D.S.ext) _
      (D.S.over (claimRels (splitIn D.sl₁ D.sl₂) D.A₀))
      (D.S.over (claimRels (splitOut D.k D.sl₁ D.sl₂) D.A₀)) ?_
      (fun _ _ _ h => h) (fun _ => rfl) ?_))
  · rintro x y w ⟨hE, hA, hin, hr⟩
    exact ⟨hE, hA,
      (ldSpl_sum E D.S D.G₁ D.G₂ D.k D.St₁ D.St₂ D.sl₁ D.sl₂ x.1.1.1 x.1.1.2.1 x.1.1.2.2
        (D.S.msgs w.1)).2 hin, hr⟩
  · rintro x y t w _ ⟨hd, hout, hr⟩
    exact ⟨hd,
      (ldSpl_sum E D.S D.G₁ D.G₂ D.k D.St₁ D.St₂ D.sl₁ D.sl₂ x.1.1.1 x.1.1.2.1 x.1.1.2.2
        (D.S.msgs w.1)).1 t hout,
      hr⟩

/-- K6. -/
theorem ldMvK_step {E Kc : Type} [Field E] [Fintype E] (a b : LdStage E Kc)
    (f : a.X → Option b.X) (g : ExtMap a.Ex b.Ex) (m : a.X × a.W → b.X × b.W)
    (back : a.X × a.Ex.Str → b.W → a.W) (h : IOR.StepK f g back a.J.rels b.J.rels) :
    (LdMv.step a b f g m back).chain.Each (PK Kc) :=
  (each_one _ _).2 ((goodK_iff _).2 (goodK₀_pure a.J.rels b.J.rels f g back h))

/-! ## The controls: (c1): bat: the identity; split: nothing to give; step: Rules.lean. (c2):
-/

example {E Kc : Type} [Field E] (D : LdBatD E Kc) (h : D.Hyp) :
    (D.goodT h).know = (D.goodK h).know := rfl
example {E Kc : Type} [Field E] (D : LdBatD E Kc) (h : D.Hyp) :
    (D.goodT h).onOut = (D.goodK h).onOut := rfl
example {E Kc : Type} [Field E] (D : LdBatD E Kc) (h : D.Hyp) :
    (D.goodT h).isLocal = (D.goodK h).isLocal := rfl
example {E Kc : Type} [Field E] (D : LdBatD E Kc) (h : D.Hyp) :
    (D.goodT h).point = (D.goodK h).point := rfl

example {E Kc : Type} [Field E] [Fintype E] (D : LdSplD E Kc) (h : D.Hyp) :
    (ldSeg_split E Kc D h).base.know = D.goodK.know := rfl
example {E Kc : Type} [Field E] [Fintype E] (D : LdSplD E Kc) (h : D.Hyp) :
    (ldSeg_split E Kc D h).base.onOut = D.goodK.onOut := rfl
example {E Kc : Type} [Field E] [Fintype E] (D : LdSplD E Kc) (h : D.Hyp) :
    (ldSeg_split E Kc D h).base.isLocal = D.goodK.isLocal := rfl
example {E Kc : Type} [Field E] [Fintype E] (D : LdSplD E Kc) (h : D.Hyp) :
    (ldSeg_split E Kc D h).base.point = D.goodK.point := rfl

example {E Kc : Type} [Field E] [Fintype E] (a b : LdStage E Kc) (f : a.X → Option b.X)
    (g : ExtMap a.Ex b.Ex) (m : a.X × a.W → b.X × b.W) (back : a.X × a.Ex.Str → b.W → a.W)
    (h : IOR.StepT f g m back a.J.rels b.J.rels) :
    (goodT_pure _ _ _ _ _ _ _ _ _ f g m back h).know =
      ((each_one _ _).1 (ldMvK_step a b f g m back (stepK_of_stepT h))).know := rfl
example {E Kc : Type} [Field E] [Fintype E] (a b : LdStage E Kc) (f : a.X → Option b.X)
    (g : ExtMap a.Ex b.Ex) (m : a.X × a.W → b.X × b.W) (back : a.X × a.Ex.Str → b.W → a.W)
    (h : IOR.StepT f g m back a.J.rels b.J.rels) :
    (goodT_pure _ _ _ _ _ _ _ _ _ f g m back h).onOut =
      ((each_one _ _).1 (ldMvK_step a b f g m back (stepK_of_stepT h))).onOut := rfl
example {E Kc : Type} [Field E] [Fintype E] (a b : LdStage E Kc) (f : a.X → Option b.X)
    (g : ExtMap a.Ex b.Ex) (m : a.X × a.W → b.X × b.W) (back : a.X × a.Ex.Str → b.W → a.W)
    (h : IOR.StepT f g m back a.J.rels b.J.rels) :
    (goodT_pure _ _ _ _ _ _ _ _ _ f g m back h).isLocal =
      ((each_one _ _).1 (ldMvK_step a b f g m back (stepK_of_stepT h))).isLocal := rfl
example {E Kc : Type} [Field E] [Fintype E] (a b : LdStage E Kc) (f : a.X → Option b.X)
    (g : ExtMap a.Ex b.Ex) (m : a.X × a.W → b.X × b.W) (back : a.X × a.Ex.Str → b.W → a.W)
    (h : IOR.StepT f g m back a.J.rels b.J.rels) :
    (goodT_pure _ _ _ _ _ _ _ _ _ f g m back h).point =
      ((each_one _ _).1 (ldMvK_step a b f g m back (stepK_of_stepT h))).point := rfl

end Cb

#check @Cb.LdBatD.goodK
#check @Cb.LdSplD.goodK
#check @Cb.ldMvK_step
