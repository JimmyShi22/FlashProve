-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSplitVProofs.lean: the proofs of the statements of Cb/Ld/LdSplitV.lean (batch proofs: how a
sub-protocol for one instance is run for N instances, once in each or once for all).
-/
import Cb.Ld.LdSplitV
import Cb.Ld.LdFrontProofs
import Ior.LinkVMaskedRulesProofs

set_option autoImplicit false

namespace Iop
open Prob IOR

theorem link_sh_kb : Spec.link_sh_kb := by
  intro K A B l N kA kB F h hon hz hF
  have h1 := knowB_joining _ _ _ _ _ _ l.R (RAnn.ofShared .sh) (fun _ => rfl) N _ _ _ _ _ h
  rw [hz] at h1
  exact ⟨knowB_conseq _ _ _ _ _ _ _ _ N _ _ _ _ _ _ _ _ _ _ h1 (fun _ _ => trivial)
      (fun a _ => hon a) (fun _ _ _ w => w) (fun _ _ w => w),
    sameKey_shared _ _ _ _ _ _ l.R N kA.key kB.key F hF⟩

theorem mm_tagPub : Spec.mm_tagPub := fun _ _ _ _ _ _ _ _ _ _ h =>
  ⟨h.noOrc, h.free, h.run, fun xp k M hc => ⟨h.stable xp k.1 M hc.1, hc.2⟩,
    fun k xp ρ hc => h.law k.1 xp ρ hc.1⟩

/-- Nothing hidden is withheld by a masked block. (`H.Hid w x = ∅`, under `h : H.MM D`) -/
theorem mm_noHid {Xi Xo : Type} {Ei Eo : ExtSpec} {R : IOR Xi Ei Xo Eo} {Wi Wo : Type}
    {H : R.Honest Wi Wo} {D : MaskData R Wi} (h : H.MM D) (w : Wi) (x : Xi) : H.Hid w x = ∅ :=
  (Set.union_empty_iff.1 (h.free w x)).2

theorem link_loV_pm : Spec.link_loV_pm := by
  intro K N A B l D VA tieB qB g hBad hb ht hn hH
  exact
    { base :=
        { isLocal := g.base.isLocal
          acc := accV_local _ _ _ _ l.R _ _ VA.W0 l.H A.rels.rel B.rels.rel VA.rel
            (JV.rel (⟨VA.W0, tieB, qB⟩ : JV N B)) g.base.acc (mm_noHid g.mm) (fun _ _ _ h => h.1)
            (fun x y w c ρ h _ hRo => ⟨hRo, ht x y w c ρ h⟩)
          bears := fun J ρ Us hU => ⟨fun _ => hb _ _, hn J ρ Us hU⟩
          her := hH }
      mm := mmV_local _ _ _ _ l.R _ _ VA.W0 l.H D N g.mm hBad
      claim := fun x y w h => g.claim x y w.2 h.1
      free := funext fun _ =>
        funext fun _ => funext fun _ => propext ⟨fun _ => trivial, fun _ _ => hb _ _⟩ }

theorem link_shV_pm : Spec.link_shV_pm := by
  intro K N A B l D xp₀ VA W0' s0 k tieB qB g hBad hb hrun ht hs0 hcl hn hH
  exact
    { base :=
        { isLocal := g.base.isLocal
          acc := accV_shared _ _ _ _ l.R _ _ VA.W0 W0' l.H s0 A.rels.rel B.rels.rel VA.rel
            (JV.rel (⟨W0', tieB, qB⟩ : JV N B)) g.base.acc (mm_noHid g.mm) (fun _ _ _ h => h.1) hrun
            (fun x y w c ρ h _ hRo => ⟨hRo, ht x y w c ρ h⟩)
          bears := fun J ρ Us hU => ⟨fun _ => hb _ _, hn J ρ Us hU⟩
          her := hH }
      mm := mmV_shared _ _ _ _ l.R _ _ VA.W0 W0' l.H s0 (D.tagPub xp₀) k N
        (mm_tagPub _ _ _ _ _ _ _ _ D xp₀ g.mm) hBad
        (fun w0 c ρ xp hc => by
          rw [hs0]
          show D.msg (k w0).1 (k w0).2 ρ = D.msg (k w0).1 xp ρ
          rw [hc.2])
        (fun xp xp' κ h h' => h.2.symm.trans h'.2)
      claim := fun x y w h => hcl x y w h
      free := funext fun _ =>
        funext fun _ => funext fun _ => propext ⟨fun _ => trivial, fun _ _ => hb _ _⟩ }

end Iop

namespace Cb
open Iop Prob Hiop Cb.Ood IOR

section
variable (E Kc : Type) [Field E] [Fintype E]

theorem ldSplV_lo_kb : Spec.ldSplV_lo_kb E Kc := fun D N kA kB F hD hF =>
  link_lo_kb Kc _ _ D.link N kA kB F (ldSeg_split E Kc D hD).base.know (fun _ => trivial) hF

theorem ldSplV_sh_kb : Spec.ldSplV_sh_kb E Kc := fun D N kA kB F hD hF =>
  link_sh_kb Kc _ _ D.link N kA kB F (ldSeg_split E Kc D hD).base.know (fun _ => trivial) rfl hF

theorem ldSplV_need : Spec.ldSplV_need E Kc := by
  intro D N An q J ρ Us h
  have e : (fun j : J => D.link.R.need (ρ.slot j.1) (Us j)) = Us :=
    funext fun j => ldSay_need _ _ _ (ρ.slot j.1) (Us j)
  rw [e]
  exact h

theorem ldSplV_lo_pm : Spec.ldSplV_lo_pm E Kc := fun D N VA tieB hD ht hH =>
  link_loV_pm Kc N _ _ D.link D.mask VA tieB VA.q (ldSeg_split E Kc D hD) rfl (fun _ _ => trivial)
    (fun x y w _ _ h => ht x y w h) (ldSplV_need E Kc D N _ VA.q) hH

theorem ldSplV_sh_pm : Spec.ldSplV_sh_pm E Kc := by
  intro D N VA rd xp₀ tieB hD hrd ht hH
  have g := ldSeg_split E Kc D hD
  have hv : ∀ x y w, VA.rel x y w →
      splitVal D.k D.sl₁ (D.S.msgs w.2.1) x.1.1.2.1 =
        splitVal D.k D.sl₁ (rd w.1).1 (rd w.1).2.2.1 := by
    intro x y w h
    obtain ⟨h1, h2⟩ := hrd x y w h
    rw [h1, h2]
    exact congrArg Prod.fst (g.mm.run w.2 x () ((), ()))
  refine link_shV_pm Kc N _ _ D.link D.mask xp₀ VA VA.W0
    (ldSplS0 D fun w0 => ((rd w0).1, (rd w0).2.2.1)) rd tieB VA.q g rfl (fun _ _ => trivial) ?_
    (fun x y w _ _ h => ht x y w h) (fun _ _ _ => rfl) ?_ (ldSplV_need E Kc D N _ VA.q) hH
  · intro x y w c ρ h
    show ((((), splitVal D.k D.sl₁ (D.S.msgs w.2.1) x.1.1.2.1), ρ.1, ()) : Tr [sayRound E 0]) =
      (((), splitVal D.k D.sl₁ (rd w.1).1 (rd w.1).2.2.1), ρ.1, ())
    rw [hv x y w h]
    rfl
  · intro x y w h
    obtain ⟨h1, h2⟩ := hrd x y w h
    refine ⟨?_, h2⟩
    rw [h1]
    exact g.claim x y w.2 h.1

end
end Cb
