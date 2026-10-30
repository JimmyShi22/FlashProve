-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdGroupSegProofs.lean: the proofs of the statements of Cb/Ld/LdGroupSeg.lean. Nothing is
assumed beyond what a statement names.

Main names (statements and hypotheses: Cb/Ld/LdGroupSeg.lean):
  `ldGroup_seg`: under the hypotheses of `Spec.ldGroup_seg`, the link `Hd.link ..` meets all four
    hypotheses (`(Hd.foldD ..).Hyp`: good, word, wit, laws) of the move "first half of the closing
    of a group" (`LdFoldD`, Cb/Req1/LdSegKit.lean).
  `ldGroup_seg_word`, `ldGroup_seg_wit`, `ldGroup_seg_laws`: the second, third and fourth of these:
    see the doc comments of their statements.

Limits: what the head of Cb/Ld/LdGroupSeg.lean lists as not said is not said here either.
-/
import Cb.Ld.LdGroupSeg

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.Ood

theorem ldGroup_seg_word : Spec.ldGroup_seg_word := by
  intro E B Kc St₀ Wp _ _ _ S G _ Sh kp _ Hd Sb sl Z E₀ A₀ hc dw d t Lst mC mS mW L hL a τ b hout k
  obtain ⟨xo, -, rfl⟩ := Option.map_eq_some_iff.1 hout
  have hk := ldGroup_out_kept E B St₀ S G Sh kp Sb sl Z E₀ d t Lst mC mS mW a.2 τ
  obtain ⟨γ, -, h2⟩ := ldGroup_out_word E B St₀ S G Sh kp Sb sl Z E₀ d t Lst mC mS mW a.2 τ
  have e1 : (fun (p : Sh.Cb.NP) (s : Sh.Rm (Hd.at' k) × Sh.Cb.NS p) =>
        LdCode.fstW (C₁ := Sh.Cs) (C₂ := Sh.Zb.pair Sh.par.Zw)
          ((ldRunG G kp Sb sl Z St₀ E₀ (Sh.block Sb sl Z d t Lst mC mS mW)).imp a.2 τ).1
          p (some (Hd.slot k s.1), s.2)) =
      fun p s =>
        LdCode.fstW (C₁ := Sh.Cb.il (Σ a, Sh.Rm a)) (C₂ := Sh.Zb.il (Σ a, Sh.Rz a))
            (Sh.flat.wd (G.word a.2.2)) p (⟨Hd.at' k, s.1⟩, s.2) := by
    funext p s
    rw [hk, hL.kept]
  show Hd.unW k (fun p s =>
      LdCode.fstW (C₁ := Sh.Cs) (C₂ := Sh.Zb.pair Sh.par.Zw)
        ((ldRunG G kp Sb sl Z St₀ E₀ (Sh.block Sb sl Z d t Lst mC mS mW)).imp a.2 τ).1
        p (some (Hd.slot k s.1), s.2)) =
    (S.om k.1.1).upW
      (((ldRunG G kp Sb sl Z St₀ E₀ (Sh.block Sb sl Z d t Lst mC mS mW)).imp a.2 τ).2.2 k.1)
  rw [e1, hL.word, h2]
  rfl

theorem ldGroup_seg_wit : Spec.ldGroup_seg_wit := by
  intro E B Kc St₀ Wp _ _ _ S G _ Sh kp _ Hd Sb sl Z E₀ A₀ hc dw d t Lst mC mS mW L hL w x c ρ k
  obtain ⟨γ, -, -, h3⟩ := ldGroup_out_wit E B St₀ Wp S G Sh kp Sb sl Z E₀ d t Lst mC mS mW w x c ρ
  have hk := fun j =>
    ldGroup_out_wit_kept E B St₀ Wp S G Sh kp Sb sl Z E₀ d t Lst mC mS mW w x c ρ j
  have hr : (((ldRunGH G kp Sb sl Z St₀ Wp E₀ (Sh.block Sb sl Z d t Lst mC mS mW)).strat w x c).run
        ρ).2.2.2.1 k.1 = w.1 k.1.1 := by
    rw [h3]
    rfl
  refine Eq.trans (Prod.ext (funext fun j => ?_) (funext fun q => ?_)) hr.symm
  · show (((ldRunGH G kp Sb sl Z St₀ Wp E₀ (Sh.block Sb sl Z d t Lst mC mS mW)).strat
          w x c).run ρ).2.2.1.1
        (.inl (some (Hd.slot k (Hd.cJ k j).1), (Hd.cJ k j).2)) = (w.1 k.1.1).1 j
    rw [(hk _).1, hL.kept, hL.upJ]
    rfl
  · show (((ldRunGH G kp Sb sl Z St₀ Wp E₀ (Sh.block Sb sl Z d t Lst mC mS mW)).strat
          w x c).run ρ).2.2.1.2
        (.inl (some (Hd.slot k (Hd.cQ k q).1), (Hd.cQ k q).2)) = (w.1 k.1.1).2 q
    rw [(hk _).2, hL.kept, hL.upQ]
    rfl

theorem ldGroup_seg_laws : Spec.ldGroup_seg_laws := by
  intro E B Kc St₀ Wp _ _ _ S G _ Sh kp _ Hd Sb sl Z E₀ A₀ hL hF
  refine ⟨fun k m r => ?_, fun k f g hn => ?_⟩
  · exact hL.enc k (fun n => m (.inl (some (Hd.slot k n.1), n.2)))
      (fun n => r (.inl (some (Hd.slot k n.1), n.2)))
  · have hn' : cnt (fun x : G.P => Sh.Cf.T f x ≠ Sh.Cf.T g x) ≤ G.e := hn
    refine hF (Hd.at' k) _ _
      (le_trans (cnt_mono fun x hx (hc : Sh.Cf.T f x = Sh.Cf.T g x) => hx ?_) hn')
    refine hL.loc k _ _ x (funext fun α => ?_)
    exact congrFun hc (.inl (some (Hd.slot k α.1), α.2))

open Classical in
theorem ldGroup_seg : Spec.ldGroup_seg := by
  intro E B Kc St₀ Wp _ _ _ S G _ Sh kp _ Hd Sb sl Z E₀ A₀ hc dw d t Lst mC
    mS mW L hS hL hY hZ hLi hF
  exact ⟨(ldGroup_fold E B Kc St₀ Wp S G Sh kp Sb sl Z L E₀ A₀ hc dw d t Lst mC mS mW
      (fun _ => True) (fun _ => True) hS hY hZ hLi hF fun _ _ => trivial).1.good,
    ldGroup_seg_word E B Kc St₀ Wp S G Sh kp Hd Sb sl Z E₀ A₀ hc dw d t Lst mC mS mW L hL,
    ldGroup_seg_wit E B Kc St₀ Wp S G Sh kp Hd Sb sl Z E₀ A₀ hc dw d t Lst mC mS mW L hL,
    ldGroup_seg_laws E B Kc St₀ Wp S G Sh kp Hd Sb sl Z E₀ A₀ hL hF⟩

end Cb
