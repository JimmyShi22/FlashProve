-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Switch/BatFoldTotal.lean: the verifier of the block "batching round, arrangement, cut, fold"
of Cb/Pv/Tower/First.lean never rejects, if the coefficient that the fold's short rounds leave out
can be completed.

The block is made of reductions in a row and beside carried parts. Its batching round never rejects
(`Bat.never_rejects`, Cb/Pv/Bat.lean); the arrangement, the cut and the setting of the rider are
steps without rounds that never reject; the fold with short rounds never rejects under a premise on
which power is left out (`Tower.foldRide_total`, Cb/Pv/Tower/Fold.lean). This file has the rules by
which "never rejects" passes through the ways of composing, and the block's own statement.
Statements and proofs.

Main names:
  `Total R`: the verifier of R puts out a statement at every statement, oracles and transcript.
  `Total.seq`, `Total.keepE`, `Total.keepX`, `Total.keep`, `total_pure`: the rules.
  `gfRide_total`, `batFoldRide_total`: arrangement, cut, fold; the whole block.
Limits: nothing on what is put out. Nothing on soundness.

-/
import Cb.Pv.Tower.First

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.BatFold
open Iop Prob Hiop IOR Cb

/-- The verifier never rejects. -/
def Total {Xi Xo : Type} {Ei Eo : ExtSpec} (R : IOR Xi Ei Xo Eo) : Prop :=
  ∀ x y τ, (R.out x y τ).isSome

theorem Total.seq {X₁ X₂ X₃ : Type} {E₁ E₂ E₃ : ExtSpec} {R₁ : IOR X₁ E₁ X₂ E₂}
    {R₂ : IOR X₂ E₂ X₃ E₃} (h₁ : Total R₁) (h₂ : Total R₂) : Total (R₁.seq R₂) := fun x y τ => by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 (h₁ x y (Tr.fst τ))
  show ((R₁.out x y (Tr.fst τ)).bind fun x₂ =>
    R₂.out x₂ (R₁.imp y (Tr.fst τ)) (Tr.snd (s := R₁.shape) τ)).isSome
  rw [ha]
  exact h₂ _ _ _

theorem Total.keepE {Xi Xo : Type} {Ei Eo : ExtSpec} {R : IOR Xi Ei Xo Eo} (h : Total R)
    (F : ExtSpec) : Total (R.keepE F) := fun x y τ => h x y.1 τ

theorem Total.keepX {Xi Xo : Type} {Ei Eo : ExtSpec} {R : IOR Xi Ei Xo Eo} (h : Total R)
    (Z : Type) : Total (R.keepX Z) := fun x y τ => by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 (h x.1 y τ)
  show ((R.out x.1 y τ).map fun x' => (x', x.2)).isSome
  rw [ha]
  rfl

theorem Total.keep {Xi Xo : Type} {Ei Eo : ExtSpec} {R : IOR Xi Ei Xo Eo} (h : Total R)
    (Z : Type) (F : ExtSpec) : Total (R.keep Z F) := (h.keepX Z).keepE F

theorem total_pure {X X' : Type} {E E' : ExtSpec} (f : X → X') (g : ExtMap E E') :
    Total (IOR.pure (fun x => some (f x)) g) := fun _ _ _ => rfl

section
variable {E B : Type} [Field E] [Fintype E] [Fintype B] {S : Sig E} {G : Grp S} [Nonempty G.P]
  (Sh : GShape G) (Sb : B → Type) (sl : ∀ b, Slf E (Sb b) G.C.J) (Z : Evader E (G.Row B))
  (fx : Fin ((Sh.fold Sb sl Z).n + 1) × E)

/-- Arrangement, cut, fold. -/
theorem gfRide_total (h : fx.2 * (HVar.plain E (Sh.fold Sb sl Z).n).mon fx.1 = 1) :
    Total (Tower.gfRide Sh Sb sl Z fx) := by
  unfold Tower.gfRide
  refine Total.seq ?_ (Total.seq ?_ (Tower.foldRide_total (Sh.fold Sb sl Z) fx h))
  · unfold Tower.arrRide Tower.arrOwn
    exact Total.keepE (total_pure (fun x => x) _) _
  · unfold Tower.cutRide Tower.cutOwn
    exact Total.keepE (total_pure (fun x => (x.1, (x.2, x.2))) _) _

end

section
variable {E : Type} [Field E] [Fintype E] (s : Cb.Pv.Bat.Size E) [Nonempty s.G.P] (Sh : GShape s.G)
  (fx : Fin ((Sh.fold s.Sb s.sl s.Z).n + 1) × E) (St₀ : Type) (E₀ : ExtSpec)

/-- THE WHOLE BLOCK never rejects. -/
theorem batFoldRide_total (h : fx.2 * (HVar.plain E (Sh.fold s.Sb s.sl s.Z).n).mon fx.1 = 1) :
    Total (Tower.batFoldRide s Sh fx St₀ E₀) := by
  unfold Tower.batFoldRide
  exact Total.seq (Total.keepE (Cb.Pv.Bat.never_rejects s St₀ E₀) _)
    (Total.seq (total_pure (fun x => x) _) (Total.keep (gfRide_total Sh s.Sb s.sl s.Z fx h) _ _))

end

end Cb.Pv.BatFold

#print axioms Cb.Pv.BatFold.batFoldRide_total
