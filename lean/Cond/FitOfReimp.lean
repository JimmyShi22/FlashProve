-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cond/FitOfReimp.lean: the compiler's data and side conditions of one sub-protocol (`IOR.SubData`,
`IOR.SubFit`: Cond/FitOfSub.lean), through two more generic constructions.

Definitions and proofs. Generic: no protocol occurs.
This is book-keeping for the compiler, as in Cond/FitOfFrame.lean. "The implicit instance" is the
implicit part of a statement of an IOR.

Main names:
  1. "The same rounds, another new implicit instance" (`IOR.reimp`, Ior/FrameView.lean). `R.reimp`
     has the rounds, the verifier's positions and the honest messages of R; the new implicit
     instance and the sources of its symbols are others, the new explicit statement is f of R's, and
     the honest side's new witness is g of the first witness and of R's new statement and witness.
    `opensLe_reimp`, `subFit_reimp`: the rule: `OpensLe` (Cond/FitOfOpens.lean) at the numbers of
      `SubData.reimp` and `SubFit` pass from R to `R.reimp` if each symbol of the new implicit
      instance has at most bl sources, of which at most bE in the old implicit instance.
  2. "The verifier draws a value" (`IOR.draw`, Ior/Draw.lean).
    `SubData.draw`, `opensLe_draw`, `subFit_draw`, `tot_draw`: one round without a prover message; a
      sampler dD of the value is an argument, of which `subFit_draw` asks `dD.Good (κ₀ ^ dD.b)`;
      openings (0, 0, 1, 1).

Notation: `OpenB` (Cond/FitOfOpens.lean) has four numbers: `n`: own positions, in the prover's
oracles and the implicit instance together; `nE`: own positions in the implicit instance; `bl`:
positions for one query to the new implicit instance; `bE`: of these, in the implicit instance.

Terms: lean/GLOSSARY.md.
-/
import Cond.FitOfFrame
import Ior.FrameView
import Ior.Draw

set_option autoImplicit false

/-! ## 1. The same rounds, another new implicit instance -/

namespace Iop.IOR
open Prob
open scoped ENNReal

variable {Xi Xo Xo' : Type}
  {Ei Eo Eo' : ExtSpec} {Wi Wo Wo' : Type} {lam : ℕ} {R : IOR Xi Ei Xo Eo} {H : R.Honest Wi Wo}

/-- The data of `R.reimp`. bl, bE: the cost of a later query to the new implicit instance. -/
def SubData.reimp (D : R.SubData H lam) (f : Xo → Xo') (imp' : Ei.Str → Tr R.shape → Eo'.Str)
    (srcE' : Rho R.shape → Eo'.Pos → Finset Ei.Pos)
    (srcO' : Rho R.shape → Eo'.Pos → Finset (OPos R.shape)) (g : Wi → Xo → Wo → Wo') (bl bE : ℕ) :
    (R.reimp f imp' srcE' srcO').SubData (H.reimp f imp' srcE' srcO' g) lam :=
  ⟨D.pt, D.pos, D.dr, D.coin, D.decBad, D.decHid, ⟨D.ob.n, D.ob.nE, bl, bE⟩⟩

open Classical in
/-- The rule on numbers of openings: under `h`, `h3`, `h4`: the first two numbers of R stay, the
last two are bl, bE. -/
theorem opensLe_reimp {o : OpenB} (h : R.OpensLe o) (f : Xo → Xo')
    (imp' : Ei.Str → Tr R.shape → Eo'.Str) {srcE' : Rho R.shape → Eo'.Pos → Finset Ei.Pos}
    {srcO' : Rho R.shape → Eo'.Pos → Finset (OPos R.shape)} {bl bE : ℕ}
    (h3 : ∀ ρ q, (srcO' ρ q).card + (srcE' ρ q).card ≤ bl) (h4 : ∀ ρ q, (srcE' ρ q).card ≤ bE) :
    (R.reimp f imp' srcE' srcO').OpensLe ⟨o.n, o.nE, bl, bE⟩ := by
  refine opensLe_of_bounds _ _ _ _ (R.reimp f imp' srcE' srcO') ⟨o.n, o.nE, bl, bE⟩
    (fun ρ => ?_) (fun ρ => ?_) h3 h4
  · have := h.tot ρ ∅
    simpa using this
  · have := h.ext ρ ∅
    simpa using this

/-- `SubFit` passes from D to `D.reimp`, under `h`, `h3`, `h4`. -/
theorem subFit_reimp {D : R.SubData H lam} {κ₀ : ℝ≥0∞} (h : SubFit D κ₀) (f : Xo → Xo')
    (imp' : Ei.Str → Tr R.shape → Eo'.Str) {srcE' : Rho R.shape → Eo'.Pos → Finset Ei.Pos}
    {srcO' : Rho R.shape → Eo'.Pos → Finset (OPos R.shape)} (g : Wi → Xo → Wo → Wo') {bl bE : ℕ}
    (h3 : ∀ ρ q, (srcO' ρ q).card + (srcE' ρ q).card ≤ bl) (h4 : ∀ ρ q, (srcE' ρ q).card ≤ bE) :
    SubFit (D.reimp f imp' srcE' srcO' g bl bE) κ₀ :=
  ⟨h.good, opensLe_reimp h.opens f imp' h3 h4⟩

theorem tot_reimp (D : R.SubData H lam) (f : Xo → Xo') (imp' : Ei.Str → Tr R.shape → Eo'.Str)
    (srcE' : Rho R.shape → Eo'.Pos → Finset Ei.Pos)
    (srcO' : Rho R.shape → Eo'.Pos → Finset (OPos R.shape)) (g : Wi → Xo → Wo → Wo') (bl bE : ℕ) :
    (D.reimp f imp' srcE' srcO' g bl bE).tot = D.tot ∧
    (D.reimp f imp' srcE' srcO' g bl bE).maxB = D.maxB := ⟨rfl, rfl⟩

end Iop.IOR

/-! ## 2. The verifier draws a value -/

namespace Iop.IOR
open Prob
open scoped ENNReal

variable {X X' : Type} {lam : ℕ}

/-- The data of `IOR.draw`; dD is a sampler of the value. -/
def SubData.draw (D : Type) [Fintype D] [Nonempty D] (nx : X → D → X') (E : ExtSpec)
    (W : Type) (dD : BS lam D) :
    (IOR.draw D nx E).SubData (Honest.draw D nx E W) lam where
  pt := (Blocks.plainPoint Unit D (), ())
  pos := (Num.ofFinEnum Empty, ())
  dr := (dD, ())
  coin := Num.ofFinEnum Unit
  decBad := fun _ => isFalse fun h => h
  decHid := fun _ _ _ => isFalse fun h => h
  ob := ⟨0, 0, 1, 1⟩

theorem opensLe_draw (D : Type) [Fintype D] [Nonempty D] (nx : X → D → X') (E : ExtSpec) :
    (IOR.draw D nx E).OpensLe ⟨0, 0, 1, 1⟩ :=
  opensLe_of_bounds _ _ _ _ (IOR.draw D nx E) ⟨0, 0, 1, 1⟩ (fun _ => Nat.le_refl 0)
    (fun _ => Nat.le_refl 0) (fun _ _ => Nat.le_of_eq rfl) (fun _ _ => Nat.le_of_eq rfl)

theorem subFit_draw (D : Type) [Fintype D] [Nonempty D] (nx : X → D → X') (E : ExtSpec) (W : Type)
    (dD : BS lam D) {κ₀ : ℝ≥0∞} (h : dD.Good (κ₀ ^ dD.b)) :
    SubFit (SubData.draw D nx E W dD) κ₀ :=
  ⟨⟨h, trivial⟩, opensLe_draw D nx E⟩

theorem tot_draw (D : Type) [Fintype D] [Nonempty D] (nx : X → D → X') (E : ExtSpec)
    (W : Type) (dD : BS lam D) :
    (SubData.draw D nx E W dD).tot = dD.b ∧ (SubData.draw D nx E W dD).maxB = dD.b :=
  ⟨Nat.add_zero _, Nat.max_zero _⟩

end Iop.IOR
