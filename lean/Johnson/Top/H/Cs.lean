-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/Cs.lean: the kind of block CS (the two rounds of a code switch) as a value of `Kind`
(Johnson/Top/Kind.lean), at any written list of sizes, in its two forms, with the kind's hypothesis
and the three facts beside it.

Nothing new is proved: every line is a call of Cb/Pv/Tower/Cs.lean or of the library. A size is
that file's record `CsSize E`: data alone. The joints hang on the size alone.
Main names:
  `kCs L`: the code switch whose first message bears a rider. `kCs₁ L`: the library's own.
  `kCs_know`, `_point`, `_local`, `_onOut`, `_good` and the same for `kCs₁`: `_know` under the
    conditions at every size of the list (`CsSize.OK`); `_local` if the new code's
    transformation reads what it declares (`CsSize.OKLocal`); `_good` under both.
  `HCs`, `HCs₁`: closed, over the field `Cb.Gl.E`: for every list of sizes that meet the conditions
    the kind is knowledge sound. `hCs`, `hCs₁`: they hold.
Limits: no list of sizes is written here. Values of D at stages of a proximity test that are given
in numbers, the conditions at these values, and written lists of such numbers, meant as a key
file's: Johnson/Top/H/CsValues.lean and Johnson/Top/H/KeyValues.lean, with limits of their own.
Nothing says that a block of the kind is the step that the programs run, or that its errors are
small. Nothing on an honest prover.

-/
import Johnson.Top.Kind
import Cb.Pv.Tower.Cs
import Cb.Gl.GlField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop Cb IOR Cb.Pv.Tower

section
variable {E : Type} [Field E] [Fintype E]

/-- CS that bears a rider, at a written list of sizes. -/
@[reducible] noncomputable def kCs (L : List (CsSize E)) : Kind.{1} where
  Size := CsSize E
  sizes := L
  src := fun s => jOf (s.D.jIn s.e).rels
  dst := fun s => jOf (csOut s.D s.Cw s.e')
  block := fun s =>
    ⟨csRide s.D s.Cw s.Pt s.lf s.lfW, fun _ _ w' => s.D.back w',
      csErr s.D s.Cw s.Pt s.lf s.lfW s.e s.L⟩

/-- CS without a rider, at a written list of sizes. -/
@[reducible] noncomputable def kCs₁ (L : List (CsSize E)) : Kind.{1} where
  Size := CsSize E
  sizes := L
  src := fun s => jOf (s.D.jIn s.e).rels
  dst := fun s => jOf (s.D.jOut s.e').rels
  block := fun s =>
    ⟨ldSwitch s.D, fun _ _ w' => s.D.back w', (s.D.W.err1 s.L, (s.D.W.err2 s.e s.L, ()))⟩

variable (L : List (CsSize E))

theorem kCs_know (h : ∀ s ∈ L, s.OK) : (kCs L).Know := fun s hs => s.h (h s hs)

theorem kCs_point : (kCs L).Point := fun s _ => cs_point s.D s.Cw s.Pt s.lf s.lfW

theorem kCs_local (h : ∀ s ∈ L, s.OKLocal) : (kCs L).Local := fun s hs =>
  cs_isLocal s.D s.Cw s.Pt s.lf s.lfW (h s hs)

theorem kCs_onOut : (kCs L).OnOut := fun _ _ _ _ _ _ _ => trivial

theorem kCs_good (h : ∀ s ∈ L, s.OK) (hR : ∀ s ∈ L, s.OKLocal) :
    ∀ s ∈ L, ((kCs L).block s).Good :=
  Kind.good (kCs_know L h) (kCs_point L) (kCs_local L hR) (kCs_onOut L)

theorem kCs₁_know (h : ∀ s ∈ L, s.OK) : (kCs₁ L).Know := fun s hs => s.h₁ (h s hs)

theorem kCs₁_point : (kCs₁ L).Point := fun s _ => ⟨s.D.pt⟩

theorem kCs₁_local (h : ∀ s ∈ L, s.OKLocal) : (kCs₁ L).Local := fun s hs =>
  ldSwitch_isLocal s.D (h s hs)

theorem kCs₁_onOut : (kCs₁ L).OnOut := fun _ _ _ _ _ _ _ => trivial

theorem kCs₁_good (h : ∀ s ∈ L, s.OK) (hR : ∀ s ∈ L, s.OKLocal) :
    ∀ s ∈ L, ((kCs₁ L).block s).Good :=
  Kind.good (kCs₁_know L h) (kCs₁_point L) (kCs₁_local L hR) (kCs₁_onOut L)

end

/-- The hypothesis of the kind, closed: knowledge soundness alone, for every list of sizes that meet
the conditions. -/
def HCs : Prop := ∀ L : List (CsSize Cb.Gl.E), (∀ s ∈ L, s.OK) → (kCs L).Know

theorem hCs : HCs := kCs_know

/-- The same for the code switch without a rider. -/
def HCs₁ : Prop := ∀ L : List (CsSize Cb.Gl.E), (∀ s ∈ L, s.OK) → (kCs₁ L).Know

theorem hCs₁ : HCs₁ := kCs₁_know

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.hCs
#print axioms VerifiableInference.OnPublicFiles.hCs₁
#print axioms VerifiableInference.OnPublicFiles.kCs_good
#print axioms VerifiableInference.OnPublicFiles.kCs₁_good
