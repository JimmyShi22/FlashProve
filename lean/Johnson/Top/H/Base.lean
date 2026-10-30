-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/Base.lean: the kind of block BASE (the two rounds of the last step of a proximity
test) as a value of `Kind` (Johnson/Top/Kind.lean), at any written list of sizes, in its two forms,
with the kind's hypothesis and the three facts beside it.

Nothing new is proved: every line is a call of Cb/Pv/Tower/Base.lean or of the library. A size is
that file's record `BaseSize E`: data alone. The joints hang on the size alone.
Main names:
  `kBase L`: the last step whose masking word was sent earlier and stands among the input's oracles.
  `kBase₁ L`: the library's own, which sends it in its first round.
  `kBase_know`, `_point`, `_local`, `_onOut`, `_good` and the same for `kBase₁`: under the
    conditions at every size of the list (`BaseSize.OK`); `_point` and `_onOut` without.
  `HBase`, `HBase₁`: closed, over the field `Cb.Gl.E`: for every list of sizes that meet the
    conditions the kind is knowledge sound. `hBase`, `hBase₁`: they hold.
Limits: no list of sizes is written here. Values of the joint a at stages of a proximity test that
are given in numbers, the conditions at these values, and written lists of such numbers, meant as a
key file's: Johnson/Top/H/BaseValues.lean and Johnson/Top/H/KeyValues.lean, with limits of their
own. Nothing says that a block of the kind is the step that the programs run, or that its errors are
small. Nothing on an honest prover.

-/
import Johnson.Top.Kind
import Cb.Pv.Tower.Base
import Cb.Gl.GlField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop Cb IOR Cb.Pv.Tower

section
variable {E : Type} [Field E] [Fintype E]

/-- BASE whose masking word was sent earlier, at a written list of sizes. -/
@[reducible] noncomputable def kBase (L : List (BaseSize E)) : Kind.{1} where
  Size := BaseSize E
  sizes := L
  src := fun s => jOf (baseIn s.a)
  dst := fun _ => jOf trivRels
  block := fun s => ⟨baseRide s.a s.t s.cov, baseExt s.a s.t s.d, baseErr s.a s.t s.bad s.L2⟩

/-- BASE that sends its masking word, at a written list of sizes. -/
@[reducible] noncomputable def kBase₁ (L : List (BaseSize E)) : Kind.{1} where
  Size := BaseSize E
  sizes := L
  src := fun s => jOf s.a.rels
  dst := fun _ => jOf trivRels
  block := fun s =>
    ⟨ldBaseIOR s.a.C s.a.sl s.t s.cov, ldBaseExt s.a.C s.t s.d,
      ldBaseErr s.a.C s.t s.a.e s.bad s.L2⟩

variable (L : List (BaseSize E))

theorem kBase_know (h : ∀ s ∈ L, s.OK) : (kBase L).Know := fun s hs => s.h (h s hs)

theorem kBase_point : (kBase L).Point := fun s _ => base_point s.a s.t s.cov

theorem kBase_local (h : ∀ s ∈ L, s.OK) : (kBase L).Local := fun s hs =>
  base_isLocal s.a s.t s.cov (h s hs).laws

theorem kBase_onOut : (kBase L).OnOut := fun _ _ _ _ _ _ _ => trivial

theorem kBase_good (h : ∀ s ∈ L, s.OK) : ∀ s ∈ L, ((kBase L).block s).Good :=
  Kind.good (kBase_know L h) (kBase_point L) (kBase_local L h) (kBase_onOut L)

theorem kBase₁_know (h : ∀ s ∈ L, s.OK) : (kBase₁ L).Know := fun s hs => s.h₁ (h s hs)

theorem kBase₁_point : (kBase₁ L).Point := fun s _ => ⟨ldBasePoint s.a.C s.t⟩

theorem kBase₁_local (h : ∀ s ∈ L, s.OK) : (kBase₁ L).Local := fun s hs =>
  ldBase_isLocal (h s hs).laws

theorem kBase₁_onOut : (kBase₁ L).OnOut := fun _ _ _ _ _ _ _ => trivial

theorem kBase₁_good (h : ∀ s ∈ L, s.OK) : ∀ s ∈ L, ((kBase₁ L).block s).Good :=
  Kind.good (kBase₁_know L h) (kBase₁_point L) (kBase₁_local L h) (kBase₁_onOut L)

end

/-- The hypothesis of the kind, closed: knowledge soundness alone, for every list of sizes that meet
the conditions. -/
def HBase : Prop := ∀ L : List (BaseSize Cb.Gl.E), (∀ s ∈ L, s.OK) → (kBase L).Know

theorem hBase : HBase := kBase_know

/-- The same for the last step that sends its masking word. -/
def HBase₁ : Prop := ∀ L : List (BaseSize Cb.Gl.E), (∀ s ∈ L, s.OK) → (kBase₁ L).Know

theorem hBase₁ : HBase₁ := kBase₁_know

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.hBase
#print axioms VerifiableInference.OnPublicFiles.hBase₁
#print axioms VerifiableInference.OnPublicFiles.kBase_good
#print axioms VerifiableInference.OnPublicFiles.kBase₁_good
