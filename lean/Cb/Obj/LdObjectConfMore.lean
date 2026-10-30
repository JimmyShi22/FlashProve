-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectConfMore.lean: the conditions on the code that encodes the index (distance, sizes of
lists), each stated once, with the forms in which the sub-protocols use them derived from it; and
the fold's agreement count at a radius e', for 3 e' below the distance or, with ok e', under
`Enc.Prox`.

Definitions, statements (in `Cb.Spec`) and proofs, over the configuration of
Cb/Obj/LdObjectConf.lean.
The sub-protocols over `Cf.conf` require of the index code, each in its own terms: a distance of the
generator over F and of the generator over E; lists at the radius of decoding for tables over F (the
record binds) and at the radius of a test for tables over E (the fold); an agreement count.
`LdIx.MCAeq e' bad` (Cb/Ld/LdFoldEq.lean) says that, for every table, bad bounds the number of fold
points γ at which mutual correlated agreement at the radius e' fails for the coefficients eq(γ, ·).

Main names:
  `Cf.ListOK L`: the one condition on lists: every table over E has at most L tables of full
    messages within eM columns.
  `Cf.CodeOK L`: the code's conditions: `Enc.Core`, eM below the distance, `Cf.ListOK L`, the sample
    map evades zeros on vectors whose pad part is in F.
  `Spec.ldCm_ok`: `CodeOK L` and `ModelOK` give `Cf.OK L`.
  `Spec.ldCm_dist`: the distance over E from the distance over F.
  `Spec.ldCm_list_le`: `ListOK L` gives the list bound L at every radius e' ≤ eM, for all tables
    over E. `Spec.ldCm_list_F`: and the clause of `Cf.OK`, for tables over F.
  `ListOK L` itself: `Spec.ldCm_list_johnson` (eM below the Johnson radius: L = listMax n d eM);
    `Spec.ldCm_list_unique` (2 eM below the distance: L = 1); `Spec.ldCm_list_at` (from
    `Enc.ListAt`).
  `Spec.ldCm_mca_third`: the agreement count of the fold with nothing assumed beyond the hypotheses
    of its statement, for 3 e' below the distance. `Spec.ldCm_mca_prox`: from `Enc.Prox`, at a
    radius e' with ok e'.

Limits: this file does not say that there is a proximity gap beyond a third of the distance. It says
nothing on numerals. `Spec.ldCm_mca_prox` takes such a gap as a hypothesis (`Enc.Prox`).

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectConfProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood

namespace LdCf
variable {F E : Type} [Field F] [Field E] [Algebra F E] (Cf : LdCf F E)

/-- The one condition on lists. -/
def ListOK (L : ℕ) : Prop := ∀ f : Cf.Row → Fin Cf.C₀.n → E, ListLE (DecodesTo Cf.X.G Cf.eM f) L

/-- The code's conditions. -/
structure CodeOK [Fintype F] (L : ℕ) : Prop where
  core   : Cf.C₀.Core
  rad    : Cf.eM < Cf.C₀.d
  list   : Cf.ListOK L
  evades : Cf.Z.OKOn (PadInF F)

/-- The model's conditions. -/
structure ModelOK : Prop where
  sub    : ∀ i x w, Cf.Ryes i x w → Cf.Rno i x w
  admits : ∀ i x w, Cf.Ryes i x w → Cf.Ryes i x (Cf.trace i x)
  held   : ∀ i, Cf.heldB (Cf.body i) = some i
  reads  : ∀ a a' : Cf.Row × Cf.J₀ → F,
    (∀ r l, a (r, Cf.lay l) = a' (r, Cf.lay l)) → Cf.heldB a = Cf.heldB a'

end LdCf

namespace Spec
section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

def ldCm_ok : Prop := ∀ (Cf : LdCf F E) (L : ℕ), Cf.CodeOK L → Cf.ModelOK → Cf.OK L

def ldCm_dist : Prop := ∀ (Cf : LdCf F E), HasDist Cf.C₀.G Cf.C₀.d → HasDist Cf.X.G Cf.C₀.d

def ldCm_list_le : Prop :=
  ∀ (Cf : LdCf F E) (L e' : ℕ),
    Cf.ListOK L → e' ≤ Cf.eM → ∀ f : Cf.X.Row → Fin Cf.C₀.n → E, ListLE (DecodesTo Cf.X.G e' f) L

def ldCm_list_F : Prop :=
  ∀ (Cf : LdCf F E) (L : ℕ), Cf.ListOK L →
    ∀ f₀ : Cf.Row → Fin Cf.C₀.n → F,
      ListLE (DecodesTo (Cf.C₀.GE E) Cf.eM fun a => Code.liftWord E (f₀ a)) L

def ldCm_list_johnson : Prop :=
  ∀ (Cf : LdCf F E), HasDist Cf.C₀.G Cf.C₀.d → InJohnson Cf.C₀.n Cf.C₀.d Cf.eM →
    Cf.ListOK (listMax Cf.C₀.n Cf.C₀.d Cf.eM)

def ldCm_list_unique : Prop :=
  ∀ (Cf : LdCf F E), HasDist Cf.C₀.G Cf.C₀.d → 2 * Cf.eM < Cf.C₀.d → Cf.ListOK 1

def ldCm_list_at : Prop := ∀ (Cf : LdCf F E) (L : ℕ), Cf.C₀.ListAt E Cf.Row Cf.eM L → Cf.ListOK L

def ldCm_mca_third : Prop :=
  ∀ (Cf : LdCf F E) (e' : ℕ), HasDist Cf.C₀.G Cf.C₀.d → 3 * e' < Cf.C₀.d →
    Cf.X.MCAeq e' (Cf.v * (e' + 1) * Fintype.card E ^ (Cf.v - 1))

def ldCm_mca_prox : Prop :=
  ∀ (Cf : LdCf F E) (ok : ℕ → Prop) (L bad : ℕ → ℕ → ℕ) (e' : ℕ), Cf.C₀.Prox E ok L bad → ok e' →
    Cf.X.MCAeq e' ((∑ j ∈ Finset.range Cf.v, bad e' (2 ^ j)) * Fintype.card E ^ (Cf.v - 1))

end
end Spec

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

omit [Fintype F] [Fintype E] in
theorem ldCm_list_F : Spec.ldCm_list_F F E := fun _ _ h f₀ => h fun a => Code.liftWord E (f₀ a)

omit [Fintype E] in
theorem ldCm_ok : Spec.ldCm_ok F E := fun Cf L h m =>
  ⟨h.core, h.rad, ldCm_list_F F E Cf L h.list, h.evades, m.sub, m.admits, m.held, m.reads⟩

omit [Fintype F] [Fintype E] in
theorem ldCm_dist : Spec.ldCm_dist F E := fun _ hd => HasDist.map (E := E) hd

omit [Fintype F] [Fintype E] in
theorem ldCm_list_le : Spec.ldCm_list_le F E := fun _ L _ h he f =>
  ood_list_mono _ _ _ L (fun _ hM => hM.mono he) (h f)

omit [Fintype F] [Fintype E] in
theorem ldCm_list_johnson : Spec.ldCm_list_johnson F E := fun Cf hd hJ f =>
  ldFc_list_johnson F E Cf.C₀ Cf.eM hd hJ _ f

omit [Fintype F] [Fintype E] in
theorem ldCm_list_unique : Spec.ldCm_list_unique F E := fun Cf hd h2 f =>
  ldFc_list_unique F E Cf.C₀ Cf.eM hd h2 _ f

omit [Fintype F] in
theorem ldCm_list_at : Spec.ldCm_list_at F E := fun _ _ h f => ood_list_of_cnt _ _ _ (h f)

omit [Fintype F] in
theorem ldCm_mca_third : Spec.ldCm_mca_third F E := fun Cf e' hd h3 =>
  ldFc_mca_third F E Cf.C₀ Cf.hp Cf.J Cf.plE Cf.v Cf.Z Cf.eM Cf.rank e' hd h3

omit [Fintype F] in
theorem ldCm_mca_prox : Spec.ldCm_mca_prox F E := fun Cf ok L bad e' hP hok =>
  ldFc_mca_prox F E Cf.C₀ Cf.hp Cf.J Cf.plE Cf.v Cf.Z Cf.eM Cf.rank ok L bad e' hP hok

end
end Cb
