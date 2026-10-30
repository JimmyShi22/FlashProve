-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoShapeZ.lean: at the record of every smallness test in what
Verify.publicOf returns, the lookup's record of public numbers is made of the test's own two calls,
numbers of padding keys and cap; so the one test on these numbers says yes there.

Fo.ShapeOf calls pub lid h (OnBytes/Tie/Pv/Lookup/Port/FoHeard.lean): Forest.shape calls lid
returns some h0, Forest.pubAsk h0 pub returns, and h is h0 with pub. Fo.ZPlan.piecesF_cut
(OnBytes/Tie/Pv/Lookup/Ends/FoZRec.lean) has these three clauses at the record that HTailF2.piecesF
returns. Fo.ZPlan.FromPieces (OnBytes/Tie/Pv/Lookup/Ends/FoZPlaced1.lean) says of the record in a
plan that it is such a record up to fields that the clauses do not read.

 - ShapeZ tl: ShapeOf at the two calls of tl, tl.f9.pub, tl.lidb and tl.f9.
 - piecesF_shapeZ: where HTailF2.piecesF returns tl': ShapeZ tl'. ShapeZ.same: it reads z1, z2,
   lidb and f9 alone. shapeZ_from: FromPieces tl gives ShapeZ tl.
 - ShapeZ.ok: so FoNums.ok tl.f9 = true (Fo.Pay.shapeOf_ok).
 - public_shapeZ, public_okZ: from Verify.publicOf pol KL layout = .ok X: ShapeZ, and FoNums.ok of
   f9, at hp.tl for every member hp of X.G, at a.seam.tl for every member a of X.A, and at X.H.tl.
 - lookPubZ_okX, public_lookPubZ: Fo.Pub2.lookPubZ_ok (OnBytes/Tie/Pv/Lookup/Ends/FoLookPubZ.lean)
   with its premise paid: at every record with FromPieces; at the three kinds of records of X.

Limits: the records are the plans'. That the record with which a run goes on has these four fields
is not laid here. In public_lookPubZ the first slot next, the entries en and mk and the reading rd₀
stay free: no clause asks that different places are different entries.
Not claimed: anything on soundness, completeness or hiding.
Nor is it claimed that publicOf returns.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoZPlaced1
import OnBytes.Tie.Pv.Lookup.Ends.FoLookPubZ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo.ZPlan
open OnBytes OnBytes.Model OnBytes.DgP Fo.Pub Fo.Pub2

/-- The record of a smallness test's lookup is made of the test's own two calls, numbers of padding
keys and cap. -/
def ShapeZ (tl : HTailF2) : Prop :=
  ShapeOf #[tl.z1.call, tl.z2.call] tl.f9.pub tl.lidb tl.f9

theorem piecesF_shapeZ {tl tl' : HTailF2} (h : tl.piecesF = .ok tl') : ShapeZ tl' := by
  obtain ⟨f9, pub, h9, hp, he⟩ := piecesF_cut h
  refine ⟨f9, h9, ?_, ?_⟩
  · rw [he]
    exact hp
  · rw [he]

/-- ShapeZ reads z1, z2, lidb and f9 alone. -/
theorem ShapeZ.same {a b : HTailF2} (h : ShapeZ a) (k : SameP a b) : ShapeZ b := by
  unfold ShapeZ
  rw [k.same.z1, k.same.z2, k.f9, k.lidb]
  exact h

theorem shapeZ_from {tl : HTailF2} (h : FromPieces tl) : ShapeZ tl := by
  obtain ⟨tl0, tlp, hp, k⟩ := h
  exact (piecesF_shapeZ hp).same k

/-- The one test on the lookup's public numbers. -/
theorem ShapeZ.ok {tl : HTailF2} (h : ShapeZ tl) : FoNums.ok tl.f9 = true :=
  Fo.Pay.shapeOf_ok h

section
variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}

/-- **At the record of every smallness test in what publicOf returns.** -/
theorem public_shapeZ (h : Verify.publicOf pol KL layout = .ok X) :
    (∀ (g : ℕ) (hp : Layer.HPlan2), X.G[g]? = some hp → ShapeZ hp.tl) ∧
    (∀ (g : ℕ) (a : Attention.Plan), X.A[g]? = some a → ShapeZ a.seam.tl) ∧ ShapeZ X.H.tl :=
  ⟨fun g hp hg => shapeZ_from (public_G_from h g hp hg),
    fun g a hg => shapeZ_from (public_A_from h g a hg), shapeZ_from (public_H_from h)⟩

/-- **The test FoNums.ok says yes there.** -/
theorem public_okZ (h : Verify.publicOf pol KL layout = .ok X) :
    (∀ (g : ℕ) (hp : Layer.HPlan2), X.G[g]? = some hp → FoNums.ok hp.tl.f9 = true) ∧
    (∀ (g : ℕ) (a : Attention.Plan), X.A[g]? = some a → FoNums.ok a.seam.tl.f9 = true) ∧
    FoNums.ok X.H.tl.f9 = true :=
  ⟨fun g hp hg => ((public_shapeZ h).1 g hp hg).ok, fun g a hg => ((public_shapeZ h).2.1 g a hg).ok,
    (public_shapeZ h).2.2.ok⟩

end

section
variable {M₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀]

/-- lookPubZ_ok, its premise paid at every record that comes from piecesF. -/
theorem lookPubZ_okX {tl : HTailF2} (h : FromPieces tl) (en : Ent3 → J₀) (mk : ℕ → J₀) (next : ℕ)
    (rd₀ : M₀ → J₀ → Cb.Gl.E) (St : Type) :
    LookPubOK (lookPubZ tl en mk next rd₀ St) #[tl.z1.call, tl.z2.call] tl.f9.pub tl.lidb 5 next mk
      (plV tl en) :=
  lookPubZ_ok tl en mk next rd₀ St (shapeZ_from h)

/-- **The digits' share of the public record, from publicOf's success alone.** -/
theorem public_lookPubZ {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) (en : Ent3 → J₀) (mk : ℕ → J₀) (next : ℕ)
    (rd₀ : M₀ → J₀ → Cb.Gl.E) (St : Type) :
    (∀ (g : ℕ) (hp : Layer.HPlan2), X.G[g]? = some hp →
      LookPubOK (lookPubZ hp.tl en mk next rd₀ St) #[hp.tl.z1.call, hp.tl.z2.call] hp.tl.f9.pub
        hp.tl.lidb 5 next mk (plV hp.tl en)) ∧
    (∀ (g : ℕ) (a : Attention.Plan), X.A[g]? = some a →
      LookPubOK (lookPubZ a.seam.tl en mk next rd₀ St) #[a.seam.tl.z1.call, a.seam.tl.z2.call]
        a.seam.tl.f9.pub a.seam.tl.lidb 5 next mk (plV a.seam.tl en)) ∧
    LookPubOK (lookPubZ X.H.tl en mk next rd₀ St) #[X.H.tl.z1.call, X.H.tl.z2.call] X.H.tl.f9.pub
      X.H.tl.lidb 5 next mk (plV X.H.tl en) :=
  ⟨fun g hp hg => lookPubZ_okX (public_G_from h g hp hg) en mk next rd₀ St,
    fun g a hg => lookPubZ_okX (public_A_from h g a hg) en mk next rd₀ St,
    lookPubZ_okX (public_H_from h) en mk next rd₀ St⟩

end

end Fo.ZPlan
