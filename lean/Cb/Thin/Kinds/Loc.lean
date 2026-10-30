-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Thin/Kinds/Loc.lean.
A KNOW-ONLY LEMMA FOR EACH KIND OF MOVE. THE KIND «loc» (LdLocD, Cb/Req1/LdSegKit.lean:357-445).
D5 LdLocD.HypK: Near's relR and on, to the letter, and laws. NOT IN IT: Near's clause on the exact
relation and its clause on the core.
K5 LdLocD.goodK, BY «the exact side swapped»: the four read neither the joint's exact relation nor
its core nor H: so the library's own theorem is called at the record D' that differs from D in these
two components of A alone, where the two dropped clauses hold by definition; the four fields of
D'.link ARE D.link's, by unfolding. No line of the library is repeated.
NO THIN DEFINITION OR PREMISE names a bundle, an honest side, a joint's exact relation or core. THE
CONTROLS AND EXAMPLES DO.

-/
import Cb.Thin.Kinds.Rules
import Cb.Req1.LdSegProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb
open Iop Prob Hiop Cb.Ood IOR IOR.Chain

/-- D5. -/
structure LdLocD.HypK {E Kc : Type} [Field E] [Fintype E] (D : LdLocD E Kc) : Prop where
  relR : ∀ a w,
    D.A.relR a w ↔
    ConL D.C.N D.e D.Φ (a.1.1.1, a.2.1) (D.cut w.1) ∧
    (∀ k, (D.hd.o k).decW (D.hd.sW k a.2.1) (a.1.1.2 k) = some (D.hd.msg (D.cut w.1).1 k)) ∧
    D.A₁.relR (a.1.2, a.2.2) w
  on   : ∀ a,
    D.A.on a ↔ (∀ k, ¬ (D.hd.o k).ClashW (D.hd.sW k a.2.1) (a.1.1.2 k).1) ∧ D.A₁.on (a.1.2, a.2.2)
  laws : D.hd.Laws D.e

/-- K5. -/
theorem LdLocD.goodK {E Kc : Type} [Field E] [Fintype E] (D : LdLocD E Kc) (h : D.HypK) :
    D.link.GoodK := by
  have g := ldSeg_loc_goodT
    { D with
      A := ⟨fun x y w =>
          Con D.C.N D.Φ x.1.1 y.1 (D.cut w.1) ∧
          (∀ k, (D.hd.o k).Z.val (x.1.2 k).1 (D.hd.msg (D.cut w.1).1 k) = (x.1.2 k).2) ∧
          D.A₁.rel x.2 y.2 w,
        D.A.relR, D.A.on, D.A₁.core⟩ }
    ⟨⟨fun _ _ _ => Iff.rfl, h.relR, h.on, fun _ => rfl⟩, h.laws⟩
  exact ⟨g.point, g.isLocal, g.onOut, g.know⟩

/-! ## The controls -/

/-- (c1). -/
theorem LdLocD.hypK_of_hyp {E Kc : Type} [Field E] [Fintype E] (D : LdLocD E Kc) (h : D.Hyp) :
    D.HypK :=
  ⟨h.near.relR, h.near.on, h.laws⟩

/-- (c2). -/
example {E Kc : Type} [Field E] [Fintype E] (D : LdLocD E Kc) (h : D.Hyp) :
    (ldSeg_loc_goodT D h).know = (D.goodK (D.hypK_of_hyp h)).know := rfl
example {E Kc : Type} [Field E] [Fintype E] (D : LdLocD E Kc) (h : D.Hyp) :
    (ldSeg_loc_goodT D h).onOut = (D.goodK (D.hypK_of_hyp h)).onOut := rfl
example {E Kc : Type} [Field E] [Fintype E] (D : LdLocD E Kc) (h : D.Hyp) :
    (ldSeg_loc_goodT D h).isLocal = (D.goodK (D.hypK_of_hyp h)).isLocal := rfl
example {E Kc : Type} [Field E] [Fintype E] (D : LdLocD E Kc) (h : D.Hyp) :
    (ldSeg_loc_goodT D h).point = (D.goodK (D.hypK_of_hyp h)).point := rfl

end Cb

#check @Cb.LdLocD.goodK
#print Cb.LdLocD.HypK
