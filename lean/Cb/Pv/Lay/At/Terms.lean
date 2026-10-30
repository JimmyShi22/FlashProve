-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/At/Terms.lean: the parameters of the sumcheck of the terms of a layers' sub-proof
(Cb/Pv/Lay/Tok.lean) at a value: the library's description of a group of layers
(Inst/Model/FF/Objects.lean).

The summand of the sumcheck of the terms is the sum of the products of two values at a position that
stand in the keys of a group of layers. It is written by the late panels: at a point u it is the sum
Sig1 of their shares at the contractions of the cells at u, and each share is a sum of terms
  (a coefficient) * (a shown contraction, or the extension of a public vector) * (a kept value)
(Cb/Pv/Lay/End/TermsSum.lean).

Main names:
  `TermPar0`: what stays free: the sizes, the tables, the first layer, the entries, how the entries
  are read as cells and as weights, and the places of the sumcheck's own masks.
  `ShA`, `KpB`, `PbC`: the names of the shown, the kept and the public vectors.
  `recAt`: the contractions of the cells at a point, with the honest routed gated products.
  `recV`: a record with other values in the places of the shown contractions.
  `TermPar0.tm`: the parameters. The state is the lookup's point z.
  `kb_sum`: the sum over the kept names of coefficient, factor and kept value is Sig1.
  `tm_smd`: the summand at a position is Sig1 at the contractions at that vertex of the cube.
  `tm_sum`: the extension of the summand at the token part of z is ClT, the honest hidden sum.
  `tm_kept`: the kept part at the last point is Sig1 at the contractions at that point with the
  shown values in the places of the shown contractions.
Limits: tm_sum asks what the panel QK needs of the sizes, that in each layer the shifts of queries
and keys are equal or both at least 16, and that a layer has twice the hidden units of an expert.
That the programs' vectors, coefficients and point are these is not said here. Nothing is said on an
honest prover, on completeness or on zero knowledge.


-/
import Cb.Pv.Lay.Over
import Cb.Pv.Lay.End.TermsSum
import Cb.Pv.Lay.End.SigG
import Cb.Pv.Lay.End.SigT

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.At
open Cb Finset
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell LW Pan Rd rdTrue Sig1 Gpos ClT wc call kp hhU valU xU zpos ew AH
  Wqk Ct St lf)
open Cb.Pv.Lay.End (kQK kXR kG kU kD sig1_terms)

noncomputable section

/-! ### Functions of a point that are extensions of vectors -/

section Ext
variable {E : Type} [Field E] {g : ℕ}

/-- F is the extension of a vector over the cube of g bits. -/
def IsExt (g : ℕ) (F : (ℕ → E) → E) : Prop := ∃ v : ℕ → E, ∀ u, F u = Blocks.ext g v u

theorem IsExt.of (v : ℕ → E) : IsExt g fun u => Blocks.ext g v u := ⟨v, fun _ => rfl⟩

/-- Such a function is the extension of its own values at the vertices. -/
theorem IsExt.cube {F : (ℕ → E) → E} (h : IsExt g F) (u : ℕ → E) :
    Blocks.ext g (fun i => F (Blocks.cubePt g i)) u = F u := by
  obtain ⟨v, hv⟩ := h
  rw [hv u]
  exact Blocks.ext_congr (fun i hi => by rw [hv, Blocks.ext_cubePt g v hi]) u

theorem IsExt.add {F G : (ℕ → E) → E} (hF : IsExt g F) (hG : IsExt g G) :
    IsExt g fun u => F u + G u := by
  obtain ⟨v, hv⟩ := hF
  obtain ⟨w, hw⟩ := hG
  exact ⟨fun X => v X + w X, fun u => by
    show F u + G u = _
    rw [hv, hw, Blocks.ext_add]⟩

theorem IsExt.sub {F G : (ℕ → E) → E} (hF : IsExt g F) (hG : IsExt g G) :
    IsExt g fun u => F u - G u := by
  obtain ⟨v, hv⟩ := hF
  obtain ⟨w, hw⟩ := hG
  exact ⟨fun X => v X - w X, fun u => by
    show F u - G u = _
    rw [hv, hw, Blocks.ext_sub]⟩

theorem IsExt.const_mul {F : (ℕ → E) → E} (c : E) (hF : IsExt g F) : IsExt g fun u => c * F u := by
  obtain ⟨v, hv⟩ := hF
  exact ⟨fun X => c * v X, fun u => by
    show c * F u = _
    rw [hv, Blocks.ext_smul]⟩

theorem IsExt.mul_const {F : (ℕ → E) → E} (c : E) (hF : IsExt g F) : IsExt g fun u => F u * c := by
  obtain ⟨v, hv⟩ := hF
  exact ⟨fun X => c * v X, fun u => by
    show F u * c = _
    rw [hv, Blocks.ext_smul, mul_comm]⟩

theorem IsExt.sum {ι : Type} (s : Finset ι) {F : ι → (ℕ → E) → E} (h : ∀ j, IsExt g (F j)) :
    IsExt g fun u => ∑ j ∈ s, F j u := by
  choose v hv using h
  exact ⟨fun X => ∑ j ∈ s, v j X, fun u => by
    rw [Blocks.ext_sum]
    exact sum_congr rfl fun j _ => hv j u⟩

end Ext

/-! ### The names -/

/-- The shown vectors: the reciprocal of a norm; the score of a routed layer; an entry of its
selector. -/
abbrev ShA (D : Dim) : Type := Fin D.nNu ⊕ (Fin D.ne ⊕ Fin D.ne × Fin D.nx)

/-- The kept vectors, panel by panel, in the order of sig1_terms: Gr, Ur, N1, N2, Dr, QK, XR, DD,
MR. -/
abbrev KpB (D : Dim) : Type :=
  ((((((((Fin D.ne × Fin D.nx) ⊕ (Fin D.ne × Fin D.nx)) ⊕ Fin D.nl) ⊕ Fin D.nl) ⊕
    (Fin D.ne × Fin D.nx)) ⊕ (Fin D.nl × Fin D.P.ch)) ⊕ Fin D.ne) ⊕ (Fin D.ne × Fin D.nx)) ⊕
      (Fin D.ne × Fin D.nx)

/-- The public vectors: a layer and a channel of a head. -/
abbrev PbC (D : Dim) : Type := Fin D.nl × Fin D.P.ch

/-- A function on the kept names, from its nine parts. -/
def el9 {D : Dim} {α : Type} (g u : Fin D.ne × Fin D.nx → α) (n1 n2 : Fin D.nl → α)
    (d : Fin D.ne × Fin D.nx → α) (qk : Fin D.nl × Fin D.P.ch → α) (xr : Fin D.ne → α)
    (dd mr : Fin D.ne × Fin D.nx → α) : KpB D → α :=
  Sum.elim (Sum.elim (Sum.elim (Sum.elim (Sum.elim (Sum.elim (Sum.elim (Sum.elim g u) n1) n2) d)
    qk) xr) dd) mr

/-- The name of the reciprocal of the first norm of layer l, and of the second. -/
def recA1 {D : Dim} (l : Fin D.nl) : ShA D :=
  .inl ⟨2 * l, by have := l.isLt; show 2 * (l : ℕ) < 2 * D.nl; omega⟩
def recA2 {D : Dim} (l : Fin D.nl) : ShA D :=
  .inl ⟨2 * l + 1, by have := l.isLt; show 2 * (l : ℕ) + 1 < 2 * D.nl; omega⟩
def scA {D : Dim} (l : Fin D.ne) : ShA D := .inr (.inl l)
def selA {D : Dim} (p : Fin D.ne × Fin D.nx) : ShA D := .inr (.inr p)

section Letters
variable {E : Type} [Field E] [scl : Scl] (D : Dim) (tb : Tables) (L0 : ℕ)

/-- The contractions of the cells at the point u, with the honest routed gated products. -/
def recAt (t : Cell → E) (z u : ℕ → E) : Rd E :=
  rdTrue D t z u (fun _ _ => 0) fun l' j => hhU D t (2 * l' + 1) (D.fe + j) u

/-- The shown contractions of a record, by name. -/
def sh9 (r : Rd E) : ShA D → E :=
  Sum.elim (fun ν => r.R2 ν) (Sum.elim (fun l => r.sc2 l) fun p => r.sel2 p.1 p.2)

/-- The record r with the values v in the places of the shown contractions. -/
def recV (r : Rd E) (v : ShA D → E) : Rd E :=
  { r with
    R2 := fun ν => if h : ν < D.nNu then v (.inl ⟨ν, h⟩) else 0
    sc2 := fun l => if h : l < D.ne then v (.inr (.inl ⟨l, h⟩)) else 0
    sel2 := fun l e =>
      if h : l < D.ne ∧ e < D.nx then v (.inr (.inr (⟨l, h.1⟩, ⟨e, h.2⟩))) else 0 }

/-- The coefficient of a kept name. -/
def cf9 (z : ℕ → E) : KpB D → E :=
  el9 (fun p => wc D z (call .G) * (Pan.Gr p.1).wt D z p.2)
    (fun p => wc D z (call .U) * (Pan.Ur p.1).wt D z p.2)
    (fun l => wc D z (call .N1) * Pan.N1.wt D z l) (fun l => wc D z (call .N2) * Pan.N2.wt D z l)
    (fun p => wc D z (call .D) * (Pan.Dr p.1).wt D z p.2)
    (fun p => wc D z (call .QK) * Pan.QK.wt D z p.1) (fun l => wc D z (call .XR) * Pan.XR.wt D z l)
    (fun p => wc D z (call .DD) * Pan.DD.wt D z p.1) fun p => wc D z (call .MR) * Pan.MR.wt D z p.1

/-- The factor beside a kept value: a shown contraction of r, or, for the panel QK, the public
number kp at the point zh. -/
def fc9 (z zh : ℕ → E) (r : Rd E) : KpB D → E :=
  el9 (fun p => r.sel2 p.1 p.2) (fun p => r.sel2 p.1 p.2) (fun l => r.R2 (2 * l))
    (fun l => r.R2 (2 * l + 1)) (fun p => r.sel2 p.1 p.2) (fun p => kp D tb L0 z zh p.1 p.2)
    (fun l => r.sc2 l) (fun p => r.sel2 p.1 p.2) fun p => r.sel2 p.1 p.2

/-- The kept value of a name at the record r. -/
def kp9 (w : ℕ → LW E) (z zh : ℕ → E) (r : Rd E) : KpB D → E :=
  el9 (fun p => kG D r tb L0 w z zh p.1 p.2) (fun p => kU D r tb L0 w z zh p.1 p.2)
    (fun l => r.xF (2 * l)) (fun l => r.xF (2 * l + 1)) (fun p => kD D r tb L0 w z zh p.1 p.2)
    (fun p => kQK D r w z p.1 p.2) (fun l => kXR D r z l) (fun p => r.lr2 p.1 p.2)
    fun p => r.lr2 p.1 p.2

/-- The sum over the kept names is Sig1. -/
theorem kb_sum (w : ℕ → LW E) (z zh : ℕ → E) (r : Rd E) :
    ∑ b, cf9 D z b * fc9 D tb L0 z zh r b * kp9 D tb L0 w z zh r b =
      Sig1 D r tb L0 w z zh := by
  rw [sig1_terms]
  simp only [← Fin.sum_univ_eq_sum_range, Fintype.sum_sum_type, Fintype.sum_prod_type, cf9, fc9,
    kp9, el9, Sum.elim_inl, Sum.elim_inr]

omit scl in
/-- A kept value does not read the shown contractions. -/
theorem kp9_recV (w : ℕ → LW E) (z zh : ℕ → E) (r : Rd E) (v : ShA D → E) (b : KpB D) :
    kp9 D tb L0 w z zh (recV D r v) b = kp9 D tb L0 w z zh r b := by
  rcases b with (((((((p | p) | l) | l) | p) | p) | l) | p) | p <;> rfl

omit scl in
/-- Each kept value is, as a function of the point, the extension of a vector. -/
theorem kp9_isExt (t : Cell → E) (w : ℕ → LW E) (z : ℕ → E) (b : KpB D) :
    IsExt D.lT fun u => kp9 D tb L0 w z u (recAt D t z u) b := by
  rcases b with (((((((p | p) | l) | l) | p) | p) | l) | p) | p
  · show IsExt D.lT fun u => ∑ j ∈ range D.d,
      Blocks.ext D.lT (fun i => Inst.Model.FFSeg.val t .xr p.1 j i) u *
        ∑ x ∈ range D.fe, ew D z .G (D.fe + x) * (w (2 * p.1 + 1)).Eg p.2 j x
    exact IsExt.sum _ fun j => IsExt.mul_const _ (IsExt.of _)
  · show IsExt D.lT fun u => ∑ j ∈ range D.d,
      Blocks.ext D.lT (fun i => Inst.Model.FFSeg.val t .xr p.1 j i) u *
        ∑ x ∈ range D.fe, ew D z .U (D.fe + x) * (w (2 * p.1 + 1)).Eu p.2 j x
    exact IsExt.sum _ fun j => IsExt.mul_const _ (IsExt.of _)
  · show IsExt D.lT fun u => ∑ x ∈ range D.d,
      ew D z (if 2 * (l : ℕ) % 2 = 0 then .N1 else .N2) x *
        Blocks.ext D.lT (fun i => Inst.Model.FFSeg.xS D t (2 * l) x i) u
    exact IsExt.sum _ fun x => IsExt.const_mul _ (IsExt.of _)
  · show IsExt D.lT fun u => ∑ x ∈ range D.d,
      ew D z (if (2 * (l : ℕ) + 1) % 2 = 0 then .N1 else .N2) x *
        Blocks.ext D.lT (fun i => Inst.Model.FFSeg.xS D t (2 * l + 1) x i) u
    exact IsExt.sum _ fun x => IsExt.const_mul _ (IsExt.of _)
  · show IsExt D.lT fun u => ∑ j ∈ range D.fe,
      Blocks.ext D.lT (fun i => Inst.Model.FFSeg.hh t (2 * p.1 + 1) (D.fe + j) i) u *
        ∑ x ∈ range D.d, ew D z .D x * (w (2 * p.1 + 1)).Ed p.2 j x
    exact IsExt.sum _ fun j => IsExt.mul_const _ (IsExt.of _)
  · show IsExt D.lT fun u => ∑ j ∈ range D.d,
      Blocks.ext D.lT (fun i => Inst.Model.FFSeg.val t .a p.1 j i) u *
        ∑ h ∈ range (D.P.nq + D.P.nkv), AH D z h * Wqk D w p.1 j h p.2
    exact IsExt.sum _ fun j => IsExt.mul_const _ (IsExt.of _)
  · show IsExt D.lT fun u => ∑ x ∈ range D.d, ew D z .XR x *
      Blocks.ext D.lT (fun i => Inst.Model.FFSeg.val t .m (2 * l + 1) x i) u
    exact IsExt.sum _ fun x => IsExt.const_mul _ (IsExt.of _)
  · exact IsExt.of _
  · exact IsExt.of _

omit scl in
/-- The public number kp is, as a function of the point, the extension of a vector. -/
theorem kp_isExt (z : ℕ → E) (l x : ℕ) : IsExt D.lT fun u => kp D tb L0 z u l x := by
  unfold Inst.Model.FFSeg.kp
  by_cases h : x % 2 = 0
  · simp only [if_pos h]
    exact (IsExt.mul_const _ (IsExt.of _)).add (IsExt.mul_const _ (IsExt.of _))
  · simp only [if_neg h]
    exact (IsExt.mul_const _ (IsExt.of _)).sub (IsExt.mul_const _ (IsExt.of _))

end Letters

/-! ### What stays free -/

/-- The letters of the sumcheck of the terms that stay free. -/
structure TermPar0 (E : Type) [Field E] [Fintype E] [scl : Scl] where
  /-- the sizes, the tables, the number of the group's first layer -/
  D : Dim
  tb : Tables
  L0 : ℕ
  /-- the entries; how they are read as cells and as weights -/
  J : Type
  [finJ : Fintype J]
  rd : (J → E) → Cell → E
  rw : (J → E) → ℕ → LW E
  /-- the masks: the sent sum's; the hiding polynomial's coefficients; the end values' -/
  rT : J
  wT : PIdx (ldPartFmt E D.lT (fun _ => 2) ++ [pDummy E 1]) → J
  cT : ShA D → J

attribute [instance] TermPar0.finJ

variable {E : Type} [Field E] [Fintype E] [scl : Scl]

namespace TermPar0
variable (P : TermPar0 E)

/-- The terms with a shown factor. -/
def tb9 : KpB P.D → List (((ℕ → E) → E) × List (ShA P.D)) := fun b =>
  el9 (fun p => [(fun z => cf9 P.D z b, [selA p])]) (fun p => [(fun z => cf9 P.D z b, [selA p])])
    (fun l => [(fun z => cf9 P.D z b, [recA1 l])]) (fun l => [(fun z => cf9 P.D z b, [recA2 l])])
    (fun p => [(fun z => cf9 P.D z b, [selA p])]) (fun _ => [])
    (fun l => [(fun z => cf9 P.D z b, [scA l])]) (fun p => [(fun z => cf9 P.D z b, [selA p])])
    (fun p => [(fun z => cf9 P.D z b, [selA p])]) b

/-- The terms with a public factor. -/
def tc9 : KpB P.D → List (((ℕ → E) → E) × PbC P.D) := fun b =>
  el9 (fun _ => []) (fun _ => []) (fun _ => []) (fun _ => []) (fun _ => [])
    (fun p => [(fun z => cf9 P.D z b, p)]) (fun _ => []) (fun _ => []) (fun _ => []) b

/-- The parameters of the sumcheck of the terms, at the value. The state is the lookup's point. -/
def tm : TokL E where
  J := P.J
  k := P.D.lT
  St := ℕ → E
  A := ShA P.D
  B := KpB P.D
  vA := fun z m a i => sh9 P.D (recAt P.D (P.rd m) z (Blocks.cubePt P.D.lT i)) a
  vB := fun z m b i => kp9 P.D P.tb P.L0 (P.rw m) z (Blocks.cubePt P.D.lT i)
    (recAt P.D (P.rd m) z (Blocks.cubePt P.D.lT i)) b
  pnt := fun z j => zpos P.D z j
  t0 := []
  tb := P.tb9
  C := PbC P.D
  vC := fun z c i => kp P.D P.tb P.L0 z (Blocks.cubePt P.D.lT i) c.1 c.2
  tc := P.tc9
  dy := 1
  h0 := fun _ h => absurd h (List.not_mem_nil)
  hb := fun b t ht => by
    rcases b with (((((((p | p) | l) | l) | p) | p) | l) | p) | p <;>
      simp [tb9, el9] at ht <;> subst ht <;> exact ⟨le_refl 1, le_refl 1⟩
  rJ := P.rT
  wAt := P.wT
  cAt := P.cT
  Rd := fun _ _ => True

/-- The terms of a kept name, on values v of the shown vectors and values c of the public ones. -/
theorem terms_at (z : ℕ → E) (v : ShA P.D → E) (c : PbC P.D → E) (zh : ℕ → E) (r : Rd E)
    (hv : ∀ a, v a = sh9 P.D r a) (hc : ∀ q, c q = kp P.D P.tb P.L0 z zh q.1 q.2) (b : KpB P.D) :
    ((P.tb9 b).map fun t => t.1 z * (t.2.map v).prod).sum +
        ((P.tc9 b).map fun t => t.1 z * c t.2).sum =
      cf9 P.D z b * fc9 P.D P.tb P.L0 z zh r b := by
  rcases b with (((((((p | p) | l) | l) | p) | p) | l) | p) | p <;>
    simp [tb9, tc9, el9, fc9, hv, hc, sh9, selA, scA, recA1, recA2]

/-- The summand at a position is Sig1 at the contractions at that vertex of the cube. -/
theorem tm_smd (z : ℕ → E) (m : P.J → E) (X : ℕ) :
    P.tm.smd z m X =
      Sig1 P.D (recAt P.D (P.rd m) z (Blocks.cubePt P.D.lT X)) P.tb P.L0 (P.rw m) z
        (Blocks.cubePt P.D.lT X) := by
  rw [← kb_sum]
  show (([] : List (((ℕ → E) → E) × List (ShA P.D))).map _).sum + _ = _
  rw [List.map_nil, List.sum_nil, zero_add]
  exact sum_congr rfl fun b _ => by
    rw [← P.terms_at z _ _ (Blocks.cubePt P.D.lT X) _ (fun _ => rfl) (fun _ => rfl) b]
    rfl

/-- The extension of the summand at the token part of the lookup's point is the honest hidden
sum. -/
theorem tm_sum (C : P.D.ChOK)
    (hk : ∀ l, l < P.D.nl →
      (P.D.Pl l).kq = (P.D.Pl l).kk ∨ (16 ≤ (P.D.Pl l).kq ∧ 16 ≤ (P.D.Pl l).kk))
    (hf : P.D.f = 2 * P.D.fe) (z : ℕ → E) (m : P.J → E) :
    Blocks.ext P.D.lT (P.tm.smd z m) (Blocks.nat (P.tm.pnt z)) =
      ClT P.D (P.rd m) P.tb P.L0 (P.rw m) z := by
  have e : Blocks.ext P.D.lT (P.tm.smd z m) (Blocks.nat (P.tm.pnt z)) =
      Blocks.ext P.D.lT (P.tm.smd z m) (zpos P.D z) :=
    Blocks.ext_congr_point (fun t ht => Blocks.nat_fun_of_lt (zpos P.D z) ht) _
  rw [e, End.Sig.clT_gpos P.D (P.rd m) P.tb P.L0 (P.rw m) z hf]
  refine Blocks.ext_congr (fun X _ => ?_) _
  rw [tm_smd]
  exact End.Sig.sig1_gpos P.D (P.rd m) P.tb P.L0 (P.rw m) z _ _ _ C hk fun _ _ _ _ => rfl

omit scl in
/-- The kept part of a sumcheck with kept maps, at the verifier's point. -/
theorem kept_eq {St J : Type} [Fintype J] {S : LdPartSm E St J} (Q : KeptSm S) (M : LdPartMk S)
    (o : (Q.our M).par.Out) (m : J → E) :
    keptAt (Q.our M).par o m =
      ∑ b, Q.polB o.st (Q.outPt M o) o.vals b * Q.Fb o.st m b (Q.outPt M o) := by
  unfold KeptSm.outPt
  rw [← ldPartVars_ini E S.k M.n (ldPartDat E S.k M.n (S.w o.st))
    (pDummy E M.DY) (pDummyD E M.DY) o.pt]
  rfl

/-- The kept part at the last point is Sig1 at the contractions at that point, with the shown values
in the places of the shown contractions. -/
theorem tm_kept (o : P.tm.toSum.T.par.Out) (m : P.J → E) :
    keptAt P.tm.toSum.T.par o m =
      Sig1 P.D (recV P.D (recAt P.D (P.rd m) o.st (Blocks.nat (P.tm.Kp.outPt P.tm.Mk o))) o.vals)
        P.tb P.L0 (P.rw m) o.st (Blocks.nat (P.tm.Kp.outPt P.tm.Mk o)) := by
  rw [← kb_sum]
  refine (kept_eq P.tm.Kp P.tm.Mk o m).trans (sum_congr rfl fun b _ => ?_)
  rw [kp9_recV, ← P.terms_at o.st o.vals
    (fun q => Blocks.ext P.D.lT (P.tm.vC o.st q) (Blocks.nat (P.tm.Kp.outPt P.tm.Mk o)))
    (Blocks.nat (P.tm.Kp.outPt P.tm.Mk o)) _ (fun a => ?_)
    (fun q => (kp_isExt P.D P.tb P.L0 o.st q.1 q.2).cube _) b]
  · congr 1
    · unfold KeptSm.polB
      show (((P.tb9 b).map P.tm.tm ++ (P.tc9 b).map P.tm.tmC).map _).sum = _
      rw [List.map_append, List.sum_append, List.map_map, List.map_map]
      congr 1
      refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
      exact mul_one _
    · exact (kp9_isExt P.D P.tb P.L0 (P.rd m) (P.rw m) o.st b).cube _
  · rcases a with ν | l | p
    · show o.vals (.inl ν) = if h : (ν : ℕ) < P.D.nNu then o.vals (.inl ⟨ν, h⟩) else 0
      rw [dif_pos ν.isLt]
    · show o.vals (.inr (.inl l)) =
        if h : (l : ℕ) < P.D.ne then o.vals (.inr (.inl ⟨l, h⟩)) else 0
      rw [dif_pos l.isLt]
    · show o.vals (.inr (.inr p)) =
        if h : (p.1 : ℕ) < P.D.ne ∧ (p.2 : ℕ) < P.D.nx then
          o.vals (.inr (.inr (⟨p.1, h.1⟩, ⟨p.2, h.2⟩))) else 0
      rw [dif_pos ⟨p.1.isLt, p.2.isLt⟩]

end TermPar0

end
end Cb.Pv.Lay.At

#print axioms Cb.Pv.Lay.At.TermPar0.tm_sum
#print axioms Cb.Pv.Lay.At.TermPar0.tm_kept
