-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/LateMeet.lean: what the library's late entries are worth, with each at its form's
value: the extensions of the cells that the early entries spell, family by family.

The library's ledger of a layers' sub-proof speaks of early and late entries. With each late entry
at the value of its form (lateAt, Johnson/Road/K4/CarriageParts.lean) the library already shows that
its tables are true: tables_true (Cb/Pv/Lay/End/NormsA.lean), terms_true (TermsA.lean), gated_tables
(GatedShare.lean). Here these three are called at the chain's letters, under the library's own
records NormsOk, TermsOk, GatedOk; and each family of reads is brought to the shape of the right
sides of Johnson/Road/K4/ReadsThere2.lean: cells by their names, the weights of a block's features
from coordinate 0 on, no 128.

Main names:
  `tables_uP`, `tables_uR`, `tables_uSel`, `tables_uXi0`, `tables_uXi`: the fields of TablesTrue in
    that shape, at any letters; `readAt_off`: the same for the gated products' readAt.
  `yL`: the entries: the early ones of the messages m, each late one at its form's value.
  `late_norms`, `late_terms`, `late_gated`: the three records at yL.
  `late_uP`, `late_uR`, `late_uSel`, `late_uXi0`, `late_uXi`; `late_uS5`, `late_uU5`, `late_uS6`,
    `late_uU6`: one family each, at the library's own names and records. For the terms' three
    families the fields of late_terms have the shape as they stand.
Limits. NormsOk, TermsOk and GatedOk are premises: that the forms fm are the library's and that the
names are names of late entries. The cells are P.rd (P.msg m). Nothing of a verifier's text occurs:
no array of reads, no world. Identities alone; nothing on soundness.


-/
import Johnson.Road.K4.CarriageParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Finset
open TWhole Cb Cb.Sub Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Cell Arr lF lFe)

/-! ## The records' fields, in the shape of the verifier's side -/

section Fields

variable {E J : Type} [Field E] {N : NormsNames J} {e : NormsE E}
  {D : Dim} {t : Cell → E} {lNI b s B : ℕ} {y : J → E}

/-- Cell n of the row of norm ν at the norms' token point. -/
theorem tables_uP (T : TablesTrue N e D t lNI b s B y) {ν n : ℕ} (hν : ν < D.nNu) (hn : n < 99) :
    y (N.uP ν n) = Blocks.ext D.lT (fun p => t ⟨.D, 0, ν, n, p⟩) e.pV := by
  have h := T.atP ν n hν hn
  simp only [led_cell] at h
  rw [Blocks.ext_add, Blocks.ext_const] at h
  exact add_right_cancel h

/-- Cell n of the row of norm ν at the end point of the token sumcheck of the row products. -/
theorem tables_uR (T : TablesTrue N e D t lNI b s B y) {ν n : ℕ} (hν : ν < D.nNu) (hn : n < 99) :
    y (N.uR ν n) = Blocks.ext D.lT (fun p => t ⟨.D, 0, ν, n, p⟩) e.r2 := by
  have h := T.atR ν n hν hn
  simp only [led_cell] at h
  rw [Blocks.ext_add, Blocks.ext_const] at h
  exact add_right_cancel h

/-- Entry x of the selector of routed layer l at the tail of the lookup's point. -/
theorem tables_uSel (T : TablesTrue N e D t lNI b s B y) {l x : ℕ} (hl : l < D.ne)
    (hx : x < D.nx) :
    y (N.uSel l x) = Blocks.ext D.lT (fun p => t ⟨.sel, 0, l, x, p⟩) e.zt := by
  rw [T.sel l x hl hx]
  simp only [sel_cell]

/-- Limb l of block kh of the stream that comes in, at the squares' point. -/
theorem tables_uXi0 (T : TablesTrue N e D t lNI b s B y) (h0 : 0 < D.nNu) {l kh : ℕ} (hl : l < 5)
    (hk : kh < B) :
    y (N.uXi 0 l kh) = ∑ r ∈ range (2 ^ s), Blocks.eqN s 0 (fun j => e.r1 (lNI + b + j)) r *
      Blocks.ext D.lT (fun p => t ⟨.x0, l, 0, kh * 2 ^ s + r, p⟩)
        (fun j => e.r1 (lNI + (b + s) + j)) := by
  rw [T.xi 0 l kh h0 hl hk]
  refine sum_congr rfl fun r _ => ?_
  rw [eqN_off s (lNI + b) e.r1 r]
  rfl

/-- Limb l of block kh of the stream after write number ν of the group, 0 < ν. -/
theorem tables_uXi (T : TablesTrue N e D t lNI b s B y) {ν l kh : ℕ} (h0 : 0 < ν)
    (hν : ν < D.nNu) (hl : l < 5) (hk : kh < B) :
    y (N.uXi ν l kh) = ∑ r ∈ range (2 ^ s), Blocks.eqN s 0 (fun j => e.r1 (lNI + b + j)) r *
      Blocks.ext D.lT (fun p => t ⟨.xs, l, ν - 1, kh * 2 ^ s + r, p⟩)
        (fun j => e.r1 (lNI + (b + s) + j)) := by
  have h2 : D.nNu = 2 * D.nl := rfl
  have hs : Inst.Model.FFSeg.streamAt D ν = (.xs, ν - 1) := by
    unfold Inst.Model.FFSeg.streamAt
    rw [if_neg (by omega), if_neg (by omega)]
  rw [T.xi ν l kh hν hl hk]
  refine sum_congr rfl fun r _ => ?_
  rw [eqN_off s (lNI + b) e.r1 r]
  simp only [Inst.Model.FFSeg.bS, hs]

/-- The read of a limb of a block of the gated products' tensors, with the weights of the block's
features from coordinate 0 on. -/
theorem readAt_off (A : Arr) (r : ℕ → E) (g l lam kh : ℕ) :
    readAt D t A r g s l lam kh =
      ∑ q ∈ range (2 ^ s), Blocks.eqN s 0 (fun j => r (g + j)) q *
        Blocks.ext D.lT (fun p => t ⟨A, l, lam, kh * 2 ^ s + q, p⟩) (fun j => r (g + s + j)) := by
  unfold readAt
  exact sum_congr rfl fun q _ => by rw [eqN_off s g r q]

end Fields

/-! ## At the chain's letters -/

variable {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type} (P : FullPar E M X)
  {Nm J₂ : Type} {Y : LateLay Nm J₂} {ιN : NormsNm → Nm}
  {ιT : TermsNm → Nm} {ιG : GatedNm → Nm} {fm : (tailF P).s7.Nx → Nm → TWhole.Aff E P.J}
  {zt : (tailF P).s7.Nx → ℕ → E} {b s B sG : ℕ}

/-- The entries: the early ones of the messages m, each late one at its form's value. -/
noncomputable abbrev yL (Y : LateLay Nm J₂) (fm : (tailF P).s7.Nx → Nm → TWhole.Aff E P.J)
    (e : (tailF P).s7.Nx) (m : M) : P.J ⊕ J₂ → E :=
  Sum.elim (P.msg m) (lateAt P Y fm e m)

/-- The norms' tables are true at yL. -/
theorem late_norms (O : NormsOk P.toOwnPar P.wPart Y ιN fm zt b s B) (e : (tailF P).s7.Nx)
    (m : M) :
    TablesTrue (namesAt P.nr (readsAt Y ιN)) (eAt P.toOwnPar P.wPart e (zt e)) P.D
      (P.rd (P.msg m)) (P.D.lL + 1) b s B (yL P Y fm e m) :=
  tables_true P.nr P.hrd Y ιN (fm e) _ (P.D.lL + 1) b s B (O.hfm e) O.gXi O.gP O.gR O.gS (P.msg m)

/-- The terms' tables are true at yL. -/
theorem late_terms (O : TermsOk P Y ιT fm) (e : (tailF P).s7.Nx) (m : M) :
    TermsTrue (namesT P.tp (readsT Y ιT)) (termsEAt P.tp ((tailF P).b3 e).2) P.D
      (P.rd (P.msg m)) (yL P Y fm e m) :=
  terms_true P.tp P.hrd Y ιT (fm e) _ (O.hfm e) O.gR O.gC O.gS (P.msg m)

/-- The gated products' tables are true at yL. -/
theorem late_gated (O : GatedOk P Y ιG fm sG) (e : (tailF P).s7.Nx) (m : M) :
    GatedTables (gNamesAt P.fp (gReadsAt Y ιG))
      (gatedEAt P.fp ((tailF P).b5 e).2 ((tailF P).b6 e).2) P.D (P.rd (P.msg m)) sG
      (yL P Y fm e m) :=
  gated_tables P.fp P.hrd Y ιG (fm e) _ sG (O.hfm e) O.hY (P.msg m)

section Norms

variable (O : NormsOk P.toOwnPar P.wPart Y ιN fm zt b s B) (e : (tailF P).s7.Nx) (m : M)
include O

/-- The rows at the norms' token point. -/
theorem late_uP {ν n : ℕ} (hν : ν < P.D.nNu) (hn : n < 99) :
    yL P Y fm e m ((namesAt P.nr (readsAt Y ιN)).uP ν n) =
      Blocks.ext P.D.lT (fun p => P.rd (P.msg m) ⟨.D, 0, ν, n, p⟩)
        (eAt P.toOwnPar P.wPart e (zt e)).pV :=
  tables_uP (late_norms P O e m) hν hn

/-- The rows at the end point of the token sumcheck of the row products. -/
theorem late_uR {ν n : ℕ} (hν : ν < P.D.nNu) (hn : n < 99) :
    yL P Y fm e m ((namesAt P.nr (readsAt Y ιN)).uR ν n) =
      Blocks.ext P.D.lT (fun p => P.rd (P.msg m) ⟨.D, 0, ν, n, p⟩)
        (eAt P.toOwnPar P.wPart e (zt e)).r2 :=
  tables_uR (late_norms P O e m) hν hn

/-- The selectors at the tail of the lookup's point. -/
theorem late_uSel {l x : ℕ} (hl : l < P.D.ne) (hx : x < P.D.nx) :
    yL P Y fm e m ((namesAt P.nr (readsAt Y ιN)).uSel l x) =
      Blocks.ext P.D.lT (fun p => P.rd (P.msg m) ⟨.sel, 0, l, x, p⟩)
        (eAt P.toOwnPar P.wPart e (zt e)).zt :=
  tables_uSel (late_norms P O e m) hl hx

/-- The stream that comes in, at the squares' point. -/
theorem late_uXi0 (h0 : 0 < P.D.nNu) {l kh : ℕ} (hl : l < 5) (hk : kh < B) :
    yL P Y fm e m ((namesAt P.nr (readsAt Y ιN)).uXi 0 l kh) =
      ∑ r ∈ range (2 ^ s), Blocks.eqN s 0
          (fun j => (eAt P.toOwnPar P.wPart e (zt e)).r1 (P.D.lL + 1 + b + j)) r *
        Blocks.ext P.D.lT (fun p => P.rd (P.msg m) ⟨.x0, l, 0, kh * 2 ^ s + r, p⟩)
          (fun j => (eAt P.toOwnPar P.wPart e (zt e)).r1 (P.D.lL + 1 + (b + s) + j)) :=
  tables_uXi0 (late_norms P O e m) h0 hl hk

/-- The stream after write number ν of the group, 0 < ν, at the squares' point. -/
theorem late_uXi {ν l kh : ℕ} (h0 : 0 < ν) (hν : ν < P.D.nNu) (hl : l < 5) (hk : kh < B) :
    yL P Y fm e m ((namesAt P.nr (readsAt Y ιN)).uXi ν l kh) =
      ∑ r ∈ range (2 ^ s), Blocks.eqN s 0
          (fun j => (eAt P.toOwnPar P.wPart e (zt e)).r1 (P.D.lL + 1 + b + j)) r *
        Blocks.ext P.D.lT (fun p => P.rd (P.msg m) ⟨.xs, l, ν - 1, kh * 2 ^ s + r, p⟩)
          (fun j => (eAt P.toOwnPar P.wPart e (zt e)).r1 (P.D.lL + 1 + (b + s) + j)) :=
  tables_uXi (late_norms P O e m) h0 hν hl hk

end Norms

section Gated

variable (O : GatedOk P Y ιG fm sG) (e : (tailF P).s7.Nx) (m : M)
include O

/-- The tensor s at the first product layer's point. -/
theorem late_uS5 {l i k : ℕ} (hl : l < 2) (hi : i < 2 ^ P.D.lL) (hk : k < 2 ^ (lF P.D - sG)) :
    yL P Y fm e m ((gNamesAt P.fp (gReadsAt Y ιG)).uS5 l i k) =
      ∑ q ∈ range (2 ^ sG), Blocks.eqN sG 0 (fun j =>
          (gatedEAt P.fp ((tailF P).b5 e).2 ((tailF P).b6 e).2).r5 (P.D.lL + lF P.D - sG + j)) q *
        Blocks.ext P.D.lT (fun p => P.rd (P.msg m) ⟨.sl, l, i, k * 2 ^ sG + q, p⟩) (fun j =>
          (gatedEAt P.fp ((tailF P).b5 e).2 ((tailF P).b6 e).2).r5
            (P.D.lL + lF P.D - sG + sG + j)) :=
  ((late_gated P O e m).s5 l hl i hi k hk).trans (readAt_off _ _ _ _ _ _)

/-- The tensor u at the first product layer's point. -/
theorem late_uU5 {l i k : ℕ} (hl : l < 2) (hi : i < 2 ^ P.D.lL) (hk : k < 2 ^ (lF P.D - sG)) :
    yL P Y fm e m ((gNamesAt P.fp (gReadsAt Y ιG)).uU5 l i k) =
      ∑ q ∈ range (2 ^ sG), Blocks.eqN sG 0 (fun j =>
          (gatedEAt P.fp ((tailF P).b5 e).2 ((tailF P).b6 e).2).r5 (P.D.lL + lF P.D - sG + j)) q *
        Blocks.ext P.D.lT (fun p => P.rd (P.msg m) ⟨.up, l, i, k * 2 ^ sG + q, p⟩) (fun j =>
          (gatedEAt P.fp ((tailF P).b5 e).2 ((tailF P).b6 e).2).r5
            (P.D.lL + lF P.D - sG + sG + j)) :=
  ((late_gated P O e m).u5 l hl i hi k hk).trans (readAt_off _ _ _ _ _ _)

/-- The tensor s at the second product layer's point: layer 2 i + 1, the routed half's block k. -/
theorem late_uS6 {l i k : ℕ} (hl : l < 2) (hi : i < 2 ^ (P.D.lL - 1))
    (hk : k < 2 ^ (lFe P.D - sG)) :
    yL P Y fm e m
        ((gNamesAt P.fp (gReadsAt Y ιG)).uS6 l (2 * i + 1) (2 ^ (lFe P.D - sG) + k)) =
      ∑ q ∈ range (2 ^ sG), Blocks.eqN sG 0 (fun j =>
          (gatedEAt P.fp ((tailF P).b5 e).2 ((tailF P).b6 e).2).r6
            (P.D.lL - 1 + lFe P.D - sG + j)) q *
        Blocks.ext P.D.lT (fun p => P.rd (P.msg m)
          ⟨.sl, l, 2 * i + 1, (2 ^ (lFe P.D - sG) + k) * 2 ^ sG + q, p⟩) (fun j =>
          (gatedEAt P.fp ((tailF P).b5 e).2 ((tailF P).b6 e).2).r6
            (P.D.lL - 1 + lFe P.D - sG + sG + j)) :=
  ((late_gated P O e m).s6 l hl i hi k hk).trans (readAt_off _ _ _ _ _ _)

/-- The tensor u at the second product layer's point. -/
theorem late_uU6 {l i k : ℕ} (hl : l < 2) (hi : i < 2 ^ (P.D.lL - 1))
    (hk : k < 2 ^ (lFe P.D - sG)) :
    yL P Y fm e m
        ((gNamesAt P.fp (gReadsAt Y ιG)).uU6 l (2 * i + 1) (2 ^ (lFe P.D - sG) + k)) =
      ∑ q ∈ range (2 ^ sG), Blocks.eqN sG 0 (fun j =>
          (gatedEAt P.fp ((tailF P).b5 e).2 ((tailF P).b6 e).2).r6
            (P.D.lL - 1 + lFe P.D - sG + j)) q *
        Blocks.ext P.D.lT (fun p => P.rd (P.msg m)
          ⟨.up, l, 2 * i + 1, (2 ^ (lFe P.D - sG) + k) * 2 ^ sG + q, p⟩) (fun j =>
          (gatedEAt P.fp ((tailF P).b5 e).2 ((tailF P).b6 e).2).r6
            (P.D.lL - 1 + lFe P.D - sG + sG + j)) :=
  ((late_gated P O e m).u6 l hl i hi k hk).trans (readAt_off _ _ _ _ _ _)

end Gated

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.tables_uP
#print axioms OnBytes.Road.K4.tables_uR
#print axioms OnBytes.Road.K4.tables_uSel
#print axioms OnBytes.Road.K4.tables_uXi0
#print axioms OnBytes.Road.K4.tables_uXi
#print axioms OnBytes.Road.K4.readAt_off
#print axioms OnBytes.Road.K4.late_norms
#print axioms OnBytes.Road.K4.late_terms
#print axioms OnBytes.Road.K4.late_gated
#print axioms OnBytes.Road.K4.late_uP
#print axioms OnBytes.Road.K4.late_uR
#print axioms OnBytes.Road.K4.late_uSel
#print axioms OnBytes.Road.K4.late_uXi0
#print axioms OnBytes.Road.K4.late_uXi
#print axioms OnBytes.Road.K4.late_uS5
#print axioms OnBytes.Road.K4.late_uU5
#print axioms OnBytes.Road.K4.late_uS6
#print axioms OnBytes.Road.K4.late_uU6
