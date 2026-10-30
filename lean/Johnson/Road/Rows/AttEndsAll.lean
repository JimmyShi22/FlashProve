-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/AttEndsAll.lean: the statements of Johnson/Road/Rows/AttEnds14.lean, used for all
pairs of a sumcheck; and two tools on the relation of an attention segment.

Main theorems.
 - pair_of_piece: under PiecesAll the pair of piece b has the number b.
 - score_ends, product_ends, below_ends: from the public premises and the claims on the end values
   of all pieces to EndsAt (Johnson/Road/Rows/AttBetween.lean).
 - rfraw_down: the relation over a ring into which a ring F maps one to one gives the relation
   over F.
 - cells_cast: the cells of integer matrices, read in a field.

What is not claimed. That the premises hold of a run. Nothing is said about probabilities or about
hiding. The program does not import this file.


-/
import Johnson.Road.Rows.AttBetween
import Johnson.Road.Rows.AttEnds14Below

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open Cb.Pv.Att

open Finset
open OnBytes.Model (Reading World Aff Fork HTailF2)
open OnBytes.Attention (Heard Score ScoreTables PW Seg Shape)
open Inst.Model.AttSeg (Calls Pub Step KSc Reg rv sumPhi Idn idnVal keyVec lutSet lut castT RFraw
  Raw Dim)

variable {K : Type} [Field K]

/-! ## Pieces and pairs -/

/-- Under PiecesAll there is a piece number b for each pair b; its head is below HA and its pair has
the number b. -/
theorem pair_of_piece {S : Shape} {pw : Array PW} (P : PiecesAll S pw) {b : ℕ} (hb : b < S.NP) :
    ∃ w, pw[b]? = some w ∧ w.a < S.HA ∧ w.lam * S.HA + w.a = b := by
  have hs : b < pw.size := by rw [P.1]; exact hb
  have hpos : 0 < S.HA := by
    rcases Nat.eq_zero_or_pos S.HA with h0 | h0
    · have e : S.NP = 0 := by
        show S.Lam * S.HA = 0
        rw [h0, Nat.mul_zero]
      omega
    · exact h0
  refine ⟨pw[b], Array.getElem?_eq_getElem hs, ?_, ?_⟩
  · rw [(P.2 b hb _ (Array.getElem?_eq_getElem hs)).2]
    exact Nat.mod_lt _ hpos
  · rw [(P.2 b hb _ (Array.getElem?_eq_getElem hs)).1,
      (P.2 b hb _ (Array.getElem?_eq_getElem hs)).2]
    exact Nat.div_add_mod' b S.HA

section Ends

variable {ρ : Reading K} {W : World K} {tl : HTailF2} {K3 : ℕ} {M : Mats K} {h : Heard}
  {lid : ℕ} {cf : Attention.Cfg} {fs : Model.Forest.Shape} {C : Calls} {p : Pub K}

/-- The end values of a unit of the scores, for all pairs. -/
theorem score_ends {seg : Seg} {st : Step} (E : ScoreEnd seg st)
    (A : AttAt ρ W tl K3 M h lid cf fs) {k : Score} {tb : ScoreTables}
    (P : ScorePub ρ tl h C p seg k tb) (Gv : ScoreGiven ρ W K3 h k tb) :
    EndsAt ρ W h M C p k.sc st := by
  intro b hb
  obtain ⟨w, hw, ha, e⟩ := pair_of_piece P.pairs hb
  obtain ⟨q, kx, F, F', G, G', c, c1, c', c1', g1, g2, g3, g4, g5, g6⟩ := Gv b w hw
  have r := E K ρ W tl K3 M h lid cf fs C p k tb b w q kx F F' G G' c c1 c' c1' A g1 g2 P.isSeg P.r
    P.zi P.zj ha P.vi P.vj P.tQ P.tK g3 g4 g5 g6
  rw [e] at r
  exact r

/-- The end values of the denominator times the output, for all pairs. -/
theorem product_ends (A : AttAt ρ W tl K3 M h lid cf fs) (P : ProductPub ρ tl h C p)
    (Gv : ProductGiven ρ W K3 h) : EndsAt ρ W h M C p h.d.scE .s8 := by
  intro b hb
  obtain ⟨w, hw, ha, e⟩ := pair_of_piece P.pairs hb
  obtain ⟨z, o, F, F', G, G', c, c1, c', c1', g1, g2, g3, g4, g5, g6⟩ := Gv b w hw
  have r := productEnd K ρ W tl K3 M h lid cf fs C p b w z o F F' G G' c c1 c' c1' A g1 g2 P.r
    P.zc ha P.vn P.hE P.qO g3 g4 g5 g6
  rw [e] at r
  exact r

/-- The end values of the value product below the diagonal, for all pairs. -/
theorem below_ends (A : AttAt ρ W tl K3 M h lid cf fs) (P : ProductPub ρ tl h C p)
    (Q : BelowPub ρ tl h C p) (Gv : BelowGiven ρ W K3 h) :
    EndsAt ρ W h M C p h.d.vpm .s11 := by
  intro b hb
  obtain ⟨w, hw, ha, e⟩ := pair_of_piece P.pairs hb
  obtain ⟨p3, p4, v, F, F', F'', G, G', G'', c, c1, c', c1', c'', c1'', g1, g2, g3, g4, g5, g6,
    g7, g8⟩ := Gv b w hw
  have r := valueBelowEnd K ρ W tl K3 M h lid cf fs C p b w p3 p4 v F F' F'' G G' G'' c c1 c' c1'
    c'' c1'' A g1 g2 g3 Q.r Q.zi P.zc ha Q.ptM Q.wJv Q.vi P.vn Q.gam Q.tVM Q.qVM g4 g5 g6 g7 g8
  rw [e] at r
  exact r

end Ends

/-! ## From one ring to another -/

/-- The relation over a ring R gives the relation over a ring F that maps into R one to one. -/
theorem rfraw_down [scl : Inst.Model.Scl] (D : Dim) (tb : Inst.Model.Tables) {F R : Type}
    [CommRing F] [CommRing R] (φ : F →+* R) (hφ : Function.Injective φ) {t : Raw → ℤ}
    (H : RFraw D tb R t) : RFraw D tb F t := by
  obtain ⟨h1, h2, h3⟩ := H
  refine ⟨h1, fun c X hX => ?_, fun j hj => hφ ?_⟩
  · obtain ⟨ι, hι, he⟩ := h2 c X hX
    refine ⟨ι, hι, hφ ?_⟩
    rw [Inst.Model.AttSeg.key_cast, map_intCast, map_intCast, ← he,
      Inst.Model.AttSeg.key_cast]
  · rw [Inst.Model.AttSeg.idn_cast, map_intCast, map_zero, ← Inst.Model.AttSeg.idn_cast]
    exact h3 j hj

/-- The cells of the integer matrices, read in the field. -/
theorem cells_cast (S : Shape) (Z : L5.Zs) :
    cellsK S (fun a r c => ((Z a r c : ℤ) : K)) = (castT (L5.cellsA S Z) : Raw → K) := rfl

end OnBytes.Road.Rows
