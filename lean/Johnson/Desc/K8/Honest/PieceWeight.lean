-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/PieceWeight.lean: THE SMALLNESS TEST: BEHIND THE ADDING, THE WEIGHT ON EACH
COLUMN OF A PIECE's VIRTUAL ROW OF THE DIGITS' ARRAY: INSIDE THE PIECE's COLUMNS THE BATCHING
ELEMENT TO THE NUMBER OF THE CLAIMS IN FRONT, TIMES THE PIECE's TERM (BY VALUE); OUTSIDE THEM THE
WORD 0: WHERE NO PLAIN CLAIM BUT THE CLAIM ON THE LOOKUP's KEY VECTORS BEARS ON THE ENTRY. A
definition and lemmas; none of the library's goals. On ledgers, lists of claims and plain data
(`Added8`, Johnson/Desc/K8/Honest/Added8.lean): no block, no prover; nothing on completeness,
soundness or hiding.

  `OffBut fr k8 bk k t r i`, `planeOff_iff`   of the plain claims none but number k bears on the
      entry. `PlaneOff` (Johnson/Desc/K8/Honest/PlanesWeight.lean) is the same sentence at the
      planes' array and its own number
  `offAt_piece`   under `apartB` (Johnson/Desc/K8/Honest/ApartOf.lean) and `piecesLaid`
      (PiecesLaid.lean): a piece's virtual row is none of those on which the ties and reads lay a
      weight
  `four8_rest_off`   the second to fourth claims of the list "K8.equations" name nothing of an array
      that is not the planes', where the form among them that the digits' lookup has heard names no
      entry
  `join_at_front`, `oneOn_join`   the claim behind the claims in front is `joinClaim`
      (JoinCoef.lean); from `OffBut` to `OneOn` (PlanesWeight.lean). The steps are those of
      `plane_claim`, `oneOn_plane` (PlanesWeight.lean)
  **`Added8.weight_piece`**, **`Added8.weight_beside`**   the two sentences of the title
By: `Added8.weight_one` (PlanesWeight.lean) · `join_coef_in`, `join_coef_out` (JoinCoef.lean) ·
`pair_row` (NamesOff.lean) · `apartB_iff` (ApartOf.lean) · `four8_zero` (DigitsLiveOf.lean) ·
`rowForm_ents`, `no_ent` (GoodOf.lean) · `word_of_val` (OkWeights.lean) · K9L.take_four
(Johnson/Desc/First/Batch/Law/K8Four.lean).
Limits. `Added8`, `OffBut`, what the lookup has heard, the two tests and "begins at column 0" are
premises.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K8.Honest.JoinCoef
import Johnson.Desc.K8.Honest.PlanesWeight
import Johnson.Desc.K8.Honest.ApartOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open OnBytes.Tie.Pv.Tail.Port

/-- Of the plain claims, none but number k bears on the entry. -/
def OffBut (fr k8 bk : List Claim) (k t r i : Nat) : Prop :=
  (∀ (j : Nat) (cl : Claim), (fr ++ k8.take 4)[j]? = some cl → j ≠ k → coefOn cl t r i = 0) ∧
    ∀ (j : Nat) (cl : Claim), bk[j]? = some cl → coefOn cl t r i = 0

/-- `PlaneOff` (PlanesWeight.lean) is `OffBut` at its own number and place. -/
theorem planeOff_iff (fr k8 bk : List Claim) (tl : HTailF2) (e x : Nat) :
    PlaneOff fr k8 bk tl e x ↔ OffBut fr k8 bk (fr.length + 1 + e) tl.ix.BZ e x := Iff.rfl

/-- A piece's virtual row is none of those on which the ties and reads lay a weight. -/
theorem offAt_piece (tl : HTailF2) (hA : apartB tl = true) (hL : piecesLaid tl = true)
    (x : Nat × OnBytes.Model.Piece) (hx : x ∈ joinPairs tl) : OffAt tl tl.ix.ZZ x.2.row := by
  obtain ⟨-, hr⟩ := pair_row tl hL x hx
  obtain ⟨-, ⟨u0, -⟩, ⟨u2, -⟩, hm⟩ := (apartB_iff tl).1 hA
  refine ⟨fun h => ?_, fun h => ?_, fun mu hmu h => (hm mu hmu).2.1 h.1, u0, u2⟩
  · have k := h.2
    unfold HTailF2.zzRowTies at k
    omega
  · have k := h.2
    unfold HTailF2.zzRowReads at k
    omega

/-- **The second to fourth claims of the list "K8.equations" name nothing of an array that is not
the planes'**: where the form among them that the digits' lookup has heard names no entry. -/
theorem four8_rest_off (tl : HTailF2) (g : Forest.Heard)
    (hl : g.leaves.start.ents.isEmpty = true) (t : Nat) (hB : tl.ix.BZ ≠ t) :
    ∀ cl ∈ (K9L.four8 tl g).drop 1, NamesNot t cl := by
  have bz : ∀ (row : Nat) (c : E) (w : Array E), ∀ u ∈ (#[Fo.bzRun tl row c w] : Array Run2),
      u.tree ≠ t := by
    intro row c w u hu
    obtain rfl : u = Fo.bzRun tl row c w := List.mem_singleton.1 (Array.mem_toList_iff.2 hu)
    exact hB
  intro cl hcl
  simp only [K9L.four8, List.drop_succ_cons, List.drop_zero, List.mem_cons, List.not_mem_nil,
    or_false] at hcl
  rcases hcl with rfl | rfl | rfl
  · refine ⟨fun x hx => ?_, bz _ _ _⟩
    obtain ⟨y, hy, -, -, -⟩ := rowForm_ents _ _ x (Array.mem_toList_iff.2 hx)
    exact absurd hy (no_ent _ hl y)
  · exact ⟨fun x hx => by simp [Aff.slot] at hx, bz _ _ _⟩
  · exact ⟨fun x hx => by simp [Aff.ofConst] at hx, bz _ _ _⟩

section
variable {tl tl' : HTailF2} {funs : Array HFun} {Y G F₁ F₂ : Fork} {fr k8 bk : List Claim}
  {n₀ : Nat}

/-- The claim behind the claims in front is the claim on the lookup's key vectors. -/
theorem join_at_front (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀) {g : Forest.Heard}
    (hg : tl.heard = some g) : (fr ++ k8.take 4)[fr.length]? = some (joinClaim tl g) := by
  obtain ⟨g', -, hg', h4, -⟩ := K9L.take_four A.eq
  obtain rfl : g' = g := Option.some.inj (hg'.symm.trans hg)
  rw [h4, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  exact four8_zero tl g'

/-- From "no other" and the claim's own coefficient to `OneOn`. -/
theorem oneOn_join (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀) {g : Forest.Heard}
    (hg : tl.heard = some g) (t r i : Nat) (hP : OffBut fr k8 bk fr.length t r i) :
    OneOn fr k8 bk t r i fr.length (coefOn (joinClaim tl g) t r i) := by
  refine ⟨fun j cl hj => ?_, hP.2⟩
  by_cases ej : j = fr.length
  · rw [if_pos ej]
    rw [ej, join_at_front A hg] at hj
    rw [Option.some.inj hj]
  · rw [if_neg ej]
    exact hP.1 j cl hj ej

/-- **THE WEIGHT ON A COLUMN OF A PIECE, IN ITS VIRTUAL ROW, BY VALUE**: the batching element to the
number of the claims in front, times the piece's term. -/
theorem Added8.weight_piece (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀) {g : Forest.Heard}
    (hg : tl.heard = some g) (hc : g.cEnd.ents.isEmpty = true) (hA : apartB tl = true)
    (hL : piecesLaid tl = true) (x : Nat × OnBytes.Model.Piece) (hx : x ∈ joinPairs tl) (cc : Nat)
    (hcc : cc < x.2.Cp) (h0 : ((Y.trees.getD tl.ix.ZZ {}).rows.getD x.2.row {}).L0 = 0)
    (hP : OffBut fr k8 bk fr.length tl.ix.ZZ x.2.row (x.2.c0 + cc)) :
    Reading.gl.val ((weightsOf G tl.ix.ZZ x.2.row).getD (x.2.c0 + cc) zeroE) =
      Reading.gl.val Y.theta ^ fr.length * joinTerm tl g x (x.2.c0 + cc) := by
  rw [A.weight_one tl.ix.ZZ x.2.row (x.2.c0 + cc) fr.length _ h0 (offAt_piece tl hA hL x hx)
    (by omega) (oneOn_join A hg _ _ _ hP), join_coef_in tl g hc hL x hx cc hcc]

/-- **OUTSIDE THE PIECE's COLUMNS, IN ITS VIRTUAL ROW: THE WORD 0.** -/
theorem Added8.weight_beside (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀) {g : Forest.Heard}
    (hg : tl.heard = some g) (hc : g.cEnd.ents.isEmpty = true) (hA : apartB tl = true)
    (hL : piecesLaid tl = true) (x : Nat × OnBytes.Model.Piece) (hx : x ∈ joinPairs tl) (i : Nat)
    (hi : ¬ (x.2.c0 ≤ i ∧ i < x.2.c0 + x.2.Cp))
    (h0 : ((Y.trees.getD tl.ix.ZZ {}).rows.getD x.2.row {}).L0 = 0)
    (hP : OffBut fr k8 bk fr.length tl.ix.ZZ x.2.row i) :
    (weightsOf G tl.ix.ZZ x.2.row).getD i zeroE = zeroE := by
  refine word_of_val A.core.2.2.2 rfl ?_
  rw [A.weight_one tl.ix.ZZ x.2.row i fr.length _ h0 (offAt_piece tl hA hL x hx) (by omega)
    (oneOn_join A hg _ _ _ hP), join_coef_out tl g hc hL x hx i hi, mul_zero, Reading.gl.zero]

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.planeOff_iff
#print axioms VerifiableInference.Desc.First.K8.Honest.offAt_piece
#print axioms VerifiableInference.Desc.First.K8.Honest.four8_rest_off
#print axioms VerifiableInference.Desc.First.K8.Honest.join_at_front
#print axioms VerifiableInference.Desc.First.K8.Honest.oneOn_join
#print axioms VerifiableInference.Desc.First.K8.Honest.Added8.weight_piece
#print axioms VerifiableInference.Desc.First.K8.Honest.Added8.weight_beside
