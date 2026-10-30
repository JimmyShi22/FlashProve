-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/SecondOpen.lean: THE SMALLNESS TEST: `SecondEqs`
(Johnson/Desc/K8/Honest/SecondParts.lean: what must never fail in the verifier's two tests on
weights by a second computation), WHOLE, AT THE DATA AND THE LEDGER BEHIND THE ADDING. Definitions
and lemmas; none of the library's goals. On ledgers, lists of claims and plain data (`Added8`,
Johnson/Desc/K8/Honest/Added8.lean): no block, no prover; nothing on completeness, soundness or
hiding. An assembly.

  `plainOff_of_others`, `offBut_of_others`   `PlainOff` (Added8.lean) and `OffBut` at the number of
      the claims in front (PieceWeight.lean) come down to the list's own first claims and to
      `OthersOff` (Johnson/Desc/K8/Honest/PlanesOff.lean). `plainOff_reads`, `planeOff_of`
      (PlanesOff.lean) are the like at the reads' row and at the planes' array; their steps are
      taken over
  `SecondFront tl F`   what both halves ask in front of the batching: five tests and conditions on
      public numbers and on the drawn matrix; every virtual row begins at column 0; each matrix's
      array has a virtual row 0; the second computation's number of blocks is the data's; the two
      forms that the digits' lookup has heard name no entry; `PieceFront` (PieceWhole.lean) at every
      expected piece
  `OthersApart tl fr bk`   no claim of another run names the digits' array or a matrix's array of
      symbols (`NamesNot`, NamesOff.lean)
  **`Added8.secondEqs`**   under `Added8` at the number of the claims in front, `SecondFront`,
      `OthersApart` and two conditions at the data and the ledger behind the adding: `SecondEqs`
By: `Added8.pieceEqs` (PieceWhole.lean) · `Added8.tieEqs` (TieWhole.lean) · `eq_join_bits`
(Johnson/Desc/K8/Honest/PlanesFront.lean) · `four8_off`, `coefOn_off`, `namesNot_at` (NamesOff.lean)
· `four8_rest_off` (PieceWeight.lean) · `apartB_iff` (ApartOf.lean) · `wants_same`,
`hasRow_of_shape` (SecondFew.lean) · `L0_of_shape`, `shape_of_frame` (FallDraw.lean) · K9L.take_four
(Johnson/Desc/First/Batch/Law/K8Four.lean) · eq_same
(Johnson/Desc/First/TailClaims/EquationsCover.lean).
Limits. EVERY PREMISE IS SHOWN OF NO STATE HERE. No challenge is named; `Added8` and the two last
premises speak of the ledgers and the data behind the batching's draw.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K8.Honest.PieceWhole
import Johnson.Desc.K8.Honest.TieBehind
import Johnson.Desc.K8.Honest.PlanesOff
import Johnson.Desc.K8.Honest.PlanesFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open Fo (HasRow)
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open OnBytes.Tie.Pv.Tail.Port

section
variable {tl tl' : HTailF2} {funs : Array HFun} {Y G F₁ F₂ : Fork} {fr k8 bk : List Claim}
  {n₀ : Nat}

/-- `PlainOff` comes down to the list's first four and the other runs' claims. -/
theorem plainOff_of_others (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀) {g : Forest.Heard}
    (hg : tl.heard = some g) (t r i : Nat) (h4 : ∀ cl ∈ K9L.four8 tl g, coefOn cl t r i = 0)
    (hO : OthersOff fr bk t r i) : PlainOff fr k8 bk t r i := by
  obtain ⟨g', -, hg', e4, -⟩ := K9L.take_four A.eq
  obtain rfl : g' = g := Option.some.inj (hg'.symm.trans hg)
  refine ⟨fun j cl hj => ?_, fun j cl hj => hO.2 cl (List.mem_of_getElem? hj)⟩
  rcases List.mem_append.1 (List.mem_of_getElem? hj) with h | h
  · exact hO.1 cl h
  · exact h4 cl (e4 ▸ h)

/-- `OffBut` at the number of the claims in front comes down to the list's second to fourth and
the other runs' claims. -/
theorem offBut_of_others (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀) {g : Forest.Heard}
    (hg : tl.heard = some g) (t r i : Nat)
    (h3 : ∀ cl ∈ (K9L.four8 tl g).drop 1, coefOn cl t r i = 0) (hO : OthersOff fr bk t r i) :
    OffBut fr k8 bk fr.length t r i := by
  obtain ⟨g', -, hg', e4, -⟩ := K9L.take_four A.eq
  obtain rfl : g' = g := Option.some.inj (hg'.symm.trans hg)
  refine ⟨fun j cl hj hne => ?_, fun j cl hj => hO.2 cl (List.mem_of_getElem? hj)⟩
  by_cases hlt : j < fr.length
  · rw [List.getElem?_append_left hlt] at hj
    exact hO.1 cl (List.mem_of_getElem? hj)
  · rw [List.getElem?_append_right (by omega), e4] at hj
    refine h3 cl ?_
    obtain ⟨k, hk⟩ : ∃ k, j - fr.length = k + 1 := ⟨j - fr.length - 1, by omega⟩
    rw [hk] at hj
    have hd : ((K9L.four8 tl g').drop 1)[k]? = some cl := by
      rw [List.getElem?_drop, Nat.add_comm]
      exact hj
    exact List.mem_of_getElem? hd

end

/-- **What both halves ask, on the data, the ledger and what the digits' lookup has heard, in front
of the batching.** -/
structure SecondFront (tl : HTailF2) (F : Fork) : Prop where
  laid : tiesLaid tl = true
  sym : symbolsLaid tl = true
  front : TieFront tl
  apart : apartB tl = true
  pieces : piecesLaid tl = true
  zero : ∀ t r, ((F.trees.getD t {}).rows.getD r {}).L0 = 0
  row : ∀ mu, mu < tl.NM → HasRow F (tl.gtTree.getD mu 0) 0
  blocks : ∀ nbW W, tl.wants = some (nbW, W) → nbW = tl.zzBlocks
  cEnd : ∀ g, tl.heard = some g → g.cEnd.ents.isEmpty = true
  leaves : ∀ g, tl.heard = some g → g.leaves.start.ents.isEmpty = true
  want : ∀ g nbW W, tl.heard = some g → tl.wants = some (nbW, W) → ∀ w ∈ W, PieceFront tl g w

/-- No claim of another run names the digits' array or a matrix's array of symbols. -/
def OthersApart (tl : HTailF2) (fr bk : List Claim) : Prop :=
  ∀ cl, cl ∈ fr ∨ cl ∈ bk →
    NamesNot tl.ix.ZZ cl ∧ ∀ mu, mu < tl.NM → NamesNot (tl.gtTree.getD mu 0) cl

/-- **BOTH HALVES, ON `Added8` AT THE NUMBER OF THE CLAIMS IN FRONT: `SecondEqs` WHOLE.** -/
theorem Added8.secondEqs {tl tl' : HTailF2} {funs : Array HFun} {Y G F₁ F₂ F : Fork}
    {fr k8 bk : List Claim} (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk fr.length)
    (hsh : shapeOf Y.trees = shapeOf F.trees) (hS : SecondFront tl F)
    (hO : OthersApart tl fr bk) (T : Fo.CoefOK tl' G)
    (hR : ∀ nbW W, tl.wants = some (nbW, W) → ∀ w ∈ W,
      w.r0 + w.Rp ≤ (G.trees.getD tl.ix.ZZ {}).R) :
    SecondEqs tl' G := by
  intro g jo nbW W hg hj hW
  have eH : tl'.heard = tl.heard :=
    eq_same (·.heard) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl)
  have eN : tl'.NM = tl.NM :=
    eq_same (·.NM) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl)
  have eτ : tl'.tau = tl.tau :=
    eq_same (·.tau) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl)
  have ez : tl'.mz = tl.mz :=
    eq_same (·.mz) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl)
  rw [eH] at hg
  rw [wants_same eτ ez] at hW
  obtain ⟨g', hg', hj', -⟩ := eq_join_bits A.eq
  obtain rfl : fr.length = jo := Option.some.inj (hj'.symm.trans hj)
  have hc := hS.cEnd g hg
  have hl := hS.leaves g hg
  obtain ⟨aZB, -, -, aM⟩ := (apartB_iff tl).1 hS.apart
  have hzY : ∀ t r, ((Y.trees.getD t {}).rows.getD r {}).L0 = 0 := fun t r => by
    rw [L0_of_shape, hsh, ← L0_of_shape]
    exact hS.zero t r
  have shG : shapeOf G.trees = shapeOf F.trees := (shape_of_frame _ _ A.core.2.2.1).trans hsh
  have oth : ∀ t r i, (∀ cl, cl ∈ fr ∨ cl ∈ bk → NamesNot t cl) → OthersOff fr bk t r i :=
    fun t r i h => ⟨fun cl hcl => coefOn_off (namesNot_at (h cl (Or.inl hcl)) r) i,
      fun cl hcl => coefOn_off (namesNot_at (h cl (Or.inr hcl)) r) i⟩
  refine ⟨fun w hw => ?_, fun mu hmu => ?_⟩
  · exact A.pieceEqs hg hc hS.apart hS.pieces w (hS.want g nbW W hg hW w hw) T (hR nbW W hW w hw)
      (hzY _ _) fun i => offBut_of_others A hg _ _ _
        (fun cl hcl => coefOn_off (namesNot_at
          (four8_rest_off tl g hl tl.ix.ZZ (fun h => aZB h.symm) cl hcl) _) i)
        (oth _ _ _ fun cl hcl => (hO cl hcl).1)
  · refine A.tieEqs g nbW (hS.blocks nbW W hW) hS.laid hS.sym hS.front hzY
      (fun nu hnu => hasRow_of_shape shG (hS.row nu hnu))
      (fun nu hnu i _ pl _ => plainOff_of_others A hg _ _ _
        (fun cl hcl => coefOn_off (four8_off tl g hc hl hS.pieces tl.ix.ZZ tl.zzRowTies
          (fun h => aZB h.symm) (fun h => by
            have k := h.2
            unfold HTailF2.zzRowTies at k
            omega) cl hcl) _)
        (oth _ _ _ fun cl hcl => (hO cl hcl).1))
      (fun nu hnu c _ => plainOff_of_others A hg _ _ _
        (fun cl hcl => coefOn_off (four8_off tl g hc hl hS.pieces (tl.gtTree.getD nu 0) 0
          (fun h => (aM nu hnu).1 h.symm) (fun h => (aM nu hnu).2.1 h.1.symm) cl hcl) _)
        (oth _ _ _ fun cl hcl => (hO cl hcl).2 nu hnu))
      mu (eN ▸ hmu)

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.plainOff_of_others
#print axioms VerifiableInference.Desc.First.K8.Honest.offBut_of_others
#print axioms VerifiableInference.Desc.First.K8.Honest.Added8.secondEqs
