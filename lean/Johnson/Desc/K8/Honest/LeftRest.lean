-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/LeftRest.lean: THE SMALLNESS TEST: THE THREE TESTS ON WHAT THE ADDING HAS
LEFT THAT READ NO WEIGHT's VALUE (OnBytes/Model/Tail.lean, "tileSelfTestF"): the clause on the
digits' array's number of virtual rows, the lookup's public numbers (`forestHeld`) and the two calls
(`callHeld`) · that the calls' pieces tile the digits' array (`piecesTile`) · the calls' points and
weights (`pointsHeld`): BEHIND THE ADDING, FROM SENTENCES IN FRONT. `forestHeld`, `callHeld` and
`pointsHeld` read the plan's numbers and what the digits' lookup has heard, and no ledger: a yes of
"K8.equations" leaves what they read, SO THEY ARE MOVED TO THE DATA IN FRONT, WORD FOR WORD, NOT
PAID. What a yes of `piecesTile` means is the library's (`piecesTile_iff`,
Johnson/Desc/First/TailClaims/AgainMeans.lean; `piecesTile_eq`, AgainAgrees.lean). None of the
library's goals.

  `name_of_frame`, `coef_name`   an array's name, off the arrays' frame; the step that lays the
                   rows' weights leaves it
  `Added8.forest_stays`, `Added8.call_stays`, `Added8.points_stays`   Added8 ⊢ each of the three
                   tests says at the data behind what it says at the data in front (`eq_same`,
                   Johnson/Desc/First/TailClaims/EquationsCover.lean)
  `Added8.wants_stays`, `Added8.heard_stays`   Added8 ⊢ the expected pieces and what was heard are
                   the same at both (`wants_same`, Johnson/Desc/K8/Honest/SecondFew.lean)
  `DigitsFront tl F`   at the ledger in front the digits' array has the name "ZZ", tau rows, 2 mz
                   columns and 2 * tl.zzBlocks + 2 virtual rows
  **`Added8.firstClause`**   Added8 · the arrays behind the runs are F's, filled · DigitsFront · nbW
                   = tl.zzBlocks · forestHeld and both callHeld AT THE DATA IN FRONT ⊢ the clause,
                   in the verifier's own letters
  `WantPub tl w`   of one expected piece, on public numbers: the plan's piece under its call and
                   index is one of the calls' pieces, lies in the digits' array and has the expected
                   virtual row, rows and columns; these lie in the array; the array has that virtual
                   row
  **`Added8.tile`**   Added8 · the arrays behind the runs are F's, filled · DigitsFront · what the
                   laws on the declared weights ask, at the data and the ledger behind (Fo.CoefOK) ·
                   WantPub at every expected piece · no two expected pieces meet · their areas add
                   up to tau * (2 mz) ⊢ tl'.piecesTile (coefBody tl' g G) W = true
By: `piece_coef` (Johnson/Desc/K8/Honest/PieceWhole.lean) · `full_of_fill`, `fill_at`
(BitsFilled.lean) · `look_at`, `lsize_of_frame` (PlanesShape.lean) · `weights_coefBody`
(BehindWeight.lean) · `K9L.coef_looks`, `K9L.fill_looks`, `LinkJoin.looks_of_frame`, `coefBody_inv`,
`Fo.tree_onRow` (the library's).
Limits. IMPLICATIONS. NOTHING IS PAID HERE BUT TWO OF `piecesTile`'s TEN CLAUSES A PIECE: the
numbers of the row weights and of the column weights of the piece's virtual row (the first under
Fo.CoefOK). ALL ELSE IS MOVED TO THE DATA AND THE LEDGER IN FRONT OR CARRIED OVER: `Added8`,
`DigitsFront`, `WantPub`, Fo.CoefOK, the three tests in front and the two sentences on the list of
expected pieces ARE PAID BY NOBODY HERE. Fo.CoefOK stands at the data and the ledger behind the
adding (`Added8.coefOK`, Johnson/Desc/K8/Honest/SecondAtPlain.lean, carries it there from in front:
not called here). The list of expected pieces is a letter: that it is the list which `wants`
computes is not said here; that list is a function of tau and mz alone, so the two sentences on it,
and the last three fields of `WantPub`, are arithmetic: not done here (`wants_tile`,
Johnson/Desc/K8/Honest/WantsTile.lean, does it where tau is not 0). PAYERS IN SIGHT, NOT CALLED: of
`WantPub`: the array, the virtual row and the columns are what the public test `piecesLaid` compares
(PiecesLaid.lean); the rows are not. ASKED TWICE WHERE BOTH STAND, NOT TWO OBLIGATIONS: six of
`WantPub`'s sentences stand in `PieceFront` too (PieceWhole.lean), the five equations the other way
round (`wantPub_of_front`, WantsTile.lean) · `DigitsFront`'s number of columns is a premise of
`fiveHeld_at_link` (TiesAtLink.lean), and its number of virtual rows yields that the array has the
ties' row.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.TiesAtLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open OnBytes.Tie.Pv.Tail.Port

/-- An array's name, off the arrays' frame. -/
theorem name_of_frame (A : Array HTree) (t : Nat) :
    (A.getD t {}).name = ((treesFrame A).getD t (HTree.frame {})).1.name := by
  simp only [treesFrame, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases A[t]? <;> rfl

/-- The step that lays the rows' weights leaves the arrays' names. -/
theorem coef_name (tl : HTailF2) (g : Forest.Heard) (F : Fork) (t : Nat) :
    ((coefBody tl g F).trees.getD t {}).name = (F.trees.getD t {}).name :=
  coefBody_inv (fun r => (r.trees.getD t {}).name = (F.trees.getD t {}).name)
    (fun r t' r' f h => by
      show ((HTailF2.onRow r t' r' f).trees.getD t {}).name = _
      rw [Fo.tree_onRow]
      split <;> exact h) tl g F rfl

/-- The digits' array at the ledger in front. -/
structure DigitsFront (tl : HTailF2) (F : Fork) : Prop where
  name : (F.trees.getD tl.ix.ZZ {}).name = "ZZ"
  R : (F.trees.getD tl.ix.ZZ {}).R = tl.tau
  K : (F.trees.getD tl.ix.ZZ {}).K = 2 * tl.mz
  rows : (F.trees.getD tl.ix.ZZ {}).rows.size = 2 * tl.zzBlocks + 2

/-- Of one expected piece, on public numbers. -/
structure WantPub (tl : HTailF2) (w : Want) : Prop where
  mem : (w.call, (tl.zOf w.call).pieces.getD w.i {}) ∈ joinPairs tl
  tree : ((tl.zOf w.call).pieces.getD w.i {}).tree = tl.ix.ZZ
  row : ((tl.zOf w.call).pieces.getD w.i {}).row = w.row
  r0 : ((tl.zOf w.call).pieces.getD w.i {}).r0 = w.r0
  Rp : ((tl.zOf w.call).pieces.getD w.i {}).Rp = w.Rp
  c0 : ((tl.zOf w.call).pieces.getD w.i {}).c0 = w.c0
  Cp : ((tl.zOf w.call).pieces.getD w.i {}).Cp = w.Cp
  inR : w.r0 + w.Rp ≤ tl.tau
  inK : w.c0 + w.Cp ≤ 2 * tl.mz
  has : w.row < 2 * tl.zzBlocks + 2

section
variable {tl tl' : HTailF2} {funs : Array HFun} {Y G F₁ F₂ F : Fork} {fr k8 bk : List Claim}
  {n₀ : Nat}

/-- The test on the lookup's public numbers reads nothing that the run turns. -/
theorem Added8.forest_stays (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀) (g : Forest.Heard) :
    tl'.forestHeld g = tl.forestHeld g :=
  eq_same (fun t : HTailF2 => t.forestHeld g) A.eq (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ _ _ => rfl)

/-- Nor does the test on a call. -/
theorem Added8.call_stays (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀) (g : Forest.Heard)
    (nbW q : Nat) : tl'.callHeld g nbW q = tl.callHeld g nbW q :=
  eq_same (fun t : HTailF2 => t.callHeld g nbW q) A.eq (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ _ _ => rfl)

/-- Nor the test on the calls' points and weights. -/
theorem Added8.points_stays (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀) (g : Forest.Heard) :
    tl'.pointsHeld g = tl.pointsHeld g :=
  eq_same (fun t : HTailF2 => t.pointsHeld g) A.eq (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ _ _ => rfl)

/-- The expected pieces are the same. -/
theorem Added8.wants_stays (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀) :
    tl'.wants = tl.wants :=
  wants_same (eq_same (·.tau) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ _ => rfl))
    (eq_same (·.mz) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ _ => rfl))

/-- What the digits' lookup has heard is the same. -/
theorem Added8.heard_stays (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀) :
    tl'.heard = tl.heard :=
  eq_same (·.heard) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ _ => rfl)

/-- **THE CLAUSE ON THE NUMBER OF VIRTUAL ROWS, THE LOOKUP's NUMBERS AND THE TWO CALLS.** -/
theorem Added8.firstClause (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀) (g : Forest.Heard)
    (T : Tail2) (hYt : Y.trees = (t2FillL F T).trees) (D : DigitsFront tl F)
    (nbW : Nat) (hn : nbW = tl.zzBlocks) (hf : tl.forestHeld g = true)
    (hc : [0, 1].all (tl.callHeld g nbW) = true) :
    (((coefBody tl' g G).trees.getD tl'.ix.ZZ {}).rows.size == 2 * nbW + 2 && tl'.forestHeld g &&
      [0, 1].all (tl'.callHeld g nbW)) = true := by
  obtain ⟨-, -, hfr, -⟩ := A.core
  have eIx : tl'.ix = tl.ix :=
    eq_same (·.ix) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ _ => rfl)
  have lk : LinkJoin.look ((coefBody tl' g G).trees.getD tl.ix.ZZ {}) =
      LinkJoin.look (F.trees.getD tl.ix.ZZ {}) :=
    ((look_at (K9L.coef_looks tl' g G) _).trans
      (look_at (LinkJoin.looks_of_frame _ _ hfr) _)).trans (by
        rw [hYt]
        exact look_at (K9L.fill_looks F T) _)
  have hr : ((coefBody tl' g G).trees.getD tl'.ix.ZZ {}).rows.size = 2 * nbW + 2 := by
    rw [eIx, hn]
    exact (congrArg (·.2.2.2) lk).trans D.rows
  have ec : tl'.callHeld g nbW = tl.callHeld g nbW := funext (A.call_stays g nbW)
  simp only [Bool.and_eq_true, beq_iff_eq]
  exact ⟨⟨hr, (A.forest_stays g).trans hf⟩, by rw [ec]; exact hc⟩

/-- **THE CALLS' PIECES TILE THE DIGITS' ARRAY, BEHIND THE ADDING.** -/
theorem Added8.tile (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀) (g : Forest.Heard)
    (W : List Want) (T : Tail2) (hYt : Y.trees = (t2FillL F T).trees)
    (hT : T.nt.size = F.trees.size) (D : DigitsFront tl F) (C : Fo.CoefOK tl' G)
    (hW : ∀ w ∈ W, WantPub tl w) (hpair : W.Pairwise fun w x => ¬ TailClaims.Meets w x)
    (harea : W.foldl (fun s w => s + w.Rp * w.Cp) 0 = tl.tau * (2 * tl.mz)) :
    tl'.piecesTile (coefBody tl' g G) W = true := by
  obtain ⟨-, -, hfr, -⟩ := A.core
  have eIx : tl'.ix = tl.ix :=
    eq_same (·.ix) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ _ => rfl)
  have eTau : tl'.tau = tl.tau :=
    eq_same (·.tau) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ _ => rfl)
  have eMz : tl'.mz = tl.mz :=
    eq_same (·.mz) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ _ => rfl)
  have eZ : ∀ q, tl'.zOf q = tl.zOf q := fun q =>
    eq_same (fun t : HTailF2 => t.zOf q) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ _ => rfl)
  have eJ : joinPairs tl' = joinPairs tl :=
    eq_same (fun t : HTailF2 => joinPairs t) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ _ => rfl)
  have h0 : 0 < (F.trees.getD tl.ix.ZZ {}).rows.size := by
    rw [D.rows]
    omega
  have hZ : tl.ix.ZZ < T.nt.size := by
    rw [hT]
    exact (hasRow_of_rows rfl h0).1
  have lkG : LinkJoin.look (G.trees.getD tl.ix.ZZ {}) =
      LinkJoin.look (F.trees.getD tl.ix.ZZ {}) :=
    (look_at (LinkJoin.looks_of_frame _ _ hfr) _).trans (by
      rw [hYt]
      exact look_at (K9L.fill_looks F T) _)
  have lk : LinkJoin.look ((coefBody tl' g G).trees.getD tl.ix.ZZ {}) =
      LinkJoin.look (F.trees.getD tl.ix.ZZ {}) :=
    (look_at (K9L.coef_looks tl' g G) _).trans lkG
  have nm : ((coefBody tl' g G).trees.getD tl.ix.ZZ {}).name = "ZZ" := by
    rw [coef_name, name_of_frame, hfr, ← name_of_frame, hYt]
    exact (congrArg (·.name) ((fill_at F.trees tl.ix.ZZ T.nt.size).trans (if_pos hZ))).trans
      D.name
  have hR : ((coefBody tl' g G).trees.getD tl.ix.ZZ {}).R = tl.tau :=
    (congrArg (·.2.1) lk).trans D.R
  have hK : ((coefBody tl' g G).trees.getD tl.ix.ZZ {}).K = 2 * tl.mz :=
    (congrArg (·.2.2.1) lk).trans D.K
  have h := (piecesTile_iff tl' (coefBody tl' g G) W).2 (by
    dsimp only
    rw [eIx, eTau, eMz, hR, hK]
    refine ⟨nm, rfl, rfl, hpair, harea, fun w hw => ?_⟩
    have P := hW w hw
    rw [eZ w.call]
    refine ⟨P.tree, P.row, P.r0, P.Rp, P.c0, P.Cp, P.inR, P.inK, ?_, ?_⟩
    · have hx : (w.call, (tl'.zOf w.call).pieces.getD w.i {}) ∈ joinPairs tl' := by
        rw [eJ, eZ]
        exact P.mem
      have hc := piece_coef tl' g G C _ hx
      dsimp only at hc
      rw [eZ w.call, P.tree, P.row] at hc
      rw [hc]
      unfold Fo.pieceW
      rw [Array.size_map, Array.size_range]
      exact (congrArg (·.2.1) lkG).trans D.R
    · have e1 : (((coefBody tl' g G).trees.getD tl.ix.ZZ {}).rows.getD w.row {}).L =
          weightsOf G tl.ix.ZZ w.row := weights_coefBody tl' g G _ _
      rw [e1]
      show ((G.trees.getD tl.ix.ZZ {}).rows.getD w.row {}).L.size = _
      rw [lsize_of_frame, hfr, ← lsize_of_frame]
      exact (full_of_fill T hZ (by rw [D.rows]; exact P.has) hYt).trans D.K)
  rw [piecesTile_eq] at h
  exact h

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.name_of_frame
#print axioms VerifiableInference.Desc.First.K8.Honest.coef_name
#print axioms VerifiableInference.Desc.First.K8.Honest.Added8.forest_stays
#print axioms VerifiableInference.Desc.First.K8.Honest.Added8.call_stays
#print axioms VerifiableInference.Desc.First.K8.Honest.Added8.points_stays
#print axioms VerifiableInference.Desc.First.K8.Honest.Added8.wants_stays
#print axioms VerifiableInference.Desc.First.K8.Honest.Added8.heard_stays
#print axioms VerifiableInference.Desc.First.K8.Honest.Added8.firstClause
#print axioms VerifiableInference.Desc.First.K8.Honest.Added8.tile
