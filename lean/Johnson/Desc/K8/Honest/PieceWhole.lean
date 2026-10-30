-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/PieceWhole.lean: THE SMALLNESS TEST: THE PIECES' HALF OF WHAT MUST NEVER FAIL
IN THE VERIFIER's TWO TESTS ON WEIGHTS BY A SECOND COMPUTATION (`PieceEqs`, in the first conjunct of
`SecondEqs`: Johnson/Desc/K8/Honest/SecondParts.lean), AT ONE EXPECTED PIECE, WHOLE, BEHIND THE
ADDING: WHERE NO PLAIN CLAIM BUT THE CLAIM ON THE LOOKUP's KEY VECTORS BEARS ON THE PIECE's VIRTUAL
ROW. A definition and lemmas; none of the library's goals. On ledgers, lists of claims and plain
data (`Added8`, Johnson/Desc/K8/Honest/Added8.lean): no block, no prover; nothing on completeness,
soundness or hiding. An assembly.

  `joinPairs_all`, `pieceW_in`, `pieceW_out`, `piece_coef`   the two lists of the calls' pieces are
      one; an entry of the declared weights of a piece's virtual row (Fo.pieceW,
      OnBytes/Tie/Pv/Lookup/Ends/FoCoef.lean), AS A WORD, inside and outside the piece's rows
      (Fo.pieceW_read, OnBytes/Tie/Pv/Lookup/Ends/FoTailLaw.lean, has its value); the library's law
      on these weights, at the ledger as the tests read it
  `PieceFront tl g w`   what is asked of one expected piece, in front of the batching: the plan's
      piece under its call and index is one of the calls' pieces and has its virtual row, rows and
      columns; it has a column; Fo.PieceOK (OnBytes/Tie/Pv/Lookup/Ends/FoTailKf.lean); the call's
      point has the call's number of coordinates; a bound; the lookup's weight of the call is the
      second computation's
  **`Added8.piece_cell`**   at every cell of the piece: the product of the weight on its row and the
      weight on its column is what the second computation expects, as words
  **`Added8.pieceEqs`**   all seven parts of `PieceEqs`, at the data behind and at the ledger behind
      the step that lays the rows' weights, at the batching element to the number of the claims in
      front
By: `Added8.weight_piece`, `Added8.weight_beside` (Johnson/Desc/K8/Honest/PieceWeight.lean) ·
`joinTerm_in` (JoinCoef.lean) · `piece_factor_ok` (EqFactor.lean) · `eqAt_plain` (EqRunPlain.lean) ·
`kappa_val` (SecondNz.lean) · `weights_coefBody` (BehindWeight.lean) · Fo.CoefOK.pieceW
(OnBytes/Tie/Pv/Lookup/Ends/FoTailPlanes.lean) · ProdV.gl_inj (Johnson/Desc/First/ProdV/Drawn.lean)
· Part.MaskedSum.okE_mul (Johnson/Top/H/P1Tie/Words.lean) · eq_same
(Johnson/Desc/First/TailClaims/EquationsCover.lean) · K9L.core_coefBody
(Johnson/Desc/First/Batch/Law/Coef.lean).
Limits. EVERY PREMISE IS SHOWN OF NO STATE HERE. That the data behind hold the number of the claims
in front as the number under which the test takes its weight is not said here. Two premises stand at
the data and the ledger behind the adding: Fo.CoefOK, and that the piece's rows lie in the array.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K8.Honest.PieceWeight
import Johnson.Desc.K8.Honest.EqFactor
import Johnson.Desc.K8.Honest.SecondNz
import OnBytes.Tie.Pv.Lookup.Ends.FoTailPlanes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law
open OnBytes.Tie.Pv.Tail.Port

/-- The two lists of the calls' pieces are one. -/
theorem joinPairs_all (tl : HTailF2) : joinPairs tl = Fo.allPieces tl := by
  unfold joinPairs Fo.allPieces
  simp

/-- The declared weights of a piece's virtual row: inside the piece's rows. -/
theorem pieceW_in (c : CallZ) (zk : Array E) (p : OnBytes.Model.Piece) (R r : Nat) (hr : r < p.Rp)
    (hR : p.r0 + p.Rp ≤ R) :
    (Fo.pieceW c zk p R).getD (p.r0 + r) zeroE =
      (eqTab (zk.extract (c.call.n - p.b) (c.call.n - p.b + p.a))).getD r zeroE := by
  unfold Fo.pieceW
  rw [getD_map_range _ _ _ _ (by omega), if_pos ⟨Nat.le_add_right _ _, by omega⟩,
    Nat.add_sub_cancel_left]

/-- Outside the piece's rows: the word 0. -/
theorem pieceW_out (c : CallZ) (zk : Array E) (p : OnBytes.Model.Piece) (R r : Nat)
    (h : ¬ (p.r0 ≤ r ∧ r < p.r0 + p.Rp)) : (Fo.pieceW c zk p R).getD r zeroE = zeroE := by
  unfold Fo.pieceW
  by_cases hr : r < R
  · rw [getD_map_range _ _ _ _ hr, if_neg h]
  · simp [Array.getD, hr]

/-- **The weights on the rows of a piece's virtual row, behind the step that lays them**: the
library's law, at the ledger as the tests read it. -/
theorem piece_coef (tl : HTailF2) (g : Forest.Heard) (F : Fork) (T : Fo.CoefOK tl F)
    (x : Nat × OnBytes.Model.Piece) (hx : x ∈ joinPairs tl) :
    (((coefBody tl g F).trees.getD x.2.tree {}).rows.getD x.2.row {}).coef =
      Fo.pieceW (tl.zOf x.1) (g.zk.getD x.1 #[]) x.2 (F.trees.getD x.2.tree {}).R :=
  T.pieceW g x (joinPairs_all tl ▸ hx)

/-- **What the pieces' half asks of one expected piece, in front of the batching**: on public
numbers and on what the digits' lookup has heard: of the plan's piece under the expected piece's
call and index. -/
structure PieceFront (tl : HTailF2) (g : Forest.Heard) (w : Want) : Prop where
  mem : (w.call, (tl.zOf w.call).pieces.getD w.i {}) ∈ joinPairs tl
  row : w.row = ((tl.zOf w.call).pieces.getD w.i {}).row
  r0 : w.r0 = ((tl.zOf w.call).pieces.getD w.i {}).r0
  Rp : w.Rp = ((tl.zOf w.call).pieces.getD w.i {}).Rp
  c0 : w.c0 = ((tl.zOf w.call).pieces.getD w.i {}).c0
  Cp : w.Cp = ((tl.zOf w.call).pieces.getD w.i {}).Cp
  pos : 0 < ((tl.zOf w.call).pieces.getD w.i {}).Cp
  ok : Fo.PieceOK tl w.call (tl.zOf w.call).call.n ((tl.zOf w.call).pieces.getD w.i {})
  size : (g.zk.getD w.call #[]).size = (tl.zOf w.call).call.n
  n63 : (tl.zOf w.call).call.n - ((tl.zOf w.call).pieces.getD w.i {}).b ≤ 63
  e : g.e.getD w.call zeroE = callWeightAgain g w.call

section
variable {tl tl' : HTailF2} {funs : Array HFun} {Y G F₁ F₂ : Fork} {fr k8 bk : List Claim}
  {n₀ : Nat}

/-- **THE PRODUCT OF THE TWO WEIGHTS AT A CELL OF A PIECE IS WHAT THE SECOND COMPUTATION EXPECTS, AS
WORDS.** In the letters of the data in front. -/
theorem Added8.piece_cell (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀)
    {g : Forest.Heard} (hg : tl.heard = some g) (hc : g.cEnd.ents.isEmpty = true)
    (hA : apartB tl = true) (hL : piecesLaid tl = true) (w : Want) (hw : PieceFront tl g w)
    (R : Nat)
    (hR : ((tl.zOf w.call).pieces.getD w.i {}).r0 + ((tl.zOf w.call).pieces.getD w.i {}).Rp ≤ R)
    (h0 : ((Y.trees.getD tl.ix.ZZ {}).rows.getD
      ((tl.zOf w.call).pieces.getD w.i {}).row {}).L0 = 0)
    (hP : ∀ i, OffBut fr k8 bk fr.length tl.ix.ZZ ((tl.zOf w.call).pieces.getD w.i {}).row i)
    (r cc : Nat) (hr : r < ((tl.zOf w.call).pieces.getD w.i {}).Rp)
    (hcc : cc < ((tl.zOf w.call).pieces.getD w.i {}).Cp) :
    mulE ((Fo.pieceW (tl.zOf w.call) (g.zk.getD w.call #[])
          ((tl.zOf w.call).pieces.getD w.i {}) R).getD
          (((tl.zOf w.call).pieces.getD w.i {}).r0 + r) zeroE)
        ((weightsOf G tl.ix.ZZ ((tl.zOf w.call).pieces.getD w.i {}).row).getD
          (((tl.zOf w.call).pieces.getD w.i {}).c0 + cc) zeroE) =
      mulE (subE zeroE (mulE (t2fKappaByText Y.theta fr.length) (callWeightAgain g w.call)))
        (eqPlainF (g.zk.getD w.call #[]) (((tl.zOf w.call).pieces.getD w.i {}).off +
          r * ((tl.zOf w.call).pieces.getD w.i {}).CP + cc)) := by
  refine ProdV.gl_inj _ _ (Part.MaskedSum.okE_mul _ _) (Part.MaskedSum.okE_mul _ _) ?_
  have hv := A.weight_piece hg hc hA hL (w.call, (tl.zOf w.call).pieces.getD w.i {}) hw.mem cc hcc
    h0 (hP _)
  rw [joinTerm_in] at hv
  have hf := piece_factor_ok hw.ok (g.zk.getD w.call #[]) hw.size hw.n63 r cc hr
    (Nat.lt_of_lt_of_le hcc hw.ok.le)
  rw [Reading.gl.mul, Reading.gl.mul, pieceW_in _ _ _ _ _ hr hR, hv, hf, Reading.gl.sub,
    Reading.gl.zero, Reading.gl.mul, kappa_val, hw.e]
  unfold Fo.joinZc
  ring

/-- **THE PIECES' HALF OF WHAT MUST NEVER FAIL, AT ONE EXPECTED PIECE, WHOLE, BEHIND THE ADDING**:
all seven parts of `PieceEqs`, at the data behind and the ledger behind the step that lays the
rows' weights, at the weight that the test takes: the batching element to the number of the claims
in front. -/
theorem Added8.pieceEqs (A : Added8 tl tl' funs Y G F₁ F₂ fr k8 bk n₀)
    {g : Forest.Heard} (hg : tl.heard = some g) (hc : g.cEnd.ents.isEmpty = true)
    (hA : apartB tl = true) (hL : piecesLaid tl = true) (w : Want) (hw : PieceFront tl g w)
    (T : Fo.CoefOK tl' G) (hR : w.r0 + w.Rp ≤ (G.trees.getD tl.ix.ZZ {}).R)
    (hz : ((Y.trees.getD tl.ix.ZZ {}).rows.getD w.row {}).L0 = 0)
    (hP : ∀ i, OffBut fr k8 bk fr.length tl.ix.ZZ w.row i) :
    PieceEqs tl' (coefBody tl' g G) g (t2fKappaByText (coefBody tl' g G).theta fr.length) w := by
  have bθ : (coefBody tl' g G).theta = Y.theta :=
    (congrArg (·.2.1) (K9L.core_coefBody tl' g G)).trans A.core.1
  have eZ : tl'.zOf w.call = tl.zOf w.call :=
    eq_same (fun t : HTailF2 => t.zOf w.call) A.eq (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ => rfl) (fun _ _ _ _ => rfl)
  have eI : tl'.ix = tl.ix :=
    eq_same (·.ix) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl)
  have eJ : joinPairs tl' = joinPairs tl :=
    eq_same (fun t : HTailF2 => joinPairs t) A.eq (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun _ _ _ _ => rfl)
  have eC : (((coefBody tl' g G).trees.getD tl.ix.ZZ {}).rows.getD
      ((tl.zOf w.call).pieces.getD w.i {}).row {}).coef =
      Fo.pieceW (tl.zOf w.call) (g.zk.getD w.call #[]) ((tl.zOf w.call).pieces.getD w.i {})
        (G.trees.getD tl.ix.ZZ {}).R := by
    have k := piece_coef tl' g G T (w.call, (tl.zOf w.call).pieces.getD w.i {})
      (by rw [eJ]; exact hw.mem)
    rw [eZ] at k
    have ht : ((tl.zOf w.call).pieces.getD w.i {}).tree = tl.ix.ZZ := hw.ok.tree
    simp only [ht] at k
    exact k
  have eW : (((coefBody tl' g G).trees.getD tl.ix.ZZ {}).rows.getD
      ((tl.zOf w.call).pieces.getD w.i {}).row {}).L =
      weightsOf G tl.ix.ZZ ((tl.zOf w.call).pieces.getD w.i {}).row :=
    weights_coefBody tl' g G _ _
  have hRp : 0 < ((tl.zOf w.call).pieces.getD w.i {}).Rp := by
    rw [hw.ok.rp]
    exact Nat.two_pow_pos _
  rw [hw.r0, hw.Rp] at hR
  rw [hw.row] at hP hz
  have cell := A.piece_cell hg hc hA hL w hw _ hR hz hP
  unfold PieceEqs
  dsimp only
  rw [bθ, eZ, eI, hw.row, hw.r0, hw.Rp, hw.c0, hw.Cp, eC, eW]
  refine ⟨fun cc hcc => ?_, fun r hr => ?_, ?_, fun r hr => ?_, fun r h1 _ => ?_,
    fun cc hcc => ?_, fun cc h1 _ => ?_⟩
  · have k := cell 0 cc hRp hcc
    rw [Nat.add_zero, Nat.zero_mul, Nat.add_zero] at k
    rw [eqAt_plain]
    exact k
  · have k := cell r 0 hr hw.pos
    rw [Nat.add_zero, Nat.add_zero] at k
    exact k
  · have k := cell (((tl.zOf w.call).pieces.getD w.i {}).Rp - 1)
      (((tl.zOf w.call).pieces.getD w.i {}).Cp - 1) (by omega) (by have := hw.pos; omega)
    rw [← Nat.add_sub_assoc hRp, ← Nat.add_sub_assoc hw.pos] at k
    exact k
  · exact pieceW_out _ _ _ _ _ fun h => by omega
  · exact pieceW_out _ _ _ _ _ fun h => by omega
  · exact A.weight_beside hg hc hA hL (w.call, (tl.zOf w.call).pieces.getD w.i {}) hw.mem cc
      (fun h => by
        have h' : ((tl.zOf w.call).pieces.getD w.i {}).c0 ≤ cc := h.1
        omega) hz (hP _)
  · exact A.weight_beside hg hc hA hL (w.call, (tl.zOf w.call).pieces.getD w.i {}) hw.mem cc
      (fun h => by
        have h' : cc < ((tl.zOf w.call).pieces.getD w.i {}).c0 +
          ((tl.zOf w.call).pieces.getD w.i {}).Cp := h.2
        omega) hz (hP _)

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.joinPairs_all
#print axioms VerifiableInference.Desc.First.K8.Honest.pieceW_in
#print axioms VerifiableInference.Desc.First.K8.Honest.pieceW_out
#print axioms VerifiableInference.Desc.First.K8.Honest.piece_coef
#print axioms VerifiableInference.Desc.First.K8.Honest.Added8.piece_cell
#print axioms VerifiableInference.Desc.First.K8.Honest.Added8.pieceEqs
