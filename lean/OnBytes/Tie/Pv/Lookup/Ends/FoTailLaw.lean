-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoTailLaw.lean.
The smallness test's four hand-made claims, under one hypothesis on the world.

tail_four_dig (OnBytes/Tie/Pv/Lookup/Ends/FoTailDig.lean) takes, for each virtual row that the four
claims read, the hypothesis that the row is a named combination of its array's rows. This file pays
these hypotheses from one: RowsLaw (OnBytes/Tie/Pv/Lookup/Ends/FoRowsLaw.lean): every virtual row
that the state has is the combination of its array's rows under the weights that the state declares
for it. The state is coefAll tl g Fc, which is what a run of the byte-level routine coefficientsF
on the record tl from the state Fc leaves (coefficientsF_ok,
OnBytes/Tie/Pv/Lookup/Ends/FoCoef.lean).

* sum_window: a sum over the rows below R of a term that is 0 outside a window is the sum over the
  window.
* pieceW_read: the declared weights of a piece's row, read, at a row below the array's number.
* virt_piece: under RowsLaw at coefAll tl g Fc, CoefOK tl Fc, and the piece's rows inside its array,
  a piece's virtual row is the combination of the piece's own rows under the equality weights of the
  coordinates for the rows.
* tail_four_law: tail_four_dig with all four hypotheses on virtual rows paid. Its other premises
  stay. Left, on the world: RowsLaw at the entries cellAt t r i := μ₀ (en (t, r, i)). On the state
  Fc before coefficientsF: CoefOK (OnBytes/Tie/Pv/Lookup/Ends/FoTailPlanes.lean: coefTest is a test
  that can be run and gives it) and that each piece's rows lie inside its array.
  Fc is any state with these two properties: no premise ties it to the states of the two runs, and
  the record is the one before linJoin9.

Not claimed: anything on completeness or hiding.
Nor is it claimed that RowsLaw holds of committed arrays, that CoefOK follows from the success of
the routines that make the record and the arrays, or that the verifier runs coefficientsF on this
record from such a state.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoTailDig
import OnBytes.Tie.Pv.Lookup.Ends.FoTailPlanes

set_option autoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun OnBytes.DgP Cb.Fo Cb.LdLkp Finset

section
variable {K : Type} [CommRing K]

/-- A sum of a term that is 0 outside a window. -/
theorem sum_window (R r0 n : ℕ) (h : r0 + n ≤ R) (f : ℕ → K) :
    ∑ r ∈ range R, (if r0 ≤ r ∧ r < r0 + n then f r else 0) = ∑ j ∈ range n, f (r0 + j) := by
  rw [← Finset.sum_filter]
  have e : (range R).filter (fun r => r0 ≤ r ∧ r < r0 + n) = Ico r0 (r0 + n) := by
    ext r
    simp only [mem_filter, mem_range, mem_Ico]
    constructor
    · exact fun x => x.2
    · exact fun x => ⟨by omega, x⟩
  rw [e, sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]

variable (ρ : Reading K)

/-- The declared weights of a piece's row, read. -/
theorem pieceW_read (cz : CallZ) (zk : Array E) (p : Piece) (R r : ℕ) (hr : r < R) :
    ρ.val ((pieceW cz zk p R).getD r zeroE) =
      if p.r0 ≤ r ∧ r < p.r0 + p.Rp then
        (eqTabK (exL (rdL ρ zk) (cz.call.n - p.b) (cz.call.n - p.b + p.a))).getD (r - p.r0) 0
      else 0 := by
  have e : (pieceW cz zk p R).getD r zeroE =
      if p.r0 ≤ r ∧ r < p.r0 + p.Rp then
        (eqTab (zk.extract (cz.call.n - p.b) (cz.call.n - p.b + p.a))).getD (r - p.r0) zeroE
      else zeroE := by
    unfold pieceW
    simp [Array.getD, hr]
  rw [e]
  split_ifs
  · rw [rdL_getD, eqTab_val, rdL_extract]
  · exact ρ.zero

/-- Under the law a piece's virtual row is the combination of the piece's own rows. -/
theorem virt_piece (tl : HTailF2) (g : Heard) (Fc : Fork) (T : CoefOK tl Fc) (a : ℕ × Piece)
    (ha : a ∈ allPieces tl) (hR : a.2.r0 + a.2.Rp ≤ (Fc.trees.getD a.2.tree {}).R) (W : World K)
    (cellAt : ℕ → ℕ → ℕ → K) (hL : RowsLaw ρ (coefAll tl g Fc) W cellAt) (i : ℕ) :
    W.entry a.2.tree a.2.row i = ∑ r ∈ range a.2.Rp,
      (eqTabK (exL (rdL ρ (g.zk.getD a.1 #[])) ((tl.zOf a.1).call.n - a.2.b)
        ((tl.zOf a.1).call.n - a.2.b + a.2.a))).getD r 0 * cellAt a.2.tree (a.2.r0 + r) i := by
  have hR' : ((coefAll tl g Fc).trees.getD a.2.tree {}).R = (Fc.trees.getD a.2.tree {}).R :=
    ((frame_all tl g Fc).2 a.2.tree).1
  rw [hL a.2.tree a.2.row i ((frame_all tl g Fc).hasRow (T.piece a ha).1), hR', T.pieceW g a ha]
  rw [sum_congr rfl fun r hr => by
    rw [pieceW_read ρ _ _ _ _ r (mem_range.1 hr), ite_mul, zero_mul]]
  rw [sum_window _ _ _ hR fun r =>
    (eqTabK (exL (rdL ρ (g.zk.getD a.1 #[])) ((tl.zOf a.1).call.n - a.2.b)
      ((tl.zOf a.1).call.n - a.2.b + a.2.a))).getD (r - a.2.r0) 0 * cellAt a.2.tree r i]
  exact sum_congr rfl fun j _ => by rw [Nat.add_sub_cancel_left]

end

section
variable {K : Type} [Field K] (ρ : Reading K) {J₀ : Type}

theorem mem_allPieces {tl : HTailF2} {q : ℕ} (hq : q < 2) {p : Piece} (hp : p ∈ piecesL tl q) :
    (q, p) ∈ allPieces tl := by
  unfold allPieces
  rw [List.mem_append]
  rcases Nat.lt_succ_iff_lt_or_eq.1 hq with h | h
  · obtain rfl : q = 0 := by omega
    exact .inl (List.mem_map.2 ⟨p, hp, rfl⟩)
  · subst h
    exact .inr (List.mem_map.2 ⟨p, hp, rfl⟩)

/-- The four hand-made claims, under one hypothesis on the world. Fc: the state from which
coefficientsF runs. -/
theorem tail_four_law (tl tl1 tl2 : HTailF2) (F G1 G2 : Fork) (c c1 c2 : Ctx)
    (hJ : tl.linJoin9 F c = .ok ((tl1, G1), c1)) (hB : tl1.linBits9 G1 c1 = .ok ((tl2, G2), c2))
    (g : Heard) (hg : tl.heard = some g) (hs : tl.f9 = g.shape) (jLK : ℕ) (rsK : Rounds K)
    (F0 : Fork) (hI : HeardIs ρ g F0 (endsOf g.shape 5 jLK rsK)) (h0 : Later F0 F)
    (hok : FoNums.ok g.shape = true) (hT : TailOK tl) (hF : Sized F) (hLS : F.LS.size = F.ns)
    (hfull : 2 ^ g.shape.cK = g.shape.NC) (h5 : 5 ≤ g.shape.kT + g.shape.cK)
    (hn : ∀ q < 2, (g.zk.getD q #[]).size = (tl.zOf q).call.n)
    (h63 : ∀ q < 2, (tl.zOf q).call.n ≤ 63)
    (hP : ∀ q < 2, ∀ p ∈ piecesL tl q, PieceOK tl q (tl.zOf q).call.n p)
    (hD : ∀ q < 2, (piecesL tl q).Pairwise fun p p' =>
      p.off + 2 ^ p.b ≤ p'.off ∨ p'.off + 2 ^ p'.b ≤ p.off)
    (Fc : Fork) (T : CoefOK tl Fc)
    (hRw : ∀ a ∈ allPieces tl, a.2.r0 + a.2.Rp ≤ (Fc.trees.getD a.2.tree {}).R)
    (en : Ent3 → J₀) (mk : ℕ → J₀) (μ₀ : J₀ → K) (entry : ℕ → ℕ → ℕ → K)
    (H : Fork) (hH : Later G2 H)
    (hL : RowsLaw ρ (coefAll tl g Fc) (H.worldOf ρ (fun j => μ₀ (mk j)) entry)
      fun t r i => μ₀ (en (t, r, i))) :
    G2.total ρ (H.worldOf ρ (fun j => μ₀ (mk j)) entry) =
      F.total ρ (H.worldOf ρ (fun j => μ₀ (mk j)) entry) +
        ρ.val F.theta ^ F.nClaim * claimJoin g.shape 5 jLK rsK
          (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
          (fun c => AffK.val (digKF tl en (fun c => (endsOf g.shape 5 jLK rsK).zk.getD c []) c)
            (zext μ₀)) +
        ρ.val F.theta ^ (F.nClaim + 1) * claimLeaves g.shape 5 jLK rsK
          (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
          (colsK g.shape 5 (endsOf g.shape 5 jLK rsK).zb0
            fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p)) +
        ρ.val F.theta ^ (F.nClaim + 2) * claimBits g.shape 5 jLK rsK
          (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
          (colsK g.shape 5 (endsOf g.shape 5 jLK rsK).zb1
            fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p)) +
        ρ.val F.theta ^ (F.nClaim + 3) * Pin.countK g.shape 5
          (Pin.pinColK 5 fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p)) := by
  obtain ⟨v0, v1, v2⟩ := virt_bz ρ tl g Fc T.bz.1 T.bz.2.1 T.bz.2.2 T.mats T.bzR _ _ hL _ _
    (show rdL ρ g.zb0 = _ from hI.zb0) (show rdL ρ g.zb1 = _ from hI.zb1) tl.bzColumns
  refine tail_four_dig ρ tl tl1 tl2 F G1 G2 c c1 c2 hJ hB g hg hs jLK rsK F0 hI h0 hok hT hF hLS
    hfull h5 hn h63 hP hD en mk μ₀ entry v0 v1 v2 (fun q hq p hp i _ => ?_) H hH
  have e := virt_piece ρ tl g Fc T (q, p) (mem_allPieces hq hp) (hRw _ (mem_allPieces hq hp)) _ _
    hL (p.c0 + i)
  rw [(hP q hq p hp).tree] at e ⊢
  exact e

end
end Fo
