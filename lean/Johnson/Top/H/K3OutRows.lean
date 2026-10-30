-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3OutRows.lean: the kind "lookup" (K3) at the smallness test's digits: THE PAYER INTO
THE ROW OUT UNDER NO MORE OF THE LAW OF THE ROWS THAN THE FOUR CLAIMS READ. Definitions and theorems
with their proofs.

Why. k3Out_of_eq and its kin (Johnson/Top/H/K3OutEq.lean, Johnson/Top/H/K3OutEqX.lean) ask the
library's RowsLaw: at EVERY virtual row of EVERY array of the ledger the entry is the combination of
that array's cells, the cells read off the caller's entries μ₀ by a map en. The four claims read
only the three virtual rows of the counts' array and the pieces' virtual rows on the digits' array.
A closed caller need not have a place for the cells of the link's other arrays; where it has none,
the whole law asks of such a row what an honest run does not meet, and the premise could not be
paid. The closed caller of Johnson/Desc/First/Look/K3Caller.lean has none for an array that an
earlier link sent; here the question does not arise.

Main names:
  `DigRows ρ tl g entry cell`: four clauses: the counts' array's virtual rows 0 and 1 are its 32
    rows under the equality weights of the first five coordinates of the two points heard; its row 2
    is their sum; each piece's virtual row is the piece's own rows under the equality weights of its
    share of the call's key point. The points are read off what was heard: no round is named.
  `k3Out_of_rows`: the payer, under DigRows at cell := μ₀ ∘ en. No ledger Fc, no CoefOK, no later
    record.
  `digRows_of_law`: the whole RowsLaw, with CoefOK at a later record and the pieces' rows inside
    their arrays, gives DigRows: so whoever has the whole law loses nothing.

Limits. A tie: it has no error term. Those of Johnson/Top/H/EqPort/EqFour.lean. DigRows is met by
entries that are DEFINED by its right sides from any cells: that μ₀ is what was committed, and that
the world at which the link's equation speaks has these entries, is owed by whoever turns runs into
rows on oracle messages.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3OutEqX

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun OnBytes.DgP Cb.Fo Cb.LdLkp Finset
open _root_.Fo _root_.Fo.Eq
open VerifiableInference.Desc.First.TailClaims

section
variable {K : Type} [Field K] (ρ : Reading K)

/-- **What of the law of the rows the four claims read.** -/
structure DigRows (tl : HTailF2) (g : Heard) (entry : ℕ → ℕ → ℕ → K) (cell : Ent3 → K) : Prop where
  bz0 : VirtRow entry tl.ix.BZ 0 (fun r => (eqTabK ((rdL ρ g.zb0).take 5)).getD r 0)
    (fun r i => cell (tl.ix.BZ, r, i)) 32 tl.bzColumns
  bz1 : VirtRow entry tl.ix.BZ 1 (fun r => (eqTabK ((rdL ρ g.zb1).take 5)).getD r 0)
    (fun r i => cell (tl.ix.BZ, r, i)) 32 tl.bzColumns
  bz2 : VirtRow entry tl.ix.BZ 2 (fun _ => 1) (fun r i => cell (tl.ix.BZ, r, i)) 32 tl.bzColumns
  piece : ∀ q < 2, ∀ p ∈ piecesL tl q, ∀ i < p.Cp, entry p.tree p.row (p.c0 + i) =
    ∑ r ∈ range p.Rp, (eqTabK (exL (rdL ρ (g.zk.getD q #[])) ((tl.zOf q).call.n - p.b)
      ((tl.zOf q).call.n - p.b + p.a))).getD r 0 * cell (tl.ix.ZZ, p.r0 + r, p.c0 + i)

variable {J₀ : Type} {front : ℕ}

/-- **The payer into the row out, under DigRows.** -/
theorem k3Out_of_rows (tl tl1 tl2 : HTailF2) (F G1 G2 : Fork) (c c1 c2 : Array Desc.Claim)
    (hJ : EqM.at (eqKeys tl) front F c = .ok ((tl1, G1), c1))
    (hB : EqM.at (eqCounts tl1) front G1 c1 = .ok ((tl2, G2), c2))
    (g : Heard) (hg : tl.heard = some g) (hs : tl.f9 = g.shape) (jLK : ℕ)
    (F' : Fork) (h0 : _root_.Fo.Later F' F)
    (hok : FoNums.ok g.shape = true) (hT : TailOK tl) (hF : Sized F)
    (hfull : 2 ^ g.shape.cK = g.shape.NC) (h5 : 5 ≤ g.shape.kT + g.shape.cK)
    (hn : ∀ q < 2, (g.zk.getD q #[]).size = (tl.zOf q).call.n)
    (h63 : ∀ q < 2, (tl.zOf q).call.n ≤ 63)
    (hP : ∀ q < 2, ∀ p ∈ piecesL tl q, PieceOK tl q (tl.zOf q).call.n p)
    (hD : ∀ q < 2, (piecesL tl q).Pairwise fun p p' =>
      p.off + 2 ^ p.b ≤ p'.off ∨ p'.off + 2 ^ p'.b ≤ p.off)
    (en : Ent3 → J₀) (mk : ℕ → J₀) (μ₀ : J₀ → K) (entry : ℕ → ℕ → ℕ → K)
    (H : Fork) (hH : _root_.Fo.Later G2 H)
    (hV : DigRows ρ tl g entry fun e => μ₀ (en e))
    (clO : List Desc.Claim)
    (hO : ∀ rs : Rounds K, HeardIs ρ g F' (endsOf g.shape 5 jLK rs) →
      clO.map (valC ρ (H.worldOf ρ (fun j => μ₀ (mk j)) entry)) =
        (endsOf g.shape 5 jLK rs).rows.map
          (rowRes fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p)))
    (hzO : ∀ k ∈ clO, valC ρ (H.worldOf ρ (fun j => μ₀ (mk j)) entry) k = 0)
    (hz : ∀ k ∈ c2.toList, valC ρ (H.worldOf ρ (fun j => μ₀ (mk j)) entry) k = 0) :
    K3Out g.shape 5 jLK (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
      (forK K (digL5 K tl en mk jLK Unit) () (zext μ₀)) ρ g F' := by
  refine (k3Out_iff _ _ _ _ _ _ _ _).2 fun rs hI => ?_
  have e0 : rdL ρ g.zb0 = (endsOf g.shape 5 jLK rs).zb0 := hI.zb0
  have e1 : rdL ρ g.zb1 = (endsOf g.shape 5 jLK rs).zb1 := hI.zb1
  obtain ⟨k1, k2, k3, k4, e, _, _, vJ, vP⟩ := eq_four ρ tl tl1 tl2 F G1 G2 c c1 c2 hJ hB g hg hs
    jLK rs F' hI h0 hok hT hF hfull h5 hn h63 hP hD en mk μ₀ entry (e0 ▸ hV.bz0) (e1 ▸ hV.bz1)
    hV.bz2 hV.piece H hH
  have hA : K3ClaimsAre (valC ρ (H.worldOf ρ (fun j => μ₀ (mk j)) entry)) g.shape 5 jLK rs
      (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
      (fun c => (digKF tl en (fun c => (endsOf g.shape 5 jLK rs).zk.getD c []) c).val (zext μ₀))
      clO [k2, k3, k4] [k1] := ⟨hO rs hI, vP, vJ⟩
  have hk := dig5_KFok_ends hT (by rw [hs]; exact hok) en mk jLK () 5 jLK rs
  rw [hs] at hk
  have hA' := claimsAre_kf (kf' := keysAt g.shape 5 jLK
    (forK K (digL5 K tl en mk jLK Unit) () (zext μ₀)) rs) (fun q hq => hk (zext μ₀) q hq) hA
  refine claimsAre_zero hA' fun k hk' => ?_
  have m : ∀ x, x = k1 ∨ x = k2 ∨ x = k3 ∨ x = k4 → x ∈ c2.toList := by
    intro x hx
    rw [e]
    simp only [Array.toList_push, List.mem_append, List.mem_singleton]
    tauto
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hk'
  rcases hk' with (hk' | hk' | hk' | hk') | hk'
  · exact hzO k hk'
  · exact hz k (m k (by tauto))
  · exact hz k (m k (by tauto))
  · exact hz k (m k (by tauto))
  · exact hz k (m k (by tauto))

/-- **The whole law of the rows gives DigRows.** tlX, Fc: the record at which, and the ledger from
which, the rows' weights are laid. -/
theorem digRows_of_law (tl tlX : HTailF2) (hX : SameZ tl tlX) (g : Heard)
    (hP : ∀ q < 2, ∀ p ∈ piecesL tl q, PieceOK tl q (tl.zOf q).call.n p)
    (Fc : Fork) (T : CoefOK tlX Fc)
    (hRw : ∀ a ∈ allPieces tl, a.2.r0 + a.2.Rp ≤ (Fc.trees.getD a.2.tree {}).R)
    (W : World K) (cell : Ent3 → K)
    (hL : RowsLaw ρ (coefAll tlX g Fc) W fun t r i => cell (t, r, i)) :
    DigRows ρ tl g W.entry cell := by
  obtain ⟨v0, v1, v2⟩ := virt_bz ρ tlX g Fc T.bz.1 T.bz.2.1 T.bz.2.2 T.mats T.bzR _ _ hL _ _
    rfl rfl tl.bzColumns
  rw [hX.ix] at v0 v1 v2
  refine ⟨v0, v1, v2, fun q hq p hp i _ => ?_⟩
  have e := virt_piece ρ tlX g Fc T (q, p) (hX.pieces ▸ mem_allPieces hq hp)
    (hRw _ (mem_allPieces hq hp)) _ _ hL (p.c0 + i)
  rw [hX.zOf] at e
  rw [(hP q hq p hp).tree] at e ⊢
  exact e

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3Out_of_rows
#print axioms VerifiableInference.OnPublicFiles.digRows_of_law
