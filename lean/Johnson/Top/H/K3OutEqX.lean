-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3OutEqX.lean: the kind "lookup" (K3) at the smallness test's digits: eq_four_law
(Johnson/Top/H/EqPort/EqFour.lean), claimsAre_of_eq (Johnson/Top/H/K3OutDigits.lean) and k3Out_of_eq
(Johnson/Top/H/K3OutEq.lean) ONCE MORE, WITH THE LAW OF THE ROWS AT A LATER RECORD. Theorems with
their proofs.

Why. The rows' weights are not laid at the record tl from which eqKeys runs: they are laid later in
the link, behind the adding of all its claims, at the record tlX as the run of claims has left it,
from the link's ledger Fc behind its last claim. So CoefOK and RowsLaw are wanted at tlX. The
library has the like for its own law (tail_four_lawX,
OnBytes/Tie/Pv/Lookup/Ends/FoLookDigitsSame.lean): tlX is any record with SameZ tl tlX: the same
numbers of the arrays, the same two calls, the same record of what was heard. At tlX := tl these are
the three elder theorems.

Limits. Those of the three files. That the record at which a run lays the weights has SameZ with tl,
and that the ledger with the weights is coefAll tlX g Fc, is not said here.
RowsLaw whole is not payable at the closed caller of Johnson/Desc/First/Look/K3Caller.lean (no seat
for an earlier link's array): there use k3Out_of_rows, Johnson/Top/H/K3OutRows.lean.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3OutEq
import OnBytes.Tie.Pv.Lookup.Ends.FoLookDigitsSame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo.Eq
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun OnBytes.DgP Cb.Fo Cb.LdLkp Finset
open VerifiableInference
open VerifiableInference.Desc.First.TailClaims

variable {front : ℕ}

local notation:65 x:66 " ⟫ " F:max c:max => EqM.at x front F c

section
variable {K : Type} [Field K] (ρ : Reading K) {J₀ : Type}

/-- **The four claims, one by one, under the law of the rows at a later record.** tlX: the record at
which the rows' weights are laid. Fc: the ledger from which they are laid. -/
theorem eq_four_lawX (tl tl1 tl2 tlX : HTailF2) (hX : SameZ tl tlX) (F G1 G2 : Fork)
    (c c1 c2 : Array Desc.Claim)
    (hJ : eqKeys tl ⟫ F c = .ok ((tl1, G1), c1)) (hB : eqCounts tl1 ⟫ G1 c1 = .ok ((tl2, G2), c2))
    (g : Heard) (hg : tl.heard = some g) (hs : tl.f9 = g.shape) (jLK : ℕ) (rsK : Rounds K)
    (F0 : Fork) (hI : HeardIs ρ g F0 (endsOf g.shape 5 jLK rsK)) (h0 : _root_.Fo.Later F0 F)
    (hok : FoNums.ok g.shape = true) (hT : TailOK tl) (hF : Sized F)
    (hfull : 2 ^ g.shape.cK = g.shape.NC) (h5 : 5 ≤ g.shape.kT + g.shape.cK)
    (hn : ∀ q < 2, (g.zk.getD q #[]).size = (tl.zOf q).call.n)
    (h63 : ∀ q < 2, (tl.zOf q).call.n ≤ 63)
    (hP : ∀ q < 2, ∀ p ∈ piecesL tl q, PieceOK tl q (tl.zOf q).call.n p)
    (hD : ∀ q < 2, (piecesL tl q).Pairwise fun p p' =>
      p.off + 2 ^ p.b ≤ p'.off ∨ p'.off + 2 ^ p'.b ≤ p.off)
    (Fc : Fork) (T : CoefOK tlX Fc)
    (hRw : ∀ a ∈ allPieces tl, a.2.r0 + a.2.Rp ≤ (Fc.trees.getD a.2.tree {}).R)
    (en : Ent3 → J₀) (mk : ℕ → J₀) (μ₀ : J₀ → K) (entry : ℕ → ℕ → ℕ → K)
    (H : Fork) (hH : _root_.Fo.Later G2 H)
    (hL : RowsLaw ρ (coefAll tlX g Fc) (H.worldOf ρ (fun j => μ₀ (mk j)) entry)
      fun t r i => μ₀ (en (t, r, i))) :
    ∃ k1 k2 k3 k4 : Desc.Claim, c2 = (((c.push k1).push k2).push k3).push k4 ∧
      _root_.Fo.Later F G2 ∧ Sized G2 ∧
      [k1].map (valC ρ (H.worldOf ρ (fun j => μ₀ (mk j)) entry)) =
        [claimJoin g.shape 5 jLK rsK (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
          (fun c => AffK.val (digKF tl en (fun c => (endsOf g.shape 5 jLK rsK).zk.getD c []) c)
            (zext μ₀))] ∧
      [k2, k3, k4].map (valC ρ (H.worldOf ρ (fun j => μ₀ (mk j)) entry)) =
        [claimLeaves g.shape 5 jLK rsK (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
            (colsK g.shape 5 (endsOf g.shape 5 jLK rsK).zb0
              fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p)),
          claimBits g.shape 5 jLK rsK (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
            (colsK g.shape 5 (endsOf g.shape 5 jLK rsK).zb1
              fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p)),
          Pin.countK g.shape 5
            (Pin.pinColK 5 fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))] := by
  obtain ⟨v0, v1, v2⟩ := virt_bz ρ tlX g Fc T.bz.1 T.bz.2.1 T.bz.2.2 T.mats T.bzR _ _ hL _ _
    (show rdL ρ g.zb0 = _ from hI.zb0) (show rdL ρ g.zb1 = _ from hI.zb1) tl.bzColumns
  rw [hX.ix] at v0 v1 v2
  refine eq_four ρ tl tl1 tl2 F G1 G2 c c1 c2 hJ hB g hg hs jLK rsK F0 hI h0 hok hT hF
    hfull h5 hn h63 hP hD en mk μ₀ entry v0 v1 v2 (fun q hq p hp i _ => ?_) H hH
  have e := virt_piece ρ tlX g Fc T (q, p) (hX.pieces ▸ mem_allPieces hq hp)
    (hRw _ (mem_allPieces hq hp)) _ _ hL (p.c0 + i)
  rw [hX.zOf] at e
  rw [(hP q hq p hp).tree] at e ⊢
  exact e


end
end Fo.Eq

namespace VerifiableInference.OnPublicFiles
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun OnBytes.DgP Cb.Fo Cb.LdLkp Finset
open _root_.Fo _root_.Fo.Eq
open VerifiableInference.Desc.First.TailClaims

section
variable {K : Type} [Field K] (ρ : Reading K) {J₀ : Type} {front : ℕ}

/-- **The second way to the middle: the digits, the rows' weights laid at a later record.** clO: the
claims of the lookup's run "objects". -/
theorem claimsAre_of_eqX (tl tl1 tl2 tlX : HTailF2) (hX : SameZ tl tlX) (F G1 G2 : Fork)
    (c c1 c2 : Array Desc.Claim)
    (hJ : EqM.at (eqKeys tl) front F c = .ok ((tl1, G1), c1))
    (hB : EqM.at (eqCounts tl1) front G1 c1 = .ok ((tl2, G2), c2))
    (g : Heard) (hg : tl.heard = some g) (hs : tl.f9 = g.shape) (jLK : ℕ) (rsK : Rounds K)
    (F0 : Fork) (hI : HeardIs ρ g F0 (endsOf g.shape 5 jLK rsK)) (h0 : _root_.Fo.Later F0 F)
    (hok : FoNums.ok g.shape = true) (hT : TailOK tl) (hF : Sized F)
    (hfull : 2 ^ g.shape.cK = g.shape.NC) (h5 : 5 ≤ g.shape.kT + g.shape.cK)
    (hn : ∀ q < 2, (g.zk.getD q #[]).size = (tl.zOf q).call.n)
    (h63 : ∀ q < 2, (tl.zOf q).call.n ≤ 63)
    (hP : ∀ q < 2, ∀ p ∈ piecesL tl q, PieceOK tl q (tl.zOf q).call.n p)
    (hD : ∀ q < 2, (piecesL tl q).Pairwise fun p p' =>
      p.off + 2 ^ p.b ≤ p'.off ∨ p'.off + 2 ^ p'.b ≤ p.off)
    (Fc : Fork) (T : CoefOK tlX Fc)
    (hRw : ∀ a ∈ allPieces tl, a.2.r0 + a.2.Rp ≤ (Fc.trees.getD a.2.tree {}).R)
    (en : Ent3 → J₀) (mk : ℕ → J₀) (μ₀ : J₀ → K) (entry : ℕ → ℕ → ℕ → K)
    (H : Fork) (hH : _root_.Fo.Later G2 H)
    (hL : RowsLaw ρ (coefAll tlX g Fc) (H.worldOf ρ (fun j => μ₀ (mk j)) entry)
      fun t r i => μ₀ (en (t, r, i)))
    (clO : List Desc.Claim)
    (hO : clO.map (valC ρ (H.worldOf ρ (fun j => μ₀ (mk j)) entry)) =
      (endsOf g.shape 5 jLK rsK).rows.map
        (rowRes fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))) :
    ∃ k1 k2 k3 k4 : Desc.Claim, c2 = (((c.push k1).push k2).push k3).push k4 ∧
      _root_.Fo.Later F G2 ∧ Sized G2 ∧
      K3ClaimsAre (valC ρ (H.worldOf ρ (fun j => μ₀ (mk j)) entry)) g.shape 5 jLK rsK
        (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
        (fun c => (digKF tl en (fun c => (endsOf g.shape 5 jLK rsK).zk.getD c []) c).val
          (zext μ₀)) clO [k2, k3, k4] [k1] := by
  obtain ⟨k1, k2, k3, k4, e, l, s, vJ, vP⟩ := eq_four_lawX ρ tl tl1 tl2 tlX hX F G1 G2 c c1 c2 hJ hB
    g hg hs jLK rsK F0 hI h0 hok hT hF hfull h5 hn h63 hP hD Fc T hRw en mk μ₀ entry H hH hL
  exact ⟨k1, k2, k3, k4, e, l, s, hO, vP, vJ⟩


/-- **The payer into the row out, at the digits, the rows' weights laid at a later record.** -/
theorem k3Out_of_eqX (tl tl1 tl2 tlX : HTailF2) (hX : SameZ tl tlX) (F G1 G2 : Fork)
    (c c1 c2 : Array Desc.Claim)
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
    (Fc : Fork) (T : CoefOK tlX Fc)
    (hRw : ∀ a ∈ allPieces tl, a.2.r0 + a.2.Rp ≤ (Fc.trees.getD a.2.tree {}).R)
    (en : Ent3 → J₀) (mk : ℕ → J₀) (μ₀ : J₀ → K) (entry : ℕ → ℕ → ℕ → K)
    (H : Fork) (hH : _root_.Fo.Later G2 H)
    (hL : RowsLaw ρ (coefAll tlX g Fc) (H.worldOf ρ (fun j => μ₀ (mk j)) entry)
      fun t r i => μ₀ (en (t, r, i)))
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
  obtain ⟨k1, k2, k3, k4, e, _, _, hA⟩ := claimsAre_of_eqX ρ tl tl1 tl2 tlX hX F G1 G2 c c1 c2 hJ
    hB g hg hs jLK rs F' hI h0 hok hT hF hfull h5 hn h63 hP hD Fc T hRw en mk μ₀ entry H hH hL clO
    (hO rs hI)
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


end

end VerifiableInference.OnPublicFiles

#print axioms Fo.Eq.eq_four_lawX
#print axioms VerifiableInference.OnPublicFiles.k3Out_of_eqX
