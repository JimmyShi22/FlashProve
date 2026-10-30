-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3OutDigits.lean: the kind "lookup" (K3) at the smallness test's digits: THE SECOND
WAY TO THE MIDDLE STATEMENT K3ClaimsAre (Johnson/Top/H/K3OutWide.lean): the lookup's own rows as its
run "objects" hands them out, and the four claims that the smallness test's run of claims lays by
hand (eqKeys, eqCounts, Johnson/Desc/First/TailClaims/Equations.lean), each a form plus runs on
virtual rows. Theorems with their proofs.

Main names:
  `claimsAre_kf`: in K3ClaimsAre the values for the key vectors matter at the calls alone.
  `valC_plain`: a claim without runs is worth its form.
  `claimsAre_of_eq`: where eqKeys and then eqCounts say yes, under the premises of eq_four_law
    (Johnson/Top/H/EqPort/EqFour.lean), RowsLaw among them, and where the lookup's rows are worth
    their residues: K3ClaimsAre, with the four claims in the list's order: the join's first, then
    the planes' three.

How the world is read: the claims are judged at H.worldOf ρ (fun j => μ₀ (mk j)) entry, for a ledger
H later than the one that eqCounts leaves, AND «entry» IS TIED TO THE SAME μ₀ BY RowsLaw: every
virtual row's entry is the combination of its array's rows, at the cells μ₀ (en (t, r, i)), under
the weights that are laid in the ledger coefAll tl g Fc.

Limits. A tie: it has no error term. Those of the two files named. The values for the key vectors
are those of the library's typed key forms (digKF); that these are the key vectors' extensions at
the calls' points is the library's dig5_KFok_ends, spent by whoever closes the caller.
RowsLaw whole is not payable at the closed caller of Johnson/Desc/First/Look/K3Caller.lean (no seat
for an earlier link's array): there use k3Out_of_rows, Johnson/Top/H/K3OutRows.lean.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3OutWide
import Johnson.Top.H.EqPort.EqFour

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun OnBytes.DgP Cb.Fo Cb.LdLkp Finset
open _root_.Fo _root_.Fo.Eq
open VerifiableInference.Desc.First.TailClaims

/-- The values for the key vectors matter at the calls alone. -/
theorem claimsAre_kf {Cl K : Type} [CommRing K] {val : Cl → K} {h : FoNums.Sh} {lm jLK : ℕ}
    {rs : Rounds K} {ν : _root_.Fo.Pl → K} {kf kf' : ℕ → K} {clO clP clJ : List Cl}
    (hk : ∀ c, c < h.NC → kf c = kf' c) (hA : K3ClaimsAre val h lm jLK rs ν kf clO clP clJ) :
    K3ClaimsAre val h lm jLK rs ν kf' clO clP clJ :=
  ⟨hA.1, hA.2.1, by rw [hA.2.2, _root_.Fo.claimJoin_congr h lm jLK rs ν kf kf' hk]⟩

/-- A claim without runs is worth its form. -/
theorem valC_plain {K : Type} [CommRing K] (ρ : Reading K) (W : World K) (k : Desc.Claim)
    (h : k.runs = #[]) : valC ρ W k = k.form.value ρ W := by
  unfold valC
  rw [h]
  simp

section
variable {K : Type} [Field K] (ρ : Reading K) {J₀ : Type} {front : ℕ}

/-- **The second way to the middle: the digits.** clO: the claims of the lookup's run "objects". -/
theorem claimsAre_of_eq (tl tl1 tl2 : HTailF2) (F G1 G2 : Fork) (c c1 c2 : Array Desc.Claim)
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
    (Fc : Fork) (T : CoefOK tl Fc)
    (hRw : ∀ a ∈ allPieces tl, a.2.r0 + a.2.Rp ≤ (Fc.trees.getD a.2.tree {}).R)
    (en : Ent3 → J₀) (mk : ℕ → J₀) (μ₀ : J₀ → K) (entry : ℕ → ℕ → ℕ → K)
    (H : Fork) (hH : _root_.Fo.Later G2 H)
    (hL : RowsLaw ρ (coefAll tl g Fc) (H.worldOf ρ (fun j => μ₀ (mk j)) entry)
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
  obtain ⟨k1, k2, k3, k4, e, l, s, vJ, vP⟩ := eq_four_law ρ tl tl1 tl2 F G1 G2 c c1 c2 hJ hB g hg
    hs jLK rsK F0 hI h0 hok hT hF hfull h5 hn h63 hP hD Fc T hRw en mk μ₀ entry H hH hL
  exact ⟨k1, k2, k3, k4, e, l, s, hO, vP, vJ⟩

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.claimsAre_of_eq
