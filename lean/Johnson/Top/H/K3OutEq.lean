-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3OutEq.lean: the kind "lookup" (K3) at the smallness test's digits: A PAYER INTO THE
ROW OUT, UNDER THE WHOLE LAW OF THE ROWS: where the lookup's own rows (its run "objects") and the
four claims that the smallness test's run of claims lays (eqKeys, eqCounts,
Johnson/Desc/First/TailClaims/Equations.lean) are all worth 0 in a world that meets the law of the
rows, the row out K3Out (Johnson/Top/H/K3RowOut.lean) holds: at all rounds for which the heard
record stands, every member of the library's list of the lookup's claims is 0, at the committed
cells' own combinations and at the key vectors' extensions. Theorems with their proofs.

Main names:
  `objects_valC`: the claims of "objects", laid as claims without runs, are worth the rows'
    residues, at all rounds for which the heard record stands.
  `k3Out_of_eq`: that payer.

How the world is read: one μ₀ for all: the mask under slot j is μ₀ (mk j); the cell (t, r, i) of a
committed array is μ₀ (en (t, r, i)); the entries of virtual rows are tied to these cells by RowsLaw
at the ledger coefAll tl g Fc in which the rows' weights are laid; the key vectors are the layout's
(digL5) at zext μ₀. The claims are judged at one ledger H, later than the ledgers that the runs
leave.

Premises, and who pays: as in Johnson/Top/H/EqPort/EqFour.lean. Later F' F, Later GO H, Later G2 H,
and that what was heard stands at the record of "objects": the link's frame. That all claims are
worth 0 at H's world: the link's one equation. RowsLaw: whoever turns runs into rows on oracle
messages.

Limits. A tie: it has no error term. None of the public premises is shown at a value here. lm is 5.
Over a field.
RowsLaw whole is not payable at the closed caller of Johnson/Desc/First/Look/K3Caller.lean (no seat
for an earlier link's array): there use k3Out_of_rows, Johnson/Top/H/K3OutRows.lean.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3RowOut
import Johnson.Top.H.K3OutDigits
import OnBytes.Tie.Pv.Lookup.Forest.FoDig5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun OnBytes.DgP Cb.Fo Cb.LdLkp Finset
open _root_.Fo _root_.Fo.Eq
open VerifiableInference.Desc.First.TailClaims

/-- **The claims of "objects", as claims without runs.** -/
theorem objects_valC {S K : Type} [CommRing K] (ρ : Reading K) (fork : S → Option Fork)
    (heard : S → Option Heard) (lm : ℕ)
    (objects : ℕ → S → Except String (List Desc.Claim × S))
    (hW : K3RunIsWorth fork heard (fun k : Desc.Claim => k.form) lm objects
      (fun _ _ g jLK rsK ν _ => (endsOf g.shape lm jLK rsK).rows.map (rowRes ν)))
    (g : Heard) (F' : Fork) (jLK : ℕ) (hok : FoNums.ok g.shape = true) (sO : S)
    (clO : List Desc.Claim) (GO H : Fork) (rO : K3RanAt fork heard g F' objects sO clO GO)
    (lO : _root_.Fo.Later GO H) (hpl : ∀ k ∈ clO, k.runs = #[]) (ν : _root_.Fo.Pl → K)
    (entry : ℕ → ℕ → ℕ → K) (rs : Rounds K) (hI : HeardIs ρ g F' (endsOf g.shape lm jLK rs)) :
    clO.map (valC ρ (H.worldOf ρ (fun j => ν (.mask j)) entry)) =
      (endsOf g.shape lm jLK rs).rows.map (rowRes ν) := by
  obtain ⟨FO, fO, laO, szO⟩ := rO.later
  obtain ⟨nO, sO', runO, gO⟩ := rO.ran
  obtain ⟨GO', bO, _, _, _, _, vO⟩ :=
    hW K ρ g jLK rs F' FO nO sO sO' clO rO.heard fO hI laO hok szO runO
  obtain rfl : GO = GO' := Option.some.inj (gO.symm.trans bO)
  have w := vO H lO ν entry
  beta_reduce at w
  rw [← w]
  exact List.map_congr_left fun k hk => valC_plain ρ _ k (hpl k hk)

section
variable {K : Type} [Field K] (ρ : Reading K) {J₀ : Type} {front : ℕ}

/-- **The payer into the row out, at the digits.** -/
theorem k3Out_of_eq (tl tl1 tl2 : HTailF2) (F G1 G2 : Fork) (c c1 c2 : Array Desc.Claim)
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
    (Fc : Fork) (T : CoefOK tl Fc)
    (hRw : ∀ a ∈ allPieces tl, a.2.r0 + a.2.Rp ≤ (Fc.trees.getD a.2.tree {}).R)
    (en : Ent3 → J₀) (mk : ℕ → J₀) (μ₀ : J₀ → K) (entry : ℕ → ℕ → ℕ → K)
    (H : Fork) (hH : _root_.Fo.Later G2 H)
    (hL : RowsLaw ρ (coefAll tl g Fc) (H.worldOf ρ (fun j => μ₀ (mk j)) entry)
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
  obtain ⟨k1, k2, k3, k4, e, _, _, hA⟩ := claimsAre_of_eq ρ tl tl1 tl2 F G1 G2 c c1 c2 hJ hB g hg
    hs jLK rs F' hI h0 hok hT hF hfull h5 hn h63 hP hD Fc T hRw en mk μ₀ entry H hH hL clO
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

#print axioms VerifiableInference.OnPublicFiles.objects_valC
#print axioms VerifiableInference.OnPublicFiles.k3Out_of_eq
