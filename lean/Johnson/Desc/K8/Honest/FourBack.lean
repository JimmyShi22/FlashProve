-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/FourBack.lean: THE SMALLNESS TEST: THE LIBRARY's EXCHANGE AT THE BATCHING's
FRONT (`k3PlanesKeys_of_rows`, Johnson/Top/H/Keep/EquationsPlanesKeys.lean: the first four claims of
the run "K8.equations" worth 0 give the lookup's items "planes" and "keys") WALKED BACKWARD: WHERE
THE HEARD STRUCTURE STANDS FOR SOME ROUNDS AND THE TWO ITEMS HOLD AT THESE ROUNDS, THE FOUR CLAIMS
ARE WORTH 0. It can be turned round because the library's `Fo.Eq.eq_four`
(Johnson/Top/H/EqPort/EqFour.lean) ends in EQUATIONS between the four values and the items' four
expressions. A lemma on the library's own text; none of its goals.

  **`rows_of_k3PlanesKeys`**   the premises of `k3PlanesKeys_of_rows` but "the claims are worth 0",
                   from the empty list of claims; rs with HeardIs ρ g F' (endsOf g.shape 5 jLK rs);
                   K3Planes … rs; K3Keys … rs ⊢ every claim of the list behind the two routines is
                   worth 0 in the world H.worldOf ρ (μ₀ ∘ mk) entry
Limits. AT ONE rs: that there is one is a premise (`K3Stands`, Johnson/Top/H/K3RowOut.lean): the
kind "lookup"'s. `DigRows` of the world's entries is a premise. The letters en, mk, μ₀, entry, H
are free. Nothing on which world a caller values the claims in.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Top.H.Keep.EquationsPlanesKeys

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.First.K8.Honest
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun OnBytes.DgP Cb.Fo Cb.LdLkp Finset
open _root_.Fo _root_.Fo.Eq
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound

variable {K : Type} [Field K] (ρ : OnBytes.Model.Reading K) {J₀ : Type} {front : ℕ}

/-- **The exchange, backward.** -/
theorem rows_of_k3PlanesKeys (tl tl1 tl2 : HTailF2) (F G1 G2 : Fork) (c1 c2 : Array Desc.Claim)
    (hJ : EqM.at (eqKeys tl) front F #[] = .ok ((tl1, G1), c1))
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
    (rs : Rounds K) (hI : HeardIs ρ g F' (endsOf g.shape 5 jLK rs))
    (hPl : K3Planes g.shape 5 jLK (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p)) rs)
    (hK : K3Keys g.shape 5 jLK (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
      (forK K (digL5 K tl en mk jLK Unit) () (zext μ₀)) rs) :
    ∀ k ∈ c2.toList, valC ρ (H.worldOf ρ (fun j => μ₀ (mk j)) entry) k = 0 := by
  have e0 : rdL ρ g.zb0 = (endsOf g.shape 5 jLK rs).zb0 := hI.zb0
  have e1 : rdL ρ g.zb1 = (endsOf g.shape 5 jLK rs).zb1 := hI.zb1
  obtain ⟨k1, k2, k3, k4, e, _, _, vJ, vP⟩ := eq_four ρ tl tl1 tl2 F G1 G2 #[] c1 c2 hJ hB g hg hs
    jLK rs F' hI h0 hok hT hF hfull h5 hn h63 hP hD en mk μ₀ entry (e0 ▸ hV.bz0) (e1 ▸ hV.bz1)
    hV.bz2 hV.piece H hH
  have hk := dig5_KFok_ends hT (by rw [hs]; exact hok) en mk jLK () 5 jLK rs
  rw [hs] at hk
  have hJ0 : claimJoin g.shape 5 jLK rs (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
      (fun c => (digKF tl en (fun c => (endsOf g.shape 5 jLK rs).zk.getD c []) c).val (zext μ₀)) =
      0 :=
    (_root_.Fo.claimJoin_congr g.shape 5 jLK rs
      (fun p => zext μ₀ (NumsEq.placeOf mk (plV tl en) p))
      (fun c => (digKF tl en (fun c => (endsOf g.shape 5 jLK rs).zk.getD c []) c).val (zext μ₀))
      (keysAt g.shape 5 jLK (forK K (digL5 K tl en mk jLK Unit) () (zext μ₀)) rs)
      fun q hq => hk (zext μ₀) q hq).trans
      (show claimJoin g.shape 5 jLK rs _ (keysAt g.shape 5 jLK
        (forK K (digL5 K tl en mk jLK Unit) () (zext μ₀)) rs) = 0 from hK)
  simp only [List.map_cons, List.map_nil] at vJ vP
  injection vJ with j1 _
  injection vP with a1 t1
  injection t1 with a2 t2
  injection t2 with a3 _
  intro k hk'
  rw [e] at hk'
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hk'
  rcases hk' with ((( hk' | rfl) | rfl) | rfl) | rfl
  · simp at hk'
  · exact j1.trans hJ0
  · exact a1.trans hPl.1
  · exact a2.trans hPl.2.1
  · exact a3.trans hPl.2.2

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.rows_of_k3PlanesKeys
