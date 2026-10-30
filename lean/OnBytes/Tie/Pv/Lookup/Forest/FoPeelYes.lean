-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoPeelYes.lean.
A lookup's stretch of a file's written rounds, where the byte-level routine returns: the written
transcript has an image, and what the routine has heard is what the typed verifier puts out at
that image.

Main names:
  `lookImg h L Ex ds τ`: the typed transcript made of the written transcript's plain data by the
    readers of OnBytes/Tie/Pv/Lookup/Forest/FoPeelForB.lean.
  `lookCarry_pass`: where every test of work passes, lookImg is the image under lookCarry.
  `spec_len`, `rv_len`: if 1 ≤ h.v, the spec has as many rounds as the lookup's plan; where the
    written rounds meet the spec and send no answer to a sample, the view has as many rounds of
    them.
  `look_yes`: let the written rounds ds meet Fo.specF h and send no answer to a sample; let every
    test of work of the written transcript τ pass; let h be the shape that is made of the calls
    (ShapeOf); let Forest.pad return the record g from a state whose arrays have their sizes and a
    context on a view with no message open, whose rounds left begin with the view's rounds of τ;
    let the layout be the flat function's; let 5 ≤ lm ≤ h.kT + 5. Then: τ has the image lookImg;
    that image reads as the
    view's rounds of τ; the run has taken exactly these rounds and leaves the rest; g.shape = h;
    PadLeft, HeardIs, TieRows, TiePlanes and TieJoin hold at these rounds; and at every statement
    a the typed verifier puts out, at that image, a statement x with the caller's state and the
    shift in it, for which TieIff holds.
By Fo.hcTie, Fo.look_leaf, Fo.Peel.lookCarry_read and Fo.Peel.flWs_view.
Whom the clauses serve: TiePlanes, TieJoin and TieIff speak of Forest.planeClaims and of the form of
Forest.join: attention and the head call these. A caller that makes its claims on the planes and on
the keys by hand (the smallness test's lookup on the digits) is served by HeardIs and TieRows; one
that makes no claim on the keys but starts a sumcheck from that form (the layers) by these two and
TiePlanes.
What the run leaves of the context's other fields: Fo.pad_still, Fo.look_leaf_still
(OnBytes/Tie/Pv/Lookup/Peel/FoPadStill.lean).
Does not say: that the routine returns; that a test of work passes; anything on the rounds behind.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoPeelMeets
import OnBytes.Tie.Pv.Lookup.Forest.FoPeelLeaf
import OnBytes.Tie.Pv.Lookup.Forest.FoTieProof

set_option autoImplicit false

namespace Fo.Peel
open Iop IOR Prob Cb Cb.LdLkp TWhole TwV Tw Cb.Fo OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model
open OnBytes.PscRun Run

theorem spec_len (h : FoNums.Sh) (hv : 1 ≤ h.v) : (specF h).length = (planF h).length := by
  rw [← spec_sizes h hv]
  exact (List.length_map _).symm

section
variable {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀] (h : FoNums.Sh) (L : Lay GE St₀ J₀)
  (Ex : ExtSpec) (ds : List PQ.RD)

/-- The typed transcript made of a written transcript's plain data. -/
noncomputable def lookImg (τ : Tr (PQ.uL (ckP .two) ds)) :
    Tr (forB GE h L V₀ V₀C (Ex := Ex)).R.shape :=
  img _ (specF h) (rkFor h L Ex).R (flWs ds τ)

/-- Where every test of work passes, it is the image. -/
theorem lookCarry_pass (hl : ds.length = (specF h).length) (τ : Tr (PQ.uL (ckP .two) ds))
    (hp : PQ.passSL (ckP .two) ds (PQ.rhoSL (ckP .two) ds τ) = true) :
    (lookCarry h L Ex ds hl).tr τ = some (lookImg h L Ex ds τ) := by
  unfold lookCarry lookImg
  rw [car_tr, if_pos hp]

theorem rv_len (hv : 1 ≤ h.v) (hM : List.Forall₂ Meets ds (specF h))
    (hA : ∀ d ∈ ds, NoAns d.items) (τ : Tr (PQ.uL (ckP .two) ds)) :
    (PQ.rvSL (ckP .two) ds τ).length = (planF h).length := by
  rw [← spec_len h hv, (flWs_fit ds (specF h) hM τ).length_eq, ← flWs_view ds τ hA, List.length_map]

theorem look_yes (calls : Array Call) (pub : Array Nat) (lid lm : ℕ) (Fk F' : Fork) (c c' : Ctx)
    (g : Forest.Heard) (mk : ℕ → J₀) (pl : ℕ → ℕ → J₀) (τ : Tr (PQ.uL (ckP .two) ds))
    (rest : List Fmt.RoundView) (hr : Forest.pad calls pub lid Fk c = .ok ((g, F'), c'))
    (hS : ShapeOf calls pub lid h) (hF : Sized Fk) (hc : Clean c) (h5 : 5 ≤ lm)
    (hlm : lm ≤ h.kT + 5)
    (hmk : ∀ s, L.mkS s = mk (Fk.next + s))
    (hbc : ∀ t k j, k < h.NC →
      L.bc t k j = pl (FoNums.cellRC h lm (t, k, j)).1 (FoNums.cellRC h lm (t, k, j)).2)
    (hM : List.Forall₂ Meets ds (specF h)) (hA : ∀ d ∈ ds, NoAns d.items)
    (hp : PQ.passSL (ckP .two) ds (PQ.rhoSL (ckP .two) ds τ) = true)
    (hl : c.ch.left = PQ.rvSL (ckP .two) ds τ ++ rest) :
    (lookCarry h L Ex ds hM.length_eq).tr τ = some (lookImg h L Ex ds τ) ∧
      forFl h L Ex (lookImg h L Ex ds τ) = (PQ.rvSL (ckP .two) ds τ).map (rdRV gl) ∧
      Took c (PQ.rvSL (ckP .two) ds τ) c' ∧ c'.ch.left = rest ∧ g.shape = h ∧
      PadLeft h Fk F' g ∧
      HeardIs gl g F' (endsOf h lm Fk.next ((PQ.rvSL (ckP .two) ds τ).map (rdRV gl))) ∧
      TieRows g F' lm Fk.next ((PQ.rvSL (ckP .two) ds τ).map (rdRV gl)) ∧
      TiePlanes g F' lm Fk.next ((PQ.rvSL (ckP .two) ds τ).map (rdRV gl)) ∧
      TieJoin g F' lm Fk.next ((PQ.rvSL (ckP .two) ds τ).map (rdRV gl)) ∧
      ∀ a : St₀ × Ex.Str, ∃ x : TX (St₀ × GE) GE (Option J₀),
        (forB GE h L V₀ V₀C (Ex := Ex)).R.red.out a (lookImg h L Ex ds τ) = some (x, a.2) ∧
        x.1 = (a.1, (endsOf h lm Fk.next ((PQ.rvSL (ckP .two) ds τ).map (rdRV gl))).theta) ∧
        TieIff g F' lm Fk.next ((PQ.rvSL (ckP .two) ds τ).map (rdRV gl)) L mk pl a.1 x := by
  have hg : g.shape = h := by
    obtain ⟨h0, a1, -, rfl⟩ := hS
    obtain ⟨h1, b1, -, e1⟩ := (hcOut2V GE gl calls pub lid lm Fk F' c c' g hr hF hc).1
    obtain rfl : h0 = h1 := Except.ok.inj (a1.symm.trans b1)
    exact e1
  subst hg
  have e := lookCarry_pass g.shape L Ex ds hM.length_eq τ hp
  have hv := lookCarry_view g.shape L Ex ds hM hA τ _ e
  have hy : YNonZero g.shape ((PQ.rvSL (ckP .two) ds τ).map (rdRV gl)) := by
    rw [flWs_view ds τ hA]
    exact (lookCarry_read g.shape L Ex ds hM τ _ e).2.2.1
  obtain ⟨s1, s2, rv0, t0, s3, s4, s5, s6, s7⟩ :=
    hcTie calls pub lid lm Fk F' c c' g St₀ J₀ L mk pl hr hF hc h5 hlm hmk hbc
  have H : FoNums.ok g.shape = true := by
    obtain ⟨h0, hs0, hp0, he⟩ := s1
    rw [he]
    exact shape_ok hs0 hp0
  have hv1 : 1 ≤ g.shape.v := by
    have := ok_v H
    omega
  obtain ⟨t1, t2, -, -, -⟩ :=
    look_leaf gl lm hr hF hc hl (rv_len g.shape ds hv1 hM hA τ)
  obtain rfl := took_unique t0 t1
  exact ⟨e, hv, t1, t2, rfl, s2, s3, s4, s5, s6, fun a => (s7 hy Ex a).2.2 _ hv⟩

end
end Fo.Peel
