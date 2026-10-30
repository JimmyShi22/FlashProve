-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoPeelT.lean.
The maps from a file's own written rounds to the typed rounds of the sub-proofs' lookup.

OnBytes/Tie/Pv/Lookup/Forest/FoPeelForB.lean, OnBytes/Tie/Pv/Lookup/Forest/FoPeelMeets.lean and
OnBytes/Tie/Pv/Lookup/Forest/FoPeelYes.lean speak of written rounds PQ.uL (ckP .two) ds,
ds : List PQ.RD. A file's chains have the rounds uLT (ckP .two) ds, ds : List RDT
(OnBytes/Maker/Trees.lean), over which OnBytes/Tie/Pv/Lookup/Forest/FoPeelKitT.lean says the written
side again. This file says
the lookup's statements over these rounds. The readers (rkFor) are
OnBytes/Tie/Pv/Lookup/Forest/FoPeelForB.lean's, unturned.

Main names, each as its twin without the T:
  `lookCarryT h L Ex ds hl` : CarryS (uLT (ckP .two) ds) (forB GE h L V₀ V₀C).R.shape.
  `lookCarryT_read`, `lookCarryT_none`, `lookCarryT_fits`, `lookCarryT_view`.
  `meets_mapT`, `meets_planT`: written rounds ds with Plain (toRD d), whose entries are those of a
    plan that the planner finishes at Params.planForest for the shape h, meet Fo.specF h.
  `lookImgT`, `lookCarryT_pass`, `rvT_len`, `look_yesT`.
Under, does not say, whom the clauses of look_yesT serve: as the twins
(OnBytes/Tie/Pv/Lookup/Forest/FoPeelYes.lean's head).
What a run of Forest.pad leaves of the context's other fields: Fo.pad_still, Fo.look_leaf_still
(OnBytes/Tie/Pv/Lookup/Peel/FoPadStill.lean).
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoPeelKitT
import OnBytes.Tie.Pv.Lookup.Forest.FoPeelYes

set_option autoImplicit false

namespace Fo.Peel
open Iop IOR Prob Cb Cb.LdLkp TWhole TwV Tw Cb.Fo OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model
open OnBytes.PscRun OnBytes.Maker Run

section
variable {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀] (h : FoNums.Sh) (L : Lay GE St₀ J₀)
  (Ex : ExtSpec) (ds : List RDT)

/-- The maps from the file's written rounds ds to the lookup's typed rounds. -/
noncomputable def lookCarryT (hl : ds.length = (specF h).length) :
    CarryS (uLT (ckP .two) ds) (forB GE h L V₀ V₀C (Ex := Ex)).R.shape :=
  carT ds _ (specF h) (rkFor h L Ex).R hl

/-- The image, read as plain data, is the written transcript's plain data. -/
theorem lookCarryT_read (hM : List.Forall₂ MeetsT ds (specF h)) (τ : Tr (uLT (ckP .two) ds))
    (τ' : Tr (forB GE h L V₀ V₀C (Ex := Ex)).R.shape)
    (e : (lookCarryT h L Ex ds hM.length_eq).tr τ = some τ') :
    forFl h L Ex τ' = flWsT ds τ ∧ List.Forall₂ RFit (specF h) (flWsT ds τ) ∧
      YNonZero h (flWsT ds τ) ∧ passT (ckP .two) ds (Maker.rhoT (ckP .two) ds τ) = true := by
  obtain ⟨h1, h2, h3⟩ := carT_read ds _ (specF h) (rkFor h L Ex).R hM τ τ' e
  exact ⟨((rkFor h L Ex).read τ').symm.trans h1, h2, ynz_of_fit h2, h3⟩

/-- A written transcript without an image has failed a test of work. -/
theorem lookCarryT_none (hl : ds.length = (specF h).length) (τ : Tr (uLT (ckP .two) ds))
    (e : (lookCarryT h L Ex ds hl).tr τ = none) :
    passT (ckP .two) ds (Maker.rhoT (ckP .two) ds τ) = false :=
  carT_none ds _ (specF h) (rkFor h L Ex).R hl τ e

/-- The written rounds' error counts bear the typed ones. -/
theorem lookCarryT_fits (hM : List.Forall₂ MeetsT ds (specF h))
    (ε : Err (forB GE h L V₀ V₀C (Ex := Ex)).R.shape) (ε' : Err (uLT (ckP .two) ds))
    (hB : BearsT ds _ ε ε') : (lookCarryT h L Ex ds hM.length_eq).Fits ε ε' :=
  carT_fits ds _ (specF h) (rkFor h L Ex).R hM ε ε' hB

/-- The image, read as plain data, is the view's rounds read in the field. -/
theorem lookCarryT_view (hM : List.Forall₂ MeetsT ds (specF h)) (hA : ∀ d ∈ ds, NoAns d.items)
    (τ : Tr (uLT (ckP .two) ds)) (τ' : Tr (forB GE h L V₀ V₀C (Ex := Ex)).R.shape)
    (e : (lookCarryT h L Ex ds hM.length_eq).tr τ = some τ') :
    forFl h L Ex τ' = (rvT (ckP .two) ds τ).map (rdRV Reading.gl) :=
  (lookCarryT_read h L Ex ds hM τ τ' e).1.trans (flWsT_view ds τ hA).symm

end

theorem meets_mapT : ∀ ds : List RDT, (∀ d ∈ ds, Plain (toRD d)) →
    List.Forall₂ MeetsT ds ((ds.map (·.entry)).map spEnt)
  | [], _ => .nil
  | d :: ds, h => .cons (meets_entry (h d List.mem_cons_self))
      (meets_mapT ds fun d' hd => h d' (List.mem_cons_of_mem _ hd))

/-- Written rounds whose entries are the plan's meet the lookup's spec. -/
theorem meets_planT {s : Params.Setting} {sc : Params.Scope} (h : FoNums.Sh) (hv : 1 ≤ h.v)
    {P : Params.Planned}
    (hf : Params.finish s sc (Params.planForest ⟨h.v, h.d, FoNums.several h⟩) = .ok P)
    (ds : List RDT) (hd : ∀ d ∈ ds, Plain (toRD d))
    (he : ds.map (·.entry) = P.rounds.map (·.entry)) : List.Forall₂ MeetsT ds (specF h) := by
  have := meets_mapT ds hd
  rwa [he, plan_spec h hv hf] at this

section
variable {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀] (h : FoNums.Sh) (L : Lay GE St₀ J₀)
  (Ex : ExtSpec) (ds : List RDT)

/-- The typed transcript made of a written transcript's plain data. -/
noncomputable def lookImgT (τ : Tr (uLT (ckP .two) ds)) :
    Tr (forB GE h L V₀ V₀C (Ex := Ex)).R.shape :=
  img _ (specF h) (rkFor h L Ex).R (flWsT ds τ)

/-- Where every test of work passes, it is the image. -/
theorem lookCarryT_pass (hl : ds.length = (specF h).length) (τ : Tr (uLT (ckP .two) ds))
    (hp : passT (ckP .two) ds (Maker.rhoT (ckP .two) ds τ) = true) :
    (lookCarryT h L Ex ds hl).tr τ = some (lookImgT h L Ex ds τ) := by
  unfold lookCarryT lookImgT
  rw [carT_tr, if_pos hp]

theorem rvT_len (hv : 1 ≤ h.v) (hM : List.Forall₂ MeetsT ds (specF h))
    (hA : ∀ d ∈ ds, NoAns d.items) (τ : Tr (uLT (ckP .two) ds)) :
    (rvT (ckP .two) ds τ).length = (planF h).length := by
  rw [← spec_len h hv, (flWsT_fit ds (specF h) hM τ).length_eq, ← flWsT_view ds τ hA,
    List.length_map]

theorem look_yesT (calls : Array Call) (pub : Array Nat) (lid lm : ℕ) (Fk F' : Fork) (c c' : Ctx)
    (g : Forest.Heard) (mk : ℕ → J₀) (pl : ℕ → ℕ → J₀) (τ : Tr (uLT (ckP .two) ds))
    (rest : List Fmt.RoundView) (hr : Forest.pad calls pub lid Fk c = .ok ((g, F'), c'))
    (hS : ShapeOf calls pub lid h) (hF : Sized Fk) (hc : Clean c) (h5 : 5 ≤ lm)
    (hlm : lm ≤ h.kT + 5)
    (hmk : ∀ s, L.mkS s = mk (Fk.next + s))
    (hbc : ∀ t k j, k < h.NC →
      L.bc t k j = pl (FoNums.cellRC h lm (t, k, j)).1 (FoNums.cellRC h lm (t, k, j)).2)
    (hM : List.Forall₂ MeetsT ds (specF h)) (hA : ∀ d ∈ ds, NoAns d.items)
    (hp : passT (ckP .two) ds (Maker.rhoT (ckP .two) ds τ) = true)
    (hl : c.ch.left = rvT (ckP .two) ds τ ++ rest) :
    (lookCarryT h L Ex ds hM.length_eq).tr τ = some (lookImgT h L Ex ds τ) ∧
      forFl h L Ex (lookImgT h L Ex ds τ) = (rvT (ckP .two) ds τ).map (rdRV gl) ∧
      Took c (rvT (ckP .two) ds τ) c' ∧ c'.ch.left = rest ∧ g.shape = h ∧
      PadLeft h Fk F' g ∧
      HeardIs gl g F' (endsOf h lm Fk.next ((rvT (ckP .two) ds τ).map (rdRV gl))) ∧
      TieRows g F' lm Fk.next ((rvT (ckP .two) ds τ).map (rdRV gl)) ∧
      TiePlanes g F' lm Fk.next ((rvT (ckP .two) ds τ).map (rdRV gl)) ∧
      TieJoin g F' lm Fk.next ((rvT (ckP .two) ds τ).map (rdRV gl)) ∧
      ∀ a : St₀ × Ex.Str, ∃ x : TX (St₀ × GE) GE (Option J₀),
        (forB GE h L V₀ V₀C (Ex := Ex)).R.red.out a (lookImgT h L Ex ds τ) = some (x, a.2) ∧
        x.1 = (a.1, (endsOf h lm Fk.next ((rvT (ckP .two) ds τ).map (rdRV gl))).theta) ∧
        TieIff g F' lm Fk.next ((rvT (ckP .two) ds τ).map (rdRV gl)) L mk pl a.1 x := by
  have hg : g.shape = h := by
    obtain ⟨h0, a1, -, rfl⟩ := hS
    obtain ⟨h1, b1, -, e1⟩ := (hcOut2V GE gl calls pub lid lm Fk F' c c' g hr hF hc).1
    obtain rfl : h0 = h1 := Except.ok.inj (a1.symm.trans b1)
    exact e1
  subst hg
  have e := lookCarryT_pass g.shape L Ex ds hM.length_eq τ hp
  have hv := lookCarryT_view g.shape L Ex ds hM hA τ _ e
  have hy : YNonZero g.shape ((rvT (ckP .two) ds τ).map (rdRV gl)) := by
    rw [flWsT_view ds τ hA]
    exact (lookCarryT_read g.shape L Ex ds hM τ _ e).2.2.1
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
    look_leaf gl lm hr hF hc hl (rvT_len g.shape ds hv1 hM hA τ)
  obtain rfl := took_unique t0 t1
  exact ⟨e, hv, t1, t2, rfl, s2, s3, s4, s5, s6, fun a => (s7 hy Ex a).2.2 _ hv⟩

end
end Fo.Peel
