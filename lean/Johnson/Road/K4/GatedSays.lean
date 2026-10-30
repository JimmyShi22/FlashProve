--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/GatedSays.lean: from the in-claims of the two product layers of the gated products
to what the batched sumcheck's end asks of the never-sent vectors.

The end of the batched sumcheck (Johnson/Road/FormsKeysEnd.lean, `EndsTrue`; in the letters of a
public record, `Pub34.Gated`, Johnson/Road/Rows/LayerEnds34.lean) asks that the hidden end value of
each never-sent vector is that vector's extension at the end point's coordinates of its panel. The
two product layers are there to show it. Johnson/Road/Rows/GatedStartsProofs.lean proves what the
sums on which the layers run are (gatedFirstIn, gatedSecondIn). Here the two are joined.

  `VirtOK`: which panels bear a never-sent vector: a panel without the selector bears number 0
      alone,
      and has the down product's bits; a panel with the selector bears a number 1 + lm, lm below
      LamM, and has the bits of a routed expert's hidden units in a column.
  `virt_panels`, `virt_placed`: the verifier's own list of panels has it, placed or not.
  `gated_says`: IF the hidden value under sH1 is the sum on which the first layer runs, AND each
      hidden value under sH1 + 1 + lm is the extension of the honest routed vector, THEN the two
      clauses of `EndsTrue` on never-sent vectors hold at the honest vectors `hvOf`, at every panel
      of the placed list.

Limits. Implications in one world: no draw, no soundness. The two premises are what the product
layers' sumchecks and the draw of the fresh point over the routed layers are there to show: nothing
of that is shown here. Five public equations on the layout's numbers are premises. Plain functions
that K4's own text calls (panelsA, panelsT, placePanels) alone are spoken of.
-/
import Johnson.Road.Rows.GatedStartsProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Finset
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (SBlk Lay placePanels Panels PanelEnv panelA panelT panelsA panelsT
  downFrom)
open Inst.Model.FFSeg (Dim Cell slV upV lF lFe)

/-- Which panels bear a never-sent vector, and their bits. -/
structure VirtOK (y : Lay) (b : SBlk) : Prop where
  plain : b.tri = false → ∀ k, b.virt = some k →
    k = 0 ∧ b.wy = ceilLog2 y.h.f ∧ b.w = ceilLog2 y.Lam + ceilLog2 y.h.f
  tri : b.tri = true → ∀ k, b.virt = some k →
    (∃ lm, lm < y.LamM ∧ k = 1 + lm) ∧ b.wy = ceilLog2 y.h.fe

theorem virt_plain (y : Lay) (ec : E) (claim : ℕ) (moeSet : Bool) (ny : ℕ)
    (A B : Option (ℕ → ℕ → Option Aff)) (wt : ℕ → E) (virt : Option ℕ) (s : Panels)
    (hv : ∀ k, virt = some k → k = 0 ∧ moeSet = false ∧ ny = y.h.f)
    (hs : ∀ b ∈ s.bl.toList, VirtOK y b) :
    ∀ b ∈ (Layer.plain y ec claim moeSet ny A B wt virt s).bl.toList, VirtOK y b := by
  intro b hb
  unfold Layer.plain at hb
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hb
  rcases hb with hb | rfl
  · exact hs b hb
  · refine ⟨fun _ k hk => ?_, fun h => by cases h⟩
    obtain ⟨e0, e1, e2⟩ := hv k hk
    subst e1
    subst e2
    exact ⟨e0, rfl, rfl⟩

theorem virt_tri (y : Lay) (ec : E) (claim nk : ℕ) (sl : Array E) (xx : Array Aff)
    (virt : Option ℕ) (wt : E) (s : Panels)
    (hv : ∀ k, virt = some k → (∃ lm, lm < y.LamM ∧ k = 1 + lm) ∧ nk = y.h.fe)
    (hs : ∀ b ∈ s.bl.toList, VirtOK y b) :
    ∀ b ∈ (Layer.tri y ec claim nk sl xx virt wt s).bl.toList, VirtOK y b := by
  intro b hb
  unfold Layer.tri at hb
  simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hb
  rcases hb with hb | rfl
  · exact hs b hb
  · refine ⟨fun h => (by cases h), fun _ k hk => ?_⟩
    obtain ⟨e0, e1⟩ := hv k hk
    subst e1
    exact ⟨e0, rfl⟩

theorem no_virtP {y : Lay} {m : Bool} {ny : ℕ} :
    ∀ k, (none : Option ℕ) = some k → k = 0 ∧ m = false ∧ ny = y.h.f := fun _ e => nomatch e

theorem no_virtT {y : Lay} {nk : ℕ} :
    ∀ k, (none : Option ℕ) = some k → (∃ lm, lm < y.LamM ∧ k = 1 + lm) ∧ nk = y.h.fe :=
  fun _ e => nomatch e

theorem virt_panelA (p : PanelEnv) (ec : E) (el : Array E) (sn : String) (s : Panels)
    (hs : ∀ b ∈ s.bl.toList, VirtOK p.v.y b) :
    ∀ b ∈ (panelA p ec el sn s).bl.toList, VirtOK p.v.y b := by
  simp only [panelA]
  split_ifs <;> first
    | exact hs
    | exact virt_plain _ _ _ _ _ _ _ _ _ _ no_virtP hs
    | exact virt_plain _ _ _ _ _ _ _ _ _ _
        (fun k e => ⟨(Option.some.inj e).symm, rfl, rfl⟩) hs

theorem virt_panelT (p : PanelEnv) (ec : E) (el : Array E) (sn : String) (s s' : Panels)
    (hs : ∀ b ∈ s.bl.toList, VirtOK p.v.y b) (h : panelT p ec el sn s = some s') :
    ∀ b ∈ s'.bl.toList, VirtOK p.v.y b := by
  simp only [panelT] at h
  split_ifs at h <;> first
    | (cases h; exact hs)
    | (cases h; exact virt_plain _ _ _ _ _ _ _ _ _ _ no_virtP hs)
    | (obtain ⟨_, _, h⟩ := bind_some h; cases h
       exact virt_plain _ _ _ _ _ _ _ _ _ _ no_virtP hs)
    | exact foldlM_inv_mem (fun s : Panels => ∀ b ∈ s.bl.toList, VirtOK p.v.y b) _ _
        (fun s lm s' hm hs h => by
          first
            | (cases h
               exact virt_tri _ _ _ _ _ _ _ _ _
                 (fun k e => ⟨⟨lm, List.mem_range.mp hm, (Option.some.inj e).symm⟩, rfl⟩) hs)
            | (obtain ⟨_, _, h⟩ := bind_some h; cases h
               exact virt_tri _ _ _ _ _ _ _ _ _ no_virtT hs))
        _ _ hs h

/-- The verifier's own list of panels. -/
theorem virt_panels (p : PanelEnv) (TS : List ℕ) {pans : Panels}
    (h : panelsT p TS (panelsA p {}) = some pans) : ∀ b ∈ pans.bl.toList, VirtOK p.v.y b := by
  have h0 : ∀ b ∈ ({} : Panels).bl.toList, VirtOK p.v.y b :=
    fun b hb => absurd hb List.not_mem_nil
  have hA : ∀ b ∈ (panelsA p {}).bl.toList, VirtOK p.v.y b := by
    unfold panelsA
    refine foldl_inv (fun s : Panels => ∀ b ∈ s.bl.toList, VirtOK p.v.y b) _ (fun s q hs => ?_)
      _ _ h0
    exact foldl_inv (fun s : Panels => ∀ b ∈ s.bl.toList, VirtOK p.v.y b) _
      (fun s g hs => virt_panelA p _ _ _ s hs) _ _ hs
  unfold panelsT at h
  refine foldlM_inv (fun s : Panels => ∀ b ∈ s.bl.toList, VirtOK p.v.y b) _
    (fun s q s' hs e => ?_) _ _ _ hA h
  exact foldlM_inv (fun s : Panels => ∀ b ∈ s.bl.toList, VirtOK p.v.y b) _
    (fun s g s' hs e => virt_panelT p _ _ _ s s' hs e) _ _ _ hs e

/-- The placing changes nothing of it. -/
theorem virt_placed {y : Lay} {bl : Array SBlk} (R : ∀ b ∈ bl.toList, VirtOK y b) :
    ∀ b ∈ (placePanels bl).1.toList, VirtOK y b := by
  intro b hb
  obtain ⟨b0, h0, o, rfl⟩ := placed_from bl b hb
  exact ⟨(R b0 h0).plain, (R b0 h0).tri⟩

variable {K : Type} [Field K]

/-- **The two clauses on never-sent vectors, at the honest vectors.** -/
theorem gated_says (ρ : Reading K) (W : World K) (D : Dim) (t : Cell → K) {p : PanelEnv}
    {TS : List ℕ} {pans : Panels} (hp : panelsT p TS (panelsA p {}) = some pans)
    (rs ztF rt : Array E) (sH1 : ℕ)
    (hf : ceilLog2 p.v.y.h.f = lF D) (hL : ceilLog2 p.v.y.Lam = D.lL)
    (hfe : ceilLog2 p.v.y.h.fe = lFe D) (hrs : D.lL + lF D ≤ rs.size)
    (i1 : W.slot sH1 = Blocks.ext (D.lL + lF D + D.lT) (fun X => slV D t X * upV D t X)
      (pt ρ (downFrom rs (D.lL + lF D) ++ ztF)))
    (i2 : ∀ lm, lm < p.v.y.LamM → W.slot (sH1 + 1 + lm) =
      ∑ yv ∈ range (2 ^ lFe D), eqR ρ rs 0 (lFe D) yv *
        Rows.hvOf D t (pt ρ ztF) (pt ρ rt) (1 + lm) yv) :
    ∀ b ∈ (placePanels pans.bl).1.toList,
      (∀ k, b.tri = true → b.virt = some k → W.slot (sH1 + k) =
        ∑ yv ∈ range (2 ^ b.wy), eqR ρ rs 0 b.wy yv *
          Rows.hvOf D t (pt ρ ztF) (pt ρ rt) k yv) ∧
      (∀ k, b.tri = false → b.virt = some k → W.slot (sH1 + k) =
        gsum ρ rs b (fun i yv => Rows.hvOf D t (pt ρ ztF) (pt ρ rt) k (i * 2 ^ b.wy + yv))) := by
  intro b hb
  have V := virt_placed (virt_panels p TS hp) b hb
  constructor
  · intro k ht hk
    obtain ⟨⟨lm, hlm, rfl⟩, hw⟩ := V.tri ht k hk
    rw [hw, hfe, ← Nat.add_assoc]
    exact i2 lm hlm
  · intro k ht hk
    obtain ⟨rfl, hwy, hw⟩ := V.plain ht k hk
    rw [hf] at hwy
    rw [hL, hf] at hw
    have e := Rows.gatedFirstIn K ρ D t rs ztF b (pt ρ rt) hwy hw (by rw [hw]; exact hrs)
    rw [hw] at e
    rw [Nat.add_zero, i1]
    exact e

#print axioms virt_panels
#print axioms gated_says

end OnBytes.Road.K4
