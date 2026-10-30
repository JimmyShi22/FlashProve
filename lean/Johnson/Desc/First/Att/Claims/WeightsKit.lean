-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/WeightsKit.lean: kind K5: builders for the ties of weights RowW, LongW
and ColW (Johnson/Desc/First/Att/Claims/AgreeAll.lean).

Main names: `WNums`; `tok_eq`: equality weights on the positions; `tok_tile`: weights on the
positions from weights on the tiles and a point in the tile; `eqT_tile`: the equality weights of a
point (tile | place in the tile) as a product; `rowW_of`, `longW_of`, `colW_of`.
By eqTab_at, tok_psi, tok_size, ptCut (Johnson/Road/Rows/AttEnds14Tiles.lean, AttTiles.lean),
lowOf_size, lowOf_value (AttReadHead.lean), eqN_cat, eqN_low (Cb/Pv/Att/Mean/), eqN_agree,
eqN_shift', eqTab_value.

Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Road.Rows.AttLinMore
import Johnson.Desc.First.Att.Claims.AgreeAll

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K5Law
open Finset
open OnBytes OnBytes.Model OnBytes.Attention OnBytes.Road OnBytes.Road.Rows
open Cb.Pv.Att
open Inst.Model.AttSeg (eqT cat)
open Cb.Pv.Att.End (TabW)

variable {Kf : Type} [Field Kf] {ρ : Reading Kf} {h : Attention.Heard}

/-- The numbers of the shape that the weights read. -/
structure WNums (h : Attention.Heard) : Prop where
  Z : Sizes h.S
  lT : (L5.dimOf h.S).lT = h.S.cf.lt
  T : (L5.dimOf h.S).T = h.S.T

/-- Equality weights on the positions. -/
theorem tok_eq (Nn : WNums h) {z : Array E} {v : ℕ → Kf} (hz : z.size = h.S.cf.lt)
    (hv : ∀ j < h.S.cf.lt, pt ρ z j = v j) :
    (eqTab z).size = h.S.T ∧ ∀ i < h.S.T, ρ.val ((eqTab z).getD i zeroE) = eqT (L5.dimOf h.S) v i := by
  refine ⟨by rw [OnBytes.Road.eqTab_size, hz, Nn.Z.T], fun i hi => ?_⟩
  unfold eqT
  rw [Nn.lT]
  exact eqTab_at ρ hz hv (by rw [← Nn.Z.T]; exact hi)

/-- Weights on the positions from weights w on the tiles and a point in the tile. -/
theorem tok_tile (Nn : WNums h) {hi lo : Array E} {w v : ℕ → Kf}
    (hhi : ∀ I < h.S.nT, ρ.val (hi.getD I zeroE) = w I) (hlo : lo.size = h.S.cf.lB)
    (hv : ∀ j < h.S.cf.lB, pt ρ lo j = v j) :
    (tok h.S hi lo).size = h.S.T ∧ ∀ i < h.S.T, ρ.val ((tok h.S hi lo).getD i zeroE) =
      Blocks.eqN (L5.dimOf h.S).lB 0 v (i % (L5.dimOf h.S).B) * w (i / (L5.dimOf h.S).B) :=
  ⟨tok_size _ _ _, fun _ hi' => tok_psi ρ Nn.Z Nn.T hhi hlo hv (by rw [Nn.T]; exact hi')⟩

/-- Equality weights of a point (vI | v), tile and place in the tile, as a product. -/
theorem eqT_tile (D : Inst.Model.AttSeg.Dim) (vI v : ℕ → Kf) (i : ℕ) :
    Blocks.eqN D.lB 0 v (i % D.B) * Blocks.eqN (D.lP + 1) 0 vI (i / D.B) = eqT D (cat (D.lP + 1) vI v) i := by
  show _ = Blocks.eqN (D.lP + 1 + D.lB) 0 _ i
  have hpos : 0 < 2 ^ D.lB := Nat.two_pow_pos _
  have hsplit : i = i / 2 ^ D.lB * 2 ^ D.lB + i % 2 ^ D.lB := (Nat.div_add_mod' i _).symm
  rw [eqN_cat]
  conv_rhs => rw [hsplit, eqN_low _ _ _ (Nat.mod_lt _ hpos)]
  rw [← hsplit]
  exact mul_comm _ _

theorem rowW_of {phi : Array E} {Ψ : ℕ → Kf}
    (hw : phi.size = h.S.T ∧ ∀ i < h.S.T, ρ.val (phi.getD i zeroE) = Ψ i) : RowW ρ h phi (.row Ψ) :=
  ⟨Ψ, rfl, hw.2⟩

/-- The weights of a table on blocks of features. vn: the library's point on the features of a head. -/
theorem longW_of (Nn : WNums h) {zc tokv : Array E} {vn Ψ : ℕ → Kf} (hz : zc.size = h.S.cf.ldh)
    (hn : ∀ j < h.S.cf.ldh, pt ρ zc j = vn j)
    (hw : tokv.size = h.S.T ∧ ∀ i < h.S.T, ρ.val (tokv.getD i zeroE) = Ψ i) :
    LongW ρ h zc tokv (.long (Blocks.eqN h.S.ls (h.S.cf.ldh - h.S.ls) vn) Ψ) := by
  refine ⟨_, Ψ, rfl, lowOf_size _ hz Nn.Z.ls, hw.1, fun c hc => ?_, hw.2⟩
  rw [lowOf_value ρ _ hz Nn.Z.ls hc]
  exact eqN_agree (fun k hk => hn _ (by have := Nn.Z.ls; omega)) c

/-- The weights of a table on as. n: the length of the point; v: the library's point. -/
theorem colW_of {z : Array E} {n : ℕ} {v : ℕ → Kf} (hz : z.size = n) (hn : h.S.cf.lmS ≤ n)
    (hv : ∀ j < n, n - h.S.cf.lmS ≤ j → pt ρ z j = v j) :
    ColW ρ h (lastN z h.S.cf.lmS) (.col (Blocks.eqN h.S.cf.lmS (n - h.S.cf.lmS) v)) := by
  refine ⟨_, rfl, fun k hk => ?_⟩
  have s1 : (lastCoords z h.S.cf.lmS).size = h.S.cf.lmS := by
    unfold lastCoords
    rw [Array.size_extract]
    omega
  unfold lastN
  rw [eqTab_value ρ _ k (by rw [s1]; exact hk), s1, ← eqN_shift' h.S.cf.lmS (n - h.S.cf.lmS)]
  refine eqN_agree (fun j hj => ?_) k
  rw [Nat.zero_add]
  unfold lastCoords
  rw [ptCut ρ z (Nat.le_refl _) (by omega), hz]
  exact hv _ (by omega) (by omega)

end K5Law
