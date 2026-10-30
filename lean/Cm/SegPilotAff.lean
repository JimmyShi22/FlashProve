-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegPilotAff.lean: the key families of the feed-forward segment that are affine in cells, all 22
at once, as families (`Fam`) of Cb/Req/ReqSpec.lean.

Part of the arithmetisation of the model. The cells (the entries of one matrix for each segment)
must meet zero tests (identities) and table lookups (keys) at the vertices of Boolean cubes
(`SegSpec.Holds`, Cb/Req/ReqSpec.lean). A family (`Fam`) has one value at each vertex b < 2^v of a
cube; in this file it is the value of an affine form in cells (`affFam`, Cm/SegAlg.lean). Used in
the feed-forward segment (`affKey_ok`: Cm/TargetSegFF.lean).

Main names:
  `isAff s`: the family s of Inst/Model/FF/ (`FFSeg.Fam`) has keys that are affine in cells:
    digits, high digits of roundings, clamps and function tables (joint keys of argument and
    value), ledger bytes.
  `affKeyFam g tb s`: the family. Vertices: b = (ℓ · 2^vx + x) · 2^10 + i with 2 bits for ℓ,
    vx = ⌈log2 (length of the family)⌉ bits for x, 10 bits for i. A vertex is live if x is below
    the length and the family is present in layer ℓ; every other vertex is dead.
  `affKey_live` (V), `affKey_dead` (D), `affKey_wf` (W), `affKey_places` (P): see their docstrings.
    `affKey_iff`: for an affine family and a set S that has the padding value (`padOf`), "every key
    of the family on the cube is in S" says exactly "every key of the family of
    Inst/Model/FF/Trace.lean is".
Terms: lean/GLOSSARY.md.
-/
import Cm.SegPilotKit
import Inst.Model.FF.CastValid

set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg
open Cb Inst.Model Inst.Model.All Finset

variable [scl : Scl]

/-- The families whose keys are affine in cells. -/
def isAff : FFSeg.Fam → Bool
  | .UT | .LT | .GH | .UH | .OH | .DH | .VH | .LH | .QKH | .N1H | .N2H | .ROW | .SEL | .L3 | .G0 | .CN1 | .CN2 | .CQK | .CV | .CLR | .F | .CG => true
  | _ => false

section
variable {E : Type} [Field E] (g : ℕ)

/-- the high key of a rounding, as a form -/
def cHigh (rh : CForm E) (k top : ℕ) : CForm E := ((2 : E) ^ (top - k)) • rh
def cShigh (rh : CForm E) (k top : ℕ) : CForm E := ((2 : E) ^ (top - Site.up k)) • rh

/-- The key of an affine family as a form: the mirror of `FFSeg.key`. -/
def cKey : FFSeg.Fam → ℕ → ℕ → ℕ → CForm E
  | .UT, l, x, i => cVal g .up l x i + cK (2 ^ 15)
  | .LT, l, x, i => (2 : E) • (cVal g .lr (l / 2) x i + cK (2 ^ 14))
  | .GH, l, x, i => cShigh (cVal g .rg l x i) (FFSeg.kG DF l x) 24
  | .UH, l, x, i => cShigh (cVal g .ru l x i) (FFSeg.kU DF l x) 24
  | .OH, l, x, i => cShigh (cVal g .ro l x i) (DF.Pl l).ko 24
  | .DH, l, x, i => cShigh (cVal g .rd l x i) (DF.Pl l).kd 24
  | .VH, l, x, i => cShigh (cVal g .rv l x i) (DF.Pl l).kv 24
  | .LH, l, x, i => cShigh (cVal g .rl (l / 2) x i) (DF.Pl l).kr 24
  | .QKH, l, x, i => cShigh (cVal g .rqk l x i) (FFSeg.kQK DF l x) 32
  | .N1H, l, x, i => cHigh (cVal g .ra l x i) (DF.Pl l).n1.K 32
  | .N2H, l, x, i => cHigh (cVal g .rm l x i) (DF.Pl l).n2.K 32
  | .ROW, l, x, i =>
    (((Ledger.mu (x % FFSeg.nLedger) : ℤ) : E)) •
      cVal g .D (2 * l + x / FFSeg.nLedger) (x % FFSeg.nLedger) i
  | .SEL, l, x, i => (128 : E) • cVal g .sel (l / 2) x i
  | .L3, l, x, i => (32 : E) • cVal g .l3 (l / 2) x i
  | .G0, l, x, i => cVal g .g0 l x i + cK 128
  | .CN1, l, x, i =>
    (cVal g .aw l x i + cK (2 ^ 15)) + ((2 : E) ^ 28) • (cVal g .a l x i + cK (2 ^ 11))
  | .CN2, l, x, i =>
    (cVal g .mw l x i + cK (2 ^ 15)) + ((2 : E) ^ 28) • (cVal g .m l x i + cK (2 ^ 11))
  | .CQK, l, x, i =>
    (cVal g .qkw l x i + cK (2 ^ 15)) +
      ((2 : E) ^ 28) •
        ((if x < DF.dq then cVal g .q l x i else cVal g .kx l (x - DF.dq) i) + cK (2 ^ 11))
  | .CV, l, x, i =>
    (cVal g .vw l x i + cK (2 ^ 15)) + ((2 : E) ^ 28) • (cVal g .v l x i + cK (2 ^ 11))
  | .CLR, l, x, i =>
    (cVal g .ly (l / 2) x i + cK (2 ^ 15)) +
      ((2 : E) ^ 25) • (cVal g .lr (l / 2) x i - cVal g .l3 (l / 2) x i) + cK (2 ^ 39)
  | .F, l, x, i =>
    (cVal g .g0 l x i + (256 : E) • cVal g .gc l x i + cK (2 ^ 15)) +
      ((2 : E) ^ 28) • (cVal g .sl l x i + cK (2 ^ 12))
  | .CG, l, x, i =>
    (cVal g .gh l x i + cK 49152) + ((2 : E) ^ 28) • (cVal g .gc l x i + cK 128) + cK (2 ^ 40)
  | _, _, _, _ => cK 0

/-- For an affine family (`isAff s`), the form's value is the key of Inst/Model/FF/Trace.lean, at
the matrices read as a trace; for all matrices, tables, weights. -/
theorem val_cKey (A : ℕ → ℕ → ℕ → E) (tb : Tables) (L0 : ℕ) (w : ℕ → FFSeg.LW E) (s : FFSeg.Fam)
    (hs : isAff s = true) (l x i : ℕ) :
    (cKey g s l x i : CForm E).val A = FFSeg.key DF (tA g A) tb L0 w s l x i := by
  cases s <;> first
    | exact absurd hs (by decide)
    | simp [cKey, FFSeg.key, cShigh, cHigh, Site.shigh_eq, Site.high, FFSeg.led]

/-- The form `cKey` reads only places of valid cells that the segment reads, own or borrowed
(`IsFF`), at an index of the family. -/
theorem inFF_cKey (s : FFSeg.Fam) {l x i : ℕ} (hl : l < DF.nl) (hp : FFSeg.present s l = true)
    (hx : x < FFSeg.len DF s) (hi : i < DF.T) :
    InFF g (cKey g s l x i : CForm E) := by
  have half : FFSeg.isExp s = true → l / 2 < DF.ne := fun he => FFSeg.CastValid.half_lt hl (by
    unfold FFSeg.present at hp
    rw [he] at hp
    simpa using hp)
  have V : ∀ {X : FFSeg.Arr} {a j : ℕ},
      a < X.cnt DF → j < X.width DF → InFF g (cVal g X a j i : CForm E) :=
    fun ha hj => inFF_cVal g ha hj hi
  cases s
  case UT => exact (V hl hx).add (.cK _)
  case LT => exact ((V (half rfl) hx).add (.cK _)).smul _
  case GH => exact (V hl hx).smul _
  case UH => exact (V hl hx).smul _
  case OH => exact (V hl hx).smul _
  case DH => exact (V hl hx).smul _
  case VH => exact (V hl hx).smul _
  case LH => exact (V (half rfl) hx).smul _
  case QKH => exact (V hl hx).smul _
  case N1H => exact (V hl hx).smul _
  case N2H => exact (V hl hx).smul _
  case ROW =>
    have hx' : x < 2 * 99 := hx
    have hl' : l < 4 := hl
    exact (V (show 2 * l + x / 99 < 2 * 4 by omega)
      (show x % 99 < 99 from Nat.mod_lt _ (by norm_num))).smul _
  case SEL => exact (V (half rfl) hx).smul _
  case L3 => exact (V (half rfl) hx).smul _
  case G0 => exact (V hl hx).add (.cK _)
  case CN1 => exact ((V hl hx).add (.cK _)).add (((V hl hx).add (.cK _)).smul _)
  case CN2 => exact ((V hl hx).add (.cK _)).add (((V hl hx).add (.cK _)).smul _)
  case CQK =>
    have hx' : x < DF.dq + DF.dkv := hx
    have hq : InFF g
        ((if x < DF.dq then cVal g .q l x i else cVal g .kx l (x - DF.dq) i : CForm E)) := by
      by_cases h : x < DF.dq
      · rw [if_pos h]
        exact V hl h
      · rw [if_neg h]
        exact V hl (Nat.sub_lt_left_of_lt_add (Nat.le_of_not_lt h) hx')
    exact ((V hl hx).add (.cK _)).add ((hq.add (.cK _)).smul _)
  case CV => exact ((V hl hx).add (.cK _)).add (((V hl hx).add (.cK _)).smul _)
  case CLR =>
    exact (((V (half rfl) hx).add (.cK _)).add
      (((V (half rfl) hx).sub (V (half rfl) hx)).smul _)).add (.cK _)
  case F =>
    exact (((V hl hx).add ((V hl hx).smul _)).add (.cK _)).add (((V hl hx).add (.cK _)).smul _)
  case CG => exact (((V hl hx).add (.cK _)).add (((V hl hx).add (.cK _)).smul _)).add (.cK _)
  all_goals exact AllPl.cK _

/-! ## The families -/

variable {X F : Type} [Field F] [Algebra F E] (tb : Tables)

/-- the number of bits of the index x of a family -/
def vxOf (s : FFSeg.Fam) : ℕ := Nat.clog 2 (FFSeg.len DF s)

theorem len_le (s : FFSeg.Fam) : FFSeg.len DF s ≤ 2 ^ vxOf s := Nat.le_pow_clog (by norm_num) _

/-- the vertex is live: x is an index of the family, which is present in layer ℓ -/
def Live (s : FFSeg.Fam) (b : ℕ) : Prop :=
  (dec3 (vxOf s) b).2.1 < FFSeg.len DF s ∧ FFSeg.present s (dec3 (vxOf s) b).1 = true

instance (s : FFSeg.Fam) (b : ℕ) : Decidable (Live s b) := by unfold Live; infer_instance

/-- the padding value of the family's table -/
def padOf (s : FFSeg.Fam) : ℤ := (FFSeg.lut tb (FFSeg.call s)).pad

/-- the form at a vertex -/
def keyForm (s : FFSeg.Fam) (b : ℕ) : CForm E :=
  if Live s b then cKey g s (dec3 (vxOf s) b).1 (dec3 (vxOf s) b).2.1 (dec3 (vxOf s) b).2.2
  else cK ((padOf tb s : ℤ) : E)

/-- The family. -/
def affKeyFam (s : FFSeg.Fam) : Cb.Fam X E := affFam (2 + vxOf s + 10) (keyForm g tb s)

variable (Φ : IdxFmt F) (x₀ : X) (W : ℕ → ℕ → F) (A : ℕ → ℕ → ℕ → E)

/-- (V) for an affine family, at the vertex of an index (ℓ, x, i) of the family, the family's value
is the key of Inst/Model/FF/Trace.lean -/
theorem affKey_live (L0 : ℕ) (w : ℕ → FFSeg.LW E) {s : FFSeg.Fam} (hs : isAff s = true) {l x i : ℕ}
    (hp : FFSeg.present s l = true) (hx : x < FFSeg.len DF s) (hi : i < DF.T) :
    (affKeyFam (X := X) g tb s).val Φ x₀ W A (enc3 (vxOf s) l x i) =
      FFSeg.key DF (tA g A) tb L0 w s l x i := by
  have hd : dec3 (vxOf s) (enc3 (vxOf s) l x i) = (l, x, i) :=
    dec3_enc3 (lt_of_lt_of_le hx (len_le s)) hi
  have hL : Live s (enc3 (vxOf s) l x i) := by
    unfold Live
    rw [hd]
    exact ⟨hx, hp⟩
  unfold affKeyFam
  rw [affFam_val]
  unfold keyForm
  rw [if_pos hL, hd]
  exact val_cKey g A tb L0 w s hs l x i

/-- (D) at a dead vertex the family's value is the padding value of the table -/
theorem affKey_dead {s : FFSeg.Fam} {b : ℕ} (hb : ¬ Live s b) :
    (affKeyFam (X := X) g tb s).val Φ x₀ W A b = ((padOf tb s : ℤ) : E) := by
  unfold affKeyFam
  rw [affFam_val]
  unfold keyForm
  rw [if_neg hb, val_cK]

/-- every vertex of the cube is dead or the vertex of an index of the family -/
theorem live_cases (s : FFSeg.Fam) {b : ℕ} (hb : b < 2 ^ (2 + vxOf s + 10)) (hL : Live s b) :
    ∃ l x i, l < DF.nl ∧ FFSeg.present s l = true ∧ x < FFSeg.len DF s ∧
      i < DF.T ∧ dec3 (vxOf s) b = (l, x, i) :=
  ⟨_, _, _, (dec3_lt hb).1, hL.2, hL.1, (dec3_lt hb).2.2, rfl⟩

/-- (W) the family is well formed (`Fam.WF`) at every format Φ -/
theorem affKey_wf (s : FFSeg.Fam) : (affKeyFam (X := X) g tb s : Cb.Fam X E).WF Φ := affFam_wf _ _ Φ

/-- (P) the places read are places of valid cells that the segment reads -/
theorem affKey_places (s : FFSeg.Fam) :
    ∀ p ∈ (affKeyFam (X := X) g tb s : Cb.Fam X E).places, IsFF g p :=
  affFam_places fun b hb => by
    unfold keyForm
    refine AllPl.ite (fun hL => ?_) fun _ => AllPl.cK _
    exact inFF_cKey g s (dec3_lt hb).1 hL.2 hL.1 (dec3_lt hb).2.2

/-- For an affine family, "every key of the family on the cube is in the set S" says exactly "every
key of the family of Inst/Model/FF/Trace.lean is", if the padding value is in S. -/
theorem affKey_iff (L0 : ℕ) (w : ℕ → FFSeg.LW E) {s : FFSeg.Fam} (hs : isAff s = true)
    (S : Set E) (hpad : ((padOf tb s : ℤ) : E) ∈ S) :
    (∀ b < 2 ^ (affKeyFam (X := X) g tb s : Cb.Fam X E).v,
      (affKeyFam (X := X) g tb s).val Φ x₀ W A b ∈ S) ↔
    ∀ l < DF.nl, FFSeg.present s l = true →
      ∀ x < FFSeg.len DF s, ∀ i < DF.T, FFSeg.key DF (tA g A) tb L0 w s l x i ∈ S := by
  constructor
  · intro h l hl hp x hx i hi
    rw [← affKey_live g tb Φ x₀ W A L0 w hs hp hx hi]
    exact h _ (enc3_lt hl (lt_of_lt_of_le hx (len_le s)) hi)
  · intro h b hb
    by_cases hL : Live s b
    · obtain ⟨l, x, i, hl, hp, hx, hi, hd⟩ := live_cases s hb hL
      have he : b = enc3 (vxOf s) l x i := by
        have h1 : l = b / 2 ^ 10 / 2 ^ vxOf s := (congrArg Prod.fst hd).symm
        have h2 : x = b / 2 ^ 10 % 2 ^ vxOf s := (congrArg (fun q => q.2.1) hd).symm
        have h3 : i = b % 2 ^ 10 := (congrArg (fun q => q.2.2) hd).symm
        unfold enc3
        rw [h1, h2, h3, Nat.div_add_mod' , Nat.div_add_mod']
      rw [he, affKey_live g tb Φ x₀ W A L0 w hs hp hx hi]
      exact h l hl hp x hx i hi
    · rw [affKey_dead g tb Φ x₀ W A hL]
      exact hpad

end
end Cm.Seg
