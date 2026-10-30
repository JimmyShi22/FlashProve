-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegFFCellKeys.lean: the key families of the feed-forward segment with products of cells and no
weight: N1, N2 (stream times reciprocal: the low keys of the two normalisations' roundings), XR
(gate of the expert times input), DD and MR (which hold mr = ∑_e sel_e · lr_e), as families (`Fam`)
of Cb/Req/ReqSpec.lean.

Part of the arithmetisation of the model. The cells (the entries of one matrix for each segment)
must meet zero tests (identities) and table lookups (keys) at the vertices of Boolean cubes
(`SegSpec.Holds`, Cb/Req/ReqSpec.lean). A family has one value at each vertex b < 2^v of a cube.

Main names:
  `isQuad s`: s is one of the five.
  `qF`, `qG`, `qA g s ℓ x i`: affine forms qF, qG, qA: a mirror of `FFSeg.key`, line by line
    (`key_eq`).
  `quadSpec`, `quadKeyFam`: the family (`QSpec`, Cm/SegFFCellKit.lean). Vertices as in
    Cm/SegPilotAff.lean: b = (ℓ · 2^vx + x) · 2^10 + i; live if x is below the length and the
    family is present in layer ℓ; every other vertex is dead. mr is a sum atom over the ⌈log2 nx⌉
    bits of e, with the coefficient table [the vertex is live and e < nx].
  `quadKey_live` (V), `quadKey_dead` (D), `quadKey_wf` (W), `quadKey_places` (P), `quadKey_iff`: see
    their doc comments. That the five families have `KeyOK`: Cm/TargetSegFFCellKeys.lean.
Terms: lean/GLOSSARY.md.
-/
import Cm.SegFFCellKit
import Cm.SegFFCellLed
import Cm.SegPilotAff
import Cm.SegFF

set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg
open Cb Inst.Model Inst.Model.All Finset

variable [scl : Scl]

/-- The key families with products of cells and no weight. -/
def isQuad : FFSeg.Fam → Bool
  | .N1 | .N2 | .XR | .DD | .MR => true
  | _ => false

/-- the families that hold mr -/
def hasMr : FFSeg.Fam → Bool
  | .DD | .MR => true
  | _ => false

section
variable {E : Type} [Field E] (g : ℕ)

def qF : FFSeg.Fam → ℕ → ℕ → ℕ → CForm E
  | .N1, l, x, i => cXS g (2 * l) x i
  | .N2, l, x, i => cXS g (2 * l + 1) x i
  | .XR, l, _, i => cVal g .sc (l / 2) 0 i
  | _, _, _, _ => cK 0

def qG : FFSeg.Fam → ℕ → ℕ → ℕ → CForm E
  | .N1, l, _, i => LF.R (cLed g (2 * l) i)
  | .N2, l, _, i => LF.R (cLed g (2 * l + 1) i)
  | .XR, l, x, i => cVal g .m l x i
  | _, _, _, _ => cK 0

def qA : FFSeg.Fam → ℕ → ℕ → ℕ → CForm E
  | .N1, l, x, i =>
    cK (2 ^ ((DF.Pl l).n1.K - 1)) - ((2 : E) ^ (DF.Pl l).n1.K) • cVal g .aw l x i -
      ((2 : E) ^ 16) • cVal g .ra l x i
  | .N2, l, x, i =>
    cK (2 ^ ((DF.Pl l).n2.K - 1)) - ((2 : E) ^ (DF.Pl l).n2.K) • cVal g .mw l x i -
      ((2 : E) ^ 16) • cVal g .rm l x i
  | .XR, l, x, i => cK (2 ^ 15) - ((2 : E) ^ 16) • cVal g .xr (l / 2) x i
  | .DD, l, x, i =>
    cK 0 - cVal g .lr (l / 2) x i -
      cSum DF.nx fun e => if x < e then cVal g .sel (l / 2) e i else cK 0
  | .MR, l, _, i => cK (2 ^ 14) + ((2 : E) ^ 17) • cVal g .sc (l / 2) 0 i
  | _, _, _, _ => cK 0

/-- the number of bits of the number e of an expert -/
def wE : ℕ := Nat.clog 2 DF.nx

theorem nx_le : DF.nx ≤ 2 ^ wE := Nat.le_pow_clog (by norm_num) _

variable {X F : Type} [Field F] [Algebra F E] (tb : Tables)

/-- the inner vertex b' = b · 2^wE + e is live -/
def LiveE (s : FFSeg.Fam) (b' : ℕ) : Prop := Live s (b' / 2 ^ wE) ∧ b' % 2 ^ wE < DF.nx

instance (s : FFSeg.Fam) (b' : ℕ) : Decidable (LiveE s b') := by unfold LiveE; infer_instance

/-- The parts of the family. -/
def quadSpec (s : FFSeg.Fam) : QSpec X E where
  v := 2 + vxOf s + 10
  w := wE
  nS := if hasMr s then 1 else 0
  nQ := 1
  κ := fun _ _ b' => if LiveE s b' then 1 else 0
  p := fun _ b' =>
    if LiveE s b' then
      cVal g .sel ((dec3 (vxOf s) (b' / 2 ^ wE)).1 / 2)
        (b' % 2 ^ wE) (dec3 (vxOf s) (b' / 2 ^ wE)).2.2
    else cK 0
  q := fun _ b' =>
    if LiveE s b' then
      cVal g .lr ((dec3 (vxOf s) (b' / 2 ^ wE)).1 / 2)
        (b' % 2 ^ wE) (dec3 (vxOf s) (b' / 2 ^ wE)).2.2
    else cK 0
  a := fun b =>
    if Live s b then qA g s (dec3 (vxOf s) b).1 (dec3 (vxOf s) b).2.1 (dec3 (vxOf s) b).2.2
    else cK ((padOf tb s : ℤ) : E)
  f := fun _ b =>
    if Live s b then qF g s (dec3 (vxOf s) b).1 (dec3 (vxOf s) b).2.1 (dec3 (vxOf s) b).2.2
    else cK 0
  g := fun _ b =>
    if Live s b then qG g s (dec3 (vxOf s) b).1 (dec3 (vxOf s) b).2.1 (dec3 (vxOf s) b).2.2
    else cK 0

/-- The family. -/
def quadKeyFam (s : FFSeg.Fam) : Cb.Fam X E := (quadSpec (X := X) (E := E) g tb s).fam

variable (Φ : IdxFmt F) (x₀ : X) (W : ℕ → ℕ → F) (A : ℕ → ℕ → ℕ → E)

theorem div_mod_wE (b : ℕ) {e : ℕ} (he : e < 2 ^ wE) :
    (b * 2 ^ wE + e) / 2 ^ wE = b ∧ (b * 2 ^ wE + e) % 2 ^ wE = e := by
  constructor
  · rw [Nat.mul_comm, Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt he, Nat.add_zero]
  · rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt he]

/-- the value of the family, with the sum atom worked out -/
theorem quadKey_val (s : FFSeg.Fam) (b : ℕ) :
    (quadKeyFam (X := X) g tb s).val Φ x₀ W A b =
      if Live s b then
        (if hasMr s then FFSeg.mr DF (tA g A) ((dec3 (vxOf s) b).1 / 2) (dec3 (vxOf s) b).2.2
            else 0) +
          (qA g s (dec3 (vxOf s) b).1 (dec3 (vxOf s) b).2.1 (dec3 (vxOf s) b).2.2 : CForm E).val A +
          (qF g s (dec3 (vxOf s) b).1 (dec3 (vxOf s) b).2.1 (dec3 (vxOf s) b).2.2 : CForm E).val A *
            (qG g s (dec3 (vxOf s) b).1 (dec3 (vxOf s) b).2.1 (dec3 (vxOf s) b).2.2 : CForm E).val A
      else ((padOf tb s : ℤ) : E) := by
  unfold quadKeyFam
  rw [QSpec.fam_val]
  have hin : ∀ e ∈ range (2 ^ wE),
      (∑ n ∈ range (quadSpec (X := X) (E := E) g tb s).nS,
          (quadSpec (X := X) (E := E) g tb s).κ n x₀ (b * 2 ^ wE + e) *
            (((quadSpec (X := X) (E := E) g tb s).p n (b * 2 ^ wE + e)).val A *
              ((quadSpec (X := X) (E := E) g tb s).q n (b * 2 ^ wE + e)).val A)) =
        if e < DF.nx then
          (if Live s b ∧ hasMr s = true then
              FFSeg.val (tA g A) .sel ((dec3 (vxOf s) b).1 / 2) e (dec3 (vxOf s) b).2.2 *
                FFSeg.val (tA g A) .lr ((dec3 (vxOf s) b).1 / 2) e (dec3 (vxOf s) b).2.2
            else 0)
        else 0 := by
    intro e he
    obtain ⟨e1, e2⟩ := div_mod_wE b (mem_range.mp he)
    simp only [quadSpec, LiveE, e1, e2]
    by_cases hm : hasMr s = true
    · by_cases hL : Live s b
      · by_cases hx : e < DF.nx <;> simp [hm, hL, hx]
      · simp [hm, hL]
    · simp [hm]
  have hsum : (∑ j ∈ range (2 ^ (quadSpec (X := X) (E := E) g tb s).w),
        ∑ n ∈ range (quadSpec (X := X) (E := E) g tb s).nS,
          (quadSpec (X := X) (E := E) g tb s).κ
              n x₀ (b * 2 ^ (quadSpec (X := X) (E := E) g tb s).w + j) *
            (((quadSpec (X := X) (E := E) g tb s).p
                n (b * 2 ^ (quadSpec (X := X) (E := E) g tb s).w + j)).val A *
              ((quadSpec (X := X) (E := E) g tb s).q
                n (b * 2 ^ (quadSpec (X := X) (E := E) g tb s).w + j)).val A)) =
      if Live s b ∧ hasMr s = true then
        FFSeg.mr DF (tA g A) ((dec3 (vxOf s) b).1 / 2) (dec3 (vxOf s) b).2.2
      else 0 := by
    refine (sum_congr rfl hin).trans ?_
    rw [sum_range_ind nx_le]
    split_ifs
    · rfl
    · exact sum_const_zero
  rw [hsum]
  by_cases hL : Live s b
  · by_cases hm : hasMr s = true <;> simp [quadSpec, hL, hm]
  · simp [quadSpec, hL]

/-- for one of the five families, the key of Inst/Model/FF/Trace.lean is qA + qF · qG, plus mr for
DD and MR -/
theorem key_eq (L0 : ℕ) (w : ℕ → FFSeg.LW E) (s : FFSeg.Fam) (hs : isQuad s = true) (l x i : ℕ) :
    (if hasMr s then FFSeg.mr DF (tA g A) (l / 2) i else 0) + (qA g s l x i : CForm E).val A +
        (qF g s l x i : CForm E).val A * (qG g s l x i : CForm E).val A =
      FFSeg.key DF (tA g A) tb L0 w s l x i := by
  cases s <;> first
    | exact absurd hs (by decide)
    | (simp [hasMr, qA, qF, qG, FFSeg.key, Site.site, val_cLed, sum_filter]; try ring)

/-- (V) for one of the five families, at the vertex of an index (ℓ, x, i) of the family, the
family's value is the key of Inst/Model/FF/Trace.lean -/
theorem quadKey_live (L0 : ℕ) (w : ℕ → FFSeg.LW E) {s : FFSeg.Fam} (hs : isQuad s = true)
    {l x i : ℕ} (hp : FFSeg.present s l = true) (hx : x < FFSeg.len DF s) (hi : i < DF.T) :
    (quadKeyFam (X := X) g tb s).val Φ x₀ W A (enc3 (vxOf s) l x i) =
      FFSeg.key DF (tA g A) tb L0 w s l x i := by
  have hd : dec3 (vxOf s) (enc3 (vxOf s) l x i) = (l, x, i) :=
    dec3_enc3 (lt_of_lt_of_le hx (len_le s)) hi
  have hL : Live s (enc3 (vxOf s) l x i) := by
    unfold Live
    rw [hd]
    exact ⟨hx, hp⟩
  rw [quadKey_val, if_pos hL, hd]
  exact key_eq g tb A L0 w s hs l x i

/-- (D) at a dead vertex it is the padding value of the table -/
theorem quadKey_dead {s : FFSeg.Fam} {b : ℕ} (hb : ¬ Live s b) :
    (quadKeyFam (X := X) g tb s).val Φ x₀ W A b = ((padOf tb s : ℤ) : E) := by
  rw [quadKey_val, if_neg hb]

/-- (W) the family is well formed -/
theorem quadKey_wf (s : FFSeg.Fam) : (quadKeyFam (X := X) g tb s : Cb.Fam X E).WF Φ :=
  QSpec.fam_wf _ Φ

/-- in a family of the layers with experts, for ℓ < `DF.nl` in which the family is present, ℓ / 2
numbers such a layer -/
theorem half_of {s : FFSeg.Fam} {l : ℕ} (he : FFSeg.isExp s = true)
    (hl : l < DF.nl) (hp : FFSeg.present s l = true) : l / 2 < DF.ne :=
  FFSeg.CastValid.half_lt hl (by
    unfold FFSeg.present at hp
    rw [he] at hp
    simpa using hp)

/-- the three forms read only places of valid cells that the segment reads, own or borrowed
(`IsFF`), at an index of the family -/
theorem inFF_q (s : FFSeg.Fam) {l x i : ℕ} (hl : l < DF.nl) (hp : FFSeg.present s l = true)
    (hx : x < FFSeg.len DF s) (hi : i < DF.T) :
    InFF g (qA g s l x i : CForm E) ∧
    InFF g (qF g s l x i : CForm E) ∧
    InFF g (qG g s l x i : CForm E) := by
  have V : ∀ {Y : FFSeg.Arr} {a j : ℕ},
      a < Y.cnt DF → j < Y.width DF → InFF g (cVal g Y a j i : CForm E) :=
    fun ha hj => inFF_cVal g ha hj hi
  have hl4 : l < 4 := hl
  cases s
  case N1 =>
    exact ⟨((AllPl.cK _).sub ((V hl hx).smul _)).sub ((V hl hx).smul _),
      inFF_cXS g (show 2 * l ≤ 2 * 4 by omega) hx hi,
      LF.allPl_R (inFF_cLed g (show 2 * l < 2 * 4 by omega) hi)⟩
  case N2 =>
    exact ⟨((AllPl.cK _).sub ((V hl hx).smul _)).sub ((V hl hx).smul _),
      inFF_cXS g (show 2 * l + 1 ≤ 2 * 4 by omega) hx hi,
      LF.allPl_R (inFF_cLed g (show 2 * l + 1 < 2 * 4 by omega) hi)⟩
  case XR =>
    exact ⟨(AllPl.cK _).sub ((V (half_of rfl hl hp) hx).smul _),
      V (half_of rfl hl hp) Nat.one_pos,
      V hl hx⟩
  case DD =>
    exact ⟨((AllPl.cK _).sub (V (half_of rfl hl hp) hx)).sub
        (AllPl.cSum fun e he => AllPl.ite (fun _ => V (half_of rfl hl hp) he) fun _ => AllPl.cK _),
      AllPl.cK _, AllPl.cK _⟩
  case MR =>
    exact ⟨(AllPl.cK _).add ((V (half_of rfl hl hp) Nat.one_pos).smul _), AllPl.cK _, AllPl.cK _⟩
  all_goals exact ⟨AllPl.cK _, AllPl.cK _, AllPl.cK _⟩

/-- (P) the places read are places of valid cells that the segment reads -/
theorem quadKey_places (s : FFSeg.Fam) :
    ∀ p ∈ (quadKeyFam (X := X) g tb s : Cb.Fam X E).places, IsFF g p := by
  refine QSpec.fam_places _ (fun n hn b' hb' => ?_) (fun b hb => ?_) (fun n _ b hb => ?_)
  · have hm : hasMr s = true := by
      by_contra hm
      have : (quadSpec (X := X) (E := E) g tb s).nS = 0 := if_neg hm
      omega
    have he : FFSeg.isExp s = true := by cases s <;> first | rfl | exact absurd hm (by decide)
    have hb : b' / 2 ^ wE < 2 ^ (2 + vxOf s + 10) := by
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add]
      exact hb'
    exact ⟨AllPl.ite
        (fun hL => inFF_cVal g (half_of he (dec3_lt hb).1 hL.1.2) hL.2 (dec3_lt hb).2.2)
        fun _ => AllPl.cK _,
      AllPl.ite (fun hL => inFF_cVal g (half_of he (dec3_lt hb).1 hL.1.2) hL.2 (dec3_lt hb).2.2)
        fun _ => AllPl.cK _⟩
  · exact AllPl.ite (fun hL => (inFF_q g s (dec3_lt hb).1 hL.2 hL.1 (dec3_lt hb).2.2).1)
      fun _ => AllPl.cK _
  · exact ⟨AllPl.ite (fun hL => (inFF_q g s (dec3_lt hb).1 hL.2 hL.1 (dec3_lt hb).2.2).2.1)
        fun _ => AllPl.cK _,
      AllPl.ite (fun hL => (inFF_q g s (dec3_lt hb).1 hL.2 hL.1 (dec3_lt hb).2.2).2.2)
        fun _ => AllPl.cK _⟩

/-- For one of the five families, "every key of the family on the cube is in the set S" says
exactly "every key of the family of Inst/Model/FF/Trace.lean is", if the padding value is in S. -/
theorem quadKey_iff (L0 : ℕ) (w : ℕ → FFSeg.LW E) {s : FFSeg.Fam} (hs : isQuad s = true)
    (S : Set E) (hpad : ((padOf tb s : ℤ) : E) ∈ S) :
    (∀ b < 2 ^ (quadKeyFam (X := X) g tb s : Cb.Fam X E).v,
      (quadKeyFam (X := X) g tb s).val Φ x₀ W A b ∈ S) ↔
    ∀ l < DF.nl, FFSeg.present s l = true →
      ∀ x < FFSeg.len DF s, ∀ i < DF.T, FFSeg.key DF (tA g A) tb L0 w s l x i ∈ S := by
  constructor
  · intro h l hl hp x hx i hi
    rw [← quadKey_live g tb Φ x₀ W A L0 w hs hp hx hi]
    exact h _ (enc3_lt hl (lt_of_lt_of_le hx (len_le s)) hi)
  · intro h b hb
    by_cases hL : Live s b
    · obtain ⟨l, x, i, hl, hp, hx, hi, hd⟩ := live_cases s hb hL
      have he : b = enc3 (vxOf s) l x i := by
        have h1 : l = b / 2 ^ 10 / 2 ^ vxOf s := (congrArg Prod.fst hd).symm
        have h2 : x = b / 2 ^ 10 % 2 ^ vxOf s := (congrArg (fun q => q.2.1) hd).symm
        have h3 : i = b % 2 ^ 10 := (congrArg (fun q => q.2.2) hd).symm
        unfold enc3
        rw [h1, h2, h3, Nat.div_add_mod', Nat.div_add_mod']
      rw [he, quadKey_live g tb Φ x₀ W A L0 w hs hp hx hi]
      exact h l hl hp x hx i hi
    · rw [quadKey_dead g tb Φ x₀ W A hL]
      exact hpad

end

end Cm.Seg
