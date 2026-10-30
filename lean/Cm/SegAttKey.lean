-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegAttKey.lean: the key families of the attention segment as families (`Fam`) of
Cb/Req/ReqSpec.lean: what is required of each, and the four that are affine in cells: 1M, 1D, 3X, 4
(Inst/Model/Att/Trace.lean: `key1`, `key3X`, `key4`; `keyVec`).

Part of the arithmetisation of the model. The cells (the entries of one matrix for each segment)
must meet zero tests (identities) and table lookups (keys) at the vertices of Boolean cubes
(`SegSpec.Holds`, Cb/Req/ReqSpec.lean). A family has one value at each vertex B < 2^v of a cube; a
vertex beyond the index set is called dead. A call c : Fin 4 has a table (`AttSeg.lut`) and a key
vector (`AttSeg.keyVec`), whose keys are the entries at the indices in pieces (below
`AttSeg.Dim.used`).
The families 2M, 2D, 3W, which have sums of products of cells, are in Cm/SegAttKeySum.lean.

Main names:
  `AttKeyOK Φ g u0 tb c off N f`: at the vertex B the value of f is entry off + B of the key vector
    of call c (that of Inst/Model/Att/Trace.lean, over E, at the trace `tAtt g A`) if B < N, and
    row 0 of the table if not; N ≤ 2^v; well-formed; it reads only places of valid cells that the
    segment reads, own or borrowed (`IsAtt`).
  `fam1` (at the regions M and D), `fam3X`, `fam4`: the four families; `fam1M_ok`, `fam1D_ok`,
    `fam3X_ok`, `fam4_ok`: each has `AttKeyOK`.

Vertices: B = b · 2^l + y, b the pair (layer, number of the query head among those of its key/value
head: `AttSeg.Dim.nb`) in 5 bits (20 are live), y the inner index of the piece: the number of a
vertex is the index in the family's part of the key vector.
u0 is the number of live rows of the exponential (a size of Inst/Model/Att/Index.lean; in the
segment's keys, tables and identities only the second table, `tau2`, and the constants
`AttSeg.Dim.cutC` and `AttSeg.Om` read it).
Terms: lean/GLOSSARY.md.
-/
import Cm.SegAttKeyKit

set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg
open Cb Inst.Model Inst.Model.All Finset Ex
open Inst.Model.AttSeg (Raw Reg)

variable [scl : Scl] {X F E : Type} [Field F] [Field E] [Algebra F E]

/-- the value of a family at its dead vertices: row 0 of the table of the call, in E. (Not the
padding value of Inst/Model/Att/Trace.lean: that one is shown to be an entry of the second table
under u0 < 2^16 (`AttSeg.pad_mem`, which says nothing for u0 ≥ 2^16); row 0 is an entry for every
table of scales.) (At the other three tables the padding value is row 0: `tau1`, `tau3`, `tau4`,
Inst/Model/Tables.lean.) -/
def padA (u0 : ℕ) (tb : Tables) (c : Fin 4) : E := (((AttSeg.lut (DU u0) tb c).row 0 : ℤ) : E)

/-- What the theorems on `attSpec` (Cm/TargetSegAtt.lean) require of a family of keys. -/
structure AttKeyOK (Φ : IdxFmt F) (g u0 : ℕ) (tb : Tables) (c : Fin 4)
    (off N : ℕ) (f : Cb.Fam X E) : Prop where
  le : N ≤ 2 ^ f.v
  val : ∀ (x₀ : X) (W : ℕ → ℕ → F) (A : ℕ → ℕ → ℕ → E) (B : ℕ), f.val Φ x₀ W A B =
    if B < N then AttSeg.keyVec (DU u0) tb (tAtt g A) c (off + B) else padA u0 tb c
  wf : f.WF Φ
  places : ∀ p ∈ f.places, IsAtt g p

/-! ## Tools -/

omit scl in
theorem twoFam_fst {R : Type} {nb l l' : ℕ} {f f' : ℕ → ℕ → R} {pad : R}
    {B : ℕ} (h : B < nb * 2 ^ l) :
    AttSeg.twoFam nb l l' f f' pad (0 + B) = f (bOf l B) (yOf l B) := by
  rw [Nat.zero_add]
  exact if_pos h

omit scl in
theorem twoFam_snd {R : Type} {nb l l' : ℕ} {f f' : ℕ → ℕ → R} {pad : R}
    {B : ℕ} (h : B < nb * 2 ^ l') :
    AttSeg.twoFam nb l l' f f' pad (nb * 2 ^ l + B) = f' (bOf l' B) (yOf l' B) := by
  unfold AttSeg.twoFam
  rw [if_neg (by omega), Nat.add_sub_cancel_left, if_pos h]
  rfl

omit scl in
theorem nb_le (l : ℕ) : DA.nb * 2 ^ l ≤ 2 ^ (5 + l) := by
  rw [pow_add]
  exact Nat.mul_le_mul_right _ (by decide)

omit scl in
theorem bOf_lt {l B : ℕ} (h : B < DA.nb * 2 ^ l) : bOf l B < DA.nb :=
  Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at h)

/-- the form K b y at a live vertex, a constant at a dead one -/
def live (l : ℕ) (pad : E) (K : ℕ → ℕ → CForm E) : ℕ → CForm E := fun B =>
  if B < DA.nb * 2 ^ l then K (bOf l B) (yOf l B) else cK pad

omit scl in
theorem val_live (l : ℕ) (pad : E) (K : ℕ → ℕ → CForm E) (A : ℕ → ℕ → ℕ → E) (B : ℕ) :
    (live l pad K B).val A = if B < DA.nb * 2 ^ l then (K (bOf l B) (yOf l B)).val A else pad := by
  unfold live
  rw [val_ite, val_cK]

omit scl in
theorem pl_live {l : ℕ} {pad : E} {K : ℕ → ℕ → CForm E} {P : Cb.Place → Prop}
    (h : ∀ b < DA.nb, ∀ y < 2 ^ l, AllPl P (K b y)) (B : ℕ) : AllPl P (live l pad K B) :=
  AllPl.ite (fun hB => h _ (bOf_lt hB) _ (yOf_lt l B)) fun _ => AllPl.cK _

omit scl in
theorem sum_range_ite {M : Type} [AddCommMonoid M] {m n : ℕ} (h : m ≤ n) (G : ℕ → M) :
    ∑ j ∈ range n, (if j < m then G j else 0) = ∑ j ∈ range m, G j := by
  rw [← sum_filter]
  refine sum_congr ?_ fun _ _ => rfl
  ext j
  rw [mem_filter, mem_range, mem_range]
  exact ⟨fun h' => h'.2, fun h' => ⟨lt_of_lt_of_le h' h, h'⟩⟩

omit scl in
theorem ite_val {N B : ℕ} {a b pad : E} (h : B < N → a = b) :
    (if B < N then a else pad) = if B < N then b else pad := by
  split_ifs with hB
  · exact h hB
  · rfl

/-! ### Indices are in range -/

omit scl in
theorem pos_lt {a r : ℕ} (ha : a < DA.nBlk) (hr : r < DA.B) : DA.B * a + r < DA.T := by
  unfold AttSeg.Dim.T
  nlinarith
omit scl in
theorem lam_lt {b : ℕ} (hb : b < DA.nb) : DA.lamOf b < DA.nl := by
  have h : b < DA.nl * DA.na := hb
  exact Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at h)
omit scl in
theorem mI_lt (x : ℕ) : DA.mI x < DA.B := Nat.mod_lt _ DA.B_pos
omit scl in
theorem mJ_lt (x : ℕ) : DA.mJ x < DA.B := Nat.mod_lt _ DA.B_pos
omit scl in
theorem slotM {x : ℕ} (he : ¬ DA.EmptyM x) :
    DA.colBlk (DA.mP x) (DA.mS x) < DA.rowBlk (DA.mP x) (DA.mS x) ∧
    DA.rowBlk (DA.mP x) (DA.mS x) < DA.nBlk := by
  have h1 : DA.mS x < DA.nBlk := Nat.mod_lt _ DA.nBlk_pos
  have h2 : DA.mS x ≠ DA.nBlk - 1 := he
  have h := DA.blk_of_slot (P := DA.mP x) (s := DA.mS x) (Nat.mod_lt _ DA.hP_pos) (by omega)
  exact ⟨h.1, h.2.1⟩
omit scl in
theorem iM_lt {x : ℕ} (he : ¬ DA.EmptyM x) : DA.iM x < DA.T := pos_lt (slotM he).2 (mI_lt x)
omit scl in
theorem jM_lt {x : ℕ} (he : ¬ DA.EmptyM x) : DA.jM x < DA.T :=
  pos_lt (lt_trans (slotM he).1 (slotM he).2) (mJ_lt x)
omit scl in
theorem iD_lt (x : ℕ) : DA.iD x < DA.T := pos_lt (Nat.mod_lt _ DA.nBlk_pos) (mI_lt x)
omit scl in
theorem jD_lt (x : ℕ) : DA.jD x < DA.T := pos_lt (Nat.mod_lt _ DA.nBlk_pos) (mJ_lt x)

/-! ### The key vectors of the four calls, unfolded -/

section
variable {R : Type} [CommRing R] (D : AttSeg.Dim) (tb : Tables) (t : Raw → R)
theorem keyVec0 :
    AttSeg.keyVec D tb t 0 =
      AttSeg.twoFam D.nb D.lM D.lD (AttSeg.key1 t .M) (AttSeg.key1 t .D)
        (((AttSeg.lut D tb 0).pad : ℤ) : R) := by
  unfold AttSeg.keyVec
  rfl
theorem keyVec1 :
    AttSeg.keyVec D tb t 1 =
      AttSeg.twoFam D.nb D.lM D.lD (AttSeg.key2 D t .M) (AttSeg.key2 D t .D)
        (((AttSeg.lut D tb 1).pad : ℤ) : R) := by
  unfold AttSeg.keyVec
  rfl
theorem keyVec2 :
    AttSeg.keyVec D tb t 2 =
      AttSeg.twoFam D.nb D.lW D.lX
        (fun b y =>
          AttSeg.key3W D t (y / D.ch / D.T / D.nG) b (y / D.ch / D.T % D.nG)
            (y / D.ch % D.T) (y % D.ch))
        (fun b y => AttSeg.key3X D t b (y / D.T) (y % D.T))
        (((AttSeg.lut D tb 2).pad : ℤ) : R) := by
  unfold AttSeg.keyVec
  rfl
theorem keyVec3 :
    AttSeg.keyVec D tb t 3 =
      AttSeg.twoFam D.nb D.l4 0
        (fun b y => AttSeg.key4 t b (y / D.ch / D.T) (y / D.ch % D.T) (y % D.ch))
        (fun _ _ => (((AttSeg.lut D tb 3).pad : ℤ) : R)) (((AttSeg.lut D tb 3).pad : ℤ) : R) := by
  unfold AttSeg.keyVec
  rfl
end

variable (g u0 : ℕ) (tb : Tables) (Φ : IdxFmt F)

/-! ## 1M, 1D -/

def k1F (ρ : Reg) (b x : ℕ) : CForm E :=
  cr0 g ρ b x + ((2 : E) ^ 20) • cr1 g ρ b x + ((2 : E) ^ 40) • cfl g ρ b x

def fam1 (ρ : Reg) : Cb.Fam X E :=
  affFam (5 + DA.lReg ρ) (live (DA.lReg ρ) (padA u0 tb 0) (k1F g ρ))

omit scl in
theorem pl_k1F (ρ : Reg) :
    ∀ b < DA.nb, ∀ x < 2 ^ DA.lReg ρ, InAtt g (k1F g ρ b x : CForm E) := fun _ hb _ hx =>
  ((inAtt_cr0 g hb hx).add ((inAtt_cr1 g hb hx).smul _)).add ((inAtt_cfl g hb hx).smul _)

theorem fam1M_ok :
    AttKeyOK Φ g u0 tb 0 0 (DA.nb * 2 ^ DA.lM) (fam1 (X := X) (E := E) g u0 tb .M) where
  le := nb_le _
  val := fun x₀ W A B => by
    unfold fam1
    rw [affFam_val, val_live, keyVec0]
    refine ite_val fun h => Eq.trans ?_ (twoFam_fst h).symm
    simp [k1F, AttSeg.key1]
  wf := affFam_wf _ _ Φ
  places := affFam_places fun B _ => pl_live (pl_k1F g .M) B

theorem fam1D_ok :
    AttKeyOK Φ g u0 tb 0 (DA.nb * 2 ^ DA.lM) (DA.nb * 2 ^ DA.lD)
      (fam1 (X := X) (E := E) g u0 tb .D) where
  le := nb_le _
  val := fun x₀ W A B => by
    unfold fam1
    rw [affFam_val, val_live, keyVec0]
    refine ite_val fun h => Eq.trans ?_ (twoFam_snd h).symm
    simp [k1F, AttSeg.key1]
  wf := affFam_wf _ _ Φ
  places := affFam_places fun B _ => pl_live (pl_k1F g .D) B

/-! ## 3X, 4 -/

def k3XF (b y : ℕ) : CForm E :=
  ((2 : E) ^ (16 - DA.lT)) •
    (cK (((y % DA.T : ℕ) : E)) -
      cSum DA.lT fun k => ((2 : E) ^ k) • cib g k b (y / DA.T) (y % DA.T))

def fam3X : Cb.Fam X E := affFam (5 + DA.lX) (live DA.lX (padA u0 tb 2) (k3XF g))

omit scl in
theorem pl_k3XF : ∀ b < DA.nb, ∀ y < 2 ^ DA.lX, InAtt g (k3XF g b y : CForm E) := fun _ hb y hy =>
  ((AllPl.cK _).sub (AllPl.cSum fun _ hk => (inAtt_cib g hk hb (Nat.div_lt_of_lt_mul (by
    have : (2 : ℕ) ^ DA.lX = DA.T * DA.nG := by decide
    omega)) (Nat.mod_lt _ (by decide))).smul _)).smul _

theorem fam3X_ok :
    AttKeyOK Φ g u0 tb 2 (DA.nb * 2 ^ DA.lW) (DA.nb * 2 ^ DA.lX)
      (fam3X (X := X) (E := E) g u0 tb) where
  le := nb_le _
  val := fun x₀ W A B => by
    unfold fam3X
    rw [affFam_val, val_live, keyVec2]
    refine ite_val fun h => Eq.trans ?_ (twoFam_snd h).symm
    simp [k3XF, AttSeg.key3X] <;> rfl
  wf := affFam_wf _ _ Φ
  places := affFam_places fun B _ => pl_live (pl_k3XF g) B

def k4F (b y : ℕ) : CForm E :=
  cqh g b (y / DA.ch / DA.T) (y / DA.ch % DA.T) (y % DA.ch) +
    ((2 : E) ^ 20) • cqh' g b (y / DA.ch / DA.T) (y / DA.ch % DA.T) (y % DA.ch)

def fam4 : Cb.Fam X E := affFam (5 + DA.l4) (live DA.l4 (padA u0 tb 3) (k4F g))

omit scl in
theorem pl_k4F : ∀ b < DA.nb, ∀ y < 2 ^ DA.l4, InAtt g (k4F g b y : CForm E) := fun _ hb y hy => by
  have h1 : y / DA.ch / DA.T < DA.nG := by
    rw [Nat.div_div_eq_div_mul]
    exact Nat.div_lt_of_lt_mul (by
      have : (2 : ℕ) ^ DA.l4 = DA.ch * DA.T * DA.nG := by decide
      omega)
  have h2 : y / DA.ch % DA.T < DA.T := Nat.mod_lt _ (by decide)
  have h3 : y % DA.ch < DA.ch := Nat.mod_lt _ (by decide)
  exact (inAtt_cqh g hb h1 h2 h3).add ((inAtt_cqh' g hb h1 h2 h3).smul _)

theorem fam4_ok : AttKeyOK Φ g u0 tb 3 0 (DA.nb * 2 ^ DA.l4) (fam4 (X := X) (E := E) g u0 tb) where
  le := nb_le _
  val := fun x₀ W A B => by
    unfold fam4
    rw [affFam_val, val_live, keyVec3]
    refine ite_val fun h => Eq.trans ?_ (twoFam_fst h).symm
    simp [k4F, AttSeg.key4] <;> rfl
  wf := affFam_wf _ _ Φ
  places := affFam_places fun B _ => pl_live (pl_k4F g) B

end Cm.Seg
