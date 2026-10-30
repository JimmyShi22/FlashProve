-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Ends/AlgVec.lean: the vector of a lookup call with any function in the keys' place, and
its multilinear extension.
States, in the library's own words for a layers' segment (Inst/Model/FF):
(ext_vecF) for any function Fk of (family, layer, entry, position): the multilinear extension of the
call's vector that holds Fk where the library's key vector holds its keys, and the table's padding
value elsewhere (vecF), at any point ζ: the padding value times the padding's weight, plus, for each
layer and each family present there, the weighted extensions of Fk. The library's keyVec is vecF at
Fk := key (keyVec_eq_vecF).
(joinPart_linVec) The call's factor with the products left out: under the record Fits (which holds
that every read that the forms name has its rule value at this reading; and public numbers), what
Fits.joinPart_lines asks of the call, and hpad: the verifier's padding key of the call, read, is the
padding value of the library's table (a hypothesis here; hpad_of_word,
Johnson/Road/FormsKeysKV.lean, gives it from the word): the form that the verifier's Env.joinPart
returns for call q is worth alpha - q theta - the extension, at the call's own point, of vecF at Fk
:= lin, the affine part of the library's keys.
How: Fits.joinPart_lines (Johnson/Road/FormsKeysKF.lean), ext_three and sum_taken
(Johnson/Road/FormsKeysVec.lean); the three lemmas on vecF are that file's on keyVec (keyVec_pad,
cols_keyVec, ext_keyVec) and the library's keyVecAt, with Fk in the place of key.
Does not say: anything on the products in the keys; that a run's reads have their rule values.
Mind: what Fits.joinPart_lines asks of the call holds cd.lJ = lJ D cc, which needs the premise hfl
(the verifier's least number of columns passes the library's for no call). By the head of
Johnson/Road/FormsKeysWhole.lean hfl fails at the small example's shape for four calls:
joinPart_linVec does not apply to those four calls there. At the full-size example's shape and the
library's reference sizes hfl is a theorem (hfl_ref, Johnson/Road/FormsKeysRef.lean).
-/
import Johnson.Road.FormsKeysKF
import Johnson.Road.FormsKeysVec

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Alg

open Finset
open OnBytes.Model (Reading World Aff Seg CallD)
open OnBytes.Model.Layer (Env)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Fam LW key lin len call pos lJ aC isPad famAt fams famsIn present
  lut keyVec)
open Inst.Model.FFSeg.IndexFacts (mem_fams_iff pos_lt T_pos famAtPos)

section Vec

variable {K : Type} [Field K] (D : Dim) (tb : Tables) (Fk : Fam → ℕ → ℕ → ℕ → K)

/-- The vector of a call that holds Fk where the library's key vector holds its keys. -/
def vecF (c : Fin 8) (X : ℕ) : K :=
  match famAt D c (X / D.T % 2 ^ lJ D c) with
  | some (s, x) =>
    if present s (X / D.T / 2 ^ lJ D c) then Fk s (X / D.T / 2 ^ lJ D c) x (X % D.T)
    else (((lut tb c).pad : ℤ) : K)
  | none => (((lut tb c).pad : ℤ) : K)

/-- The library's key vector is vecF at the library's keys. -/
theorem keyVec_eq_vecF [scl : Scl] (t : Cell → K) (L0 : ℕ) (w : ℕ → LW K) (c : Fin 8) :
    keyVec D t tb L0 w c = vecF D tb (key D t tb L0 w) c := rfl

/-- The weighted sum of the extensions of Fk over the entries of family s at layer l. -/
def KEYF (ζ : ℕ → K) (s : Fam) (l : ℕ) : K :=
  ∑ x ∈ range (len D s), ewP D ζ s x *
    Blocks.ext D.lT (fun i => Fk s l x i) (uP D (call s) ζ)

/-- At a column that is padding in the layer the vector holds the table's padding value. -/
theorem vecF_pad {c : Fin 8} {l jj i : ℕ} (hjj : jj < 2 ^ lJ D c) (hi : i < D.T)
    (hp : isPad D c l jj = true) :
    vecF D tb Fk c ((l * 2 ^ lJ D c + jj) * D.T + i) = (((lut tb c).pad : ℤ) : K) := by
  have hT := T_pos D
  have hJ : 0 < 2 ^ lJ D c := Nat.two_pow_pos _
  have e1 : ((l * 2 ^ lJ D c + jj) * D.T + i) / D.T = l * 2 ^ lJ D c + jj := by
    rw [Nat.mul_comm, Nat.mul_add_div hT, Nat.div_eq_of_lt hi, Nat.add_zero]
  have e3 : (l * 2 ^ lJ D c + jj) / 2 ^ lJ D c = l := by
    rw [Nat.mul_comm, Nat.mul_add_div hJ, Nat.div_eq_of_lt hjj, Nat.add_zero]
  have e4 : (l * 2 ^ lJ D c + jj) % 2 ^ lJ D c = jj := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hjj]
  unfold isPad at hp
  unfold vecF
  rw [e1, e3, e4]
  cases hf : famAt D c jj with
  | none => rfl
  | some a =>
    obtain ⟨s, x⟩ := a
    rw [hf] at hp
    have hp' : present s l = false := by simpa using hp
    simp only
    rw [if_neg (by rw [hp']; exact Bool.false_ne_true)]

/-- At the column of entry x of a family that is present in the layer the vector holds Fk. -/
theorem vecFAt (s : Fam) (l x i : ℕ) (hx : x < len D s) (hi : i < D.T)
    (hp : present s l = true) :
    vecF D tb Fk (call s) ((l * 2 ^ lJ D (call s) + pos D s x) * D.T + i) = Fk s l x i := by
  have hT := T_pos D
  have hJ : 0 < 2 ^ lJ D (call s) := Nat.two_pow_pos _
  have hpos := pos_lt D hx
  have e1 : ((l * 2 ^ lJ D (call s) + pos D s x) * D.T + i) / D.T =
      l * 2 ^ lJ D (call s) + pos D s x := by
    rw [Nat.mul_comm, Nat.mul_add_div hT, Nat.div_eq_of_lt hi, Nat.add_zero]
  have e2 : ((l * 2 ^ lJ D (call s) + pos D s x) * D.T + i) % D.T = i := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hi]
  have e3 : (l * 2 ^ lJ D (call s) + pos D s x) / 2 ^ lJ D (call s) = l := by
    rw [Nat.mul_comm, Nat.mul_add_div hJ, Nat.div_eq_of_lt hpos, Nat.add_zero]
  have e4 : (l * 2 ^ lJ D (call s) + pos D s x) % 2 ^ lJ D (call s) = pos D s x := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hpos]
  have e5 : famAt D (call s) (pos D s x) = some (s, x) :=
    (famAtPos D (call s) (pos D s x) s x).mpr ⟨rfl, hx, rfl⟩
  unfold vecF
  rw [e1, e2, e3, e4, e5]
  simp only
  rw [if_pos hp]

/-- One layer of the vector. -/
theorem cols_vecF (c : Fin 8) (ζ : ℕ → K) (l : ℕ) :
    ∑ jj ∈ range (2 ^ lJ D c), ewcP D c ζ jj *
        Blocks.ext D.lT (fun i => vecF D tb Fk c ((l * 2 ^ lJ D c + jj) * D.T + i))
          (uP D c ζ) =
      (((lut tb c).pad : ℤ) : K) *
          (∑ jj ∈ range (2 ^ lJ D c), if isPad D c l jj then ewcP D c ζ jj else 0) +
        ((famsIn c l).map fun s => KEYF D Fk ζ s l).sum := by
  have h1 : ∀ jj ∈ range (2 ^ lJ D c), ewcP D c ζ jj *
        Blocks.ext D.lT (fun i => vecF D tb Fk c ((l * 2 ^ lJ D c + jj) * D.T + i))
          (uP D c ζ) =
      (((lut tb c).pad : ℤ) : K) * (if isPad D c l jj then ewcP D c ζ jj else 0) +
        (if isPad D c l jj then 0 else ewcP D c ζ jj *
          Blocks.ext D.lT (fun i => vecF D tb Fk c ((l * 2 ^ lJ D c + jj) * D.T + i))
            (uP D c ζ)) := by
    intro jj hjj
    cases hp : isPad D c l jj with
    | false => simp
    | true =>
      rw [Blocks.ext_congr (w := fun _ => (((lut tb c).pad : ℤ) : K))
        (fun i hi => vecF_pad D tb Fk (mem_range.mp hjj) hi hp), Blocks.ext_const]
      simp [mul_comm]
  rw [sum_congr rfl h1, sum_add_distrib, ← mul_sum, sum_taken D c l fun jj => ewcP D c ζ jj *
    Blocks.ext D.lT (fun i => vecF D tb Fk c ((l * 2 ^ lJ D c + jj) * D.T + i)) (uP D c ζ)]
  congr 2
  refine List.map_congr_left fun s hs => ?_
  obtain ⟨hs1, hs2⟩ := List.mem_filter.mp (show s ∈ (fams c).filter (present · l) from hs)
  have hc : call s = c := mem_fams_iff.mp hs1
  subst hc
  unfold KEYF
  refine sum_congr rfl fun x hx => ?_
  have e : Blocks.ext D.lT
        (fun i => vecF D tb Fk (call s) ((l * 2 ^ lJ D (call s) + pos D s x) * D.T + i))
        (uP D (call s) ζ) =
      Blocks.ext D.lT (fun i => Fk s l x i) (uP D (call s) ζ) :=
    Blocks.ext_congr (fun i hi => vecFAt D tb Fk s l x i (mem_range.mp hx) hi hs2) _
  rw [e]
  rfl

/-- **The multilinear extension of the vector of call c at any point ζ.** For all sizes. -/
theorem ext_vecF (c : Fin 8) (ζ : ℕ → K) :
    Blocks.ext (aC D c) (vecF D tb Fk c) ζ =
      (((lut tb c).pad : ℤ) : K) * PADWP D c ζ +
        ∑ l ∈ range D.nl, elP D ζ l * ((famsIn c l).map fun s => KEYF D Fk ζ s l).sum := by
  rw [ext_three]
  unfold PADWP
  rw [mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun l _ => ?_
  rw [cols_vecF]
  ring

end Vec

section Call

variable {K : Type} [Field K] {ρ : Reading K} {W : World K} [scl : Scl] {v : Env} {D : Dim}
  {c : Cells K} {t : Cell → K} {low u : ℕ → K}

/-- **The call's factor with the products left out**, in the library's words. -/
theorem joinPart_linVec (F : Fits ρ W v D c t low u) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K)
    (alpha theta : E) (q : ℕ) (cd : CallD) (weighed : Array Bool) (cc : Fin 8) (fam : Seg → Fam)
    (C : CallFits v D cd weighed cc fam) (HS : ∀ s ∈ cd.segs, SegFits v D cd.lJ s (fam s))
    (hzk : v.y.h.ll + cd.lJ ≤ (v.zk.getD q #[]).size) (hls : v.y.ls ≤ cd.lJ)
    (hlow : ∀ j, j < v.y.ls → low j = pt ρ (v.zj q cd.lJ) (cd.lJ - v.y.ls + j))
    (hu : ∀ j, j < D.lT → u j = pt ρ (v.zk.getD q #[]) (D.lL + lJ D cc + j))
    (hpad : ρ.val (ofF ((v.y.cl.getD q {}).tauAt (v.y.cl.getD q {}).t0)) =
      (((lut tb cc).pad : ℤ) : K))
    {f : Aff} (h : v.joinPart alpha theta q cd weighed = some f) :
    f.value ρ W = ρ.val alpha - (q : K) * ρ.val theta -
      Blocks.ext (aC D cc) (vecF D tb (lin D t tb L0 w) cc) (pt ρ (v.zk.getD q #[])) := by
  rw [F.joinPart_lines tb L0 w alpha theta q cd weighed cc fam C HS hzk hls hlow hu h, hpad,
    ext_vecF]
  have e : ∀ (ζ : ℕ → K) (s : Fam) (l : ℕ),
      KEYF D (lin D t tb L0 w) ζ s l = LINEP D t tb L0 w ζ s l := fun _ _ _ => rfl
  simp only [e]
  ring

end Call

#print axioms ext_vecF
#print axioms joinPart_linVec

end OnBytes.Road.Alg
