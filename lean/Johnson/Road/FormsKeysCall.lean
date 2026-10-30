-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysCall.lean: what one call's factor in the lookup's join is worth on cells.

Johnson/Road/FormsKeysJoin.lean unfolds the verifier's joinPart into the forms of the call's
segments. Johnson/Road/FormsKeysAll.lean says what each of these forms is worth.
Johnson/Road/FormsKeysEq.lean shows that the weights which joinPart passes to a segment that is read
by blocks are one set of weights, if the segment's columns are aligned on blocks. This file puts
the three together.

Main definition: SegFits (what is asked of a segment of the call).
Main theorem: Fits.joinPart_lin.

What is not claimed: see Johnson/Road/FormsKeysKit.lean. That the segments of a call which the
verifier's layout has placed meet SegFits is not proved here. That the last coordinates of the
call's point are those of the point at which the long tables are read is a hypothesis: the verifier
tests it when it runs. The program does not import this file.
-/
import Johnson.Road.FormsKeysAll
import Johnson.Road.FormsKeysJoin
import Johnson.Road.FormsKeysEq

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading World Aff eqTab Seg CallD)
open OnBytes.Model.Layer (Env)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Fam LW lin len present isExp)

variable {K : Type} [Field K]

/-- Weights that are one set under a point stay one set under a point with the same first ls
coordinates. -/
theorem Blocked.congr {ρ : Reading K} {ew wh : Array E} {ls : ℕ} {low low' : ℕ → K}
    (h : Blocked ρ ew wh ls low') (e : ∀ j, j < ls → low j = low' j) : Blocked ρ ew wh ls low := by
  intro xh r hr
  rw [h xh r hr]
  congr 1
  exact eqN_congr' ls 0 (fun j hj => by rw [Nat.zero_add, e j hj]) r

/-- No family that is read by blocks has the segment of the rows of digits. -/
theorem segName_ne_ROW (s : Fam) (h : byBlocks s = true) : (segName s != "ROW") = true := by
  cases s <;> first | rfl | exact absurd h (by decide)

/-- What is asked of a segment s of a call with 2^lJ columns, for it to hold the family fam: the
name, the length, on which layers it exists, one column for each entry, and, if the family is read
by blocks, columns that are aligned on blocks. -/
structure SegFits (v : Env) (D : Dim) (lJ : ℕ) (s : Seg) (fam : Fam) : Prop where
  /-- the segment's name -/
  name : s.name = segName fam
  /-- its length -/
  n : s.n = len D fam
  /-- whether it exists only on layers with routed experts -/
  moe : s.moe = isExp fam
  /-- one column for each entry -/
  size : s.pos.size = s.n
  /-- aligned on blocks -/
  aligned : byBlocks fam = true → Aligned s v.y.ls lJ

variable {ρ : Reading K} {W : World K} [scl : Scl] {v : Env} {D : Dim} {c : Cells K} {t : Cell → K}
  {low u : ℕ → K}

/-- One call's factor in the lookup's join, on cells: alpha - q theta, less the padding key times
the weight of the padding's columns, less, for each segment and each layer on which it exists, the
layer's weight times the weighted sum of the extensions of the affine part of the library's keys of
the segment's family. fam: the family of each segment. -/
theorem Fits.joinPart_lin (F : Fits ρ W v D c t low u) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K)
    (alpha theta : E) (q : ℕ) (cd : CallD) (weighed : Array Bool) (fam : Seg → Fam)
    (HS : ∀ s ∈ cd.segs, SegFits v D cd.lJ s (fam s))
    (hzk : v.y.h.ll + cd.lJ ≤ (v.zk.getD q #[]).size) (hls : v.y.ls ≤ cd.lJ)
    (hlow : ∀ j, j < v.y.ls → low j = pt ρ (v.zj q cd.lJ) (cd.lJ - v.y.ls + j))
    {f : Aff} (h : v.joinPart alpha theta q cd weighed = some f) :
    f.value ρ W = ρ.val alpha - (q : K) * ρ.val theta -
      ρ.val (ofF ((v.y.cl.getD q {}).tauAt (v.y.cl.getD q {}).t0)) * padJ ρ v q cd weighed -
      (cd.segs.map fun s => ((List.range v.y.Lam).map fun lam =>
        if (s.moe && !v.isMoe lam) = true then 0
        else ρ.val (elJ v q lam) * ∑ x ∈ range (len D (fam s)),
          ρ.val ((ewJ v q cd s).getD x zeroE) *
            Blocks.ext D.lT (fun i => lin D t tb L0 w (fam s) lam x i) u).sum).sum := by
  refine joinPart_value ρ W F.num v alpha theta q cd weighed _ ?_ h
  intro s hs lam g hlam hskip hg
  have S := HS s hs
  have hp : present (fam s) lam = true := by
    rw [S.moe, F.isMoe] at hskip
    unfold present
    cases h1 : isExp (fam s) with
    | false => rfl
    | true =>
      rw [h1] at hskip
      simpa using hskip
  have hsz : (ewJ v q cd s).size = len D (fam s) := by
    unfold ewJ Env.ewFrom
    rw [Array.size_map, S.size, S.n]
  rw [S.name] at hg
  refine F.line_lin tb L0 w (fam s) lam (F.Lam ▸ hlam) hp hsz (fun hb => ?_) hg
  have A := S.aligned hb
  obtain ⟨k, hk⟩ := A.whole
  have hpos : 0 < 2 ^ v.y.ls := by positivity
  have hmod : (s.n % v.y.S2 == 0 && s.name != "ROW") = true := by
    rw [F.S2, hk, Nat.mul_mod_left, S.name, segName_ne_ROW _ hb]
    rfl
  have hwh : whJ v q cd s = Env.ewhFrom (2 ^ v.y.ls) (eqTab (v.zj q (cd.lJ - v.y.ls))) s := by
    unfold whJ
    rw [if_pos hmod, F.S2]
  refine ⟨hsz, ?_, ?_⟩
  · rw [hwh]
    unfold Env.ewhFrom
    rw [Array.size_map, Array.size_range, ← S.n, hk, Nat.mul_div_cancel _ hpos]
  · rw [hwh]
    exact (blocked_join ρ v q cd.lJ hzk hls s A).congr hlow

#print axioms Fits.joinPart_lin

end OnBytes.Road
