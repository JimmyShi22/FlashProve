-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/StackEnds.lean: CONDITIONAL.

Not shown here. THAT THE HONEST SIDE's TENSORS READ AS THE LIBRARY's VALUES (TensorIs): a hypothesis
here; C/GatedCells.lean has it (`tensor_is`), from hypotheses on the cells. The numbers GatedNums: a
hypothesis here; C/GatedNums.lean has them from K4Plan (`gatedNums_of_plan`). That the data of the
batched sumcheck's job hold what StackIs says: a hypothesis here; C/StackIs.lean has it where the
function that makes the data returns. In h1_read: four numbers of the verifier's panel of the down
product: a hypothesis here; C/DownPanel.lean has them. That the challenges rs and the points zt, rt
are what the verifier has heard: asked where the statements are laid into OpenedOwn (StackAt,
Johnson/Desc/ProofFile/Honest/K4/Law/W/RightStack.lean). THE END VALUES FROM 3 + LamM ON, the weight
claims' values, ARE NOT REACHED: no statement on them stands here. That the hypotheses can hold
together: no example is known. Nothing on a slot, a ledger or a mask. Nothing on soundness, on
completeness or on any other property. No property is claimed.

Two stretches of the end values of the batched sumcheck of the layers' own rounds (sub-protocol K4),
as the honest side computes them (`StackData.endsAt`, Johnson/Desc/K4/Honest/Stack.lean: [A0, H1] ++
H2 ++ [B0] ++ V), read into the field. The right sides are typed after those of the fields h1 and h2
of `OpenedOwn` (Johnson/Road/K4/W/OpenedOwn.lean); that the letters meet is held in
Law/W/RightStack.lean.

  `StackIs Q w rt SD tb`   what the job's data hold of the gated products.
  `range_sum`, `under_read`   loops read as sums.
  `hh_read`, `slup_at`, `gatedUnder_read`   the gated products' table, and its sums over the tokens,
      in the library's letters.
  `endsAt_parts`   the end values' list, cut.
  `h2_read`   end value 2 + lm: the value, at the challenges, of the routed experts' never-sent
      vector of layer 2 lm + 1.
  `h1_read`   end value 1: the value, at the challenges, of the first never-sent vector.
-/
import Johnson.Road.K4.C.Gated
import Johnson.Road.K4.C.Fold
import Johnson.Desc.K4.Honest.Stack
import Johnson.Road.Rows.GatedStartsProofs
import Johnson.Road.FormsKeysTab

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open Finset
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Lay Ten SBlk downFrom)
open Inst.Model.FFSeg (Dim Cell Arr lF lFe slV upV hhU)
open Blocks (ext)
open OnBytes.Desc.First.K4.Honest

/-- **What the job's data hold of the gated products.** rt: the second token sumcheck's end point;
tb: the two tables of the first product layer. This defines a hypothesis; the definition claims
nothing. -/
structure StackIs (Q : K4Pub) (w : K4In) (rt : Array E) (SD : StackData) (tb : Tab × Tab) :
    Prop where
  y : SD.S.v.y = Q.P.y
  tabs : gatedTabs Q w = some tb
  hh : SD.S.hh = (Array.range tb.1.size).map fun i => mulE (tb.1.getD i zeroE) (tb.2.getD i zeroE)
  hZ : SD.hZ = SD.S.gatedUnder (eqTab SD.S.zt)
  hR : SD.hR = SD.S.gatedUnder (eqTab rt)

/-! ## 1 Loops read as sums -/

/-- A list's sum over a range is the sum over the range. -/
theorem range_sum {M : Type} [AddCommMonoid M] (f : ℕ → M) :
    ∀ n, ((List.range n).map f).sum = ∑ i ∈ range n, f i
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, range_sum f n, sum_range_succ]
    simp

/-- The double loop under two arrays of weights. -/
theorem under_read (EI EY : Array E) (ni ny : ℕ) (f : ℕ → ℕ → E) :
    Reading.gl.val (StackData.under EI EY ni ny f) =
      ∑ i ∈ range ni, Reading.gl.val (EI.getD i zeroE) *
        ∑ yv ∈ range ny, Reading.gl.val (EY.getD yv zeroE) * Reading.gl.val (f i yv) := by
  unfold StackData.under
  rw [gl_foldl_maddE, Reading.gl.zero, zero_add, range_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [gl_foldl_maddE, Reading.gl.zero, zero_add, range_sum]

/-! ## 2 The gated products -/

section
variable {Q : K4Pub} {w : K4In} {t : Cell → Cb.Gl.E} {D : Dim} {ts tu : Ten}

/-- **An entry of the table of gated products.** -/
theorem hh_read (hts : Q.P.y.T_ "s" = some ts) (htu : Q.P.y.T_ "u" = some tu)
    (Ss : TensorIs Q w t .sl ts) (Su : TensorIs Q w t .up tu) (N : GatedNums Q D)
    {rt : Array E} {SD : StackData} {tb : Tab × Tab} (I : StackIs Q w rt SD tb) {X : ℕ}
    (hX : X < 2 ^ (D.lL + lF D + D.lT)) :
    Reading.gl.val (SD.S.hh.getD X zeroE) = slV D t X * upV D t X := by
  have e := gatedTabs_eq hts htu I.tabs
  have hs : tb.1.size = 2 ^ (D.lL + lF D + D.lT) := by
    rw [e, ← N.muH]
    simp [layerTab]
  rw [I.hh, getD_range_map _ _ _ _ (by rw [hs]; exact hX), Reading.gl.mul, e,
    tab1_read N Ss hX, tab1_read N Su hX]
  rfl

/-- The product of the library's two maps at the index of layer l, hidden unit j and token i. -/
theorem slup_at (l : ℕ) {j i : ℕ} (hj : j < 2 ^ lF D) (hi : i < D.T) :
    slV D t ((l * 2 ^ lF D + j) * D.T + i) * upV D t ((l * 2 ^ lF D + j) * D.T + i) =
      Inst.Model.FFSeg.hh t l j i := by
  have p2 : 0 < D.T := Nat.lt_of_le_of_lt (Nat.zero_le _) hi
  have a1 : ((l * 2 ^ lF D + j) * D.T + i) / D.T = l * 2 ^ lF D + j := by
    rw [Nat.mul_comm, Nat.mul_add_div p2, Nat.div_eq_of_lt hi, Nat.add_zero]
  have a2 : ((l * 2 ^ lF D + j) * D.T + i) % D.T = i := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hi]
  have p1 : 0 < 2 ^ lF D := Nat.two_pow_pos _
  have a3 : (l * 2 ^ lF D + j) / 2 ^ lF D = l := by
    rw [Nat.mul_comm, Nat.mul_add_div p1, Nat.div_eq_of_lt hj, Nat.add_zero]
  have a4 : (l * 2 ^ lF D + j) % 2 ^ lF D = j := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
  unfold slV upV Inst.Model.FFSeg.hh
  rw [a1, a2, a3, a4]
  ring

/-- **The gated products summed over the tokens under a point's weights**: the library's hhU. -/
theorem gatedUnder_read (hts : Q.P.y.T_ "s" = some ts) (htu : Q.P.y.T_ "u" = some tu)
    (Ss : TensorIs Q w t .sl ts) (Su : TensorIs Q w t .up tu) (N : GatedNums Q D)
    {rt : Array E} {SD : StackData} {tb : Tab × Tab} (I : StackIs Q w rt SD tb) (z : Array E)
    (hz : z.size = D.lT) {l j : ℕ} (hl : l < 2 ^ D.lL) (hj : j < 2 ^ lF D) :
    Reading.gl.val ((SD.S.gatedUnder (eqTab z)).getD (l * 2 ^ lF D + j) zeroE) =
      hhU D t l j (pt Reading.gl z) := by
  have hT : SD.S.v.y.T = D.T := by rw [I.y]; exact N.T
  have e := gatedTabs_eq hts htu I.tabs
  have hs : SD.S.hh.size = 2 ^ (D.lL + lF D) * D.T := by
    rw [I.hh, e]
    simp only [Array.size_map, Array.size_range, layerTab, Array.size_ofFn]
    rw [N.muH, Nat.pow_add]
    rfl
  have p2 : 0 < D.T := Nat.two_pow_pos _
  have hlj : l * 2 ^ lF D + j < 2 ^ (D.lL + lF D) := by
    rw [Nat.pow_add]
    calc l * 2 ^ lF D + j < (l + 1) * 2 ^ lF D := by rw [Nat.succ_mul]; omega
      _ ≤ 2 ^ D.lL * 2 ^ lF D := Nat.mul_le_mul_right _ hl
  unfold Sides.gatedUnder
  dsimp only
  rw [getD_range_map _ _ _ _ (by rw [hs, hT, Nat.mul_div_cancel _ p2]; exact hlj), gl_foldl_maddE,
    Reading.gl.zero, zero_add, range_sum, hT]
  unfold hhU Blocks.ext
  refine sum_congr rfl fun i hi => ?_
  have hi' : i < D.T := mem_range.mp hi
  have hX : (l * 2 ^ lF D + j) * D.T + i < 2 ^ (D.lL + lF D + D.lT) := by
    rw [Nat.pow_add (n := D.lT)]
    calc (l * 2 ^ lF D + j) * D.T + i < (l * 2 ^ lF D + j + 1) * D.T := by
          rw [Nat.succ_mul]; omega
      _ ≤ 2 ^ (D.lL + lF D) * D.T := Nat.mul_le_mul_right _ hlj
  rw [eqTab_value Reading.gl z i (by rw [hz]; exact hi'), hz,
    hh_read hts htu Ss Su N I hX, slup_at l hj hi']

end

/-! ## 3 The end values -/

/-- **The end values' list, cut.** -/
theorem endsAt_parts {SD : StackData} {rs : Array E} {e : List E} (he : SD.endsAt rs = some e) :
    ∃ (A0 B0 : E) (dn : SBlk) (V : List E),
      (SD.bl.find? fun b => !b.tri && b.virt.isSome) = some dn ∧
      e = [A0, StackData.under (eqLow rs dn.wy dn.w) (eqLow rs 0 dn.wy) dn.ni dn.ny
          fun i yv => SD.hZ.getD (i * SD.S.v.y.Pf + yv) zeroE] ++
        ((List.range SD.S.v.y.LamM).map fun lm =>
          StackData.under #[oneE] (eqLow rs 0 SD.S.v.y.lfe) 1 SD.S.v.y.h.fe
            fun _ yv => SD.hR.getD (SD.S.routedAt lm yv) zeroE) ++ [B0] ++ V := by
  unfold StackData.endsAt at he
  obtain ⟨fin, _, he⟩ := Option.bind_eq_some_iff.1 he
  obtain ⟨A0, _, he⟩ := Option.bind_eq_some_iff.1 he
  obtain ⟨B0, _, he⟩ := Option.bind_eq_some_iff.1 he
  obtain ⟨dn, hdn, he⟩ := Option.bind_eq_some_iff.1 he
  exact ⟨A0, B0, dn, _, hdn, (Option.some.inj he).symm⟩

section
variable {Q : K4Pub} {w : K4In} {t : Cell → Cb.Gl.E} {D : Dim} {ts tu : Ten}

/-- **END VALUE 2 + lm: THE ROUTED EXPERTS' NEVER-SENT VECTOR's VALUE AT THE CHALLENGES.** rs: the
challenges by bit; u: any point. CONDITIONAL: on every hypothesis named. -/
theorem h2_read (hts : Q.P.y.T_ "s" = some ts) (htu : Q.P.y.T_ "u" = some tu)
    (Ss : TensorIs Q w t .sl ts) (Su : TensorIs Q w t .up tu) (N : GatedNums Q D)
    {rt : Array E} {SD : StackData} {tb : Tab × Tab} (I : StackIs Q w rt SD tb)
    (hrt : rt.size = D.lT)
    {rs : Array E} (hrs : lFe D ≤ rs.size) {e : List E} (he : SD.endsAt rs = some e)
    (u : ℕ → Cb.Gl.E) :
    ∀ lm, lm < Q.P.y.LamM → Reading.gl.val (e.getD (2 + lm) zeroE) =
      ∑ yv ∈ range (2 ^ lFe D), eqR Reading.gl rs 0 (lFe D) yv *
        Rows.hvOf D t u (pt Reading.gl rt) (1 + lm) yv := by
  intro lm hlm
  obtain ⟨A0, B0, dn, V, _, rfl⟩ := endsAt_parts he
  have hF : 2 ^ lF D = 2 * 2 ^ lFe D := by rw [N.ffe, Nat.pow_succ, Nat.mul_comm]
  have hL : 2 ^ D.lL = 2 * 2 ^ (D.lL - 1) := by
    obtain ⟨k, hk⟩ : ∃ k, D.lL = k + 1 := ⟨D.lL - 1, by have := N.lL; omega⟩
    rw [hk, Nat.add_sub_cancel, Nat.pow_succ, Nat.mul_comm]
  have g : (([A0, StackData.under (eqLow rs dn.wy dn.w) (eqLow rs 0 dn.wy) dn.ni dn.ny
          fun i yv => SD.hZ.getD (i * SD.S.v.y.Pf + yv) zeroE] ++
        ((List.range SD.S.v.y.LamM).map fun lm =>
          StackData.under #[oneE] (eqLow rs 0 SD.S.v.y.lfe) 1 SD.S.v.y.h.fe
            fun _ yv => SD.hR.getD (SD.S.routedAt lm yv) zeroE) ++ [B0] ++ V).getD (2 + lm)
        zeroE) = StackData.under #[oneE] (eqLow rs 0 SD.S.v.y.lfe) 1 SD.S.v.y.h.fe
            fun _ yv => SD.hR.getD (SD.S.routedAt lm yv) zeroE := by
    have hl : lm < SD.S.v.y.LamM := by rw [I.y]; exact hlm
    simp [List.getD_eq_getElem?_getD, Nat.add_comm 2 lm, List.getElem?_append_left, hl]
  rw [g, under_read, sum_range_one, I.y, N.lfe, N.fe]
  have h1 : Reading.gl.val ((#[oneE] : Array E).getD 0 zeroE) = 1 := Reading.gl.one
  rw [h1, one_mul]
  refine sum_congr rfl fun yv hyv => ?_
  have hy : yv < 2 ^ lFe D := mem_range.mp hyv
  rw [eqLow_value Reading.gl rs hrs (by rw [Nat.sub_zero]; exact hy), I.hR]
  congr 1
  have er : SD.S.routedAt lm yv = (2 * lm + 1) * 2 ^ lF D + (D.fe + yv) := by
    unfold Sides.routedAt
    rw [I.y, N.Pf, N.fe, N.Dfe, Nat.add_assoc]
  rw [er, gatedUnder_read hts htu Ss Su N I rt hrt (by rw [hL]; rw [N.LamM] at hlm; omega)
    (by rw [hF, N.Dfe]; omega), Nat.add_comm 1 lm]
  rfl

/-- **END VALUE 1: THE FIRST NEVER-SENT VECTOR's VALUE AT THE CHALLENGES.** dn: the verifier's panel
of the down product. CONDITIONAL: on every hypothesis named. -/
theorem h1_read (hts : Q.P.y.T_ "s" = some ts) (htu : Q.P.y.T_ "u" = some tu)
    (Ss : TensorIs Q w t .sl ts) (Su : TensorIs Q w t .up tu) (N : GatedNums Q D)
    {rt : Array E} {SD : StackData} {tb : Tab × Tab} (I : StackIs Q w rt SD tb)
    (hzt : SD.S.zt.size = D.lT) {rs : Array E} (hrs : D.lL + lF D ≤ rs.size) {e : List E}
    (he : SD.endsAt rs = some e)
    (hdn : ∀ dn, (SD.bl.find? fun b => !b.tri && b.virt.isSome) = some dn →
      dn.wy = lF D ∧ dn.w = D.lL + lF D ∧ dn.ni = 2 ^ D.lL ∧ dn.ny = 2 ^ lF D) :
    Reading.gl.val (e.getD 1 zeroE) =
      ext (D.lL + lF D + D.lT) (fun X => slV D t X * upV D t X)
        (pt Reading.gl (downFrom rs (D.lL + lF D) ++ SD.S.zt)) := by
  obtain ⟨A0, B0, dn, V, hd, rfl⟩ := endsAt_parts he
  obtain ⟨d1, d2, d3, d4⟩ := hdn dn hd
  have g := Rows.gatedFirstIn Cb.Gl.E Reading.gl D t rs SD.S.zt dn (fun _ => 0) d1 d2
    (by rw [d2]; exact hrs)
  rw [d2] at g
  rw [g]
  have g1 : (([A0, StackData.under (eqLow rs dn.wy dn.w) (eqLow rs 0 dn.wy) dn.ni dn.ny
          fun i yv => SD.hZ.getD (i * SD.S.v.y.Pf + yv) zeroE] ++
        ((List.range SD.S.v.y.LamM).map fun lm =>
          StackData.under #[oneE] (eqLow rs 0 SD.S.v.y.lfe) 1 SD.S.v.y.h.fe
            fun _ yv => SD.hR.getD (SD.S.routedAt lm yv) zeroE) ++ [B0] ++ V).getD 1 zeroE) =
      StackData.under (eqLow rs dn.wy dn.w) (eqLow rs 0 dn.wy) dn.ni dn.ny
        fun i yv => SD.hZ.getD (i * SD.S.v.y.Pf + yv) zeroE := by
    simp [List.getD_eq_getElem?_getD]
  rw [g1, under_read, d3, d4]
  unfold gsum
  rw [d1, d2, Nat.add_sub_cancel]
  refine sum_congr rfl fun i hi => ?_
  rw [Finset.mul_sum]
  refine sum_congr rfl fun yv hy => ?_
  have hi' : i < 2 ^ D.lL := mem_range.mp hi
  have hy' : yv < 2 ^ lF D := mem_range.mp hy
  have p1 : 0 < 2 ^ lF D := Nat.two_pow_pos _
  have hv : Rows.hvOf D t (pt Reading.gl SD.S.zt) (fun _ => 0) 0 (i * 2 ^ lF D + yv) =
      hhU D t i yv (pt Reading.gl SD.S.zt) := by
    show hhU D t ((i * 2 ^ lF D + yv) / 2 ^ lF D) ((i * 2 ^ lF D + yv) % 2 ^ lF D) _ = _
    rw [Nat.mul_comm i, Nat.mul_add_div p1, Nat.div_eq_of_lt hy', Nat.add_zero,
      Nat.mul_add_mod, Nat.mod_eq_of_lt hy']
  rw [eqLow_value Reading.gl rs hrs (by rw [Nat.add_sub_cancel]; exact hi'),
    eqLow_value Reading.gl rs (by omega) (by rw [Nat.sub_zero]; exact hy'), I.hZ, I.y, N.Pf,
    gatedUnder_read hts htu Ss Su N I SD.S.zt hzt hi' hy']
  beta_reduce
  rw [hv]
  ring

end

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.range_sum
#print axioms OnBytes.Road.K4.C.under_read
#print axioms OnBytes.Road.K4.C.hh_read
#print axioms OnBytes.Road.K4.C.slup_at
#print axioms OnBytes.Road.K4.C.gatedUnder_read
#print axioms OnBytes.Road.K4.C.endsAt_parts
#print axioms OnBytes.Road.K4.C.h2_read
#print axioms OnBytes.Road.K4.C.h1_read
