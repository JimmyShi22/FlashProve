-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/All/Congr.lean: at positions below T and channels below d, a layer's two blocks depend on
the stream only at such positions and channels.

Used for the theorems on the whole model (Inst/Model/All/). Two streams that agree at the positions
i < T and the channels j < d (`Agree`) give the same attention block and the same feed-forward block
of a layer: the same range conditions, the same q, kx, v, o at the positions below T, and streams
after the block that agree again. For all parameters, tables, weights and layers.
Why: a block reads the stream through NORM, which reads the channels below d, and adds to it; at
position i attention reads the positions j ≤ i only (the maximum of (PA2), the sums of (PA5),
(PA6)); UNIT reads its input below d only.
The integer program, with NORM, UNIT and the labels of its steps: Inst/Model/Program.lean.
Notation (Inst/Model/Program.lean):
  the stream `x`, `x'`: a map `ℕ → Vec`, from a position to its vector of channels (`Vec`: `ℕ → ℤ`);
    "The residual stream" (`X`).
  `P`: a `Params`, "The parameters of the program: the sizes of the model, and one set of scales for
    all layers".
  `tb`: a `Tables`, "The five table functions that the program reads."
  `w`: a `LayerW`, "The weight matrices of one layer."
  `L`: a natural number, the number of the layer ("The attention block of layer L").
  `np`: a `NormPar`, "exponent of the reciprocal; shift; constant" of a normalisation.
  q, kx, v, o: `Att.q`, `Att.kx`, `Att.v`, `Att.o`, integers at a position i and an index c: steps
    (PL5) and (PA7); "qry and key are `q` and `kx`", "val is `v`" (`Att.sc`, `Att.ac`), "o_c is
    out_i[h][n] at c = ch·h + n".
  hd, c: natural numbers: a query head h, and an index over all heads: "(h, n) is the index c = ch·h
    + n" (`Att.AY`).
  z, wg, wu, k, k': "Subroutine UNIT, one hidden unit. Input: z, two columns wg, wu of weights, two
    shifts k, k'."
-/
import Inst.Model.Program

set_option autoImplicit false

namespace Inst.Model.All

open Finset

/-- the two streams agree at the positions i < T and the channels j < d -/
def Agree (P : Params) (x x' : ℕ → Vec) : Prop := ∀ i < P.T, ∀ j < P.d, x i j = x' i j

/-! ## The subroutines -/

theorem dot_congr {n : ℕ} {a a' : Vec} (b : Vec) (h : ∀ j < n, a j = a' j) :
    dot n a b = dot n a' b :=
  sum_congr rfl fun j hj => by rw [h j (mem_range.1 hj)]

theorem maxTo_congr {f g : Vec} : ∀ n : ℕ, (∀ j ≤ n, f j = g j) → maxTo f n = maxTo g n
  | 0, h => h 0 le_rfl
  | n + 1, h => by
    simp only [maxTo]
    rw [maxTo_congr n fun j hj => h j (Nat.le_succ_of_le hj), h (n + 1) le_rfl]

section Norm
variable (np : NormPar) {d : ℕ} {y y' : Vec} (hy : ∀ j < d, y j = y' j)
include hy

theorem norm_V : NORM.V d y = NORM.V d y' := sum_congr rfl fun j hj => by rw [hy j (mem_range.1 hj)]

theorem norm_R : NORM.R np d y = NORM.R np d y' := by
  unfold NORM.R NORM.sig
  rw [norm_V hy]

theorem norm_yw {j : ℕ} (hj : j < d) : NORM.yw np d y j = NORM.yw np d y' j := by
  unfold NORM.yw
  rw [norm_R np hy, hy j hj]

theorem norm_out {j : ℕ} (hj : j < d) : NORM.out np d y j = NORM.out np d y' j := by
  unfold NORM.out
  rw [norm_yw np hy hj]

theorem norm_OK : NORM.OK np d y ↔ NORM.OK np d y' := by
  unfold NORM.OK
  rw [norm_V hy]
  exact and_congr Iff.rfl (forall_congr' fun j => forall_congr' fun hj => by rw [norm_yw np hy hj])

end Norm

section Unit
variable (tb : Tables) {d : ℕ} {z z' : Vec} (wg wu : Vec) (k k' : ℕ) (hz : ∀ j < d, z j = z' j)
include hz

theorem unit_gw : UNIT.gw d z wg k = UNIT.gw d z' wg k := by
  unfold UNIT.gw
  rw [dot_congr wg hz]

theorem unit_up : UNIT.up d z wu k' = UNIT.up d z' wu k' := by
  unfold UNIT.up
  rw [dot_congr wu hz]

theorem unit_gh : UNIT.gh d z wg k = UNIT.gh d z' wg k := by
  unfold UNIT.gh UNIT.g0
  rw [unit_gw wg k hz]

theorem unit_hh : UNIT.hh tb d z wg wu k k' = UNIT.hh tb d z' wg wu k k' := by
  unfold UNIT.hh UNIT.sl UNIT.gc UNIT.g0
  rw [unit_gh wg k hz, unit_gw wg k hz, unit_up wu k' hz]

theorem unit_OK : UNIT.OK d z wg wu k k' ↔ UNIT.OK d z' wg wu k k' := by
  unfold UNIT.OK
  rw [unit_gh wg k hz, unit_up wu k' hz]

end Unit

variable {P : Params} {tb : Tables} {w : LayerW} {L : ℕ} {x x' : ℕ → Vec}

/-! ## The attention block -/

section Att
variable (h : Agree P x x')
include h

theorem att_a {i : ℕ} (hi : i < P.T) : ∀ j < P.d, Att.a P x i j = Att.a P x' i j := fun _ hj =>
  norm_out P.n1 (h i hi) hj

theorem att_Aq {i : ℕ} (hi : i < P.T) : Att.Aq P w x i = Att.Aq P w x' i :=
  funext fun _ => dot_congr _ (att_a h hi)
theorem att_Ak {i : ℕ} (hi : i < P.T) : Att.Ak P w x i = Att.Ak P w x' i :=
  funext fun _ => dot_congr _ (att_a h hi)
theorem att_Av {i : ℕ} (hi : i < P.T) : Att.Av P w x i = Att.Av P w x' i :=
  funext fun _ => dot_congr _ (att_a h hi)

theorem att_AY {i : ℕ} (hi : i < P.T) : Att.AY P w x i = Att.AY P w x' i := funext fun c => by
  unfold Att.AY
  rw [att_Aq h hi, att_Ak h hi]

theorem att_Y' {i : ℕ} (hi : i < P.T) :
    Att.Y' P tb w L x i = Att.Y' P tb w L x' i := funext fun c => by
  unfold Att.Y'
  rw [att_AY h hi]

theorem att_qkw {i : ℕ} (hi : i < P.T) :
    Att.qkw P tb w L x i = Att.qkw P tb w L x' i := funext fun c => by
  unfold Att.qkw
  rw [att_Y' h hi]

theorem att_vw {i : ℕ} (hi : i < P.T) : Att.vw P w x i = Att.vw P w x' i := funext fun c => by
  unfold Att.vw
  rw [att_Av h hi]

theorem att_q {i : ℕ} (hi : i < P.T) :
    Att.q P tb w L x i = Att.q P tb w L x' i := funext fun c => by
  unfold Att.q
  rw [att_qkw h hi]

theorem att_kx {i : ℕ} (hi : i < P.T) :
    Att.kx P tb w L x i = Att.kx P tb w L x' i := funext fun c => by
  unfold Att.kx
  rw [att_qkw h hi]

theorem att_v {i : ℕ} (hi : i < P.T) : Att.v P w x i = Att.v P w x' i := funext fun c => by
  unfold Att.v
  rw [att_vw h hi]

theorem att_sc (hd : ℕ) {i j : ℕ} (hi : i < P.T) (hj : j < P.T) :
    Att.sc P tb w L x hd i j = Att.sc P tb w L x' hd i j := by
  unfold Att.sc
  rw [att_q h hi, att_kx h hj]

theorem att_mx (hd : ℕ) {i : ℕ} (hi : i < P.T) : Att.mx P tb w L x hd i = Att.mx P tb w L x' hd i :=
  maxTo_congr i fun _ hj => att_sc h hd hi (lt_of_le_of_lt hj hi)

theorem att_wt (hd : ℕ) {i j : ℕ} (hi : i < P.T) (hj : j ≤ i) :
    Att.wt P tb w L x hd i j = Att.wt P tb w L x' hd i j := by
  unfold Att.wt Att.u
  rw [att_mx h hd hi, att_sc h hd hi (lt_of_le_of_lt hj hi)]

theorem att_den (hd : ℕ) {i : ℕ} (hi : i < P.T) :
    Att.den P tb w L x hd i = Att.den P tb w L x' hd i :=
  sum_congr rfl fun _ hj => att_wt h hd hi (Nat.lt_succ_iff.mp (mem_range.mp hj))

theorem att_ac (hd : ℕ) {i : ℕ} (hi : i < P.T) (n : ℕ) :
    Att.ac P tb w L x hd i n = Att.ac P tb w L x' hd i n :=
  sum_congr rfl fun j hj => by
    have hj' := Nat.lt_succ_iff.mp (mem_range.mp hj)
    rw [att_wt h hd hi hj', att_v h (lt_of_le_of_lt hj' hi)]

theorem att_o {i : ℕ} (hi : i < P.T) :
    Att.o P tb w L x i = Att.o P tb w L x' i := funext fun c => by
  unfold Att.o
  rw [att_ac h _ hi, att_den h _ hi]

theorem att_q_congr : ∀ i < P.T, ∀ c, Att.q P tb w L x i c = Att.q P tb w L x' i c := fun _ hi c =>
  congrFun (att_q h hi) c
theorem att_kx_congr : ∀ i < P.T, ∀ c, Att.kx P tb w L x i c = Att.kx P tb w L x' i c :=
  fun _ hi c => congrFun (att_kx h hi) c
theorem att_v_congr : ∀ i < P.T, ∀ c, Att.v P w x i c = Att.v P w x' i c := fun _ hi c =>
  congrFun (att_v h hi) c
/-- Under `h`: the same output of attention below T. -/
theorem att_o_congr : ∀ i < P.T, ∀ c, Att.o P tb w L x i c = Att.o P tb w L x' i c := fun _ hi c =>
  congrFun (att_o h hi) c

/-- Under `h`: the streams after the attention block agree. -/
theorem att_x'_congr : Agree P (Att.x' P tb w L x) (Att.x' P tb w L x') := fun i hi c hc => by
  unfold Att.x'
  rw [h i hi c hc, att_o h hi]

/-- Under `h`: the same range conditions of the attention block. -/
theorem att_ok_congr : Att.OK P tb w L x ↔ Att.OK P tb w L x' := by
  unfold Att.OK
  exact forall_congr' fun i =>
    forall_congr' fun hi => by rw [norm_OK P.n1 (h i hi), att_qkw h hi, att_vw h hi]

end Att

/-! ## The feed-forward block -/

section FF
variable (h : Agree P x x')
include h

theorem ff_m {i : ℕ} (hi : i < P.T) : ∀ j < P.d, FF.m P x i j = FF.m P x' i j := fun _ hj =>
  norm_out P.n2 (h i hi) hj

theorem ff_lw {i : ℕ} (hi : i < P.T) : FF.lw P w x i = FF.lw P w x' i := funext fun e => by
  unfold FF.lw
  rw [dot_congr _ (ff_m h hi)]

theorem ff_ly {i : ℕ} (hi : i < P.T) : FF.ly P w x i = FF.ly P w x' i := funext fun e => by
  unfold FF.ly FF.l3
  rw [ff_lw h hi]

theorem ff_lr {i : ℕ} (hi : i < P.T) : FF.lr P w x i = FF.lr P w x' i := funext fun e => by
  unfold FF.lr FF.l3
  rw [ff_ly h hi, ff_lw h hi]

theorem ff_es {i : ℕ} (hi : i < P.T) : FF.es P w x i = FF.es P w x' i := by
  unfold FF.es
  rw [ff_lr h hi]

theorem ff_sc {i : ℕ} (hi : i < P.T) : FF.sc P tb w x i = FF.sc P tb w x' i := by
  unfold FF.sc FF.mr
  rw [ff_lr h hi, ff_es h hi]

theorem ff_xr {i : ℕ} (hi : i < P.T) :
    ∀ j < P.d, FF.xr P tb w x i j = FF.xr P tb w x' i j := fun j hj => by
  unfold FF.xr
  rw [ff_sc h hi, ff_m h hi j hj]

theorem ff_z {i : ℕ} (hi : i < P.T) (j : ℕ) :
    ∀ u < P.d, FF.z P tb w L x i j u = FF.z P tb w L x' i j u := fun u hu => by
  unfold FF.z
  split_ifs
  · exact ff_xr h hi u hu
  · exact ff_m h hi u hu

theorem ff_wg {i : ℕ} (hi : i < P.T) : FF.wg P w L x i = FF.wg P w L x' i := funext fun j => by
  unfold FF.wg
  rw [ff_es h hi]

theorem ff_wu {i : ℕ} (hi : i < P.T) : FF.wu P w L x i = FF.wu P w L x' i := funext fun j => by
  unfold FF.wu
  rw [ff_es h hi]

theorem ff_hh {i : ℕ} (hi : i < P.T) :
    FF.hh P tb w L x i = FF.hh P tb w L x' i := funext fun j => by
  unfold FF.hh
  rw [ff_wg h hi, ff_wu h hi]
  exact unit_hh tb _ _ _ _ (ff_z h hi j)

theorem ff_Ad {i : ℕ} (hi : i < P.T) :
    FF.Ad P tb w L x i = FF.Ad P tb w L x' i := funext fun c => by
  unfold FF.Ad
  rw [ff_hh h hi, ff_es h hi]

/-- Under `h`: the streams after the feed-forward block agree. -/
theorem ff_x''_congr : Agree P (FF.x'' P tb w L x) (FF.x'' P tb w L x') := fun i hi c hc => by
  unfold FF.x''
  rw [h i hi c hc, ff_Ad h hi]

/-- Under `h`: the same range conditions of the feed-forward block. -/
theorem ff_ok_congr : FF.OK P tb w L x ↔ FF.OK P tb w L x' := by
  unfold FF.OK
  refine forall_congr' fun i => forall_congr' fun hi => ?_
  rw [norm_OK P.n2 (h i hi), ff_ly h hi, ff_wg h hi, ff_wu h hi]
  exact and_congr Iff.rfl
    (and_congr Iff.rfl
      (forall_congr' fun j => forall_congr' fun _ => unit_OK _ _ _ _ (ff_z h hi j)))

end FF

end Inst.Model.All
