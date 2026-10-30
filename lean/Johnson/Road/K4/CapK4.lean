-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/CapK4.lean: THE WRITTEN COUNTS OF THE ROUNDS THAT K4's BLOCK DECLARES LIE BELOW THE
CAP AT 128, in a group that is not the first, at the library's value (`Plan4.full`) and the maps of
Johnson/Road/K4/PlanMaps.lean: `Err.le ((mapsK4 A N Ex).err (the chain's own errors)) (Err.cap 128
_)`. It is for a theorem on K4's block at a piece of the description that carries the cap as its
errors (`Err.cap`, Iop/ErrCap.lean) and K4's declared rounds as its rounds: a law that is proved at
the counts on the left then holds at the cap, by the monotony that ErrCap.lean's head names. No such
piece stands here. Statements and proofs. Arithmetic on natural numbers over the library's clauses.

THE PRICING IS NOT NEW. `Johnson.Bridge.below_of_num` (Johnson/Bridge/BasePriced.lean) gives the
clause `RoundBelow count d (2⁻¹ ^ 128)` on one written round from one comparison of natural numbers:
count · 2^193 + 3 (drawE + drawNZ) N ≤ N · 2^(work + 65), N the number of values of the round's
draws. OnBytes/Desc/First/P1/ChBelow.lean carries such clauses, round by round, to the cap.

WHAT IS DONE HERE. The rounds that K4's block declares carry NO work (`entryOf` lays none): the 128
bits come from the size of the field alone, q = p^3 > 2^191.
  `nVals_fit`: a written round that answers a row of K4's table has q^(drawn - notZero) ·
    (q - 1)^notZero values.
  `q_big`: 2^191 ≤ q - 1. `num_one`: the comparison, from 4 c + k ≤ 2^65.
  `rb_one` (one element is drawn; a count c with 4 c + 3 ≤ 2^65) · `rb_nz` (one element other than
    0; 4 c + 6 ≤ 2^65) · `rb_pt` (a point of g coordinates; the count g q^(g-1); 7 g ≤ 2^65) ·
    `rb_none` (nothing is drawn; the count 0).
  `scR_below`: so at a masked sumcheck's written rounds, for a further degree of at most 2.
  `CapSizes`: four bounds on the library's sizes: nNu, nW, lT, lL + 1 ≤ 2^60.
  `Plan4.tailBelow`, `Plan4.le_capK4`, `Plan4.le_cap_at` (at any list that is K4's declared one).

THE TYPED COUNTS, read off the library's value by unfolding: 8 at the limbs' scalars; (lL + 1) q^lL
at the norms' join; 7 nNu - 1 at the products' scalars; 1 at each point on a line and at the draw
that combines; (lL - 1) q^(lL - 2) at the routed join; nW - 1 at the weights' round; lT q^(lT - 1)
at the token point; in a sumcheck 1, then 2 a variable, then the further degree, then 0.

Limits. `CapSizes` and `Meets` are premises. THE ROUNDS ARE THOSE THAT K4's BLOCK DECLARES
(`dsLater`: the written rounds of its own table's rows), NOT A MADE PLAN's ENTRIES: at a parameter
file that asks work of the rounds that draw field elements the plan's entries carry that work and
part from the declared ones; of such a file nothing is said here. A share of the WRITTEN challenges
of each round taken alone: nothing is added up over the rounds; what such a share is worth is said
in other files of the library. Nothing on soundness of any protocol is concluded here.
-/
import Johnson.Road.K4.PlanMaps
import OnBytes.Desc.First.P1.ChBelow
import Johnson.Bridge.BasePriced

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop _root_.Run OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat OnBytes.Slice
open Inst.Model (Scl)
open OnBytes.Desc.First.K4 (Par Rd Fit rdOf fit_rdOf pointRd batchRd)
open OnBytes.Desc.First.P1 (RdBelow ScR TailM TailNums TailBelow own_le_cap)
open scoped ENNReal

local notation "qq" => Fmt.Fld.two.p ^ 3

/-! ### The values of a written round's draws -/

theorem nVals_nz : ∀ z : ℕ,
    nVals (List.replicate z Fmt.Draw.elemNZ ++ [Fmt.Draw.trits 0]) = (qq - 1) ^ z
  | 0 => rfl
  | z + 1 => by
      show (qq - 1) * nVals (List.replicate z Fmt.Draw.elemNZ ++ [Fmt.Draw.trits 0]) = _
      rw [nVals_nz z]
      exact (pow_succ' _ _).symm

theorem nVals_el (z : ℕ) : ∀ a : ℕ,
    nVals (List.replicate a Fmt.Draw.elem ++
      (List.replicate z Fmt.Draw.elemNZ ++ [Fmt.Draw.trits 0])) = qq ^ a * (qq - 1) ^ z
  | 0 => by
      rw [pow_zero, Nat.one_mul]
      exact nVals_nz z
  | a + 1 => by
      show qq * nVals (List.replicate a Fmt.Draw.elem ++
        (List.replicate z Fmt.Draw.elemNZ ++ [Fmt.Draw.trits 0])) = _
      rw [nVals_el z a, pow_succ' (Fmt.Fld.two.p ^ 3) a, Nat.mul_assoc]

/-- **The number of values of the draws of a written round that answers a row.** -/
theorem nVals_fit {d : Rd} {x : RDT} (h : Fit d x) :
    nVals (Fmt.dsOf x.entry x.kind) = qq ^ (d.drawn - d.notZero) * (qq - 1) ^ d.notZero := by
  unfold Fmt.dsOf Fmt.dsElems
  rw [h.poss, h.trits, h.drawE, h.drawNZ, if_neg h.kind_ok.2, if_neg h.kind_ok.1,
    List.replicate_zero, List.nil_append, List.append_assoc]
  exact nVals_el d.notZero (d.drawn - d.notZero)

/-- The field is large. -/
theorem q_big : 2 ^ 191 ≤ qq - 1 := by
  have e : Fmt.Fld.two.p = 18446744069414584321 := rfl
  rw [e]
  norm_num

/-- The comparison at a round with q values or q - 1: k is thrice the number of draws, one other
than 0 counted twice. -/
theorem num_one (c q k : ℕ) (hq : 2 ^ 191 ≤ q) (hc : 4 * c + k ≤ 2 ^ 65) :
    c * 2 ^ 193 + k * q ≤ q * 2 ^ 65 := by
  have e : (2 : ℕ) ^ 193 = 4 * 2 ^ 191 := by norm_num
  rw [e]
  calc c * (4 * 2 ^ 191) + k * q ≤ c * (4 * q) + k * q :=
        Nat.add_le_add_right (Nat.mul_le_mul_left c (Nat.mul_le_mul_left 4 hq)) _
    _ = (4 * c + k) * q := by ring
    _ ≤ 2 ^ 65 * q := Nat.mul_le_mul_right q hc
    _ = q * 2 ^ 65 := Nat.mul_comm _ _

/-! ### The clause at the four kinds of rounds -/

/-- One element is drawn. -/
theorem rb_one {d : Rd} {x : RDT} (h : Fit d x) (hw : x.entry.work = 0) (hd : d.drawn = 1)
    (hz : d.notZero = 0) (c : ℕ) (hc : 4 * c + 3 ≤ 2 ^ 65) : RdBelow ((2 : ℝ≥0∞)⁻¹ ^ 128) c x := by
  have hq := q_big
  have hN : nVals (Fmt.dsOf x.entry x.kind) = qq := by
    rw [nVals_fit h, hd, hz]
    simp
  refine Johnson.Bridge.below_of_num (toRD x) h.logN ?_ (fun _ => ?_) c qq hN (by omega) ?_
  · show x.entry.drawNZ ≤ x.entry.drawE
    rw [h.drawNZ, h.drawE, hz]
    exact Nat.zero_le _
  · show x.entry.work + 66 ≤ 128
    rw [hw]
    norm_num
  · show c * 2 ^ 193 + 3 * (x.entry.drawE + x.entry.drawNZ) * qq ≤ qq * 2 ^ (x.entry.work + 65)
    rw [h.drawE, h.drawNZ, hd, hz, hw]
    exact num_one c qq 3 (hq.trans (Nat.sub_le _ _)) hc

/-- One element other than 0 is drawn. -/
theorem rb_nz {d : Rd} {x : RDT} (h : Fit d x) (hw : x.entry.work = 0) (hd : d.drawn = 1)
    (hz : d.notZero = 1) (c : ℕ) (hc : 4 * c + 6 ≤ 2 ^ 65) : RdBelow ((2 : ℝ≥0∞)⁻¹ ^ 128) c x := by
  have hq := q_big
  have hN : nVals (Fmt.dsOf x.entry x.kind) = qq - 1 := by
    rw [nVals_fit h, hd, hz]
    simp
  refine Johnson.Bridge.below_of_num (toRD x) h.logN ?_ (fun _ => ?_) c (qq - 1) hN (by omega) ?_
  · show x.entry.drawNZ ≤ x.entry.drawE
    rw [h.drawNZ, h.drawE, hz, hd]
  · show x.entry.work + 66 ≤ 128
    rw [hw]
    norm_num
  · show c * 2 ^ 193 + 3 * (x.entry.drawE + x.entry.drawNZ) * (qq - 1) ≤
      (qq - 1) * 2 ^ (x.entry.work + 65)
    rw [h.drawE, h.drawNZ, hd, hz, hw]
    exact num_one c (qq - 1) 6 hq hc

/-- A point of g coordinates is drawn; the count is g q^(g - 1). -/
theorem rb_pt {d : Rd} {x : RDT} (h : Fit d x) (hw : x.entry.work = 0) {g : ℕ} (hd : d.drawn = g)
    (hz : d.notZero = 0) (hg : 7 * g ≤ 2 ^ 65) :
    RdBelow ((2 : ℝ≥0∞)⁻¹ ^ 128) (g * Fintype.card GE ^ (g - 1)) x := by
  have hq := q_big
  have hcard : Fintype.card GE = qq := Cb.Gl.gl_card.2.1
  have hN : nVals (Fmt.dsOf x.entry x.kind) = qq ^ g := by
    rw [nVals_fit h, hd, hz]
    simp
  rw [hcard]
  refine Johnson.Bridge.below_of_num (toRD x) h.logN ?_ (fun _ => ?_) _ (qq ^ g) hN
    (pow_pos (by omega) _) ?_
  · show x.entry.drawNZ ≤ x.entry.drawE
    rw [h.drawNZ, hz]
    exact Nat.zero_le _
  · show x.entry.work + 66 ≤ 128
    rw [hw]
    norm_num
  · show g * qq ^ (g - 1) * 2 ^ 193 + 3 * (x.entry.drawE + x.entry.drawNZ) * qq ^ g ≤
      qq ^ g * 2 ^ (x.entry.work + 65)
    rw [h.drawE, h.drawNZ, hd, hz, hw]
    generalize qq = q at hq ⊢
    rcases g with _ | k
    · simp
    · have e1 : k + 1 - 1 = k := rfl
      rw [e1, pow_succ]
      have h1 : q ^ k * 2 ^ 193 ≤ 4 * (q ^ k * q) := by
        have : (2 : ℕ) ^ 193 = 4 * 2 ^ 191 := by norm_num
        rw [this]
        have h2 : q ^ k * 2 ^ 191 ≤ q ^ k * q := Nat.mul_le_mul_left _ (hq.trans (Nat.sub_le _ _))
        calc q ^ k * (4 * 2 ^ 191) = 4 * (q ^ k * 2 ^ 191) := by ring
          _ ≤ 4 * (q ^ k * q) := Nat.mul_le_mul_left 4 h2
      have h3 : (k + 1) * q ^ k * 2 ^ 193 ≤ 4 * (k + 1) * (q ^ k * q) := by
        calc (k + 1) * q ^ k * 2 ^ 193 = (k + 1) * (q ^ k * 2 ^ 193) := by ring
          _ ≤ (k + 1) * (4 * (q ^ k * q)) := Nat.mul_le_mul_left _ h1
          _ = 4 * (k + 1) * (q ^ k * q) := by ring
      calc (k + 1) * q ^ k * 2 ^ 193 + 3 * (k + 1 + 0) * (q ^ k * q)
          ≤ 4 * (k + 1) * (q ^ k * q) + 3 * (k + 1 + 0) * (q ^ k * q) :=
            Nat.add_le_add_right h3 _
        _ = 7 * (k + 1) * (q ^ k * q) := by ring
        _ ≤ 2 ^ 65 * (q ^ k * q) := Nat.mul_le_mul_right _ hg
        _ = q ^ k * q * 2 ^ (0 + 65) := by ring

/-- Nothing is drawn; the count is 0. -/
theorem rb_none {d : Rd} {x : RDT} (h : Fit d x) (hd : d.drawn = 0) (hz : d.notZero = 0) :
    RdBelow ((2 : ℝ≥0∞)⁻¹ ^ 128) 0 x := by
  have hN : nVals (Fmt.dsOf x.entry x.kind) = 1 := by
    rw [nVals_fit h, hd, hz]
    simp
  refine Johnson.Bridge.below_of_num (toRD x) h.logN ?_ (fun h0 => ?_) 0 1 hN Nat.one_pos ?_
  · show x.entry.drawNZ ≤ x.entry.drawE
    rw [h.drawNZ, hz]
    exact Nat.zero_le _
  · exact absurd (h.drawE.trans hd) h0
  · show 0 * 2 ^ 193 + 3 * (x.entry.drawE + x.entry.drawNZ) * 1 ≤ 1 * 2 ^ (x.entry.work + 65)
    rw [h.drawE, h.drawNZ, hd, hz]
    simp

/-! ### K4's rows -/

/-- **A masked sumcheck's written rounds**, for a further degree of at most 2. -/
theorem scR_below (k f y e : ℕ) {DY : ℕ} (hDY : DY ≤ 2) :
    (scR k f y e).Below ((2 : ℝ≥0∞)⁻¹ ^ 128) DY where
  e := rb_one (fit_rdOf { name := .pscEpsilon, sent := f }) rfl rfl rfl 1 (by norm_num)
  v := fun d hd => by
    rw [List.eq_of_mem_replicate hd]
    exact rb_one (fit_rdOf { name := .pscRound, sent := 2 }) rfl rfl rfl 2 (by norm_num)
  y := rb_nz (fit_rdOf { name := .pscY, sent := y, notZero := 1 }) rfl rfl rfl DY (by
    have : (2 : ℕ) ^ 65 = 36893488147419103232 := by norm_num
    omega)
  z := rb_none (fit_rdOf { name := .pscValues, sent := e, drawn := 0 }) rfl rfl

/-- Four bounds on the library's sizes. -/
structure CapSizes (D : Inst.Model.FFSeg.Dim) (nW : ℕ) : Prop where
  nNu : D.nNu ≤ 2 ^ 60
  nW : nW ≤ 2 ^ 60
  lT : D.lT ≤ 2 ^ 60
  lL : D.lL + 1 ≤ 2 ^ 60

variable [scl : Scl] {M X : Type} {Q : Plan4 Cb.Gl.E M X} {p : Par} {hS : Layer.Shape}
  {pc : List (List String)}

/-- **The clause at every written round from the limbs' scalars on.** -/
theorem Plan4.tailBelow (A : Q.Meets p hS pc) (N : TailNums Q.full.own.toOwn.tail)
    (C : CapSizes Q.D Q.nW) :
    TailBelow ((2 : ℝ≥0∞)⁻¹ ^ 128)
      (TailM.ofIs (Q.tailIs_plan A.hy A.hc A.hrd A.Z A.hl A.hn A.wk A.hg) A.written.2.2 N) := by
  have two65 : (2 : ℕ) ^ 65 = 36893488147419103232 := by norm_num
  have two60 : (2 : ℕ) ^ 60 = 1152921504606846976 := by norm_num
  have c1 := C.nNu
  have c2 := C.nW
  have c4 := C.lL
  have Xd := A.dimIs
  exact
    { l := rb_one (fit_rdOf _) rfl rfl rfl (9 - 1) (by norm_num)
      n := rb_pt (fit_rdOf _) rfl (g := Q.D.lL + 1) Xd.lNI.symm rfl (by omega)
      s1 := scR_below _ _ _ _ (Nat.le_refl 2)
      t1 := rb_one (fit_rdOf _) rfl rfl rfl 1 (by norm_num)
      p := rb_one (fit_rdOf _) rfl rfl rfl (Q.D.nNu * 7 - 1) (by omega)
      s2 := scR_below _ _ _ _ (Nat.le_refl 2)
      s3 := scR_below _ _ _ _ (show 1 ≤ 2 by norm_num)
      d4 := rb_one (fit_rdOf _) rfl rfl rfl (2 - 1) (by norm_num)
      s4 := scR_below _ _ _ _ (Nat.le_refl 2)
      s5 := scR_below _ _ _ _ (Nat.le_refl 2)
      t5 := rb_one (fit_rdOf _) rfl rfl rfl 1 (by norm_num)
      r := rb_pt (fit_rdOf _) rfl (g := Q.D.lL - 1) (congrArg (· - 1) Xd.ll.symm) rfl (by omega)
      s6 := scR_below _ _ _ _ (Nat.le_refl 2)
      t6 := rb_one (fit_rdOf _) rfl rfl rfl 1 (by norm_num)
      w := rb_one (fit_rdOf _) rfl rfl rfl (Q.nW - 1) (by omega)
      s7 := scR_below _ _ _ _ (show 1 ≤ 2 by norm_num) }

/-- **The written counts of K4's own rounds are at most the cap at 128.** -/
theorem Plan4.le_capK4 (A : Q.Meets p hS pc) (N : TailNums Q.full.own.toOwn.tail)
    (Ex : Iop.ExtSpec) (C : CapSizes Q.D Q.nW) :
    Err.le ((Plan4.mapsK4 A N Ex).err (Q.full.own.toOwn.ch.eps Ex))
      (Err.cap 128 (uLT (ckP .two) (dsLater p))) := by
  have two65 : (2 : ℕ) ^ 65 = 36893488147419103232 := by norm_num
  have two60 : (2 : ℕ) ^ 60 = 1152921504606846976 := by norm_num
  have c3 := C.lT
  exact own_le_cap 128 Ex Q.full.own.toOwn _
    (rb_pt (fit_rdOf _) rfl (g := Q.D.lT) A.dimIs.lt.symm rfl (by omega))
    (Plan4.tailBelow A N C)

/-- **At any list that is K4's declared one.** -/
theorem Plan4.le_cap_at (A : Q.Meets p hS pc) (N : TailNums Q.full.own.toOwn.tail)
    (Ex : Iop.ExtSpec) (C : CapSizes Q.D Q.nW) {ds : List RDT} (e : ds = dsLater p) :
    Err.le (((Plan4.mapsK4 A N Ex).castD e).err (Q.full.own.toOwn.ch.eps Ex))
      (Err.cap 128 (uLT (ckP .two) ds)) := by
  subst e
  exact Plan4.le_capK4 A N Ex C

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.nVals_fit
#print axioms OnBytes.Road.K4.rb_one
#print axioms OnBytes.Road.K4.rb_nz
#print axioms OnBytes.Road.K4.rb_pt
#print axioms OnBytes.Road.K4.rb_none
#print axioms OnBytes.Road.K4.Plan4.le_capK4
#print axioms OnBytes.Road.K4.Plan4.le_cap_at
