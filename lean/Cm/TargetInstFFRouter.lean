-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetInstFFRouter.lean: no wrap-around in a feed-forward segment: router, routed units,
embedding, at a variable number p.

"No wrap-around": what holds modulo p of the cells' small integers is shown to hold over the
integers. All theorems are under `h` (`RFraw`, Inst/Model/FF/Cast.lean): integer cells t meet the
segment's relation, with keys and identities formed in `ZMod p`, for a variable number p with
2^61 - 1 ≤ p (the class `Big p`: Inst/Model/Bound/Base.lean; that p is prime is not assumed).

Main names, each under the hypotheses of its statement, over the integers:
  `router_facts`: in a layer with experts the router's values are those of the program
    (Inst/Model/Program.lean: `FF.ly`, `FF.l3`, `FF.lr`, `FF.es`, `FF.sc`, `FF.xr`).
  `hidden_facts`: at every hidden unit sl, up and hh are the program's, and `UNIT.OK` holds.
  `ok_facts`, `hh_abs`, `emb_facts`: see their docstrings.

Why: `Big p` lifts the router's size conditions `Router.Adm` from 2^61 - 1 (`Router.adm_ref`) to p
(`Cm.TI.Router.Adm.mono`), enters through `NWU.unit_facts` and `NWU.gate_facts`
(Cm/TargetInstFFUnit.lean), and in `emb_facts` the step "p divides a - b and |a - b| < 2^61 - 1, so
a = b" is by `Cm.TI.eq_of_dvd`.

Limits: the namespace is `Cm.TI`. What each step is, and the notation: the head of
Inst/Model/FF/NoWrapRouter.lean. (The limits on the prime: the head of Inst/Model/Bound/Base.lean.)
Terms: lean/GLOSSARY.md.
-/
import Inst.Model.FF.NoWrapRouter
import Cm.TargetInstFFUnit


set_option autoImplicit false

/- The default table of scales is not in sight in this file (`Scl.ref` is no instance here): what
reads a table reads the variable `scl`. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cm.TI.FFSeg

open Inst.Model Inst.Model.FFSeg

variable {p : ℕ} [Big p]

variable [scl : Scl]

open Finset hiding val

namespace NWR
open Inst.Model.FFSeg.NWR
open Cm.TI.FFSeg.NWU (cellB)
open Inst.Model.FFSeg.NWU (Sz)

/-! ## The router -/

section
variable {D : Dim} {tb : Tables} {L0 : ℕ} {first : Bool} {w : ℕ → LayerW} {emb : Mat}
  {tok : ℕ → ℕ} {t : Cell → ℤ}
variable (h : RFraw D tb L0 first (ZMod p) w emb tok t)
variable {l i : ℕ} (hl : l < D.nl) (he : isExpL l = true) (hi : i < D.T)

include h hl he hi

omit [Big p] in
theorem small :
    Router.Small (2 ^ 18) (257 * 2 ^ 18) (65793 * 2 ^ 18) D.nx D.d (rv t (l / 2) i) := by
  have hl' := half_lt hl he
  refine ⟨fun e hx => ?_, fun e hx => ?_, fun e hx => ?_, fun e hx => ?_,
    fun e hx => ?_, ?_, fun j hj => ?_⟩
  · have c0 := cellB h (c := ⟨.ly, 0, l / 2, e, i⟩) ⟨(by decide : 0 < 2), hl', hx, hi⟩
    have c1 := cellB h (c := ⟨.ly, 1, l / 2, e, i⟩) ⟨(by decide : 1 < 2), hl', hx, hi⟩
    simp only [rv, val, Arr.nCell, Arr.off, sum_range_succ, sum_range_zero, Int.cast_id]
    rw [abs_le]; constructor <;> omega
  · have c0 := cellB h (c := ⟨.l3, 0, l / 2, e, i⟩) ⟨(by decide : 0 < 1), hl', hx, hi⟩
    simp only [rv, val, Arr.nCell, Arr.off, sum_range_succ, sum_range_zero, Int.cast_id]
    rw [abs_le]; constructor <;> omega
  · have c0 := cellB h (c := ⟨.lr, 0, l / 2, e, i⟩) ⟨(by decide : 0 < 2), hl', hx, hi⟩
    have c1 := cellB h (c := ⟨.lr, 1, l / 2, e, i⟩) ⟨(by decide : 1 < 2), hl', hx, hi⟩
    simp only [rv, val, Arr.nCell, Arr.off, sum_range_succ, sum_range_zero, Int.cast_id]
    rw [abs_le]; constructor <;> omega
  · have c0 := cellB h (c := ⟨.sel, 0, l / 2, e, i⟩) ⟨(by decide : 0 < 1), hl', hx, hi⟩
    simp only [rv, val, Arr.nCell, Arr.off, sum_range_succ, sum_range_zero, Int.cast_id]
    rw [abs_le]; constructor <;> omega
  · have c0 := cellB h (c := ⟨.rl, 0, l / 2, e, i⟩) ⟨(by decide : 0 < 1), hl', hx, hi⟩
    simp only [rv, val, Arr.nCell, Arr.off, sum_range_succ, sum_range_zero, Int.cast_id]
    rw [abs_le]; constructor <;> omega
  · have c0 :=
      cellB h (c := ⟨.sc, 0, l / 2, 0, i⟩) ⟨(by decide : 0 < 3), hl', (by decide : 0 < 1), hi⟩
    have c1 :=
      cellB h (c := ⟨.sc, 1, l / 2, 0, i⟩) ⟨(by decide : 1 < 3), hl', (by decide : 0 < 1), hi⟩
    have c2 :=
      cellB h (c := ⟨.sc, 2, l / 2, 0, i⟩) ⟨(by decide : 2 < 3), hl', (by decide : 0 < 1), hi⟩
    simp only [rv, val, Arr.nCell, Arr.off, sum_range_succ, sum_range_zero, Int.cast_id]
    rw [abs_le]; constructor <;> omega
  · have c0 := cellB h (c := ⟨.xr, 0, l / 2, j, i⟩) ⟨(by decide : 0 < 2), hl', hj, hi⟩
    have c1 := cellB h (c := ⟨.xr, 1, l / 2, j, i⟩) ⟨(by decide : 1 < 2), hl', hj, hi⟩
    simp only [rv, val, Arr.nCell, Arr.off, sum_range_succ, sum_range_zero, Int.cast_id]
    rw [abs_le]; constructor <;> omega

omit [Big p] in
/-- the keys of the router, and (J10) -/
theorem keys :
    Router.Keys (p : ℤ) tb (D.Pl l).kr D.nx D.d (fun j => val t .m l j i)
      (fun e => dot D.d (fun j => val t .m l j i) fun j => (w l).Wr j e) (rv t (l / 2) i) := by
  have hp : ∀ s : Fam, isExp s = true → present s l = true := fun s hs => by
    unfold present
    rw [hs, he]
    rfl
  exact ⟨fun e hx => key_inLut D tb L0 first w emb tok t _ h (s := .LR) hl (hp _ rfl) hx hi,
    fun e hx => key_inLut D tb L0 first w emb tok t _ h (s := .LH) hl (hp _ rfl) hx hi,
    fun e hx => key_inLut D tb L0 first w emb tok t _ h (s := .L3) hl (hp _ rfl) hx hi,
    fun e hx => key_inLut D tb L0 first w emb tok t _ h (s := .CLR) hl (hp _ rfl) hx hi,
    fun e hx => key_inLut D tb L0 first w emb tok t _ h (s := .LT) hl (hp _ rfl) hx hi,
    fun e hx => key_inLut D tb L0 first w emb tok t _ h (s := .SEL) hl (hp _ rfl) hx hi,
    fun e hx => key_inLut D tb L0 first w emb tok t _ h (s := .DD) hl (hp _ rfl) hx hi,
    key_inLut D tb L0 first w emb tok t _ h (s := .MR) (x := 0) hl
      (hp _ rfl) (by decide : 0 < 1) hi,
    fun j hj => key_inLut D tb L0 first w emb tok t _ h (s := .XR) hl (hp _ rfl) hj hi,
    idn_modEq D tb L0 first w emb tok t _ h (j := .j10 (l / 2) i) ⟨half_lt hl he, hi⟩⟩

end

/-! ## In the words of the program -/

section
variable {D : Dim} {tb : Tables} {L0 : ℕ} {first : Bool} {w : ℕ → LayerW} {emb : Mat}
  {tok : ℕ → ℕ} {t : Cell → ℤ}
variable (h : RFraw D tb L0 first (ZMod p) w emb tok t)
variable {l i : ℕ} (hl : l < D.nl) (hi : i < D.T) {P' : Params} (hOK : tb.OK P') (S : SzR D)
  (hW : WFabs (w l)) (hmP : ∀ j < D.d, val t .m l j i = FF.m (D.Pl l) (stream D t (2 * l + 1)) i j)

include h hl hi hOK S hW hmP

/-- Steps L9, L10a to L10e: (R1) to (R6), in a layer with experts. -/
theorem router_facts (he : isExpL l = true) :
    (∀ e < D.nx, val t .ly (l / 2) e i = FF.ly (D.Pl l) (w l) (stream D t (2 * l + 1)) i e ∧
      val t .l3 (l / 2) e i = FF.l3 (D.Pl l) (w l) (stream D t (2 * l + 1)) i e ∧
      val t .lr (l / 2) e i = FF.lr (D.Pl l) (w l) (stream D t (2 * l + 1)) i e ∧
      Fits16 (FF.ly (D.Pl l) (w l) (stream D t (2 * l + 1)) i e) ∧
      val t .sel (l / 2) e i =
        if e = FF.es (D.Pl l) (w l) (stream D t (2 * l + 1)) i then 1 else 0) ∧
    FF.es (D.Pl l) (w l) (stream D t (2 * l + 1)) i < D.nx ∧
    val t .sc (l / 2) 0 i = FF.sc (D.Pl l) tb (w l) (stream D t (2 * l + 1)) i ∧
    ∀ j < D.d,
      val t .xr (l / 2) j i = FF.xr (D.Pl l) tb (w l) (stream D t (2 * l + 1)) i j ∧
      |val t .xr (l / 2) j i| ≤ 2047 := by
  have hm := m_abs hmP
  have hA : ∀ e < D.nx, |dot D.d (fun j => val t .m l j i) fun j =>
      (w l).Wr j e| ≤ 5120 * 2047 * 2 ^ 12 := fun e _ => by
    refine (abs_dot_le hm fun j _ => hW.Wr j e).trans ?_
    have : (D.d : ℤ) ≤ 5120 := by exact_mod_cast S.d
    nlinarith
  have adm : Router.Adm (p : ℤ) (2 ^ 18) (257 * 2 ^ 18) (65793 * 2 ^ 18) (5120 * 2047 * 2 ^ 12)
      20961280 2047 (D.Pl l).kr D.nx := by
    rw [S.nx]
    exact Cm.TI.Router.Adm.mono (Router.adm_ref (S.kr l).1 (S.kr l).2) (big_pow p)
  obtain ⟨r1, r2, r3, r4, r5, -, r7⟩ :=
    Router.router_sound adm hOK.2.1 (small h hl he hi) hA hm (keys h hl he hi)
  have hlw : ∀ e, rhu (dot D.d (fun j => val t .m l j i) fun j => (w l).Wr j e) (D.Pl l).kr =
      FF.lw (D.Pl l) (w l) (stream D t (2 * l + 1)) i e := fun e => by
    unfold FF.lw
    rw [All.dot_congr _ hmP]
    rfl
  have hl3 : ∀ e < D.nx,
      val t .l3 (l / 2) e i = FF.l3 (D.Pl l) (w l) (stream D t (2 * l + 1)) i e := fun e hx => by
    have := (r1 e hx).2.1
    rw [hlw] at this
    exact this
  have hly : ∀ e < D.nx,
      val t .ly (l / 2) e i = FF.ly (D.Pl l) (w l) (stream D t (2 * l + 1)) i e := fun e hx => by
    have := (r1 e hx).2.2.1
    rw [hlw] at this
    exact this
  have hlr : ∀ e < D.nx,
      val t .lr (l / 2) e i = FF.lr (D.Pl l) (w l) (stream D t (2 * l + 1)) i e := fun e hx => by
    have h5 : val t .lr (l / 2) e i =
        8 * clamp 2047 (val t .ly (l / 2) e i) + val t .l3 (l / 2) e i :=
      (r1 e hx).2.2.2.2.1
    rw [h5, hly e hx, hl3 e hx]
    rfl
  have hnx : 0 < D.nx := by rw [S.nx]; norm_num
  have hes : argTo (rv t (l / 2) i).lr (D.nx - 1) =
      FF.es (D.Pl l) (w l) (stream D t (2 * l + 1)) i :=
    Router.argTo_congr fun e hx => hlr e (by omega)
  rw [hes] at r2 r3 r4
  have hsc : val t .sc (l / 2) 0 i = FF.sc (D.Pl l) tb (w l) (stream D t (2 * l + 1)) i := by
    have h5 : val t .sc (l / 2) 0 i = tb.SIGM ((rv t (l / 2) i).mr D.nx + 2 ^ 15) := r5
    have h6 : (rv t (l / 2) i).mr D.nx =
        val t .lr (l / 2) (FF.es (D.Pl l) (w l) (stream D t (2 * l + 1)) i) i := r4
    rw [h5, h6, hlr _ r2]
    rfl
  refine ⟨fun e hx => ⟨hly e hx, hl3 e hx, hlr e hx, ?_, r3 e hx⟩,
    r2, hsc,
    fun j hj => ⟨?_, ((r7 j hj).2).trans (hm j hj)⟩⟩
  · rw [← hly e hx]
    exact (r1 e hx).2.2.2.1
  · have h5 : val t .xr (l / 2) j i = rhu (val t .sc (l / 2) 0 i * val t .m l j i) 16 := (r7 j hj).1
    rw [h5, hsc, hmP j hj]
    rfl

end

/-! ## The hidden layer -/

section
variable {D : Dim} {tb : Tables} {L0 : ℕ} {first : Bool} {w : ℕ → LayerW} {emb : Mat}
  {tok : ℕ → ℕ} {t : Cell → ℤ}
variable (h : RFraw D tb L0 first (ZMod p) w emb tok t)
variable {l i : ℕ} (hl : l < D.nl) (hi : i < D.T) {P' : Params} (hOK : tb.OK P') (S : SzR D)
  (hW : WFabs (w l)) (hmP : ∀ j < D.d, val t .m l j i = FF.m (D.Pl l) (stream D t (2 * l + 1)) i j)
  (hL0 : L0 % 2 = 0)
include h hl hi hOK S hW hmP hL0

/-- Steps L7, L7r at every hidden unit, under the hypotheses of its statement, with (FL40) on the
routed expert: sl, up and hh are the program's, and no range condition of UNIT fails. -/
theorem hidden_facts {x : ℕ} (hx : x < D.f) :
    val t .sl l x i =
      UNIT.sl tb D.d (FF.z (D.Pl l) tb (w l) (L0 + l) (stream D t (2 * l + 1)) i x)
        (FF.wg (D.Pl l) (w l) (L0 + l) (stream D t (2 * l + 1)) i x) (FF.kG (D.Pl l) (L0 + l) x) ∧
    val t .up l x i =
      UNIT.up D.d (FF.z (D.Pl l) tb (w l) (L0 + l) (stream D t (2 * l + 1)) i x)
        (FF.wu (D.Pl l) (w l) (L0 + l) (stream D t (2 * l + 1)) i x) (FF.kU (D.Pl l) (L0 + l) x) ∧
    hh t l x i = FF.hh (D.Pl l) tb (w l) (L0 + l) (stream D t (2 * l + 1)) i x ∧
    UNIT.OK D.d (FF.z (D.Pl l) tb (w l) (L0 + l) (stream D t (2 * l + 1)) i x)
      (FF.wg (D.Pl l) (w l) (L0 + l) (stream D t (2 * l + 1)) i x)
      (FF.wu (D.Pl l) (w l) (L0 + l) (stream D t (2 * l + 1)) i x)
      (FF.kG (D.Pl l) (L0 + l) x) (FF.kU (D.Pl l) (L0 + l) x) := by
  by_cases hr : routed D l x = true
  · -- the routed expert
    have hrP := (routed_iff (D := D) hL0 l x).mp hr
    have he : isExpL l = true := by
      unfold routed at hr
      exact (Bool.and_eq_true _ _ ▸ hr).1
    obtain ⟨r1, r2, -, r4⟩ := router_facts h hl hi hOK S hW hmP he
    have hz : FF.z (D.Pl l) tb (w l) (L0 + l) (stream D t (2 * l + 1)) i x =
        FF.xr (D.Pl l) tb (w l) (stream D t (2 * l + 1)) i := by
      unfold FF.z
      rw [if_pos hrP]
    have hwg : FF.wg (D.Pl l) (w l) (L0 + l) (stream D t (2 * l + 1)) i x =
        fun u => (w l).Eg (FF.es (D.Pl l) (w l) (stream D t (2 * l + 1)) i) u (x - D.fe) := by
      unfold FF.wg
      simp only [if_pos hrP]
      rfl
    have hwu : FF.wu (D.Pl l) (w l) (L0 + l) (stream D t (2 * l + 1)) i x =
        fun u => (w l).Eu (FF.es (D.Pl l) (w l) (stream D t (2 * l + 1)) i) u (x - D.fe) := by
      unfold FF.wu
      simp only [if_pos hrP]
      rfl
    have hkG : FF.kG (D.Pl l) (L0 + l) x = kG D l x := by
      unfold FF.kG FFSeg.kG
      rw [if_pos hrP, if_pos hr]
    have hkU : FF.kU (D.Pl l) (L0 + l) x = kU D l x := by
      unfold FF.kU FFSeg.kU
      rw [if_pos hrP, if_pos hr]
    have eg : Ag D t (fun l => LW.ofInt ℤ (w l)) l x i =
        dot D.d (FF.xr (D.Pl l) tb (w l) (stream D t (2 * l + 1)) i) fun u =>
          (w l).Eg (FF.es (D.Pl l) (w l) (stream D t (2 * l + 1)) i) u (x - D.fe) := by
      unfold Ag
      rw [if_pos hr, sum_ind r2 (fun e hx' => (r1 e hx').2.2.2.2)]
      exact All.dot_congr _ fun j hj => (r4 j hj).1
    have eu : Au D t (fun l => LW.ofInt ℤ (w l)) l x i =
        dot D.d (FF.xr (D.Pl l) tb (w l) (stream D t (2 * l + 1)) i) fun u =>
          (w l).Eu (FF.es (D.Pl l) (w l) (stream D t (2 * l + 1)) i) u (x - D.fe) := by
      unfold Au
      rw [if_pos hr, sum_ind r2 (fun e hx' => (r1 e hx').2.2.2.2)]
      exact All.dot_congr _ fun j hj => (r4 j hj).1
    obtain ⟨-, a2, a3, a4, a5⟩ :=
      NWU.unit_facts h hl hx hi hOK S.toSz eg eu
        (fun j hj => by rw [← (r4 j hj).1]; exact (r4 j hj).2)
        (fun j _ => hW.Eg _ j _) (fun j _ => hW.Eu _ j _)
    unfold FF.hh
    rw [hz, hwg, hwu, hkG, hkU]
    exact ⟨a2, a3, a4, a5⟩
  · -- a dense layer, or the shared expert
    have hr' : routed D l x = false := by simpa using hr
    have hrP : ¬ FF.routed (D.Pl l) (L0 + l) x := fun hc =>
      hr ((routed_iff (D := D) hL0 l x).mpr hc)
    have hz : FF.z (D.Pl l) tb (w l) (L0 + l) (stream D t (2 * l + 1)) i x =
        FF.m (D.Pl l) (stream D t (2 * l + 1)) i := by
      unfold FF.z
      rw [if_neg hrP]
    have hwg : FF.wg (D.Pl l) (w l) (L0 + l) (stream D t (2 * l + 1)) i x =
        fun u => (w l).Wg u x := by
      unfold FF.wg
      simp only [if_neg hrP]
    have hwu : FF.wu (D.Pl l) (w l) (L0 + l) (stream D t (2 * l + 1)) i x =
        fun u => (w l).Wu u x := by
      unfold FF.wu
      simp only [if_neg hrP]
    have hkG : FF.kG (D.Pl l) (L0 + l) x = kG D l x := by
      unfold FF.kG FFSeg.kG
      rw [if_neg hrP, if_neg hr]
    have hkU : FF.kU (D.Pl l) (L0 + l) x = kU D l x := by
      unfold FF.kU FFSeg.kU
      rw [if_neg hrP, if_neg hr]
    obtain ⟨eg0, eu0⟩ := NWU.acc_shared (t := t) (w := w) (i := i) hr'
    have eg := eg0.trans (All.dot_congr (fun j => (w l).Wg j x) hmP)
    have eu := eu0.trans (All.dot_congr (fun j => (w l).Wu j x) hmP)
    obtain ⟨-, a2, a3, a4, a5⟩ :=
      NWU.unit_facts h hl hx hi hOK S.toSz eg eu
        (fun j hj => by rw [← hmP j hj]; exact m_abs hmP j hj)
        (fun j _ => hW.Wg j _) (fun j _ => hW.Wu j _)
    unfold FF.hh
    rw [hz, hwg, hwu, hkG, hkU]
    exact ⟨a2, a3, a4, a5⟩

/-- Under the hypotheses of its statement, |hh| ≤ 4,095 · 2^15: what the bound on the accumulator
of the site D uses. -/
theorem hh_abs {x : ℕ} (hx : x < D.f) :
    |FF.hh (D.Pl l) tb (w l) (L0 + l) (stream D t (2 * l + 1)) i x| ≤ 4095 * 2 ^ 15 := by
  rw [← (hidden_facts h hl hi hOK S hW hmP hL0 hx).2.2.1]
  obtain ⟨-, -, -, -, a5, a6⟩ := NWU.gate_facts h hl hx hi hOK S.toSz
  unfold hh
  rw [abs_mul]
  refine mul_le_mul a6 ?_ (abs_nonneg _) (by norm_num)
  unfold Fits16 at a5
  rw [abs_le]
  constructor <;> omega

/-- Under the hypotheses of its statement, no range condition of (PL8) to (PL13) fails at position
i, given that of the normalisation. -/
theorem ok_facts (hn : NORM.OK (D.Pl l).n2 D.d (stream D t (2 * l + 1) i)) :
    NORM.OK (D.Pl l).n2 D.P.d (stream D t (2 * l + 1) i) ∧
    (hasExperts (L0 + l) →
      ∀ e < D.P.nexp, Fits16 (FF.ly (D.Pl l) (w l) (stream D t (2 * l + 1)) i e)) ∧
    ∀ j < FF.units (D.Pl l) (L0 + l), UNIT.OK D.P.d
      (FF.z (D.Pl l) tb (w l) (L0 + l) (stream D t (2 * l + 1)) i j)
      (FF.wg (D.Pl l) (w l) (L0 + l) (stream D t (2 * l + 1)) i j)
      (FF.wu (D.Pl l) (w l) (L0 + l) (stream D t (2 * l + 1)) i j)
      (FF.kG (D.Pl l) (L0 + l) j) (FF.kU (D.Pl l) (L0 + l) j) := by
  refine ⟨hn,
    fun heP e hx => ((router_facts h hl hi hOK S hW hmP ((exp_iff hL0 l).mpr heP)).1 e hx).2.2.2.1,
    fun j hj => ?_⟩
  refine (hidden_facts h hl hi hOK S hW hmP hL0 (x := j) ?_).2.2.2
  unfold FF.units at hj
  split_ifs at hj
  · rw [S.f2]
    exact hj
  · exact hj

end

/-! ## The embedding -/

/-- (J11): step (PL1), in the first segment. -/
theorem emb_facts {D : Dim} {tb : Tables} {L0 : ℕ} {w : ℕ → LayerW} {emb : Mat} {tok : ℕ → ℕ}
    {t : Cell → ℤ} (h : RFraw D tb L0 true (ZMod p) w emb tok t)
    (hE : ∀ a b, |emb a b| ≤ 2155905152) {i j : ℕ} (hi : i < D.T) (hj : j < D.d) :
    xS D t 0 j i = emb (tok i) j := by
  have hk : (p : ℤ) ∣ xS D t 0 j i - emb (tok i) j :=
    Int.modEq_zero_iff_dvd.mp (idn_modEq D tb L0 true w emb tok t _ h (j := .j11 j i) ⟨rfl, hj, hi⟩)
  have c0 := cellB h (c := ⟨.x0, 0, 0, j, i⟩) ⟨(by decide : 0 < 5), (by decide : 0 < 1), hj, hi⟩
  have c1 := cellB h (c := ⟨.x0, 1, 0, j, i⟩) ⟨(by decide : 1 < 5), (by decide : 0 < 1), hj, hi⟩
  have c2 := cellB h (c := ⟨.x0, 2, 0, j, i⟩) ⟨(by decide : 2 < 5), (by decide : 0 < 1), hj, hi⟩
  have c3 := cellB h (c := ⟨.x0, 3, 0, j, i⟩) ⟨(by decide : 3 < 5), (by decide : 0 < 1), hj, hi⟩
  have c4 := cellB h (c := ⟨.x0, 4, 0, j, i⟩) ⟨(by decide : 4 < 5), (by decide : 0 < 1), hj, hi⟩
  have hb := abs_le.mp (hE (tok i) j)
  have hx : xS D t 0 j i =
      t ⟨.x0, 0, 0, j, i⟩ + 256 * t ⟨.x0, 1, 0, j, i⟩ + 65536 * t ⟨.x0, 2, 0, j, i⟩ +
        16777216 * t ⟨.x0, 3, 0, j, i⟩ + 4294967296 * t ⟨.x0, 4, 0, j, i⟩ := by
    unfold xS streamAt
    rw [if_pos rfl]
    simp only [val, Arr.nCell, Arr.off, sum_range_succ, sum_range_zero, Int.cast_id]
    norm_num
  have := eq_of_dvd hk (by rw [hx, abs_lt]; constructor <;> omega)
  omega

end NWR

end Cm.TI.FFSeg
