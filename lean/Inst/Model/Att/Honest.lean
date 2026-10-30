-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Inst/Model/Att/Honest.lean: the honest trace of an attention segment satisfies the field relation,
  at the reference sizes (`Dim.ref`), for valid scales (`Lawful`) and tables.

    `honest`   `Spec.honest` of Inst/Model/Att/Trace.lean
  Inst/Model/Att/HonestGen.lean proves the statement for a trace `honG` that is written by the same
  rule from arbitrary integer inputs of absolute value at most 2,047. Here the trace `hon` of
  Inst/Model/Att/Trace.lean, which is written from the values of the integer program
  (Inst/Model/Program.lean, namespace `Att`), is shown to be `honG` at the program's q, kx, v and o,
  each layer at its own parameters (`hon_eq`), and the conditions `Adm` are checked: q, kx, v are
  outputs of clamps; o is the quotient of step (PA7).

  Notation (Trace.lean: Inst/Model/Att/Trace.lean): `D` : `Dim`: the sizes of an attention segment
  (Inst/Model/Att/Index.lean); `P` : ℕ → `Params`: P lam: the parameters at which layer lam of the
  segment runs (Trace.lean); `tb` : `Tables`: the five table functions that the program reads
  (Inst/Model/Program.lean); `w` : ℕ → `LayerW`: the weight matrices of each layer
  (Inst/Model/Program.lean); `L0` : ℕ: layer lam of the segment is layer L0 + lam (`hSc`,
  Trace.lean); `x` : ℕ → ℕ → `Vec`: the streams before the layers' attention blocks (`hon`,
  Trace.lean); `hSc` to `hRE`: see Trace.lean; `scP` to `reP`: see Inst/Model/Att/HonestGen.lean.
-/
import Inst.Model.Att.HonestGen

set_option autoImplicit false

namespace Inst.Model.AttSeg.Hon

open Finset

theorem abs_clamp_le {c : ℤ} (hc : 0 ≤ c) (a : ℤ) : |clamp c a| ≤ c := by
  unfold clamp
  rw [abs_le]
  constructor
  · exact le_min (le_max_right _ _) (by linarith)
  · exact min_le_right _ _

variable (D : Dim) (P : ℕ → Params) (tb : Tables) (w : ℕ → LayerW) (L0 : ℕ) (x : ℕ → ℕ → Vec)

/-- the program's q, kx, v at the indices of the segment -/
def Qp (b g i n : ℕ) : ℤ :=
  Att.q (P (D.lamOf b)) tb (w (D.lamOf b)) (L0 + D.lamOf b) (x (D.lamOf b))
    i (D.ch * D.head g b + n)
def Kp (lam g j n : ℕ) : ℤ := Att.kx (P lam) tb (w lam) (L0 + lam) (x lam) j (D.ch * g + n)
def Vp (lam g j n : ℕ) : ℤ := Att.v (P lam) (w lam) (x lam) j (D.ch * g + n)

/-- the sizes of the segment are those of the program -/
structure Fit [scl : Scl] (D : Dim) (P : Params) : Prop where
  ch : P.ch = D.ch
  na : P.nq / P.nkv = D.na
  pos : 0 < D.na
  rows : P.expRows = D.u0
  sh : P.sh = D.sh

variable {D P}

theorem Fit.kvOf [scl : Scl] {P : Params} (hF : Fit D P) (g b : ℕ) :
    Att.kvOf P (D.head g b) = g := by
  unfold Att.kvOf Dim.head Dim.aOf
  rw [hF.na, Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right _ _ hF.pos,
    Nat.div_eq_of_lt (Nat.mod_lt _ hF.pos), Nat.zero_add]

section Link

variable [scl : Scl]
variable (hF : ∀ lam, Fit D (P lam))
include hF

local notation "Q'" => Qp D P tb w L0 x
local notation "K'" => Kp D P tb w L0 x
local notation "V'" => Vp D P w x
local notation "O'" => hOut D P tb w L0 x

theorem hSc_eq (b g i : ℕ) : hSc D P tb w L0 x b g i = scP D Q' K' b g i := by
  funext j
  unfold hSc Att.sc scP Qp Kp
  rw [(hF _).kvOf, (hF _).ch]

theorem hMx_eq (b g i : ℕ) : hMx D P tb w L0 x b g i = mxP D Q' K' b g i := by
  have e := hSc_eq tb w L0 x hF b g i
  unfold hMx Att.mx mxP
  rw [← e]
  rfl

theorem hGp_eq (ρ : Reg) (b y : ℕ) : hGp D P tb w L0 x ρ b y = gpP D Q' K' ρ b y := by
  cases ρ <;> simp only [hGp, gpP, hMx_eq tb w L0 x hF, hSc_eq tb w L0 x hF]

theorem hRm_eq (ρ : Reg) (b y : ℕ) :
    hRm D P tb w L0 x ρ b y = rmOf D.sh D.u0 (gpP D Q' K' ρ b y) := by
  unfold hRm rmOf
  rw [hGp_eq tb w L0 x hF]

theorem hFl_eq (ρ : Reg) (b y : ℕ) :
    hFl D P tb w L0 x ρ b y = flOf D.sh D.u0 (gpP D Q' K' ρ b y) := by
  unfold hFl flOf
  rw [hGp_eq tb w L0 x hF]

theorem hWt_eq (ρ : Reg) (b y : ℕ) :
    hWt D P tb w L0 x ρ b y = wOf D.sh D.u0 tb (gpP D Q' K' ρ b y) := by
  unfold hWt wOf
  rw [hGp_eq tb w L0 x hF]

/-- the weight of step (PA4) -/
theorem wt_eq (b g i j : ℕ) :
    Att.wt (P (D.lamOf b)) tb (w (D.lamOf b)) (L0 + D.lamOf b) (x (D.lamOf b)) (D.head g b) i j =
      wtP D tb Q' K' b g i j := by
  have e1 : Att.mx (P (D.lamOf b)) tb (w (D.lamOf b)) (L0 + D.lamOf b)
        (x (D.lamOf b)) (D.head g b) i =
      mxP D Q' K' b g i :=
    hMx_eq tb w L0 x hF b g i
  have e2 : Att.sc (P (D.lamOf b)) tb (w (D.lamOf b)) (L0 + D.lamOf b)
        (x (D.lamOf b)) (D.head g b) i j =
      scP D Q' K' b g i j :=
    congrFun (hSc_eq tb w L0 x hF b g i) j
  unfold Att.wt Att.u wtP
  rw [e1, e2, (hF _).rows, (hF _).sh, wOf_eq_wt]

theorem hDen_eq (b g i : ℕ) : hDen D P tb w L0 x b g i = denP D tb Q' K' b g i := by
  unfold hDen Att.den denP
  exact sum_congr rfl fun j _ => wt_eq tb w L0 x hF b g i j

theorem hAc_eq (b g i n : ℕ) : hAc D P tb w L0 x b g i n = acP D tb Q' K' V' b g i n := by
  unfold hAc Att.ac acP
  refine sum_congr rfl fun j _ => ?_
  rw [wt_eq tb w L0 x hF b g i j, (hF _).kvOf, (hF _).ch]
  rfl

theorem hRE_eq (b g i n : ℕ) : hRE D P tb w L0 x b g i n = reP D tb Q' K' V' O' b g i n := by
  unfold hRE reP
  rw [hAc_eq tb w L0 x hF, hDen_eq tb w L0 x hF]

/-- (PA7) at a channel of a head -/
theorem hOut_eq (b g i : ℕ) {n : ℕ} (hn : n < D.ch) :
    hOut D P tb w L0 x b g i n =
      (2 * acP D tb Q' K' V' b g i n + denP D tb Q' K' b g i) / (2 * denP D tb Q' K' b g i) := by
  have hpos : 0 < D.ch := Nat.two_pow_pos _
  have e1 : (D.ch * D.head g b + n) / D.ch = D.head g b := by
    rw [Nat.mul_comm]
    exact (Dim.div_step hpos hn).1
  have e2 : (D.ch * D.head g b + n) % D.ch = n := by
    rw [Nat.mul_comm]
    exact (Dim.div_step hpos hn).2
  rw [← hAc_eq tb w L0 x hF, ← hDen_eq tb w L0 x hF]
  unfold hOut Att.o hAc hDen
  rw [(hF _).ch, e1, e2]

/-- If the layers' parameters fit D (hF), the honest trace of Inst/Model/Att/Trace.lean is the trace
of Inst/Model/Att/HonestGen.lean at the program's values. -/
theorem hon_eq : hon D P tb w L0 x = honG D tb Q' K' V' O' := by
  funext c
  cases c with
  | c ρ jj b y =>
    match jj with
    | 0 => simp only [hon, honG, hRm_eq tb w L0 x hF]
    | 1 => simp only [hon, honG, hRm_eq tb w L0 x hF]
    | 2 => simp only [hon, honG, hFl_eq tb w L0 x hF]
    | 3 => simp only [hon, honG, hWt_eq tb w L0 x hF]
    | _ + 4 => simp only [hon, honG, hWt_eq tb w L0 x hF]
  | mx k b g i => simp only [hon, honG, hMx_eq tb w L0 x hF]
  | den k b g i => simp only [hon, honG, hDen_eq tb w L0 x hF]
  | ib k b g i =>
    simp only [hon, honG, hSc_eq tb w L0 x hF]
    rfl
  | qh b g i n => simp only [hon, honG, hRE_eq tb w L0 x hF]
  | qh' b g i n => simp only [hon, honG, hRE_eq tb w L0 x hF, hDen_eq tb w L0 x hF]
  | qry k b g i n => rfl
  | out k b g i n => rfl
  | key k lam g j n => rfl
  | val k lam g j n => rfl

/-- the conditions of Inst/Model/Att/HonestGen.lean (hypotheses below) -/
theorem adm (hch : (D.ch : ℤ) * 2047 ^ 2 ≤ Smax) (hT : D.T ≤ 1024) (hO : ExpOK D.sh D.u0)
    (hE : ∀ u : ℕ, u < D.u0 → 1 ≤ tb.Exp u ∧ tb.Exp u ≤ 2 ^ 12) (hE0 : tb.Exp 0 = 2 ^ 12) :
    Adm D tb Q' K' V' O' where
  q := fun _ _ _ _ => abs_clamp_le (by norm_num) _
  k := fun _ _ _ _ => abs_clamp_le (by norm_num) _
  v := fun _ _ _ _ => abs_clamp_le (by norm_num) _
  o := fun b g i _ hn => hOut_eq tb w L0 x hF b g i hn
  ch := hch
  T := hT
  ex := hO
  exp := hE
  exp0 := hE0

end Link

theorem fit_ref [scl : Scl] [law : Lawful] (lam : ℕ) : Fit Dim.ref (refP lam) :=
  ⟨(rfl : ppref.ch = Dim.ref.ch), (by decide : ppref.nq / ppref.nkv = Dim.ref.na),
    by decide, law.rows lam, law.sh lam⟩

/-- The honest trace satisfies the relation, for valid scales (`Lawful`), at the reference sizes and
for tables with `tb.OK ppref`. -/
theorem honest [scl : Scl] [law : Lawful] : Spec.honest := by
  intro tb htb w L0 x
  have hA := adm tb w L0 x fit_ref (by rw [ref_sizes.2.2.2.2.2.1]; unfold Smax; norm_num)
    (by rw [ref_sizes.2.2.2.2.1]) law.ex (fun u hu => htb.2.2.2.1 u hu) htb.2.2.2.2
  rw [hon_eq tb w L0 x fit_ref]
  exact ⟨rfraw_hon hA, abs_hon_le hA⟩

end Inst.Model.AttSeg.Hon
