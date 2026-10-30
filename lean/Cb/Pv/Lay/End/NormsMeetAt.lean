-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/NormsMeetAt.lean: the premises of norms_pull can be met together.

norms_pull (Cb/Pv/Lay/End/NormsA.lean) has premises on sizes, on names and forms of late entries, on
the state that the first sumcheck's output carries, and that the pull-back of the ledger of the
claims on the norms holds. This file shows that they can be met together. Take any letters P whose
cells are read linearly, any early entries m, any points, drawn elements and coefficients. Ask of
the cells three things alone: at the extensions of each norm's bytes at the token point the two
lines that read the bytes alone hold (numbers 12 and 16), and the extension of each defect d10
vanishes at zt. Then there are sent scalars and two outputs, with the given points inside, at which
all premises hold. (The premises on names are met by the lay of Cb/Pv/Lay/End/NormsLay.lean.)

Main definitions: Dgs (the extensions of a norm's bytes), sWAt, sPAt, zAt, o1At, o2At (the scalars
and outputs). Main theorems: last_meets (NormsLast at these), norms_meets (the premises of
norms_pull that are not on sizes).

Limits. Nothing says that the scalars are an honest prover's: dl is any element: what the letter of
product 4 holds more and that of product 5 less, as the two stand in one line together
(Cb/Pv/Lay/End/NormsMeet.lean). That cells with the three properties exist is shown by theorems in
Cb/Pv/Lay/End/TestNormsPull.lean (small sizes) and
Cb/Pv/Lay/End/TestLayBill.lean [not in this library] (the reference sizes), not here.


-/
import Cb.Pv.Lay.End.NormsMeet
import Cb.Pv.Lay.End.NormsPullIff

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cb.Pv.Lay.End

open Finset Cb Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model (Scl)
open Inst.Model.FFSeg (Cell led Pv npOf d10 lDd)
open Inst.Model.Ledger (l1 h1 sig rr rq)
open Blocks (ext)

variable {E : Type} [Field E] [Fintype E] [scl : Scl] (P : NormPar0 E) [DecidableEq P.J]

/-- The extensions of the bytes of norm ν at the token point. -/
def Dgs (m : P.J → E) (p : Fin P.D.lT → E) (ν n : ℕ) : E :=
  ext P.D.lT (fun i => led (P.rd m) ν i n) (Blocks.nat p)

/-- The scalars sent for the sums of squares. -/
def sWAt (m : P.J → E) (p : Fin P.D.lT → E) : Fin (P.D.nNu * 9) → E := fun n =>
  hidW (Dgs P m p ((n : ℕ) / 9)) ((n : ℕ) % 9) +
    m (P.mkS (finProdFinEquiv.symm n).1 (finProdFinEquiv.symm n).2)

/-- The hidden row products, by their number. -/
def hpAt (m : P.J → E) (p : Fin P.D.lT → E) (dl : E) (x : ℕ) : E :=
  hidP (npOf P.D (x / 7)) (Dgs P m p (x / 7)) dl (x % 7)

/-- The scalars sent for the row products. -/
def sPAt (m : P.J → E) (p : Fin P.D.lT → E) (dl : E) : Fin (P.D.nNu * 7) → E := fun n =>
  hpAt P m p dl n + m (P.mkP n)

/-- The sent sum of the token sumcheck. -/
def zAt (m : P.J → E) (p : Fin P.D.lT → E) (dl σ : E) : E :=
  ∑ x ∈ range (7 * P.D.nNu), σ ^ x * hpAt P m p dl x + m P.rP

/-- The state of the first sumcheck's claim. -/
def st1At (m : P.J → E) (p : Fin P.D.lT → E) (c : E) (ρj : Fin (P.D.lL + 1) → E) :
    P.sq.R.L.toSum.T.par.St :=
  (((p, fun q => sWAt P m p (finProdFinEquiv q)), c), ρj)

/-- The first output without its values. -/
noncomputable def o1Base (m : P.J → E) (p : Fin P.D.lT → E) (c : E)
    (ρj : Fin (P.D.lL + 1) → E) (eps : E) (pt : PPt P.sq.R.L.toSum.T.par.fmt) :
    P.sq.R.L.toSum.T.par.Out := ⟨st1At P m p c ρj, eps, pt, 0, fun _ => 0⟩

/-- The values of the first output. -/
noncomputable def v1At (m : P.J → E) (p : Fin P.D.lT → E) (c : E) (ρj : Fin (P.D.lL + 1) → E)
    (eps : E) (pt : PPt P.sq.R.L.toSum.T.par.fmt) : Bool → E := fun bb =>
  ext (P.D.lL + 1 + (lDd P.D + P.D.lT)) (Pv P.D (P.rd m) c)
      (Blocks.nat fun i => (noKept P.sq.R.L.Sm).outPt P.sq.R.L.Mk (o1Base P m p c ρj eps pt)
        (P.sq.R.L.e.symm i)) +
    m (P.cS bb) * (noKept P.sq.R.L.Sm).outB P.sq.R.L.Mk (o1Base P m p c ρj eps pt)

/-- An output with given state, coefficient, point and values whose first output claim holds. -/
noncomputable def outU (Y : PscPar E) (st : Y.St) (eps : E) (pt : PPt Y.fmt) (vals : Y.A → E)
    (m : Y.J → E) : Y.Out :=
  ⟨st, eps, pt,
    hU (Y.vars st) (Y.W st m) (Y.hp st pt) + eps * hPsi (Y.vars st) (Y.hp st pt) * Y.inc st m +
      eps * ∑ b, Y.S1 st (Y.hp st pt) vals b * Y.Gb st m b (Y.hp st pt) +
      eps * Y.S0 st (Y.hp st pt) vals, vals⟩

omit [Fintype E] scl in
theorem outU_holds (Y : PscPar E) (st : Y.St) (eps : E) (pt : PPt Y.fmt) (vals : Y.A → E)
    (m : Y.J → E) : Y.UHolds (outU Y st eps pt vals m) m :=
  (add_sub_cancel_right _ _).symm

/-- The first output. -/
noncomputable def o1At (m : P.J → E) (p : Fin P.D.lT → E) (c : E) (ρj : Fin (P.D.lL + 1) → E)
    (eps : E) (pt : PPt P.sq.R.L.toSum.T.par.fmt) : P.sq.R.L.toSum.T.par.Out :=
  outU P.sq.R.L.toSum.T.par (st1At P m p c ρj) eps pt (v1At P m p c ρj eps pt) m

/-- The second output without its values. -/
noncomputable def o2Base (m : P.J → E) (p : Fin P.D.lT → E) (dl σ eps : E)
    (pt : PPt P.rows.tok.toSum.T.par.fmt) : P.rows.tok.toSum.T.par.Out :=
  ⟨((p, sPAt P m p dl), σ), eps, pt, 0, fun _ => 0⟩

/-- The values of the second output. -/
noncomputable def v2At (m : P.J → E) (p : Fin P.D.lT → E) (dl σ eps : E)
    (pt : PPt P.rows.tok.toSum.T.par.fmt) : Fin P.D.nNu × Fin 4 → E := fun a =>
  ext P.D.lT (fun i => rowVal (led (P.rd m) a.1 i) a.2)
      (Blocks.nat (P.rows.tok.Kp.outPt P.rows.tok.Mk (o2Base P m p dl σ eps pt))) +
    m (P.cP a) * P.rows.tok.Kp.outB P.rows.tok.Mk (o2Base P m p dl σ eps pt)

/-- The second output. -/
noncomputable def o2At (m : P.J → E) (p : Fin P.D.lT → E) (dl σ eps : E)
    (pt : PPt P.rows.tok.toSum.T.par.fmt) : P.rows.tok.toSum.T.par.Out :=
  outU P.rows.tok.toSum.T.par ((p, sPAt P m p dl), σ) eps pt (v2At P m p dl σ eps pt) m

variable {J₂ : Type}

omit [DecidableEq P.J] in
/-- NormsLast at these scalars and outputs, whatever the late entries are. -/
theorem last_meets (U : NormsReads J₂) (m : P.J → E) (u : J₂ → E) (p : Fin P.D.lT → E)
    (c σ dl e1 e2 : E) (ρj : Fin (P.D.lL + 1) → E) (pt1 : PPt P.sq.R.L.toSum.T.par.fmt)
    (pt2 : PPt P.rows.tok.toSum.T.par.fmt) (zt : ℕ → E) (b s : ℕ) (hl : lDd P.D = b + s)
    (h12 : ∀ ν, ν < P.D.nNu →
      l1 (Dgs P m p ν) + h1 (Dgs P m p ν) - 2 * sig (Dgs P m p ν) = 0)
    (h16 : ∀ ν, ν < P.D.nNu → rr (Dgs P m p ν) + rq (Dgs P m p ν) - sig (Dgs P m p ν) + 1 = 0)
    (hHot : ∀ l, l < P.D.ne → ext P.D.lT (d10 P.D (P.rd m) l) zt = 0) :
    NormsLast (namesAt P U)
      (normsEAt P p (sWAt P m p) c (o1At P m p c ρj e1 pt1) (sPAt P m p dl) σ (zAt P m p dl σ)
        (o2At P m p dl σ e2 pt2) zt) P.D (P.rd m) (P.D.lL + 1) b s (Sum.elim m u) := by
  have hP : ∀ x, x < P.D.nNu * 7 →
      (if h : x < P.D.nNu * 7 then sPAt P m p dl ⟨x, h⟩ else 0) -
        Sum.elim m u (if h : x < P.D.nNu * 7 then .inl (P.mkP ⟨x, h⟩) else .inl P.rP) =
      hpAt P m p dl x := fun x hx => by
    rw [dif_pos hx, dif_pos hx]
    exact add_sub_cancel_right _ _
  have hW : ∀ x, x < P.D.nNu * 9 →
      (if h : x < P.D.nNu * 9 then sWAt P m p ⟨x, h⟩ else 0) -
        Sum.elim m u (if h : x < P.D.nNu * 9 then
          .inl (P.mkS (finProdFinEquiv.symm ⟨x, h⟩).1 (finProdFinEquiv.symm ⟨x, h⟩).2)
          else .inl P.rP) = hidW (Dgs P m p (x / 9)) (x % 9) := fun x hx => by
    rw [dif_pos hx, dif_pos hx]
    exact add_sub_cancel_right _ _
  have eβ : ∀ A v β : E, A + v * β - β * v = A := fun A v β => by ring
  refine ⟨?_, ?_, ?_, fun x hx => ?_, fun ν hν k _ => ?_, hHot⟩
  · rw [← hl]
    exact eβ _ (m (P.cS false)) _
  · exact (eβ _ (m (P.cS true)) _).trans (eβ _ (m (P.cS false)) _).symm
  · show zAt P m p dl σ - m P.rP = _
    unfold zAt
    rw [add_sub_cancel_right]
    refine sum_congr rfl fun x hx => ?_
    have hx' : x < P.D.nNu * 7 := by
      rw [Nat.mul_comm]
      exact mem_range.mp hx
    exact congrArg _ (hP x hx').symm
  · have hx' : x < P.D.nNu * 4 := by
      rw [Nat.mul_comm]
      exact hx
    show (if h : x < P.D.nNu * 4 then v2At P m p dl σ e2 pt2 (finProdFinEquiv.symm ⟨x, h⟩) else 0) -
      _ * Sum.elim m u (if h : x < P.D.nNu * 4 then .inl (P.cP (finProdFinEquiv.symm ⟨x, h⟩))
        else .inl P.rP) = _
    rw [dif_pos hx', dif_pos hx']
    show v2At P m p dl σ e2 pt2 (finProdFinEquiv.symm ⟨x, hx'⟩) -
      _ * m (P.cP (finProdFinEquiv.symm ⟨x, hx'⟩)) = _
    refine (eβ _ (m (P.cP (finProdFinEquiv.symm ⟨x, hx'⟩))) _).trans ?_
    refine Blocks.ext_congr (fun i _ => ?_) _
    have q1 : (((finProdFinEquiv.symm (⟨x, hx'⟩ : Fin (P.D.nNu * 4))).1 : Fin P.D.nNu) : ℕ) =
        x / 4 := rfl
    have q2 : (((finProdFinEquiv.symm (⟨x, hx'⟩ : Fin (P.D.nNu * 4))).2 : Fin 4) : ℕ) = x % 4 := rfl
    rw [← match_rowVal, q1, q2]
    rfl
  · have e1' := idnP_hid P.two (npOf P.D ν) (Dgs P m p ν) dl (h12 ν hν) (h16 ν hν) k
    rw [← e1']
    refine idnP_congr (npOf P.D ν) _ (fun x hx => ?_) (fun j hj => ?_) k
    · have hlt : 9 * ν + x < P.D.nNu * 9 := by omega
      refine (hW (9 * ν + x) hlt).trans ?_
      rw [(by omega : (9 * ν + x) / 9 = ν), (by omega : (9 * ν + x) % 9 = x)]
    · have hlt : 7 * ν + j < P.D.nNu * 7 := by omega
      refine (hP (7 * ν + j) hlt).trans ?_
      unfold hpAt
      rw [(by omega : (7 * ν + j) / 7 = ν), (by omega : (7 * ν + j) % 7 = j)]

/-- The premises of norms_pull that are not on sizes or names, at any lay of the norms' names: the
state of the first output holds the drawn element, and the pull-back of the ledger holds. -/
theorem norms_meets [Fintype J₂] [DecidableEq J₂] (Y : LateLay NormsNm J₂)
    (hrd : ∀ (a b : E) (m m' : P.J → E) (c : Cell),
      P.rd (fun j => a * m j + b * m' j) c = a * P.rd m c + b * P.rd m' c)
    (m : P.J → E) (p : Fin P.D.lT → E) (c σ dl e1 e2 : E) (ρj : Fin (P.D.lL + 1) → E)
    (pt1 : PPt P.sq.R.L.toSum.T.par.fmt) (pt2 : PPt P.rows.tok.toSum.T.par.fmt) (zt : ℕ → E)
    (b s B : ℕ) (hl : lDd P.D = b + s) (hd : P.D.d = B * 2 ^ s) (hB : B ≤ 2 ^ b)
    (gXi : ∀ ν l kh, ν < P.D.nNu → l < 5 → kh < B → Y.good (.xi ν l kh))
    (gP : ∀ ν n, ν < P.D.nNu → n < 99 → Y.good (.atP ν n))
    (gR : ∀ ν n, ν < P.D.nNu → n < 99 → Y.good (.atR ν n))
    (gS : ∀ l x, l < P.D.ne → x < P.D.nx → Y.good (.sel l x))
    (h12 : ∀ ν, ν < P.D.nNu →
      l1 (Dgs P m p ν) + h1 (Dgs P m p ν) - 2 * sig (Dgs P m p ν) = 0)
    (h16 : ∀ ν, ν < P.D.nNu → rr (Dgs P m p ν) + rq (Dgs P m p ν) - sig (Dgs P m p ν) + 1 = 0)
    (hHot : ∀ l, l < P.D.ne → ext P.D.lT (d10 P.D (P.rd m) l) zt = 0) :
    (o1At P m p c ρj e1 pt1).st.1.2 = c ∧
      TWhole.Ledger.Holds (Cb.Sub.pullL
        (lateA Y fun x => toAff (normsFm P.rd P.D
          (normsEAt P p (sWAt P m p) c (o1At P m p c ρj e1 pt1) (sPAt P m p dl) σ (zAt P m p dl σ)
            (o2At P m p dl σ e2 pt2) zt) (P.D.lL + 1) b s x))
        (normsLed (namesAt P (readsAt Y id))
          (normsEAt P p (sWAt P m p) c (o1At P m p c ρj e1 pt1) (sPAt P m p dl) σ (zAt P m p dl σ)
            (o2At P m p dl σ e2 pt2) zt) (u1At P (o1At P m p c ρj e1 pt1))
          (u2At P (o2At P m p dl σ e2 pt2)) P.D (P.D.lL + 1) b B)) m :=
  ⟨rfl, (norms_pull_iff P hrd Y id _ p _ c _ _ σ _ _ zt m b s B hl hd hB (fun _ _ => rfl)
    gXi gP gR gS).2
    ⟨last_meets P _ m _ p c σ dl e1 e2 ρj pt1 pt2 zt b s hl h12 h16 hHot,
      outU_holds _ _ _ _ _ _, outU_holds _ _ _ _ _ _⟩⟩

end Cb.Pv.Lay.End
