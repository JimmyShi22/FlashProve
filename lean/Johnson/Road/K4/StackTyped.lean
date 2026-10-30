-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/StackTyped.lean: the form parts of the verifier's two long vectors are the two form
parts of the library's typed batched sumcheck (Cb/Pv/Lay/At/Inner.lean), place by place, if the
typed state holds what the verifier has heard.

Johnson/Road/K4/StackSides.lean writes the verifier's form parts as blocks of vaOf and vbOf, at the
record of reads rPort (Johnson/Road/FormsKeysPort.lean). The typed sumcheck has its own records: rE
for the early panels, rL for the late ones, which holds what the sumcheck of the terms has SHOWN in
the places of the reciprocals, the scores and the selectors' entries. Under the ties StackTies the
panels that are form parts read the same numbers in both.

Main names:
  `StackTies`: the typed state against the verifier's letters: the lookup's point, twice; the end
    point of the sumcheck of the terms; the drawn element; the shown values, name by name.
  `a_tie`, `b_tie`: the first factor of a panel whose A side is no never-sent vector, and the
    second factor of a panel without weights, are the same at both records, on the panel's rows and
    columns.
  `typed_A`, `typed_B`: so the sums of blocks are the summands of the typed form parts.
  `a0_at`, `b0_at`: the typed form parts at a point, written out (by definition).
Limits. StackTies is a premise on letters: that a run of the verifier and the typed chain's state at
that run meet it is not shown here. Identities: nothing on a draw, on soundness or on hiding.


-/
import Johnson.Road.K4.StackSides
import Cb.Pv.Lay.At.Inner

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open OnBytes.Model (Reading)
open OnBytes.Model.Layer (Lay)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Pan pans)
open Cb.Pv.Lay.At (InnPar0 isVirt blk nP cellOf recV recAt kS extAt)

variable {K : Type} [Field K] [Fintype K] [scl : Scl]

/-- The typed state holds what the verifier has heard. z: the lookup's point; zh: the end point of
the sumcheck of the terms; shownT: what that sumcheck has shown; om: the two claims' weights. -/
structure StackTies (P : InnPar0 K) (st : P.St) (ρ : Reading K) (y : Lay) (shownT om : Array E)
    (z zh : ℕ → K) : Prop where
  /-- the lookup's point in the state -/
  z0 : st.z = z
  /-- the lookup's point in the state of the output of the sumcheck of the terms -/
  z3 : P.zP st .QK = z
  /-- the end point of the sumcheck of the terms -/
  rt : P.rt st = zh
  /-- the drawn element is the weight of claim 1 -/
  x : st.β = ρ.val (om.getD 1 zeroE)
  /-- the shown reciprocals -/
  R2 : ∀ ν (h : ν < P.D.nNu), st.o3.vals (.inl ⟨ν, h⟩) = sentAt ρ shownT ν
  /-- the shown scores -/
  sc2 : ∀ l (h : l < P.D.ne),
    st.o3.vals (.inr (.inl ⟨l, h⟩)) = sentAt ρ shownT (y.NN * y.Lam + l)
  /-- the shown entries of the selectors -/
  sel2 : ∀ l e (h : l < P.D.ne ∧ e < P.D.nx),
    st.o3.vals (.inr (.inr (⟨l, h.1⟩, ⟨e, h.2⟩))) =
      sentAt ρ shownT (y.NN * y.Lam + y.LamM + l * y.h.NE + e)

variable {P : InnPar0 K} {st : P.St} {ρ : Reading K} {y : Lay} {shownT om : Array E}
  {z zh : ℕ → K}

/-- Every panel reads the lookup's point z. -/
theorem StackTies.zP (T : StackTies P st ρ y shownT om z zh) (p : Pan) : P.zP st p = z := by
  have h3 : st.o3.st = z := T.z3
  unfold InnPar0.zP
  split_ifs
  · exact h3
  · exact T.z0

/-- The record of the late panels, at the letters z and zh. -/
theorem StackTies.rL (T : StackTies P st ρ y shownT om z zh) (m : P.J → K) :
    P.rL st m = recV P.D (recAt P.D (P.rd m) z zh) st.o3.vals := by
  have h3 : st.o3.st = z := T.z3
  unfold InnPar0.rL
  rw [h3, T.rt]

/-- The first factor of a panel whose A side is no never-sent vector. -/
theorem a_tie (T : StackTies P st ρ y shownT om z zh) (m : P.J → K) (hh : ℕ → ℕ → K) {pn : Pan}
    (hp : pn ∈ pans P.D) (hv : isVirt pn = false) {i j : ℕ} (hi : i < pn.nr P.D)
    (hj : j < pn.nc P.D) :
    pn.A P.D (P.rP st m pn) i j = pn.A P.D (rPort ρ y shownT hh P.D (P.rd m) z zh) i j := by
  have rLe := T.rL m
  have rEe : ∀ a b c, (a = (P.rE st m).m1 ∧ b = (P.rE st m).a1 ∧ c = (P.rE st m).o1) →
      a = (rPort ρ y shownT hh P.D (P.rd m) z zh).m1 ∧
      b = (rPort ρ y shownT hh P.D (P.rd m) z zh).a1 ∧
      c = (rPort ρ y shownT hh P.D (P.rd m) z zh).o1 := by
    rintro a b c ⟨rfl, rfl, rfl⟩
    unfold InnPar0.rE
    rw [T.z0, T.rt]
    exact ⟨rfl, rfl, rfl⟩
  obtain ⟨e1, e2, e3⟩ := rEe _ _ _ ⟨rfl, rfl, rfl⟩
  cases pn with
  | G => exact congrFun (congrFun e1 i) j
  | U => exact congrFun (congrFun e1 i) j
  | V => exact congrFun (congrFun e2 i) j
  | O => exact congrFun (congrFun e3 i) j
  | LR => exact congrFun (congrFun e1 (2 * i + 1)) j
  | D => cases hv
  | Dr l' => cases hv
  | QK =>
    show Pan.QK.A P.D (P.rL st m) i j = _
    rw [rLe]
    rfl
  | N1 =>
    have h : 2 * i < P.D.nNu := by
      have h1 : i < P.D.nl := hi
      unfold Dim.nNu
      omega
    show Pan.N1.A P.D (P.rL st m) i j = _
    rw [rLe]
    show (if h : 2 * i < P.D.nNu then st.o3.vals (.inl ⟨2 * i, h⟩) else 0) =
      sentAt ρ shownT (2 * i)
    rw [dif_pos h, T.R2]
  | N2 =>
    have h : 2 * i + 1 < P.D.nNu := by
      have h1 : i < P.D.nl := hi
      unfold Dim.nNu
      omega
    show Pan.N2.A P.D (P.rL st m) i j = _
    rw [rLe]
    show (if h : 2 * i + 1 < P.D.nNu then st.o3.vals (.inl ⟨2 * i + 1, h⟩) else 0) =
      sentAt ρ shownT (2 * i + 1)
    rw [dif_pos h, T.R2]
  | XR =>
    have h : i < P.D.ne := hi
    show Pan.XR.A P.D (P.rL st m) i j = _
    rw [rLe]
    show (if h : i < P.D.ne then st.o3.vals (.inr (.inl ⟨i, h⟩)) else 0) =
      sentAt ρ shownT (y.NN * y.Lam + i)
    rw [dif_pos h, T.sc2]
  | DD =>
    have h : i < P.D.ne ∧ j < P.D.nx := ⟨hi, hj⟩
    show Pan.DD.A P.D (P.rL st m) i j = _
    rw [rLe]
    show (if h : i < P.D.ne ∧ j < P.D.nx then
      st.o3.vals (.inr (.inr (⟨i, h.1⟩, ⟨j, h.2⟩))) else 0) =
      sentAt ρ shownT (y.NN * y.Lam + y.LamM + i * y.h.NE + j)
    rw [dif_pos h, T.sel2 _ _ h]
  | MR =>
    have h : i < P.D.ne ∧ j < P.D.nx := ⟨hi, hj⟩
    show Pan.MR.A P.D (P.rL st m) i j = _
    rw [rLe]
    show (if h : i < P.D.ne ∧ j < P.D.nx then
      st.o3.vals (.inr (.inr (⟨i, h.1⟩, ⟨j, h.2⟩))) else 0) =
      sentAt ρ shownT (y.NN * y.Lam + y.LamM + i * y.h.NE + j)
    rw [dif_pos h, T.sel2 _ _ h]
  | Gr l' =>
    have hl : l' < P.D.ne := by simpa [pans] using hp
    have h : l' < P.D.ne ∧ i < P.D.nx := ⟨hl, hi⟩
    show Pan.A P.D (P.rL st m) (.Gr l') i j = _
    rw [rLe]
    show (if h : l' < P.D.ne ∧ i < P.D.nx then
      st.o3.vals (.inr (.inr (⟨l', h.1⟩, ⟨i, h.2⟩))) else 0) * _ =
      sentAt ρ shownT (y.NN * y.Lam + y.LamM + l' * y.h.NE + i) * _
    rw [dif_pos h, T.sel2 _ _ h]
    rfl
  | Ur l' =>
    have hl : l' < P.D.ne := by simpa [pans] using hp
    have h : l' < P.D.ne ∧ i < P.D.nx := ⟨hl, hi⟩
    show Pan.A P.D (P.rL st m) (.Ur l') i j = _
    rw [rLe]
    show (if h : l' < P.D.ne ∧ i < P.D.nx then
      st.o3.vals (.inr (.inr (⟨l', h.1⟩, ⟨i, h.2⟩))) else 0) * _ =
      sentAt ρ shownT (y.NN * y.Lam + y.LamM + l' * y.h.NE + i) * _
    rw [dif_pos h, T.sel2 _ _ h]
    rfl

/-- The second factor of a panel without weights. -/
theorem b_tie (T : StackTies P st ρ y shownT om z zh) (m : P.J → K) (hh : ℕ → ℕ → K) {pn : Pan}
    (hg : pn.weight = false) (i j : ℕ) :
    P.κB st pn i * P.FB st m pn i j =
      pn.B P.D (rPort ρ y shownT hh P.D (P.rd m) z zh) P.tb P.L0 (P.rw m) z zh i j := by
  have rLe := T.rL m
  unfold InnPar0.FB
  rw [T.zP, T.rt]
  cases pn with
  | N1 =>
    show 1 * Pan.N1.B P.D (P.rL st m) P.tb P.L0 (P.rw m) z zh i j = _
    rw [rLe, one_mul]
    rfl
  | N2 =>
    show 1 * Pan.N2.B P.D (P.rL st m) P.tb P.L0 (P.rw m) z zh i j = _
    rw [rLe, one_mul]
    rfl
  | XR =>
    show 1 * Pan.XR.B P.D (P.rL st m) P.tb P.L0 (P.rw m) z zh i j = _
    rw [rLe, one_mul]
    rfl
  | DD =>
    show 1 * Pan.DD.B P.D (P.rL st m) P.tb P.L0 (P.rw m) z zh i j = _
    rw [rLe, one_mul]
    rfl
  | MR =>
    show 1 * Pan.MR.B P.D (P.rL st m) P.tb P.L0 (P.rw m) z zh i j = _
    rw [rLe, one_mul]
    rfl
  | _ => cases hg

omit [Fintype K] scl in
/-- A block of vectors that agree. -/
theorem blk_congr {g n : ℕ} {V V' : ℕ → K} (h : ∀ t, V t = V' t) (Y : ℕ) :
    blk g n V Y = blk g n V' Y := by
  unfold blk
  split_ifs
  · exact h _
  · rfl

/-- **The first side.** -/
theorem typed_A (T : StackTies P st ρ y shownT om z zh) (m : P.J → K) (hh : ℕ → ℕ → K) (Y : ℕ) :
    ((pans P.D).map fun pn => blk (pn.wid P.D) (nP P.D pn)
      (vaOf P.D (rPort ρ y shownT hh P.D (P.rd m) z zh) z (ρ.val (om.getD 1 zeroE)) pn) Y).sum =
      ((pans P.D).map fun p => if isVirt p then 0 else P.onP (P.VA st m) p Y).sum := by
  refine congrArg List.sum (List.map_congr_left fun pn hp => ?_)
  by_cases hv : isVirt pn = true
  · rw [if_pos hv]
    unfold blk vaOf
    rw [if_pos hv]
    split_ifs <;> rfl
  · rw [if_neg hv]
    unfold InnPar0.onP
    refine blk_congr (fun t => ?_) Y
    unfold vaOf InnPar0.VA
    rw [if_neg hv, if_neg hv]
    unfold cellOf
    split_ifs with hc
    · unfold faOf InnPar0.FA
      rw [T.zP, T.x, a_tie T m hh hp (by simpa using hv) hc.1 hc.2]
    · rfl

/-- **The second side.** -/
theorem typed_B (T : StackTies P st ρ y shownT om z zh) (m : P.J → K) (hh : ℕ → ℕ → K) (Y : ℕ) :
    ((pans P.D).map fun pn => blk (pn.wid P.D) (nP P.D pn)
      (vbOf P.D (rPort ρ y shownT hh P.D (P.rd m) z zh) P.tb P.L0 (P.rw m) z zh pn) Y).sum =
      ((pans P.D).map fun p => if p.weight then 0 else P.onP (P.VB st m) p Y).sum := by
  refine congrArg List.sum (List.map_congr_left fun pn _ => ?_)
  by_cases hg : pn.weight = true
  · rw [if_pos hg]
    unfold blk vbOf
    rw [if_pos hg]
    split_ifs <;> rfl
  · rw [if_neg hg]
    unfold InnPar0.onP
    refine blk_congr (fun t => ?_) Y
    unfold vbOf InnPar0.VB
    rw [if_neg hg]
    unfold cellOf
    split_ifs with hc
    · exact (b_tie T m hh (by simpa using hg) _ _).symm
    · rfl

/-- The typed form part of the first side, written out. -/
theorem a0_at (P : InnPar0 K) (st : P.St) (m : P.J → K) (zz : Fin (kS P.D) → K) :
    P.inn.F st m (.inl (.inl ())) zz =
      extAt (kS P.D) (kS P.D - kS P.D)
        (fun y => ((pans P.D).map fun p => if isVirt p then 0 else P.onP (P.VA st m) p y).sum)
        (Blocks.nat zz) :=
  rfl

/-- The typed form part of the second side, written out. -/
theorem b0_at (P : InnPar0 K) (st : P.St) (m : P.J → K) (zz : Fin (kS P.D) → K) :
    P.inn.F st m (.inr (.inl ())) zz =
      extAt (kS P.D) (kS P.D - kS P.D)
        (fun y => ((pans P.D).map fun p => if p.weight then 0 else P.onP (P.VB st m) p y).sum)
        (Blocks.nat zz) :=
  rfl

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.typed_A
#print axioms OnBytes.Road.K4.typed_B
