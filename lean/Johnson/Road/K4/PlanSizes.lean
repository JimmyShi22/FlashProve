-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/PlanSizes.lean: THE LIBRARY's SIZES ARE THE PLANNER's, AT THE RECORD OF SIZES THAT
THE PROGRAM's OWN FUNCTION MAKES, WHERE K4's TEXT COVERS THE PUBLIC RECORD: the condition
`DimIs D x` (OnBytes/Tie/Pv/Lay/At/Sizes.lean: fourteen equations) holds at
x := `Verify.layerNumbers P hp g` (OnBytes/Model/VerifySubproofs.lean: the record from which the
rounds of the layer sub-proof of group g are planned, apart from those of its lookup and of its
smallness test), UNDER THE FIVE PREMISES NAMED BELOW. Without the covering it fails at shapes that
`layout` admits (four limbs: seven sums, not nine). Statements and proofs.

  `LaySizes h y`, `laySizes_of_base`, `laySizes_of_layout`: ten plain facts on the numbers of a
    layout that the function `layout` returns for the shape h. Five of them stand in the
    record `Laid` too, there for a shape with routed experts.
  `planG_sizes`: the plan that `planG` returns holds `lamSOf` and `nclOf` of the layout.
  `sum_range_const`, `sum_cntB`, `panTotal_eq`: on the library alone: the number of the panels'
    weight claims is 6 nl + 4 ne; the number of all panels' places, written out.
  `nl_tie`, `ne_tie`, `nNu_tie`: three of the library's numbers in the shape's (near twins of
    `Sized.nl_eq`, `ne_eq`, `nNu_eq`, Johnson/Road/FormsKeysFits.lean).
  `lamSOf_eq`: the program's number of rounds of the batched sumcheck is the library's `lamS`, for
    a layout with routed experts.
  `dimIs_layerNumbers`: the fourteen equations. They read fourteen of the record's nineteen fields
    (not ls, lkW, withTerms, firstGroup, routed) and eight of `Sized`'s nine numbers (not nkv).
  `dimIs_of_planG`: the same with the plan's two numbers paid by `planG`'s return.

The premises of `dimIs_layerNumbers`: the layout is what `layout` returns for a shape hS; K4's
text covers the public record (`covers`: five limbs, routed experts, terms in the second token
sumcheck, among others); the tables of reads are what `readsOf` returns; the library's sizes D
agree with hS in the nine numbers of `Sized` (`dimOf hS` does: `sized_dimOf`); the plan's lamS and
NCL are `lamSOf` and `nclOf` of the layout.

Limits. Equations between numbers: nothing on what the rounds hold. Nothing is said of a layout
without routed experts or with four limbs. That a given run's P and hp come from `layout`,
`readsOf` and `planG` is a premise here. The scripts of `laySizes_of_base` and `planG_sizes` follow
`admitted_of_base` (Johnson/Road/FormsKeysLaid.lean) and `planG_size`
(OnBytes/Tie/Pv/Lookup/Ends/FoPlanSize.lean).
-/
import Johnson.Road.FormsKeysLaid
import Johnson.Road.FormsKeysPos
import OnBytes.Tie.Pv.Lay.At.Sizes
import OnBytes.Tie.Pv.Lookup.Ends.FoLayerMu
import OnBytes.Model.Fit.LayerCaps
import OnBytes.Model.VerifySubproofs
import OnBytes.Desc.First.K4.Rounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Lay Shape Pub Reads HPlan2 layout layoutBase layoutLook readsOf planG
  lamSOf nclOf shownByTerms)
open OnBytes.Tie.Pv.Lay.At (DimIs)
open Cb.Pv.Lay.At (cntB)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim Pan pans panTotal lamS lDd lF lFe)
open OnBytes.Desc.First.K4 (covers)

/-! ## The layout's numbers -/

/-- Ten plain facts on the numbers of a layout for the shape h. -/
structure LaySizes (h : Shape) (y : Lay) : Prop where
  /-- the layout holds its shape -/
  shape : y.h = h
  /-- a group has at least two layers -/
  ll : 1 ≤ h.ll
  /-- the layers of a group, and those with routed experts -/
  Lam : y.Lam = 2 ^ h.ll
  LamM : y.LamM = 2 ^ h.ll / 2
  /-- two norms in a layer; the norms of a group -/
  NN : y.NN = 2
  NI : y.NI = 2 * 2 ^ h.ll
  /-- the width of the queries -/
  dq : y.dq = h.H * h.dh
  /-- the bits of the three widths -/
  lPd : y.lPd = ceilLog2 h.d
  lPf : y.lPf = ceilLog2 h.f
  lfe : y.lfe = if h.p3 then ceilLog2 h.fe else 0

/-- The first half of the layout. -/
theorem laySizes_of_base {h : Shape} {pc : List (List String)} {y : Lay}
    (hy : layoutBase h pc = .ok y) : LaySizes h y := by
  unfold layoutBase at hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨e2, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨taken, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  obtain ⟨-, hy⟩ := ok_of_refuse hy
  generalize Model.Layer.gateTables h.eg h.smax h.p3 h.gcl = gt at hy
  obtain ⟨silu, fs⟩ := gt
  cases hy
  -- the test on the shape's words
  have a1 := or_false_split e2
  have a2 := or_false_split a1.1
  have a3 := or_false_split a2.1
  have a5 := or_false_split a3.1
  have a6 := or_false_split a5.1
  have a7 := or_false_split a6.1
  have a8 := or_false_split a7.1
  have ll : 1 ≤ h.ll := Nat.not_lt.mp (of_decide_eq_false a8.2)
  exact ⟨rfl, ll, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Every layout that the function `layout` returns. -/
theorem laySizes_of_layout {h : Shape} {pc : List (List String)} {y : Lay}
    (hy : layout h pc = .ok y) : LaySizes h y := by
  unfold layout at hy
  obtain ⟨y0, h0, h1⟩ := ok_of_bind hy
  have A := laySizes_of_base h0
  obtain ⟨-, fo, kbm, rfl⟩ := look_keeps h1
  exact ⟨A.shape, A.ll, A.Lam, A.LamM, A.NN, A.NI, A.dq, A.lPd, A.lPf, A.lfe⟩

/-! ## The plan's two numbers -/

/-- The plan that `planG` returns holds `lamSOf` and `nclOf` of the layout. -/
theorem planG_sizes {P : Pub} {g : ℕ} {O : Option HPlan2} {hp : HPlan2}
    (h : planG P g O = .ok hp) : hp.lamS = lamSOf P.y ∧ hp.NCL = nclOf P.y g := by
  unfold planG at h
  obtain ⟨⟨mats, txOf, ft⟩, -, h⟩ := ok_of_bind h
  obtain ⟨tl, -, h⟩ := ok_of_bind h
  obtain ⟨⟨tl1, Fp, Tp⟩, -, h⟩ := ok_of_bind h
  obtain ⟨Tp1, -, h⟩ := ok_of_bind h
  obtain ⟨-, -, h⟩ := ok_of_bind h
  dsimp only at h
  split at h
  · obtain ⟨-, -, h⟩ := ok_of_bind h
    obtain ⟨y, -, h⟩ := ok_of_bind h
    obtain ⟨-, -, h⟩ := ok_of_bind h
    cases h
    exact ⟨rfl, rfl⟩
  · split at h
    · repeat obtain ⟨_, _, h⟩ := ok_of_bind h
      cases h
      exact ⟨rfl, rfl⟩
    · obtain ⟨_, hx, _⟩ := ok_of_bind h
      cases hx

/-! ## On the library alone -/

/-- The sum of a function that is constant, over the first n numbers. -/
theorem sum_range_const (c : ℕ) (f : ℕ → ℕ) (hf : ∀ i, f i = c) :
    ∀ n : ℕ, ((List.range n).map f).sum = n * c
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_range_const c f hf n,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hf, Nat.add_zero, Nat.add_mul,
      Nat.one_mul]

/-- The number of the panels' weight claims. -/
theorem sum_cntB (D : Dim) : ((pans D).map (cntB D)).sum = 6 * D.nl + 4 * D.ne := by
  have hG := sum_range_const 1 (fun i => cntB D (.Gr i)) (fun _ => rfl) D.ne
  have hU := sum_range_const 1 (fun i => cntB D (.Ur i)) (fun _ => rfl) D.ne
  have hD := sum_range_const 1 (fun i => cntB D (.Dr i)) (fun _ => rfl) D.ne
  have e1 : cntB D .G = D.nl := rfl
  have e2 : cntB D .U = D.nl := rfl
  have e3 : cntB D .O = D.nl := rfl
  have e4 : cntB D .D = D.nl := rfl
  have e5 : cntB D .V = D.nl := rfl
  have e6 : cntB D .LR = D.ne := rfl
  have e7 : cntB D .N1 = 0 := rfl
  have e8 : cntB D .N2 = 0 := rfl
  have e9 : cntB D .QK = D.nl := rfl
  have e10 : cntB D .XR = 0 := rfl
  have e11 : cntB D .DD = 0 := rfl
  have e12 : cntB D .MR = 0 := rfl
  unfold pans
  simp only [List.map_append, List.sum_append, List.map_map, Function.comp_def, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, hG, hU, hD, e1, e2, e3, e4, e5, e6, e7, e8, e9,
    e10, e11, e12]
  omega

/-- The number of all panels' places, in the order in which the program's `lamSOf` adds it up. -/
theorem panTotal_eq (D : Dim) : panTotal D =
    4 * 2 ^ (Nat.clog 2 D.nl + Nat.clog 2 D.d) + 2 ^ (Nat.clog 2 D.nl + Nat.clog 2 D.dq) +
        2 ^ (Nat.clog 2 D.nl + Nat.clog 2 D.f) + 2 * 2 ^ Nat.clog 2 D.nl +
      (2 ^ (Nat.clog 2 D.ne + Nat.clog 2 D.d) + 2 ^ Nat.clog 2 D.ne +
        2 * 2 ^ (Nat.clog 2 D.ne + Nat.clog 2 D.nx) +
        D.ne * (2 * 2 ^ (Nat.clog 2 D.nx + Nat.clog 2 D.d) +
          2 ^ (Nat.clog 2 D.nx + Nat.clog 2 D.fe))) := by
  have c1 : Nat.clog 2 1 = 0 := Nat.clog_of_right_le_one (Nat.le_refl 1) 2
  have hG := sum_range_const (2 ^ (Nat.clog 2 D.nx + Nat.clog 2 D.d))
    (fun i => 2 ^ (Pan.Gr i).wid D) (fun _ => rfl) D.ne
  have hU := sum_range_const (2 ^ (Nat.clog 2 D.nx + Nat.clog 2 D.d))
    (fun i => 2 ^ (Pan.Ur i).wid D) (fun _ => rfl) D.ne
  have hD := sum_range_const (2 ^ (Nat.clog 2 D.nx + Nat.clog 2 D.fe))
    (fun i => 2 ^ (Pan.Dr i).wid D) (fun _ => rfl) D.ne
  have e1 : Pan.G.wid D = Nat.clog 2 D.nl + Nat.clog 2 D.d := rfl
  have e2 : Pan.U.wid D = Nat.clog 2 D.nl + Nat.clog 2 D.d := rfl
  have e3 : Pan.O.wid D = Nat.clog 2 D.nl + Nat.clog 2 D.dq := rfl
  have e4 : Pan.D.wid D = Nat.clog 2 D.nl + Nat.clog 2 D.f := rfl
  have e5 : Pan.V.wid D = Nat.clog 2 D.nl + Nat.clog 2 D.d := rfl
  have e6 : Pan.LR.wid D = Nat.clog 2 D.ne + Nat.clog 2 D.d := rfl
  have e7 : Pan.N1.wid D = Nat.clog 2 D.nl + Nat.clog 2 1 := rfl
  have e8 : Pan.N2.wid D = Nat.clog 2 D.nl + Nat.clog 2 1 := rfl
  have e9 : Pan.QK.wid D = Nat.clog 2 D.nl + Nat.clog 2 D.d := rfl
  have e10 : Pan.XR.wid D = Nat.clog 2 D.ne + Nat.clog 2 1 := rfl
  have e11 : Pan.DD.wid D = Nat.clog 2 D.ne + Nat.clog 2 D.nx := rfl
  have e12 : Pan.MR.wid D = Nat.clog 2 D.ne + Nat.clog 2 D.nx := rfl
  unfold panTotal pans
  simp only [List.map_append, List.sum_append, List.map_map, Function.comp_def, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, hG, hU, hD, e1, e2, e3, e4, e5, e6, e7, e8, e9,
    e10, e11, e12, c1, Nat.add_zero]
  ring

/-! ## The ties -/

section Ties

variable {hS : Shape} {y : Lay} {D : Dim}

/-- The library's number of layers in a group. -/
theorem nl_tie (Z : Sized hS D) : D.nl = 2 ^ hS.ll := by
  unfold Dim.nl
  rw [Z.lL]

/-- Its number of layers with routed experts. -/
theorem ne_tie (Z : Sized hS D) : D.ne = 2 ^ hS.ll / 2 := by
  unfold Dim.ne
  rw [nl_tie Z]

/-- Its number of norms. -/
theorem nNu_tie (Z : Sized hS D) : D.nNu = 2 * 2 ^ hS.ll := by
  unfold Dim.nNu
  rw [nl_tie Z]

/-- **The program's number of rounds of the batched sumcheck is the library's**, for a layout with
routed experts. -/
theorem lamSOf_eq (L : LaySizes hS y) (Z : Sized hS D) (hp3 : hS.p3 = true) :
    lamSOf y = lamS D := by
  have hd : D.d = hS.d := Z.d
  have hf : D.f = hS.f := Z.f
  have hfe : D.fe = hS.fe := Z.fe
  have hnx : D.nx = hS.NE := Z.nexp
  have hdq : D.dq = hS.H * hS.dh := by
    unfold Dim.dq
    rw [Z.nq, Z.ch]
  unfold lamS
  rw [panTotal_eq, nl_tie Z, ne_tie Z, hd, hf, hfe, hnx, hdq]
  unfold lamSOf
  simp only [L.shape, hp3, if_true, L.Lam, L.LamM, L.dq, ceilLog2_eq_clog]

/-- **The library's sizes are the planner's, at the record that the program's function makes**:
where K4's text covers the public record, the layout and the reads are `layout`'s and `readsOf`'s,
the plan's lamS and NCL are `lamSOf` and `nclOf`, and D agrees with the shape (`Sized`). -/
theorem dimIs_layerNumbers [scl : Scl] {pc : List (List String)} {P : Pub} {hp : HPlan2} {g : ℕ}
    (hy : layout hS pc = .ok P.y) (hc : covers P = true) (hrd : readsOf P.y = .ok P.rd)
    (Z : Sized hS D) (hl : hp.lamS = lamSOf P.y) (hn : hp.NCL = nclOf P.y g) :
    DimIs D (Verify.layerNumbers P hp g) := by
  have L := laySizes_of_layout hy
  have r1 := Model.Fit.readsOf_lNI hrd
  unfold covers at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨c1, p3⟩, -⟩, -⟩, c5⟩ := hc
  have xl : P.y.h.xl = 5 := beq_iff_eq.mp c1
  have hp3 : hS.p3 = true := by
    rw [← L.shape]
    exact p3
  have tsc : ¬ P.rd.tscCalls.isEmpty = true := by
    intro e
    rw [e] at c5
    exact Bool.false_ne_true c5
  have two : 2 * 2 ^ hS.ll = 2 ^ (hS.ll + 1) := by
    rw [Nat.pow_succ, Nat.mul_comm]
  exact {
    lt := by
      show D.lT = P.y.h.lt
      rw [Z.lT, L.shape]
    NI := by
      show D.nNu = P.y.NI
      rw [L.NI, nNu_tie Z]
    NS := by
      show 9 = ledNS P.y.h.xl
      rw [xl]
      rfl
    lNI := by
      show D.lL + 1 = P.rd.lNI
      rw [r1, L.NI, two, ceilLog2_eq_clog, Nat.clog_pow 2 _ (by decide), Z.lL]
    lPd := by
      show Nat.clog 2 D.P.d = P.y.lPd
      rw [L.lPd, ceilLog2_eq_clog, Z.d]
    NP := by
      show 7 = ledNP P.y.h.xl
      rw [xl]
      rfl
    NO := by
      show 4 = ledNO P.y.h.xl
      rw [xl]
      rfl
    shown := by
      show D.nNu + (D.ne + D.ne * D.P.nexp) = (if P.rd.tscCalls.isEmpty = true then 0
        else P.y.NN * P.y.Lam + (if P.y.h.p3 = true then P.y.LamM * (1 + P.y.h.NE) else 0))
      rw [if_neg tsc, if_pos p3, L.NN, L.Lam, L.LamM, L.shape, nNu_tie Z, ne_tie Z, Z.nexp]
      ring
    lamS := by
      show lamS D = hp.lamS
      rw [hl]
      exact (lamSOf_eq L Z hp3).symm
    never := by
      show 1 + D.ne = 1 + (if P.y.h.p3 = true then P.y.LamM else 0)
      rw [if_pos p3, L.LamM, ne_tie Z]
    claims := by
      show ((pans D).map (cntB D)).sum = hp.NCL - (if (g == 0) = true then 1 else 0)
      rw [sum_cntB, hn]
      unfold nclOf
      rw [if_pos p3, L.Lam, L.LamM, nl_tie Z, ne_tie Z, Nat.add_sub_cancel]
    ll := by
      show D.lL = P.y.h.ll
      rw [Z.lL, L.shape]
    lPf := by
      show Nat.clog 2 D.P.f = P.y.lPf
      rw [L.lPf, ceilLog2_eq_clog, Z.f]
    lfe := by
      show Nat.clog 2 D.P.fe = P.y.lfe
      rw [L.lfe, if_pos hp3, ceilLog2_eq_clog, Z.fe] }

/-- The same with the plan's two numbers paid by `planG`'s return. -/
theorem dimIs_of_planG [scl : Scl] {pc : List (List String)} {P : Pub} {hp : HPlan2} {g : ℕ}
    {O : Option HPlan2} (hy : layout hS pc = .ok P.y) (hc : covers P = true)
    (hrd : readsOf P.y = .ok P.rd) (Z : Sized hS D) (hpl : planG P g O = .ok hp) :
    DimIs D (Verify.layerNumbers P hp g) :=
  dimIs_layerNumbers hy hc hrd Z (planG_sizes hpl).1 (planG_sizes hpl).2

end Ties

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.laySizes_of_layout
#print axioms OnBytes.Road.K4.planG_sizes
#print axioms OnBytes.Road.K4.sum_cntB
#print axioms OnBytes.Road.K4.panTotal_eq
#print axioms OnBytes.Road.K4.lamSOf_eq
#print axioms OnBytes.Road.K4.dimIs_layerNumbers
#print axioms OnBytes.Road.K4.dimIs_of_planG
