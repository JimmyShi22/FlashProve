-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysWvB.lean: the vector of a weight claim, read from the committed matrix of
weights, is the B side of the library's panel.

Johnson/Road/FormsKeysWv.lean makes, from a weight claim of the verifier and a matrix W, a vector
(wvClaim; wvOf for claim number a of a list): the sum that the claim speaks of in W, with the factor
on the columns of the claim's panel, and on its rows if the panel has the selector, replaced by an
indicator. The library writes the B side of a weight panel as a sum over the weights of a layer
(Pan.B in Inst/Model/FF/Objects.lean). This file shows that the two are equal, for the ten kinds of
weight panels, where the library's weights are those that the library's own layout reads in the same
W: w l := layerR D.P lk W (L0 + l).

What is compared with what: wvClaim and wvOf, definitions of these files on the verifier's own
claims and layout of the weights, against the library's Pan.B.

The way. The library's value of a panel's tensor claim (Pan.TnRow, Pan.TnPan) is the extension of
the B side at a point ζ, and Johnson/Road/FormsKeysTn.lean shows, for every ζ, that it is the
functional of a tensor claim on W (tnOf). At a vertex of the cube (zetaAt) the weights of the
columns and rows are indicators (Ec_zetaAt, Er_zetaAt), so the value is the B side at one entry
(TnRow_at, TnPan_at). On the verifier's side the vector at that entry is the functional of the same
tensor claim (sumSel_boxSum, wvClaim_Tn, wv_Tn; wv_two, wv_three), by the steps by which
Johnson/Road/FormsKeysAim.lean and, for the panel QK, Johnson/Road/FormsKeysQKF.lean compare the
claims themselves: the two layouts of the weights are one, and the factors that are not replaced are
the library's.

Main definitions: zetaAt; SelAre.
Main theorems.
 - wvB_V, wvB_O, wvB_G, wvB_U, wvB_D, wvB_LR, wvB_QK; wvB_Gr, wvB_Ur, wvB_Dr: panel by panel, for a
   claim in the words of Johnson/Road/FormsKeysFold.lean.
 - wvB_acc, wvB_routed: the same with the segment's name as a variable, for a member of the list
   that claimsA or claimsT returns; wvB_acc_zero: past the panel's columns the vector is 0.
 - wvOf_AtA, wvOf_AtQK, wvOf_AtR: for a panel b of which AtA, AtQK or AtR holds
   (FormsKeysFold.lean): the vector of claim number v0 + i is row i of the B side of the library's
   panel of the segment's name; with the selector, the vector of claim number v0 at the place of row
   e and column yv of b is the B side at (e, yv).
 - wvOf_AtA_zero, wvOf_AtQK_zero, wvOf_AtR_zero: past the columns of the library's panel these
   vectors are 0.

The hypotheses are the record AimFits of FormsKeysAim.lean with the tie of the call of the panel's
own family (CallTie there) and, for the panel QK, those of claims_QK in FormsKeysQKF.lean. The heads
of these two files say for each part what shows that it can be met, and that no theorem shows it of
all together. The point ζ of the records is not read here: the vector does not hang on the batched
sumcheck's point.

What is not claimed. For a panel with the selector, what the vector is at a place whose row the
library's panel does not have. That the verifier's A sides and weights are the library's.
That a hidden value is what its claim says. See also Johnson/Road/FormsKeysKit.lean. The program
does not import this file.
-/
import Johnson.Road.FormsKeysWv
import Johnson.Road.FormsKeysJoinFG
import Johnson.Road.FormsKeysQKF
import Blocks.LookupRel

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading eqTab WsShape WsGrp WsUnit WsLay WsFac WsClaim Seg CallD wsLayOf)
open OnBytes.Model.Layer (ClaimEnv SBlk Panels PanelEnv isAcc)
open Inst.Model (Params Tables TClaim entryW boxSum)
open Inst.Model.Layout (Kind Coord UnitS units first uQK)
open Inst.Model.FFSeg (Dim Fam Pan Rd LW pans lamS layerR isExpL fSh ew len call aC zc AH kp)

variable {K : Type} [Field K]

/-! ## The library's panels at a vertex of the cube -/

/-- The equality weight of a vertex of the cube at a number is 1 if the number is the vertex's, and
0 if not. -/
theorem eqN_cube (g : ℕ) {X Y : ℕ} (hX : X < 2 ^ g) (hY : Y < 2 ^ g) :
    Blocks.eqN g 0 (Blocks.cubePt g X : ℕ → K) Y = if X = Y then 1 else 0 := by
  have e := Blocks.ext_cubePt (E := K) g (fun i => if i = Y then (1 : K) else 0) hX
  unfold Blocks.ext at e
  simp only [mul_ite, mul_one, mul_zero] at e
  rw [Finset.sum_ite_eq', if_pos (mem_range.mpr hY)] at e
  exact e

section Vertex

variable (D : Dim)

/-- A point for the batched sumcheck's place, in the library's order, that is the vertex of row e
and column ι on the coordinates of the rows and columns of panel p. -/
def zetaAt (p : Pan) (e ι : ℕ) : ℕ → K := fun t =>
  if t < lamS D - p.wcol D then Blocks.cubePt (p.wid D - p.wcol D) e (t - (lamS D - p.wid D))
  else Blocks.cubePt (p.wcol D) ι (t - (lamS D - p.wcol D))

/-- At that point the library's weight of a column is the indicator of column ι. -/
theorem Ec_zetaAt (p : Pan) (e : ℕ) {ι j : ℕ} (hι : ι < 2 ^ p.wcol D) (hj : j < 2 ^ p.wcol D) :
    p.Ec D (zetaAt (K := K) D p e ι) j = if ι = j then 1 else 0 := by
  unfold Pan.Ec
  rw [← eqN_cube (K := K) (p.wcol D) hι hj, ← eqN_shift' (p.wcol D) (lamS D - p.wcol D)]
  refine eqN_congr' _ _ (fun t _ => ?_) j
  show zetaAt D p e ι (lamS D - p.wcol D + (0 + t)) = Blocks.cubePt (p.wcol D) ι (0 + t)
  unfold zetaAt
  rw [if_neg (by omega), Nat.add_sub_cancel_left]

/-- At that point the library's weight of a row is the indicator of row e. -/
theorem Er_zetaAt (p : Pan) (hle : p.wid D ≤ lamS D) (ι : ℕ) {e j : ℕ}
    (he : e < 2 ^ (p.wid D - p.wcol D)) (hj : j < 2 ^ (p.wid D - p.wcol D)) :
    p.Er D (zetaAt (K := K) D p e ι) j = if e = j then 1 else 0 := by
  unfold Pan.Er
  rw [← eqN_cube (K := K) (p.wid D - p.wcol D) he hj,
    ← eqN_shift' (p.wid D - p.wcol D) (lamS D - p.wid D)]
  refine eqN_congr' _ _ (fun t ht => ?_) j
  show zetaAt D p e ι (lamS D - p.wid D + (0 + t)) =
    Blocks.cubePt (p.wid D - p.wcol D) e (0 + t)
  unfold zetaAt
  rw [if_pos (by omega), Nat.add_sub_cancel_left]

variable (r : Rd K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K) (z zh : ℕ → K)

/-- At that point the value of the tensor claim of a row is the B side at column ι. -/
theorem TnRow_at (p : Pan) (e ρ' : ℕ) {ι : ℕ} (hι : ι < p.nc D) :
    p.TnRow D r tb L0 w z zh (zetaAt D p e ι) ρ' = p.B D r tb L0 w z zh ρ' ι := by
  have hle : p.nc D ≤ 2 ^ p.wcol D := Nat.le_pow_clog (by norm_num) _
  unfold Pan.TnRow
  rw [sum_congr rfl fun j hj => by
    rw [Ec_zetaAt D p e (lt_of_lt_of_le hι hle) (lt_of_lt_of_le (mem_range.mp hj) hle)]]
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq, if_pos (mem_range.mpr hι)]

/-- At that point the value of the tensor claim of a panel with three factors is the B side at row e
and column ι. -/
theorem TnPan_at (p : Pan) (hle : p.wid D ≤ lamS D) {e ι : ℕ} (he : e < p.nr D)
    (hι : ι < p.nc D) :
    p.TnPan D r tb L0 w z zh (zetaAt D p e ι) = p.B D r tb L0 w z zh e ι := by
  have hw : p.wid D - p.wcol D = Nat.clog 2 (p.nr D) :=
    Nat.add_sub_cancel (Nat.clog 2 (p.nr D)) (p.wcol D)
  have hr : p.nr D ≤ 2 ^ (p.wid D - p.wcol D) := by
    rw [hw]
    exact Nat.le_pow_clog (by norm_num) _
  unfold Pan.TnPan
  rw [sum_congr rfl fun j hj => by
    rw [Er_zetaAt D p hle ι (lt_of_lt_of_le he hr) (lt_of_lt_of_le (mem_range.mp hj) hr),
      TnRow_at D r tb L0 w z zh p e j hι]]
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq, if_pos (mem_range.mpr he)]

end Vertex

/-! ## The vector of a claim as the functional of a tensor claim -/

section Box

variable (ρ : Reading K)

/-- The functions fs stand for the factors under a choice sel of picked indices: for a group in
which an index is picked the function is that index's indicator on the group's indices; for another
group it is what the verifier's factor weighs the indices with. -/
def SelAre (sel : WsGrp → Option ℕ) (fg : List (WsFac × WsGrp)) (fs : List (ℕ → K)) : Prop :=
  List.Forall₂ (fun (xg : WsFac × WsGrp) (f : ℕ → K) => match sel xg.2 with
    | some v => ∀ i, i < xg.2.R → f i = if v = i then (1 : K) else 0
    | none => ∀ i, i < xg.2.R → facAt ρ xg.1 xg.2 i = f i) fg fs

/-- Then sumSel is the library's sum over the tuples of indices with these functions. -/
theorem sumSel_boxSum (sel : WsGrp → Option ℕ) :
    ∀ (fg : List (WsFac × WsGrp)) (fs : List (ℕ → K)) (F : List ℕ → K),
      SelAre ρ sel fg fs → sumSel ρ sel fg F = boxSum (fg.map fun xg => coordOf xg.2) fs F
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by cases h
  | _ :: _, [], _, h => by cases h
  | (x, g) :: fg, f :: fs, F, h => by
    cases h with
    | cons h1 h2 =>
      show _ = ∑ i ∈ range g.R, f i * boxSum (fg.map fun xg => coordOf xg.2) fs fun is =>
        F (i :: is)
      cases hs : sel g with
      | some v =>
        have h1' : ∀ i, i < g.R → f i = if v = i then 1 else 0 := by
          simpa only [hs] using h1
        rw [sumSel_some ρ hs, sum_congr rfl fun i hi => by rw [h1' i (mem_range.mp hi)]]
        simp only [ite_mul, one_mul, zero_mul]
        rw [Finset.sum_ite_eq, sumSel_boxSum sel fg fs _ h2]
        simp only [mem_range]
      | none =>
        have h1' : ∀ i, i < g.R → facAt ρ x g i = f i := by
          simpa only [hs] using h1
        rw [sumSel_none ρ hs]
        refine sum_congr rfl fun i hi => ?_
        rw [h1' i (mem_range.mp hi), sumSel_boxSum sel fg fs _ h2]

/-- One claim's vector. As claimVal_Tn of Johnson/Road/FormsKeysTnP.lean, for the vector at Y in the
place of the claim's sum. -/
theorem wvClaim_Tn {lay : WsLay} {W : Wm K} {c : WsClaim} {u : WsUnit} {P : Params} {lk n Y : ℕ}
    {U : UnitS} {fs : List (ℕ → K)} (hu : lay.U[c.ui]? = some u)
    (hco : u.g.map coordOf = U.coords) (hlen : c.f.length = u.g.length) (hnl : u.nlw = U.nU)
    (hcell : ∀ q idx, cellOf u q idx = Inst.Model.Layout.place lk (units P) n U q idx)
    (hf : SelAre ρ (selOf u.g Y) (c.f.zip u.g) fs) :
    wvClaim ρ lay W c Y = (⟨n, U, fs⟩ : TClaim K).Tn P lk W := by
  have e1 : ((c.f.zip u.g).map fun xg => coordOf xg.2) = U.coords := by
    rw [← hco]
    have e2 : ((c.f.zip u.g).map fun xg => coordOf xg.2) =
        ((c.f.zip u.g).map Prod.snd).map coordOf := by
      rw [List.map_map]
      rfl
    rw [e2, List.map_snd_zip (by omega)]
  have e3 : wgtOf u W = fun i => entryW P lk W n U i := by
    funext idx
    unfold wgtOf entryW
    rw [hnl]
    refine sum_congr rfl fun q _ => ?_
    rw [hcell]
  unfold wvClaim
  rw [hu]
  show sumSel ρ (selOf u.g Y) (c.f.zip u.g) (wgtOf u W) =
    boxSum U.coords fs fun i => entryW P lk W n U i
  rw [sumSel_boxSum ρ _ _ _ _ hf, e1, e3]

/-- The generic step, as claim_Tn of Johnson/Road/FormsKeysClaim.lean, for the vector at Y. -/
theorem wv_Tn {c : ClaimEnv} {s : WsShape} {D : Dim} {lk L0 : ℕ} {ζ : ℕ → K}
    (F : ClaimFits ρ c s D lk L0 ζ) (W : Wm K) {X lam i Y : ℕ} {fac : WsGrp → Option WsFac}
    {cl : WsClaim} (hcl : c.claim X lam fac = some cl) (hlam : lam < c.v.y.Lam)
    (hX : (kindsOf (L0 + lam))[i]? = some X) {U : UnitS}
    (hU : (units D.P)[first D.P (L0 + lam) + i]? = some U) {fs : List (ℕ → K)}
    (hf : ∀ u, UnitOK lk u → u.g.map coordOf = U.coords →
      u.g.map (fun y => (y.name, y.cls)) = groupsOf X →
      ∀ Fs, u.g.mapM fac = some Fs → SelAre ρ (selOf u.g Y) (Fs.zip u.g) fs) :
    wvClaim ρ c.wsLay W cl Y = (⟨first D.P (L0 + lam) + i, U, fs⟩ : TClaim K).Tn D.P lk W := by
  obtain ⟨u, h1, h2, h3⟩ := claim_inv hcl
  have hl : c.v.lay lam = L0 + lam := by
    rw [F.base]
    rfl
  have hL := F.layers lam hlam
  rw [hl, (unitOf_eq F.sized F.lay).1 (L0 + lam) hL i X hX] at h1
  have hui : cl.ui = first D.P (L0 + lam) + i := (Option.some.inj h1).symm
  obtain ⟨-, -, -, hall⟩ := layout_eq F.sized F.lay
  obtain ⟨u', hu', ok, hnl, -, -, hco, -, -, hcell⟩ := hall _ U hU
  rw [hui] at h2
  have e : u' = u := Option.some.inj (hu'.symm.trans h2)
  subst e
  have hg := unit_groups F.sized F.lay (L0 + lam) hL i X hX u' hu'
  have hlen : cl.f.length = u'.g.length := (list_mapM_some _ _ _ h3).1
  have hu'' : c.wsLay.U[cl.ui]? = some u' := by
    rw [hui]
    exact hu'
  exact wvClaim_Tn ρ hu'' hco hlen hnl hcell (hf u' ok hco hg cl.f h3)

end Box

/-! ## The two shapes of a unit -/

section Shapes

omit [Field K] in
/-- What a place i 2^wk + yv picks in a unit with the groups kk, e and x. -/
theorem sel_three {g1 g2 g3 : WsGrp} (n1 : g1.name = "kk") (n2 : g2.name = "e")
    (n3 : g3.name = "x") {wk : ℕ} (hwk : ceilLog2 g1.R = wk) (i : ℕ) {yv : ℕ}
    (hy : yv < 2 ^ wk) :
    selOf [g1, g2, g3] (i * 2 ^ wk + yv) g1 = some yv ∧
      selOf [g1, g2, g3] (i * 2 ^ wk + yv) g2 = some i ∧
      selOf [g1, g2, g3] (i * 2 ^ wk + yv) g3 = none := by
  have hpos : 0 < 2 ^ wk := by positivity
  have em : (i * 2 ^ wk + yv) % 2 ^ wk = yv := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hy]
  have ed : (i * 2 ^ wk + yv) / 2 ^ wk = i := by
    rw [Nat.mul_comm, Nat.mul_add_div hpos, Nat.div_eq_of_lt hy, Nat.add_zero]
  refine ⟨?_, ?_, selOf_other _ _ (by rw [n3]; rfl) (by rw [n3]; rfl)⟩
  · rw [selOf_kk _ _ n1, hasE_three n1 n2 n3, wkOf_three n1, hwk, if_pos rfl, em]
  · rw [selOf_e _ _ n2, wkOf_three n1, hwk, ed]

variable {ρ : Reading K} {c : ClaimEnv} {h : Model.Layer.Shape} {pc : List (List String)}
  {s : WsShape} {D : Dim} {lk L0 : ℕ} {z ζ : ℕ → K} (A : AimFits ρ c h pc s D lk L0 ζ)

include A

/-- The vector at column Y of a claim on a unit with the groups kk and x, as the verifier makes it
for a segment of the lookup's join: it is the functional of the library's tensor claim in which the
factor on the columns is taken at the vertex of column Y. As aim_two of
Johnson/Road/FormsKeysAim.lean. -/
theorem wv_two (W : Wm K) {X lam i wy : ℕ} {s0 : Fam} {p : Pan} {cl : WsClaim}
    (hcl : c.claim X lam (fun G => if G.name == "kk" then c.facRs G 0 wy
      else c.facEw G (segName s0) 0) = some cl)
    (hlam : lam < c.v.y.Lam) (hX : (kindsOf (L0 + lam))[i]? = some X)
    (hg : groupsOf X = [("kk", 'E'), ("x", 'E')]) {R1 R2 : ℕ} {k1 k2 : Kind}
    (hU : (units D.P)[first D.P (L0 + lam) + i]? = some ⟨[⟨R1, k1⟩, ⟨R2, k2⟩], 2⟩)
    (hwy : wy = p.wcol D) (T : CallTie ρ c h D z s0) {b : ℕ} (hlen : len D s0 = b * R2)
    (hb : 0 < b) (e : ℕ) {Y : ℕ} (hY : Y < 2 ^ p.wcol D) :
    wvClaim ρ c.wsLay W cl Y = (⟨first D.P (L0 + lam) + i, ⟨[⟨R1, k1⟩, ⟨R2, k2⟩], 2⟩,
      [p.Ec D (zetaAt D p e Y), ew D z s0]⟩ : TClaim K).Tn D.P lk W := by
  refine wv_Tn ρ A.claim W hcl hlam hX hU fun u ok hco hgr Fs hFs => ?_
  rw [hg] at hgr
  obtain ⟨g1, g2, hu, e1, e2⟩ := map_two hgr
  have m1 : g1 ∈ u.g := by rw [hu]; simp
  have m2 : g2 ∈ u.g := by rw [hu]; simp
  rw [hu] at hco hFs ⊢
  have n1 : g1.name = "kk" := congrArg Prod.fst e1
  have c1 : g1.cls = 'E' := congrArg Prod.snd e1
  have n2 : g2.name = "x" := congrArg Prod.fst e2
  have c2 : g2.cls = 'E' := congrArg Prod.snd e2
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hco
  have r2 : g2.R = R2 := congrArg Coord.R hco.2
  obtain ⟨X1, r1, f1, ha, rfl⟩ := mapM_cons_some hFs
  obtain ⟨X2, r3, f2, hb2, rfl⟩ := mapM_cons_some ha
  have hr : r3 = [] := by simpa using hb2.symm
  subst hr
  have f1' : (if g1.name == "kk" then c.facRs g1 0 wy
      else c.facEw g1 (segName s0) 0) = some X1 := f1
  rw [if_pos (beq_iff_eq.mpr n1)] at f1'
  have f2' : (if g2.name == "kk" then c.facRs g2 0 wy
      else c.facEw g2 (segName s0) 0) = some X2 := f2
  rw [n2] at f2'
  have f2'' : c.facEw g2 (segName s0) 0 = some X2 := f2'
  have hle : g1.R ≤ 2 ^ p.wcol D := by
    rw [size_of_ok ok m1 c1, ← hwy]
    exact facRs_le f1'
  have s1 : selOf [g1, g2] Y g1 = some Y := by
    rw [selOf_kk _ _ n1, hasE_two n1 n2]
    rfl
  have s2 : selOf [g1, g2] Y g2 = none :=
    selOf_other _ _ (by rw [n2]; rfl) (by rw [n2]; rfl)
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil)
  · simp only [s1]
    intro j hj
    exact Ec_zetaAt D p e hY (lt_of_lt_of_le hj hle)
  · simp only [s2]
    intro v hv
    rw [ew_at A T c2 (size_of_ok ok m2 c2) (a := 0) (b := b) (Nat.zero_mul _).symm
      (by rw [r2]; exact hlen) hb f2'' v hv, Nat.zero_add]

/-- The vector at the place e 2^wk + yv of a claim on a unit with the groups kk, e and x, as the
verifier makes it for a routed product: it is the functional of the library's tensor claim in which
the factors on the columns and on the rows are taken at the vertex of row e and column yv. As
aim_three of Johnson/Road/FormsKeysAim.lean. -/
theorem wv_three (W : Wm K) {X lam i wk wr x0 : ℕ} {s0 : Fam} {p : Pan} {cl : WsClaim}
    (hcl : c.claim X lam (fun G => if G.name == "kk" then c.facRs G 0 wk
      else if G.name == "e" then c.facRs G wk wr else c.facEw G (segName s0) x0) = some cl)
    (hlam : lam < c.v.y.Lam) (hX : (kindsOf (L0 + lam))[i]? = some X)
    (hg : groupsOf X = [("kk", 'E'), ("e", 'E'), ("x", 'E')]) {R1 R2 R3 : ℕ} {k1 k2 k3 : Kind}
    (hU : (units D.P)[first D.P (L0 + lam) + i]? = some ⟨[⟨R1, k1⟩, ⟨R2, k2⟩, ⟨R3, k3⟩], 2⟩)
    (hp : p ∈ pans D) (hwk : wk = p.wcol D) (hwr : wr = Nat.clog 2 (p.nr D))
    (hR1 : ceilLog2 R1 = wk) (T : CallTie ρ c h D z s0) {a b : ℕ} (hx0 : x0 = a * R3)
    (hlen : len D s0 = b * R3) (hab : a < b) {f3 : ℕ → K}
    (h3 : ∀ x, ew D z s0 (x0 + x) = f3 x) {e yv : ℕ} (he : e < 2 ^ wr) (hy : yv < 2 ^ wk) :
    wvClaim ρ c.wsLay W cl (e * 2 ^ wk + yv) =
      (⟨first D.P (L0 + lam) + i, ⟨[⟨R1, k1⟩, ⟨R2, k2⟩, ⟨R3, k3⟩], 2⟩,
        [p.Ec D (zetaAt D p e yv), p.Er D (zetaAt D p e yv), f3]⟩ : TClaim K).Tn D.P lk W := by
  refine wv_Tn ρ A.claim W hcl hlam hX hU fun u ok hco hgr Fs hFs => ?_
  rw [hg] at hgr
  obtain ⟨g1, g2, g3, hu, e1, e2, e3⟩ := map_three hgr
  have m1 : g1 ∈ u.g := by rw [hu]; simp
  have m2 : g2 ∈ u.g := by rw [hu]; simp
  have m3 : g3 ∈ u.g := by rw [hu]; simp
  rw [hu] at hco hFs ⊢
  have n1 : g1.name = "kk" := congrArg Prod.fst e1
  have c1 : g1.cls = 'E' := congrArg Prod.snd e1
  have n2 : g2.name = "e" := congrArg Prod.fst e2
  have c2 : g2.cls = 'E' := congrArg Prod.snd e2
  have n3 : g3.name = "x" := congrArg Prod.fst e3
  have c3 : g3.cls = 'E' := congrArg Prod.snd e3
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hco
  have r1 : g1.R = R1 := congrArg Coord.R hco.1
  have r3 : g3.R = R3 := congrArg Coord.R hco.2.2
  obtain ⟨X1, q1, f1, ha, rfl⟩ := mapM_cons_some hFs
  obtain ⟨X2, q2, f2, hb2, rfl⟩ := mapM_cons_some ha
  obtain ⟨X3, q3, f3', hb3, rfl⟩ := mapM_cons_some hb2
  have hr : q3 = [] := by simpa using hb3.symm
  subst hr
  have f1' : (if g1.name == "kk" then c.facRs g1 0 wk
      else if g1.name == "e" then c.facRs g1 wk wr
      else c.facEw g1 (segName s0) x0) = some X1 := f1
  rw [if_pos (beq_iff_eq.mpr n1)] at f1'
  have f2' : (if g2.name == "kk" then c.facRs g2 0 wk
      else if g2.name == "e" then c.facRs g2 wk wr
      else c.facEw g2 (segName s0) x0) = some X2 := f2
  rw [n2] at f2'
  have f2'' : c.facRs g2 wk wr = some X2 := f2'
  have f3'' : (if g3.name == "kk" then c.facRs g3 0 wk
      else if g3.name == "e" then c.facRs g3 wk wr
      else c.facEw g3 (segName s0) x0) = some X3 := f3'
  rw [n3] at f3''
  have f3k : c.facEw g3 (segName s0) x0 = some X3 := f3''
  have hw : p.wid D - p.wcol D = wr := by
    rw [hwr]
    exact Nat.add_sub_cancel (Nat.clog 2 (p.nr D)) (p.wcol D)
  have hle1 : g1.R ≤ 2 ^ p.wcol D := by
    rw [size_of_ok ok m1 c1, ← hwk]
    exact facRs_le f1'
  have hle2 : g2.R ≤ 2 ^ (p.wid D - p.wcol D) := by
    rw [size_of_ok ok m2 c2, hw]
    exact facRs_le f2''
  obtain ⟨s1, s2, s3⟩ := sel_three n1 n2 n3 (by rw [r1]; exact hR1) e hy
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil))
  · simp only [s1]
    intro j hj
    exact Ec_zetaAt D p e (hwk ▸ hy) (lt_of_lt_of_le hj hle1)
  · simp only [s2]
    intro j hj
    exact Er_zetaAt D p (wid_le_lamS D hp) yv (hw.symm ▸ he) (lt_of_lt_of_le hj hle2)
  · simp only [s3]
    intro v hv
    rw [ew_at A T c3 (size_of_ok ok m3 c3) (a := a) (b := b) (by rw [r3]; exact hx0)
      (by rw [r3]; exact hlen) hab f3k v hv, h3]

end Shapes

/-! ## The nine panels -/

omit [Field K] in
/-- A column of a panel has a number of wcol bits. -/
theorem nc_lt {D : Dim} {p : Pan} {Y : ℕ} (hY : Y < p.nc D) : Y < 2 ^ p.wcol D :=
  lt_of_lt_of_le hY (Nat.le_pow_clog (by norm_num) _)

section Nine

variable {ρ : Reading K} {c : ClaimEnv} {h : Model.Layer.Shape} {pc : List (List String)}
  {s : WsShape} {D : Dim} {lk L0 : ℕ} {z ζ : ℕ → K} (A : AimFits ρ c h pc s D lk L0 ζ)
  (W : Wm K) (r : Rd K) (tb : Tables) (zh : ℕ → K)

include A

/-- Panel V: the vector of the claim of row lam is the row of the B side. -/
theorem wvB_V (T : CallTie ρ c h D z .V) {lam : ℕ} (hlam : lam < c.v.y.Lam)
    {cl : WsClaim}
    (hcl : c.claim 1 lam (fun G => if G.name == "kk" then c.facRs G 0 (ceilLog2 c.v.y.h.d)
      else c.facEw G "V" 0) = some cl) {Y : ℕ} (hY : Y < Pan.V.nc D) :
    wvClaim ρ c.wsLay W cl Y =
      Pan.V.B D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh lam Y := by
  rw [← TnRow_at D r tb L0 _ z zh .V 0 lam hY, TnRow_V D r tb lk W z zh _ L0 lam]
  have hU := tnOf_unit D tb A.claim.even z zh (zetaAt D .V 0 Y) .V rfl lam
    (A.claim.layers lam hlam)
  have hX : (kindsOf (L0 + lam))[1]? = some 1 := by
    rcases layer_cases A lam with ⟨-, -, e, -⟩ | ⟨-, -, e, -⟩ <;> simp [e]
  exact wv_two A W (s0 := .V) (p := .V) hcl hlam hX rfl hU (wy_d A) T (b := 1)
    (Nat.one_mul _).symm Nat.one_pos 0 (nc_lt hY)

/-- Panel O. -/
theorem wvB_O (T : CallTie ρ c h D z .O) {lam : ℕ} (hlam : lam < c.v.y.Lam)
    {cl : WsClaim}
    (hcl : c.claim 2 lam (fun G => if G.name == "kk" then c.facRs G 0 (ceilLog2 c.v.y.dq)
      else c.facEw G "O" 0) = some cl) {Y : ℕ} (hY : Y < Pan.O.nc D) :
    wvClaim ρ c.wsLay W cl Y =
      Pan.O.B D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh lam Y := by
  rw [← TnRow_at D r tb L0 _ z zh .O 0 lam hY, TnRow_O D r tb lk W z zh _ L0 lam]
  have hU := tnOf_unit D tb A.claim.even z zh (zetaAt D .O 0 Y) .O rfl lam
    (A.claim.layers lam hlam)
  have hX : (kindsOf (L0 + lam))[2]? = some 2 := by
    rcases layer_cases A lam with ⟨-, -, e, -⟩ | ⟨-, -, e, -⟩ <;> simp [e]
  have hwy : ceilLog2 c.v.y.dq = Pan.O.wcol D := by
    rw [ceilLog2_eq_clog, A.claim.dq]
    rfl
  exact wv_two A W (s0 := .O) (p := .O) hcl hlam hX rfl hU hwy T (b := 1)
    (Nat.one_mul _).symm Nat.one_pos 0 (nc_lt hY)

/-- Panel G. -/
theorem wvB_G (T : CallTie ρ c h D z .G) {lam : ℕ} (hlam : lam < c.v.y.Lam)
    {cl : WsClaim}
    (hcl : c.claim (if c.v.isMoe lam then 5 else 3) lam (fun G =>
      if G.name == "kk" then c.facRs G 0 (ceilLog2 c.v.y.h.d) else c.facEw G "G" 0) = some cl)
    {Y : ℕ} (hY : Y < Pan.G.nc D) :
    wvClaim ρ c.wsLay W cl Y =
      Pan.G.B D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh lam Y := by
  rw [← TnRow_at D r tb L0 _ z zh .G 0 lam hY, TnRow_G D r tb A.claim.even lk W z zh _ lam]
  have hU := tnOf_unit D tb A.claim.even z zh (zetaAt D .G 0 Y) .G rfl lam
    (A.claim.layers lam hlam)
  rcases layer_cases A lam with ⟨em, -, ek, ef⟩ | ⟨em, -, ek, ef⟩
  · rw [em] at hcl
    exact wv_two A W (X := 5) (s0 := .G) (p := .G) (i := 3) hcl hlam (by simp [ek]) rfl hU
      (wy_d A) T (b := 2)
      (by show D.f = 2 * fSh D lam; rw [ef]; exact A.f2) (by decide) 0 (nc_lt hY)
  · rw [em] at hcl
    exact wv_two A W (X := 3) (s0 := .G) (p := .G) (i := 3) hcl hlam (by simp [ek]) rfl hU
      (wy_d A) T (b := 1)
      (by show D.f = 1 * fSh D lam; rw [ef, Nat.one_mul]) Nat.one_pos 0 (nc_lt hY)

/-- Panel U. -/
theorem wvB_U (T : CallTie ρ c h D z .U) {lam : ℕ} (hlam : lam < c.v.y.Lam)
    {cl : WsClaim}
    (hcl : c.claim (if c.v.isMoe lam then 6 else 4) lam (fun G =>
      if G.name == "kk" then c.facRs G 0 (ceilLog2 c.v.y.h.d) else c.facEw G "U" 0) = some cl)
    {Y : ℕ} (hY : Y < Pan.U.nc D) :
    wvClaim ρ c.wsLay W cl Y =
      Pan.U.B D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh lam Y := by
  rw [← TnRow_at D r tb L0 _ z zh .U 0 lam hY, TnRow_U D r tb A.claim.even lk W z zh _ lam]
  have hU := tnOf_unit D tb A.claim.even z zh (zetaAt D .U 0 Y) .U rfl lam
    (A.claim.layers lam hlam)
  rcases layer_cases A lam with ⟨em, -, ek, ef⟩ | ⟨em, -, ek, ef⟩
  · rw [em] at hcl
    exact wv_two A W (X := 6) (s0 := .U) (p := .U) (i := 4) hcl hlam (by simp [ek]) rfl hU
      (wy_d A) T (b := 2)
      (by show D.f = 2 * fSh D lam; rw [ef]; exact A.f2) (by decide) 0 (nc_lt hY)
  · rw [em] at hcl
    exact wv_two A W (X := 4) (s0 := .U) (p := .U) (i := 4) hcl hlam (by simp [ek]) rfl hU
      (wy_d A) T (b := 1)
      (by show D.f = 1 * fSh D lam; rw [ef, Nat.one_mul]) Nat.one_pos 0 (nc_lt hY)

/-- Panel D. On a layer with routed experts both sides are 0 from column fe on. -/
theorem wvB_D (T : CallTie ρ c h D z .D) {lam : ℕ} (hlam : lam < c.v.y.Lam)
    {cl : WsClaim}
    (hcl : c.claim 9 lam (fun G => if G.name == "kk" then c.facRs G 0 (ceilLog2 c.v.y.h.f)
      else c.facEw G "D" 0) = some cl) {Y : ℕ} (hY : Y < Pan.D.nc D) :
    wvClaim ρ c.wsLay W cl Y =
      Pan.D.B D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh lam Y := by
  have hfe : D.fe ≤ D.f := by
    have := A.f2
    omega
  rw [← TnRow_at D r tb L0 _ z zh .D 0 lam hY, TnRow_D D r tb A.claim.even lk W z zh _ hfe lam]
  have hU := tnOf_unit D tb A.claim.even z zh (zetaAt D .D 0 Y) .D rfl lam
    (A.claim.layers lam hlam)
  have hwy : ceilLog2 c.v.y.h.f = Pan.D.wcol D := by
    rw [ceilLog2_eq_clog, A.claim.f]
    rfl
  have e : ∀ n, tnOf D tb L0 z zh (zetaAt D .D 0 Y) .D lam =
        ⟨first D.P (L0 + lam) + n, Inst.Model.Layout.uD D.P (fSh D lam),
          [Pan.D.Ec D (zetaAt D .D 0 Y), ew D z .D]⟩ → (kindsOf (L0 + lam))[n]? = some 9 →
      wvClaim ρ c.wsLay W cl Y = (tnOf D tb L0 z zh (zetaAt D .D 0 Y) .D lam).Tn D.P lk W := by
    intro n en hX
    rw [en] at hU ⊢
    exact wv_two A W (s0 := .D) (p := .D) hcl hlam hX rfl hU hwy T (b := 1)
      (Nat.one_mul _).symm Nat.one_pos 0 (nc_lt hY)
  have t : tnOf D tb L0 z zh (zetaAt D .D 0 Y) .D lam =
      ⟨first D.P (L0 + lam) + (if isExpL lam then 7 else 5), Inst.Model.Layout.uD D.P (fSh D lam),
        [Pan.D.Ec D (zetaAt D .D 0 Y), ew D z .D]⟩ := rfl
  rcases layer_cases A lam with ⟨-, ee, ek, -⟩ | ⟨-, ee, ek, -⟩
  · rw [if_pos ee] at t
    exact e 7 t (by simp [ek])
  · rw [if_neg ee] at t
    exact e 5 t (by simp [ek])

/-- Panel LR: row i is the router of layer 2 i + 1 of the group. -/
theorem wvB_LR (T : CallTie ρ c h D z .LR) {i : ℕ} (hi : i < c.v.y.LamM) {cl : WsClaim}
    (hcl : c.claim 11 (2 * i + 1) (fun G =>
      if G.name == "kk" then c.facRs G 0 (ceilLog2 c.v.y.h.d) else c.facEw G "LR" 0) = some cl)
    {Y : ℕ} (hY : Y < Pan.LR.nc D) :
    wvClaim ρ c.wsLay W cl Y =
      Pan.LR.B D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh i Y := by
  obtain ⟨hlam, -⟩ := odd_layer A hi
  rw [← TnRow_at D r tb L0 _ z zh .LR 0 i hY, TnRow_LR D r tb A.claim.even lk W z zh _ i]
  have hU := tnOf_unit D tb A.claim.even z zh (zetaAt D .LR 0 Y) .LR rfl i
    (A.claim.layers _ hlam)
  have hX : (kindsOf (L0 + (2 * i + 1)))[9]? = some 11 := by simp [odd_kinds A]
  exact wv_two A W (s0 := .LR) (p := .LR) hcl hlam hX rfl hU (wy_d A) T (b := 1)
    (Nat.one_mul _).symm Nat.one_pos 0 (nc_lt hY)

/-- A row of a panel with the selector has a number of as many bits as the verifier gives it. -/
theorem nx_lt {e : ℕ} (he : e < D.nx) : e < 2 ^ ceilLog2 (max c.v.y.h.NE 1) := by
  rw [wr_NE A]
  exact lt_of_lt_of_le he (Nat.le_pow_clog (by norm_num) _)

/-- Panel Gr lm: the vector of the one claim at the place of row e and column yv is the B side. -/
theorem wvB_Gr (T : CallTie ρ c h D z .G) {lm : ℕ} (hlm : lm < c.v.y.LamM) {cl : WsClaim}
    (hcl : c.claim 7 (2 * lm + 1) (fun G =>
      if G.name == "kk" then c.facRs G 0 (ceilLog2 c.v.y.h.d)
      else if G.name == "e" then c.facRs G (ceilLog2 c.v.y.h.d) (ceilLog2 (max c.v.y.h.NE 1))
      else c.facEw G "G" c.v.y.h.fe) = some cl) {e yv : ℕ} (he : e < (Pan.Gr lm).nr D)
    (hy : yv < (Pan.Gr lm).nc D) :
    wvClaim ρ c.wsLay W cl (e * 2 ^ ceilLog2 c.v.y.h.d + yv) =
      (Pan.Gr lm).B D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh e yv := by
  obtain ⟨hlam, hne⟩ := odd_layer A hlm
  have hp : Pan.Gr lm ∈ pans D := by simp [pans, hne]
  rw [← TnPan_at D r tb L0 _ z zh (.Gr lm) (wid_le_lamS D hp) he hy,
    TnPan_Gr D r tb A.claim.even lk W z zh _ lm]
  have hU := tnOf_unit D tb A.claim.even z zh (zetaAt D (.Gr lm) e yv) (.Gr lm) rfl 0
    (A.claim.layers _ hlam)
  exact wv_three A W (s0 := .G) (p := .Gr lm) (i := 5) hcl hlam (by simp [odd_kinds A]) rfl hU
    hp (wy_d A) (wr_NE A) (by rw [A.claim.d]; rfl) T (a := 1) (b := 2)
    (by rw [Nat.one_mul]; exact A.claim.fe) A.f2 (by decide)
    (fun x => by rw [A.claim.fe]) (nx_lt A he) (by rw [wy_d A]; exact nc_lt hy)

/-- Panel Ur lm. -/
theorem wvB_Ur (T : CallTie ρ c h D z .U) {lm : ℕ} (hlm : lm < c.v.y.LamM) {cl : WsClaim}
    (hcl : c.claim 8 (2 * lm + 1) (fun G =>
      if G.name == "kk" then c.facRs G 0 (ceilLog2 c.v.y.h.d)
      else if G.name == "e" then c.facRs G (ceilLog2 c.v.y.h.d) (ceilLog2 (max c.v.y.h.NE 1))
      else c.facEw G "U" c.v.y.h.fe) = some cl) {e yv : ℕ} (he : e < (Pan.Ur lm).nr D)
    (hy : yv < (Pan.Ur lm).nc D) :
    wvClaim ρ c.wsLay W cl (e * 2 ^ ceilLog2 c.v.y.h.d + yv) =
      (Pan.Ur lm).B D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh e yv := by
  obtain ⟨hlam, hne⟩ := odd_layer A hlm
  have hp : Pan.Ur lm ∈ pans D := by simp [pans, hne]
  rw [← TnPan_at D r tb L0 _ z zh (.Ur lm) (wid_le_lamS D hp) he hy,
    TnPan_Ur D r tb A.claim.even lk W z zh _ lm]
  have hU := tnOf_unit D tb A.claim.even z zh (zetaAt D (.Ur lm) e yv) (.Ur lm) rfl 0
    (A.claim.layers _ hlam)
  exact wv_three A W (s0 := .U) (p := .Ur lm) (i := 6) hcl hlam (by simp [odd_kinds A]) rfl hU
    hp (wy_d A) (wr_NE A) (by rw [A.claim.d]; rfl) T (a := 1) (b := 2)
    (by rw [Nat.one_mul]; exact A.claim.fe) A.f2 (by decide)
    (fun x => by rw [A.claim.fe]) (nx_lt A he) (by rw [wy_d A]; exact nc_lt hy)

/-- Panel Dr lm. -/
theorem wvB_Dr (T : CallTie ρ c h D z .D) {lm : ℕ} (hlm : lm < c.v.y.LamM) {cl : WsClaim}
    (hcl : c.claim 10 (2 * lm + 1) (fun G =>
      if G.name == "kk" then c.facRs G 0 (ceilLog2 c.v.y.h.fe)
      else if G.name == "e" then c.facRs G (ceilLog2 c.v.y.h.fe) (ceilLog2 (max c.v.y.h.NE 1))
      else c.facEw G "D" 0) = some cl) {e yv : ℕ} (he : e < (Pan.Dr lm).nr D)
    (hy : yv < (Pan.Dr lm).nc D) :
    wvClaim ρ c.wsLay W cl (e * 2 ^ ceilLog2 c.v.y.h.fe + yv) =
      (Pan.Dr lm).B D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh e yv := by
  obtain ⟨hlam, hne⟩ := odd_layer A hlm
  have hp : Pan.Dr lm ∈ pans D := by simp [pans, hne]
  rw [← TnPan_at D r tb L0 _ z zh (.Dr lm) (wid_le_lamS D hp) he hy,
    TnPan_Dr D r tb A.claim.even lk W z zh _ lm]
  have hU := tnOf_unit D tb A.claim.even z zh (zetaAt D (.Dr lm) e yv) (.Dr lm) rfl 0
    (A.claim.layers _ hlam)
  have hwk : ceilLog2 c.v.y.h.fe = (Pan.Dr lm).wcol D := by
    rw [ceilLog2_eq_clog, A.claim.fe]
    rfl
  exact wv_three A W (s0 := .D) (p := .Dr lm) (i := 8) hcl hlam (by simp [odd_kinds A]) rfl hU
    hp hwk (wr_NE A) (by rw [A.claim.fe]; rfl) T (a := 0) (b := 1)
    (Nat.zero_mul _).symm (Nat.one_mul _).symm Nat.one_pos (fun x => by rw [Nat.zero_add])
    (nx_lt A he) (by rw [hwk]; exact nc_lt hy)

end Nine

/-! ## By the segment's name, and on the verifier's own lists -/

section Names

variable {ρ : Reading K} {c : ClaimEnv} {h : Model.Layer.Shape} {pc : List (List String)}
  {s : WsShape} {D : Dim} {lk L0 : ℕ} {z ζ : ℕ → K} (A : AimFits ρ c h pc s D lk L0 ζ)
  (W : Wm K) (r : Rd K) (tb : Tables) (zh : ℕ → K)

include A

/-- The vector of member number i of the list of claims that claimsA returns for one of its six
segments is row i of the B side of the segment's panel, on the panel's columns. -/
theorem wvB_acc {sn : String} (hs : isAcc sn = true) (T : CallTie ρ c h D z (panOf sn).fam)
    {l : List WsClaim} (hl : c.claimsA sn = some l) {i : ℕ} {x : WsClaim} (hi : l[i]? = some x)
    {Y : ℕ} (hY : Y < (panOf sn).nc D) :
    wvClaim ρ c.wsLay W x Y =
      (panOf sn).B D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh i Y := by
  have hlt : i < l.length := (List.getElem?_eq_some_iff.mp hi).1
  have hn := claimsA_length c sn hl hs
  rcases (isAcc_iff sn).mp hs with rfl | rfl | rfl | rfl | rfl | rfl
  · exact wvB_G A W r tb zh T (lt_of_lt_of_eq hlt hn) ((claimsA_at_G c hl i hlt).symm.trans hi) hY
  · exact wvB_U A W r tb zh T (lt_of_lt_of_eq hlt hn) ((claimsA_at_U c hl i hlt).symm.trans hi) hY
  · exact wvB_V A W r tb zh T (lt_of_lt_of_eq hlt hn) ((claimsA_at_V c hl i hlt).symm.trans hi) hY
  · exact wvB_O A W r tb zh T (lt_of_lt_of_eq hlt hn) ((claimsA_at_O c hl i hlt).symm.trans hi) hY
  · exact wvB_D A W r tb zh T (lt_of_lt_of_eq hlt hn) ((claimsA_at_D c hl i hlt).symm.trans hi) hY
  · exact wvB_LR A W r tb zh T (lt_of_lt_of_eq hlt hn) ((claimsA_at_LR c hl i hlt).symm.trans hi) hY

/-- Past the columns of the segment's panel the vector of such a claim is 0. -/
theorem wvB_acc_zero {sn : String} (hs : isAcc sn = true) {l : List WsClaim}
    (hl : c.claimsA sn = some l) {i : ℕ} {x : WsClaim} (hi : l[i]? = some x) {Y : ℕ}
    (hY : (panOf sn).nc D ≤ Y) : wvClaim ρ c.wsLay W x Y = 0 := by
  have hlt : i < l.length := (List.getElem?_eq_some_iff.mp hi).1
  have hcl := (claimsA_at c sn hl hs i hlt).symm.trans hi
  obtain ⟨k1, k2⟩ := kindA_groups sn (c.v.isMoe (if sn == "LR" then 2 * i + 1 else i))
    (c.v.isMoe (if sn == "LR" then 2 * i + 1 else i)) hs
  refine claim_zero_two ρ A.claim.lay W hcl k1 k2 Y (le_trans ?_ hY)
  have hd : s.d = D.d := A.claim.sized.d
  have g5 : ∀ (l' : ℕ) (m : Bool), kkSize (shapeOf s true) l' (if m then 5 else 3) = s.d :=
    fun _ m => by cases m <;> rfl
  have g6 : ∀ (l' : ℕ) (m : Bool), kkSize (shapeOf s true) l' (if m then 6 else 4) = s.d :=
    fun _ m => by cases m <;> rfl
  rcases (isAcc_iff sn).mp hs with rfl | rfl | rfl | rfl | rfl | rfl
  · show kkSize (shapeOf s true) _ (if c.v.isMoe i then 5 else 3) ≤ D.d
    rw [g5, hd]
  · show kkSize (shapeOf s true) _ (if c.v.isMoe i then 6 else 4) ≤ D.d
    rw [g6, hd]
  · show s.d ≤ D.d
    rw [hd]
  · show s.dq ≤ D.dq
    exact le_of_eq A.claim.sized.dq
  · show (if (shapeOf s true).moe.getD (c.v.lay i) false = true then s.fe else s.f) ≤ D.f
    have hf : s.f = D.f := A.claim.sized.f
    have hfe : s.fe = D.fe := A.claim.sized.fe
    have h2 := A.f2
    split_ifs <;> omega
  · show s.d ≤ D.d
    rw [hd]

/-- The vector of member number lm of the list of claims that claimsT returns for the segment G, U
or D, at the place of row e and column yv, is the B side of the panel of the segment's routed
product on the layer with routed experts number lm. -/
theorem wvB_routed {sn : String} (hs : sn = "G" ∨ sn = "U" ∨ sn = "D") {lm : ℕ}
    (T : CallTie ρ c h D z (panR sn lm).fam) {l : List WsClaim} (hl : c.claimsT sn = some l)
    {x : WsClaim} (hi : l[lm]? = some x) {e yv : ℕ}
    (he : e < (panR sn lm).nr D) (hy : yv < (panR sn lm).nc D) :
    wvClaim ρ c.wsLay W x
        (e * 2 ^ ceilLog2 (if sn == "D" then c.v.y.h.fe else c.v.y.h.d) + yv) =
      (panR sn lm).B D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh e yv := by
  have hlt : lm < l.length := (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨hn, hat⟩ := claimsT_routed_at c sn A.claim.p3 hs hl
  rcases hs with rfl | rfl | rfl
  · exact wvB_Gr A W r tb zh T (hn ▸ hlt) ((hat lm hlt).symm.trans hi) he hy
  · exact wvB_Ur A W r tb zh T (hn ▸ hlt) ((hat lm hlt).symm.trans hi) he hy
  · exact wvB_Dr A W r tb zh T (hn ▸ hlt) ((hat lm hlt).symm.trans hi) he hy

/-- If b, with the number v0, is the panel of segment g of call q of the lookup's join (AtA), then
the vector of claim number v0 + i, for a row i of b, is row i of the B side of the library's panel
of the name of g, on that panel's columns. -/
theorem wvOf_AtA {p : PanelEnv} {cl : List WsClaim} {b : SBlk} {v0 q : ℕ} {g : Seg}
    (T : CallTie ρ c h D z (panOf g.name).fam) (H : AtA p c cl b v0 q g) :
    ∀ i, i < b.ni → ∀ Y, Y < (panOf g.name).nc D → wvOf ρ c.wsLay W cl (v0 + i) Y =
      (panOf g.name).B D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh i Y := by
  obtain ⟨st, l, hacc, -, -, hl, hlen, hat⟩ := H
  intro i hi Y hY
  have hi' : i < l.length := by omega
  have e : l[i]? = some l[i] := List.getElem?_eq_getElem hi'
  rw [wvOf_at ρ c.wsLay W ((hat i hi).trans e)]
  exact wvB_acc A W r tb zh hacc T hl e hY

/-- If b, with the number v0, is the panel of the routed product of segment g on the layer with
routed experts number lm (AtR), then the vector of claim number v0, at the place of row e and column
yv of b, is the B side of the library's panel of the name of g and of lm. Asked beside: the panels
and the claims are made from one environment. -/
theorem wvOf_AtR {p : PanelEnv} (hv : p.v = c.v) {cl : List WsClaim} {b : SBlk} {v0 q : ℕ}
    {g : Seg} {lm : ℕ} (T : CallTie ρ c h D z (panR g.name lm).fam)
    (H : AtR p c cl b v0 q g lm) :
    ∀ e, e < (panR g.name lm).nr D → ∀ yv, yv < (panR g.name lm).nc D →
      wvOf ρ c.wsLay W cl v0 (e * 2 ^ b.wy + yv) =
        (panR g.name lm).B D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh e yv := by
  obtain ⟨st, st', l, -, hname, hlm, -, hstep, hbl, hl, hlen, hat⟩ := H
  intro e he yv hy
  have hlm' : lm < l.length := by omega
  have e2 : l[lm]? = some l[lm] := List.getElem?_eq_getElem hlm'
  obtain ⟨hwy, -⟩ := triStep_wy hstep hbl
  rw [hv] at hwy
  rw [wvOf_at ρ c.wsLay W (hat.trans e2), hwy]
  exact wvB_routed A W r tb zh hname T hl e2 he hy

end Names

#print axioms eqN_cube
#print axioms TnRow_at
#print axioms TnPan_at
#print axioms sumSel_boxSum
#print axioms wvClaim_Tn
#print axioms wv_two
#print axioms wv_three
#print axioms wvB_acc
#print axioms wvB_acc_zero
#print axioms wvB_routed
#print axioms wvOf_AtA
#print axioms wvOf_AtR

/-! ## The panel QK -/

section PanelQK

variable (ρ : Reading K)

/-- Panel QK: the vector of the claim of row lam is the row of the B side, on the panel's columns.
The hypotheses are those of claim_QK in Johnson/Road/FormsKeysQKF.lean. -/
theorem wvB_QK {c : ClaimEnv} {sW : WsShape} {D : Dim} {lk L0 : ℕ} {ζ : ℕ → K}
    (C : ClaimFits ρ c sW D lk L0 ζ) {q : ℕ} {cd : CallD} {sg : Seg} (F : QKFits c D q cd sg)
    {ah lfc : Array E} (h : c.headWeights = some (ah, lfc)) (hrt : c.rt.size = D.lT)
    {tb : Tables} {lam : ℕ} (hlam : lam < c.v.y.Lam) (R : RopeFits ρ c D tb L0 lam)
    {z zh : ℕ → K}
    (hz : ∀ j < aC D (call .QK), pt ρ (c.v.zk.getD q #[]) j = zc D z (call .QK) j)
    (hzh : ∀ j < D.lT, zh j = pt ρ c.rt j) (r : Rd K) (W : Wm K) {cl : WsClaim}
    (hcl : c.claim 0 lam (fun G =>
      if G.name == "hd" then some { AV := ah }
      else if G.name == "cd" then some { AV := c.ropeFactor (eqTab c.rt) lfc lam }
      else c.facRs G 0 (ceilLog2 c.v.y.h.d)) = some cl) {Y : ℕ} (hY : Y < Pan.QK.nc D) :
    wvClaim ρ c.wsLay W cl Y =
      Pan.QK.B D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh lam Y := by
  have hh : D.P.nq + D.P.nkv ≤ 64 := by
    rw [F.sized.nq, F.sized.nkv]
    exact F.heads
  have hX : (kindsOf (L0 + lam))[0]? = some 0 := by
    unfold kindsOf
    split <;> rfl
  have hU : (units D.P)[first D.P (L0 + lam) + 0]? = some (uQK D.P) :=
    tnOf_unit D tb C.even z zh ζ .QK rfl lam (C.layers lam hlam)
  have hcl' : c.claim 0 lam (facQK c ah lfc lam) = some cl := hcl
  rw [← TnRow_at D r tb L0 _ z zh .QK 0 lam hY, TnRow_QK D r tb L0 lk W z zh _ hh lam]
  refine wv_Tn ρ C W hcl' hlam hX hU
    (fs := [fun hd => if hd < D.P.nq + D.P.nkv then AH D z hd else 0, kp D tb L0 z zh lam,
      Pan.QK.Ec D (zetaAt D .QK 0 Y)]) ?_
  intro u hOK hco hnm Fs hFs
  have hnm' : u.g.map (fun y => (y.name, y.cls)) = [("hd", 'A'), ("cd", 'A'), ("kk", 'E')] := hnm
  obtain ⟨g1, g2, g3, hg, n1, n2, n3⟩ := map_three hnm'
  have m3 : g3 ∈ u.g := by
    rw [hg]
    simp
  rw [hg] at hco hFs ⊢
  have a1 : g1.name = "hd" := congrArg Prod.fst n1
  have a2 : g2.name = "cd" := congrArg Prod.fst n2
  have a3 : g3.name = "kk" := congrArg Prod.fst n3
  have b1 : g1.cls = 'A' := congrArg Prod.snd n1
  have b2 : g2.cls = 'A' := congrArg Prod.snd n2
  have b3 : g3.cls = 'E' := congrArg Prod.snd n3
  have hco' : [coordOf g1, coordOf g2, coordOf g3] =
      [⟨64, .whole⟩, ⟨D.P.ch, .whole⟩, ⟨D.P.d, .low⟩] := hco
  have r2 : g2.R = D.P.ch := congrArg Coord.R (List.cons.inj (List.cons.inj hco').2).1
  have c1 : (g1.cls == 'E') = false := by
    rw [b1]
    rfl
  have c2 : (g2.cls == 'E') = false := by
    rw [b2]
    rfl
  have hwy : ceilLog2 c.v.y.h.d = Pan.QK.wcol D := by
    rw [ceilLog2_eq_clog, C.d]
    rfl
  have hcol := (F.chOK h).col
  obtain ⟨X1, q1, f1, ha, rfl⟩ := mapM_cons_some hFs
  obtain ⟨X2, q2, f2, hb, rfl⟩ := mapM_cons_some ha
  obtain ⟨X3, q3, f3, hc, rfl⟩ := mapM_cons_some hb
  have hr : q3 = [] := by simpa using hc.symm
  subst hr
  rw [facQK_hd c ah lfc lam a1] at f1
  rw [facQK_cd c ah lfc lam a2] at f2
  rw [facQK_kk c ah lfc lam a3] at f3
  cases f1
  cases f2
  have hle : g3.R ≤ 2 ^ Pan.QK.wcol D := by
    rw [size_of_ok hOK m3 b3, ← hwy]
    exact facRs_le f3
  have s1 : selOf [g1, g2, g3] Y g1 = none :=
    selOf_other _ _ (by rw [a1]; rfl) (by rw [a1]; rfl)
  have s2 : selOf [g1, g2, g3] Y g2 = none :=
    selOf_other _ _ (by rw [a2]; rfl) (by rw [a2]; rfl)
  have s3 : selOf [g1, g2, g3] Y g3 = some Y := by
    rw [selOf_kk _ _ a3, hasE_last a1 a2 a3]
    rfl
  refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil))
  · simp only [s1]
    intro v _
    rw [fac_hd ρ F h g1 c1 v, AHP_eq_AH D hz v]
  · simp only [s2]
    intro v hv
    have hv' : v < c.v.y.h.dh := by
      rw [← F.sized.ch, ← r2]
      exact hv
    rw [fac_cd ρ F h hrt R g2 c2 hv', ← kpP_zh D tb L0 _ hzh lam v,
      kpP_eq_kp D hcol tb L0 hz zh lam v]
  · simp only [s3]
    intro j hj
    exact Ec_zetaAt D .QK 0 (nc_lt hY) (lt_of_lt_of_le hj hle)

/-- If b, with the number v0, is the panel of a segment named QK (AtQK), then the vector of claim
number v0 + i, for a row i of b, is row i of the B side of the library's panel QK, on that panel's
columns. The hypotheses are those of claims_QK in Johnson/Road/FormsKeysQKF.lean. -/
theorem wvOf_AtQK {c : ClaimEnv} {sW : WsShape} {D : Dim} {lk L0 : ℕ} {ζ : ℕ → K}
    (C : ClaimFits ρ c sW D lk L0 ζ) {q : ℕ} {cd : CallD} {sg : Seg} (F : QKFits c D q cd sg)
    (hrt : c.rt.size = D.lT) {tb : Tables}
    (R : ∀ lam, lam < c.v.y.Lam → RopeFits ρ c D tb L0 lam) {z zh : ℕ → K}
    (hz : ∀ j < aC D (call .QK), pt ρ (c.v.zk.getD q #[]) j = zc D z (call .QK) j)
    (hzh : ∀ j < D.lT, zh j = pt ρ c.rt j) (r : Rd K) (W : Wm K) {p : PanelEnv}
    {cl : List WsClaim} {b : SBlk} {v0 q' : ℕ} {g : Seg} (H : AtQK p c cl b v0 q' g) :
    ∀ i, i < b.ni → ∀ Y, Y < Pan.QK.nc D → wvOf ρ c.wsLay W cl (v0 + i) Y =
      Pan.QK.B D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh i Y := by
  obtain ⟨st, st', l, hname, -, -, -, hl, hlen, hat⟩ := H
  rw [hname] at hl
  obtain ⟨hL, ah, lfc, hw, hatq⟩ := claimsT_QK_at c hl
  intro i hi Y hY
  have hi' : i < l.length := by omega
  have e : l[i]? = some l[i] := List.getElem?_eq_getElem hi'
  rw [wvOf_at ρ c.wsLay W ((hat i hi).trans e)]
  exact wvB_QK ρ C F hw hrt (hL ▸ hi') (R i (hL ▸ hi')) hz hzh r W ((hatq i hi').symm.trans e) hY

end PanelQK

#print axioms wvB_QK
#print axioms wvOf_AtQK

/-! ## Past the columns -/

section Past

omit [Field K] in
/-- The groups of an asked unit of kind 0 have 64, dh and d indices. -/
theorem sizes_kind0 {s' : WsShape} {l : ℕ} {a : AskW} (ha : a ∈ layerAsks s' l) (hX : a.X = 0) :
    a.g.map (·.R) = [64, s'.dh, s'.d] := by
  unfold layerAsks at ha
  by_cases hm : s'.moe.getD l false = true
  · rw [if_pos hm] at ha
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with e | e | e | e | e | e | e | e | e | e <;> subst e <;>
      first | rfl | (exfalso; simp at hX)
  · rw [if_neg hm] at ha
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with e | e | e | e | e | e <;> subst e <;> first | rfl | (exfalso; simp at hX)

variable (ρ : Reading K)

/-- The vector of a claim on the unit of queries and keys (kind 0) is 0 from d on, the number of the
indices of kk. -/
theorem claim_zero_last {c : ClaimEnv} {s : WsShape} {lk : ℕ}
    (hl : wsLayOf s true lk = .ok c.wsLay) (W : Wm K) {lam : ℕ} {fac : WsGrp → Option WsFac}
    {x : WsClaim} (hcl : c.claim 0 lam fac = some x) :
    ∀ Y, s.d ≤ Y → wvClaim ρ c.wsLay W x Y = 0 := by
  intro Y hY
  obtain ⟨u, h1, h2, h3⟩ := claim_inv hcl
  have hgr : u.g.map (fun y => (y.name, y.cls)) = [("hd", 'A'), ("cd", 'A'), ("kk", 'E')] :=
    groups_found hl h1 h2 (Nat.zero_le _)
  obtain ⟨g1, g2, g3, hu, e1, e2, e3⟩ := map_three hgr
  have n1 : g1.name = "hd" := congrArg Prod.fst e1
  have n2 : g2.name = "cd" := congrArg Prod.fst e2
  have n3 : g3.name = "kk" := congrArg Prod.fst e3
  obtain ⟨-, a, ha, o, e, eX, -⟩ := unit_found hl h1 h2
  obtain ⟨l', hl'⟩ := ask_of_layer ha (by rw [eX]; exact Nat.zero_le _)
  have hR : u.g.map (·.R) = [64, s.dh, s.d] := by
    rw [e]
    show (placeP a.g lk 0).map (·.R) = _
    rw [sizes_placeP]
    have r := sizes_kind0 hl' eX
    exact r
  rw [hu] at hR
  have hR3 : g3.R = s.d := by
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hR
    exact hR.2.2
  rw [hu] at h3
  obtain ⟨X1, r1, -, hb, hf⟩ := mapM_cons_some h3
  obtain ⟨X2, r2, -, hb2, rfl⟩ := mapM_cons_some hb
  obtain ⟨X3, r3, -, hb3, rfl⟩ := mapM_cons_some hb2
  have hr : r3 = [] := by simpa using hb3.symm
  subst hr
  unfold wvClaim
  simp only [h2, hu, hf]
  show sumSel ρ (selOf [g1, g2, g3] Y) [(X1, g1), (X2, g2), (X3, g3)] (wgtOf u W) = 0
  rw [sumSel_last ρ n1 n2 n3, if_neg (by omega)]

/-- Past the columns of the library's panel of the name of g, the vector of a claim of a panel of
which AtA holds is 0. -/
theorem wvOf_AtA_zero {c : ClaimEnv} {h : Model.Layer.Shape} {pc : List (List String)}
    {s : WsShape} {D : Dim} {lk L0 : ℕ} {ζ : ℕ → K} (A : AimFits ρ c h pc s D lk L0 ζ)
    (W : Wm K) {p : PanelEnv} {cl : List WsClaim} {b : SBlk} {v0 q : ℕ} {g : Seg}
    (H : AtA p c cl b v0 q g) :
    ∀ i, i < b.ni → ∀ Y, (panOf g.name).nc D ≤ Y → wvOf ρ c.wsLay W cl (v0 + i) Y = 0 := by
  obtain ⟨st, l, hacc, -, -, hl, hlen, hat⟩ := H
  intro i hi Y hY
  have hi' : i < l.length := by omega
  have e : l[i]? = some l[i] := List.getElem?_eq_getElem hi'
  rw [wvOf_at ρ c.wsLay W ((hat i hi).trans e)]
  exact wvB_acc_zero A W hacc hl e hY

/-- Past the columns of the library's panel QK, the vector of a claim of a panel of which AtQK holds
is 0. -/
theorem wvOf_AtQK_zero {c : ClaimEnv} {sW : WsShape} {D : Dim} {lk L0 : ℕ} {ζ : ℕ → K}
    (C : ClaimFits ρ c sW D lk L0 ζ) (W : Wm K) {p : PanelEnv} {cl : List WsClaim} {b : SBlk}
    {v0 q' : ℕ} {g : Seg} (H : AtQK p c cl b v0 q' g) :
    ∀ i, i < b.ni → ∀ Y, Pan.QK.nc D ≤ Y → wvOf ρ c.wsLay W cl (v0 + i) Y = 0 := by
  obtain ⟨st, st', l, hname, -, -, -, hl, hlen, hat⟩ := H
  rw [hname] at hl
  obtain ⟨-, ah, lfc, -, hatq⟩ := claimsT_QK_at c hl
  intro i hi Y hY
  have hi' : i < l.length := by omega
  have e : l[i]? = some l[i] := List.getElem?_eq_getElem hi'
  rw [wvOf_at ρ c.wsLay W ((hat i hi).trans e)]
  refine claim_zero_last ρ C.lay W ((hatq i hi').symm.trans e) Y ?_
  have hd : sW.d = D.d := C.sized.d
  rw [hd]
  exact hY

end Past

#print axioms claim_zero_last
#print axioms wvOf_AtA_zero
#print axioms wvOf_AtQK_zero

/-! ## Past the columns of a panel with the selector -/

section PastThree

variable (ρ : Reading K)

/-- The vector of a claim on a unit of routed experts (kinds 7, 8, 10) is 0 at every place whose
column is none of the indices of kk. wk: the bits of a column. -/
theorem claim_zero_three {c : ClaimEnv} {s : WsShape} {lk : ℕ}
    (hl : wsLayOf s true lk = .ok c.wsLay) (W : Wm K) {X lam : ℕ} {fac : WsGrp → Option WsFac}
    {x : WsClaim} (hcl : c.claim X lam fac = some x) (hX : X = 7 ∨ X = 8 ∨ X = 10) {wk : ℕ}
    (hwk : ceilLog2 (if X = 10 then s.fe else s.d) = wk) :
    ∀ i yv, yv < 2 ^ wk → (if X = 10 then s.fe else s.d) ≤ yv →
      wvClaim ρ c.wsLay W x (i * 2 ^ wk + yv) = 0 := by
  intro i yv hy hle
  obtain ⟨u, h1, h2, h3⟩ := claim_inv hcl
  have hgr := groups_found hl h1 h2 (by omega)
  have hg : groupsOf X = [("kk", 'E'), ("e", 'E'), ("x", 'E')] := by
    rcases hX with e | e | e <;> rw [e] <;> rfl
  rw [hg] at hgr
  obtain ⟨g1, g2, g3, hu, e1, e2, e3⟩ := map_three hgr
  have n1 : g1.name = "kk" := congrArg Prod.fst e1
  have n2 : g2.name = "e" := congrArg Prod.fst e2
  have n3 : g3.name = "x" := congrArg Prod.fst e3
  have hR := first_found hl h1 h2 hX
  rw [hu] at hR
  have hR1 : g1.R = if X = 10 then s.fe else s.d := Option.some.inj hR
  rw [hu] at h3
  obtain ⟨X1, r1, -, ha, hf⟩ := mapM_cons_some h3
  obtain ⟨X2, r2, -, hb, rfl⟩ := mapM_cons_some ha
  obtain ⟨X3, r3, -, hc, rfl⟩ := mapM_cons_some hb
  have hr : r3 = [] := by simpa using hc.symm
  subst hr
  unfold wvClaim
  simp only [h2, hu, hf]
  show sumSel ρ (selOf [g1, g2, g3] (i * 2 ^ wk + yv)) [(X1, g1), (X2, g2), (X3, g3)]
    (wgtOf u W) = 0
  rw [sumSel_three ρ n1 n2 n3 X1 X2 X3 _ (by rw [hR1]; exact hwk) i hy, if_neg (by omega)]

/-- The same for a claim of a routed product, by the segment's name: past the columns of the
library's panel. -/
theorem routed_zero {c : ClaimEnv} {sW : WsShape} {D : Dim} {lk L0 : ℕ} {ζ : ℕ → K}
    (C : ClaimFits ρ c sW D lk L0 ζ) (W : Wm K) {sn : String}
    (hs : sn = "G" ∨ sn = "U" ∨ sn = "D") {lm lam : ℕ} {fac : WsGrp → Option WsFac} {x : WsClaim}
    (hcl : c.claim (if sn == "G" then 7 else if sn == "U" then 8 else 10) lam fac = some x) :
    ∀ e yv, yv < 2 ^ ceilLog2 (if sn == "D" then c.v.y.h.fe else c.v.y.h.d) →
      (panR sn lm).nc D ≤ yv →
      wvClaim ρ c.wsLay W x
        (e * 2 ^ ceilLog2 (if sn == "D" then c.v.y.h.fe else c.v.y.h.d) + yv) = 0 := by
  have hd : sW.d = D.d := C.sized.d
  have hfe : sW.fe = D.fe := C.sized.fe
  intro e yv hy hn
  rcases hs with rfl | rfl | rfl
  · refine claim_zero_three ρ C.lay W hcl (Or.inl rfl) (wk := ceilLog2 c.v.y.h.d) ?_ e yv hy ?_
    · show ceilLog2 sW.d = ceilLog2 c.v.y.h.d
      rw [hd, C.d]
    · show sW.d ≤ yv
      rw [hd]
      exact hn
  · refine claim_zero_three ρ C.lay W hcl (Or.inr (Or.inl rfl)) (wk := ceilLog2 c.v.y.h.d) ?_ e yv
      hy ?_
    · show ceilLog2 sW.d = ceilLog2 c.v.y.h.d
      rw [hd, C.d]
    · show sW.d ≤ yv
      rw [hd]
      exact hn
  · refine claim_zero_three ρ C.lay W hcl (Or.inr (Or.inr rfl)) (wk := ceilLog2 c.v.y.h.fe) ?_ e
      yv hy ?_
    · show ceilLog2 sW.fe = ceilLog2 c.v.y.h.fe
      rw [hfe, C.fe]
    · show sW.fe ≤ yv
      rw [hfe]
      exact hn

/-- Past the columns of the library's panel of the name of g and of lm, in every row, the vector of
the claim of a panel of which AtR holds is 0. -/
theorem wvOf_AtR_zero {c : ClaimEnv} {sW : WsShape} {D : Dim} {lk L0 : ℕ} {ζ : ℕ → K}
    (C : ClaimFits ρ c sW D lk L0 ζ) (W : Wm K) {p : PanelEnv} (hv : p.v = c.v)
    {cl : List WsClaim} {b : SBlk} {v0 q : ℕ} {g : Seg} {lm : ℕ}
    (H : AtR p c cl b v0 q g lm) :
    ∀ e yv, yv < 2 ^ b.wy → (panR g.name lm).nc D ≤ yv →
      wvOf ρ c.wsLay W cl v0 (e * 2 ^ b.wy + yv) = 0 := by
  obtain ⟨st, st', l, h3, hname, hlm, -, hstep, hbl, hl, hlen, hat⟩ := H
  intro e yv hy hn
  have hlm' : lm < l.length := by omega
  have e2 : l[lm]? = some l[lm] := List.getElem?_eq_getElem hlm'
  obtain ⟨hwy, -⟩ := triStep_wy hstep hbl
  rw [hv] at hwy
  obtain ⟨-, hatr⟩ := claimsT_routed_at c g.name (hv ▸ h3) hname hl
  rw [wvOf_at ρ c.wsLay W (hat.trans e2)]
  rw [hwy] at hy ⊢
  exact routed_zero ρ C W hname ((hatr lm hlm').symm.trans e2) e yv hy hn

end PastThree

#print axioms claim_zero_three
#print axioms wvOf_AtR_zero

end OnBytes.Road
