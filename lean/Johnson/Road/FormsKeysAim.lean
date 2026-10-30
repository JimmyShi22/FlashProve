-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysAim.lean: what a weight claim of a layer sub-proof claims, in the library's
words: nine of the ten kinds of panels.

A layer sub-proof ends with claims on the committed matrix W of weights (ClaimEnv.claimsA and
claimsT in OnBytes/Model/LayerPanels.lean). The sum that such a claim speaks of, over the entries
of W, is claimVal (Johnson/Road/FormsKeysWm.lean). The library has tensor claims on W and their
functional (TClaim.Tn in Inst/Model/Common/TensorClaim.lean), and, for each row of a weight panel
of a feed-forward segment, the value of the row's tensor claim (Pan.TnRow; for a panel with the
selector Pan.TnPan; Inst/Model/FF/Objects.lean), written with the weights w l of the segment's
layers. This file shows that claimVal is the functional of a named tensor claim, and so the panel's
value where the library's weights are those that the library's own layout reads in the same W: w l
:= layerR D.P lk W (L0 + l).

What is compared with what. The left side, claimVal, is a definition of these files, on the record
that ClaimEnv.claim returns on the verifier's own layout of the weights, with its own factors. It
is not a function of the verifier. That the verifier's own settling of a claim comes to claimVal is
claim_cells (Johnson/Road/FormsKeysFac.lean); the two are joined in
Johnson/Road/FormsKeysSettle.lean. The right sides are the library's.

Main definitions: CallTie, AimFits, zetaOf. Main theorems.
 - claimTn_G, claimTn_U, claimTn_V, claimTn_O, claimTn_D, claimTn_LR, claimTn_Gr, claimTn_Ur,
   claimTn_Dr: claimVal = (tnOf D tb L0 z zh ζ p row).Tn D.P lk W, with tnOf of
   Johnson/Road/FormsKeysTn.lean.
 - claim_G to claim_Dr: the same with Pan.TnRow (for Gr, Ur, Dr: Pan.TnPan) on the right.
 - list_G to list_Dr: the same of member number i of the lists that claimsA and claimsT return.
 - claimFits_of_layout, aimFits_of_layout: the records from the two layouts. Each claim theorem
   takes the claim in the words in which Johnson/Road/FormsKeysFold.lean says what member number i
   of the verifier's list is (claimsA_at_G and its like; claimsT_routed_at). The panel QK is the
   matter of another file.

Who reads the right sides. In the library's state beside which these files are built, Pan.TnRow and
Pan.TnPan are named in Inst/Model/FF/Objects.lean alone, and there in definitions alone: no theorem
reads them. TClaim and layerR are named in many files. So the form with tnOf is the one that can
meet a theorem of the library.

The parts. Johnson/Road/FormsKeysWLay.lean: the two layouts of the weights are one; the number,
names and classes of a unit. Johnson/Road/FormsKeysTnP.lean and Johnson/Road/FormsKeysClaim.lean:
from a claim to a tensor claim of the library; the factors on the coordinates of the batched
sumcheck's place. Johnson/Road/FormsKeysEw.lean: the factor on a segment's entries.
Johnson/Road/FormsKeysTn.lean: the library's panels on the library's layout.

The cuts. On a layer with routed experts the verifier's unit for G and U has kind 5 and 6 and fe
indices of x, the first half of the family's f entries; the routed G and U begin at entry fe. The
unit for D has kind 9 on every layer, with fe or f indices of kk, while the factor on kk is made
from the bits of f columns on every layer.

The hypotheses. Every theorem on a claim asks the record AimFits and the tie of its own family's
call (CallTie), no other family's.
 - AimFits. aimFits_of_layout concludes it from: layout returns the layout of the layer sub-proof;
   the switches; the sizes agree with the shape; g is the number of a group; the shape of the
   weights agrees with the library's parameters and has the shape's number of layers; wsLayOf
   returns on it; ζ is the batched sumcheck's point on the library's lamS D coordinates. The last
   is met by the definition zetaOf; the verifier's own number of rounds need not be lamS D. The
   hypotheses on the shape of the weights in the words of the verifier's caller, and sizes D that
   meet all of them, are in Johnson/Road/FormsKeysAimV.lean. The sizes dimOf h of
   Johnson/Road/FormsKeysFits.lean do not: they have the vocabulary 0, on which wsLayOf refuses.
 - CallTie s0: the call that holds the family's segment has the library's line; the verifier's
   least number of columns does not pass the library's; the call's point has the coordinates of the
   layer and the column; it reads as the library's point zc D z of the call. G and U stand in call
   0; V, O and D in call 1; LR in call 2. By the runs of Johnson/Road/FormsKeysRunK.lean the second
   clause holds for all calls at the full-size public example; at the small one it fails for call 0
   and holds for calls 1 and 2: there the theorems on G, U, Gr and Ur do not apply. The first two
   clauses are also run on made-up shapes (Johnson/Road/FormsKeysRun8.lean). For one call the last
   clause can be met at every point (zc_met, Johnson/Road/FormsKeysQKF.lean); for all calls at one
   z it follows from the letters in which the lookup makes the calls' points, where the second
   clause holds for all eight calls (callTieV_of_look, Johnson/Road/FormsKeysLookT.lean; see there
   for what it asks).
 - All of them together at one environment: no run, no theorem.

What is not claimed. That the hidden value under a claim's slot is claimVal is not shown here.
Which claim belongs to which row of which panel of the verifier's own list is the matter of
Johnson/Road/FormsKeysFold.lean. See also Johnson/Road/FormsKeysKit.lean. The program does
not import this file.
-/
import Johnson.Road.FormsKeysClaim
import Johnson.Road.FormsKeysTn
import Johnson.Road.FormsKeysEw

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading WsShape WsGrp WsFac WsClaim CallD Seg wsLayOf)
open OnBytes.Model.Layer (ClaimEnv Env layout)
open Inst.Model (Tables TClaim)
open Inst.Model.Layout (Kind Coord UnitS units first uD)
open Inst.Model.FFSeg (Dim Fam Pan Rd pans lamS layerR isExpL fSh ew len call fams used aC zc)

variable {K : Type} [Field K]

/-! ## The hypotheses -/

/-- The call of the verifier's layout that holds the segment of family s0 is the library's call of
the family, and its point is the library's: its line names the library's families in order; the
verifier's least number of columns does not pass the library's; the point has the coordinates of the
layer and of the column; on the library's number of coordinates it reads as the library's point of
the call. -/
def CallTie (ρ : Reading K) (c : ClaimEnv) (h : Model.Layer.Shape) (D : Dim) (z : ℕ → K)
    (s0 : Fam) : Prop :=
  ∀ (q : ℕ) (cd : CallD) (s : Seg), c.v.callOf (segName s0) = some (q, cd, s) →
    cd.segs.map (·.name) = (fams (call s0)).map segName ∧
    h.nmin - h.ll - h.lt ≤ Nat.clog 2 (used D (call s0)) ∧
    c.v.y.h.ll + cd.lJ ≤ (c.v.zk.getD q #[]).size ∧
    ∀ j, j < aC D (call s0) → pt ρ (c.v.zk.getD q #[]) j = zc D z (call s0) j

/-- What all theorems of this file ask. The tie of a family's call (CallTie) is not in it: each
theorem asks that of its own family. -/
structure AimFits (ρ : Reading K) (c : ClaimEnv) (h : Model.Layer.Shape) (pc : List (List String))
    (s : WsShape) (D : Dim) (lk L0 : ℕ) (ζ : ℕ → K) : Prop where
  /-- the record of Johnson/Road/FormsKeysClaim.lean -/
  claim : ClaimFits ρ c s D lk L0 ζ
  /-- the layout of the layer sub-proof is the one that layout returns -/
  hy : layout h pc = .ok c.v.y
  /-- the switches -/
  sw : Switches h
  /-- the library's sizes agree with the shape -/
  sized : Sized h D
  /-- a layer has twice the hidden units of an expert -/
  f2 : D.f = 2 * D.fe

section Aim

variable {ρ : Reading K} {c : ClaimEnv} {h : Model.Layer.Shape} {pc : List (List String)}
  {s : WsShape} {D : Dim} {lk L0 : ℕ} {z ζ : ℕ → K} (A : AimFits ρ c h pc s D lk L0 ζ)

include A

/-! ## Tools -/

/-- The factor on the entries of a family's segment, from entry x0 on, weighs an index as the
library's ew does. a, b: x0 is a times, the family's length b times the number of the group's
indices. -/
theorem ew_at {s0 : Fam} (T : CallTie ρ c h D z s0) {G : WsGrp}
    (hE : G.cls = 'E') (hR : G.R = G.o * 2 ^ G.z) {x0 a b : ℕ} (hx0 : x0 = a * G.R)
    (hlen : len D s0 = b * G.R) (hab : a < b) {X : WsFac}
    (hX : c.facEw G (segName s0) x0 = some X) :
    ∀ x, x < G.R → facAt ρ X G x = ew D z s0 (x0 + x) := by
  obtain ⟨q, cd, sg, hcall⟩ := facEw_call hX
  obtain ⟨hn, hfl, hsz, hz⟩ := T q cd sg hcall
  exact facEw_ew_mul ρ A.hy A.sw A.sized s0 hcall hn hfl hsz hz G x0 (beq_iff_eq.mpr hE) hR hx0
    hlen hab hX

/-- A layer of the group has routed experts in the verifier's count, in the library's count within
the segment and in the model, or in none of the three; with the kinds of its units and the number of
its hidden units that are not routed. -/
theorem layer_cases (lam : ℕ) :
    (c.v.isMoe lam = true ∧ isExpL lam = true ∧
        kindsOf (L0 + lam) = [0, 1, 2, 5, 6, 7, 8, 9, 10, 11] ∧ fSh D lam = D.fe) ∨
      (c.v.isMoe lam = false ∧ ¬ isExpL lam = true ∧ kindsOf (L0 + lam) = [0, 1, 2, 3, 4, 9] ∧
        fSh D lam = D.f) := by
  have h0 := A.claim.even
  by_cases he : lam % 2 = 1
  · have e1 : isExpL lam = true := by simp [isExpL, he]
    exact Or.inl ⟨by simp [Env.isMoe, A.claim.p3, he], e1, if_pos (by omega), if_pos e1⟩
  · have he0 : lam % 2 = 0 := by omega
    have e1 : ¬ isExpL lam = true := by simp [isExpL, he0]
    exact Or.inr ⟨by simp [Env.isMoe, A.claim.p3, he0], e1, if_neg (by omega), if_neg e1⟩

/-- A claim on a unit with the two groups kk and x, as the verifier makes it for a segment of the
lookup's join: the factor on kk from the lowest wy coordinates of the batched sumcheck's place, the
factor on x from the segment's entries. p: the library's panel; b: the family's length is b times
the number of indices of x. -/
theorem aim_two (W : Wm K) {X lam i wy : ℕ} {s0 : Fam} {p : Pan} {cl : WsClaim}
    (hcl : c.claim X lam (fun G => if G.name == "kk" then c.facRs G 0 wy
      else c.facEw G (segName s0) 0) = some cl)
    (hlam : lam < c.v.y.Lam) (hX : (kindsOf (L0 + lam))[i]? = some X)
    (hg : groupsOf X = [("kk", 'E'), ("x", 'E')]) {R1 R2 : ℕ} {k1 k2 : Kind}
    (hU : (units D.P)[first D.P (L0 + lam) + i]? = some ⟨[⟨R1, k1⟩, ⟨R2, k2⟩], 2⟩)
    (hp : p ∈ pans D) (hwy : wy = p.wcol D)
    (T : CallTie ρ c h D z s0) {b : ℕ} (hlen : len D s0 = b * R2)
    (hb : 0 < b) :
    claimVal ρ c.wsLay W cl = (⟨first D.P (L0 + lam) + i, ⟨[⟨R1, k1⟩, ⟨R2, k2⟩], 2⟩,
      [p.Ec D ζ, ew D z s0]⟩ : TClaim K).Tn D.P lk W := by
  refine claim_Tn A.claim W hcl hlam hX hU fun u ok hco hgr Fs hFs => ?_
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
  refine facs_two hFs (fun Xf hXf => ?_) (fun Xf hXf => ?_)
  · have hXf' : (if g1.name == "kk" then c.facRs g1 0 wy
        else c.facEw g1 (segName s0) 0) = some Xf := hXf
    rw [if_pos (beq_iff_eq.mpr n1)] at hXf'
    exact Ec_at A.claim hp c1 (size_of_ok ok m1 c1) hwy hXf'
  · have hXf' : (if g2.name == "kk" then c.facRs g2 0 wy
        else c.facEw g2 (segName s0) 0) = some Xf := hXf
    rw [n2, if_neg (by decide)] at hXf'
    intro v hv
    rw [ew_at A T c2 (size_of_ok ok m2 c2) (a := 0) (b := b) (Nat.zero_mul _).symm
      (by rw [r2]; exact hlen) hb hXf' v hv, Nat.zero_add]

/-- A claim on a unit with the three groups kk, e and x, as the verifier makes it for a routed
product: the factor on kk from the lowest wk coordinates of the place, that on e from the wr
coordinates above them, that on x from the segment's entries from x0 on. f3: the library's factor on
x. -/
theorem aim_three (W : Wm K) {X lam i wk wr x0 : ℕ} {s0 : Fam} {p : Pan} {cl : WsClaim}
    (hcl : c.claim X lam (fun G => if G.name == "kk" then c.facRs G 0 wk
      else if G.name == "e" then c.facRs G wk wr else c.facEw G (segName s0) x0) = some cl)
    (hlam : lam < c.v.y.Lam) (hX : (kindsOf (L0 + lam))[i]? = some X)
    (hg : groupsOf X = [("kk", 'E'), ("e", 'E'), ("x", 'E')]) {R1 R2 R3 : ℕ} {k1 k2 k3 : Kind}
    (hU : (units D.P)[first D.P (L0 + lam) + i]? = some ⟨[⟨R1, k1⟩, ⟨R2, k2⟩, ⟨R3, k3⟩], 2⟩)
    (hp : p ∈ pans D) (hwk : wk = p.wcol D) (hwr : wr = Nat.clog 2 (p.nr D))
    (T : CallTie ρ c h D z s0) {a b : ℕ} (hx0 : x0 = a * R3)
    (hlen : len D s0 = b * R3) (hab : a < b) {f3 : ℕ → K}
    (h3 : ∀ x, ew D z s0 (x0 + x) = f3 x) :
    claimVal ρ c.wsLay W cl = (⟨first D.P (L0 + lam) + i, ⟨[⟨R1, k1⟩, ⟨R2, k2⟩, ⟨R3, k3⟩], 2⟩,
      [p.Ec D ζ, p.Er D ζ, f3]⟩ : TClaim K).Tn D.P lk W := by
  refine claim_Tn A.claim W hcl hlam hX hU fun u ok hco hgr Fs hFs => ?_
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
  have r3 : g3.R = R3 := congrArg Coord.R hco.2.2
  refine facs_three hFs (fun Xf hXf => ?_) (fun Xf hXf => ?_) (fun Xf hXf => ?_)
  · have hXf' : (if g1.name == "kk" then c.facRs g1 0 wk
        else if g1.name == "e" then c.facRs g1 wk wr
        else c.facEw g1 (segName s0) x0) = some Xf := hXf
    rw [if_pos (beq_iff_eq.mpr n1)] at hXf'
    exact Ec_at A.claim hp c1 (size_of_ok ok m1 c1) hwk hXf'
  · have hXf' : (if g2.name == "kk" then c.facRs g2 0 wk
        else if g2.name == "e" then c.facRs g2 wk wr
        else c.facEw g2 (segName s0) x0) = some Xf := hXf
    rw [n2, if_neg (by decide), if_pos (by decide)] at hXf'
    exact Er_at A.claim hp c2 (size_of_ok ok m2 c2) hwk hwr hXf'
  · have hXf' : (if g3.name == "kk" then c.facRs g3 0 wk
        else if g3.name == "e" then c.facRs g3 wk wr
        else c.facEw g3 (segName s0) x0) = some Xf := hXf
    rw [n3, if_neg (by decide), if_neg (by decide)] at hXf'
    intro v hv
    rw [ew_at A T c3 (size_of_ok ok m3 c3) (a := a) (b := b) (by rw [r3]; exact hx0)
      (by rw [r3]; exact hlen) hab hXf' v hv, h3]

/-- The number of bits of a column of d entries. -/
theorem wy_d : ceilLog2 c.v.y.h.d = Nat.clog 2 D.d := by rw [ceilLog2_eq_clog, A.claim.d]

/-- An odd layer of the group that the verifier counts among those with routed experts is a layer of
the group, and its number among them is below the library's number of such layers. -/
theorem odd_layer {lm : ℕ} (hlm : lm < c.v.y.LamM) : 2 * lm + 1 < c.v.y.Lam ∧ lm < D.ne := by
  have h1 : lm < D.ne := A.claim.LamM ▸ hlm
  have h2 : D.ne = D.nl / 2 := rfl
  rw [A.claim.Lam]
  omega

/-- The kinds of the units of an odd layer of the group. -/
theorem odd_kinds (lm : ℕ) : kindsOf (L0 + (2 * lm + 1)) = [0, 1, 2, 5, 6, 7, 8, 9, 10, 11] := by
  have h0 := A.claim.even
  exact if_pos (by omega)

/-! ## The six panels of the lookup's join -/

variable (W : Wm K) (r : Rd K) (tb : Tables) (zh : ℕ → K)

/-- Panel V: the claim of row lam. -/
theorem claimTn_V (T : CallTie ρ c h D z .V) {lam : ℕ} (hlam : lam < c.v.y.Lam) {cl : WsClaim}
    (hcl : c.claim 1 lam (fun G => if G.name == "kk" then c.facRs G 0 (ceilLog2 c.v.y.h.d)
      else c.facEw G "V" 0) = some cl) :
    claimVal ρ c.wsLay W cl = (tnOf D tb L0 z zh ζ .V lam).Tn D.P lk W := by
  have hU := tnOf_unit D tb A.claim.even z zh ζ .V rfl lam (A.claim.layers lam hlam)
  have hX : (kindsOf (L0 + lam))[1]? = some 1 := by
    rcases layer_cases A lam with ⟨-, -, e, -⟩ | ⟨-, -, e, -⟩ <;> simp [e]
  exact aim_two A W (s0 := .V) (p := .V) hcl hlam hX rfl hU (by simp [pans]) (wy_d A)
    T (b := 1) (Nat.one_mul _).symm Nat.one_pos

/-- The same in the words of the library's panels. -/
theorem claim_V (T : CallTie ρ c h D z .V) {lam : ℕ} (hlam : lam < c.v.y.Lam) {cl : WsClaim}
    (hcl : c.claim 1 lam (fun G => if G.name == "kk" then c.facRs G 0 (ceilLog2 c.v.y.h.d)
      else c.facEw G "V" 0) = some cl) :
    claimVal ρ c.wsLay W cl =
      Pan.V.TnRow D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh ζ lam :=
  (claimTn_V A W tb zh T hlam hcl).trans (TnRow_V D r tb lk W z zh ζ L0 lam).symm

/-- Panel O: the claim of row lam. -/
theorem claimTn_O (T : CallTie ρ c h D z .O) {lam : ℕ} (hlam : lam < c.v.y.Lam) {cl : WsClaim}
    (hcl : c.claim 2 lam (fun G => if G.name == "kk" then c.facRs G 0 (ceilLog2 c.v.y.dq)
      else c.facEw G "O" 0) = some cl) :
    claimVal ρ c.wsLay W cl = (tnOf D tb L0 z zh ζ .O lam).Tn D.P lk W := by
  have hU := tnOf_unit D tb A.claim.even z zh ζ .O rfl lam (A.claim.layers lam hlam)
  have hX : (kindsOf (L0 + lam))[2]? = some 2 := by
    rcases layer_cases A lam with ⟨-, -, e, -⟩ | ⟨-, -, e, -⟩ <;> simp [e]
  have hwy : ceilLog2 c.v.y.dq = Pan.O.wcol D := by
    rw [ceilLog2_eq_clog, A.claim.dq]
    rfl
  exact aim_two A W (s0 := .O) (p := .O) hcl hlam hX rfl hU (by simp [pans]) hwy
    T (b := 1) (Nat.one_mul _).symm Nat.one_pos

/-- The same in the words of the library's panels. -/
theorem claim_O (T : CallTie ρ c h D z .O) {lam : ℕ} (hlam : lam < c.v.y.Lam) {cl : WsClaim}
    (hcl : c.claim 2 lam (fun G => if G.name == "kk" then c.facRs G 0 (ceilLog2 c.v.y.dq)
      else c.facEw G "O" 0) = some cl) :
    claimVal ρ c.wsLay W cl =
      Pan.O.TnRow D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh ζ lam :=
  (claimTn_O A W tb zh T hlam hcl).trans (TnRow_O D r tb lk W z zh ζ L0 lam).symm

/-- Panel G: the claim of row lam. On a layer with routed experts the unit is of kind 5 and holds
the gate's fe columns that are not routed, half of the family's entries. -/
theorem claimTn_G (T : CallTie ρ c h D z .G) {lam : ℕ} (hlam : lam < c.v.y.Lam) {cl : WsClaim}
    (hcl : c.claim (if c.v.isMoe lam then 5 else 3) lam (fun G =>
      if G.name == "kk" then c.facRs G 0 (ceilLog2 c.v.y.h.d) else c.facEw G "G" 0) = some cl) :
    claimVal ρ c.wsLay W cl = (tnOf D tb L0 z zh ζ .G lam).Tn D.P lk W := by
  have hU := tnOf_unit D tb A.claim.even z zh ζ .G rfl lam (A.claim.layers lam hlam)
  rcases layer_cases A lam with ⟨em, -, ek, ef⟩ | ⟨em, -, ek, ef⟩
  · rw [em] at hcl
    exact aim_two A W (X := 5) (s0 := .G) (p := .G) (i := 3) hcl hlam (by simp [ek]) rfl hU
      (by simp [pans]) (wy_d A) T (b := 2)
      (by show D.f = 2 * fSh D lam; rw [ef]; exact A.f2) (by decide)
  · rw [em] at hcl
    exact aim_two A W (X := 3) (s0 := .G) (p := .G) (i := 3) hcl hlam (by simp [ek]) rfl hU
      (by simp [pans]) (wy_d A) T (b := 1)
      (by show D.f = 1 * fSh D lam; rw [ef, Nat.one_mul]) Nat.one_pos

/-- The same in the words of the library's panels. -/
theorem claim_G (T : CallTie ρ c h D z .G) {lam : ℕ} (hlam : lam < c.v.y.Lam) {cl : WsClaim}
    (hcl : c.claim (if c.v.isMoe lam then 5 else 3) lam (fun G =>
      if G.name == "kk" then c.facRs G 0 (ceilLog2 c.v.y.h.d) else c.facEw G "G" 0) = some cl) :
    claimVal ρ c.wsLay W cl =
      Pan.G.TnRow D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh ζ lam :=
  (claimTn_G A W tb zh T hlam hcl).trans (TnRow_G D r tb A.claim.even lk W z zh ζ lam).symm

/-- Panel U: the claim of row lam. -/
theorem claimTn_U (T : CallTie ρ c h D z .U) {lam : ℕ} (hlam : lam < c.v.y.Lam) {cl : WsClaim}
    (hcl : c.claim (if c.v.isMoe lam then 6 else 4) lam (fun G =>
      if G.name == "kk" then c.facRs G 0 (ceilLog2 c.v.y.h.d) else c.facEw G "U" 0) = some cl) :
    claimVal ρ c.wsLay W cl = (tnOf D tb L0 z zh ζ .U lam).Tn D.P lk W := by
  have hU := tnOf_unit D tb A.claim.even z zh ζ .U rfl lam (A.claim.layers lam hlam)
  rcases layer_cases A lam with ⟨em, -, ek, ef⟩ | ⟨em, -, ek, ef⟩
  · rw [em] at hcl
    exact aim_two A W (X := 6) (s0 := .U) (p := .U) (i := 4) hcl hlam (by simp [ek]) rfl hU
      (by simp [pans]) (wy_d A) T (b := 2)
      (by show D.f = 2 * fSh D lam; rw [ef]; exact A.f2) (by decide)
  · rw [em] at hcl
    exact aim_two A W (X := 4) (s0 := .U) (p := .U) (i := 4) hcl hlam (by simp [ek]) rfl hU
      (by simp [pans]) (wy_d A) T (b := 1)
      (by show D.f = 1 * fSh D lam; rw [ef, Nat.one_mul]) Nat.one_pos

/-- The same in the words of the library's panels. -/
theorem claim_U (T : CallTie ρ c h D z .U) {lam : ℕ} (hlam : lam < c.v.y.Lam) {cl : WsClaim}
    (hcl : c.claim (if c.v.isMoe lam then 6 else 4) lam (fun G =>
      if G.name == "kk" then c.facRs G 0 (ceilLog2 c.v.y.h.d) else c.facEw G "U" 0) = some cl) :
    claimVal ρ c.wsLay W cl =
      Pan.U.TnRow D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh ζ lam :=
  (claimTn_U A W tb zh T hlam hcl).trans (TnRow_U D r tb A.claim.even lk W z zh ζ lam).symm

/-- Panel D: the claim of row lam. The unit is of kind 9 on every layer; it stands at place 7 of a
layer with routed experts and at place 5 of a dense one, and its group kk has fe or f indices. The
factor on kk is made from the bits of f columns on every layer. -/
theorem claimTn_D (T : CallTie ρ c h D z .D) {lam : ℕ} (hlam : lam < c.v.y.Lam) {cl : WsClaim}
    (hcl : c.claim 9 lam (fun G => if G.name == "kk" then c.facRs G 0 (ceilLog2 c.v.y.h.f)
      else c.facEw G "D" 0) = some cl) :
    claimVal ρ c.wsLay W cl = (tnOf D tb L0 z zh ζ .D lam).Tn D.P lk W := by
  have hU := tnOf_unit D tb A.claim.even z zh ζ .D rfl lam (A.claim.layers lam hlam)
  have hwy : ceilLog2 c.v.y.h.f = Pan.D.wcol D := by
    rw [ceilLog2_eq_clog, A.claim.f]
    rfl
  have e : ∀ n, tnOf D tb L0 z zh ζ .D lam = ⟨first D.P (L0 + lam) + n, uD D.P (fSh D lam),
        [Pan.D.Ec D ζ, ew D z .D]⟩ → (kindsOf (L0 + lam))[n]? = some 9 →
      claimVal ρ c.wsLay W cl = (tnOf D tb L0 z zh ζ .D lam).Tn D.P lk W := by
    intro n en hX
    rw [en] at hU ⊢
    exact aim_two A W (s0 := .D) (p := .D) hcl hlam hX rfl hU (by simp [pans]) hwy
      T (b := 1) (Nat.one_mul _).symm Nat.one_pos
  have t : tnOf D tb L0 z zh ζ .D lam = ⟨first D.P (L0 + lam) + (if isExpL lam then 7 else 5),
      uD D.P (fSh D lam), [Pan.D.Ec D ζ, ew D z .D]⟩ := rfl
  rcases layer_cases A lam with ⟨-, ee, ek, -⟩ | ⟨-, ee, ek, -⟩
  · rw [if_pos ee] at t
    exact e 7 t (by simp [ek])
  · rw [if_neg ee] at t
    exact e 5 t (by simp [ek])

/-- The same in the words of the library's panels. -/
theorem claim_D (T : CallTie ρ c h D z .D) {lam : ℕ} (hlam : lam < c.v.y.Lam) {cl : WsClaim}
    (hcl : c.claim 9 lam (fun G => if G.name == "kk" then c.facRs G 0 (ceilLog2 c.v.y.h.f)
      else c.facEw G "D" 0) = some cl) :
    claimVal ρ c.wsLay W cl =
      Pan.D.TnRow D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh ζ lam :=
  (claimTn_D A W tb zh T hlam hcl).trans
    (TnRow_D D r tb A.claim.even lk W z zh ζ (by have := A.f2; omega) lam).symm

/-- Panel LR: the claim of row i, the router of layer 2 i + 1 of the group. -/
theorem claimTn_LR (T : CallTie ρ c h D z .LR) {i : ℕ} (hi : i < c.v.y.LamM) {cl : WsClaim}
    (hcl : c.claim 11 (2 * i + 1) (fun G =>
      if G.name == "kk" then c.facRs G 0 (ceilLog2 c.v.y.h.d) else c.facEw G "LR" 0) = some cl) :
    claimVal ρ c.wsLay W cl = (tnOf D tb L0 z zh ζ .LR i).Tn D.P lk W := by
  obtain ⟨hlam, -⟩ := odd_layer A hi
  have hU := tnOf_unit D tb A.claim.even z zh ζ .LR rfl i (A.claim.layers _ hlam)
  have hX : (kindsOf (L0 + (2 * i + 1)))[9]? = some 11 := by simp [odd_kinds A]
  exact aim_two A W (s0 := .LR) (p := .LR) hcl hlam hX rfl hU (by simp [pans]) (wy_d A)
    T (b := 1) (Nat.one_mul _).symm Nat.one_pos

/-- The same in the words of the library's panels. -/
theorem claim_LR (T : CallTie ρ c h D z .LR) {i : ℕ} (hi : i < c.v.y.LamM) {cl : WsClaim}
    (hcl : c.claim 11 (2 * i + 1) (fun G =>
      if G.name == "kk" then c.facRs G 0 (ceilLog2 c.v.y.h.d) else c.facEw G "LR" 0) = some cl) :
    claimVal ρ c.wsLay W cl =
      Pan.LR.TnRow D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh ζ i :=
  (claimTn_LR A W tb zh T hi hcl).trans (TnRow_LR D r tb A.claim.even lk W z zh ζ i).symm

/-! ## The three kinds of panels with the selector -/

/-- The number of bits of an expert's number. -/
theorem wr_NE : ceilLog2 (max c.v.y.h.NE 1) = Nat.clog 2 D.nx := by
  rw [ceilLog2_eq_clog, A.claim.NE]
  rcases Nat.eq_zero_or_pos D.nx with e | e
  · rw [e]
    simp
  · rw [Nat.max_eq_left e]

/-- Panel Gr lm: the one claim of the routed gates of layer 2 lm + 1 of the group. -/
theorem claimTn_Gr (T : CallTie ρ c h D z .G) {lm : ℕ} (hlm : lm < c.v.y.LamM) {cl : WsClaim}
    (hcl : c.claim 7 (2 * lm + 1) (fun G =>
      if G.name == "kk" then c.facRs G 0 (ceilLog2 c.v.y.h.d)
      else if G.name == "e" then c.facRs G (ceilLog2 c.v.y.h.d) (ceilLog2 (max c.v.y.h.NE 1))
      else c.facEw G "G" c.v.y.h.fe) = some cl) :
    claimVal ρ c.wsLay W cl = (tnOf D tb L0 z zh ζ (.Gr lm) 0).Tn D.P lk W := by
  obtain ⟨hlam, hne⟩ := odd_layer A hlm
  have hU := tnOf_unit D tb A.claim.even z zh ζ (.Gr lm) rfl 0 (A.claim.layers _ hlam)
  exact aim_three A W (s0 := .G) (p := .Gr lm) (i := 5) hcl hlam (by simp [odd_kinds A]) rfl hU
    (by simp [pans, hne]) (wy_d A) (wr_NE A) T (a := 1) (b := 2)
    (by rw [Nat.one_mul]; exact A.claim.fe) A.f2 (by decide)
    (fun x => by rw [A.claim.fe])

/-- The same in the words of the library's panels. -/
theorem claim_Gr (T : CallTie ρ c h D z .G) {lm : ℕ} (hlm : lm < c.v.y.LamM) {cl : WsClaim}
    (hcl : c.claim 7 (2 * lm + 1) (fun G =>
      if G.name == "kk" then c.facRs G 0 (ceilLog2 c.v.y.h.d)
      else if G.name == "e" then c.facRs G (ceilLog2 c.v.y.h.d) (ceilLog2 (max c.v.y.h.NE 1))
      else c.facEw G "G" c.v.y.h.fe) = some cl) :
    claimVal ρ c.wsLay W cl =
      (Pan.Gr lm).TnPan D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh ζ :=
  (claimTn_Gr A W tb zh T hlm hcl).trans (TnPan_Gr D r tb A.claim.even lk W z zh ζ lm).symm

/-- Panel Ur lm. -/
theorem claimTn_Ur (T : CallTie ρ c h D z .U) {lm : ℕ} (hlm : lm < c.v.y.LamM) {cl : WsClaim}
    (hcl : c.claim 8 (2 * lm + 1) (fun G =>
      if G.name == "kk" then c.facRs G 0 (ceilLog2 c.v.y.h.d)
      else if G.name == "e" then c.facRs G (ceilLog2 c.v.y.h.d) (ceilLog2 (max c.v.y.h.NE 1))
      else c.facEw G "U" c.v.y.h.fe) = some cl) :
    claimVal ρ c.wsLay W cl = (tnOf D tb L0 z zh ζ (.Ur lm) 0).Tn D.P lk W := by
  obtain ⟨hlam, hne⟩ := odd_layer A hlm
  have hU := tnOf_unit D tb A.claim.even z zh ζ (.Ur lm) rfl 0 (A.claim.layers _ hlam)
  exact aim_three A W (s0 := .U) (p := .Ur lm) (i := 6) hcl hlam (by simp [odd_kinds A]) rfl hU
    (by simp [pans, hne]) (wy_d A) (wr_NE A) T (a := 1) (b := 2)
    (by rw [Nat.one_mul]; exact A.claim.fe) A.f2 (by decide)
    (fun x => by rw [A.claim.fe])

/-- The same in the words of the library's panels. -/
theorem claim_Ur (T : CallTie ρ c h D z .U) {lm : ℕ} (hlm : lm < c.v.y.LamM) {cl : WsClaim}
    (hcl : c.claim 8 (2 * lm + 1) (fun G =>
      if G.name == "kk" then c.facRs G 0 (ceilLog2 c.v.y.h.d)
      else if G.name == "e" then c.facRs G (ceilLog2 c.v.y.h.d) (ceilLog2 (max c.v.y.h.NE 1))
      else c.facEw G "U" c.v.y.h.fe) = some cl) :
    claimVal ρ c.wsLay W cl =
      (Pan.Ur lm).TnPan D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh ζ :=
  (claimTn_Ur A W tb zh T hlm hcl).trans (TnPan_Ur D r tb A.claim.even lk W z zh ζ lm).symm

/-- Panel Dr lm. -/
theorem claimTn_Dr (T : CallTie ρ c h D z .D) {lm : ℕ} (hlm : lm < c.v.y.LamM) {cl : WsClaim}
    (hcl : c.claim 10 (2 * lm + 1) (fun G =>
      if G.name == "kk" then c.facRs G 0 (ceilLog2 c.v.y.h.fe)
      else if G.name == "e" then c.facRs G (ceilLog2 c.v.y.h.fe) (ceilLog2 (max c.v.y.h.NE 1))
      else c.facEw G "D" 0) = some cl) :
    claimVal ρ c.wsLay W cl = (tnOf D tb L0 z zh ζ (.Dr lm) 0).Tn D.P lk W := by
  obtain ⟨hlam, hne⟩ := odd_layer A hlm
  have hU := tnOf_unit D tb A.claim.even z zh ζ (.Dr lm) rfl 0 (A.claim.layers _ hlam)
  have hwk : ceilLog2 c.v.y.h.fe = (Pan.Dr lm).wcol D := by
    rw [ceilLog2_eq_clog, A.claim.fe]
    rfl
  exact aim_three A W (s0 := .D) (p := .Dr lm) (i := 8) hcl hlam (by simp [odd_kinds A]) rfl hU
    (by simp [pans, hne]) hwk (wr_NE A) T (a := 0) (b := 1) (Nat.zero_mul _).symm
    (Nat.one_mul _).symm Nat.one_pos (fun x => by rw [Nat.zero_add])

/-- The same in the words of the library's panels. -/
theorem claim_Dr (T : CallTie ρ c h D z .D) {lm : ℕ} (hlm : lm < c.v.y.LamM) {cl : WsClaim}
    (hcl : c.claim 10 (2 * lm + 1) (fun G =>
      if G.name == "kk" then c.facRs G 0 (ceilLog2 c.v.y.h.fe)
      else if G.name == "e" then c.facRs G (ceilLog2 c.v.y.h.fe) (ceilLog2 (max c.v.y.h.NE 1))
      else c.facEw G "D" 0) = some cl) :
    claimVal ρ c.wsLay W cl =
      (Pan.Dr lm).TnPan D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh ζ :=
  (claimTn_Dr A W tb zh T hlm hcl).trans (TnPan_Dr D r tb A.claim.even lk W z zh ζ lm).symm

/-! ## The verifier's own lists of claims -/

/-- Member number i of the verifier's list of claims of segment G. -/
theorem list_G (T : CallTie ρ c h D z .G) {l : List WsClaim}
    (hl : c.claimsA "G" = some l) {i : ℕ} {cl : WsClaim} (hi : l[i]? = some cl) :
    claimVal ρ c.wsLay W cl =
      Pan.G.TnRow D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh ζ i := by
  have hlt : i < l.length := (List.getElem?_eq_some_iff.mp hi).1
  have hn : l.length = c.v.y.Lam := claimsA_length c "G" hl rfl
  exact claim_G A W r tb zh T (hn ▸ hlt) ((claimsA_at_G c hl i hlt).symm.trans hi)

/-- Member number i of the verifier's list of claims of segment U. -/
theorem list_U (T : CallTie ρ c h D z .U) {l : List WsClaim}
    (hl : c.claimsA "U" = some l) {i : ℕ} {cl : WsClaim} (hi : l[i]? = some cl) :
    claimVal ρ c.wsLay W cl =
      Pan.U.TnRow D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh ζ i := by
  have hlt : i < l.length := (List.getElem?_eq_some_iff.mp hi).1
  have hn : l.length = c.v.y.Lam := claimsA_length c "U" hl rfl
  exact claim_U A W r tb zh T (hn ▸ hlt) ((claimsA_at_U c hl i hlt).symm.trans hi)

/-- Member number i of the verifier's list of claims of segment V. -/
theorem list_V (T : CallTie ρ c h D z .V) {l : List WsClaim}
    (hl : c.claimsA "V" = some l) {i : ℕ} {cl : WsClaim} (hi : l[i]? = some cl) :
    claimVal ρ c.wsLay W cl =
      Pan.V.TnRow D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh ζ i := by
  have hlt : i < l.length := (List.getElem?_eq_some_iff.mp hi).1
  have hn : l.length = c.v.y.Lam := claimsA_length c "V" hl rfl
  exact claim_V A W r tb zh T (hn ▸ hlt) ((claimsA_at_V c hl i hlt).symm.trans hi)

/-- Member number i of the verifier's list of claims of segment O. -/
theorem list_O (T : CallTie ρ c h D z .O) {l : List WsClaim}
    (hl : c.claimsA "O" = some l) {i : ℕ} {cl : WsClaim} (hi : l[i]? = some cl) :
    claimVal ρ c.wsLay W cl =
      Pan.O.TnRow D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh ζ i := by
  have hlt : i < l.length := (List.getElem?_eq_some_iff.mp hi).1
  have hn : l.length = c.v.y.Lam := claimsA_length c "O" hl rfl
  exact claim_O A W r tb zh T (hn ▸ hlt) ((claimsA_at_O c hl i hlt).symm.trans hi)

/-- Member number i of the verifier's list of claims of segment D. -/
theorem list_D (T : CallTie ρ c h D z .D) {l : List WsClaim}
    (hl : c.claimsA "D" = some l) {i : ℕ} {cl : WsClaim} (hi : l[i]? = some cl) :
    claimVal ρ c.wsLay W cl =
      Pan.D.TnRow D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh ζ i := by
  have hlt : i < l.length := (List.getElem?_eq_some_iff.mp hi).1
  have hn : l.length = c.v.y.Lam := claimsA_length c "D" hl rfl
  exact claim_D A W r tb zh T (hn ▸ hlt) ((claimsA_at_D c hl i hlt).symm.trans hi)

/-- Member number i of the verifier's list of claims of segment LR. -/
theorem list_LR (T : CallTie ρ c h D z .LR) {l : List WsClaim}
    (hl : c.claimsA "LR" = some l) {i : ℕ} {cl : WsClaim} (hi : l[i]? = some cl) :
    claimVal ρ c.wsLay W cl =
      Pan.LR.TnRow D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh ζ i := by
  have hlt : i < l.length := (List.getElem?_eq_some_iff.mp hi).1
  have hn : l.length = c.v.y.LamM := claimsA_length c "LR" hl rfl
  exact claim_LR A W r tb zh T (hn ▸ hlt) ((claimsA_at_LR c hl i hlt).symm.trans hi)

/-- Member number lm of the verifier's list of claims of the routed product G. -/
theorem list_Gr (T : CallTie ρ c h D z .G) {l : List WsClaim}
    (hl : c.claimsT "G" = some l) {lm : ℕ} {cl : WsClaim} (hi : l[lm]? = some cl) :
    claimVal ρ c.wsLay W cl =
      (Pan.Gr lm).TnPan D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh ζ := by
  have hlt : lm < l.length := (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨hn, hat⟩ := claimsT_routed_at c "G" A.claim.p3 (by simp) hl
  exact claim_Gr A W r tb zh T (hn ▸ hlt) ((hat lm hlt).symm.trans hi)

/-- Member number lm of the verifier's list of claims of the routed product U. -/
theorem list_Ur (T : CallTie ρ c h D z .U) {l : List WsClaim}
    (hl : c.claimsT "U" = some l) {lm : ℕ} {cl : WsClaim} (hi : l[lm]? = some cl) :
    claimVal ρ c.wsLay W cl =
      (Pan.Ur lm).TnPan D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh ζ := by
  have hlt : lm < l.length := (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨hn, hat⟩ := claimsT_routed_at c "U" A.claim.p3 (by simp) hl
  exact claim_Ur A W r tb zh T (hn ▸ hlt) ((hat lm hlt).symm.trans hi)

/-- Member number lm of the verifier's list of claims of the routed product D. -/
theorem list_Dr (T : CallTie ρ c h D z .D) {l : List WsClaim}
    (hl : c.claimsT "D" = some l) {lm : ℕ} {cl : WsClaim} (hi : l[lm]? = some cl) :
    claimVal ρ c.wsLay W cl =
      (Pan.Dr lm).TnPan D r tb L0 (fun l => layerR D.P lk W (L0 + l)) z zh ζ := by
  have hlt : lm < l.length := (List.getElem?_eq_some_iff.mp hi).1
  obtain ⟨hn, hat⟩ := claimsT_routed_at c "D" A.claim.p3 (by simp) hl
  exact claim_Dr A W r tb zh T (hn ▸ hlt) ((hat lm hlt).symm.trans hi)

end Aim

/-! ## The record, from the layouts -/

/-- The batched sumcheck's point in the library's order, on the library's number of coordinates: the
top bit's coordinate first. -/
def zetaOf (ρ : Reading K) (c : ClaimEnv) (D : Dim) : ℕ → K :=
  fun t => ρ.val (c.rs.getD (lamS D - 1 - t) zeroE)

/-- The record ClaimFits follows from the two layouts. Asked: layout returns the layout of the
layer sub-proof; the switches; the sizes agree with the shape; g is the number of a group; the
shape of the weights agrees with the library's parameters and has the shape's number of layers;
wsLayOf returns the layout of the weights; ζ is the batched sumcheck's point on the library's
coordinates (zetaOf is such a ζ). Concluded: that the group's first layer is even, that its layers
are layers of the model, the widths, and the numbers of layers of a group. No call's tie is asked.
-/
theorem claimFits_of_layout {ρ : Reading K} {c : ClaimEnv} {h : Model.Layer.Shape}
    {pc : List (List String)} {s : WsShape} {D : Dim} {lk : ℕ} {ζ : ℕ → K}
    (hy : layout h pc = .ok c.v.y) (S : Switches h) (Z : Sized h D) (hg : c.v.g < c.v.y.NGr)
    (Zw : SizedW s D.P) (hsL : s.L = h.L) (hl : wsLayOf s true lk = .ok c.wsLay)
    (hζ : ∀ t, t < lamS D → ζ t = zetaOf ρ c D t) :
    ClaimFits ρ c s D lk (c.v.g * c.v.y.Lam) ζ := by
  have A := admitted_of_layout hy S.p3
  have sh := A.shape
  have hLam : c.v.y.Lam = 2 ^ h.ll := by rw [A.laid.Lam, sh]
  have hll : 1 ≤ h.ll := sh ▸ A.laid.ll
  have hnl : D.nl = 2 ^ h.ll := by
    show 2 ^ D.lL = _
    rw [Z.lL]
  refine ⟨Zw, hl, rfl, ?_, by rw [sh]; exact S.p3, ?_, hζ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have d2 : 2 ∣ c.v.g * c.v.y.Lam := by
      rw [hLam]
      exact Dvd.dvd.mul_left (dvd_pow_self 2 (by omega)) _
    exact Nat.mod_eq_zero_of_dvd d2
  · intro lam hlam
    rw [hLam] at hlam ⊢
    rw [← Zw.L, hsL]
    have hg' : c.v.g + 1 ≤ h.L / 2 ^ h.ll := by
      rw [← A.NGr]
      exact hg
    have h1 : (c.v.g + 1) * 2 ^ h.ll ≤ h.L / 2 ^ h.ll * 2 ^ h.ll := Nat.mul_le_mul_right _ hg'
    have h2 := Nat.div_mul_le_self h.L (2 ^ h.ll)
    have h3 : (c.v.g + 1) * 2 ^ h.ll = c.v.g * 2 ^ h.ll + 2 ^ h.ll := by ring
    omega
  · rw [sh]
    exact Z.d.symm
  · rw [sh]
    exact Z.f.symm
  · rw [sh]
    exact Z.fe.symm
  · rw [sh]
    exact Z.nexp.symm
  · show c.v.y.dq = D.P.nq * D.P.ch
    rw [A.laid.dq, sh, Z.nq, Z.ch]
  · rw [hLam, hnl]
  · show c.v.y.LamM = D.nl / 2
    rw [A.laid.LamM, sh, hnl]

/-- So does the record AimFits, under the same hypotheses; f = 2 fe is concluded too. -/
theorem aimFits_of_layout {ρ : Reading K} {c : ClaimEnv} {h : Model.Layer.Shape}
    {pc : List (List String)} {s : WsShape} {D : Dim} {lk : ℕ} {ζ : ℕ → K}
    (hy : layout h pc = .ok c.v.y) (S : Switches h) (Z : Sized h D) (hg : c.v.g < c.v.y.NGr)
    (Zw : SizedW s D.P) (hsL : s.L = h.L) (hl : wsLayOf s true lk = .ok c.wsLay)
    (hζ : ∀ t, t < lamS D → ζ t = zetaOf ρ c D t) :
    AimFits ρ c h pc s D lk (c.v.g * c.v.y.Lam) ζ := by
  have A := admitted_of_layout hy S.p3
  have hf2 : D.f = 2 * D.fe := by
    show D.P.f = 2 * D.P.fe
    rw [Z.f, Z.fe, ← A.shape]
    exact A.laid.ffe
  exact ⟨claimFits_of_layout hy S Z hg Zw hsL hl hζ, hy, S, Z, hf2⟩

#print axioms claimTn_V
#print axioms claimTn_O
#print axioms claimTn_G
#print axioms claimTn_U
#print axioms claimTn_D
#print axioms claimTn_LR
#print axioms claimTn_Gr
#print axioms claimTn_Ur
#print axioms claimTn_Dr
#print axioms claim_V
#print axioms claim_O
#print axioms claim_G
#print axioms claim_U
#print axioms claim_D
#print axioms claim_LR
#print axioms claim_Gr
#print axioms claim_Ur
#print axioms claim_Dr
#print axioms list_G
#print axioms list_U
#print axioms list_V
#print axioms list_O
#print axioms list_D
#print axioms list_LR
#print axioms list_Gr
#print axioms list_Ur
#print axioms list_Dr
#print axioms claimFits_of_layout
#print axioms aimFits_of_layout

end OnBytes.Road
