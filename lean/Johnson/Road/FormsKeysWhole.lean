-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysWhole.lean: the start form of the batched sumcheck of a layer sub-proof, less
the sum of the products of the two long vectors, is a sum of three parts.

A key of the lookup holds products of two hidden values and matrix products with weights. The
verifier's form for a call's factor in the lookup's join is worth alpha - q theta, less the
extension of the library's key vector, with these products added back (joinPart_keyVec',
Johnson/Road/FormsKeysShape.lean). The verifier starts the batched sumcheck from a form that holds
the eight factors (startOf, Johnson/Road/FormsKeysStart.lean). The sum over all places of the
product of the two long vectors that Johnson/Road/FormsKeysEnd.lean defines from the verifier's
panels is the sum of the panels' shares, which the comparisons of the panels show to be the
library's Sig0 plus om[1] times its Sig1. This file puts the two together.

What is compared with what. startOf is the last lines of the verifier's joinStart (joinStart_eq in
FormsKeysStart.lean, by definition). Sig0, Sig1, ClT, keyVec, wc, zc are the library's own. elP,
ACCP, TSP (Johnson/Road/FormsKeysFree.lean) are the library's el, ACC, TS with a free point for the
call's point. rPort is the record of Johnson/Road/FormsKeysPort.lean.

Main theorems.
 - sig0_ends: Sig0 reads none of the three families of end values that the second token sumcheck
   sends.
 - acc_side: the matrix products that the eight factors add back, under the calls' weights, are Sig0
   at rPort.
 - ts_side: the sums of products of two cells that the eight factors add back, under the calls'
   weights, are ClT.
 - start_whole: the worth of the start form less S, for any S that is Sig0 plus om[1] times Sig1 at
   rPort, is the sum of: (1) the sum over the calls of the call's weight times alpha - q theta less
   the extension of the key vector, plus the padding trees' number, less the worth of the form that
   the lookup's end leaves; (2) ClT less the hidden sum that the second token sumcheck claims; (3)
   om[1] times the difference of what the second token sumcheck leaves (KT) and Sig1.
 - start_stack: start_whole with the sum over all places of the product of the two long vectors for
   S, through stack_sig of Johnson/Road/FormsKeysPortSig.lean, at the weights and the points of the
   panels' environment.
 - parts_of_lines: the two hypotheses of start_whole on the factors, from the two lines in which
   joinStart makes them.

What is shown and what is only carried. Two cancellations are shown: that of the matrix products
against Sig0, and that of the sums of products of two cells against ClT. Sig1 is moved, not used:
any element could stand for it in hS and in the conclusion of start_whole. What KT is worth is not
looked at: H.KT, H.fo.cEnd and tT.sCl are fields of a free record here, and a wrong sign in the line
that makes KT (hearTerms, OnBytes/Model/Layer.lean) would be seen by nothing in these files. In
start_whole alpha and theta are any two elements; that they are the lookup's is asked nowhere in it.

Which value is which. The calls' weights, alpha, theta, om and the padding trees' number are public.
W.slot tT.sCl is a hidden value. The form of the lookup's end and KT are forms in hidden values.
rPort holds the array shownT as it is; that in the verifier's caller this array is what the second
token sumcheck sent is by reading hearStack (OnBytes/Model/Layer.lean). Sig0 reads nothing of it.
The never-sent vectors are free but for hH.

The hypotheses, and where they are met. No witness of all of them together is given here.
 - hz, hwc: the points and the weights of the calls 0, 1, 2 and 5 read as the library's at one z.
   acc_side asks them of the calls 0, 1 and 2, which hold the six families with a matrix product;
   ts_side of all four, which hold the nine families with products of two cells. Nothing is asked of
   the four other calls. Where the verifier's least number of columns passes the library's for no
   call, look_fits (Johnson/Road/FormsKeysLookT.lean) concludes them for all eight calls at one z
   from the letters in which the lookup makes the points and the weights. By the runs of
   Johnson/Road/FormsKeysRunK.lean and Johnson/Road/FormsKeysRunZ.lean that is
   so at the full-size shipped example; at the small one call 0 has more columns than the library's,
   and its point does not read as the library's at the two points z that are run there.
 - hH: the never-sent vector number 0 is the honest vector of the gated products at the library's
   token point. It can be met by definition, since hv is free; that it holds of what a prover has
   committed to is the matter of the product layers, which are not looked at.
 - hcap, hfe: start_stack concludes them from the record SigFits and hc.
 - hS: stack_sig concludes it, under the record SigFits, which sigFits_of_look
   (Johnson/Road/FormsKeysCaller.lean) concludes.
 - parts_of_lines asks hn, hfl and hpad of all eight calls: hfl fails at the small shipped example
   for four calls, so there it does not apply. Its other hypotheses are those of joinPart_keyVec'.

What is not claimed. All statements are identities in a world. No part is claimed by itself. That
the left side is 0 is the matter of the batched sumcheck. Then the element from which om is made
parts the third from the first two; the second token sumcheck gives the second from the third; the
first is what is left, and the lookup reads it. None of these steps is looked at. The program does
not import this file.
-/
import Johnson.Road.FormsKeysStart
import Johnson.Road.FormsKeysSig
import Johnson.Road.FormsKeysSigG
import Johnson.Road.FormsKeysPortSig

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading World Aff CallD WsShape WsClaim lastOf)
open OnBytes.Model.Layer (Env Lay Heard Reads TableAsk TableAt PanelEnv ClaimEnv Panels StackEnd
  layout scalesHeld readsOf layTables tableAsks panelsA panelsT placePanels stackEnd)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell Fam LW Rd Sig0 Sig1 ClT wc famsIn fSh hhU zpos zc aC keyVec fams
  used lut layerR)

variable {K : Type} [Field K]

/-! ## Sums over the eight calls -/

/-- A function on the eight calls as a function on the numbers: 0 from 8 on. -/
def onFin (f : Fin 8 → K) (q : ℕ) : K := if h : q < 8 then f ⟨q, h⟩ else 0

/-- At the number of a call. -/
theorem onFin_val (f : Fin 8 → K) (c : Fin 8) : onFin f c.val = f c := by
  unfold onFin
  rw [dif_pos c.isLt]

/-- A weighted sum over the numbers below 8 is the sum over the calls. -/
theorem sum_onFin (g : ℕ → K) (f : Fin 8 → K) :
    ∑ q ∈ range 8, g q * onFin f q = ∑ c : Fin 8, g c.val * f c := by
  rw [← Fin.sum_univ_eq_sum_range (fun q => g q * onFin f q) 8]
  exact Finset.sum_congr rfl fun c _ => by rw [onFin_val]

/-- At a number below 8. -/
theorem onFin_lt (f : Fin 8 → K) {q : ℕ} (hq : q < 8) : onFin f q = f ⟨q, hq⟩ := by
  unfold onFin
  rw [dif_pos hq]

/-! ## The matrix products -/

omit [Field K] in
/-- The calls from number 3 on hold none of the six families. -/
theorem sixIn_none : ∀ c : Fin 8, ¬ c.val < 3 → ∀ b : Bool, sixIn c b = [] := by decide

omit [Field K] in
/-- So no family of such a call is one of the six. -/
theorem not_six {c : Fin 8} (h3 : ¬ c.val < 3) {l : ℕ} {s : Fam} (hs : s ∈ famsIn c l) :
    s ∉ six := by
  intro h6
  have hm : s ∈ (famsIn c l).filter (fun s => decide (s ∈ six)) :=
    List.mem_filter.mpr ⟨hs, by simpa using h6⟩
  rw [famsIn_six, sixIn_none c h3] at hm
  simp at hm

omit [Field K] in
/-- The calls other than 0, 1, 2 and 5 hold none of the nine families with products of two cells. -/
theorem nineIn_none : ∀ c : Fin 8, c ∉ [(0 : Fin 8), 1, 2, 5] → ∀ b : Bool, nineIn c b = [] := by
  decide

omit [Field K] in
/-- So no family of such a call is one of the nine. -/
theorem not_nine {c : Fin 8} (h : c ∉ [(0 : Fin 8), 1, 2, 5]) {l : ℕ} {s : Fam}
    (hs : s ∈ famsIn c l) : s ∉ nine := by
  intro h9
  have hm : s ∈ (famsIn c l).filter (fun s => decide (s ∈ nine)) :=
    List.mem_filter.mpr ⟨hs, by simpa using h9⟩
  rw [famsIn_nine, nineIn_none c h] at hm
  simp at hm

omit [Field K] in
/-- The calls 0, 1 and 2 are among the four. -/
theorem three_of_four : ∀ c : Fin 8, c.val < 3 → c ∈ [(0 : Fin 8), 1, 2, 5] := by decide

section Acc

variable [scl : Scl] (ρ : Reading K) (y : Lay) (shownT : Array E) (hv : ℕ → ℕ → K) (D : Dim)
  (t : Cell → K) (tb : Tables) (L0 : ℕ) (w : ℕ → LW K) (z zh : ℕ → K)

/-- The early panels read none of the three families of end values of the second token sumcheck. -/
theorem sig0_ends (r : Rd K) (R2 sc2 : ℕ → K) (sel2 : ℕ → ℕ → K) :
    Sig0 D (withEnds r R2 sc2 sel2) tb L0 w z zh = Sig0 D r tb L0 w z zh := by
  unfold Sig0
  rw [early_pans]
  rfl

/-- The keys of a family other than the six hold no matrix product: its sum ACCP is 0 at any
point. -/
theorem ACCP_zero {s : Fam} (hs : s ∉ six) (ζ : ℕ → K) (l : ℕ) : ACCP D t w ζ s l = 0 := by
  unfold ACCP
  refine Finset.sum_eq_zero fun x _ => ?_
  have e : (fun i => Inst.Model.FFSeg.mat D t w s l x i) = fun _ => 0 :=
    funext (mat_zero D t w hs l x)
  rw [e, Blocks.ext_const, mul_zero]

variable (e : Array E) (ζ : Fin 8 → ℕ → K)

/-- The matrix products that the calls' factors add back are the early panels' shares. ζ c: the
point of call c; e: the calls' weights. If the point of each of the calls 0, 1 and 2, which hold the
six families with a matrix product, reads as the library's point of the call at one z (hz), the
weight of each of the three as the library's (hwc), and the never-sent vector number 0 is the honest
vector of the gated products at the library's token point (hH), then the sum over the eight calls,
under their weights, over the layers, under theirs, and over the families of the call that are
present in the layer, of the matrix products in the family's keys is the library's Sig0 at the
record rPort. Nothing is asked of the five other calls. -/
theorem acc_side (hcap : D.lT ≤ D.cap) (hfe : D.fe ≤ D.f)
    (hz : ∀ c : Fin 8, c.val < 3 → ∀ j, j < aC D c → ζ c j = zc D z c j)
    (hwc : ∀ c : Fin 8, c.val < 3 → ρ.val (e.getD c.val zeroE) = wc D z c)
    (hH : ∀ l, l < D.nl → ∀ j, j < fSh D l →
      hv 0 (l * 2 ^ ceilLog2 y.h.f + j) = hhU D t l j (zpos D z)) :
    ∑ c : Fin 8, ρ.val (e.getD c.val zeroE) * ∑ l ∈ range D.nl, elP D (ζ c) l *
        ((famsIn c l).map fun s => ACCP D t w (ζ c) s l).sum =
      Sig0 D (rPort ρ y shownT hv D t z zh) tb L0 w z zh := by
  unfold rPort
  rw [sig0_ends, sig0_acc D t tb L0 w z zh zh _ _ hfe hH]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases h3 : c.val < 3
  · have hlist : ∀ l, ((famsIn c l).map fun s => ACCP D t w (ζ c) s l) =
        (famsIn c l).map fun s => Inst.Model.FFSeg.ACC D t w z s l := fun l =>
      List.map_congr_left fun s hs => ACCP_eq_ACC D t w hcap (call_of_famsIn hs) (hz c h3) l
    have hin : ∑ l ∈ range D.nl, elP D (ζ c) l *
          ((famsIn c l).map fun s => ACCP D t w (ζ c) s l).sum =
        ∑ l ∈ range D.nl, Inst.Model.FFSeg.el D z c l *
          ((famsIn c l).map fun s => Inst.Model.FFSeg.ACC D t w z s l).sum :=
      Finset.sum_congr rfl fun l _ => by rw [elP_eq_el D (hz c h3) l, hlist l]
    rw [hwc c h3, hin]
  · have a0 : ∀ l, ((famsIn c l).map fun s => ACCP D t w (ζ c) s l).sum = 0 := fun l =>
      List.sum_eq_zero fun x hx => by
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
        exact ACCP_zero D t w (not_six h3 hs) (ζ c) l
    have b0 : ∀ l, ((famsIn c l).map fun s => Inst.Model.FFSeg.ACC D t w z s l).sum = 0 :=
      fun l => List.sum_eq_zero fun x hx => by
        obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
        exact ACC_zero D t w z (not_six h3 hs) l
    simp only [a0, b0, mul_zero, Finset.sum_const_zero]

/-! ## The products of two cells -/

/-- The keys of a family other than the nine hold no product of two cells. -/
theorem term_zero {s : Fam} (hs : s ∉ nine) (l x i : ℕ) :
    Inst.Model.FFSeg.term D t tb L0 w s l x i = 0 := by
  cases s <;> first
    | rfl
    | exact absurd (by simp [nine]) hs

/-- So for a call other than 0, 1, 2 and 5 nothing is left to the sumcheck over the positions, at
any point. -/
theorem TSP_zero {c : Fin 8} (h : c ∉ [(0 : Fin 8), 1, 2, 5]) (ξ : ℕ → K) :
    TSP D t tb L0 w c ξ = 0 := by
  have a0 : ∀ l i, ((famsIn c l).map fun s => TERMP D t tb L0 w ξ s l i).sum = 0 := fun l i =>
    List.sum_eq_zero fun x hx => by
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
      unfold TERMP
      exact Finset.sum_eq_zero fun x _ => by
        rw [term_zero D t tb L0 w (not_nine h hs), mul_zero]
  unfold TSP
  simp only [a0, mul_zero, Finset.sum_const_zero]
  rw [Blocks.ext_const]

/-- The same for the library's TS. -/
theorem TS_zero {c : Fin 8} (h : c ∉ [(0 : Fin 8), 1, 2, 5]) :
    Inst.Model.FFSeg.TS D t tb L0 w z c = 0 := by
  have a0 : ∀ l i,
      ((famsIn c l).map fun s => Inst.Model.FFSeg.TERM D t tb L0 w z s l i).sum = 0 := fun l i =>
    List.sum_eq_zero fun x hx => by
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
      unfold Inst.Model.FFSeg.TERM
      exact Finset.sum_eq_zero fun x _ => by
        rw [term_zero D t tb L0 w (not_nine h hs), mul_zero]
  unfold Inst.Model.FFSeg.TS
  simp only [a0, mul_zero, Finset.sum_const_zero]
  rw [Blocks.ext_const]

/-- The sums of the products of two cells that the calls' factors add back are the library's ClT,
the honest value of the sum that the second token sumcheck claims. Asked: the points and the weights
of the calls 0, 1, 2 and 5, which hold the nine families with such products, read as the library's
at one z. Nothing is asked of the four other calls. -/
theorem ts_side (hcap : D.lT ≤ D.cap)
    (hz : ∀ c : Fin 8, c ∈ [(0 : Fin 8), 1, 2, 5] → ∀ j, j < aC D c → ζ c j = zc D z c j)
    (hwc : ∀ c : Fin 8, c ∈ [(0 : Fin 8), 1, 2, 5] → ρ.val (e.getD c.val zeroE) = wc D z c) :
    ∑ c : Fin 8, ρ.val (e.getD c.val zeroE) * TSP D t tb L0 w c (ζ c) = ClT D t tb L0 w z := by
  unfold ClT
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases h : c ∈ [(0 : Fin 8), 1, 2, 5]
  · rw [hwc c h, TSP_eq_TS D t tb L0 w hcap (hz c h)]
  · rw [TSP_zero D t tb L0 w h, TS_zero D t tb L0 w z h, mul_zero, mul_zero]

/-! ## The start form against the sum of the batched sumcheck -/

/-- The start form of the batched sumcheck, less S. S: any element that is the library's Sig0 plus
om[1] times its Sig1 at the record rPort (hS). parts: eight forms, each worth what joinPart_keyVec'
(Johnson/Road/FormsKeysShape.lean) concludes of a call's factor, at any two elements alpha and theta
and at the points ζ (hp). Under the hypotheses of acc_side and ts_side the difference is the sum of
three parts: the sum over the calls of the call's weight times alpha - q theta less the extension of
the key vector, plus the padding trees' number, less the worth of the form that the lookup's end
leaves; the library's ClT less the hidden sum that the second token sumcheck claims; and om[1] times
the difference of what the second token sumcheck leaves and Sig1. Two cancellations are shown: the
matrix products against Sig0, and the sums of products of two cells against ClT. Sig1 is moved from
S to the third part and not used. -/
theorem start_whole (W : World K) (H : Heard) (om : Array E) (parts : List Aff) {tT : Model.Tsc}
    (hT : H.tT = some tT) (hlen : parts.length = 8) (alpha theta : E)
    (hp : ∀ (c : Fin 8) (f : Aff), parts[c.val]? = some f →
      f.value ρ W = ρ.val alpha - (c.val : K) * ρ.val theta -
        Blocks.ext (aC D c) (keyVec D t tb L0 w c) (ζ c) + TSP D t tb L0 w c (ζ c) +
        ∑ l ∈ range D.nl, elP D (ζ c) l * ((famsIn c l).map fun s => ACCP D t w (ζ c) s l).sum)
    (hcap : D.lT ≤ D.cap) (hfe : D.fe ≤ D.f)
    (hz : ∀ c : Fin 8, c ∈ [(0 : Fin 8), 1, 2, 5] → ∀ j, j < aC D c → ζ c j = zc D z c j)
    (hwc : ∀ c : Fin 8, c ∈ [(0 : Fin 8), 1, 2, 5] →
      ρ.val (H.fo.e.getD c.val zeroE) = wc D z c)
    (hH : ∀ l, l < D.nl → ∀ j, j < fSh D l →
      hv 0 (l * 2 ^ ceilLog2 y.h.f + j) = hhU D t l j (zpos D z))
    {S : K} (hS : S = Sig0 D (rPort ρ y shownT hv D t z zh) tb L0 w z zh +
      ρ.val (om.getD 1 zeroE) * Sig1 D (rPort ρ y shownT hv D t z zh) tb L0 w z zh) :
    (startOf H om parts).value ρ W - S =
      ((∑ c : Fin 8, ρ.val (H.fo.e.getD c.val zeroE) *
          (ρ.val alpha - (c.val : K) * ρ.val theta -
            Blocks.ext (aC D c) (keyVec D t tb L0 w c) (ζ c))) +
        ρ.val (padOf H) - H.fo.cEnd.value ρ W) +
      (ClT D t tb L0 w z - W.slot tT.sCl) +
      ρ.val (om.getD 1 zeroE) *
        (H.KT.value ρ W - Sig1 D (rPort ρ y shownT hv D t z zh) tb L0 w z zh) := by
  have hp' : ∀ x ∈ parts.zipIdx, x.1.value ρ W =
      onFin (fun c : Fin 8 => ρ.val alpha - (c.val : K) * ρ.val theta -
        Blocks.ext (aC D c) (keyVec D t tb L0 w c) (ζ c)) x.2 - onFin (fun _ => 0) x.2 +
      onFin (fun c : Fin 8 => TSP D t tb L0 w c (ζ c)) x.2 +
      onFin (fun c : Fin 8 => ∑ l ∈ range D.nl, elP D (ζ c) l *
        ((famsIn c l).map fun s => ACCP D t w (ζ c) s l).sum) x.2 := by
    rintro ⟨f, q⟩ hx
    have h1 : parts[q]? = some f := by simpa using List.mem_zipIdx_iff_getElem?.mp hx
    obtain ⟨hq, -⟩ := List.getElem?_eq_some_iff.mp h1
    rw [hlen] at hq
    have h2 := hp ⟨q, hq⟩ f h1
    show f.value ρ W = onFin _ q - onFin _ q + onFin _ q + onFin _ q
    rw [onFin_lt _ hq, onFin_lt _ hq, onFin_lt _ hq, onFin_lt _ hq, h2, sub_zero]
  have key := start_parts ρ W H om parts hT
    (onFin fun c : Fin 8 => ρ.val alpha - (c.val : K) * ρ.val theta -
      Blocks.ext (aC D c) (keyVec D t tb L0 w c) (ζ c))
    (onFin fun _ => 0) (onFin fun c : Fin 8 => TSP D t tb L0 w c (ζ c))
    (onFin fun c : Fin 8 => ∑ l ∈ range D.nl, elP D (ζ c) l *
      ((famsIn c l).map fun s => ACCP D t w (ζ c) s l).sum) hp'
  rw [hlen] at key
  simp only [mul_sub, Finset.sum_sub_distrib] at key
  rw [sum_onFin, sum_onFin, sum_onFin, sum_onFin,
    acc_side ρ y shownT hv D t tb L0 w z zh H.fo.e ζ hcap hfe
      (fun c h3 => hz c (three_of_four c h3)) (fun c h3 => hwc c (three_of_four c h3)) hH,
    ts_side ρ D t tb L0 w z H.fo.e ζ hcap hz hwc] at key
  rw [key, hS]
  simp only [mul_zero, Finset.sum_const_zero, sub_zero]
  ring

end Acc

/-! ## With the sum over all places -/

section Sum

variable [scl : Scl] {ρ : Reading K} {Wo : World K} {p : PanelEnv} {c : ClaimEnv}
  {h : Model.Layer.Shape} {pc : List (List String)} {s : WsShape} {D : Dim} {lk L0 : ℕ}
  {cc : Cells K} {t : Cell → K} {low z zh ζ : ℕ → K} {tb : Tables}

/-- start_whole with the sum over all places of the product of the two long vectors of
Johnson/Road/FormsKeysEnd.lean for S, through stack_sig (Johnson/Road/FormsKeysPortSig.lean), whose
hypotheses stand first here, from S to hlam. The weights are those that the library's layout reads
in the matrix M. The start form reads the calls' weights of the panels' environment (hHe), and the
calls' points are those of that environment, as in the verifier's caller. hz: the points of the
calls 0, 1, 2 and 5 read as the library's; their weights do by the record S. hc: the library's cap
on a tree's depth is the shape's. -/
theorem start_stack (S : SigFits ρ Wo p c h pc s D lk L0 cc t low z zh ζ tb) (M : Wm K)
    (hh : ℕ → ℕ → K) {TS : List ℕ} (hTS : TS = [0, 1, 2, 5]) {pans' : Panels}
    {cl : List WsClaim} (hp : panelsT p TS (panelsA p {}) = some pans')
    (hcl : c.weightClaims TS = some cl) {om : Array E} (hom : ρ.val (om.getD 0 zeroE) = 1)
    {rs H1 V : Array E} {lam : ℕ} {shownA shownB : E} {s' : StackEnd}
    (hst : stackEnd p.v.y (placePanels pans'.bl).1 rs lam om H1 V shownA shownB = some s')
    (hlam : (ceilLog2 (placePanels pans'.bl).2 == lam) = true)
    (H : Heard) (hHe : H.fo.e = p.e) (parts : List Aff) {tT : Model.Tsc} (hT : H.tT = some tT)
    (hlen : parts.length = 8) (alpha theta : E)
    (hparts : ∀ (q : Fin 8) (f : Aff), parts[q.val]? = some f →
      f.value ρ Wo = ρ.val alpha - (q.val : K) * ρ.val theta -
        Blocks.ext (aC D q) (keyVec D t tb L0 (fun l => layerR D.P lk M (L0 + l)) q)
          (pt ρ (p.v.zk.getD q.val #[])) +
        TSP D t tb L0 (fun l => layerR D.P lk M (L0 + l)) q (pt ρ (p.v.zk.getD q.val #[])) +
        ∑ l ∈ range D.nl, elP D (pt ρ (p.v.zk.getD q.val #[])) l * ((famsIn q l).map fun s0 =>
          ACCP D t (fun l => layerR D.P lk M (L0 + l)) (pt ρ (p.v.zk.getD q.val #[])) s0 l).sum)
    (hc : D.cap = h.lidb)
    (hz : ∀ q : Fin 8, q ∈ [(0 : Fin 8), 1, 2, 5] → ∀ j, j < aC D q →
      pt ρ (p.v.zk.getD q.val #[]) j = zc D z q j)
    (hH : ∀ l, l < D.nl → ∀ j, j < fSh D l →
      hh 0 (l * 2 ^ ceilLog2 p.v.y.h.f + j) = hhU D t l j (zpos D z)) :
    (startOf H om parts).value ρ Wo -
        ∑ Y ∈ range (2 ^ lam), vecOf (aG ρ Wo p.v.y om hh) (placePanels pans'.bl).1.toList Y *
          vecOf (bG ρ Wo (wvOf ρ c.wsLay M cl)) (placePanels pans'.bl).1.toList Y =
      ((∑ q : Fin 8, ρ.val (H.fo.e.getD q.val zeroE) *
          (ρ.val alpha - (q.val : K) * ρ.val theta -
            Blocks.ext (aC D q) (keyVec D t tb L0 (fun l => layerR D.P lk M (L0 + l)) q)
              (pt ρ (p.v.zk.getD q.val #[])))) +
        ρ.val (padOf H) - H.fo.cEnd.value ρ Wo) +
      (ClT D t tb L0 (fun l => layerR D.P lk M (L0 + l)) z - Wo.slot tT.sCl) +
      ρ.val (om.getD 1 zeroE) *
        (H.KT.value ρ Wo - Sig1 D (rPort ρ p.v.y p.shownT hh D t z zh) tb L0
          (fun l => layerR D.P lk M (L0 + l)) z zh) :=
  start_whole ρ p.v.y p.shownT hh D t tb L0 _ z zh (fun q => pt ρ (p.v.zk.getD q.val #[])) Wo H om
    parts hT hlen alpha theta hparts (hcap_of_layout S.aim.hy S.aim.sized hc)
    (by have h2 := S.aim.f2; omega) hz (fun q hq => by rw [hHe]; exact S.wc q hq) hH
    (stack_sig S M hh hTS hp hcl hom hst hlam)

end Sum

/-! ## The calls' factors, on the verifier's own lines -/

section Lines

variable {h : Model.Layer.Shape} {pc : List (List String)} {v : Env} {rd : Reads}
  {mats : Array (ℕ × ℕ)} {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}

/-- The hypotheses hlen and hp of start_whole, on the two lines in which joinStart makes the marks
and the calls' factors (hw, hparts; see joinStart_eq in Johnson/Road/FormsKeysStart.lean). Asked
beside what joinPart_keyVec' (Johnson/Road/FormsKeysShape.lean) asks for all calls: the layout has
eight calls (h8); the line of each names the families of the library's call of that number, in order
(hn); for none does the verifier's least number of columns pass the library's (hfl); the padding key
of each is the library's (hpad). Then there are eight factors, and the factor of call number cc is
worth alpha - cc theta, less the extension of the library's key vector of the call at the call's own
point, plus the sums of the products of two cells and the matrix products at that point. -/
theorem parts_of_lines (hy : layout h pc = .ok v.y) (S : Switches h)
    (hs : scalesHeld h v.sc = .ok ()) (hg : v.g < v.y.NGr) (hrd : readsOf v.y = .ok rd)
    (hl : layTables mats (tableAsks v.y rd v.g) 0 = some r) (ht : v.tab = r.1)
    {ρ : Reading K} (hρ : Numerals ρ) {D : Dim} (Zd : Sized h D) {W : World K}
    {zx Z zt : Array E} {ends : Array (Array E)}
    (hZ : lastOf zx v.y.h.la = .ok Z) (hzt : lastOf zx v.y.h.lt = .ok zt)
    (hm : v.zk.mapM (fun z => (lastOf z v.y.h.la).toOption) = some ends)
    (ha : ends.all (· == Z) = true) {s0 : Model.Forest.Shape}
    (hs0 : Model.Forest.shape v.y.cl v.y.h.lidb = .ok s0)
    (hpt : ((List.range s0.NC).all fun c =>
      (v.zk.getD c #[]).size == ((s0.calls[c]?).map (·.n)).getD 0) = true)
    (c : Cells K) (T : TrueAt ρ W v h.lt c (pt ρ Z) (pt ρ zt)) (tb : Tables) (L0 : ℕ)
    (w : ℕ → LW K) (alpha theta : E) {weighed : Array (Array Bool)}
    (hw : v.y.calls.mapM v.weighedOf = some weighed) {parts : List Aff}
    (hparts : (v.y.calls.zip weighed).toList.zipIdx.mapM
      (fun x => v.joinPart alpha theta x.2 x.1.1 x.1.2) = some parts)
    (h8 : v.y.calls.size = 8)
    (hn : ∀ (cc : Fin 8) (cd : CallD), v.y.calls[cc.val]? = some cd →
      cd.segs.map (·.name) = (fams cc).map segName)
    (hfl : ∀ cc : Fin 8, h.nmin - h.ll - h.lt ≤ Nat.clog 2 (used D cc))
    (hpad : ∀ cc : Fin 8,
      ρ.val (ofF ((v.y.cl.getD cc.val {}).tauAt (v.y.cl.getD cc.val {}).t0)) =
        (((lut tb cc).pad : ℤ) : K)) :
    parts.length = 8 ∧ ∀ (cc : Fin 8) (f : Aff), parts[cc.val]? = some f →
      f.value ρ W = ρ.val alpha - (cc.val : K) * ρ.val theta -
        Blocks.ext (aC D cc)
          (keyVec (scl := sclOf h v.sc v.g v.y.Lam) D (cellsOf D c) tb L0 w cc)
          (pt ρ (v.zk.getD cc.val #[])) +
        TSP (scl := sclOf h v.sc v.g v.y.Lam) D (cellsOf D c) tb L0 w cc
          (pt ρ (v.zk.getD cc.val #[])) +
        ∑ l ∈ range D.nl, elP D (pt ρ (v.zk.getD cc.val #[])) l *
          ((famsIn cc l).map fun s =>
            ACCP (scl := sclOf h v.sc v.g v.y.Lam) D (cellsOf D c) w
              (pt ρ (v.zk.getD cc.val #[])) s l).sum := by
  rw [Array.mapM_eq_mapM_toList] at hw
  obtain ⟨wl, hwl, rfl⟩ := map_some hw
  obtain ⟨lw, iw⟩ := list_mapM_some _ _ _ hwl
  obtain ⟨lp, ip⟩ := list_mapM_some _ _ _ hparts
  have hlw : wl.length = 8 := by rw [lw, Array.length_toList, h8]
  refine ⟨by rw [lp]; simp [hlw, h8], fun cc f hf => ?_⟩
  have hc8 : cc.val < v.y.calls.size := by rw [h8]; exact cc.isLt
  obtain ⟨cd, hcq⟩ : ∃ cd, v.y.calls[cc.val]? = some cd := ⟨_, Array.getElem?_eq_getElem hc8⟩
  have hcl : v.y.calls.toList[cc.val]? = some cd := by rw [Array.getElem?_toList]; exact hcq
  obtain ⟨wg, hwg, hwo⟩ := iw cc.val cd hcl
  have hin : ((v.y.calls.zip wl.toArray).toList.zipIdx)[cc.val]? = some ((cd, wg), cc.val) := by
    simp [Array.toList_zip, List.getElem?_zipIdx, List.getElem?_zip_eq_some, hcl, hwg]
  obtain ⟨b, hb, hjb⟩ := ip cc.val _ hin
  have e : b = f := Option.some.inj (hb.symm.trans hf)
  subst e
  exact joinPart_keyVec' hy S hs hg hrd hl ht hρ Zd hZ hzt hm ha hs0 hpt c T tb L0 w alpha theta
    cc.val cd hcq (hn cc cd hcq) (hfl cc) hwo (hpad cc) hjb

end Lines

#print axioms sig0_ends
#print axioms acc_side
#print axioms ts_side
#print axioms start_whole
#print axioms start_stack
#print axioms parts_of_lines

end OnBytes.Road
