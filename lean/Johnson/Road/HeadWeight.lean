-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadWeight.lean: the output head's one claim on the committed matrix of weights: what
it says of the library's output matrix.

The logits are products of the clamped activations with the output matrix H. The verifier's forms
never name an entry of H. The last token sumcheck of the head's sub-proof ends in two hidden values:
one is read in the cells of the activations, the other is the value of one claim on the committed
matrix W of weights (weightsClaim, OnBytes/Model/Head.lean). The claim names the last unit of the
layout of W and has two factors: on the vocabulary's index a vector AV that is written out, on the
channels' index the equality weights of the sumcheck's challenges over the channels. The library
reads H in W by its own layout (Hof, Inst/Model/Head/Trace.lean). This file shows that the sum which
the claim speaks of is the sum of AV[v] times the channel's weight times the library's H[k][v].

What is compared with what. "Ours" is a definition of these files, neither the verifier's text nor
the library's.
 - facKK_at: the verifier's factor on the channels, weighed by facAt (ours), with the equality
   weight of all its coordinates (eqR, Johnson/Road/FormsKeysEnd.lean: ours, a way of writing the
   library's kernel). eqLow_eqR: the verifier's own table of these weights with eqR.
 - head_unit: the verifier's layout of W with itself: its last unit is the head's.
 - entryW_Hof, units_head: the library with itself.
 - claimVal_head: ours with the library: claimVal (Johnson/Road/FormsKeysWm.lean) is our writing, on
   the verifier's records, of the sum that a claim speaks of; on the right stands the library's Hof.
   It goes through layout_eq and claimVal_Tn_of_layout, which hold for every unit.
 - settle_head, settle_of_run: the verifier with the library: the verifier's own settling of the
   claim on rows and columns (wsGamma, wsRowPart, wsEpsT), summed over the unit's cells, with the
   same sum. These two alone have the verifier's functions on the left without claimVal between.
 - avStep_value, avFold_value, avOf_value: the verifier's loop that fills AV with a closed form.
 - av_loop, weightsClaim_ok: the verifier with itself: what weightsClaim returns.
 - claim_of_run, claim_end, claim_end_lib, claim_end_port: the verifier's weightsClaim, valued by
   our claimVal, with the library's Hof under weights. bLib, the function of a position and a
   channel in which the last two are written, is ours, on the library's record of a request.
 - logits_start_lib: the library with itself (lg, nrm, Req), in bLib.
 - logits_end, logits_start: two identities on sums, no text of either side: what the last token
   sumcheck starts from and what it ends in.

The hypotheses, and where they are met.
 - SizedW s ppref, nine equations between the shape of the weights and the library's reference
   parameters; wsLayOf s true kRef returns. The verifier's public part calls wsLayOf on the shape
   weightShape P y, the switch y.h.p3 and the number P.lkW of the parameter file
   (OnBytes/Model/VerifyPublic.lean). That at the full-size example these meet the nine equations,
   are true and 18, and that the call returns, is a run:
   Johnson/Road/HeadWeightRun.lean [not in this library]. Of what it returns the run holds the
   number of units and the last unit against the layout which the public part hands on, no more;
   that the two are one layout is a theorem (publicH_of_public, Johnson/Road/HeadMade.lean).
 - weightsClaim succeeds; wsClaimShape passes; lamS = 13: runs there, at made-up points.
 - 13 ≤ rs.size, tH.r.size = lt: lengths of what the check draws. The context is a view's, not a dry
   run's. ReqFits: the library's request is the run's (Johnson/Road/HeadLines.lean). SegHas: the
   segment HD0 has one entry for each entry of the vocabulary. None is concluded here.

What is not claimed. W is any function: nothing ties it to a commitment. That the hidden value under
the claim's slot is the claim's sum is the matter of the merge and of the row that is tested on the
committed table: random steps, not looked at. Nothing is a statement on what a verifier's acceptance
shows. The program does not import this file.
-/
import Johnson.Road.HeadLines
import Johnson.Road.FormsKeysFacRs
import Johnson.Road.FormsKeysTnP
import Johnson.Road.FormsKeysFac
import Inst.Model.Head.Trace

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Finset
open OnBytes.Model (Reading eqTab eqLow WsShape WsGrp WsUnit WsLay WsFac WsClaim wsLayOf
  wsClaimShape wsGamma wsRowPart wsEpsT)
open Inst.Model (ppref TClaim entryW)
open Inst.Model.Layout (kRef units uH uEmb layerUnits first place)
open Inst.Model.Head (Hof oH nV nD)

/-! ## The factor on the channels -/

section Factor

variable {K : Type} [Field K] (ρ : Reading K)

/-- An entry of the first b members of an array. -/
theorem getD_cut {α : Type} (z : Array α) {b j : ℕ} (hb : b ≤ z.size) (hj : j < b) (d : α) :
    (z.extract 0 b).getD j d = z.getD j d := by
  have h2 : j < z.size := by omega
  simp [Array.getD, h2, hj]

/-- The factor that weightsClaim makes for the group kk: z coordinates for the low bits of the
index, the highest bit first, and for each of the o values of the rest the equality weight of the
coordinates from z to lamS - 1. rs[v] is the coordinate of bit v. -/
def facKK (rs : Array E) (z o lamS : ℕ) : WsFac :=
  { pt := (Array.range z).map fun i => rs.getD (z - 1 - i) zeroE,
    HV := (eqLow rs z lamS).extract 0 o }

/-- It weighs every index v of its group with the equality weight of all lamS coordinates at v. -/
theorem facKK_at (rs : Array E) (G : WsGrp) (lamS : ℕ) (hE : (G.cls == 'E') = true)
    (hz : G.z ≤ lamS) (hs : lamS ≤ rs.size) (ho : G.o ≤ 2 ^ (lamS - G.z)) (v : ℕ)
    (hv : v < G.o * 2 ^ G.z) :
    facAt ρ (facKK rs G.z G.o lamS) G v = eqR ρ rs 0 lamS v := by
  have hpos : 0 < 2 ^ G.z := by positivity
  have hhi : v / 2 ^ G.z < G.o := by
    rw [Nat.div_lt_iff_lt_mul hpos]
    exact hv
  have hr : v % 2 ^ G.z < 2 ^ G.z := Nat.mod_lt _ hpos
  have hsplit : v = v / 2 ^ G.z * 2 ^ G.z + v % 2 ^ G.z := by
    rw [Nat.mul_comm]
    exact (Nat.div_add_mod v (2 ^ G.z)).symm
  have hlt : v / 2 ^ G.z < 2 ^ (lamS - G.z) := lt_of_lt_of_le hhi ho
  have hsz : (eqLow rs G.z lamS).size = 2 ^ (lamS - G.z) := by
    unfold eqLow
    rw [eqTab_size, rev_size rs hs]
  have hHV : ((eqLow rs G.z lamS).extract 0 G.o).getD (v / 2 ^ G.z) zeroE =
      (eqLow rs G.z lamS).getD (v / 2 ^ G.z) zeroE :=
    getD_cut _ (by rw [hsz]; exact ho) hhi zeroE
  have hmid := eqR_split ρ rs (lo := 0) (mid := G.z) (hi := lamS) (Nat.zero_le _) hz
    (v / 2 ^ G.z) (c' := v % 2 ^ G.z) (by rw [Nat.sub_zero]; exact hr)
  rw [Nat.sub_zero, ← hsplit] at hmid
  rw [hmid]
  unfold facAt
  rw [if_pos hE]
  show ρ.val (((eqLow rs G.z lamS).extract 0 G.o).getD (v / 2 ^ G.z) zeroE) *
    Blocks.eqN G.z 0 (pt ρ ((Array.range G.z).map fun i => rs.getD (G.z - 1 - i) zeroE))
      (v % 2 ^ G.z) = _
  rw [hHV, eqLow_value ρ rs hs hlt]
  congr 1
  unfold eqR
  rw [Nat.sub_zero]
  refine eqN_congr' _ _ (fun j hj => ?_) _
  unfold pt
  rw [Nat.zero_add, getD_map_lt _ _ (by simpa using hj) zeroE 0]
  simp [Array.getD, hj]

end Factor

/-! ## The head's unit -/

/-- What the layout of W asks for the head: kind 13, two digits, the vocabulary's index written out,
the channels' index with its low bits first. It is the last member of allAsks
(Johnson/Road/FormsKeysWLay.lean). -/
def askH (S : WsShape) : AskW := ⟨13, S.L, 2, [WsLay.A_ "x" S.V, WsLay.E_ "kk" S.d false]⟩

/-- The last unit of a layout that the verifier builds is the head's. -/
theorem head_unit {s : WsShape} {p3 : Bool} {lk : ℕ} {lay : WsLay}
    (h : wsLayOf s p3 lk = .ok lay) :
    ∃ o, lay.U[lay.U.size - 1]? = some (unitP lk o (askH (shapeOf s p3))) := by
  obtain ⟨_, h2, _, _⟩ := wsLayOf_units h
  generalize shapeOf s p3 = S at h2 ⊢
  have hlen : lay.U.size = ((List.range S.L).flatMap (layerAsks S)).length + 2 := by
    rw [← Array.length_toList, h2, unitsFrom_length]
    unfold allAsks
    rw [List.length_append]
    rfl
  have ha : (allAsks S)[((List.range S.L).flatMap (layerAsks S)).length + 1]? =
      some (askH S) := by
    unfold allAsks
    rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    rfl
  have e : ((List.range S.L).flatMap (layerAsks S)).length + 2 - 1 =
      ((List.range S.L).flatMap (layerAsks S)).length + 1 := rfl
  refine ⟨0 + (((allAsks S).take (((List.range S.L).flatMap (layerAsks S)).length + 1)).map
    (rowsP lk)).sum, ?_⟩
  rw [hlen, e, ← Array.getElem?_toList, h2]
  exact unitsFrom_get lk _ 0 _ _ ha

/-! ## The library's place of the output matrix -/

/-- The library's list has 384 units of the layers. -/
theorem units_layers : ((List.range ppref.layers).flatMap (layerUnits ppref)).length = 384 := by
  have h := Inst.Model.Head.first_layers
  rw [List.length_flatMap]
  have e : first ppref ppref.layers =
      ((List.range ppref.layers).map fun L' => (layerUnits ppref L').length).sum := rfl
  rw [e] at h
  omega

/-- The library's list has 386 units, and the last is the output matrix. -/
theorem units_head : (units ppref).length = 386 ∧ (units ppref)[385]? = some (uH ppref) := by
  have hl := units_layers
  constructor
  · unfold units
    rw [List.length_append, hl]
    rfl
  · unfold units
    rw [List.getElem?_append_right (le_of_eq_of_le hl (by decide)), hl]
    rfl

/-- The entry (v, k) of the library's unit "output matrix" in a matrix W is the library's H[k][v].
-/
theorem entryW_Hof {K : Type} [CommRing K] (W : ℕ → ℕ → K) (v k : ℕ) :
    entryW ppref kRef W 385 (uH ppref) [v, k] = Hof W k v := by
  have h2 : (uH ppref).nU = 2 := rfl
  have hp : ∀ jj,
      place kRef (units ppref) 385 (uH ppref) jj [v, k] = (oH + (5120 * jj + k), v) := by
    intro jj
    simp only [place, Inst.Model.Head.oH_eq, Inst.Model.Head.bits_uH]
    simp [uH, Inst.Model.Layout.row, Inst.Model.Layout.col, Inst.Model.Layout.split,
      Inst.Model.Layout.lOf, ppref]
    omega
  unfold entryW
  simp only [h2, Finset.sum_range_succ, Finset.sum_range_zero, hp, pow_zero, pow_one, one_mul,
    zero_add, Hof, Nat.mul_zero, Nat.mul_one, Nat.add_assoc]

/-! ## What the claim says of the library's output matrix -/

section Claim

variable {K : Type} [Field K] (ρ : Reading K)

/-- The low bits and the odd part of 5,120. -/
theorem kk_5120 : (WsLay.E_ "kk" 5120 false).z = 10 ∧ (WsLay.E_ "kk" 5120 false).o = 5 :=
  ⟨rfl, rfl⟩

/-- **The sum that the head's claim speaks of.** For a shape of the weights that agrees with the
library's reference parameters, a layout that wsLayOf returns with the library's number of column
bits, any matrix W, any vector AV and any coordinates rs, 13 of which are used: the claim on the
last unit with the factors AV and facKK says: the sum over the vocabulary and the channels of AV[v]
times the equality weight of the 13 coordinates at k times the library's H[k][v], read in the same
W. -/
theorem claimVal_head {s : WsShape} (Z : SizedW s ppref) {lay : WsLay}
    (h : wsLayOf s true kRef = .ok lay) (W : Wm K) (AV rs : Array E) (hs : 13 ≤ rs.size) :
    claimVal ρ lay W { ui := lay.U.size - 1, f := [{ AV := AV }, facKK rs 10 5 13] } =
      ∑ v ∈ range nV, ∑ k ∈ range nD,
        ρ.val (AV.getD v zeroE) * eqR ρ rs 0 13 k * Hof W k v := by
  obtain ⟨-, hsz, -, -⟩ := layout_eq Z h
  have hsz' : lay.U.size = 386 := hsz.trans units_head.1
  obtain ⟨o, hu⟩ := head_unit h
  have hd : (shapeOf s true).d = 5120 := Z.d
  have e385 : lay.U.size - 1 = 385 := by omega
  rw [e385] at hu ⊢
  rw [claimVal_Tn_of_layout ρ Z h W (c := { ui := 385, f := [{ AV := AV }, facKK rs 10 5 13] })
    (U := uH ppref) units_head.2
    (fs := [fun v => ρ.val (AV.getD v zeroE), fun k => eqR ρ rs 0 13 k]) ?_]
  · rw [TClaim.Tn_two ppref kRef W 385 (uH ppref) ⟨ppref.V, .whole⟩ ⟨ppref.d, .low⟩ rfl]
    exact sum_congr rfl fun v _ => sum_congr rfl fun k _ => by rw [entryW_Hof]
  · intro u hu'
    have hu'' : lay.U[385]? = some u := hu'
    rw [hu] at hu''
    have e := (Option.some.inj hu'').symm
    subst e
    refine ⟨rfl, ?_⟩
    unfold askH
    rw [hd]
    refine List.Forall₂.cons (fun v _ => rfl)
      (List.Forall₂.cons (fun v hv => ?_) List.Forall₂.nil)
    have hv' : v < 5 * 2 ^ 10 := hv
    exact facKK_at ρ rs _ 13 rfl (show 10 ≤ 13 by decide) hs (show 5 ≤ 2 ^ (13 - 10) by decide) v
      hv'

/-- The verifier's own settling of the head's claim on the rows and the columns of W, summed over
the unit's cells, is the two scalars times that sum. -/
theorem settle_head (hρ : Numerals ρ) {s : WsShape} (Z : SizedW s ppref) {lay : WsLay}
    (h : wsLayOf s true kRef = .ok lay) (W : Wm K) (AV rs : Array E) (hs : 13 ≤ rs.size)
    {u : WsUnit} (hu : lay.U[lay.U.size - 1]? = some u)
    (hsh : wsClaimShape lay { ui := lay.U.size - 1, f := [{ AV := AV }, facKK rs 10 5 13] } =
      .ok ()) (ka wgt : E) :
    ∑ C ∈ range (2 ^ lay.lk), ∑ y ∈ range u.rows,
      ρ.val ((wsGamma u (wsRowPart lay
        { ui := lay.U.size - 1, f := [{ AV := AV }, facKK rs 10 5 13] } ka) wgt).getD y zeroE) *
        ρ.val (wsEpsT lay { ui := lay.U.size - 1, f := [{ AV := AV }, facKK rs 10 5 13] }
          (bitsOf lay.lk C)) * W (u.off + y) C =
      ρ.val wgt * ρ.val ka * ∑ v ∈ range nV, ∑ k ∈ range nD,
        ρ.val (AV.getD v zeroE) * eqR ρ rs 0 13 k * Hof W k v := by
  rw [claim_cells_layout hρ h hu hsh W ka wgt, claimVal_head ρ Z h W AV rs hs]

end Claim

/-! ## The factor on the vocabulary -/

section Vocabulary

variable {K : Type} [Field K] (ρ : Reading K)

/-- One step of the loop that fills AV: at a covered position t the entry of the checked token grows
by wx times the position's weight. -/
def avStep (on : Array Bool) (win : Array ℕ) (wx : E) (eH : Array E) (AV : Array E) (t : ℕ) :
    Array E :=
  if on.getD t false = true then
    AV.modify (win.getD t 0) fun a => addE a (mulE wx (eH.getD t zeroE))
  else AV

/-- A step keeps the length. -/
theorem avStep_size (on : Array Bool) (win : Array ℕ) (wx : E) (eH AV : Array E) (t : ℕ) :
    (avStep on win wx eH AV t).size = AV.size := by
  unfold avStep
  split
  · exact Array.size_modify
  · rfl

/-- The entry that a change of one entry changes. -/
theorem getD_modify_self {α : Type} (A : Array α) (f : α → α) {v : ℕ} (hv : v < A.size) (d : α) :
    (A.modify v f).getD v d = f (A.getD v d) := by
  simp [Array.getD, Array.getElem_modify, hv]

/-- Another entry. -/
theorem getD_modify_ne {α : Type} (A : Array α) (f : α → α) {w v : ℕ} (h : ¬ w = v)
    (hv : v < A.size) (d : α) : (A.modify w f).getD v d = A.getD v d := by
  simp [Array.getD, Array.getElem_modify, hv, h]

/-- What a step does to an entry. -/
theorem avStep_value (on : Array Bool) (win : Array ℕ) (wx : E) (eH AV : Array E) (t : ℕ) {v : ℕ}
    (hv : v < AV.size) :
    ρ.val ((avStep on win wx eH AV t).getD v zeroE) = ρ.val (AV.getD v zeroE) +
      if on.getD t false = true ∧ win.getD t 0 = v then ρ.val wx * ρ.val (eH.getD t zeroE)
      else 0 := by
  unfold avStep
  by_cases h1 : on.getD t false = true
  · rw [if_pos h1]
    by_cases h2 : win.getD t 0 = v
    · rw [if_pos ⟨h1, h2⟩, h2]
      rw [getD_modify_self AV _ hv, ρ.add, ρ.mul]
    · rw [if_neg (fun h => h2 h.2), add_zero]
      rw [getD_modify_ne AV _ h2 hv]
  · rw [if_neg h1, if_neg (fun h => h1 h.1), add_zero]

/-- The vector AV after the steps of the first n positions, from the vector A0 on. -/
def avFold (on : Array Bool) (win : Array ℕ) (wx : E) (eH A0 : Array E) (n : ℕ) : Array E :=
  (List.range n).foldl (avStep on win wx eH) A0

/-- Its length, and its entries in closed form. -/
theorem avFold_value (on : Array Bool) (win : Array ℕ) (wx : E) (eH A0 : Array E) {v : ℕ}
    (hv : v < A0.size) : ∀ n : ℕ, (avFold on win wx eH A0 n).size = A0.size ∧
    ρ.val ((avFold on win wx eH A0 n).getD v zeroE) = ρ.val (A0.getD v zeroE) +
      ∑ t ∈ range n, if on.getD t false = true ∧ win.getD t 0 = v then
        ρ.val wx * ρ.val (eH.getD t zeroE) else 0
  | 0 => ⟨rfl, by simp [avFold]⟩
  | n + 1 => by
    obtain ⟨i1, i2⟩ := avFold_value on win wx eH A0 hv n
    have e : avFold on win wx eH A0 (n + 1) =
        avStep on win wx eH (avFold on win wx eH A0 n) n := by
      unfold avFold
      rw [List.range_succ, List.foldl_append]
      rfl
    rw [e]
    refine ⟨(avStep_size _ _ _ _ _ _).trans i1, ?_⟩
    rw [avStep_value ρ on win wx eH _ n (by rw [i1]; exact hv), i2, Finset.sum_range_succ,
      add_assoc]

end Vocabulary

/-! ## Two identities on sums -/

section Sums

variable {K : Type} [Field K]

/-- **What the last token sumcheck ends in.** T positions, V entries of the vocabulary, d channels.
on t says whether position t is covered, win t is its checked token, below V. eH t is the weight of
position t, e k that of channel k, ew v that of entry v, wx any scalar. Let B t k be
wx H[k][win t] minus the sum of ew v H[k][v] at a covered position, and 0 elsewhere. The sum of
eH t e k B t k over positions and channels is the sum over the vocabulary and the channels of
(wx psi v - sR ew v) e k H[k][v], where psi v adds up eH over the covered positions with the checked
token v, and sR over all covered positions. -/
theorem logits_end (T V d : ℕ) (on : ℕ → Prop) [DecidablePred on] (win : ℕ → ℕ)
    (hw : ∀ t, t < T → on t → win t < V) (eH e ew : ℕ → K) (wx : K) (H : ℕ → ℕ → K) :
    ∑ t ∈ range T, ∑ k ∈ range d, eH t * e k *
        (if on t then wx * H k (win t) - ∑ v ∈ range V, ew v * H k v else 0) =
      ∑ v ∈ range V, ∑ k ∈ range d,
        (wx * (∑ t ∈ range T, if on t ∧ win t = v then eH t else 0) -
          (∑ t ∈ range T, if on t then eH t else 0) * ew v) * e k * H k v := by
  have hpsi : ∀ k, ∑ v ∈ range V, (∑ t ∈ range T, if on t ∧ win t = v then eH t else 0) * H k v =
      ∑ t ∈ range T, if on t then eH t * H k (win t) else 0 := by
    intro k
    simp only [sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun t ht => ?_
    by_cases h1 : on t
    · rw [if_pos h1]
      rw [sum_eq_single (win t)]
      · rw [if_pos ⟨h1, rfl⟩]
      · intro v _ hne
        rw [if_neg (fun h => hne h.2.symm), zero_mul]
      · intro hn
        exact absurd (mem_range.mpr (hw t (mem_range.mp ht) h1)) hn
    · rw [if_neg h1]
      exact sum_eq_zero fun v _ => by rw [if_neg (fun h => h1 h.1), zero_mul]
  have hR : ∀ k, ∑ v ∈ range V,
      (wx * (∑ t ∈ range T, if on t ∧ win t = v then eH t else 0) -
        (∑ t ∈ range T, if on t then eH t else 0) * ew v) * e k * H k v =
      e k * (wx * (∑ t ∈ range T, if on t then eH t * H k (win t) else 0) -
        (∑ t ∈ range T, if on t then eH t else 0) * ∑ v ∈ range V, ew v * H k v) := by
    intro k
    rw [← hpsi k, mul_sum, mul_sum, ← sum_sub_distrib, mul_sum]
    exact sum_congr rfl fun v _ => by ring
  rw [sum_comm, sum_comm (s := range V)]
  refine sum_congr rfl fun k _ => ?_
  rw [hR k]
  generalize (∑ v ∈ range V, ew v * H k v) = S
  rw [mul_sum, sum_mul, ← sum_sub_distrib, mul_sum]
  refine sum_congr rfl fun t _ => ?_
  by_cases h1 : on t
  · simp only [if_pos h1]
    ring
  · simp only [if_neg h1]
    ring

/-- **What the last token sumcheck starts from.** a i is the weight of position i, nrm k i the
activation of channel k there, lg i v the logit, the sum of nrm k i H[k][v] over the channels. The
weighted sum over the vocabulary and the covered positions of lg i (win i) - lg i v is the sum over
positions and channels of a i nrm k i B i k, with B as in logits_end at wx the sum of the weights
ew. -/
theorem logits_start (T V d : ℕ) (on : ℕ → Prop) [DecidablePred on] (win : ℕ → ℕ)
    (a ew : ℕ → K) (nrm H : ℕ → ℕ → K) :
    ∑ v ∈ range V, ew v * ∑ i ∈ range T, a i *
        (if on i then (∑ k ∈ range d, nrm k i * H k (win i)) - ∑ k ∈ range d, nrm k i * H k v
          else 0) =
      ∑ i ∈ range T, ∑ k ∈ range d, a i * nrm k i *
        (if on i then (∑ v ∈ range V, ew v) * H k (win i) - ∑ v ∈ range V, ew v * H k v
          else 0) := by
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  by_cases h1 : on i
  · simp only [if_pos h1]
    have e1 : ∀ v, ew v * (a i * ((∑ k ∈ range d, nrm k i * H k (win i)) -
        ∑ k ∈ range d, nrm k i * H k v)) =
        ∑ k ∈ range d, a i * nrm k i * (ew v * H k (win i) - ew v * H k v) := by
      intro v
      rw [← sum_sub_distrib, mul_sum, mul_sum]
      exact sum_congr rfl fun k _ => by ring
    simp only [e1]
    rw [sum_comm]
    refine sum_congr rfl fun k _ => ?_
    rw [← mul_sum, sum_sub_distrib, sum_mul]
  · simp only [if_neg h1, mul_zero, sum_const_zero]

end Sums

/-! ## What weightsClaim returns -/

section Returns

open OnBytes.Model (Fork SubM)
open OnBytes.Model.Head (weightsClaim ewOf wxOf onSum)

/-- A routine under a condition that holds. -/
theorem ok_ite_pos {α : Type} {c : Prop} [Decidable c] {a b : SubM α} (hc : c) {F G : Fork}
    {C D : Ctx} {x : α} (h : Ok (if c then a else b) F C x G D) : Ok a F C x G D := by
  rw [if_pos hc] at h
  exact h

/-- A routine under a condition that fails. -/
theorem ok_ite_neg {α : Type} {c : Prop} [Decidable c] {a b : SubM α} (hc : ¬ c) {F G : Fork}
    {C D : Ctx} {x : α} (h : Ok (if c then a else b) F C x G D) : Ok b F C x G D := by
  rw [if_neg hc] at h
  exact h

/-- A condition on values that goes on leaves the context, and it holds unless the run is dry. -/
theorem testAs_ok {n : String} {b : Bool} {C D : Ctx} {u : Unit}
    (h : Model.testAs n b C = .ok (u, D)) : D = C ∧ (b = true ∨ C.ch.dry = true) := by
  have e : Model.testAs n b C =
      (if (b || C.ch.dry) = true then (pure () : Blk Unit) else Model.refuse n) C := rfl
  rw [e] at h
  by_cases hc : (b || C.ch.dry) = true
  · rw [if_pos hc] at h
    have h' : (Except.ok ((), C) : Except Failure (Unit × Ctx)) = .ok (u, D) := h
    cases h'
    exact ⟨rfl, by simpa using hc⟩
  · rw [if_neg hc] at h
    have h' : (Except.error { name := n } : Except Failure (Unit × Ctx)) = .ok (u, D) := h
    cases h'

/-- One more position. -/
theorem avFold_succ (on : Array Bool) (win : Array ℕ) (wx : E) (eH A0 : Array E) (n : ℕ) :
    avFold on win wx eH A0 (n + 1) = avStep on win wx eH (avFold on win wx eH A0 n) n := by
  unfold avFold
  rw [List.range_succ, List.foldl_append]
  rfl

/-- The vector AV that weightsClaim fills, from the weights ew of the entries of the segment HD0:
it starts from - sR ew[v] and takes the steps of all T positions. -/
def avOf (R : Model.Head.Run) (ew : Array E) : Array E :=
  avFold R.cov.hOn R.x.win (wxOf R ew) (eqTab R.x.tH.r)
    ((Array.range R.h.V).map fun v => subE zeroE (mulE (onSum R R.x.tH.r) (ew.getD v zeroE))) R.h.T

/-- The loop that fills AV, as weightsClaim runs it: it leaves state and context, it returns the
vector after the steps of all T positions, and on a view, not in a dry run, the checked token of
every covered position is an entry of the vocabulary. -/
theorem av_loop (R : Model.Head.Run) (wx : E) (eH A0 : Array E) {F G : Fork} {C D : Ctx}
    {AV : Array E}
    (h : Ok (forIn [:R.h.T] A0 fun t (A : Array E) =>
      if R.cov.hOn.getD t false = true then
        (liftM (Model.testAs "header-y" (decide (R.x.win.getD t 0 < R.h.V))) : SubM Unit) >>=
          fun _ => (pure PUnit.unit : SubM PUnit) >>= fun _ =>
            pure (ForInStep.yield
              (A.modify (R.x.win.getD t 0) fun a => addE a (mulE wx (eH.getD t zeroE))))
      else (pure PUnit.unit : SubM PUnit) >>= fun _ => pure (ForInStep.yield A)) F C AV G D) :
    G = F ∧ D = C ∧ AV = avFold R.cov.hOn R.x.win wx eH A0 R.h.T ∧
      (C.ch.dry = false → ∀ t, t < R.h.T → R.cov.hOn.getD t false = true →
        R.x.win.getD t 0 < R.h.V) := by
  refine ok_forIn_range R.h.T _
    (fun t A F' C' => F' = F ∧ C' = C ∧ A = avFold R.cov.hOn R.x.win wx eH A0 t ∧
      (C.ch.dry = false → ∀ t', t' < t → R.cov.hOn.getD t' false = true →
        R.x.win.getD t' 0 < R.h.V))
    ?_ ⟨rfl, rfl, rfl, fun _ t' ht' => absurd ht' (Nat.not_lt_zero t')⟩ h
  rintro t A F' C' r' F'' C'' - ⟨e1, e2, e3, hw⟩ hr
  by_cases hon : R.cov.hOn.getD t false = true
  · have hr := ok_ite_pos hon hr
    obtain ⟨ua, Fa, Ca, ka, hr⟩ := (ok_bind _ _ _ _ _ _ _).mp hr
    obtain ⟨ja, ea⟩ := (ok_lift _ _ _ _ _ _).mp ka
    obtain ⟨eb, hv⟩ := testAs_ok ja
    obtain ⟨ub, Fb, Cb, kb, hr⟩ := (ok_bind _ _ _ _ _ _ _).mp hr
    obtain ⟨-, ec, ed⟩ := (ok_pure _ _ _ _ _ _).mp kb
    obtain ⟨ee, ef, eg⟩ := (ok_pure _ _ _ _ _ _).mp hr
    refine ⟨_, ee, by rw [ef, ec, ea, e1], by rw [eg, ed, eb, e2], ?_, ?_⟩
    · rw [avFold_succ, ← e3]
      unfold avStep
      rw [if_pos hon]
    · intro hd t' ht' hon'
      rcases Nat.lt_succ_iff_lt_or_eq.mp ht' with h1 | h1
      · exact hw hd t' h1 hon'
      · rw [h1]
        rcases hv with h2 | h2
        · exact of_decide_eq_true h2
        · rw [e2, hd] at h2
          cases h2
  · have hr := ok_ite_neg hon hr
    obtain ⟨ub, Fb, Cb, kb, hr⟩ := (ok_bind _ _ _ _ _ _ _).mp hr
    obtain ⟨-, ec, ed⟩ := (ok_pure _ _ _ _ _ _).mp kb
    obtain ⟨ee, ef, eg⟩ := (ok_pure _ _ _ _ _ _).mp hr
    refine ⟨_, ee, by rw [ef, ec, e1], by rw [eg, ed, e2], ?_, ?_⟩
    · rw [avFold_succ, ← e3]
      unfold avStep
      rw [if_neg hon]
    · intro hd t' ht' hon'
      rcases Nat.lt_succ_iff_lt_or_eq.mp ht' with h1 | h1
      · exact hw hd t' h1 hon'
      · rw [h1] at hon'
        exact absurd hon' hon

/-- **What weightsClaim returns**, if the last unit of the layout has two groups with the names x
and kk: the claim on the last unit with the factors avOf and facKK. State and context are left as
they were. On a view, not in a dry run, the checked token of every covered position is an entry of
the vocabulary. -/
theorem weightsClaim_ok {R : Model.Head.Run} {lay : WsLay} {F G : Fork} {C D : Ctx} {cl : WsClaim}
    (hk : Ok (weightsClaim R lay) F C cl G D) {gx gk : WsGrp}
    (hg : (lay.U.getD (lay.U.size - 1) default).g = [gx, gk]) (hx : gx.name = "x")
    (hkk : gk.name = "kk") :
    G = F ∧ D = C ∧ ∃ ew, Ok (ewOf R "HD0") F C ew F C ∧
      cl = { ui := lay.U.size - 1,
             f := [{ AV := avOf R ew }, facKK R.x.rs gk.z gk.o R.hp.lamS] } ∧
      (C.ch.dry = false → ∀ t, t < R.h.T → R.cov.hOn.getD t false = true →
        R.x.win.getD t 0 < R.h.V) := by
  have hxb : (gx.name == "x") = true := by
    rw [hx]
    rfl
  have hkx : ¬ (gk.name == "x") = true := by
    rw [hkk]
    decide
  have hkb : (gk.name == "kk") = true := by
    rw [hkk]
    rfl
  unfold Model.Head.weightsClaim at hk
  obtain ⟨ew, F1, C1, k1, hk1⟩ := (ok_bind _ _ _ _ _ _ _).mp hk
  clear hk
  obtain ⟨rfl, rfl, -⟩ := ok_ewOf k1
  obtain ⟨u2, F2, C2, k2, hk2⟩ := (ok_bind _ _ _ _ _ _ _).mp hk1
  clear hk1
  obtain ⟨j2, rfl⟩ := (ok_lift _ _ _ _ _ _).mp k2
  obtain ⟨-, rfl⟩ := (mustAs_ok _ _ _ _ _).mp j2
  clear k2 j2
  obtain ⟨r, F3, C3, q3, hk3⟩ := (ok_bind _ _ _ _ _ _ _).mp hk2
  clear hk2
  obtain ⟨rfl, rfl, rfl⟩ := (ok_pure _ _ _ _ _ _).mp hk3
  clear hk3
  rw [hg, List.forIn_cons] at q3
  obtain ⟨s1, F4, C4, k4, q4⟩ := (ok_bind _ _ _ _ _ _ _).mp q3
  clear q3
  have k5 := ok_ite_pos hxb k4
  clear k4
  obtain ⟨AVr, F5, C5, k6, k7⟩ := (ok_bind _ _ _ _ _ _ _).mp k5
  clear k5
  obtain ⟨rfl, rfl, rfl, hwin⟩ := av_loop R _ _ _ k6
  clear k6
  obtain ⟨uc, Fc, Cc, kc, k8⟩ := (ok_bind _ _ _ _ _ _ _).mp k7
  clear k7
  obtain ⟨-, rfl, rfl⟩ := (ok_pure _ _ _ _ _ _).mp kc
  clear kc
  obtain ⟨rfl, rfl, rfl⟩ := (ok_pure _ _ _ _ _ _).mp k8
  clear k8
  have q5 : Ok (forIn [gk] ([] ++ [({ AV := avOf R ew } : WsFac)]) _) _ _ _ _ _ := q4
  clear q4
  rw [List.forIn_cons] at q5
  obtain ⟨s2, F6, C6, k9, q6⟩ := (ok_bind _ _ _ _ _ _ _).mp q5
  clear q5
  have k10 := ok_ite_pos hkb (ok_ite_neg hkx k9)
  clear k9
  obtain ⟨ud, Fd, Cd, kd, k11⟩ := (ok_bind _ _ _ _ _ _ _).mp k10
  clear k10
  obtain ⟨-, rfl, rfl⟩ := (ok_pure _ _ _ _ _ _).mp kd
  clear kd
  obtain ⟨rfl, rfl, rfl⟩ := (ok_pure _ _ _ _ _ _).mp k11
  clear k11
  have q7 : Ok (pure (([] ++ [({ AV := avOf R ew } : WsFac)]) ++
      [facKK R.x.rs gk.z gk.o R.hp.lamS]) : SubM (List WsFac)) _ _ _ _ _ := q6
  clear q6
  obtain ⟨rfl, rfl, rfl⟩ := (ok_pure _ _ _ _ _ _).mp q7
  exact ⟨rfl, rfl, ew, k1, rfl, hwin⟩

end Returns

/-! ## The claim of a run, on the library's output matrix -/

section Whole

open OnBytes.Model (Fork)
open OnBytes.Model.Head (weightsClaim ewOf wxOf onSum)

variable {K : Type} [Field K] (ρ : Reading K)

/-- An entry of avOf, in closed form: wx psi[v] - sR ew[v]. -/
theorem avOf_value (R : Model.Head.Run) (ew : Array E) {v : ℕ} (hv : v < R.h.V) :
    ρ.val ((avOf R ew).getD v zeroE) =
      ρ.val (wxOf R ew) * (∑ t ∈ range R.h.T,
        if R.cov.hOn.getD t false = true ∧ R.x.win.getD t 0 = v then
          ρ.val ((eqTab R.x.tH.r).getD t zeroE) else 0) -
      ρ.val (onSum R R.x.tH.r) * ρ.val (ew.getD v zeroE) := by
  have hsz : v < ((Array.range R.h.V).map fun v =>
      subE zeroE (mulE (onSum R R.x.tH.r) (ew.getD v zeroE))).size := by simpa using hv
  unfold avOf
  rw [(avFold_value ρ _ _ _ _ _ hsz R.h.T).2, getD_map_lt _ _ (by simpa using hv) zeroE 0, ρ.sub,
    ρ.zero, ρ.mul, mul_sum]
  have e0 : (Array.range R.h.V).getD v 0 = v := by simp [Array.getD, hv]
  rw [e0]
  have e1 : ∀ t, (if R.cov.hOn.getD t false = true ∧ R.x.win.getD t 0 = v then
      ρ.val (wxOf R ew) * ρ.val ((eqTab R.x.tH.r).getD t zeroE) else 0) =
      ρ.val (wxOf R ew) * (if R.cov.hOn.getD t false = true ∧ R.x.win.getD t 0 = v then
        ρ.val ((eqTab R.x.tH.r).getD t zeroE) else 0) := by
    intro t
    split
    · rfl
    · rw [mul_zero]
  simp only [e1]
  ring

/-- **The claim of a run of the head's check, on the library's output matrix.** For a shape of the
weights that agrees with the library's reference parameters and a layout that wsLayOf returns with
the library's number of column bits: if weightsClaim succeeds, with 13 rounds over the channels and
as many challenges, the sum that its claim speaks of, in any matrix W, is the sum over the
vocabulary and the channels of avOf's entry times the equality weight of the 13 challenges at the
channel times the library's H[k][v], read in the same W. -/
theorem claim_of_run {s : WsShape} (Z : SizedW s ppref) {lay : WsLay}
    (h : wsLayOf s true kRef = .ok lay) {R : Model.Head.Run} {F G : Fork} {C D : Ctx}
    {cl : WsClaim} (hk : Ok (weightsClaim R lay) F C cl G D) (hlam : R.hp.lamS = 13)
    (hs : 13 ≤ R.x.rs.size) (W : Wm K) :
    ∃ ew, Ok (ewOf R "HD0") F C ew F C ∧
      (C.ch.dry = false → ∀ t, t < R.h.T → R.cov.hOn.getD t false = true →
        R.x.win.getD t 0 < R.h.V) ∧
      claimVal ρ lay W cl = ∑ v ∈ range nV, ∑ k ∈ range nD,
        ρ.val ((avOf R ew).getD v zeroE) * eqR ρ R.x.rs 0 13 k * Hof W k v := by
  obtain ⟨o, hu⟩ := head_unit h
  have hd : (shapeOf s true).d = 5120 := Z.d
  have hg : (lay.U.getD (lay.U.size - 1) default).g =
      placeP [WsLay.A_ "x" (shapeOf s true).V, WsLay.E_ "kk" 5120 false] kRef 0 := by
    rw [getD_of_some hu default]
    unfold askH
    rw [hd]
    rfl
  obtain ⟨-, -, ew, hew, hcl, hwin⟩ := weightsClaim_ok hk hg rfl rfl
  refine ⟨ew, hew, hwin, ?_⟩
  rw [hcl, hlam]
  exact claimVal_head ρ Z h W (avOf R ew) R.x.rs hs

/-- **The claim's sum is what the last token sumcheck ends in.** Under the hypotheses of
claim_of_run, on a view and with the library's vocabulary: the sum that the claim speaks of is the
sum over the positions t and the channels k of the equality weight of the sumcheck's challenges over
the positions at t, times that of its challenges over the channels at k, times B t k: at a covered
position wx H[k][win t] minus the sum of ew[v] H[k][v], and 0 elsewhere; with H the library's output
matrix, read in W. -/
theorem claim_end {s : WsShape} (Z : SizedW s ppref) {lay : WsLay}
    (h : wsLayOf s true kRef = .ok lay) {R : Model.Head.Run} {F G : Fork} {C D : Ctx}
    {cl : WsClaim} (hk : Ok (weightsClaim R lay) F C cl G D) (hlam : R.hp.lamS = 13)
    (hs : 13 ≤ R.x.rs.size) (hV : R.h.V = nV) (hdry : C.ch.dry = false) (W : Wm K) :
    ∃ ew, Ok (ewOf R "HD0") F C ew F C ∧
      claimVal ρ lay W cl = ∑ t ∈ range R.h.T, ∑ k ∈ range nD,
        ρ.val ((eqTab R.x.tH.r).getD t zeroE) * eqR ρ R.x.rs 0 13 k *
          (if R.cov.hOn.getD t false = true then
            ρ.val (wxOf R ew) * Hof W k (R.x.win.getD t 0) -
              ∑ v ∈ range nV, ρ.val (ew.getD v zeroE) * Hof W k v
          else 0) := by
  obtain ⟨ew, hew, hwin, hval⟩ := claim_of_run ρ Z h hk hlam hs W
  refine ⟨ew, hew, ?_⟩
  have hw : ∀ t, t < R.h.T → R.cov.hOn.getD t false = true → R.x.win.getD t 0 < nV := by
    intro t ht hon
    rw [← hV]
    exact hwin hdry t ht hon
  have hsR : ρ.val (onSum R R.x.tH.r) = ∑ t ∈ range R.h.T,
      if R.cov.hOn.getD t false = true then ρ.val ((eqTab R.x.tH.r).getD t zeroE) else 0 :=
    foldl_on ρ (fun t => R.cov.hOn.getD t false) (eqTab R.x.tH.r) R.h.T
  rw [hval, logits_end R.h.T nV nD (fun t => R.cov.hOn.getD t false = true)
    (fun t => R.x.win.getD t 0) hw (fun t => ρ.val ((eqTab R.x.tH.r).getD t zeroE))
    (fun k => eqR ρ R.x.rs 0 13 k) (fun v => ρ.val (ew.getD v zeroE)) (ρ.val (wxOf R ew)) (Hof W)]
  refine sum_congr rfl fun v hv => sum_congr rfl fun k _ => ?_
  rw [avOf_value ρ R ew (by rw [hV]; exact mem_range.mp hv), hsR]

/-- The verifier's own settling of the claim of a run on the rows and the columns of W, summed over
the unit's cells, is the two scalars times the sum of claim_of_run. Asked beside: the verifier's
test wsClaimShape passes on the claim; by the text of wsForkEnd (OnBytes/Model/Merge.lean) the
verifier makes that test of every claim that it settles. -/
theorem settle_of_run (hρ : Numerals ρ) {s : WsShape} (Z : SizedW s ppref) {lay : WsLay}
    (h : wsLayOf s true kRef = .ok lay) {R : Model.Head.Run} {F G : Fork} {C D : Ctx}
    {cl : WsClaim} (hk : Ok (weightsClaim R lay) F C cl G D) (hlam : R.hp.lamS = 13)
    (hs : 13 ≤ R.x.rs.size) (W : Wm K) {u : WsUnit} (hu : lay.U[cl.ui]? = some u)
    (hsh : wsClaimShape lay cl = .ok ()) (ka wgt : E) :
    ∃ ew, Ok (ewOf R "HD0") F C ew F C ∧
      ∑ c ∈ range (2 ^ lay.lk), ∑ y ∈ range u.rows,
        ρ.val ((wsGamma u (wsRowPart lay cl ka) wgt).getD y zeroE) *
          ρ.val (wsEpsT lay cl (bitsOf lay.lk c)) * W (u.off + y) c =
        ρ.val wgt * ρ.val ka * ∑ v ∈ range nV, ∑ k ∈ range nD,
          ρ.val ((avOf R ew).getD v zeroE) * eqR ρ R.x.rs 0 13 k * Hof W k v := by
  obtain ⟨ew, hew, -, hval⟩ := claim_of_run ρ Z h hk hlam hs W
  exact ⟨ew, hew, by rw [claim_cells_layout hρ h hu hsh W ka wgt, hval]⟩

/-- B of a position and a channel, in the library's letters: the indicator of the covered positions
times (wx H[k][w_i] minus the sum of ew[v] H[k][v] over the vocabulary), w_i the token that is
checked at position i. -/
def bLib (y : Inst.Model.Head.Req) (wx : K) (ew : ℕ → K) (H : ℕ → ℕ → K) (i k : ℕ) : K :=
  ((y.rho i : ℤ) : K) * (wx * H k (y.win i) - ∑ v ∈ range nV, ew v * H k v)

/-- **The start, in the library's names.** The part of the keys of the family HD0 that is not affine
in the cells, under the weights ew of the entries and at the point u of the positions, is the
extension at u of the sum over the channels of the library's clamped activation times bLib, with wx
the sum of the weights. lg and nrm are the library's (Inst/Model/Head/Trace.lean). -/
theorem logits_start_lib (t : Inst.Model.Head.Cells K) (H : ℕ → ℕ → K) (y : Inst.Model.Head.Req)
    (ew : ℕ → K) (lt : ℕ) (u : ℕ → K) :
    wsum ew lt u nV (fun x i => ((y.rho i : ℤ) : K) *
        (Inst.Model.Head.lg t H i (y.win i) - Inst.Model.Head.lg t H i x)) =
      Blocks.ext lt (fun i => ∑ k ∈ range nD,
        Inst.Model.Head.nrm t k i * bLib y (∑ v ∈ range nV, ew v) ew H i k) u := by
  unfold wsum Blocks.ext bLib Inst.Model.Head.lg
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  have e1 : ∀ v, ew v * (Blocks.eqN lt 0 u i * (((y.rho i : ℤ) : K) *
      ((∑ j ∈ range nD, Inst.Model.Head.nrm t j i * H j (y.win i)) -
        ∑ j ∈ range nD, Inst.Model.Head.nrm t j i * H j v))) =
      ∑ j ∈ range nD, Blocks.eqN lt 0 u i * (Inst.Model.Head.nrm t j i *
        (((y.rho i : ℤ) : K) * (ew v * H j (y.win i) - ew v * H j v))) := by
    intro v
    rw [← sum_sub_distrib, mul_sum, mul_sum, mul_sum]
    exact sum_congr rfl fun j _ => by ring
  simp only [e1]
  rw [sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [← mul_sum, ← mul_sum, ← mul_sum, sum_sub_distrib, sum_mul]

/-- **The end, in the library's names.** Under the hypotheses of claim_end, for a request y of the
library that is the run's request (ReqFits, Johnson/Road/HeadLines.lean), 1,024 positions and as
many challenges over the positions as a position has bits: the sum that the claim speaks of is the
extension, at these challenges, of the sum over the channels of the equality weight of the
challenges over the channels times bLib, with H the library's output matrix read in W. -/
theorem claim_end_lib {s : WsShape} (Z : SizedW s ppref) {lay : WsLay}
    (h : wsLayOf s true kRef = .ok lay) {R : Model.Head.Run} {F G : Fork} {C D : Ctx}
    {cl : WsClaim} (hk : Ok (weightsClaim R lay) F C cl G D) (hlam : R.hp.lamS = 13)
    (hs : 13 ≤ R.x.rs.size) (hV : R.h.V = nV) (hdry : C.ch.dry = false) (W : Wm K)
    {y : Inst.Model.Head.Req} (Y : ReqFits R HeadSizes.ref y) (hlt : R.h.lt = 10)
    (hr : R.x.tH.r.size = R.h.lt) :
    ∃ ew, Ok (ewOf R "HD0") F C ew F C ∧
      claimVal ρ lay W cl = Blocks.ext R.h.lt (fun i => ∑ k ∈ range nD,
        eqR ρ R.x.rs 0 13 k *
          bLib y (ρ.val (wxOf R ew)) (fun v => ρ.val (ew.getD v zeroE)) (Hof W) i k)
        (pt ρ R.x.tH.r) := by
  obtain ⟨ew, hew, hval⟩ := claim_end ρ Z h hk hlam hs hV hdry W
  refine ⟨ew, hew, ?_⟩
  rw [hval]
  unfold Blocks.ext bLib
  refine sum_congr rfl fun i hi => ?_
  have hi' : i < 2 ^ R.h.lt := mem_range.mp hi
  have hi1 : i < HeadSizes.ref.T := by
    rw [hlt] at hi'
    exact hi'
  rw [eqTab_value ρ R.x.tH.r i (by rw [hr]; exact hi'), hr, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [Y.rho i hi1]
  by_cases hon : R.cov.hOn.getD i false = true
  · rw [if_pos hon, if_pos hon, Y.win i hi1 hon, Int.cast_one, one_mul, mul_assoc]
  · simp only [if_neg hon, Int.cast_zero, zero_mul, mul_zero]

/-- The verifier's own table of the equality weights of the 13 challenges over the channels, which
its claim on the first end value of the last token sumcheck reads (claimLogits,
OnBytes/Model/Head.lean), has at every channel the weight eqR. -/
theorem eqLow_eqR (rs : Array E) (hs : 13 ≤ rs.size) {k : ℕ} (hk : k < nD) :
    ρ.val ((eqLow rs 0 13).getD k zeroE) = eqR ρ rs 0 13 k :=
  eqLow_value ρ rs hs (Nat.lt_trans hk (by decide))

/-- **The end, in the letters of the start and of the verifier's other claim.** claim_end_lib with
the channels' weights read in the verifier's own table, as its claim on the first end value reads
them, and with the sum of the weights ew in the place of the verifier's wx, as logits_start_lib has
it. Asked beside: the segment HD0 has one entry for each entry of the vocabulary. -/
theorem claim_end_port {s : WsShape} (Z : SizedW s ppref) {lay : WsLay}
    (h : wsLayOf s true kRef = .ok lay) {R : Model.Head.Run} {F G : Fork} {C D : Ctx}
    {cl : WsClaim} (hk : Ok (weightsClaim R lay) F C cl G D) (hlam : R.hp.lamS = 13)
    (hs : 13 ≤ R.x.rs.size) (hV : R.h.V = nV) (hdry : C.ch.dry = false) (W : Wm K)
    {y : Inst.Model.Head.Req} (Y : ReqFits R HeadSizes.ref y) (hlt : R.h.lt = 10)
    (hr : R.x.tH.r.size = R.h.lt) (S : SegHas R "HD0" nV) :
    ∃ ew, Ok (ewOf R "HD0") F C ew F C ∧
      claimVal ρ lay W cl = Blocks.ext R.h.lt (fun i => ∑ k ∈ range nD,
        ρ.val ((eqLow R.x.rs 0 R.hp.lamS).getD k zeroE) *
          bLib y (∑ v ∈ range nV, ρ.val (ew.getD v zeroE)) (fun v => ρ.val (ew.getD v zeroE))
            (Hof W) i k)
        (pt ρ R.x.tH.r) := by
  obtain ⟨ew, hew, e⟩ := claim_end_lib ρ Z h hk hlam hs hV hdry W Y hlt hr
  refine ⟨ew, hew, ?_⟩
  have hwx : ρ.val (wxOf R ew) = ∑ v ∈ range nV, ρ.val (ew.getD v zeroE) := by
    rw [wxOf_value ρ R ew (le_of_eq (by rw [S.size hew, hV])), hV]
  rw [e, hwx, hlam]
  refine Blocks.ext_congr (fun i _ => ?_) _
  exact sum_congr rfl fun k hk => by rw [eqLow_eqR ρ R.x.rs hs (mem_range.mp hk)]

end Whole

#print axioms facKK_at
#print axioms head_unit
#print axioms units_head
#print axioms entryW_Hof
#print axioms claimVal_head
#print axioms settle_head
#print axioms avFold_value
#print axioms logits_end
#print axioms logits_start
#print axioms av_loop
#print axioms weightsClaim_ok
#print axioms avOf_value
#print axioms claim_of_run
#print axioms claim_end
#print axioms settle_of_run
#print axioms logits_start_lib
#print axioms claim_end_lib
#print axioms eqLow_eqR
#print axioms claim_end_port

end OnBytes.Road.Hd
