-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysRef.lean: the capstone at the library's reference sizes, stated on the key
vectors of the equivalence of Johnson/Road/FormsKeysPass.lean.

Johnson/Road/FormsKeysCaller.lean ends in an equation on the extensions of the library's eight key
vectors, at any sizes that agree with the verifier's shape. Johnson/Road/FormsKeysPass.lean and
Johnson/Road/FormsKeysScl.lean say, at the library's reference sizes, that the entries of eight key
vectors lie in their tables exactly if the clause on the keys of the library's condition for a group
of layers holds. This file states the first on the key vectors of the second, with those of its
hypotheses concluded that have a theorem.

What is compared with what: as in FormsKeysCaller.lean, FormsKeysPass.lean and FormsKeysScl.lean; no
new comparison is made. hKF is the shape that Johnson/Road/FormsKeysRunK.lean writes by hand after
the full-size shipped example's parameter file; a guard there holds it against the shape that the
verifier makes from the file.

The seven matches between the two statements. Six are met in the statements' letters: three by
theorems, three by choosing the letters, which narrows the theorem and moves the debt. The seventh
is not met.
 By theorems:
 - The sizes are DF, the library's Dim.ref: sizedKF (FormsKeysRunK.lean) has the two records of
   sizes at hKF; cap_ref has the cap.
 - The first layer of group g is 4 g: lam_ref. The group's number is written p.v.g throughout; the
   claims' environment has the same (env).
 - The scales: the key vectors stand under sclOf of the verifier's scale file; the library's
   condition stands under the table scalesOf (FormsKeysScl.lean): the library's reading of a file's
   records, on the records that fileOf (Johnson/Road/FormsKeysWords.lean) cuts out of the verifier's
   file, with any final normalisation (keyVecs_ffKey_file). That this table is lawful in the
   library's sense is not shown here.
 By choosing the letters, and the price of each:
 - The number of column bits is kRef and the parameters are ppref (sizedW_KF,
   Johnson/Road/FormsKeysRunWK.lean, has the weights' sizes). The price: hlw is asked at kRef.
 - The tables are tbRef. The price: hpad and R are asked at tbRef; they are run in two of the twelve
   groups.
 - The matrices are casts of integer matrices. The price: that the matrices of a run are such casts
   is shown by nothing here; it is the matter of the smallness test.
 Not met:
 - From an equation at one point to every entry: the lookup.

Main theorems.
 - kqkk_of_heldAt, hk_of_scalesHeld: the verifier's test on the file of scales gives the clause on
   the shifts of queries and keys.
 - cap_ref, hfl_ref, trees_ref: three evaluations of closed numbers; lam_ref.
 - sizes_of_lines: the lengths of the lookup's two points, from the lookup's lines and one of its
   tests.
 - worlds_of_holds: the three hypotheses of sigFits_of_look on the world, from Holds.
 - RefData, PubRef: the letters of the theorems at the reference, and their public hypotheses as one
   record. PubRef.more: what follows from the record.
 - RefIn, refRun, pubRef_of_run: a function that evaluates the public hypotheses, and the theorem
   that holds it against the record; ropeB, padB with ropeFits_of_B, hpad_of_B for the two fields
   that are evaluated in another form.
 - gpos_ref: whole_gpos at the reference, with two of its three own hypotheses concluded.
 - capstone_ref: three statements on the same eight key vectors, bundled. None follows from another:
   the second and the third read hy and the group's number alone; the hypotheses on the world and
   all other public ones serve the first.
 - sum_is_leaf, sum_is_leafAll, padOf_value, padOf_ref, capstone_leaf: the right side of the
   capstone's equation is the extension of the library's vector of leaves at the keys moved by the
   call's number times theta, plus the number for the padding trees; that number is alpha less a
   padding key times the equality weights of the unused trees, and 0 at hKF. padOf_value asks the
   lengths of the lookup's two points and the bound on the number of trees in the letters of the
   numbers that the lookup has left (H.fo.shape), not the layout's; no term joins it with
   sum_is_leafAll.
 - keys_glued_ref: beside capstone_ref, and proved from tie_port_file
   (Johnson/Road/FormsKeysTieP.lean) alone: at the field Cb.Gl.E, the left side of the third
   statement of capstone_ref holds exactly if the keys' half of the conditions of the library's
   glued segment of the group does.

Who reads the targets, by reading the library. The laws admit and force read Cond whole: all 25
segments, the identities' half too, and a bound on the cells: so nothing here reaches the relation.
The keys' half alone is read by the library's theorem on the lookup's claim before the shift
(ldPartKeys_holds in Cb/Part/LdPartLkpFam.lean), which the front of a segment and the law on the
multiplicities' bits use. No term of this file joins that theorem with keys_glued_ref. leaf_ff,
under capstone_leaf, stands on CallsOK.ext_leafK of Blocks/LookupCalls.lean, a file that
Inst/Model/FF/Objects.lean and other files of this library import.

The hypotheses. capstone has 49. capstone_ref has 40: the 35 fields of the record PubRef, which are
public, and five on the world. Fourteen are gone and five are new. Seven are theorems at the closed
letters hKF, DF, shapeV hKF 202048 and kRef: S, Z, hc, Zw, hsL, h4, and hfl (hfl_ref). Five are
traded for five lines of the verifier and for om := powers xo 2: htm, hNM by plan_sizes
(Johnson/Road/FormsKeysPlan.lean) for hP, hG, hpl (Pub.of and plansG return, and pl is the plan of
the group); hsx, hsy by sizes_of_lines for hzx, hzy (the two lines in which the lookup cuts its
points out of one array); hom by powers_two (Johnson/Road/FormsKeysRet.lean). Two follow from
others: hrd from hP (pub_reads: the reads are those of the public numbers that Pub.of returns), hs0
from hy (shape_of_layout, Johnson/Road/FormsKeysShape.lean: hpt is stated at the layout's numbers of
the lookup). alpha and theta, free in capstone, are the lookup's own. Pub.of stands at the scales,
the rotary table and the weights' layout of the two environments, as in the verifier's caller.

The public hypotheses, and what is run of them. refRun calls the verifier's functions in the forms
in which the fields of PubRef name them, and evaluates the tests among the fields: R as equalities
of integers, hpad as equalities of words. pubRef_of_run: if it returns letters, PubRef holds of
them, where numerals read as numbers (hρ: gl_numerals, Johnson/Road/FormsKeysKit.lean). In that
proof ht, env, hcrt, hHe and hlam hold by the way refRun writes the letters.
That refRun returns letters anywhere is held by a run that is no part of this library (at the
full-size example's two files, in the first and the last group of layers, at made-up points);
nothing here shows it. That the verifier's caller makes its records as refRun makes them is by
reading its text. Of the ten other groups: hy, hs, hN, hpad, hlw, hP and hG name no group; all
others are not run there. hsh of capstone_leaf is no field of PubRef and is not run.

Which value is which. Hidden: the entries of the reads (Hd), the slot sCl, the slots in the forms
cEnd and KT. Sent: the array p.shownT, which rPort holds as it is; H1, V, shownA and shownB of hst.
Drawn: the lookup's points, alpha, theta, xo, rs, the end point c.rt. Public: all else. Mz, Wi and
hh are free letters, tied to no commitment.

What is not claimed. All statements are identities in a world or equivalences of two conditions. The
library's condition has other conjuncts than the one on the keys of this segment; none is touched.
Nothing is said on soundness. No witness meets the hypotheses on the world. What KT is worth is not
looked at. The relation's two other clauses are not touched. The program does not import this file.
-/
import Johnson.Road.FormsKeysCaller
import Johnson.Road.FormsKeysScl
import Johnson.Road.FormsKeysValid
import Johnson.Road.FormsKeysLookP
import Johnson.Road.FormsKeysPlan
import Johnson.Road.FormsKeysRunWK
import Johnson.Road.FormsKeysCalls
import Johnson.Road.FormsKeysPub
import Johnson.Road.FormsKeysTieP

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open Finset
open OnBytes.Model (Reading World Aff CallD WsClaim HFun Level Settings lastOf wsLayOf powers eqTab)
open OnBytes.Model.Layer (Env Lay Heard Reads Scales TableAsk TableAt PanelEnv ClaimEnv Panels
  StackEnd Pub HPlan2 layout scalesHeld scalesHeldAt readsOf layTables tableAsks panelsA panelsT
  placePanels stackEnd pointsOf funsOf plansG)
open Inst.Model (Scl Tables Mat ppref tbRef)
open Inst.Model.All (DF)
open Inst.Model.Layout (kRef)
open Inst.Model.FFSeg (Dim Cell Fam LW Pan Sig1 ClT Gpos wc zc eC Dk sg NT fSh hhU zpos aC keyVec
  fams used lut layerR)

/-! ## The shifts of queries and keys -/

/-- The tests on the record of one layer ask that the shifts of queries and keys are equal or both
at least 16. -/
theorem kqkk_of_heldAt {h : Model.Layer.Shape} {s : Scales} {l : ℕ}
    (hy : scalesHeldAt h s l = .ok ()) :
    s.kl l Model.Layer.Lkq = s.kl l Model.Layer.Lkk ∨
      (16 ≤ s.kl l Model.Layer.Lkq ∧ 16 ≤ s.kl l Model.Layer.Lkk) := by
  unfold scalesHeldAt at hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨-, -, hy⟩ := ok_of_bind hy
  obtain ⟨t, -⟩ := ok_of_refuse hy
  by_cases e : s.kl l Model.Layer.Lkq = s.kl l Model.Layer.Lkk
  · exact Or.inl e
  · right
    have hne : (s.kl l Model.Layer.Lkq != s.kl l Model.Layer.Lkk) = true := by simpa using e
    rw [hne, Bool.true_and] at t
    obtain ⟨a, b⟩ := or_false_split t
    have a' := of_decide_eq_false a
    have b' := of_decide_eq_false b
    exact ⟨by omega, by omega⟩

/-- The hypothesis hk of sig1_port and whole_gpos (Johnson/Road/FormsKeysCaller.lean), from the
verifier's own test on the file of scales. Under the table of scales sclOf of a group g of an
admitted layout, for any sizes D and every number l: the shifts of queries and keys of layer l are
equal or both at least 16. -/
theorem hk_of_scalesHeld {h : Model.Layer.Shape} {y : Lay} {sc : Scales} (A : Admitted h y)
    (hs : scalesHeld h sc = .ok ()) {g : ℕ} (hg : g < y.NGr) (D : Dim) :
    letI : Scl := sclOf h sc g y.Lam
    ∀ l, (D.Pl l).kq = (D.Pl l).kk ∨ (16 ≤ (D.Pl l).kq ∧ 16 ≤ (D.Pl l).kk) := by
  intro l
  have e : h.L = 2 ^ h.ll * (h.L / 2 ^ h.ll) :=
    (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero A.whole)).symm
  have hLam : y.Lam = 2 ^ h.ll := by rw [A.laid.Lam, A.shape]
  rw [A.NGr] at hg
  have hlt : g * y.Lam + l % y.Lam < h.L := by
    rw [hLam]
    exact group_lt e hg (Nat.mod_lt _ (Nat.two_pow_pos _))
  exact kqkk_of_heldAt
    (forM_ok (scalesHeldAt h sc) (List.range h.L) hs _ (List.mem_range.mpr hlt))

/-! ## Closed numbers at the full-size example's shape and the library's reference sizes -/

/-- The library's cap on a tree's depth at its reference sizes is that of the full-size example's
shape: 28. An evaluation of closed numbers. -/
theorem cap_ref : DF.cap = hKF.lidb := rfl

/-- At the full-size example's shape and the library's reference sizes the verifier's least number
of columns passes the library's number for no call. An evaluation of closed numbers by Lean's
kernel. -/
theorem hfl_ref : ∀ k : Fin 8, hKF.nmin - hKF.ll - hKF.lt ≤ Nat.clog 2 (used DF k) := by
  decide +kernel

/-- At the library's reference sizes call 0 has more than one tree. An evaluation of closed numbers
by Lean's kernel. -/
theorem trees_ref : 0 < eC DF 0 := by decide +kernel

/-- A group of a layout for the full-size example's shape has four layers. -/
theorem lam_ref {pc : List (List String)} {y : Lay} (hy : layout hKF pc = .ok y) : y.Lam = 4 := by
  have A := admitted_of_layout hy switchesK.2.p3
  rw [A.laid.Lam, A.shape]
  rfl

/-! ## The lengths of the lookup's two points -/

/-- The hypotheses hsx and hsy of the theorems on the calls' points, from the lines in which the
lookup cuts its two points out of one array rho and makes the calls' points, and its test on the
length of the point of one call c0 that has more than one tree in the library's numbers. The other
hypotheses are those of look_of_lines (Johnson/Road/FormsKeysCaller.lean). -/
theorem sizes_of_lines {h : Model.Layer.Shape} {pc : List (List String)} {v : Env} {D : Dim}
    (hy : layout h pc = .ok v.y) (S : Switches h) (Z : Sized h D) (hc : D.cap = h.lidb)
    (hN : LinesAre v.y) (hfl : ∀ k : Fin 8, h.nmin - h.ll - h.lt ≤ Nat.clog 2 (used D k))
    {rho zx zy : Array E} (hzx : zx = rho.extract 0 v.y.fo.dT)
    (hzy : zy = rho.extract v.y.fo.dT rho.size)
    (hzk : v.zk = (Array.range v.y.fo.NC).map fun q =>
      zy.extract (v.y.fo.rK - v.y.fo.iota.getD q 0) zy.size ++ zx)
    {s0 : Model.Forest.Shape} (hs0 : Model.Forest.shape v.y.cl v.y.h.lidb = .ok s0)
    (hpt : ((List.range s0.NC).all fun q =>
      (v.zk.getD q #[]).size == ((s0.calls[q]?).map (·.n)).getD 0) = true)
    {c0 : Fin 8} (hpos : 0 < eC D c0) :
    zx.size = v.y.fo.dT ∧ zy.size = v.y.fo.rK := by
  obtain ⟨h8, Hc⟩ := lines_calls hN
  have H : ∀ k : Fin 8, ∃ cd, v.y.calls[k.val]? = some cd ∧
      cd.segs.map (·.name) = (fams k).map segName ∧
      h.nmin - h.ll - h.lt ≤ Nat.clog 2 (used D k) := fun k => by
    obtain ⟨cd, a, b⟩ := Hc k
    exact ⟨cd, a, b, hfl k⟩
  have T := treesFit_of_layout hy S Z hc h8 H
  have hNC : v.y.fo.NC = 8 := by rw [(fo_of_layout hy).2.1, (fo_of_layout hy).2.2, h8]
  obtain ⟨cd, hcq, hn, -⟩ := H c0
  have hrec := n_of_layout hy S Z hcq hn (hfl c0)
  have hall := List.all_eq_true.mp (test_of_port hy hs0 hpt) c0.val
    (List.mem_range.mpr (by rw [h8]; exact c0.isLt))
  rw [hrec] at hall
  have hsz : (v.zk.getD c0.val #[]).size = aC D c0 := by simpa using hall
  have hD := Inst.Model.FFSeg.IndexFacts.Dk_le D c0
  have he : eC D c0 = aC D c0 - Inst.Model.FFSeg.Dk D := rfl
  exact sizes_of_pad hzx hzy hzk (by rw [hNC]; exact c0.isLt) hsz
    (by rw [T.dT, T.iota c0]; omega) (by rw [T.iota c0, T.rK]; exact eC_le_sg D c0)
    (by rw [T.iota c0]; exact hpos)

/-! ## The sum over the calls as the library's vector of leaves -/

section Leaf

variable {K : Type} [Field K]

/-- The right side of capstone (Johnson/Road/FormsKeysCaller.lean) on the library's vector of
leaves: an element X that is the sum over the eight calls of the call's weight times al - q sh less
the extension of the call's key vector, plus pad, is the extension at z of the library's vector of
leaves at the keys moved by the call's number times sh, plus pad. By leaf_ff
(Johnson/Road/FormsKeysCalls.lean). -/
theorem sum_is_leaf [scl : Scl] (P0 : Blocks.LkPar K) (D : Dim) (t : Cell → K) (tb : Tables)
    (L0 : ℕ) (w : ℕ → LW K) (al sh : K) (z : ℕ → K) {X pad : K}
    (hE : X = (∑ q : Fin 8, wc D z q *
      (al - (q.val : K) * sh - Blocks.ext (aC D q) (keyVec D t tb L0 w q) (zc D z q))) + pad) :
    X = Blocks.ext (Dk D + sg D) ((lkP P0 D).leafK (tagKey D t tb L0 w sh) al) z + pad := by
  rw [leaf_ff]
  exact hE

/-- The same with the trees that belong to no call: if pad is al - k times the equality weights of
the numbers of these trees, X is the extension of the vector of leaves that has al - k there. By
ext_leafAll. -/
theorem sum_is_leafAll [scl : Scl] (P0 : Blocks.LkPar K) (D : Dim) (t : Cell → K) (tb : Tables)
    (L0 : ℕ) (w : ℕ → LW K) (al sh k : K) (z : ℕ → K) {X : K}
    (hE : X = (∑ q : Fin 8, wc D z q *
        (al - (q.val : K) * sh - Blocks.ext (aC D q) (keyVec D t tb L0 w q) (zc D z q))) +
      (al - k) * ∑ θ ∈ range (2 ^ sg D), if θ < NT D then 0 else Blocks.eqN (sg D) (Dk D) z θ) :
    X = Blocks.ext (Dk D + sg D) (leafAll (lkP P0 D) (tagKey D t tb L0 w sh) al k) z := by
  rw [hE, ← leaf_ff P0 D t tb L0 w al sh z]
  unfold lkP
  generalize tagKey D t tb L0 w sh = key
  generalize Dk D = d
  generalize sg D = s
  generalize NT D = n
  exact (ext_leafAll (lkOf P0 d s n) key al k z).symm

/-- What the start form's number for the padding trees reads as: alpha less the padding key of call
0, times the sum of the equality weights of the numbers of the trees past the last one in use, at
the point zOf. In the letters of the numbers that the lookup has left (H.fo.shape). Asked: the
lengths of the lookup's two points; there are at most as many trees as numbers for trees. -/
theorem padOf_value (ρ : Reading K) (H : Heard) (hsx : H.fo.zx.size = H.fo.shape.dT)
    (hsy : H.fo.zy.size = H.fo.shape.rK) (hnt : H.fo.shape.NT ≤ 2 ^ H.fo.shape.rK) :
    ρ.val (padOf H) = (ρ.val H.fo.alpha - ρ.val (H.fo.padKey 0)) *
      ∑ θ ∈ range (2 ^ H.fo.shape.rK), if θ < H.fo.shape.NT then 0
        else Blocks.eqN H.fo.shape.rK H.fo.shape.dT (zOf ρ H.fo.zx H.fo.zy) θ := by
  unfold padOf
  refine (foldl_madd_range ρ (fun t => (eqTab H.fo.zy).getD (H.fo.shape.NT + t) zeroE)
    (fun _ => subE H.fo.alpha (H.fo.padKey 0)) _).trans ?_
  beta_reduce
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hnt
  rw [hm, Nat.add_sub_cancel_left, Finset.sum_range_add,
    Finset.sum_eq_zero (fun θ hθ => if_pos (mem_range.mp hθ)), zero_add, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have ht' := mem_range.mp ht
  rw [if_neg (by omega), ρ.sub, ey_of_look hsx hsy (by rw [hm]; omega), mul_comm]

/-- At the full-size example's shape the start form's number for the padding trees reads as 0: all
numbers for trees are in use there (the field full of the library's ref_ok,
Inst/Model/FF/Index.lean). hsh: the test by which the verifier's caller holds the numbers that the
lookup has left against the layout's, in its letters (hearLook, OnBytes/Model/Layer.lean). -/
theorem padOf_ref (ρ : Reading K) {pc : List (List String)} {v : Env} {H : Heard}
    (hy : layout hKF pc = .ok v.y) (hN : LinesAre v.y)
    (hsh : (H.fo.shape.dT == v.y.fo.dT && H.fo.shape.kT == v.y.fo.kT &&
      H.fo.shape.NT == v.y.fo.NT && H.fo.shape.rK == v.y.fo.rK &&
      H.fo.shape.first == v.y.fo.first && H.fo.shape.iota == v.y.fo.iota &&
      H.fo.shape.callOf == v.y.fo.callOf) = true) :
    ρ.val (padOf H) = 0 := by
  obtain ⟨h8, Hc⟩ := lines_calls hN
  have H' : ∀ k : Fin 8, ∃ cd, v.y.calls[k.val]? = some cd ∧
      cd.segs.map (·.name) = (fams k).map segName ∧
      hKF.nmin - hKF.ll - hKF.lt ≤ Nat.clog 2 (used DF k) := fun k => by
    obtain ⟨cd, a, b⟩ := Hc k
    exact ⟨cd, a, b, hfl_ref k⟩
  have T := treesFit_of_layout hy switchesK.2 sizedKF.1 cap_ref h8 H'
  have hNT := NT_of_layout hy switchesK.2 sizedKF.1 cap_ref h8 H'
  simp only [Bool.and_eq_true, beq_iff_eq] at hsh
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, a⟩, b⟩, -⟩, -⟩, -⟩ := hsh
  have h0 : 2 ^ H.fo.shape.rK - H.fo.shape.NT = 0 := by
    rw [a, b, T.rK, hNT, Inst.Model.FFSeg.ref_ok.full]
    exact Nat.sub_self _
  unfold padOf
  rw [h0]
  exact ρ.zero

end Leaf

/-! ## The tables of the reads, from their own statements -/

/-- The hypotheses on the world of sigFits_of_look (Johnson/Road/FormsKeysCaller.lean), and the
length of the end point of the second token sumcheck, from one hypothesis on the reads: every table
of the verifier's list holds what it says of the matrices Mm. The steps are those in the proof of
capstone. -/
theorem worlds_of_holds {K : Type} [Field K] (ρ : Reading K) (Wo : World K)
    {h : Model.Layer.Shape} {pc : List (List String)} {p : PanelEnv} {c : ClaimEnv} {rd : Reads}
    {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ} {D : Dim} {Zp : Array E} {H : Heard}
    {tT : Model.Tsc} {tl : Model.HTailF2} {hd : Level} {hd2 : Option Level}
    {pts : List (String × Array E)} {funs : Array HFun}
    (hy : layout h pc = .ok p.v.y) (S : Switches h) (hg : p.v.g < p.v.y.NGr)
    (hrd : readsOf p.v.y = .ok rd)
    (hl : layTables (matsR p.v.y p.v.g) (tableAsks p.v.y rd p.v.g) 0 = some r)
    (ht : p.v.tab = r.1) (Z : Sized h D) (hZ : lastOf H.fo.zx p.v.y.h.la = .ok Zp)
    (hzt : lastOf H.fo.zx p.v.y.h.lt = .ok H.ztF) (h4 : h.p4 = true) (hcrt : c.rt = tT.r)
    (htm : (tl.mats.map fun M => (M.m, M.k)) = matsR p.v.y p.v.g) (hNM : tl.NM = tl.mats.size)
    (hpts : pointsOf p.v.y H hd hd2 = some pts)
    (hfun : funsOf p.v.y H.fo pts r.2.1 = some funs) (hT : H.tT = some tT) (Mm : Mats K)
    (Hd : ∀ Fn ∈ funs, Holds ρ Wo tl p.v.iU3 p.v.K3 Mm Fn) :
    TrueAt ρ Wo p.v h.lt (cellsAt p.v.y Mm) (pt ρ Zp) (pt ρ H.ztF) ∧
      TrueAt2 ρ Wo p.v h.lt (cellsAt p.v.y Mm) (pt ρ Zp) (pt ρ c.rt) ∧
      (∀ b, p.v.tabAt ("qa" ++ "@" ++ "zt") = some b →
        ShortTrue ρ Wo p.v b 3 h.lt (cellsAt p.v.y Mm) (pt ρ H.ztF)) ∧
      c.rt.size = D.lT := by
  have sh := (admitted_of_layout hy S.p3).shape
  obtain ⟨Z1, hZ1, T⟩ := trueAt_of_holds ρ Wo hy S hg hrd hl ht htm hNM hpts hzt hfun Mm Hd
  obtain ⟨Z2, hZ2, hr2, T2⟩ :=
    trueAt2_of_holds ρ Wo hy S hg hrd hl ht htm hNM hpts hfun hT Mm Hd
  have e1 : Z1 = Zp := Except.ok.inj (hZ1.symm.trans hZ)
  have e2 : Z2 = Zp := Except.ok.inj (hZ2.symm.trans hZ)
  subst e1
  subst e2
  have Ro := shortQa_of_holds ρ Wo hy S hg hrd hl ht htm hNM hpts hfun h4 Mm Hd
  rw [sh] at T T2 Ro
  rw [← hcrt] at T2 hr2
  exact ⟨T, T2, Ro, by rw [hr2, sh, Z.lT]⟩

/-! ## The public hypotheses as one record, and a run of them -/

/-- The letters of the theorems at the reference: the records that the check of a layer sub-proof
builds, and what the verifier's functions return on them. -/
structure RefData where
  /-- the parameter file's lines of calls -/
  pc : List (List String)
  /-- the panels' environment -/
  p : PanelEnv
  /-- the claims' environment -/
  c : ClaimEnv
  /-- what layTables returns -/
  r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ
  /-- the last la coordinates of the lookup's point inside a tree -/
  Zp : Array E
  /-- the array out of which the lookup cuts its two points -/
  rho : Array E
  /-- the last la coordinates of the calls' points -/
  ends : Array (Array E)
  /-- what the verifier holds after the lookup, the norms and the two token sumchecks -/
  H : Heard
  /-- the record of the second token sumcheck -/
  tT : Model.Tsc
  /-- the product layer of the gated products -/
  hd : Level
  /-- that of the routed gated products -/
  hd2 : Option Level
  /-- what pointsOf returns -/
  pts : List (String × Array E)
  /-- what funsOf returns -/
  funs : Array HFun
  /-- the size of the vocabulary, as Pub.of takes it -/
  V' : ℕ
  /-- the request's tokens, as Pub.of takes them -/
  tokv : Array ℕ
  /-- the numbers that the parameter file sets for a run -/
  set : Settings
  /-- what Pub.of returns -/
  P : Pub
  /-- what plansG returns -/
  G : Array HPlan2
  /-- the plan of the group -/
  pl : HPlan2
  /-- the calls of the second walk -/
  TS : List ℕ
  /-- what panelsT returns -/
  pans : Panels
  /-- what weightClaims returns -/
  cl : List WsClaim
  /-- the element from which the weights of the two claims are made -/
  xo : E
  /-- the challenges of the batched sumcheck, as stackEnd takes them -/
  rs : Array E
  /-- the shown end values of the never-sent vectors -/
  H1 : Array E
  /-- the shown values of the weight claims -/
  V : Array E
  /-- the number of rounds of the batched sumcheck -/
  lam : ℕ
  /-- the shown end value of the first long vector -/
  shownA : E
  /-- that of the second -/
  shownB : E
  /-- what stackEnd returns -/
  s' : StackEnd
  /-- what weighedOf returns for the calls -/
  weighed : Array (Array Bool)
  /-- the calls' factors -/
  parts : List Aff

/-- The public hypotheses of the theorems at the reference, on the letters d. Each field but hN, R,
hpad and hρ is a line or a test of the verifier, at the shape hKF, at the weights' shape
shapeV hKF 202048 and at the library's kRef. The reads are those of the public numbers that Pub.of
returns. hpt is stated at the layout's numbers of the lookup. -/
structure PubRef {K : Type} [Field K] (ρ : Reading K) (d : RefData) : Prop where
  /-- layout returns -/
  hy : layout hKF d.pc = .ok d.p.v.y
  /-- the tests on the file of scales pass -/
  hs : scalesHeld hKF d.p.v.sc = .ok ()
  /-- g is a group -/
  hg : d.p.v.g < d.p.v.y.NGr
  /-- layTables returns -/
  hl : layTables (matsR d.p.v.y d.p.v.g) (tableAsks d.p.v.y d.P.rd d.p.v.g) 0 = some d.r
  /-- the environment's tables are those -/
  ht : d.p.v.tab = d.r.1
  /-- numerals read as numbers -/
  hρ : Numerals ρ
  /-- the eight lines of calls are the library's -/
  hN : LinesAre d.p.v.y
  /-- the lookup's point inside a tree -/
  hzx : d.H.fo.zx = d.rho.extract 0 d.p.v.y.fo.dT
  /-- its point over the trees' numbers -/
  hzy : d.H.fo.zy = d.rho.extract d.p.v.y.fo.dT d.rho.size
  /-- the calls' points -/
  hzk : d.p.v.zk = (Array.range d.p.v.y.fo.NC).map fun q =>
    d.H.fo.zy.extract (d.p.v.y.fo.rK - d.p.v.y.fo.iota.getD q 0) d.H.fo.zy.size ++ d.H.fo.zx
  /-- the calls' weights -/
  he : d.p.e = (Array.range d.p.v.y.fo.NC).map (Model.Forest.callWeight d.p.v.y.fo d.H.fo.zy)
  /-- the last la coordinates of the lookup's point -/
  hZ : lastOf d.H.fo.zx d.p.v.y.h.la = .ok d.Zp
  /-- the token point -/
  hzt : lastOf d.H.fo.zx d.p.v.y.h.lt = .ok d.H.ztF
  /-- the last la coordinates of the calls' points -/
  hm : d.p.v.zk.mapM (fun z => (lastOf z d.p.v.y.h.la).toOption) = some d.ends
  /-- they are those of the lookup's point -/
  ha : d.ends.all (· == d.Zp) = true
  /-- each call's point has the length that the call's record says -/
  hpt : ((List.range d.p.v.y.fo.NC).all fun q =>
    (d.p.v.zk.getD q #[]).size == ((d.p.v.y.fo.calls[q]?).map (·.n)).getD 0) = true
  /-- panels and claims share one environment -/
  env : d.p.v = d.c.v
  /-- wsLayOf returns -/
  hlw : wsLayOf (shapeV hKF 202048) true kRef = .ok d.c.wsLay
  /-- the end point of the second token sumcheck -/
  hcrt : d.c.rt = d.tT.r
  /-- the rotary tables are the library's -/
  R : ∀ lam, lam < d.c.v.y.Lam → RopeFits ρ d.c DF tbRef (4 * d.p.v.g) lam
  /-- Pub.of returns -/
  hP : Pub.of d.p.v.y d.p.v.sc d.c.rope d.c.wsLay d.V' d.tokv d.set = .ok d.P
  /-- plansG returns -/
  hG : plansG d.P = .ok d.G
  /-- the plan of the group -/
  hpl : d.G[d.p.v.g]? = some d.pl
  /-- pointsOf returns -/
  hpts : pointsOf d.p.v.y d.H d.hd d.hd2 = some d.pts
  /-- funsOf returns -/
  hfun : funsOf d.p.v.y d.H.fo d.pts d.r.2.1 = some d.funs
  /-- the second token sumcheck has been heard -/
  hT : d.H.tT = some d.tT
  /-- the calls of the second walk -/
  hTS : d.P.rd.tscCalls.mapM d.p.v.y.callNo = some d.TS
  /-- panelsT returns -/
  hp : panelsT d.p d.TS (panelsA d.p {}) = some d.pans
  /-- weightClaims returns -/
  hcl : d.c.weightClaims d.TS = some d.cl
  /-- stackEnd returns -/
  hst : stackEnd d.p.v.y (placePanels d.pans.bl).1 d.rs d.lam (powers d.xo 2) d.H1 d.V d.shownA
    d.shownB = some d.s'
  /-- the number of rounds -/
  hlam : (ceilLog2 (placePanels d.pans.bl).2 == d.lam) = true
  /-- the start form reads the weights of the panels' environment -/
  hHe : d.H.fo.e = d.p.e
  /-- weighedOf returns for all calls -/
  hw : d.p.v.y.calls.mapM d.p.v.weighedOf = some d.weighed
  /-- joinPart returns for all calls -/
  hparts : (d.p.v.y.calls.zip d.weighed).toList.zipIdx.mapM
    (fun x => d.p.v.joinPart d.H.fo.alpha d.H.fo.theta x.2 x.1.1 x.1.2) = some d.parts
  /-- the padding keys are the library's -/
  hpad : ∀ k : Fin 8,
    ρ.val (ofF ((d.p.v.y.cl.getD k.val {}).tauAt (d.p.v.y.cl.getD k.val {}).t0)) =
      (((lut tbRef k).pad : ℤ) : K)

/-- The public numbers that Pub.of returns hold what readsOf returns. -/
theorem pub_reads {y : Lay} {sc : Scales} {rope : Array ℕ} {wsLay : Model.WsLay} {V : ℕ}
    {tokv : Array ℕ} {set : Settings} {P : Pub}
    (hP : Pub.of y sc rope wsLay V tokv set = .ok P) : readsOf y = .ok P.rd := by
  unfold Pub.of at hP
  obtain ⟨-, hP⟩ := ok_of_refuse hP
  obtain ⟨rd, hrd, hP⟩ := ok_of_bind hP
  have e := (Except.ok.inj hP).symm
  subst e
  exact hrd

/-- What follows from the record: readsOf returns; Forest.shape returns, with the test on the
points' lengths at what it returns; the lengths of the lookup's two points; the two equations on the
plan's list of matrices; the first layer of the group. -/
theorem PubRef.more {K : Type} [Field K] {ρ : Reading K} {d : RefData} (A : PubRef ρ d) :
    readsOf d.p.v.y = .ok d.P.rd ∧
      (∃ s0, Model.Forest.shape d.p.v.y.cl d.p.v.y.h.lidb = .ok s0 ∧
        ((List.range s0.NC).all fun q =>
          (d.p.v.zk.getD q #[]).size == ((s0.calls[q]?).map (·.n)).getD 0) = true) ∧
      d.H.fo.zx.size = d.p.v.y.fo.dT ∧ d.H.fo.zy.size = d.p.v.y.fo.rK ∧
      (d.pl.tl.mats.map fun M => (M.m, M.k)) = matsR d.p.v.y d.p.v.g ∧
      d.pl.tl.NM = d.pl.tl.mats.size ∧ d.c.v.g * d.c.v.y.Lam = 4 * d.p.v.g := by
  obtain ⟨s0, pub, hs0, e⟩ := shape_of_layout A.hy
  have hpt : ((List.range s0.NC).all fun q =>
      (d.p.v.zk.getD q #[]).size == ((s0.calls[q]?).map (·.n)).getD 0) = true := by
    have h := A.hpt
    rw [e] at h
    exact h
  obtain ⟨hsx, hsy⟩ := sizes_of_lines A.hy switchesK.2 sizedKF.1 cap_ref A.hN hfl_ref A.hzx A.hzy
    A.hzk hs0 hpt trees_ref
  obtain ⟨htm, hNM⟩ := plan_sizes A.hP A.hG A.hpl
  exact ⟨pub_reads A.hP, ⟨s0, hs0, hpt⟩, hsx, hsy, htm, hNM,
    by rw [← A.env, lam_ref A.hy, Nat.mul_comm]⟩

/-- Whether the verifier's rotary numbers of layer lam of the group are the entries of the tables C
and S at layer L0 + lam, as integers, at all positions and pairs of channels of RopeFits. -/
def ropeB (c : ClaimEnv) (D : Dim) (tb : Tables) (L0 lam : ℕ) : Bool :=
  (List.range (2 ^ D.lT)).all fun t => (List.range (c.v.y.h.dh / 2)).all fun i =>
    decide (Model.Layer.ropeC c.v.y.h c.v.sc c.rope (c.v.lay lam) t i false =
        tb.C (L0 + lam) t i) &&
      decide (Model.Layer.ropeC c.v.y.h c.v.sc c.rope (c.v.lay lam) t i true =
        tb.S (L0 + lam) t i)

/-- If so, RopeFits holds, where numerals read as numbers. -/
theorem ropeFits_of_B {K : Type} [Field K] {ρ : Reading K} (hρ : Numerals ρ) {c : ClaimEnv}
    {D : Dim} {tb : Tables} {L0 lam : ℕ} (h : ropeB c D tb L0 lam = true) :
    RopeFits ρ c D tb L0 lam := by
  have key : ∀ t i, t < 2 ^ D.lT → i < c.v.y.h.dh / 2 →
      Model.Layer.ropeC c.v.y.h c.v.sc c.rope (c.v.lay lam) t i false = tb.C (L0 + lam) t i ∧
      Model.Layer.ropeC c.v.y.h c.v.sc c.rope (c.v.lay lam) t i true = tb.S (L0 + lam) t i := by
    intro t i ht hi
    have h1 := List.all_eq_true.mp (List.all_eq_true.mp h t (List.mem_range.mpr ht)) i
      (List.mem_range.mpr hi)
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using h1
  exact ⟨fun t i ht hi => by rw [hρ.ofInt, (key t i ht hi).1],
    fun t i ht hi => by rw [hρ.ofInt, (key t i ht hi).2]⟩

/-- Whether for every call the library's padding key is not negative and the verifier's padding key,
as a word of the base field, is the word of the library's. -/
def padB (y : Lay) (tb : Tables) : Bool :=
  (List.finRange 8).all fun k =>
    decide (0 ≤ (lut tb k).pad) &&
      decide ((y.cl.getD k.val {}).tauAt (y.cl.getD k.val {}).t0 =
        Model.fOfNat (lut tb k).pad.toNat)

/-- If so, the verifier's padding keys read as the library's, where numerals read as numbers. -/
theorem hpad_of_B {K : Type} [Field K] {ρ : Reading K} (hρ : Numerals ρ) {y : Lay} {tb : Tables}
    (h : padB y tb = true) (k : Fin 8) :
    ρ.val (ofF ((y.cl.getD k.val {}).tauAt (y.cl.getD k.val {}).t0)) =
      (((lut tb k).pad : ℤ) : K) := by
  have h1 := List.all_eq_true.mp h k (List.mem_finRange k)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  rw [hpad_of_word hρ h1.2, Int.toNat_of_nonneg h1.1]

/-- What a run must be given: the parameter file's lines of calls, the scales, the group, the two
numbers of the array of reads, what the verifier holds after the lookup, the norms and the two token
sumchecks, the array out of which the lookup cuts its points, the two product layers, sent and drawn
values, the rotary table, and what Pub.of takes beside. -/
structure RefIn where
  /-- the parameter file's lines of calls -/
  pc : List (List String)
  /-- the scales -/
  sc : Scales
  /-- the number of the group -/
  g : ℕ
  /-- the number of the array of the reads -/
  iU3 : ℕ
  /-- the columns of that array -/
  K3 : ℕ
  /-- what the verifier holds after the lookup, the norms and the two token sumchecks -/
  H : Heard
  /-- the array out of which the lookup cuts its two points -/
  rho : Array E
  /-- the product layer of the gated products -/
  hd : Level
  /-- that of the routed gated products -/
  hd2 : Option Level
  /-- the values that the second token sumcheck has shown -/
  shownT : Array E
  /-- the field zt of the panels' environment -/
  zt : Array E
  /-- the field stubO of the panels' environment -/
  stubO : ℕ → ℕ → ℕ → ℤ
  /-- the rotary table -/
  rope : Array ℕ
  /-- the field rs of the claims' environment -/
  crs : Array E
  /-- the element from which the weights of the two claims are made -/
  xo : E
  /-- the challenges of the batched sumcheck, as stackEnd takes them -/
  rs : Array E
  /-- the shown end values of the never-sent vectors -/
  H1 : Array E
  /-- the shown values of the weight claims -/
  V : Array E
  /-- the shown end value of the first long vector -/
  shownA : E
  /-- that of the second -/
  shownB : E
  /-- the size of the vocabulary -/
  V' : ℕ
  /-- the request's tokens -/
  tokv : Array ℕ
  /-- the numbers that the parameter file sets for a run -/
  set : Settings

/-- The environment of the forms, as the check of a layer sub-proof writes it. -/
def RefIn.v (I : RefIn) (y : Lay) (tab : List TableAt) : Env :=
  { y, sc := I.sc, g := I.g, iU3 := I.iU3, K3 := I.K3, tab, zk := I.H.fo.zk }

/-- The panels' environment, with the calls' weights that the lookup has left. -/
def RefIn.p (I : RefIn) (y : Lay) (tab : List TableAt) : PanelEnv :=
  { v := I.v y tab, e := I.H.fo.e, shownT := I.shownT, zt := I.zt, stubO := I.stubO }

/-- The claims' environment. -/
def RefIn.c (I : RefIn) (y : Lay) (tab : List TableAt) (wsLay : Model.WsLay) (rt : Array E) :
    ClaimEnv :=
  { v := I.v y tab, wsLay, rope := I.rope, rs := I.crs, rt }

/-- The tests among the public hypotheses, as one Boolean: hg, hN, hzx, hzy, hzk, he, the second
half of hzt, ha, hpt, R as integers, hpad as words. -/
def RefIn.tests (I : RefIn) (y : Lay) (c : ClaimEnv) (Zp zt : Array E) (ends : Array (Array E)) :
    Bool :=
  decide (I.g < y.NGr) &&
  decide (y.calls.toList.map (fun cd => cd.segs.map (·.name)) =
    (List.finRange 8).map fun cc => (fams cc).map segName) &&
  decide (I.H.fo.zx = I.rho.extract 0 y.fo.dT) &&
  decide (I.H.fo.zy = I.rho.extract y.fo.dT I.rho.size) &&
  decide (I.H.fo.zk = (Array.range y.fo.NC).map fun q =>
    I.H.fo.zy.extract (y.fo.rK - y.fo.iota.getD q 0) I.H.fo.zy.size ++ I.H.fo.zx) &&
  decide (I.H.fo.e = (Array.range y.fo.NC).map (Model.Forest.callWeight y.fo I.H.fo.zy)) &&
  decide (zt = I.H.ztF) &&
  ends.all (· == Zp) &&
  ((List.range y.fo.NC).all fun q =>
    (I.H.fo.zk.getD q #[]).size == ((y.fo.calls[q]?).map (·.n)).getD 0) &&
  ((List.range y.Lam).all fun lam => ropeB c DF tbRef (4 * I.g) lam) &&
  padB y tbRef

/-- A run of the public hypotheses. It calls the verifier's functions in the forms in which the
fields of PubRef name them, and returns the letters if all of them return and the tests pass. -/
def refRun (I : RefIn) : Option RefData := do
  let y ← (layout hKF I.pc).toOption
  let _ ← (scalesHeld hKF I.sc).toOption
  let wsLay ← (wsLayOf (shapeV hKF 202048) true kRef).toOption
  let P ← (Pub.of y I.sc I.rope wsLay I.V' I.tokv I.set).toOption
  let G ← (plansG P).toOption
  let pl ← G[I.g]?
  let r ← layTables (matsR y I.g) (tableAsks y P.rd I.g) 0
  let Zp ← (lastOf I.H.fo.zx y.h.la).toOption
  let zt ← (lastOf I.H.fo.zx y.h.lt).toOption
  let ends ← I.H.fo.zk.mapM fun z => (lastOf z y.h.la).toOption
  let tT ← I.H.tT
  let pts ← pointsOf y I.H I.hd I.hd2
  let funs ← funsOf y I.H.fo pts r.2.1
  let TS ← P.rd.tscCalls.mapM y.callNo
  let pans ← panelsT (I.p y r.1) TS (panelsA (I.p y r.1) {})
  let cl ← (I.c y r.1 wsLay tT.r).weightClaims TS
  let s' ← stackEnd y (placePanels pans.bl).1 I.rs (ceilLog2 (placePanels pans.bl).2)
    (powers I.xo 2) I.H1 I.V I.shownA I.shownB
  let weighed ← y.calls.mapM (I.v y r.1).weighedOf
  let parts ← (y.calls.zip weighed).toList.zipIdx.mapM fun x =>
    (I.v y r.1).joinPart I.H.fo.alpha I.H.fo.theta x.2 x.1.1 x.1.2
  if I.tests y (I.c y r.1 wsLay tT.r) Zp zt ends = true then
    some { pc := I.pc, p := I.p y r.1, c := I.c y r.1 wsLay tT.r, r, Zp, rho := I.rho, ends,
           H := I.H, tT, hd := I.hd, hd2 := I.hd2, pts, funs, V' := I.V', tokv := I.tokv,
           set := I.set, P, G, pl, TS, pans, cl, xo := I.xo, rs := I.rs, H1 := I.H1, V := I.V,
           lam := ceilLog2 (placePanels pans.bl).2, shownA := I.shownA, shownB := I.shownB, s',
           weighed, parts }
  else none

/-- If the run returns letters, the public hypotheses hold of them, where numerals read as
numbers. -/
theorem pubRef_of_run {K : Type} [Field K] {ρ : Reading K} (hρ : Numerals ρ) {I : RefIn}
    {d : RefData} (h : refRun I = some d) : PubRef ρ d := by
  unfold refRun at h
  obtain ⟨y, hy, h⟩ := bind_some h
  obtain ⟨u, hs, h⟩ := bind_some h
  obtain ⟨wsLay, hlw, h⟩ := bind_some h
  obtain ⟨P, hP, h⟩ := bind_some h
  obtain ⟨G, hG, h⟩ := bind_some h
  obtain ⟨pl, hpl, h⟩ := bind_some h
  obtain ⟨r, hl, h⟩ := bind_some h
  obtain ⟨Zp, hZ, h⟩ := bind_some h
  obtain ⟨zt, hzt, h⟩ := bind_some h
  obtain ⟨ends, hm, h⟩ := bind_some h
  obtain ⟨tT, hT, h⟩ := bind_some h
  obtain ⟨pts, hpts, h⟩ := bind_some h
  obtain ⟨funs, hfun, h⟩ := bind_some h
  obtain ⟨TS, hTS, h⟩ := bind_some h
  obtain ⟨pans, hp, h⟩ := bind_some h
  obtain ⟨cl, hcl, h⟩ := bind_some h
  obtain ⟨s', hst, h⟩ := bind_some h
  obtain ⟨weighed, hw, h⟩ := bind_some h
  obtain ⟨parts, hparts, h⟩ := bind_some h
  by_cases ht : I.tests y (I.c y r.1 wsLay tT.r) Zp zt ends = true
  · rw [if_pos ht] at h
    have e := (Option.some.inj h).symm
    subst e
    unfold RefIn.tests at ht
    simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨t1, t2⟩, t3⟩, t4⟩, t5⟩, t6⟩, t7⟩, t8⟩, t9⟩, t10⟩, t11⟩ := ht
    exact
      { hy := ok_of_toOption hy, hs := ok_of_toOption hs, hg := t1, hl := hl, ht := rfl, hρ := hρ,
        hN := t2, hzx := t3, hzy := t4, hzk := t5, he := t6, hZ := ok_of_toOption hZ,
        hzt := t7 ▸ ok_of_toOption hzt, hm := hm, ha := t8, hpt := t9, env := rfl,
        hlw := ok_of_toOption hlw, hcrt := rfl,
        R := fun lam hl' => ropeFits_of_B hρ (List.all_eq_true.mp t10 lam (List.mem_range.mpr hl')),
        hP := ok_of_toOption hP, hG := ok_of_toOption hG, hpl := hpl, hpts := hpts, hfun := hfun,
        hT := hT, hTS := hTS, hp := hp, hcl := hcl, hst := hst, hlam := beq_self_eq_true _,
        hHe := rfl, hw := hw, hparts := hparts, hpad := hpad_of_B hρ t11 }
  · rw [if_neg ht] at h
    cases h

/-! ## At the reference -/

section Ref

variable {EE : Type} [Field EE] [Algebra Cb.Gl.F EE] {ρ : Reading EE} {Wo : World EE}
  {d : RefData} (A : PubRef ρ d) (Mz : Mats ℤ) (Wi : Mat)
  (Hd : ∀ Fn ∈ d.funs,
    Holds ρ Wo d.pl.tl d.p.v.iU3 d.p.v.K3 (fun a i j => ((Mz a i j : ℤ) : EE)) Fn)
  (hh : ℕ → ℕ → EE)
  (hH : letI : Scl := sclOf hKF d.p.v.sc d.p.v.g d.p.v.y.Lam
    ∀ l, l < DF.nl → ∀ j, j < fSh DF l → hh 0 (l * 2 ^ ceilLog2 d.p.v.y.h.f + j) =
      hhU DF (cellsOf DF (cellsAt d.p.v.y fun a i j => ((Mz a i j : ℤ) : EE))) l j
        (zpos DF (zOf ρ d.H.fo.zx d.H.fo.zy)))

include A Hd hH

omit [Algebra Cb.Gl.F EE] in
/-- whole_gpos (Johnson/Road/FormsKeysCaller.lean) at the full-size example's shape and the
library's reference sizes, tables and number of column bits, on integer matrices Mz and an integer
index matrix Wi carried into the field EE. Of the three hypotheses that whole_gpos asks beside
whole_lib's, two are concluded: what the panel QK needs of the sizes is the library's own ref_chOK
(Inst/Model/FF/Objects.lean), and the clause on the shifts of queries and keys follows from the
verifier's test on the file of scales (hk_of_scalesHeld). The third stays: the never-sent vectors
from number 1 on are the honest vectors of the routed gated products at the end point of the second
token sumcheck (hH2). The weight of the second claim is the drawn element xo itself. -/
theorem gpos_ref
    (hH2 : letI : Scl := sclOf hKF d.p.v.sc d.p.v.g d.p.v.y.Lam
      ∀ l', l' < DF.ne → ∀ j, j < DF.fe → hh (1 + l') j =
        hhU DF (cellsOf DF (cellsAt d.p.v.y fun a i j => ((Mz a i j : ℤ) : EE)))
          (2 * l' + 1) (DF.fe + j) (pt ρ d.c.rt)) :
    letI : Scl := sclOf hKF d.p.v.sc d.p.v.g d.p.v.y.Lam
    (startOf d.H (powers d.xo 2) d.parts).value ρ Wo -
        ∑ Y ∈ range (2 ^ d.lam),
          vecOf (aG ρ Wo d.p.v.y (powers d.xo 2) hh) (placePanels d.pans.bl).1.toList Y *
            vecOf (bG ρ Wo (wvOf ρ d.c.wsLay (fun a b => ((Wi a b : ℤ) : EE)) d.cl))
              (placePanels d.pans.bl).1.toList Y =
      ((∑ q : Fin 8, wc DF (zOf ρ d.H.fo.zx d.H.fo.zy) q *
          (ρ.val d.H.fo.alpha - (q.val : EE) * ρ.val d.H.fo.theta -
            Blocks.ext (aC DF q)
              (keyVec DF (cellsOf DF (cellsAt d.p.v.y fun a i j => ((Mz a i j : ℤ) : EE)))
                tbRef (4 * d.p.v.g)
                (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : EE)) (4 * d.p.v.g + l)) q)
              (zc DF (zOf ρ d.H.fo.zx d.H.fo.zy) q))) +
        ρ.val (padOf d.H) - d.H.fo.cEnd.value ρ Wo) +
      (Blocks.ext DF.lT (fun i => Gpos DF
          (cellsOf DF (cellsAt d.p.v.y fun a i j => ((Mz a i j : ℤ) : EE))) tbRef (4 * d.p.v.g)
          (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : EE)) (4 * d.p.v.g + l))
          (zOf ρ d.H.fo.zx d.H.fo.zy) (Blocks.cubePt DF.lT i))
          (zpos DF (zOf ρ d.H.fo.zx d.H.fo.zy)) -
        Wo.slot d.tT.sCl) +
      ρ.val d.xo *
        (d.H.KT.value ρ Wo -
          (Gpos DF (cellsOf DF (cellsAt d.p.v.y fun a i j => ((Mz a i j : ℤ) : EE)))
              tbRef (4 * d.p.v.g)
              (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : EE)) (4 * d.p.v.g + l))
              (zOf ρ d.H.fo.zx d.H.fo.zy) (pt ρ d.c.rt) +
            (Sig1 DF (rOff ρ d.p.v.y d.p.shownT hh DF
                  (cellsOf DF (cellsAt d.p.v.y fun a i j => ((Mz a i j : ℤ) : EE)))
                  (zOf ρ d.H.fo.zx d.H.fo.zy) (pt ρ d.c.rt)) tbRef (4 * d.p.v.g)
                (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : EE)) (4 * d.p.v.g + l))
                (zOf ρ d.H.fo.zx d.H.fo.zy) (pt ρ d.c.rt) -
              Pan.QK.share DF (rTrueP d.p.v.y hh DF
                  (cellsOf DF (cellsAt d.p.v.y fun a i j => ((Mz a i j : ℤ) : EE)))
                  (zOf ρ d.H.fo.zx d.H.fo.zy) (pt ρ d.c.rt)) tbRef (4 * d.p.v.g)
                (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : EE)) (4 * d.p.v.g + l))
                (zOf ρ d.H.fo.zx d.H.fo.zy) (pt ρ d.c.rt)))) := by
  letI : Scl := sclOf hKF d.p.v.sc d.p.v.g d.p.v.y.Lam
  have S := switchesK.2
  obtain ⟨hrd, ⟨s0, hs0, hpt⟩, hsx, hsy, htm, hNM, e⟩ := A.more
  have R := A.R
  obtain ⟨T, T2, Ro, hrt⟩ := worlds_of_holds ρ Wo A.hy S A.hg hrd A.hl A.ht sizedKF.1 A.hZ A.hzt rfl
    A.hcrt htm hNM A.hpts A.hfun A.hT _ Hd
  rw [← e] at R ⊢
  rw [← (powers_two ρ d.xo).2]
  exact whole_gpos A.hy S A.hs A.hg hrd A.hl A.ht A.hρ sizedKF.1 cap_ref A.hN hfl_ref hsx hsy A.hzk
    A.he A.hZ A.hzt A.hm A.ha hs0 hpt A.env sizedW_KF rfl A.hlw rfl hrt R T T2 Ro _ hh
    (ts_eq A.hy S.p3 A.hN hrd A.hTS) A.hp A.hcl (powers_two ρ d.xo).1 A.hst A.hlam d.H A.hHe A.hT
    d.H.fo.alpha d.H.fo.theta A.hw A.hparts A.hpad hH Inst.Model.FFSeg.ref_chOK
    (fun l _ => hk_of_scalesHeld (admitted_of_layout A.hy S.p3) A.hs A.hg DF l) hH2

/-- The capstone at the reference, on the key vectors of the equivalence of
Johnson/Road/FormsKeysPass.lean. At the full-size example's shape hKF, the library's reference sizes
DF, its reference tables tbRef and its number kRef of column bits, with the first layer 4 g of the
group g, on integer matrices Mz and an integer index matrix Wi carried into a field EE over the
library's prime field. Three statements on one and the same eight key vectors, bundled: none follows
from another, and the second and the third read hy and the number of the group alone. First,
capstone (Johnson/Road/FormsKeysCaller.lean): the form that the lookup's end leaves is worth the sum
over the calls of the library's weight of the call times alpha - q theta less the extension of the
key vector at the library's point of the call, plus the padding trees' number, at the lookup's own
alpha and theta. Second, ext_keyVec_addr (Johnson/Road/FormsKeysValid.lean): the extension of each
key vector is that of the key vector on the entries of the matrices at the library's own addresses.
Third, keyVecs_ffKey_file (Johnson/Road/FormsKeysScl.lean, over keyVecs_mem_iff of
Johnson/Road/FormsKeysPass.lean): all entries of the eight vectors below their lengths are images of
entries of their calls' tables exactly if every key of the library's own segment of the group
(Cm.TP.segFF, the letters of the conjunct ffKey of the library's condition in Cm/TargetPRel.lean),
over its prime field, under the table of scales that the library's reading makes of the records into
which fileOf (Johnson/Road/FormsKeysWords.lean) cuts the verifier's scale file by the verifier's kl
and klM, with any final normalisation nf, lies in its table, at a trace t' that holds the integer
cells. The public hypotheses are the fields of the record PubRef (A): the verifier's own lines and
tests at that shape; three comparisons with the library: the lines of calls (hN), the padding keys
(hpad), the rotary tables (R); two lines at letters that a run holds against the example's file: hy
at hKF, which is written by hand, and hlw at shapeV hKF 202048 and the library's kRef; and hρ. The
hypotheses on the world are four, and a choice; they serve the first statement alone. The four:
every table of the reads holds what it says of Mz (Hd); the start form is worth the sum of the
products of the two long vectors (hB0); what the second token sumcheck leaves is worth Sig1 at the
record rPort (hB3); the hidden sum that it claims is ClT (hB2). Each stands for random steps, is
shown by nothing here and is no claim of the verifier's list. The choice: the never-sent vectors hh
are a free letter, and hH fixes number 0 as the honest vector; the numbers from 1 on stay free. From
the first statement, an equation at one point, to the left side of the third, on every entry, lies
the lookup; nothing here leads from one to the other. -/
theorem capstone_ref
    (hB0 : (startOf d.H (powers d.xo 2) d.parts).value ρ Wo =
      ∑ Y ∈ range (2 ^ d.lam),
        vecOf (aG ρ Wo d.p.v.y (powers d.xo 2) hh) (placePanels d.pans.bl).1.toList Y *
          vecOf (bG ρ Wo (wvOf ρ d.c.wsLay (fun a b => ((Wi a b : ℤ) : EE)) d.cl))
            (placePanels d.pans.bl).1.toList Y)
    (hB3 : letI : Scl := sclOf hKF d.p.v.sc d.p.v.g d.p.v.y.Lam
      d.H.KT.value ρ Wo =
        Sig1 DF (rPort ρ d.p.v.y d.p.shownT hh DF
            (cellsOf DF (cellsAt d.p.v.y fun a i j => ((Mz a i j : ℤ) : EE)))
            (zOf ρ d.H.fo.zx d.H.fo.zy) (pt ρ d.c.rt)) tbRef (4 * d.p.v.g)
          (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : EE)) (4 * d.p.v.g + l))
          (zOf ρ d.H.fo.zx d.H.fo.zy) (pt ρ d.c.rt))
    (hB2 : letI : Scl := sclOf hKF d.p.v.sc d.p.v.g d.p.v.y.Lam
      Wo.slot d.tT.sCl =
        ClT DF (cellsOf DF (cellsAt d.p.v.y fun a i j => ((Mz a i j : ℤ) : EE))) tbRef
          (4 * d.p.v.g)
          (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : EE)) (4 * d.p.v.g + l))
          (zOf ρ d.H.fo.zx d.H.fo.zy)) :
    letI : Scl := sclOf hKF d.p.v.sc d.p.v.g d.p.v.y.Lam
    d.H.fo.cEnd.value ρ Wo =
        (∑ q : Fin 8, wc DF (zOf ρ d.H.fo.zx d.H.fo.zy) q *
          (ρ.val d.H.fo.alpha - (q.val : EE) * ρ.val d.H.fo.theta -
            Blocks.ext (aC DF q)
              (keyVec DF (cellsOf DF (cellsAt d.p.v.y fun a i j => ((Mz a i j : ℤ) : EE)))
                tbRef (4 * d.p.v.g)
                (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : EE)) (4 * d.p.v.g + l)) q)
              (zc DF (zOf ρ d.H.fo.zx d.H.fo.zy) q))) +
          ρ.val (padOf d.H) ∧
      (∀ (q : Fin 8) (ξ : ℕ → EE),
        Blocks.ext (aC DF q)
            (keyVec DF (cellsOf DF (cellsAt d.p.v.y fun a i j => ((Mz a i j : ℤ) : EE)))
              tbRef (4 * d.p.v.g)
              (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : EE)) (4 * d.p.v.g + l)) q) ξ =
          Blocks.ext (aC DF q)
            (keyVec DF
              (fun n => atAddr d.p.v.y DF (fun a i j => ((Mz a i j : ℤ) : EE))
                (Inst.Model.FFSeg.addr DF n)) tbRef (4 * d.p.v.g)
              (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : EE)) (4 * d.p.v.g + l)) q)
            ξ) ∧
      ∀ (t' : {n : Cell // n.Valid DF} → ℤ),
        (∀ n, t' n = cellsOf DF (cellsAt d.p.v.y Mz) n.val) →
        ∀ (nf : Inst.Model.NormPar) (tok : ℕ → ℕ),
        ((∀ q : Fin 8, ∀ X, X < 2 ^ aC DF q →
          ∃ u ∈ (Cm.Seg.tabOf (lut tbRef q) (if q = 3 then 8 else 16) : Cb.Tab Cb.Gl.F).set,
            keyVec DF (cellsOf DF (cellsAt d.p.v.y fun a i j => ((Mz a i j : ℤ) : EE)))
              tbRef (4 * d.p.v.g)
              (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : EE)) (4 * d.p.v.g + l)) q X =
              algebraMap Cb.Gl.F EE u) ↔
        ∀ k, (Cm.TP.segFF Cb.Gl.p (scalesOf hKF d.p.v.sc nf).kap (scalesOf hKF d.p.v.sc nf).nf
              d.p.v.g).key tok (Cm.TP.castW Cb.Gl.p Wi) t' k ∈
          (Cm.TP.segFF Cb.Gl.p (scalesOf hKF d.p.v.sc nf).kap (scalesOf hKF d.p.v.sc nf).nf
            d.p.v.g).table k) := by
  letI : Scl := sclOf hKF d.p.v.sc d.p.v.g d.p.v.y.Lam
  have S := switchesK.2
  obtain ⟨hrd, ⟨s0, hs0, hpt⟩, hsx, hsy, htm, hNM, e⟩ := A.more
  have R := A.R
  have h12 : d.p.v.g < 12 := by
    have hN12 : d.p.v.y.NGr = 12 := (admitted_of_layout A.hy S.p3).NGr.trans (by decide)
    have hg := A.hg
    omega
  refine ⟨?_, fun q ξ => ext_keyVec_addr A.hy S rfl sizedKF.1 sizedKF.2 _ tbRef _ _ q ξ,
    fun t' ht' nf tok => ?_⟩
  swap
  · rw [lam_ref A.hy]
    exact keyVecs_ffKey_file d.p.v.y Mz Wi t' ht' hKF d.p.v.sc h12 nf tok
  rw [← e] at R hB3 hB2 ⊢
  exact capstone A.hy S A.hs A.hg hrd A.hl A.ht A.hρ sizedKF.1 cap_ref A.hN hfl_ref hsx hsy A.hzk
    A.he A.hZ A.hzt A.hm A.ha hs0 hpt A.env sizedW_KF rfl A.hlw rfl A.hcrt R htm hNM A.hpts A.hfun
    A.hT _ Hd _ hh A.hTS A.hp A.hcl (powers_two ρ d.xo).1 A.hst A.hlam A.hHe d.H.fo.alpha
    d.H.fo.theta A.hw A.hparts A.hpad hH hB0 hB3 hB2

/-- The first statement of capstone_ref on the library's vector of leaves. Under the hypotheses of
capstone_ref, and the test by which the verifier's caller holds the numbers that the lookup has left
against the layout's (hsh): the form that the lookup's end leaves is worth the extension, at the
point zOf, of the library's vector of leaves of a forest (LkPar.leafK, Blocks/LookupRel.lean) with
the depth, the bits of a tree's number and the number of trees of the reference sizes, at the keys
of the library's trees (forestKey) moved by the number of the tree's call times theta, and at alpha.
The number for the padding trees is 0 there. P0: any record of the library's letters of a lookup; of
it nothing is read. Who reads the target: leaf_ff stands on CallsOK.ext_leafK of
Blocks/LookupCalls.lean, a file that Inst/Model/FF/Objects.lean and other files of this library
import. In Blocks/LookupRel.lean, where leafK is defined, no shift occurs: by a search for the word,
not by reading its theorems. -/
theorem capstone_leaf
    (hB0 : (startOf d.H (powers d.xo 2) d.parts).value ρ Wo =
      ∑ Y ∈ range (2 ^ d.lam),
        vecOf (aG ρ Wo d.p.v.y (powers d.xo 2) hh) (placePanels d.pans.bl).1.toList Y *
          vecOf (bG ρ Wo (wvOf ρ d.c.wsLay (fun a b => ((Wi a b : ℤ) : EE)) d.cl))
            (placePanels d.pans.bl).1.toList Y)
    (hB3 : letI : Scl := sclOf hKF d.p.v.sc d.p.v.g d.p.v.y.Lam
      d.H.KT.value ρ Wo =
        Sig1 DF (rPort ρ d.p.v.y d.p.shownT hh DF
            (cellsOf DF (cellsAt d.p.v.y fun a i j => ((Mz a i j : ℤ) : EE)))
            (zOf ρ d.H.fo.zx d.H.fo.zy) (pt ρ d.c.rt)) tbRef (4 * d.p.v.g)
          (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : EE)) (4 * d.p.v.g + l))
          (zOf ρ d.H.fo.zx d.H.fo.zy) (pt ρ d.c.rt))
    (hB2 : letI : Scl := sclOf hKF d.p.v.sc d.p.v.g d.p.v.y.Lam
      Wo.slot d.tT.sCl =
        ClT DF (cellsOf DF (cellsAt d.p.v.y fun a i j => ((Mz a i j : ℤ) : EE))) tbRef
          (4 * d.p.v.g)
          (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : EE)) (4 * d.p.v.g + l))
          (zOf ρ d.H.fo.zx d.H.fo.zy))
    (hsh : (d.H.fo.shape.dT == d.p.v.y.fo.dT && d.H.fo.shape.kT == d.p.v.y.fo.kT &&
      d.H.fo.shape.NT == d.p.v.y.fo.NT && d.H.fo.shape.rK == d.p.v.y.fo.rK &&
      d.H.fo.shape.first == d.p.v.y.fo.first && d.H.fo.shape.iota == d.p.v.y.fo.iota &&
      d.H.fo.shape.callOf == d.p.v.y.fo.callOf) = true)
    (P0 : Blocks.LkPar EE) :
    letI : Scl := sclOf hKF d.p.v.sc d.p.v.g d.p.v.y.Lam
    d.H.fo.cEnd.value ρ Wo =
      Blocks.ext (Dk DF + sg DF)
        ((lkP P0 DF).leafK
          (tagKey DF (cellsOf DF (cellsAt d.p.v.y fun a i j => ((Mz a i j : ℤ) : EE))) tbRef
            (4 * d.p.v.g)
            (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : EE)) (4 * d.p.v.g + l))
            (ρ.val d.H.fo.theta)) (ρ.val d.H.fo.alpha))
        (zOf ρ d.H.fo.zx d.H.fo.zy) := by
  letI : Scl := sclOf hKF d.p.v.sc d.p.v.g d.p.v.y.Lam
  have C1 := (capstone_ref A Mz Wi Hd hh hH hB0 hB3 hB2).1
  have C2 := sum_is_leaf P0 DF _ tbRef _ _ _ _ _ C1
  rw [padOf_ref ρ A.hy A.hN hsh, add_zero] at C2
  exact C2

end Ref

/-- A fourth statement on the same eight key vectors, at the field Cb.Gl.E, beside capstone_ref: it
reads nothing of that theorem. The left side is the left side of the third statement of capstone_ref
at EE := Cb.Gl.E, to the letter. All entries of the eight vectors below their lengths are images of
entries of their calls' tables exactly if the keys' half of the conditions of segment number 2 g of
the library's model in glued form holds (KeysHold, Johnson/Road/FormsKeysTie.lean: the second of the
two clauses of the library's SegSpec.Holds), at the library's format fmtRef, any public input x, the
index matrix Wi, and the library's matrices libM made from the verifier's integer matrices Mz
(Johnson/Road/FormsKeysDict.lean), under the table of scales scalesOf
(Johnson/Road/FormsKeysScl.lean). By tie_port_file (Johnson/Road/FormsKeysTieP.lean). Asked: the
layout is one for the shape hKF, and g is a group; nothing on a world. Who reads the target, by
reading the library, not by a theorem here: The laws admit and force read Cond whole: all 25
segments, the identities' half too, and a bound on the cells: so nothing here reaches the relation.
The keys' half alone is read by the library's theorem on the lookup's claim before the shift
(ldPartKeys_holds in Cb/Part/LdPartLkpFam.lean), which the front of a segment and the law on the
multiplicities' bits use. No term of this file joins that theorem with this one. -/
theorem keys_glued_ref {pc : List (List String)} {p : PanelEnv} (hy : layout hKF pc = .ok p.v.y)
    (hg : p.v.g < p.v.y.NGr) (Mz : Mats ℤ) (Wi : Mat) (nf : Inst.Model.NormPar)
    (x : Cm.Seg.XI) :
    letI : Scl := sclOf hKF p.v.sc p.v.g p.v.y.Lam
    (∀ q : Fin 8, ∀ X, X < 2 ^ aC DF q →
      ∃ u ∈ (Cm.Seg.tabOf (lut tbRef q) (if q = 3 then 8 else 16) : Cb.Tab Cb.Gl.F).set,
        keyVec DF (cellsOf DF (cellsAt p.v.y fun a i j => ((Mz a i j : ℤ) : Cb.Gl.E)))
            tbRef (4 * p.v.g)
            (fun l => layerR ppref kRef (fun a b => ((Wi a b : ℤ) : Cb.Gl.E)) (4 * p.v.g + l))
            q X =
          algebraMap Cb.Gl.F Cb.Gl.E u) ↔
    KeysHold (Cm.Seg.TS.segM (scalesOf hKF p.v.sc nf) (2 * p.v.g)).glued Cm.Seg.TS.fmtRef x
      (Cm.TP.castW Cb.Gl.p Wi) (Cb.Partition.castM (E := Cb.Gl.E) (libM p.v.y p.v.g Mz)) := by
  have h12 : p.v.g < Inst.Model.All.nGr := by
    have hN12 : p.v.y.NGr = 12 := (admitted_of_layout hy switchesK.2.p3).NGr.trans (by decide)
    show p.v.g < 12
    omega
  rw [lam_ref hy]
  exact tie_port_file hy switchesK.2 sizedKF.1 sizedKF.2 rfl Mz Wi h12 p.v.sc nf x

#print axioms kqkk_of_heldAt
#print axioms hk_of_scalesHeld
#print axioms cap_ref
#print axioms hfl_ref
#print axioms trees_ref
#print axioms lam_ref
#print axioms sizes_of_lines
#print axioms worlds_of_holds
#print axioms PubRef.more
#print axioms ropeFits_of_B
#print axioms hpad_of_B
#print axioms pubRef_of_run
#print axioms gpos_ref
#print axioms capstone_ref
#print axioms sum_is_leaf
#print axioms sum_is_leafAll
#print axioms padOf_value
#print axioms padOf_ref
#print axioms capstone_leaf
#print axioms keys_glued_ref

end OnBytes.Road
