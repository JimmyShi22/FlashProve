-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysPlan.lean: the record of the smallness test in the verifier's own plans has
the list of matrices that the theorems on the tables of the reads ask for; and how the smallness
test's own claims name an entry of the reads.

Part 1. laid1_of_run (Johnson/Road/FormsKeysTab.lean) and the theorems that stand on it, among them
trueAt_of_holds and trueAt2_of_holds, take a record tl of the smallness test's numbers with two
hypotheses: its matrices have the rows and columns of the list of tailsOf (htm), and NM is the
length of its list (hNM). This part shows both for the record in the plan of every group, as the
verifier makes it: plan_sizes.
What is compared with what: texts of the verifier with each other. On the way from tailsOf to the
plan's record the list passes bordersOf, shape with piecesF, addTrees, ownerIs and borderMeans
(OnBytes/Model/LayerPlan.lean, OnBytes/Model/Tail.lean). bordersOf rewrites two fields of a matrix
that is read from another sub-proof, and keeps the order, the number, the rows and the columns. The
others hand the list on. matsR is a definition of Johnson/Road/FormsKeysRun.lean. The library is not
mentioned.
Main theorems: bordersOf_sizes; pieces_keeps, shape_mats, addTrees_keeps, borderMeans_keeps;
planG_sizes; plansFrom_at; plan_sizes.
The hypotheses of plan_sizes, and where they are met: that Pub.of and plansG return. Run at made-up
numbers in Johnson/Road/FormsKeysRunT.lean and at the two shipped examples' files in
Johnson/Road/FormsKeysRunK.lean, which also run the conclusion.

Part 2. The forms and Holds (Johnson/Road/FormsKeysMat.lean) name an entry of the reads by the array
iU3 and its number of columns K3, which the check of a layer sub-proof takes from the plan (hearOwn,
OnBytes/Model/Layer.lean). The smallness test's claim on a read names it by tU and cols (linRead,
readEnts in OnBytes/Model/Tail.lean): tU from the record on which the test runs, cols from the
running list of arrays. That the two are the same comes to three equations: every table of the list
lies in the reads (a theorem: funsOf_inv, Johnson/Road/FormsKeysMet.lean); the record on which the
test runs has the plan's list of arrays; the array has as many columns in the running list, when the
claim is made, as in the plan's. This part has what of the last two can be said without following
the run:
 - closeFuns_keeps: the first step from the plan's record to that record keeps the list of arrays.
 - sizes_K: the check's own test at its start, that the running list has the sizes of the plan's,
   gives each array the same number of columns in both.
 - readEnts_holds: if the table holds what it says, with the reads in the array tU of cols columns,
   the entries that the claim names are worth what the docstring of linRead says that they are meant
   to hold.

What is not claimed. That the later routines of the smallness test keep the list of arrays, and that
no step of the check changes an array's number of columns, is not shown: so no theorem here says tU
= iU3 or cols = K3. The verifier never tests Holds. All numbers of part 1 are public. The program
does not import this file.
-/
import Johnson.Road.FormsKeysCap
import OnBytes.Model.LayerPlan

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open OnBytes.Model (TMat HTailF2 T2Foreign Fork Tail2 Settings)
open OnBytes.Model.Layer (Lay Pub HPlan2 Scales bordersOf planG plansFrom plansG tailsOf)

/-! ## The matrices with their border arrays -/

/-- bordersOf keeps the matrices' order, number, rows and columns. -/
theorem bordersOf_sizes {y : Lay} {ms : Array TMat}
    {r : Array TMat × Array (Option ℕ) × Array T2Foreign} (h : bordersOf y ms = .ok r) :
    (r.1.map fun M => (M.m, M.k)) = ms.map fun M => (M.m, M.k) := by
  unfold bordersOf at h
  obtain ⟨-, h⟩ := ok_of_refuse h
  have e := (Except.ok.inj h).symm
  subst e
  have H : ∀ (l : List (TMat × ℕ))
      (s : Array TMat × Array (Option ℕ) × Array T2Foreign × ℕ),
      ((l.foldl (fun (s : Array TMat × Array (Option ℕ) × Array T2Foreign × ℕ) x =>
        if (x.1.kind == 0 && (x.2 == (Model.Layer.matIx y).iXO ||
            (y.h.p4 && x.2 == (Model.Layer.matIx y).iQA))) = true then
          (s.1.push x.1, s.2.1.push (some s.2.2.2), s.2.2.1, s.2.2.2 + 1)
        else if (x.1.kind == 1) = true then
          (s.1.push { x.1 with foreign := some s.2.2.1.size, ttOff := 0 }, s.2.1.push none,
           s.2.2.1.push { name := "PXf" ++ toString s.2.2.1.size, K := x.1.k, a := 2, m := x.1.m,
                          wp := x.1.wp }, s.2.2.2)
        else (s.1.push x.1, s.2.1.push none, s.2.2.1, s.2.2.2)) s).1.toList.map
          fun M => (M.m, M.k)) =
        (s.1.toList.map fun M => (M.m, M.k)) ++ l.map fun x => (x.1.m, x.1.k) := by
    intro l
    induction l with
    | nil =>
      intro s
      simp
    | cons x l ih =>
      intro s
      rw [List.foldl_cons, ih]
      split_ifs <;> simp
  have h1 := H ms.toList.zipIdx (#[], #[], #[], 0)
  apply Array.ext'
  rw [Array.toList_map, Array.toList_map]
  refine Eq.trans h1 ?_
  have h2 : (ms.toList.zipIdx.map fun x => (x.1.m, x.1.k)) =
      (ms.toList.zipIdx.map (·.1)).map fun M => (M.m, M.k) := by
    rw [List.map_map]
    rfl
  rw [h2, List.zipIdx_map_fst]
  simp

/-! ## The shapes of the smallness test -/

/-- piecesF keeps the list of matrices and its length. -/
theorem pieces_keeps {t t' : HTailF2} (h : t.piecesF = .ok t') :
    t'.mats = t.mats ∧ t'.NM = t.NM := by
  unfold HTailF2.piecesF at h
  obtain ⟨bz, -, h⟩ := ok_of_bind h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨f9, -, h⟩ := ok_of_bind h
  obtain ⟨pub, -, h⟩ := ok_of_bind h
  obtain ⟨-, -, h⟩ := ok_of_bind h
  have e := (Except.ok.inj h).symm
  subst e
  exact ⟨rfl, rfl⟩

/-- shape records the list of matrices that it is given, and its length. -/
theorem shape_mats {tl t' : HTailF2} {m : Array TMat} {txOf : Array (Option ℕ)}
    {f : Array T2Foreign} {hasU : Array Bool} {tau : ℕ}
    (h : tl.shape m txOf f hasU tau = .ok t') : t'.mats = m ∧ t'.NM = m.size := by
  unfold HTailF2.shape HTailF2.shapeF at h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨r1, -, h⟩ := ok_of_bind h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨r2, -, h⟩ := ok_of_bind h
  obtain ⟨r3, -, h⟩ := ok_of_bind h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨-, h⟩ := ok_of_jp h
  exact pieces_keeps h

/-- addTrees keeps the list of matrices and its length. -/
theorem addTrees_keeps {tl : HTailF2} {F : Fork} {T : Tail2} {nU aTX : Array ℕ} {hb hbLine : ℕ}
    {r : HTailF2 × Fork × Tail2} (h : tl.addTrees F T nU aTX hb hbLine = .ok r) :
    r.1.mats = tl.mats ∧ r.1.NM = tl.NM := by
  unfold HTailF2.addTrees HTailF2.addTreesF at h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨r1, -, h⟩ := ok_of_bind h
  obtain ⟨r2, -, h⟩ := ok_of_bind h
  obtain ⟨r3, -, h⟩ := ok_of_bind h
  obtain ⟨r4, -, h⟩ := ok_of_bind h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨r5, -, h⟩ := ok_of_bind h
  obtain ⟨-, h⟩ := ok_of_jp h
  obtain ⟨r6, -, h⟩ := ok_of_bind h
  obtain ⟨-, h⟩ := ok_of_jp h
  have e := (Except.ok.inj h).symm
  subst e
  exact ⟨rfl, rfl⟩

/-- borderMeans keeps the list of matrices and its length. -/
theorem borderMeans_keeps {tl t' : HTailF2} {iF ownerNo index : ℕ}
    (h : tl.borderMeans iF ownerNo index = .ok t') : t'.mats = tl.mats ∧ t'.NM = tl.NM := by
  unfold HTailF2.borderMeans at h
  split at h
  · cases h
  · split at h
    · cases h
    · have e := (Except.ok.inj h).symm
      subst e
      exact ⟨rfl, rfl⟩

/-! ## The plans -/

/-- The record of the smallness test in the plan of group g: its matrices have, in order, the rows
and columns of the list that the public numbers hold for the group, and NM is the list's length. -/
theorem planG_sizes {P : Pub} {g : ℕ} {O : Option HPlan2} {hp : HPlan2}
    (h : planG P g O = .ok hp) :
    (hp.tl.mats.map fun M => (M.m, M.k)) = ((P.tails.getD g {}).mats.map fun M => (M.m, M.k)) ∧
      hp.tl.NM = hp.tl.mats.size := by
  unfold planG at h
  obtain ⟨b, hb, h⟩ := ok_of_bind h
  obtain ⟨t1, h1, h⟩ := ok_of_bind h
  obtain ⟨a, ha, h⟩ := ok_of_bind h
  obtain ⟨Tp, -, h⟩ := ok_of_bind h
  obtain ⟨-, h⟩ := ok_of_refuse h
  obtain ⟨s1, s2⟩ := shape_mats h1
  obtain ⟨a1, a2⟩ := addTrees_keeps ha
  have k2 : hp.tl.mats = a.1.mats ∧ hp.tl.NM = a.1.NM := by
    cases O with
    | none =>
      obtain ⟨-, h⟩ := ok_of_refuse h
      obtain ⟨-, h⟩ := ok_of_refuse h
      have e := (Except.ok.inj h).symm
      subst e
      exact ⟨rfl, rfl⟩
    | some O =>
      cases hb2 : O.tl.ix.TX.back? with
      | none =>
        simp only [hb2] at h
        have h' : (Except.error "internal-g-owner-shape" : Except String HPlan2) = .ok hp := h
        cases h'
      | some t =>
        simp only [hb2] at h
        obtain ⟨-, h⟩ := ok_of_refuse h
        obtain ⟨-, h⟩ := ok_of_refuse h
        obtain ⟨t3, h3, h⟩ := ok_of_bind h
        obtain ⟨pe, -, h⟩ := ok_of_bind h
        obtain ⟨-, h⟩ := ok_of_refuse h
        obtain ⟨-, h⟩ := ok_of_refuse h
        have e := (Except.ok.inj h).symm
        subst e
        have k := borderMeans_keeps h3
        exact k
  rw [k2.1, k2.2, a1, a2, s1, s2]
  exact ⟨bordersOf_sizes hb, rfl⟩

/-- Member i of the plans from group g on is a plan of group g + i. -/
theorem plansFrom_at (P : Pub) : ∀ (n g : ℕ) (O : Option HPlan2) (l : List HPlan2),
    plansFrom P n g O = .ok l → ∀ (i : ℕ) (hp : HPlan2), l[i]? = some hp →
    ∃ O', planG P (g + i) O' = .ok hp
  | 0, g, O, l, h, i, hp, hi => by
    have e : l = [] := (Except.ok.inj h).symm
    subst e
    simp at hi
  | n + 1, g, O, l, h, i, hp, hi => by
    unfold plansFrom at h
    obtain ⟨p, hp1, h⟩ := ok_of_bind h
    obtain ⟨rest, hr, h⟩ := ok_of_bind h
    have e : l = p :: rest := (Except.ok.inj h).symm
    subst e
    cases i with
    | zero =>
      have e2 : p = hp := by simpa using hi
      subst e2
      exact ⟨O, hp1⟩
    | succ i =>
      have hi' : rest[i]? = some hp := by simpa using hi
      obtain ⟨O', hO⟩ := plansFrom_at P n (g + 1) (some p) rest hr i hp hi'
      exact ⟨O', by rw [show g + (i + 1) = g + 1 + i by omega]; exact hO⟩

/-- The two hypotheses that the theorems on the tables of the reads put on the smallness test's
record hold of the verifier's own plans. If Pub.of returns the public numbers P for the layout y and
plansG returns the plans of all groups, then in the plan of each group g the matrices of the
smallness test's list have the rows and columns of the list of tailsOf, and NM is the list's
length. -/
theorem plan_sizes {y : Lay} {sc : Scales} {rope : Array ℕ} {wsLay : Model.WsLay} {V : ℕ}
    {tokv : Array ℕ} {set : Settings} {P : Pub} (hP : Pub.of y sc rope wsLay V tokv set = .ok P)
    {G : Array HPlan2} (hG : plansG P = .ok G) {g : ℕ} {hp : HPlan2} (hg : G[g]? = some hp) :
    (hp.tl.mats.map fun M => (M.m, M.k)) = matsR y g ∧ hp.tl.NM = hp.tl.mats.size := by
  unfold Pub.of at hP
  obtain ⟨-, hP⟩ := ok_of_refuse hP
  obtain ⟨rd, -, hP⟩ := ok_of_bind hP
  have e := (Except.ok.inj hP).symm
  subst e
  unfold plansG at hG
  obtain ⟨l, hl, hG⟩ := ok_of_bind hG
  have e := (Except.ok.inj hG).symm
  subst e
  have hg' : l[g]? = some hp := by simpa using hg
  obtain ⟨O', hO⟩ := plansFrom_at _ _ 0 none l hl g hp hg'
  rw [Nat.zero_add] at hO
  exact planG_sizes hO

/-! ## The entries of the reads, as the smallness test's own claims name them -/

section Reads

variable {K : Type} [Field K] (ρ : Model.Reading K) (W : Model.World K)

/-- Closing the list of tables keeps the list of arrays, the list of matrices and its length. -/
theorem closeFuns_keeps {tl t' : HTailF2} {funs : Array Model.HFun}
    (h : tl.closeFuns funs = some t') : t'.ix = tl.ix ∧ t'.mats = tl.mats ∧ t'.NM = tl.NM := by
  unfold HTailF2.closeFuns at h
  split at h
  · cases h
  · have e := (Option.some.inj h).symm
    subst e
    exact ⟨rfl, rfl, rfl⟩

/-- The test at the start of a layer sub-proof's check that the running list of arrays has the sizes
of the plan's: if it passes, each array has the same number of columns in both lists, looked up as
the check and the smallness test look it up. -/
theorem sizes_K {F F' : Fork}
    (h : ((F.trees.map fun X => (X.R, X.K)) == (F'.trees.map fun X => (X.R, X.K))) = true)
    (i : ℕ) : ((F.trees[i]?).map (·.K)).getD 0 = ((F'.trees[i]?).map (·.K)).getD 0 := by
  have e : (F.trees.map fun X => (X.R, X.K)) = F'.trees.map fun X => (X.R, X.K) := by
    simpa using h
  have e2 := congrArg (fun a : Array (ℕ × ℕ) => ((a[i]?).map (·.2)).getD 0) e
  simpa [Array.getElem?_map, Option.map_map, Function.comp_def] using e2

/-- The entries that a read's claim names. If the table Fn holds in the world W what it says of the
matrices M, with the reads in the array tU of cols columns, then the entries that readEnts appends
for the columns c, .., c + count - 1 are worth, with their coefficients, the sum over these columns
of minus times the column's weight times the sum of the column's entries in the run sg under the
table's weights. -/
theorem readEnts_holds {tl : HTailF2} {Fn : Model.HFun} {sg tU cols : ℕ} {minus : E}
    {gc : Array E} {M : Mats K} (H : Holds ρ W tl tU cols M Fn) :
    ∀ (count c : ℕ) (ents : Array Model.Ent) (b : Bool) (r : Array Model.Ent × Bool),
    tl.readEnts Fn sg tU cols minus gc count c ents b = some r →
    (r.1.toList.map (Model.Ent.value ρ W)).sum = (ents.toList.map (Model.Ent.value ρ W)).sum +
      ∑ i ∈ Finset.range count, ρ.val minus * ρ.val (gc.getD (c + i) zeroE) *
        ∑ j ∈ Finset.range Fn.len, ρ.val (Fn.phi.getD j zeroE) * M Fn.mat (sg * Fn.len + j) (c + i)
  | 0, c, ents, b, r, h => by
    have e : r = (ents, b) := (Option.some.inj h).symm
    subst e
    simp
  | count + 1, c, ents, b, r, h => by
    unfold HTailF2.readEnts at h
    cases hp : tl.tabAt Fn c sg with
    | none =>
      rw [hp] at h
      cases h
    | some pos =>
      rw [hp] at h
      have ih := readEnts_holds H count (c + 1) _ _ r h
      rw [ih, Finset.sum_range_succ', Array.toList_push, List.map_append, List.sum_append]
      have e1 : Model.Ent.value ρ W
          { tree := tU, row := pos / cols, idx := pos % cols,
            coef := mulE minus (gc.getD c zeroE) } =
          ρ.val minus * ρ.val (gc.getD (c + 0) zeroE) *
            ∑ j ∈ Finset.range Fn.len,
              ρ.val (Fn.phi.getD j zeroE) * M Fn.mat (sg * Fn.len + j) (c + 0) := by
        unfold Model.Ent.value
        rw [ρ.mul, Nat.add_zero]
        show _ * W.entry tU (pos / cols) (pos % cols) = _
        rw [H c sg pos hp]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      rw [e1, add_assoc, add_comm (ρ.val minus * _ * _)]
      congr 2
      exact Finset.sum_congr rfl fun i _ => by rw [show c + 1 + i = c + (i + 1) by omega]

end Reads

#print axioms bordersOf_sizes
#print axioms shape_mats
#print axioms addTrees_keeps
#print axioms planG_sizes
#print axioms plan_sizes
#print axioms closeFuns_keeps
#print axioms sizes_K
#print axioms readEnts_holds

end OnBytes.Road
