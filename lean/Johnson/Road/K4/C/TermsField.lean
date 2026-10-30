-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/TermsField.lean: CONDITIONAL.

Not shown here. All that TermsEnds.lean leaves open: among it that the structure which the honest
side's forms read (Sides.v) and the job's point are the verifier's at a run. No example is known.
No property is claimed.

THE END VALUES OF THE SECOND TOKEN SUMCHECK ARE THE WORTHS OF THE VERIFIER's FORMS IN THE READS AT
THE SUMCHECK's POINT, in every world with the true entries, whatever its slots hold. The verifier's
claims on these values are «the slot less a form» (termsForms, OnBytes/Desc/First/K4/Claims.lean):
the reciprocals' forms (rowR at "rt"), the scores' and the selector's (shA at "rt"). A form is
worth x in a world: Aff.value gives x.

  terms_member   end value number e, where claim number e is «a slot less the form x».
  termsForms_at  termsForms by the claims' numbers.
  TermsAt, terms_at   fourteen of the three laws' premises, under one name (they ask hH, hE and, two
                 of them, h3 besides); one end value from it.
  sides_ends     the claims that the honest side holds are termsForms' at its own structure.
  rt_read, sc_read, sel_read   the three runs of end values.
-/
import Johnson.Road.K4.C.TermsEnds
import Johnson.Road.K4.Slots.Readers
import Johnson.Desc.First.ProdV.LevelKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env Heard TableAsk TableAt layTables tableAsks funsOf matIx nEndT)
open OnBytes.Desc.First.K4 (termsForms mapM_range_get)
open OnBytes.Desc.First.K4.Slots (sl_rowR sl_shA)
open OnBytes.Desc.First.K4.Honest (K4Pub K4In Pts Sides Job matsOf jobTermsOn)
open OnBytes.Road.K4 (entryOf)

variable {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}

/-- **End value number e, where claim number e is «a slot less the form x»**, and x names no slot.
-/
theorem terms_member {S : Sides} {J : Job} (hJ : jobTermsOn S = some J)
    (hl : layTables (matsOf S.Q) (tableAsks S.Q.P.y S.Q.P.rd S.Q.g) 0 = some r) (hk : TokAsks S.Q)
    (hy : S.v.y = S.Q.P.y) (hT : S.v.y.T = 2 ^ S.v.y.h.lt) (hlow : S.zlow.size = S.v.y.ls)
    (rs : List E) {e : ℕ} (he : e < nEndT S.v.y) {s : ℕ} {x : Aff}
    (ha : S.ends[e]? = some (Aff.slot s - x)) (hx : ∀ y ∈ x.slots.toList, False)
    {fo' : Forest.Heard} {pts : List (String × Array E)} {tl : HTailF2} {Mm : Mats Cb.Gl.E}
    {G : ℕ → Prop} {funs : Array HFun} (hf : funsOf S.Q.P.y fo' pts r.2.1 = some funs)
    (hp : PtsPart (tokPts S.zlow (J.cube.pointOf rs)) pts)
    (hfo : (∀ i, G i → i ≠ (matIx S.Q.P.y).iB) ∨ fo' = S.fo)
    (hm : (tl.mats.map fun M => (M.m, M.k)) = matsOf S.Q) (hNM : tl.NM = tl.mats.size)
    (hC : CellsOn G (matsOf S.Q) S.w.cell Mm) {W : World Cb.Gl.E}
    (hW : W.entry = entryOf Reading.gl tl funs S.v.iU3 S.v.K3 Mm)
    (hG : ∀ y ∈ (Aff.slot s - x).ents.toList, ∀ z : HFun × ℕ × ℕ, z.1 ∈ funs →
      tl.tabAt z.1 z.2.1 z.2.2 = some (y.row * S.v.K3 + y.idx) → G z.1.mat) :
    Reading.gl.val ((J.ends rs).getD e zeroE) = x.value Reading.gl W := by
  have e1 := terms_true hJ hl hk hy hT hlow rs he ha hf hp hfo hm hNM hC
    (W := { slot := fun _ => 0, entry := W.entry }) hW (fun _ => rfl) hG
  rw [e1, Aff.value_sub, Aff.value_slot]
  show -((0 : Cb.Gl.E) - x.value Reading.gl { slot := fun _ => 0, entry := W.entry }) = _
  rw [zero_sub, neg_neg]
  exact VerifiableInference.Desc.First.ProdV.value_congr Reading.gl x _ W rfl
    fun y hy => (hx y hy).elim

/-- **termsForms by the claims' numbers.** -/
theorem termsForms_at {v : Env} {H : Heard} {tT : Tsc} (hT : H.tT = some tT) {l : List Aff}
    (h : termsForms v H = some l) :
    (∀ i, i < v.y.NN * v.y.Lam → ∃ x, v.rowR "rt" i = some x ∧
      l[i]? = some (Aff.slot (tT.sEnd + i) - x)) ∧
    (∀ lm, lm < v.y.LamM → ∃ x, v.shA "sc" "rt" lm 0 = some x ∧
      l[v.y.NN * v.y.Lam + lm]? = some (Aff.slot (tT.sEnd + v.y.NN * v.y.Lam + lm) - x)) ∧
    (∀ k, k < v.y.LamM * v.y.h.NE → ∃ z,
      v.shA "sel" "rt" (k / v.y.h.NE) (k % v.y.h.NE) = some z ∧
      l[v.y.NN * v.y.Lam + v.y.LamM + k]? =
        some (Aff.slot (tT.sEnd + v.y.NN * v.y.Lam + v.y.LamM + k) - z)) := by
  unfold termsForms at h
  obtain ⟨tT', a0, h⟩ := Option.bind_eq_some_iff.mp h
  obtain rfl : tT = tT' := Option.some.inj (hT.symm.trans a0)
  obtain ⟨a, a1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨b, a2, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨c, a3, h⟩ := Option.bind_eq_some_iff.mp h
  obtain rfl : a ++ b ++ c = l := Option.some.inj h
  have la : a.length = v.y.NN * v.y.Lam := by
    rw [(list_mapM_some _ _ _ a1).1, List.length_range]
  have lb : b.length = v.y.LamM := by
    rw [(list_mapM_some _ _ _ a2).1, List.length_range]
  refine ⟨fun i hi => ?_, fun lm hlm => ?_, fun k hk => ?_⟩
  · obtain ⟨y, hy, hg⟩ := mapM_range_get _ a1 hi
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hy
    refine ⟨x, hx, ?_⟩
    rw [List.getElem?_append_left (by rw [List.length_append, la]; omega),
      List.getElem?_append_left (by rw [la]; exact hi)]
    exact hg
  · obtain ⟨y, hy, hg⟩ := mapM_range_get _ a2 hlm
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hy
    refine ⟨x, hx, ?_⟩
    rw [List.getElem?_append_left (by rw [List.length_append, la, lb]; omega),
      List.getElem?_append_right (by rw [la]; omega), la, Nat.add_sub_cancel_left]
    exact hg
  · obtain ⟨y, hy, hg⟩ := mapM_range_get _ a3 hk
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hy
    refine ⟨x, hx, ?_⟩
    rw [List.getElem?_append_right (by rw [List.length_append, la, lb]; omega),
      List.length_append, la, lb, Nat.add_sub_cancel_left]
    exact hg

/-- **What the three laws below ask**, under one name. S: what the honest side's two jobs share; J:
the second token sumcheck's job; rs: its challenges; W: a world. This defines a hypothesis; the
definition claims nothing. -/
structure TermsAt (S : Sides) (J : Job) (rs : List E) (W : World Cb.Gl.E)
    (r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ) (fo' : Forest.Heard)
    (pts : List (String × Array E)) (tl : HTailF2) (Mm : Mats Cb.Gl.E) (G : ℕ → Prop)
    (funs : Array HFun) : Prop where
  /-- the job is made -/
  job : jobTermsOn S = some J
  /-- the verifier's laying of the tables returns -/
  laid : layTables (matsOf S.Q) (tableAsks S.Q.P.y S.Q.P.rd S.Q.g) 0 = some r
  /-- the families are of the sorts that TokAsk names -/
  asks : TokAsks S.Q
  /-- the forms' structure has the plan's layout -/
  y : S.v.y = S.Q.P.y
  /-- there are 2 ^ lt tokens -/
  T : S.v.y.T = 2 ^ S.v.y.h.lt
  /-- the lookup's low coordinates are ls in number -/
  low : S.zlow.size = S.v.y.ls
  /-- the verifier's list of tables -/
  tables : funsOf S.Q.P.y fo' pts r.2.1 = some funs
  /-- the two points at the job's point stand in the verifier's list of points -/
  part : PtsPart (tokPts S.zlow (J.cube.pointOf rs)) pts
  /-- G names no matrix of the lookup's planes, or the two looks are one -/
  looks : (∀ i, G i → i ≠ (matIx S.Q.P.y).iB) ∨ fo' = S.fo
  /-- the smallness test's list of matrices has the plan's sizes -/
  mats : (tl.mats.map fun M => (M.m, M.k)) = matsOf S.Q
  /-- NM is that list's length -/
  NM : tl.NM = tl.mats.size
  /-- on the matrices that G names the entries are the input's cells -/
  cells : CellsOn G (matsOf S.Q) S.w.cell Mm
  /-- the world's entries are the true ones -/
  entry : W.entry = entryOf Reading.gl tl funs S.v.iU3 S.v.K3 Mm
  /-- each claim's entries lie in tables on matrices that G names -/
  off : ∀ a ∈ S.ends, ∀ y ∈ a.ents.toList, ∀ z : HFun × ℕ × ℕ, z.1 ∈ funs →
    tl.tabAt z.1 z.2.1 z.2.2 = some (y.row * S.v.K3 + y.idx) → G z.1.mat

variable {S : Sides} {J : Job} {rs : List E} {W : World Cb.Gl.E} {fo' : Forest.Heard}
  {pts : List (String × Array E)} {tl : HTailF2} {Mm : Mats Cb.Gl.E} {G : ℕ → Prop}
  {funs : Array HFun}

/-- One end value, from TermsAt. -/
theorem terms_at (A : TermsAt S J rs W r fo' pts tl Mm G funs) {e : ℕ} (he : e < nEndT S.v.y)
    {s : ℕ} {x : Aff} (ha : S.ends[e]? = some (Aff.slot s - x))
    (hx : ∀ y ∈ x.slots.toList, False) :
    Reading.gl.val ((J.ends rs).getD e zeroE) = x.value Reading.gl W :=
  terms_member A.job A.laid A.asks A.y A.T A.low rs he ha hx A.tables A.part A.looks A.mats A.NM
    A.cells A.entry (A.off _ (List.mem_of_getElem? ha))

/-- **The reciprocals' end values.** H0: the structure at which the honest side has made its claims.
-/
theorem rt_read (A : TermsAt S J rs W r fo' pts tl Mm G funs) {H0 : Heard} {tT0 : Tsc}
    (hH : H0.tT = some tT0) (hE : termsForms S.v H0 = some S.ends) :
    ∀ i, i < S.v.y.NN * S.v.y.Lam → ∀ x, S.v.rowR "rt" i = some x →
      Reading.gl.val ((J.ends rs).getD i zeroE) = x.value Reading.gl W := by
  intro i hi x hx
  obtain ⟨x', hx', hg⟩ := (termsForms_at hH hE).1 i hi
  obtain rfl : x = x' := Option.some.inj (hx.symm.trans hx')
  exact terms_at A (by unfold nEndT; omega) hg fun y hy => sl_rowR (S := fun _ => False) hx y hy

/-- **The scores' end values.** -/
theorem sc_read (A : TermsAt S J rs W r fo' pts tl Mm G funs) {H0 : Heard} {tT0 : Tsc}
    (hH : H0.tT = some tT0) (hE : termsForms S.v H0 = some S.ends) (h3 : S.v.y.h.p3 = true) :
    ∀ lm, lm < S.v.y.LamM → ∀ x, S.v.shA "sc" "rt" lm 0 = some x →
      Reading.gl.val ((J.ends rs).getD (S.v.y.NN * S.v.y.Lam + lm) zeroE) =
        x.value Reading.gl W := by
  intro lm hlm x hx
  obtain ⟨x', hx', hg⟩ := (termsForms_at hH hE).2.1 lm hlm
  obtain rfl : x = x' := Option.some.inj (hx.symm.trans hx')
  refine terms_at A ?_ hg fun y hy => sl_shA (S := fun _ => False) hx y hy
  unfold nEndT
  rw [if_pos h3, Nat.mul_add, Nat.mul_one]
  omega

/-- **The selector's end values.** -/
theorem sel_read (A : TermsAt S J rs W r fo' pts tl Mm G funs) {H0 : Heard} {tT0 : Tsc}
    (hH : H0.tT = some tT0) (hE : termsForms S.v H0 = some S.ends) (h3 : S.v.y.h.p3 = true) :
    ∀ k, k < S.v.y.LamM * S.v.y.h.NE → ∀ z,
      S.v.shA "sel" "rt" (k / S.v.y.h.NE) (k % S.v.y.h.NE) = some z →
      Reading.gl.val ((J.ends rs).getD (S.v.y.NN * S.v.y.Lam + S.v.y.LamM + k) zeroE) =
        z.value Reading.gl W := by
  intro k hk z hz
  obtain ⟨z', hz', hg⟩ := (termsForms_at hH hE).2.2 k hk
  obtain rfl : z = z' := Option.some.inj (hz.symm.trans hz')
  refine terms_at A ?_ hg fun y hy => sl_shA (S := fun _ => False) hz y hy
  unfold nEndT
  rw [if_pos h3, Nat.mul_add, Nat.mul_one]
  omega

/-- **The claims that the honest side holds are termsForms' at its own structure.** -/
theorem sides_ends {Q : K4Pub} {w : K4In} {p : Pts} {S : Sides} (h : Sides.of Q w p = some S) :
    ∃ (H0 : Heard) (tT0 : Tsc), H0.tT = some tT0 ∧ termsForms S.v H0 = some S.ends := by
  unfold Sides.of at h
  obtain ⟨v, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨TS, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨Z, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨cls, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hw, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨opens, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨gt, -, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ends, he, h⟩ := Option.bind_eq_some_iff.mp h
  obtain rfl := Option.some.inj h
  exact ⟨_, {}, rfl, he⟩

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.terms_member
#print axioms OnBytes.Road.K4.C.termsForms_at
#print axioms OnBytes.Road.K4.C.terms_at
#print axioms OnBytes.Road.K4.C.rt_read
#print axioms OnBytes.Road.K4.C.sc_read
#print axioms OnBytes.Road.K4.C.sel_read
#print axioms OnBytes.Road.K4.C.sides_ends
