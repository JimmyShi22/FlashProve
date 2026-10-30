-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/StackVal.lean: CONDITIONAL.

Not shown here. All that ValAff.lean leaves open. THAT THE FORM WHICH THE HONEST SIDE VALUES IS THE
VERIFIER's (its panels, challenges and weights) IS NOT SHOWN: a is a free letter. That the world
holds 0 under each slot that the form names (hS) is a hypothesis: the honest side values such a
slot at 0. No example is known. No property is claimed.

THE VALUE THAT THE MAKER OF THE BATCHED SUMCHECK TAKES OF A FORM IS THE FORM's WORTH AT THE TRUE
ENTRIES. StackData.val (Johnson/Desc/K4/Honest/Stack.lean) values a form on the honest reads,
leaving out each entry whose coefficient is 0. With it the maker computes the two sides' end
values.

  valAff_filter   leaving out the entries whose coefficient is 0 does not change the value, read in
                  the field.
  val_true        where StackData.val returns x, x is the form's worth.
-/
import Johnson.Road.K4.C.ValAff
import Johnson.Road.K4.C.Fold
import Johnson.Desc.K4.Honest.Stack

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env TableAsk TableAt layTables tableAsks funsOf matIx)
open OnBytes.Desc.First.K4.Honest (K4Pub K4In Reads StackData matsOf readsAt valAff affFits)
open OnBytes.Road.K4 (entryOf)

/-- Leaving out the entries whose coefficient is 0 does not change the value. -/
theorem valAff_filter (v : Env) (R : Reads) (slot : ℕ → E) (a : Aff) :
    Reading.gl.val (valAff v R slot { a with ents := a.ents.filter fun x => !isZeroE x.coef }) =
      Reading.gl.val (valAff v R slot a) := by
  have key : ∀ (l : List Ent) (s s' : E), Reading.gl.val s = Reading.gl.val s' →
      Reading.gl.val ((l.filter fun x => !isZeroE x.coef).foldl (fun s x =>
        if x.tree == v.iU3 then maddE s x.coef (R.u3 (x.row * v.K3 + x.idx)) else s) s) =
      Reading.gl.val (l.foldl (fun s x =>
        if x.tree == v.iU3 then maddE s x.coef (R.u3 (x.row * v.K3 + x.idx)) else s) s') := by
    intro l
    induction l with
    | nil =>
      intro s s' h
      exact h
    | cons x l ih =>
      intro s s' h
      rw [List.foldl_cons]
      by_cases c : isZeroE x.coef = true
      · rw [List.filter_cons_of_neg (by rw [c]; exact Bool.false_ne_true)]
        refine ih _ _ ?_
        by_cases d : (x.tree == v.iU3) = true
        · have z : Reading.gl.val x.coef = 0 := Slice.readE_of_isZeroE x.coef c
          rw [if_pos d, gl_maddE, z, zero_mul, add_zero]
          exact h
        · rw [if_neg d]
          exact h
      · rw [List.filter_cons_of_pos (by rw [Bool.not_eq_true] at c; rw [c]; rfl), List.foldl_cons]
        refine ih _ _ ?_
        by_cases d : (x.tree == v.iU3) = true
        · rw [if_pos d, if_pos d, gl_maddE, gl_maddE, h]
        · rw [if_neg d, if_neg d]
          exact h
  show Reading.gl.val ((a.ents.filter fun x => !isZeroE x.coef).foldl (fun s x =>
      if x.tree == v.iU3 then maddE s x.coef (R.u3 (x.row * v.K3 + x.idx)) else s)
    (a.slots.foldl (fun s x => maddE s x.2 (slot x.1)) a.const)) =
    Reading.gl.val (a.ents.foldl (fun s x =>
      if x.tree == v.iU3 then maddE s x.coef (R.u3 (x.row * v.K3 + x.idx)) else s)
    (a.slots.foldl (fun s x => maddE s x.2 (slot x.1)) a.const))
  rw [← Array.foldl_toList, ← Array.foldl_toList (xs := a.ents), Array.toList_filter]
  exact key _ _ _ rfl

/-- **Where the maker's function returns x, x is the form's worth at the true entries.** -/
theorem val_true {Q : K4Pub} {w : K4In} {fo fo' : Forest.Heard} {pt pts : List (String × Array E)}
    {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ} {tl : HTailF2} {Mm : Mats Cb.Gl.E}
    {G : ℕ → Prop} {funs : Array HFun} {D : StackData} (hR : readsAt Q w fo pt = some D.R)
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r)
    (hf : funsOf Q.P.y fo' pts r.2.1 = some funs) (hp : PtsPart pt pts)
    (hfo : (∀ i, G i → i ≠ (matIx Q.P.y).iB) ∨ fo' = fo)
    (hm : (tl.mats.map fun M => (M.m, M.k)) = matsOf Q) (hNM : tl.NM = tl.mats.size)
    (hC : CellsOn G (matsOf Q) w.cell Mm) {a : Aff} {x : E} {W : World Cb.Gl.E}
    (h : D.val a = some x) (hW : W.entry = entryOf Reading.gl tl funs D.S.v.iU3 D.S.v.K3 Mm)
    (hS : ∀ s ∈ a.slots.toList, W.slot s.1 = 0)
    (hG : ∀ e ∈ a.ents.toList, ∀ z : HFun × ℕ × ℕ, z.1 ∈ funs →
      tl.tabAt z.1 z.2.1 z.2.2 = some (e.row * D.S.v.K3 + e.idx) → G z.1.mat) :
    Reading.gl.val x = a.value Reading.gl W := by
  unfold StackData.val at h
  by_cases c : affFits D.S.v D.R a = true
  · rw [if_pos c] at h
    rw [← Option.some.inj h, valAff_filter]
    exact valAff_true hR hl hf hp hfo hm hNM hC c hW
      (fun s hs => by rw [hS s hs, Reading.gl.zero]) hG
  · rw [if_neg c] at h
    cases h

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.valAff_filter
#print axioms OnBytes.Road.K4.C.val_true
