-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/ValAff.lean: CONDITIONAL.

Not shown here. All that Reads.lean leaves open. That the world's slots hold the values at which
the honest side values a form (hS) is a hypothesis: WHERE THE HONEST SIDE VALUES A CLAIM «A SLOT
LESS A FORM» AT 0 UNDER EVERY SLOT, hS FAILS IN A WORLD THAT HOLDS THE SLOT's VALUE: such a use
goes through a world with the same entries and 0 under every slot. THAT A FORM's ENTRIES LIE OFF
THE MATRIX OF THE LOOKUP's PLANES (hG) IS A HYPOTHESIS: the honest side's test affFits does not say
it. No example is known. No property is claimed.

A FORM's VALUE ON THE HONEST READS IS ITS WORTH AT THE TRUE ENTRIES. The honest side of the
sub-protocol K4 values a form of the verifier on its own reads and on given values of the hidden
scalars (valAff, Johnson/Desc/K4/Honest/Cells.lean). A form is worth x in a world: Aff.value gives
x (OnBytes/Model/HideLaws.lean).

  valAff_value   the two agree, read in the field, in every world whose slots and entries hold what
                 the honest side reads at the slots and entries that the form names.
  valAff_true    the same in a world whose entries are the true ones (entryOf).
  valAff_heard   the same at what a hearing has returned (entryTrue).
-/
import Johnson.Road.K4.C.Reads
import Johnson.Road.K4.C.Fold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Env Own TableAsk TableAt layTables tableAsks funsOf matIx)
open OnBytes.Desc.First.K4.Honest (K4Pub K4In Reads matsOf readsAt valAff affFits)
open OnBytes.Road.K4 (entryOf entryTrue)

/-- **A form's value on given reads is its worth**, in every world that holds these reads and these
values of the hidden scalars where the form names them. -/
theorem valAff_value {v : Env} {R : Reads} {slot : ℕ → E} {a : Aff} {W : World Cb.Gl.E}
    (hfit : affFits v R a = true)
    (hE : ∀ x ∈ a.ents.toList,
      W.entry v.iU3 x.row x.idx = Reading.gl.val (R.u3 (x.row * v.K3 + x.idx)))
    (hS : ∀ x ∈ a.slots.toList, W.slot x.1 = Reading.gl.val (slot x.1)) :
    Reading.gl.val (valAff v R slot a) = a.value Reading.gl W := by
  have hall : ∀ x ∈ a.ents.toList, (x.tree == v.iU3) = true := by
    unfold affFits at hfit
    rw [← Array.all_toList, List.all_eq_true] at hfit
    intro x hx
    have h1 := hfit x hx
    rw [Bool.and_eq_true] at h1
    exact h1.1
  have hents : ∀ (l : List Ent) (s : E), (∀ x ∈ l, (x.tree == v.iU3) = true ∧
      W.entry v.iU3 x.row x.idx = Reading.gl.val (R.u3 (x.row * v.K3 + x.idx))) →
      Reading.gl.val (l.foldl (fun s x =>
        if x.tree == v.iU3 then maddE s x.coef (R.u3 (x.row * v.K3 + x.idx)) else s) s) =
      Reading.gl.val s + (l.map (Ent.value Reading.gl W)).sum := by
    intro l
    induction l with
    | nil =>
      intro s _
      simp
    | cons x l ih =>
      intro s h
      obtain ⟨h1, h2⟩ := h x List.mem_cons_self
      have e : Ent.value Reading.gl W x =
          Reading.gl.val x.coef * Reading.gl.val (R.u3 (x.row * v.K3 + x.idx)) := by
        unfold Ent.value
        rw [eq_of_beq h1, h2]
      rw [List.foldl_cons, if_pos h1, ih _ (fun y hy => h y (List.mem_cons_of_mem _ hy)), gl_maddE,
        List.map_cons, List.sum_cons, e, add_assoc]
  have hslots : (a.slots.toList.map fun x : ℕ × E =>
      Reading.gl.val x.2 * Reading.gl.val (slot x.1)) =
      a.slots.toList.map (slotValue Reading.gl W) := by
    refine List.map_congr_left fun x hx => ?_
    unfold slotValue
    rw [hS x hx]
  show Reading.gl.val (a.ents.foldl (fun s x =>
      if x.tree == v.iU3 then maddE s x.coef (R.u3 (x.row * v.K3 + x.idx)) else s)
    (a.slots.foldl (fun s x => maddE s x.2 (slot x.1)) a.const)) = _
  rw [← Array.foldl_toList, ← Array.foldl_toList,
    hents _ _ (fun x hx => ⟨hall x hx, hE x hx⟩),
    gl_foldl_maddE (fun x : ℕ × E => x.2) (fun x => slot x.1), hslots]
  unfold Aff.value
  ring

/-- **A form's value on the honest reads is its worth at the true entries.** -/
theorem valAff_true {Q : K4Pub} {w : K4In} {fo fo' : Forest.Heard}
    {pt pts : List (String × Array E)} {R : Reads}
    {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ} {tl : HTailF2}
    {Mm : Mats Cb.Gl.E} {G : ℕ → Prop} {funs : Array HFun} {v : Env}
    (hR : readsAt Q w fo pt = some R)
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r)
    (hf : funsOf Q.P.y fo' pts r.2.1 = some funs) (hp : PtsPart pt pts)
    (hfo : (∀ i, G i → i ≠ (matIx Q.P.y).iB) ∨ fo' = fo)
    (hm : (tl.mats.map fun M => (M.m, M.k)) = matsOf Q) (hNM : tl.NM = tl.mats.size)
    (hC : CellsOn G (matsOf Q) w.cell Mm) {slot : ℕ → E} {a : Aff} {W : World Cb.Gl.E}
    (hfit : affFits v R a = true) (hW : W.entry = entryOf Reading.gl tl funs v.iU3 v.K3 Mm)
    (hS : ∀ x ∈ a.slots.toList, W.slot x.1 = Reading.gl.val (slot x.1))
    (hG : ∀ x ∈ a.ents.toList, ∀ z : HFun × ℕ × ℕ, z.1 ∈ funs →
      tl.tabAt z.1 z.2.1 z.2.2 = some (x.row * v.K3 + x.idx) → G z.1.mat) :
    Reading.gl.val (valAff v R slot a) = a.value Reading.gl W := by
  have hhas : ∀ x ∈ a.ents.toList, R.has (x.row * v.K3 + x.idx) = true := by
    have h0 := hfit
    unfold affFits at h0
    rw [← Array.all_toList, List.all_eq_true] at h0
    intro x hx
    have h1 := h0 x hx
    rw [Bool.and_eq_true] at h1
    exact h1.2
  refine valAff_value hfit (fun x hx => ?_) hS
  rw [hW]
  exact reads_entry hR hl hf hp hfo hm hNM hC v.iU3 v.K3 (hhas x hx) (hG x hx)

/-- The same at what a hearing has returned: in a world whose entries are entryTrue's. -/
theorem valAff_heard {Q : K4Pub} {w : K4In} {fo fo' : Forest.Heard}
    {pt pts : List (String × Array E)} {R : Reads}
    {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ} {tl : HTailF2}
    {Mm : Mats Cb.Gl.E} {G : ℕ → Prop} {o : Own} (hR : readsAt Q w fo pt = some R)
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r)
    (hf : funsOf Q.P.y fo' pts r.2.1 = some o.funs) (hp : PtsPart pt pts)
    (hfo : (∀ i, G i → i ≠ (matIx Q.P.y).iB) ∨ fo' = fo)
    (hm : (tl.mats.map fun M => (M.m, M.k)) = matsOf Q) (hNM : tl.NM = tl.mats.size)
    (hC : CellsOn G (matsOf Q) w.cell Mm) {slot : ℕ → E} {a : Aff} {W : World Cb.Gl.E}
    (hfit : affFits o.v R a = true) (hW : W.entry = entryTrue tl o Mm)
    (hS : ∀ x ∈ a.slots.toList, W.slot x.1 = Reading.gl.val (slot x.1))
    (hG : ∀ x ∈ a.ents.toList, ∀ z : HFun × ℕ × ℕ, z.1 ∈ o.funs →
      tl.tabAt z.1 z.2.1 z.2.2 = some (x.row * o.v.K3 + x.idx) → G z.1.mat) :
    Reading.gl.val (valAff o.v R slot a) = a.value Reading.gl W :=
  valAff_true hR hl hf hp hfo hm hNM hC hfit hW hS hG

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.valAff_value
#print axioms OnBytes.Road.K4.C.valAff_true
#print axioms OnBytes.Road.K4.C.valAff_heard
