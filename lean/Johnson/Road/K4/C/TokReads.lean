-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/TokReads.lean: CONDITIONAL.

Not shown here. That the families of the verifier's list are of the sorts that TokAsk names
(TokAsks): a hypothesis on public names. That layTables returns, and readsAt at the point and at
every corner. Nothing on any matrices but the input's own cells. No example is known. No property
is claimed.

THE HONEST READS AT A TOKEN POINT ARE THE COMBINATION, UNDER THE POINT's EQUALITY WEIGHTS, OF THE
HONEST READS AT THE TOKENS; AND SO IS A FORM's VALUE ON THEM. The honest side of the sub-protocol
K4 makes the tables of the second token sumcheck token by token: at token t it lays the reads at
the corner t and values the verifier's forms there (Johnson/Desc/K4/Honest/Terms.lean, tokenRows).
Here: read in the field, an entry of the reads at a point z, and a form's value on them, is the sum
over the tokens t of eq(z, t) times the same at the corner t.

  phiOf_planes, phiOf_lacks, fit_found   phiOf and wtsFit, opened.
  phi_tok        a family's weights at z and at the corners; the test wtsFit at the corners.
  TokAsks        every family of the verifier's list is of a sort that TokAsk names.
  place_lt       the place of a column and a run lies inside the part's table.
  reads_tok      an entry of the reads.
  valAff_sum     a form's value as a sum, at any reads.
  valAff_tok     a form's value.
-/
import Johnson.Road.K4.C.ReadsKit
import Johnson.Road.K4.C.TokWeights
import Johnson.Road.FormsKeysMerge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.C
open Finset
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Lay Env TableAsk TableAt layTables tableAsks phiOf)
open OnBytes.Desc.First.K4.Honest (K4Pub K4In Reads matsOf readsAt wtsFit valAff affFits)

local notation "cornerAt" => OnBytes.Desc.First.K4.Honest.bitsOf

/-- The weights of a family with one of the three names do not read the list of points. -/
theorem phiOf_planes {y : Lay} {fo : Forest.Heard} (pt pt' : List (String × Array E))
    {a : TableAsk} (hn : ¬ Named a) : phiOf y fo pt a = phiOf y fo pt' a := by
  unfold phiOf
  by_cases c0 : (a.name == "b-bits-0") = true
  · rw [if_pos c0, if_pos c0]
  rw [if_neg c0, if_neg c0]
  by_cases c1 : (a.name == "b-bits-1") = true
  · rw [if_pos c1, if_pos c1]
  rw [if_neg c1, if_neg c1]
  by_cases c2 : (a.name == "b-pin") = true
  · rw [if_pos c2, if_pos c2]
  exact absurd ⟨Bool.eq_false_iff.mpr c0, Bool.eq_false_iff.mpr c1, Bool.eq_false_iff.mpr c2⟩ hn

/-- A family with none of the three names has no weights where its point is not found. -/
theorem phiOf_lacks {y : Lay} {fo : Forest.Heard} {pt : List (String × Array E)} {a : TableAsk}
    (hn : Named a) (hf : (pt.find? fun q => q.1 == a.point) = none) : phiOf y fo pt a = none := by
  unfold phiOf
  rw [hn.1, hn.2.1, hn.2.2, hf]
  rfl

/-- The honest side's test where the family's point has a name and is found. -/
theorem fit_found {y : Lay} {fo : Forest.Heard} {pt : List (String × Array E)} {a : TableAsk}
    (he : a.point.isEmpty = false) {p : String × Array E}
    (hf : (pt.find? fun q => q.1 == a.point) = some p) :
    wtsFit y fo pt a =
      if a.lng then p.2.size == y.h.la && y.ls + y.h.lt == y.h.la && a.L == 2 ^ y.h.la
      else p.2.size == y.h.lt && a.L == 2 ^ y.h.lt := by
  unfold wtsFit
  rw [he, hf]
  rfl

/-- **A family's weights at a token point and at the corners.** -/
theorem phi_tok {y : Lay} {fo : Forest.Heard} {zlow z : Array E} {a : TableAsk} (hk : TokAsk a)
    (hok : AskOk a) (hlow : zlow.size = y.ls) (hz : z.size = y.h.lt)
    (hfit : wtsFit y fo (tokPts zlow z) a = true) :
    ∃ (φz : Array E) (φ : ℕ → Array E), phiOf y fo (tokPts zlow z) a = some φz ∧
      (∀ t, t < 2 ^ y.h.lt → phiOf y fo (tokPts zlow (cornerAt y.h.lt t)) a = some (φ t) ∧
        wtsFit y fo (tokPts zlow (cornerAt y.h.lt t)) a = true) ∧
      ∀ j, j < a.L → Reading.gl.val (φz.getD j zeroE) =
        ∑ t ∈ range (2 ^ y.h.lt), Blocks.eqN y.h.lt 0 (pt Reading.gl z) t *
          Reading.gl.val ((φ t).getD j zeroE) := by
  by_cases hn : Named a
  · rcases hk.resolve_left (not_not.mpr hn) with ⟨hp, hl⟩ | ⟨hp, hl⟩ | ⟨h1, h2⟩
    · -- a short table at "rt"
      have he : a.point.isEmpty = false := by rw [hp]; rfl
      have hfd : ∀ x : Array E,
          ((tokPts zlow x).find? fun q => q.1 == a.point) = some ("rt", x) := by
        intro x
        rw [hp]
        exact find_rt zlow x
      rw [fit_found he (hfd z), hl, if_neg Bool.false_ne_true] at hfit
      simp only [Bool.and_eq_true, beq_iff_eq] at hfit
      obtain ⟨-, hL⟩ := hfit
      have ph : ∀ x : Array E, x.size = y.h.lt → phiOf y fo (tokPts zlow x) a = some (eqTab x) := by
        intro x hx
        rw [phiOf_at hn (hfd x) (by rw [hl, if_neg Bool.false_ne_true]; exact hx), hl,
          if_neg Bool.false_ne_true]
      refine ⟨eqTab z, fun t => eqTab (cornerAt y.h.lt t), ph z hz, fun t _ => ⟨ph _
        (cornerAt_size _ _), ?_⟩, fun j hj => tok_short hz (by rw [← hL]; exact hj)⟩
      rw [fit_found he (hfd _), hl, if_neg Bool.false_ne_true]
      simp only [Bool.and_eq_true, beq_iff_eq]
      exact ⟨cornerAt_size _ _, hL⟩
    · -- a long table at "Y"
      have he : a.point.isEmpty = false := by rw [hp]; rfl
      have hfd : ∀ x : Array E, ((tokPts zlow x).find? fun q => q.1 == a.point) =
          some ("Y", longPoint zlow x) := by
        intro x
        rw [hp]
        exact find_Y zlow x
      have hsz : ∀ x : Array E, x.size = y.h.lt → (longPoint zlow x).size = y.ls + y.h.lt := by
        intro x hx
        unfold longPoint
        rw [Array.size_append, hlow, hx]
      rw [fit_found he (hfd z), hl, if_pos rfl] at hfit
      simp only [Bool.and_eq_true, beq_iff_eq] at hfit
      obtain ⟨⟨-, hla⟩, hL⟩ := hfit
      have ph : ∀ x : Array E, x.size = y.h.lt → phiOf y fo (tokPts zlow x) a =
          some (longPhi (longPoint zlow x) y.ls y.h.lt) := by
        intro x hx
        rw [phiOf_at hn (hfd x) (by rw [hl, if_pos rfl, ← hla]; exact hsz x hx), hl, if_pos rfl]
      refine ⟨_, fun t => longPhi (longPoint zlow (cornerAt y.h.lt t)) y.ls y.h.lt, ph z hz,
        fun t _ => ⟨ph _ (cornerAt_size _ _), ?_⟩,
        fun j hj => tok_long hlow hz (by rw [hla, ← hL]; exact hj)⟩
      rw [fit_found he (hfd _), hl, if_pos rfl]
      simp only [Bool.and_eq_true, beq_iff_eq]
      exact ⟨⟨by rw [← hla]; exact hsz _ (cornerAt_size _ _), hla⟩, hL⟩
    · -- a point that is not in the list
      exfalso
      have hfd := find_none zlow z h1 h2
      unfold wtsFit at hfit
      rw [phiOf_lacks hn hfd, hfd] at hfit
      by_cases he : a.point.isEmpty = true
      · rw [if_pos he] at hfit
        cases hfit
      · rw [if_neg he] at hfit
        cases hfit
  · -- a family on the planes' matrix
    have he : a.point.isEmpty = true := hok.resolve_right hn
    have hw : ∀ x : Array E, wtsFit y fo (tokPts zlow x) a =
        (phiOf y fo (tokPts zlow x) a).any fun phi => phi.size == a.L := by
      intro x
      unfold wtsFit
      rw [if_pos he]
    cases hq : phiOf y fo (tokPts zlow z) a with
    | none =>
      rw [hw, hq] at hfit
      cases hfit
    | some φz =>
      refine ⟨φz, fun _ => φz, rfl, fun t _ => ?_, fun j _ => ?_⟩
      · have e := phiOf_planes (y := y) (fo := fo) (tokPts zlow (cornerAt y.h.lt t))
          (tokPts zlow z) hn
        refine ⟨e.trans hq, ?_⟩
        rw [hw, e, ← hw]
        exact hfit
      · rw [← Finset.sum_mul, sum_eqN_one, one_mul]

/-- Every family of the verifier's list is of a sort that TokAsk names. This defines a hypothesis;
the definition claims nothing. -/
def TokAsks (Q : K4Pub) : Prop := ∀ a ∈ tableAsks Q.P.y Q.P.rd Q.g, TokAsk a

/-- The place of a column and a run lies inside the part's table. -/
theorem place_lt (mats : Array (ℕ × ℕ)) (L M : ℕ) {c sg : ℕ} (hc : c < (mats.getD M (0, 0)).2)
    (hsg : sg < (mats.getD M (0, 0)).1 / L) :
    c * ((mats.getD M (0, 0)).1 / L) + sg < wd mats L M := by
  show _ < (mats.getD M (0, 0)).2 * ((mats.getD M (0, 0)).1 / L)
  calc c * ((mats.getD M (0, 0)).1 / L) + sg
      < (c + 1) * ((mats.getD M (0, 0)).1 / L) := by rw [Nat.succ_mul]; omega
    _ ≤ (mats.getD M (0, 0)).2 * ((mats.getD M (0, 0)).1 / L) := Nat.mul_le_mul_right _ hc

variable {Q : K4Pub} {w : K4In} {fo : Forest.Heard} {zlow z : Array E}
  {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ} {Rz : Reads} {Rt : ℕ → Reads}

/-- **An entry of the honest reads at a token point.** Rz: the reads at z; Rt t: at the corner t. -/
theorem reads_tok (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r)
    (hk : TokAsks Q) (hlow : zlow.size = Q.P.y.ls) (hz : z.size = Q.P.y.h.lt)
    (hRz : readsAt Q w fo (tokPts zlow z) = some Rz)
    (hRt : ∀ t, t < 2 ^ Q.P.y.h.lt →
      readsAt Q w fo (tokPts zlow (cornerAt Q.P.y.h.lt t)) = some (Rt t))
    {pos : ℕ} (hh : Rz.has pos = true) :
    (∀ t, t < 2 ^ Q.P.y.h.lt → (Rt t).has pos = true) ∧
      Reading.gl.val (Rz.u3 pos) = ∑ t ∈ range (2 ^ Q.P.y.h.lt),
        Blocks.eqN Q.P.y.h.lt 0 (pt Reading.gl z) t * Reading.gl.val ((Rt t).u3 pos) := by
  obtain ⟨-, L2⟩ := laid_of_layTables _ _ _ _ hl
  obtain ⟨q, hq, m, hmq, c, sg, hc, hsg, rfl⟩ := place_of_has hRz hl hh
  have hask : q.1 ∈ tableAsks Q.P.y Q.P.rd Q.g := by
    rw [← L2]
    exact List.mem_map.mpr ⟨q, hq, rfl⟩
  have hj := place_lt (matsOf Q) q.1.L m.1 hc hsg
  have hfit : wtsFit Q.P.y fo (tokPts zlow z) q.1 = true := by
    rw [← (fam_at hRz hl hq hmq hj).2.1]
    exact hh
  obtain ⟨φz, φ, pz, pc, lin⟩ := phi_tok (hk _ hask) (ask_ok hask) hlow hz hfit
  have hast : ∀ t, t < 2 ^ Q.P.y.h.lt → (Rt t).has
      (m.2 + (c * (((matsOf Q).getD m.1 (0, 0)).1 / q.1.L) + sg)) = true := by
    intro t ht
    rw [(fam_at (hRt t ht) hl hq hmq hj).2.1]
    exact (pc t ht).2
  refine ⟨hast, ?_⟩
  rw [reads_sum hRz hl (fun _ _ h => h) hq hmq rfl hc hsg hh (Or.inr rfl) pz]
  have each : ∀ t ∈ range (2 ^ Q.P.y.h.lt), Blocks.eqN Q.P.y.h.lt 0 (pt Reading.gl z) t *
      Reading.gl.val ((Rt t).u3 (m.2 + (c * (((matsOf Q).getD m.1 (0, 0)).1 / q.1.L) + sg))) =
      ∑ j ∈ range q.1.L, Blocks.eqN Q.P.y.h.lt 0 (pt Reading.gl z) t *
        (Reading.gl.val ((φ t).getD j zeroE) *
          Reading.gl.val (ofF (w.cell m.1 (sg * q.1.L + j) c))) := by
    intro t ht
    have ht' := mem_range.mp ht
    rw [reads_sum (hRt t ht') hl (fun _ _ h => h) hq hmq rfl hc hsg (hast t ht') (Or.inr rfl)
      (pc t ht').1, Finset.mul_sum]
  rw [sum_congr rfl each, Finset.sum_comm]
  refine sum_congr rfl fun j hj' => ?_
  rw [lin j (mem_range.mp hj'), Finset.sum_mul]
  exact sum_congr rfl fun t _ => by ring

/-- **A form's value as a sum**, at any reads. -/
theorem valAff_sum (v : Env) (R : Reads) (slot : ℕ → E) (a : Aff) :
    Reading.gl.val (valAff v R slot a) =
      Reading.gl.val a.const +
        (a.slots.toList.map fun x => Reading.gl.val x.2 * Reading.gl.val (slot x.1)).sum +
        (a.ents.toList.map fun x => if x.tree == v.iU3 then
          Reading.gl.val x.coef * Reading.gl.val (R.u3 (x.row * v.K3 + x.idx)) else 0).sum := by
  have hents : ∀ (l : List Ent) (s : E),
      Reading.gl.val (l.foldl (fun s x =>
        if x.tree == v.iU3 then maddE s x.coef (R.u3 (x.row * v.K3 + x.idx)) else s) s) =
      Reading.gl.val s + (l.map fun x => if x.tree == v.iU3 then
        Reading.gl.val x.coef * Reading.gl.val (R.u3 (x.row * v.K3 + x.idx)) else 0).sum := by
    intro l
    induction l with
    | nil =>
      intro s
      simp
    | cons x l ih =>
      intro s
      rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]
      by_cases d : (x.tree == v.iU3) = true
      · rw [if_pos d, if_pos d, gl_maddE, add_assoc]
      · rw [if_neg d, if_neg d, zero_add]
  show Reading.gl.val (a.ents.foldl (fun s x =>
      if x.tree == v.iU3 then maddE s x.coef (R.u3 (x.row * v.K3 + x.idx)) else s)
    (a.slots.foldl (fun s x => maddE s x.2 (slot x.1)) a.const)) = _
  rw [← Array.foldl_toList, ← Array.foldl_toList, hents,
    gl_foldl_maddE (fun x : ℕ × E => x.2) (fun x => slot x.1)]

/-- **A form's value on the honest reads at a token point.** -/
theorem valAff_tok (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r)
    (hk : TokAsks Q) (hlow : zlow.size = Q.P.y.ls) (hz : z.size = Q.P.y.h.lt)
    (hRz : readsAt Q w fo (tokPts zlow z) = some Rz)
    (hRt : ∀ t, t < 2 ^ Q.P.y.h.lt →
      readsAt Q w fo (tokPts zlow (cornerAt Q.P.y.h.lt t)) = some (Rt t))
    {v : Env} {slot : ℕ → E} {a : Aff} (hfit : affFits v Rz a = true) :
    (∀ t, t < 2 ^ Q.P.y.h.lt → affFits v (Rt t) a = true) ∧
      Reading.gl.val (valAff v Rz slot a) = ∑ t ∈ range (2 ^ Q.P.y.h.lt),
        Blocks.eqN Q.P.y.h.lt 0 (pt Reading.gl z) t *
          Reading.gl.val (valAff v (Rt t) slot a) := by
  have hx : ∀ x ∈ a.ents.toList, (x.tree == v.iU3) = true ∧
      Rz.has (x.row * v.K3 + x.idx) = true := by
    have h0 := hfit
    unfold affFits at h0
    rw [← Array.all_toList, List.all_eq_true] at h0
    intro x hx
    have h1 := h0 x hx
    rw [Bool.and_eq_true] at h1
    exact h1
  constructor
  · intro t ht
    unfold affFits
    rw [← Array.all_toList, List.all_eq_true]
    intro x hx'
    rw [Bool.and_eq_true]
    exact ⟨(hx x hx').1, (reads_tok hl hk hlow hz hRz hRt (hx x hx').2).1 t ht⟩
  · have hE : (a.ents.toList.map fun x => if x.tree == v.iU3 then
        Reading.gl.val x.coef * Reading.gl.val (Rz.u3 (x.row * v.K3 + x.idx)) else 0).sum =
        ∑ t ∈ range (2 ^ Q.P.y.h.lt), Blocks.eqN Q.P.y.h.lt 0 (pt Reading.gl z) t *
          (a.ents.toList.map fun x => if x.tree == v.iU3 then
            Reading.gl.val x.coef * Reading.gl.val ((Rt t).u3 (x.row * v.K3 + x.idx))
            else 0).sum := by
      have e1 : ∀ t ∈ range (2 ^ Q.P.y.h.lt), Blocks.eqN Q.P.y.h.lt 0 (pt Reading.gl z) t *
          (a.ents.toList.map fun x => if x.tree == v.iU3 then
            Reading.gl.val x.coef * Reading.gl.val ((Rt t).u3 (x.row * v.K3 + x.idx))
            else 0).sum =
          (a.ents.toList.map fun x => Blocks.eqN Q.P.y.h.lt 0 (pt Reading.gl z) t *
            (if x.tree == v.iU3 then
              Reading.gl.val x.coef * Reading.gl.val ((Rt t).u3 (x.row * v.K3 + x.idx))
              else 0)).sum := fun t _ => (List.sum_map_mul_left _ _ _).symm
      rw [sum_congr rfl e1, sum_list_comm]
      congr 1
      refine List.map_congr_left fun x hx' => ?_
      obtain ⟨d, hh⟩ := hx x hx'
      rw [if_pos d, (reads_tok hl hk hlow hz hRz hRt hh).2, Finset.mul_sum]
      refine sum_congr rfl fun t _ => ?_
      rw [if_pos d]
      ring
    rw [valAff_sum, hE]
    have e2 : ∀ t ∈ range (2 ^ Q.P.y.h.lt), Blocks.eqN Q.P.y.h.lt 0 (pt Reading.gl z) t *
        Reading.gl.val (valAff v (Rt t) slot a) =
        Blocks.eqN Q.P.y.h.lt 0 (pt Reading.gl z) t * (Reading.gl.val a.const +
          (a.slots.toList.map fun x => Reading.gl.val x.2 * Reading.gl.val (slot x.1)).sum) +
        Blocks.eqN Q.P.y.h.lt 0 (pt Reading.gl z) t *
          (a.ents.toList.map fun x => if x.tree == v.iU3 then
            Reading.gl.val x.coef * Reading.gl.val ((Rt t).u3 (x.row * v.K3 + x.idx))
            else 0).sum := by
      intro t _
      rw [valAff_sum]
      ring
    rw [sum_congr rfl e2, Finset.sum_add_distrib, ← Finset.sum_mul, sum_eqN_one, one_mul]

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.phiOf_planes
#print axioms OnBytes.Road.K4.C.phiOf_lacks
#print axioms OnBytes.Road.K4.C.fit_found
#print axioms OnBytes.Road.K4.C.phi_tok
#print axioms OnBytes.Road.K4.C.place_lt
#print axioms OnBytes.Road.K4.C.reads_tok
#print axioms OnBytes.Road.K4.C.valAff_sum
#print axioms OnBytes.Road.K4.C.valAff_tok
