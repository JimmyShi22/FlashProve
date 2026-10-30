-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/ReadsKit.lean: CONDITIONAL.

Not shown here. That layTables returns; that the honest side's list of points is a part of the list
at which the weights are taken (PtsPart). Nothing on any matrices but the input's own cells. No
example is known. No property is claimed.

THE HONEST READS, OPENED. An entry of the honest reads of the sub-protocol K4 (readsAt,
Johnson/Desc/K4/Honest/Cells.lean), at the place of column c and run sg of a part of a family of
tables, is, read in the field, the sum of the input's cells in that run under the family's weights
as the verifier's function gives them (phiOf, OnBytes/Model/Layer.lean).

  mkFam, readsAt_at   readsAt's text for one family; the two functions where the family is known.
  fam_at         at entry j of the part (M, st) of the family q: the entry, the test, the part
                 found.
  place_of_has   a place at which Reads.has is true is such a place.
  named_of_off   a part off the matrix of the lookup's planes belongs to a family with none of the
                 three names on it.
  reads_sum      the entry as a sum of cells under the verifier's weights.
-/
import Johnson.Road.K4.C.Laid
import Johnson.Road.K4.C.Weights

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (TableAsk TableAt layTables tableAsks phiOf matIx)
open OnBytes.Desc.First.K4.Honest (K4Pub K4In Reads Fam matsOf laidOf famsAt readsAt famEntry
  famCell famPart wtsOf wtsFit)

variable {Q : K4Pub} {w : K4In} {fo : Forest.Heard} {pt pts : List (String × Array E)} {R : Reads}
  {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}

/-- What the honest side makes of a family: famsAt's text (Johnson/Desc/K4/Honest/Cells.lean). -/
def mkFam (Q : K4Pub) (fo : Forest.Heard) (pt : List (String × Array E))
    (x : TableAsk × List (ℕ × ℕ)) : Fam :=
  { ask := x.1, first := famFirst x, len := famLen (matsOf Q) x, wts := wtsOf Q.P.y fo pt x.1
    fit := Thunk.mk fun _ => wtsFit Q.P.y fo pt x.1 }

/-- The honest reads, where the family of an entry is known; and where there is none. -/
theorem readsAt_at (hR : readsAt Q w fo pt = some R)
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r) (e : ℕ) :
    (∀ f, ((r.2.1.map (mkFam Q fo pt)).find? fun f =>
        decide (f.first ≤ e) && decide (e < f.first + f.len)) = some f →
      R.u3 e = famEntry (matsOf Q) w.cell f (e - f.first) ∧ R.has e = f.fit.get) ∧
    (((r.2.1.map (mkFam Q fo pt)).find? fun f =>
        decide (f.first ≤ e) && decide (e < f.first + f.len)) = none → R.has e = false) := by
  unfold readsAt at hR
  obtain ⟨fams, hfams, rfl⟩ := Option.map_eq_some_iff.mp hR
  unfold famsAt at hfams
  obtain ⟨laid, hlaid, rfl⟩ := Option.map_eq_some_iff.mp hfams
  have e1 : laid = r.2.1 := by
    unfold laidOf at hlaid
    rw [hl] at hlaid
    exact (Option.some.inj hlaid).symm
  subst e1
  constructor
  · intro f hf
    have hf' : ((r.2.1.map (mkFam Q fo pt)).toArray.find? fun f =>
        decide (f.first ≤ e) && decide (e < f.first + f.len)) = some f := by
      rw [List.find?_toArray]
      exact hf
    constructor
    · show (match ((r.2.1.map (mkFam Q fo pt)).toArray.find? fun f =>
          decide (f.first ≤ e) && decide (e < f.first + f.len)) with
        | some f => famEntry (matsOf Q) w.cell f (e - f.first)
        | none => zeroE) = _
      rw [hf']
    · show (match ((r.2.1.map (mkFam Q fo pt)).toArray.find? fun f =>
          decide (f.first ≤ e) && decide (e < f.first + f.len)) with
        | some f => f.fit.get
        | none => false) = _
      rw [hf']
  · intro hf
    have hf' : ((r.2.1.map (mkFam Q fo pt)).toArray.find? fun f =>
        decide (f.first ≤ e) && decide (e < f.first + f.len)) = none := by
      rw [List.find?_toArray]
      exact hf
    show (match ((r.2.1.map (mkFam Q fo pt)).toArray.find? fun f =>
        decide (f.first ≤ e) && decide (e < f.first + f.len)) with
      | some f => f.fit.get
      | none => false) = _
    rw [hf']

/-- **At entry j of the part m of the family q.** -/
theorem fam_at (hR : readsAt Q w fo pt = some R)
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r)
    {q : TableAsk × List (ℕ × ℕ)} (hq : q ∈ r.2.1) {m : ℕ × ℕ} (hmq : m ∈ q.2) {j : ℕ}
    (hj : j < wd (matsOf Q) q.1.L m.1) :
    R.u3 (m.2 + j) = famEntry (matsOf Q) w.cell (mkFam Q fo pt q) (m.2 + j - famFirst q) ∧
      R.has (m.2 + j) = wtsFit Q.P.y fo pt q.1 ∧
      famPart (matsOf Q) q.1.L q.1.parts q.1.M0 (m.2 + j - famFirst q) = (m.1, j) := by
  obtain ⟨L1, -⟩ := laid_of_layTables _ _ _ _ hl
  obtain ⟨f1, f2, -⟩ := find_fam (matsOf Q) (mkFam Q fo pt) (·.first) (·.len) (fun _ => rfl)
    (fun _ => rfl) r.2.1 0 L1 q hq m hmq _ hj
  obtain ⟨u1, u2⟩ := (readsAt_at hR hl _).1 _ f1
  obtain ⟨p1, -⟩ := laid_mem (matsOf Q) r.2.1 0 L1 q hq
  have hmq' := hmq
  rw [p1] at hmq'
  have hpart := famPart_layParts (matsOf Q) q.1 q.1.parts (famFirst q) (Nat.le_refl _) m hmq' _ hj
  rw [Nat.sub_self, Nat.add_zero] at hpart
  have hidx : m.2 + j - famFirst q = m.2 - famFirst q + j := by omega
  refine ⟨u1, u2, ?_⟩
  rw [hidx]
  exact hpart

/-- **A place at which the honest side's test is true** is the place of a column and a run of a part
of a family. -/
theorem place_of_has (hR : readsAt Q w fo pt = some R)
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r) {pos : ℕ}
    (hh : R.has pos = true) :
    ∃ q ∈ r.2.1, ∃ m ∈ q.2, ∃ c sg, c < ((matsOf Q).getD m.1 (0, 0)).2 ∧
      sg < ((matsOf Q).getD m.1 (0, 0)).1 / q.1.L ∧
      pos = m.2 + (c * (((matsOf Q).getD m.1 (0, 0)).1 / q.1.L) + sg) := by
  obtain ⟨L1, -⟩ := laid_of_layTables _ _ _ _ hl
  cases hfd : ((r.2.1.map (mkFam Q fo pt)).find? fun f =>
      decide (f.first ≤ pos) && decide (pos < f.first + f.len)) with
  | none =>
    rw [(readsAt_at hR hl pos).2 hfd] at hh
    cases hh
  | some f =>
    have hin := List.find?_some hfd
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp (List.mem_of_find?_eq_some hfd)
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hin
    have h1 : famFirst q ≤ pos := hin.1
    have h2 : pos < famFirst q + famLen (matsOf Q) q := hin.2
    obtain ⟨p1, p2⟩ := laid_mem (matsOf Q) r.2.1 0 L1 q hq
    rw [p2] at h2
    obtain ⟨m, hm1, g1, g2⟩ := parts_cover (matsOf Q) q.1 q.1.parts (famFirst q) pos h1 h2
    rw [← p1] at hm1
    have g2' : pos < m.2 + ((matsOf Q).getD m.1 (0, 0)).2 *
        (((matsOf Q).getD m.1 (0, 0)).1 / q.1.L) := g2
    have hnb : 0 < ((matsOf Q).getD m.1 (0, 0)).1 / q.1.L := by
      rcases Nat.eq_zero_or_pos (((matsOf Q).getD m.1 (0, 0)).1 / q.1.L) with z | z
      · rw [z, Nat.mul_zero] at g2'
        omega
      · exact z
    refine ⟨q, hq, m, hm1, (pos - m.2) / (((matsOf Q).getD m.1 (0, 0)).1 / q.1.L),
      (pos - m.2) % (((matsOf Q).getD m.1 (0, 0)).1 / q.1.L), ?_, Nat.mod_lt _ hnb, ?_⟩
    · rw [Nat.div_lt_iff_lt_mul hnb]
      omega
    · rw [Nat.div_add_mod']
      omega

/-- **A part that does not stand on the matrix of the lookup's planes belongs to a family with none
of the three names on that matrix.** -/
theorem named_of_off (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r)
    {q : TableAsk × List (ℕ × ℕ)} (hq : q ∈ r.2.1) {m : ℕ × ℕ} (hmq : m ∈ q.2)
    (hoff : m.1 ≠ (matIx Q.P.y).iB) : Named q.1 := by
  obtain ⟨L1, L2⟩ := laid_of_layTables _ _ _ _ hl
  obtain ⟨p1, -⟩ := laid_mem (matsOf Q) r.2.1 0 L1 q hq
  have hask : q.1 ∈ tableAsks Q.P.y Q.P.rd Q.g := by
    rw [← L2]
    exact List.mem_map.mpr ⟨q, hq, rfl⟩
  rw [Fo.tableAsks_eq] at hask
  rcases List.mem_append.mp hask with h | h
  · exact ⟨beq_eq_false_iff_ne.mpr (Fo.ask_ne h _ (by decide)),
      beq_eq_false_iff_ne.mpr (Fo.ask_ne h _ (by decide)),
      beq_eq_false_iff_ne.mpr (Fo.ask_ne h _ (by decide))⟩
  · exfalso
    rw [p1] at hmq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    have one : ∀ nm : String, q.1 = Fo.planeAsk Q.P.y nm → m.1 = (matIx Q.P.y).iB := by
      intro nm e
      rw [e] at hmq
      have hm1 : m ∈ [((matIx Q.P.y).iB + (1 - 1), famFirst q)] := hmq
      rw [List.mem_singleton] at hm1
      rw [hm1]
      exact Nat.add_zero _
    rcases h with e | e | e
    · exact hoff (one _ e)
    · exact hoff (one _ e)
    · exact hoff (one _ e)

/-- **The entry as a sum of the input's cells under the verifier's weights.** fo': what the lookup
has sampled, as the weights' maker has it: free where the family has none of the three names. -/
theorem reads_sum {fo' : Forest.Heard} (hR : readsAt Q w fo pt = some R)
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r) (hp : PtsPart pt pts)
    {q : TableAsk × List (ℕ × ℕ)} (hq : q ∈ r.2.1) {m : ℕ × ℕ} (hmq : m ∈ q.2) {c sg nb : ℕ}
    (hnb : nb = ((matsOf Q).getD m.1 (0, 0)).1 / q.1.L)
    (hc : c < ((matsOf Q).getD m.1 (0, 0)).2) (hsg : sg < nb)
    (hhas : R.has (m.2 + (c * nb + sg)) = true) (hfo : Named q.1 ∨ fo' = fo) {phi : Array E}
    (hphi : phiOf Q.P.y fo' pts q.1 = some phi) :
    Reading.gl.val (R.u3 (m.2 + (c * nb + sg))) =
      ∑ j ∈ Finset.range q.1.L, Reading.gl.val (phi.getD j zeroE) *
        Reading.gl.val (ofF (w.cell m.1 (sg * q.1.L + j) c)) := by
  obtain ⟨-, L2⟩ := laid_of_layTables _ _ _ _ hl
  have hphi' : phiOf Q.P.y fo pts q.1 = some phi := by
    rcases hfo with hn | e
    · rw [phiOf_fo fo fo' hn]
      exact hphi
    · rw [← e]
      exact hphi
  have hj : c * nb + sg < wd (matsOf Q) q.1.L m.1 := by
    show c * nb + sg < ((matsOf Q).getD m.1 (0, 0)).2 * (((matsOf Q).getD m.1 (0, 0)).1 / q.1.L)
    rw [← hnb]
    calc c * nb + sg < (c + 1) * nb := by rw [Nat.succ_mul]; omega
      _ ≤ ((matsOf Q).getD m.1 (0, 0)).2 * nb := Nat.mul_le_mul_right _ hc
  obtain ⟨u1, u2, u3⟩ := fam_at hR hl hq hmq hj
  rw [u2] at hhas
  have hpos : 0 < nb := by omega
  have hmod : (c * nb + sg) % nb = sg := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hsg]
  have hdiv : (c * nb + sg) / nb = c := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hsg, Nat.zero_add]
  have hcell : famCell (matsOf Q) q.1 (m.2 + (c * nb + sg) - famFirst q) 0 =
      (m.1, sg * q.1.L + 0, c) := by
    unfold famCell
    rw [u3]
    show (m.1, (c * nb + sg) % (((matsOf Q).getD m.1 (0, 0)).1 / q.1.L) * q.1.L + 0,
      (c * nb + sg) / (((matsOf Q).getD m.1 (0, 0)).1 / q.1.L)) = _
    rw [← hnb, hmod, hdiv]
  have hent : famEntry (matsOf Q) w.cell (mkFam Q fo pt q) (m.2 + (c * nb + sg) - famFirst q) =
      entrySum q.1.L (wtsOf Q.P.y fo pt q.1) fun j => w.cell m.1 (sg * q.1.L + 0 + j) c := by
    have e0 : famEntry (matsOf Q) w.cell (mkFam Q fo pt q) (m.2 + (c * nb + sg) - famFirst q) =
        entrySum q.1.L (wtsOf Q.P.y fo pt q.1) fun j =>
          w.cell (famCell (matsOf Q) q.1 (m.2 + (c * nb + sg) - famFirst q) 0).1
            ((famCell (matsOf Q) q.1 (m.2 + (c * nb + sg) - famFirst q) 0).2.1 + j)
            (famCell (matsOf Q) q.1 (m.2 + (c * nb + sg) - famFirst q) 0).2.2 := rfl
    rw [e0, hcell]
  have hask : q.1 ∈ tableAsks Q.P.y Q.P.rd Q.g := by
    rw [← L2]
    exact List.mem_map.mpr ⟨q, hq, rfl⟩
  rw [u1, hent, entry_sum (ask_ok hask) hhas hphi' hp]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.add_zero]

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.readsAt_at
#print axioms OnBytes.Road.K4.C.fam_at
#print axioms OnBytes.Road.K4.C.place_of_has
#print axioms OnBytes.Road.K4.C.named_of_off
#print axioms OnBytes.Road.K4.C.reads_sum
