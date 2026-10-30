-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/Keep/K3Late.lean: The kind "lookup" (K3): WHAT ITS RUNS OF CLAIMS FILL LATE,
AS A LIST, AND WHAT "objects" ANSWERS AT A RECORD. Definitions, statements and proofs.

Why. A run of claims can be read through a reader: at a record it gives the run's forms and its LATE
SLOTS: the slots that are free in the ledger in front of the run and filled in the ledger behind it,
with what lies under them. For each run of each kind one answer is owed at every record at which the
run's claims are still to come.

Main names:
  lateG F G: the slots that are free in F and filled in G, with what G holds under them: A COPY of
    lateOf, as it is typed in a file on the reader of kind K9 that is not in this library; typed
    here so that this file stands over the library alone; the tie is to be rfl, over that file.
  late_same: where G has F's marks the list is empty. late_paid: so behind a mark on a debt.
  range_cut: a filterMap over the numbers below ns that answers on one stretch alone.
  late_hideRun: BEHIND A RUN OF n VALUES v UNDER THE SLOTS FROM a ON, from a ledger that has its
    sizes: the list is just these n slots, in order, each with its value and the factor.
  objects_answer: where a ledger is open and g was heard, "objects" RETURNS: g's rows as claims,
    and the record with a mark on a debt: an equation.
    "objects" and "join" lay a mark on a debt and no more (objects_cut, joinRun_cut): by late_paid
    they fill nothing late.
  planes_late: THE LATE SLOTS OF "planes": the lvLen g slots from g.leaves.first on, each with
    (0 shown, the factor 0 - 1): a function of what was heard alone.

Limits. planes_late is from a return of the run; that its write returns where the stretch is still
owed: Johnson/Top/H/Keep/K3Start.lean's own_write_returns. The forms of "planes" and "join" hang on
the calling kind's readers and keys at the record: nothing on them here.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.Keep.K3Inv

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.K.Kc OnBytes.PscRun
open VerifiableInference.Desc (named need)
open VerifiableInference.Desc.K3 (Seat joinRun planesRun Readers)

/-- The slots that are free in F and filled in G, with what G holds under them. -/
def lateG (F G : Fork) : List (Nat × E × E) :=
  (List.range G.ns).filterMap fun j =>
    if !(F.gotF.getD j false) && G.gotF.getD j false then
      some (j, G.vp.getD j zeroE, G.mf.getD j zeroE) else none

/-- Where G has F's marks nothing is late. -/
theorem late_same {F G : Fork} (h : ∀ j, G.gotF.getD j false = F.gotF.getD j false) :
    lateG F G = [] := by
  unfold lateG
  refine List.filterMap_eq_nil_iff.2 fun j _ => ?_
  rw [h j]
  cases F.gotF.getD j false <;> rfl

theorem late_paid (F : Fork) (i : ℕ) : lateG F (F.paid i) = [] := late_same fun _ => rfl

/-- A filterMap over the numbers below ns that answers on one stretch alone. -/
theorem range_cut {α : Type} (φ : ℕ → Option α) (ψ : ℕ → α) (a n ns : ℕ) (hn : a + n ≤ ns)
    (hin : ∀ t, t < n → φ (a + t) = some (ψ t))
    (hout : ∀ j, (j < a ∨ a + n ≤ j) → φ j = none) :
    (List.range ns).filterMap φ = (List.range n).map ψ := by
  obtain ⟨r, rfl⟩ : ∃ r, ns = a + (n + r) := ⟨ns - (a + n), by omega⟩
  rw [List.range_add, List.range_add, List.map_append, List.filterMap_append,
    List.filterMap_append]
  have h1 : (List.range a).filterMap φ = [] :=
    List.filterMap_eq_nil_iff.2 fun j hj => hout j (Or.inl (List.mem_range.1 hj))
  have h3 : (((List.range r).map (n + ·)).map (a + ·)).filterMap φ = [] := by
    refine List.filterMap_eq_nil_iff.2 fun j hj => ?_
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hj
    obtain ⟨y, _, rfl⟩ := List.mem_map.1 hx
    exact hout _ (Or.inr (by omega))
  have h2 : ((List.range n).map (a + ·)).filterMap φ = (List.range n).map ψ := by
    rw [List.filterMap_map, ← List.filterMap_eq_map]
    exact List.filterMap_congr fun t ht => hin t (List.mem_range.1 ht)
  rw [h1, h2, h3, List.nil_append, List.append_nil]

/-- **Behind a run of values under slots.** -/
theorem late_hideRun {F G : Fork} {a : ℕ} {v : Array E} {f : E} (hF : Sized F)
    (h : F.hideRun a v f = some G) :
    lateG F G = (List.range v.size).map fun t => (a + t, v.getD t zeroE, f) := by
  obtain ⟨hsame, _, hin, hout⟩ := hideRun_ok F G a v f hF h
  have hns : G.ns = F.ns := by rw [hsame]
  unfold lateG
  by_cases hv : v.size = 0
  · rw [hv]
    refine List.filterMap_eq_nil_iff.2 fun j _ => ?_
    have hj := (hout j (by omega)).2.2
    by_cases hf : F.gotF.getD j false = true
    · rw [hf]
      rfl
    · have hg : ¬ G.gotF.getD j false = true := fun x => hf (hj.1 x)
      rw [Bool.not_eq_true] at hg
      rw [hg, Bool.and_false]
      rfl
  · refine range_cut _ _ a v.size G.ns ?_ (fun t ht => ?_) fun j hj => ?_
    · have := (hin (v.size - 1) (by omega)).1
      rw [hns]
      omega
    · obtain ⟨_, h2, h3, h4, h5⟩ := hin t ht
      have h2' : F.gotF.getD (a + t) false = false := by
        rw [← Bool.not_eq_true]
        exact h2
      have h3' : G.gotF.getD (a + t) false = true := h3
      rw [h2', h3', h4, h5]
      rfl
    · have hj' := (hout j hj).2.2
      by_cases hf : F.gotF.getD j false = true
      · rw [hf]
        rfl
      · have hg : ¬ G.gotF.getD j false = true := fun x => hf (hj'.1 x)
        rw [Bool.not_eq_true] at hg
        rw [hg, Bool.and_false]
        rfl

variable {S Cl : Type}

/-- **"objects" returns**, and what. -/
theorem objects_answer (seat : Seat S Cl) (i : ℕ) {s : S} {F : Fork} {g : Forest.Heard}
    (hF : seat.fork s = some F) (hg : seat.heard s = some g) :
    objectsRun seat i s =
      .ok (g.rows.toList.map seat.claim, seat.mark s (F.paid g.owedObjects)) := by
  unfold objectsRun
  rw [hF, hg]
  rfl

/-- **The late slots of "planes".** -/
theorem planes_late (seat : Seat S Cl) (lm : ℕ) (readers : Readers S) {i : ℕ} {s s' : S}
    {l : List Cl} {F : Fork} {g : Forest.Heard} (hf : seat.fork s = some F) (hS : Sized F)
    (hg : seat.heard s = some g) (h : planesRun seat lm readers i s = .ok (l, s')) :
    ∃ G, s' = seat.mark s G ∧
      lateG F G = (List.range (lvLen g)).map fun t =>
        (g.leaves.first + t, zeroE, subE zeroE oneE) := by
  obtain ⟨G, hG, rfl⟩ := planes_fills seat lm readers hf hg h
  refine ⟨G.paid g.owedPlanes, rfl, ?_⟩
  have e : lateG F (G.paid g.owedPlanes) = lateG F G := rfl
  rw [e, late_hideRun hS hG, Array.size_replicate]
  refine List.map_congr_left fun t ht => ?_
  have ht' : t < lvLen g := List.mem_range.1 ht
  simp [Array.getD_eq_getD_getElem?, ht']

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.late_paid
#print axioms VerifiableInference.OnPublicFiles.range_cut
#print axioms VerifiableInference.OnPublicFiles.late_hideRun
#print axioms VerifiableInference.OnPublicFiles.objects_answer
#print axioms VerifiableInference.OnPublicFiles.planes_late
