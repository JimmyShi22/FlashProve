-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K15/GroundInv.lean: beneath K15's law: what a yes of each plain ground function
(Johnson/Desc/First/Base/Ground.lean) says: its
effect in the library's own closed form (withGroup · stSent · admitted · withMessageInGroup · withRow |
withRows), and of its tests what the
library's facts on a link's run keep. General in the carried record's own part L. Small lemmas by
unfolding; no program is run.
-/
import Johnson.Desc.Ground.Calls
import OnBytes.Slice.BlkStLaws
import Johnson.Desc.Own.RowsAgree
import Johnson.Desc.Own.ShapesAgree
import Johnson.Desc.Own.TreesAgree
import Johnson.Desc.Own.SendAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K15
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open VerifiableInference.Desc.Ground (newGroupP recvP admitP joinP addRowP addRowsP addRowsFrom ok
    rowL recvL admitL joinL)

variable {L : Type}

/-- The plain ground's text of «one more group» is the library's. -/
theorem withGroup_is (S : Statement) (a b : Nat) :
    VerifiableInference.Desc.Ground.withGroup S a b = OnBytes.Slice.withGroup S a b := rfl

theorem newGroupP_inv (d d' : DState L) (a b g : Nat) (h : newGroupP d a b = some (g, d')) :
    g = d.st.groups.size ∧ d' = { d with st := OnBytes.Slice.withGroup d.st a b } := by
  unfold newGroupP at h
  split at h
  · injection h with h
    injection h with h1 h2
    exact ⟨h1.symm, h2.symm⟩
  · cases h

theorem joinP_inv (d d' : DState L) (g o : Nat) (k : Bool) (h : joinP d g o k = some d') :
    ∃ G, d.st.groups[g]? = some G ∧ d' = { d with st := withMessageInGroup d.st g o k G } := by
  unfold joinP at h
  split at h
  · cases hG : d.st.groups[g]? with
    | none => rw [hG] at h; cases h
    | some G =>
      rw [hG] at h
      injection h with h
      exact ⟨G, rfl, h.symm⟩
  · cases h

theorem addRowP_inv (d d' : DState L) (g : Nat) (row : Row) (h : addRowP d g row = some d') :
    ok (rowL d.st g row) = true ∧ d' = { d with st := withRow d.st g row } := by
  unfold addRowP at h
  split at h
  · rename_i hk
    injection h with h
    exact ⟨hk, h.symm⟩
  · cases h

/-- Of the tests in front of a new open row: what the library's facts keep (RowChecked), and that it
is no sample row. -/
theorem rowL_checked (S : Statement) (g : Nat) (row : Row) (h : ok (rowL S g row) = true) :
    row.kind ≠ .sample ∧ RowChecked S row := by
  unfold ok rowL at h
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨hG, _, hk, ht, _, hr, hf, _⟩ := h
  cases hGG : S.groups[g]? with
  | none => rw [hGG] at hG; cases hG
  | some G =>
    rw [hGG] at ht hr hf
    simp only [← VerifiableInference.Desc.Own.placeFits_agrees, ←
        VerifiableInference.Desc.Own.formFits_agrees] at ht hr hf
    simp only [VerifiableInference.Desc.Ground.on, VerifiableInference.Desc.Ground.has,
        Option.map_some, Option.getD_some,
      Array.all_eq_true_iff_forall_mem, Blk.placeOk, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at ht hr hf
    refine ⟨by simpa using hk, ⟨fun t h1 => ?_, fun w h1 => ?_, fun f h1 => ?_⟩⟩
    · exact (ht t (Array.mem_toList_iff.1 h1)).2.1.2
    · exact (hr w (Array.mem_toList_iff.1 h1)).1.2
    · exact (hf f (Array.mem_toList_iff.1 h1)).2

theorem addRowsFrom_inv (g : Nat) : ∀ (l : List Row) (d d' : DState L), addRowsFrom g l d = some d'
    →
    (∀ r ∈ l, r.kind ≠ .sample ∧ RowChecked d.st r) ∧ d' = { d with st := withRows d.st g l }
  | [], d, d', h => by
    injection h with h
    exact ⟨fun _ hr => (nomatch hr), h.symm⟩
  | r :: l, d, d', h => by
    unfold addRowsFrom at h
    cases h1 : addRowP d g r with
    | none => rw [h1] at h; cases h
    | some d1 =>
      rw [h1] at h
      obtain ⟨hk, rfl⟩ := addRowP_inv d d1 g r h1
      obtain ⟨hl, rfl⟩ := addRowsFrom_inv g l _ d' h
      refine ⟨fun x hx => ?_, rfl⟩
      rcases List.mem_cons.1 hx with rfl | hx
      · exact rowL_checked _ _ _ hk
      · exact ⟨(hl x hx).1, (hl x hx).2.withRow g r⟩

theorem addRowsP_inv (d d' : DState L) (g : Nat) (l : List Row) (h : addRowsP d g l = some d') :
    (∀ r ∈ l, r.kind ≠ .sample ∧ RowChecked d.st r) ∧ d' = { d with st := withRows d.st g l } := by
  unfold addRowsP at h
  split at h
  · exact addRowsFrom_inv g l d d' h
  · cases h

theorem recvP_inv (ft : Nat) (d d' : DState L) (sent : Array OracleNotice) (ids : Array Nat)
    (h : recvP ft d sent = some (ids, d')) :
    ∃ lay, layTrees d.st.codes sent = some lay ∧ d.st.oracles.size = d.book.place.size ∧
      ids = (Array.range sent.size).map (· + d.st.oracles.size) ∧
      d' = { d with
        st := stSent d.st sent
        book :=
          { trees := partsLaid sent lay d.st.oracles.size d.book.trees.size
              (treesSent ft lay.shapes.toList d.roots d.book.trees)
            place := d.book.place ++ (Array.range sent.size).map fun i =>
              (d.book.trees.size + lay.tree.getD i 0, lay.part.getD i 0) }
        roots := d.roots + lay.shapes.size } := by
  unfold recvP at h
  rw [VerifiableInference.Desc.Own.treesMade_eq] at h
  split at h
  · rename_i hk
    cases hl : layTrees d.st.codes sent with
    | none => rw [hl] at h; cases h
    | some lay =>
      rw [hl] at h
      injection h with h
      injection h with h1 h2
      refine ⟨lay, rfl, ?_, h1.symm, h2.symm⟩
      unfold ok recvL at hk
      simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
        beq_iff_eq] at hk
      exact hk.2
  · cases h

theorem admitP_inv (d d' : DState L) (o : Nat) (rows : Array Row) (h : admitP d o rows = some d') :
    ∃ x places, d.st.oracles[o]? = some x ∧ Send.pad d.st.codes x.shape = some places ∧
      d' = { d with st := admitted d.st o x.shape places rows } := by
  unfold admitP at h
  simp only [VerifiableInference.Desc.Own.padMade_eq] at h
  split at h
  · cases hx : d.st.oracles[o]? with
    | none => rw [hx] at h; cases h
    | some x =>
      rw [hx] at h
      cases hp : Send.pad d.st.codes x.shape with
      | none => simp [hp] at h
      | some places =>
        simp only [hp, Option.bind_eq_bind, Option.bind_some] at h
        injection h with h
        exact ⟨x, places, rfl, hp, h.symm⟩
  · cases h

end Desc.K15

#print axioms Desc.K15.rowL_checked
#print axioms Desc.K15.addRowsP_inv
#print axioms Desc.K15.recvP_inv
#print axioms Desc.K15.admitP_inv
#print axioms Desc.K15.joinP_inv
#print axioms Desc.K15.newGroupP_inv
