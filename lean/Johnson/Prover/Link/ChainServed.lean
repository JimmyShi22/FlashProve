-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/ChainServed.lean: "ALL THAT IS WANTED IS SERVED" (Served,
Johnson/Prover/Link/ChainDefs.lean), over groupsOf's list with its widths, FROM THE LIKE OVER THE
LIBRARY's LIST OF PAIRS (wantedX) with the widths apart. Statements and proofs.

  wideTie         A CLOSED TEST, WITH CODE: each declared stored part names item 0 or 1 and states
                  the width of that stored string's columns; each declared opened tree has a number
                  below 2 ^ 16 and states the width that the rounds' data state of that tree
  groups_mem      whence a member of groupsOf's list comes: a declared stored part, or a declared
                  opened tree: with its key and width
  served_of_look  under wantTie and wideTie: where every wanted pair is there, under a stored
                  string's key with that string's width, under a tree's number with that tree's
                  width: Served

Limits. The premise on the pairs is a premise here. The two closed tests: at the copy's
file's written letters, both sizes, they are evaluated in Johnson/Prover/Link/ChainAtFull.lean
(fr_wantTie, fr_wideTie, sr_wantTie, sr_wideTie). Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.ChainCols

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open VerifiableInference.Desc
open VerifiableInference.Desc.Plain.One (lookY)
open _root_.Run.PQ (XO SgX storedKey)
open TypedOracleCompiler.Run.PQ (RD treeSh wantedX)
open _root_.Iop (twoExternalStrings)

/-- **The closed test on widths.** W: the width of each stored string's columns. -/
def wideTie (ds : List RD) (W : Bool → ℕ) (decls : List Fmt.DeclaredRound) : Bool :=
  decls.all fun d =>
    d.stored.all (fun s => decide (s.item < 2) && s.sh.W == W (s.item == 1)) &&
      d.opens.all fun o =>
        decide (o.1.tree < 2 ^ 16) && (treeSh ds o.1.tree).map (·.W) == some o.1.W

/-- Whence a member of groupsOf's list comes. -/
theorem groups_mem : ∀ (decls : List Fmt.DeclaredRound) (Ds : List Fmt.Drawn) (w : ℕ × ℕ × ℕ),
    w ∈ (groupsOf 0 decls Ds).flatMap id → ∃ d ∈ decls,
      (∃ s ∈ d.stored, w.1 = Fmt.storedKey s.item ∧ w.2.2 = s.sh.W) ∨
        ∃ o ∈ d.opens, w.1 = o.1.tree - 0 ∧ w.2.2 = o.1.W
  | [], Ds, w, h => by cases Ds <;> simp [groupsOf] at h
  | _ :: _, [], w, h => by simp [groupsOf] at h
  | d :: decls, D :: Ds, w, h => by
    unfold groupsOf at h
    rw [List.flatMap_append, List.flatMap_append] at h
    rcases List.mem_append.1 h with h | h
    · rcases List.mem_append.1 h with h | h
      · obtain ⟨g, hg, hw⟩ := List.mem_flatMap.1 h
        obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hg
        obtain ⟨x, -, rfl⟩ := List.mem_map.1 hw
        exact ⟨d, List.mem_cons_self, Or.inl ⟨s, hs, rfl, rfl⟩⟩
      · obtain ⟨g, hg, hw⟩ := List.mem_flatMap.1 h
        obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hg
        obtain ⟨x, -, rfl⟩ := List.mem_map.1 hw
        exact ⟨d, List.mem_cons_self, Or.inr ⟨o, ho, rfl, rfl⟩⟩
    · obtain ⟨d', hd', r⟩ := groups_mem decls Ds w h
      exact ⟨d', List.mem_cons_of_mem _ hd', r⟩

/-- **Served, from the like over the library's pairs.** -/
theorem served_of_look (ds : List RD) (a : ℕ) (xs : List XO) (decls : List Fmt.DeclaredRound)
    (next : ℕ → List Fmt.Drawn → MsgV) (y : (twoExternalStrings (2 ^ a) SgX).Str) (Ds : List Fmt.Drawn)
    (W : Bool → ℕ) (ht : wantTie a ds xs decls = true) (hw : wideTie ds W decls = true)
    (H : ∀ kx ∈ wantedX a ds xs Ds, ∃ c, lookY a y (colOf ds 0 [] next Ds) kx.1 kx.2 = some c ∧
      (∀ w, kx.1 = storedKey w → c.length = W w) ∧
      ∀ s, kx.1 < 2 ^ 16 → treeSh ds kx.1 = some s → c.length = s.W) :
    Served (lookV ds a next y Ds) ((groupsOf 0 decls Ds).flatMap id) := by
  intro w hm
  have hk : (w.1, w.2.1) ∈ wantedX a ds xs Ds := by
    rw [wanted_groups a ds xs decls ht Ds]
    exact List.mem_map.2 ⟨w, hm, rfl⟩
  obtain ⟨c, hc, h1, h2⟩ := H _ hk
  refine ⟨c, hc, ?_⟩
  simp only [wideTie, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hw
  obtain ⟨d, hd, ⟨s, hs, e1, e2⟩ | ⟨o, ho, e1, e2⟩⟩ := groups_mem decls Ds w hm
  · obtain ⟨hi, hW⟩ := (hw d hd).1 s hs
    rw [e2, hW]
    exact h1 _ (by rw [storedKey_item _ hi]; exact e1)
  · obtain ⟨hl, hW⟩ := (hw d hd).2 o ho
    obtain ⟨s, hs, e⟩ := Option.map_eq_some_iff.1 hW
    have e1' : w.1 = o.1.tree := e1
    rw [e2, ← e]
    exact h2 s (by show w.1 < _; rw [e1']; exact hl) (by show treeSh ds w.1 = _; rw [e1']; exact hs)

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.groups_mem
#print axioms Johnson.Prover.Link.served_of_look
