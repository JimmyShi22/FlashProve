-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ChainEndCovered.lean: the chains' end's law joined with "a statement only grows": what
stood in the statement AT ANY BORDER of a chain is covered at the chain's end. Theorems.

  Covered T T'        every group of T stands in T' under its number, with its code, its members and
                      the mark inRun; every message that is sampled in T stands in T' under its
                      number, with its shape, sampled, and names there a group that is there and has
                      the mark.
  covered_of          Grows T T' and NothingLeft T' give Covered T T'.
  chainAt_covered     **at every border**: a chain whose blocks all keep Grows (read by st), with
                      the end as last block and untestedL's clauses among its own: where the chain's
                      decision says yes, the statement at each border is covered by the last one.
What is not claimed. That a block of the protocol keeps Grows is a premise: each kind's own matter.
Nothing on rows: that a claim which was laid as a row on a group is among the rows that the group's
test takes in is not said here. "Has the mark" says that the test has begun, not that it was carried
through.

-/
import Johnson.Desc.ChainEndExact
import Johnson.Desc.FoldKeeps
import Johnson.Desc.Grows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.ChainEnd
open OnBytes VerifiableInference.Desc

/-- What stood in T is covered in T'. -/
def Covered (T T' : Statement) : Prop :=
  (∀ (i : Nat) G, T.groups[i]? = some G →
    ∃ G', T'.groups[i]? = some G' ∧ GroupGrows G G' ∧ G'.inRun = true) ∧
  ∀ (i : Nat) x, T.oracles[i]? = some x →
    ∃ x', T'.oracles[i]? = some x' ∧ OracleGrows x x' ∧
      (x.sampled = true → ∃ g ∈ x'.groups, ∃ G, T'.groups[g]? = some G ∧ G.inRun = true)

/-- A statement that has grown into one in which nothing is left untested is covered by it. -/
theorem covered_of (T T' : Statement) (hg : Grows T T') (hn : NothingLeft T') : Covered T T' := by
  refine ⟨fun i G h => ?_, fun i x h => ?_⟩
  · obtain ⟨G', h', g⟩ := hg.2.1 i G h
    obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.1 h'
    exact ⟨G', h', g, he ▸ hn.1 i hi⟩
  · obtain ⟨x', h', g⟩ := hg.2.2 i x h
    obtain ⟨hi, he⟩ := Array.getElem?_eq_some_iff.1 h'
    refine ⟨x', h', g, fun hs => ?_⟩
    have := hn.2 i hi (by rw [he]; exact g.2.1 hs)
    rw [he] at this
    exact this

variable {S Cl : Type}

/-- The relation on records: the statement, read by st, grows. -/
def GrowsBy (st : S → Statement) : S → S → Prop := fun s s' => Grows (st s) (st s')

/-- **At every border of a chain, what stood in the statement is covered at the end.** -/
theorem chainAt_covered (name : String) (ft chain piece : Nat) (sealed : Bool)
    (inFront : List Fmt.DeclaredRound) (st : S → Statement) (ask : S → Clauses) (ha : Asks st ask)
    (l₁ l₂ : List (Block S Cl)) (hb : ∀ b ∈ l₁ ++ l₂, Keeps.Decides (GrowsBy st) b) (s s' : S)
    (v : Fmt.View)
    (h : chainAt name ft (l₁ ++ (l₂ ++ [chainEnd chain piece sealed inFront ask])) s v = .ok s') :
    ∃ t rs cols, foldBlocks ft l₁ s v.rounds v.opened = .ok (t, rs, cols) ∧
      Covered (st t) (st s') := by
  have hn : NothingLeft (st s') := by
    rw [← List.append_assoc] at h
    exact chainAt_nothing_left name ft chain piece sealed inFront st ask ha _ s s' v h
  have he : Keeps.Decides (GrowsBy st) (chainEnd (Cl := Cl) chain piece sealed inFront ask) := by
    intro a rs gs a' hd
    obtain ⟨hx, _⟩ := (chainEnd_decide_iff chain piece sealed inFront ask a a' rs gs).1 hd
    subst hx
    exact Grows.refl _
  obtain ⟨t, rs, cols, h1, _, h3⟩ := Keeps.chainAt_border (GrowsBy st) (fun a => Grows.refl _)
    (fun _ _ _ x y => Grows.trans x y) name ft l₁ (l₂ ++ [chainEnd chain piece sealed inFront ask])
    (by
      intro b hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hb b (List.mem_append_left _ hx)
      · rcases List.mem_append.1 hx with hx | hx
        · exact hb b (List.mem_append_right _ hx)
        · rcases List.mem_cons.1 hx with rfl | hx
          · exact he
          · cases hx) s s' v h
  exact ⟨t, rs, cols, h1, covered_of _ _ h3 hn⟩

end VerifiableInference.Desc.ChainEnd
