-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/TreeClass.lean: A LAW ON THE PROGRAM's TEXT THAT LAYS A PROVER's
MESSAGE INTO TREES (`layTrees`, OnBytes/Iop/Ground.lean): TWO ORACLE MESSAGES OF ONE SENDING THAT
LIE IN ONE TREE HAVE ONE CLASS OF LEAVES. No state, no plan. The library's laws on that text
(OnBytes/Iop/LayTreesLaws.lean) say of a message's tree its lengths and widths, nothing of classes.
A tool for `ReadFits.own` at the switch into group 1. A definition; statements with their proofs.

  `ClassAt sent s j` in the state of a placing pass: message j's tree is there in the list of
                    classes, with message j's class
  `passStep_sizes`, `passStep_keepsC`, `passStep_placesC`, `pass_invC` one step keeps "as many
                    classes as trees", leaves every other message's, places its own; so a pass. THE
                    LIBRARY's `passStep_keeps`, `passStep_places`, `pass_inv` carry `Placed`: their
                    lines stand here again at the list of classes
  `laid_class` behind both passes every message has it
  `layTrees_class` THE TOP: `layTrees cs sent = some L` · i, j below the number of messages ·
                    `L.tree.getD i 0 = L.tree.getD j 0` ⊢ the two notices have the same `leafClass`

By, all the library's: `passStep`, `laid`, `layTrees_eq`, `foldl_range_inv`, `passStep_size`,
`passStep_skip` (OnBytes/Iop/LayTreesLaws.lean). Near relatives, not called: `LayInv`,
`layTrees_two` (OnBytes/Params/Fit/TreesFew.lean): where a sending's messages lie in at most two
classes there are at most two trees; that file says of itself "Nothing on what lies in a tree". A
sister of the top's form, a premise there: `fill_total` (Johnson/Desc/Own/TreesMean.lean) asks that
two messages of one tree have one length of mask rows.

Limits. The converse is not said: two messages of one class may lie in two trees (main rows of two
lengths). Nothing on any property.


-/
import OnBytes.Iop.LayTreesLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open OnBytes.LayTreesLaws (State passStep laid layTrees_eq foldl_range_inv passStep_size
  passStep_skip fillStep settle)

/-- Message j's tree is there in the list of classes, with message j's class. -/
def ClassAt (sent : Array OracleNotice) (s : State) (j : Nat) : Prop :=
  s.2.1[s.2.2.getD j 0]? = some (sent.getD j default).leafClass

/-- A step keeps "as many classes as trees". -/
theorem passStep_sizes (codes : Codes) (sent : Array OracleNotice) (b : Bool) (s : State)
    (k : Nat) (h : s.2.1.size = s.1.size) :
    (passStep codes sent b s k).2.1.size = (passStep codes sent b s k).1.size := by
  simp only [passStep]
  split
  · exact h
  · split
    · exact h
    · simp [h]

/-- A step leaves the class of every other message's tree as it is. -/
theorem passStep_keepsC (codes : Codes) (sent : Array OracleNotice) (b : Bool) (s : State)
    (j k : Nat) (hjk : j ≠ k) (cl : Nat) (h : s.2.1[s.2.2.getD j 0]? = some cl) :
    (passStep codes sent b s k).2.1[(passStep codes sent b s k).2.2.getD j 0]? = some cl := by
  have hkj : k ≠ j := fun e => hjk e.symm
  simp only [Array.getD_eq_getD_getElem?] at h
  simp only [passStep]
  split
  · simpa using h
  · split
    · simpa [Array.getElem?_setIfInBounds, hkj] using h
    · have hlt := (Array.getElem?_eq_some_iff.1 h).1
      simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, hkj, if_false]
      rw [Array.getElem?_push, if_neg (Nat.ne_of_lt hlt)]
      exact h

/-- A step of its own pass places its message in a tree of its class. -/
theorem passStep_placesC (codes : Codes) (sent : Array OracleNotice) (b : Bool) (s : State)
    (k : Nat) (hk : ((sent.getD k default).shape.mainRows == 0) = b) (hsz : k < s.2.2.size)
    (h : s.2.1.size = s.1.size) : ClassAt sent (passStep codes sent b s k) k := by
  simp only [ClassAt, passStep]
  rw [if_neg (by rw [hk]; simp)]
  split
  · rename_i t ht
    have hfit := List.find?_some ht
    have hmem := List.mem_range.1 (List.mem_of_find?_eq_some ht)
    have hmem' : t < s.2.1.size := by rw [h]; exact hmem
    simp only [Bool.and_eq_true, beq_iff_eq] at hfit
    have e := hfit.1
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hmem', Option.getD_some] at e
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, if_pos hsz, if_true,
      Option.getD_some]
    rw [Array.getElem?_eq_getElem hmem', e, Array.getD_eq_getD_getElem?]
  · simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, if_pos hsz, if_true,
      Option.getD_some]
    rw [← h, Array.getElem?_push_size]

/-- Behind a pass every message of the pass has it, and so has every message that had. -/
theorem pass_invC (codes : Codes) (sent : Array OracleNotice) (b : Bool) (D : Nat → Prop)
    (s0 : State) (hsz : s0.2.2.size = sent.size) (hc : s0.2.1.size = s0.1.size)
    (h0 : ∀ j, D j → ClassAt sent s0 j) :
    ((List.range sent.size).foldl (passStep codes sent b) s0).2.2.size = sent.size ∧
      ((List.range sent.size).foldl (passStep codes sent b) s0).2.1.size =
        ((List.range sent.size).foldl (passStep codes sent b) s0).1.size ∧
      ∀ j, D j ∨ (j < sent.size ∧ ((sent.getD j default).shape.mainRows == 0) = b) →
        ClassAt sent ((List.range sent.size).foldl (passStep codes sent b) s0) j := by
  refine foldl_range_inv (passStep codes sent b)
    (fun k s => s.2.2.size = sent.size ∧ s.2.1.size = s.1.size ∧
      ∀ j, D j ∨ (j < k ∧ ((sent.getD j default).shape.mainRows == 0) = b) →
        ClassAt sent s j)
    sent.size s0 ⟨hsz, hc, ?_⟩ ?_
  · intro j hj
    rcases hj with hj | hj
    · exact h0 j hj
    · exact absurd hj.1 (Nat.not_lt_zero j)
  · intro k s hk ⟨hs, hcs, hp⟩
    refine ⟨by rw [passStep_size, hs], passStep_sizes codes sent b s k hcs, ?_⟩
    intro j hj
    by_cases hb : ((sent.getD k default).shape.mainRows == 0) = b
    · by_cases hjk : j = k
      · subst hjk
        exact passStep_placesC codes sent b s j hb (by omega) hcs
      · have hj' : D j ∨ (j < k ∧ ((sent.getD j default).shape.mainRows == 0) = b) := by
          rcases hj with hj | hj
          · exact Or.inl hj
          · exact Or.inr ⟨by omega, hj.2⟩
        exact passStep_keepsC codes sent b s j k hjk _ (hp j hj')
    · rw [passStep_skip codes sent b s k hb]
      apply hp j
      rcases hj with hj | hj
      · exact Or.inl hj
      · have hjk : j ≠ k := fun e => hb (e ▸ hj.2)
        exact Or.inr ⟨by omega, hj.2⟩

/-- Behind both passes every message lies in a tree of its class. -/
theorem laid_class (codes : Codes) (sent : Array OracleNotice) (j : Nat) (hj : j < sent.size) :
    ClassAt sent (laid codes sent) j := by
  have h1 := pass_invC codes sent false (fun _ => False) (#[], #[], Array.replicate sent.size 0)
    (by simp) rfl (fun _ h => h.elim)
  have h2 := pass_invC codes sent true
    (fun j => j < sent.size ∧ ((sent.getD j default).shape.mainRows == 0) = false) _ h1.1 h1.2.1
    (fun j h => h1.2.2 j (Or.inr h))
  apply h2.2.2 j
  by_cases hb : ((sent.getD j default).shape.mainRows == 0) = true
  · exact Or.inr ⟨hj, hb⟩
  · exact Or.inl ⟨hj, eq_false_of_ne_true hb⟩

/-- **Two messages of one tree have one class of leaves.** -/
theorem layTrees_class (cs : Codes) (sent : Array OracleNotice) (L : TreeLay)
    (h : layTrees cs sent = some L) {i j : Nat} (hi : i < sent.size) (hj : j < sent.size)
    (e : L.tree.getD i 0 = L.tree.getD j 0) :
    (sent.getD i default).leafClass = (sent.getD j default).leafClass := by
  rw [layTrees_eq] at h
  cases hf : (List.range sent.size).foldlM (fillStep cs sent (laid cs sent).2.2)
      ((laid cs sent).1, #[], Array.replicate (laid cs sent).1.size 0) with
  | none =>
    rw [hf] at h
    cases h
  | some filled =>
    rw [hf, Option.bind_some] at h
    split at h
    · cases h
      have a := laid_class cs sent i hi
      have b := laid_class cs sent j hj
      unfold ClassAt at a b
      have e' : (laid cs sent).2.2.getD i 0 = (laid cs sent).2.2.getD j 0 := e
      rw [e'] at a
      exact Option.some.inj (a.symm.trans b)
    · cases h

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.passStep_sizes
#print axioms VerifiableInference.Desc.K2.Honest.Returns.passStep_keepsC
#print axioms VerifiableInference.Desc.K2.Honest.Returns.passStep_placesC
#print axioms VerifiableInference.Desc.K2.Honest.Returns.pass_invC
#print axioms VerifiableInference.Desc.K2.Honest.Returns.laid_class
#print axioms VerifiableInference.Desc.K2.Honest.Returns.layTrees_class
