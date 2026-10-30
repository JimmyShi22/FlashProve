-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Book/LayOmega.lean: THE PROVER's MESSAGE WITH OMEGA (linMessageOmega,
OnBytes/Iop/Lin.lean), AS layTrees PLACES IT IN TREES: AT EVERY LAWFUL SHAPE OMEGA LIES ALONE IN
TREE 0, AND THAT TREE HAS THE SHAPE OF A TREE LAID FOR OMEGA ALONE. Statements and proofs over
Johnson/Desc/Book/LayAlone.lean. No definition.



Why. The shared chain sends Omega, with the split's message beside it where the shape splits, and
its book gets the tree that layTrees makes of that sending. The last chain lays a tree anew for
Omega's copy, alone (Johnson/Desc/Third/Law/TreeShape.lean). That the two trees have one shape
follows here from a test that both chains ask
anyway: the shape is lawful (LinShape.ok, the first clause of linOk).

  ok_of_linOk        linOk's first clause.
  ok_omega_main      a lawful shape: Omega has main rows.
  ok_split           a lawful shape that splits: the split's message has no main rows, and its class
                     of leaves is not Omega's.
  tree_two           two messages, the first with main rows, the second without, of two classes of
                     leaves: trees 0 and 1.
  tree_omega         the message with Omega: Omega in tree 0; the split's message, if any, in 1.
  uniq_omega, shapes_pos_omega, tree_omega_at   Omega is alone in its tree; there is a tree 0; the
                     same as tree_omega in the form T.tree[i]? = some i.
  lay_omega_alone    that sending's tree 0 has the shape shapeAlone codes S.omega.
  lay_omega_same     it is the shape of tree 0 of the layout of Omega's notice alone.
IS IT EMPTY? Two premises. (1) S.ok = true: linOk at the state's codes and the plan's shape is one
of the tests on the verifier's state in a file of evaluations
(not in this library: "linOk", "lin₀"); on the honest walk of both stored
key files (synthetic weights; small and full size) no test said no at any border (evaluated there
in a build of that file's own). (2) layTrees returns a layout:
for Omega's notice alone by laid_tree_shape, since K14's second part accepted on that walk; for the
message with Omega it is printed nowhere by itself: the shared chain's sending of Omega accepted on
that walk. Prints, no theorem.
WHAT IS NOT HERE. Anything on a state, a book or a run; that the two chains' codes are one; that an
IOP as written in Lean tells of Omega's tree what this layout says. Nothing on soundness.

-/
import Johnson.Desc.Book.LayAlone
import OnBytes.Iop.Lin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Book
open OnBytes
open OnBytes.Params (LinShape laidOf layPass layStep)
open OnBytes.Tie.Pv.Keeps.Fit

/-- linOk's first clause. -/
theorem ok_of_linOk {codes : Codes} {S : LinShape} (h : linOk codes S = true) : S.ok = true := by
  unfold linOk at h
  simp only [Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1

/-- A lawful shape: Omega has main rows. -/
theorem ok_omega_main {S : LinShape} (h : S.ok = true) : (S.omega.mainRows == 0) = false := by
  unfold LinShape.ok at h
  simp only [Bool.and_eq_true] at h
  have v : LinShape.vectorMessageOk S.omega = true := h.1.1.1.1.1.1.1.1.2
  unfold LinShape.vectorMessageOk at v
  simp only [Bool.and_eq_true] at v
  have m : (S.omega.mainRows != 0) = true := v.1.1.2
  cases e : (S.omega.mainRows == 0) with
  | false => rfl
  | true =>
    rw [bne, e] at m
    cases m

/-- A lawful shape that splits: the split's message has no main rows, and its class of leaves is not
Omega's. -/
theorem ok_split {S : LinShape} (h : S.ok = true) (hs : S.sharedSplitNeeded = true) :
    (S.sharedSplit.mainRows == 0) = true ∧
      (S.omegaLeafClass == S.sharedSplitLeafClass) = false := by
  unfold LinShape.ok at h
  simp only [Bool.and_eq_true] at h
  have c : (!S.sharedSplitNeeded || S.omegaLeafClass != S.sharedSplitLeafClass) = true :=
    h.1.1.1.2
  have m : (!S.sharedSplitNeeded ||
      LinShape.splitMessageOk S.sharedSplit S.sharedMaskCode) = true := h.1.2
  rw [hs] at c m
  have c' : (S.omegaLeafClass != S.sharedSplitLeafClass) = true := c
  have m' : LinShape.splitMessageOk S.sharedSplit S.sharedMaskCode = true := m
  unfold LinShape.splitMessageOk at m'
  simp only [Bool.and_eq_true] at m'
  refine ⟨m'.1.1.1, ?_⟩
  cases e : (S.omegaLeafClass == S.sharedSplitLeafClass) with
  | false => rfl
  | true =>
    rw [bne, e] at c'
    cases c'

/-- Two messages, the first with main rows, the second without, of two classes of leaves: the first
pass lays the first into tree 0, the second pass the second into tree 1. -/
theorem tree_two {codes : Codes} {n0 n1 : OracleNotice} {T : TreeLay}
    (h : layTrees codes #[n0, n1] = some T) (h0 : (n0.shape.mainRows == 0) = false)
    (h1 : (n1.shape.mainRows == 0) = true) (hc : (n0.leafClass == n1.leafClass) = false) :
    T.tree.getD 0 0 = 0 ∧ T.tree.getD 1 0 = 1 := by
  obtain ⟨_, _, eT, _⟩ := layTrees_some h
  rw [eT]
  have r2 : List.range 2 = [0, 1] := rfl
  have r1 : List.range 1 = [0] := rfl
  first
    | (constructor <;> simp [laidOf, layPass, layStep, h0, h1, hc, r2, r1])
    | (constructor <;> simp [laidOf, layPass, layStep, h0, h1, hc, List.range_succ])
    | (simp [laidOf, layPass, layStep, h0, h1, hc, r2, r1, Array.replicate, Array.setIfInBounds])

/-- The message with Omega, where the shape splits. -/
theorem omega_two (S : LinShape) (h : S.sharedSplitNeeded = true) :
    linMessageOmega S =
      #[⟨S.omega, S.omegaLeafClass⟩, ⟨S.sharedSplit, S.sharedSplitLeafClass⟩] := by
  unfold linMessageOmega
  simp [h]

/-- The message with Omega, where it does not. -/
theorem omega_one (S : LinShape) (h : S.sharedSplitNeeded = false) :
    linMessageOmega S = #[⟨S.omega, S.omegaLeafClass⟩] := by
  unfold linMessageOmega
  simp [h]

/-- **The message with Omega: Omega lies in tree 0; the split's message, if any, in tree 1.** -/
theorem tree_omega {codes : Codes} {S : LinShape} {T : TreeLay} (hok : S.ok = true)
    (h : layTrees codes (linMessageOmega S) = some T) :
    T.tree.getD 0 0 = 0 ∧ (S.sharedSplitNeeded = true → T.tree.getD 1 0 = 1) := by
  cases hs : S.sharedSplitNeeded with
  | true =>
    rw [omega_two S hs] at h
    obtain ⟨m, c⟩ := ok_split hok hs
    obtain ⟨a, b⟩ := tree_two h (ok_omega_main hok) m c
    exact ⟨a, fun _ => b⟩
  | false =>
    rw [omega_one S hs] at h
    exact ⟨tree_single h, fun e => by cases e⟩

/-- The message with Omega holds a message. -/
theorem omega_size_pos (S : LinShape) : 0 < (linMessageOmega S).size := by
  cases hs : S.sharedSplitNeeded with
  | true => rw [omega_two S hs]; simp
  | false => rw [omega_one S hs]; simp

/-- Omega is alone in its tree. -/
theorem uniq_omega {codes : Codes} {S : LinShape} {T : TreeLay} (hok : S.ok = true)
    (h : layTrees codes (linMessageOmega S) = some T) :
    ∀ j, j < (linMessageOmega S).size → T.tree.getD j 0 = T.tree.getD 0 0 → j = 0 := by
  obtain ⟨t0, t1⟩ := tree_omega hok h
  intro j hj e
  cases hs : S.sharedSplitNeeded with
  | true =>
    rw [omega_two S hs] at hj
    have hj' : j < 2 := by simpa using hj
    rcases Nat.lt_or_ge j 1 with q | q
    · omega
    · obtain rfl : j = 1 := by omega
      rw [t1 hs, t0] at e
      cases e
  | false =>
    rw [omega_one S hs] at hj
    have hj' : j < 1 := by simpa using hj
    omega

/-- There is a tree 0. -/
theorem shapes_pos_omega {codes : Codes} {S : LinShape} {T : TreeLay} (hok : S.ok = true)
    (h : layTrees codes (linMessageOmega S) = some T) : 0 < T.shapes.size := by
  have a := (lay_one h (omega_size_pos S) (uniq_omega hok h)).1
  rw [(tree_omega hok h).1] at a
  exact a

/-- An entry that is there, by its reading with a default. -/
theorem getElem?_of_getD {α : Type} (a : Array α) (i : Nat) (d : α) (h : i < a.size) :
    a[i]? = some (a.getD i d) := by
  first
    | simp [Array.getD, h]
    | simp [Array.getD_eq_getD_getElem?, h]

/-- A layout names a tree for every message. -/
theorem tree_size {codes : Codes} {sent : Array OracleNotice} {T : TreeLay}
    (h : layTrees codes sent = some T) (hpos : 0 < sent.size) : T.tree.size = sent.size := by
  obtain ⟨_, _, eT, _⟩ := layTrees_some h
  obtain ⟨pi, _⟩ := laid_spec (codes := codes) hpos
  rw [eT]
  exact pi.2

/-- tree_omega in the form "the entry is there". -/
theorem tree_omega_at {codes : Codes} {S : LinShape} {T : TreeLay} (hok : S.ok = true)
    (h : layTrees codes (linMessageOmega S) = some T) :
    T.tree[0]? = some 0 ∧ (S.sharedSplitNeeded = true → T.tree[1]? = some 1) := by
  obtain ⟨t0, t1⟩ := tree_omega hok h
  have sz := tree_size h (omega_size_pos S)
  refine ⟨?_, fun hs => ?_⟩
  · rw [getElem?_of_getD T.tree 0 0 (by rw [sz]; exact omega_size_pos S), t0]
  · have two : (linMessageOmega S).size = 2 := by rw [omega_two S hs]; rfl
    rw [getElem?_of_getD T.tree 1 0 (by rw [sz, two]; omega), t1 hs]

/-- **That sending's tree 0 has the shape of a tree that holds Omega alone.** -/
theorem lay_omega_alone {codes : Codes} {S : LinShape} {T : TreeLay} (hok : S.ok = true)
    (h : layTrees codes (linMessageOmega S) = some T) :
    T.shapes.getD 0 {} = shapeAlone codes S.omega := by
  obtain ⟨t0, t1⟩ := tree_omega hok h
  cases hs : S.sharedSplitNeeded with
  | true =>
    rw [omega_two S hs] at h
    have a := lay_alone (i0 := 0) h (by simp) (fun j hj e => by
      have hj' : j < 2 := by simpa using hj
      rcases Nat.lt_or_ge j 1 with q | q
      · omega
      · obtain rfl : j = 1 := by omega
        rw [t1 hs, t0] at e
        cases e)
    rw [t0] at a
    simpa using a
  | false =>
    rw [omega_one S hs] at h
    exact lay_single h

/-- **It is the shape of tree 0 of the layout of Omega's notice alone.** -/
theorem lay_omega_same {codes : Codes} {S : LinShape} {T₂ T₁ : TreeLay} (hok : S.ok = true)
    (h₂ : layTrees codes (linMessageOmega S) = some T₂)
    (h₁ : layTrees codes #[⟨S.omega, S.omegaLeafClass⟩] = some T₁) :
    T₂.shapes.getD 0 {} = T₁.shapes.getD 0 {} := by
  rw [lay_omega_alone hok h₂, lay_single h₁]

end VerifiableInference.Desc.Book

#print axioms VerifiableInference.Desc.Book.tree_two
#print axioms VerifiableInference.Desc.Book.tree_omega
#print axioms VerifiableInference.Desc.Book.tree_omega_at
#print axioms VerifiableInference.Desc.Book.shapes_pos_omega
#print axioms VerifiableInference.Desc.Book.lay_omega_alone
#print axioms VerifiableInference.Desc.Book.lay_omega_same
