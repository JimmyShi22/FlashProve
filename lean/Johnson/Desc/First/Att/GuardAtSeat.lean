-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/GuardAtSeat.lean: kind K5: THE GUARD's YES AT THE SEAT's OWN PUBLIC RECORD,
AT EVERY o: a yes of every named test of k5AsksFilesN (Att/GuardN.lean), which makes its record by
Verify.publicOf, is the guard's yes at every attention segment of whatever record
PlanWritten.publicOfO o returns at the same three files.

Why it holds. Two returns of publicOfO at two arguments o differ at most in the three digests of the
lists of lookup calls (publicOfO_two, Johnson/Desc/Ok/PlanWritten/PublicAtTwo.lean);
publicOf is publicOfO at the second hash function itself (publicOfO_older); and no test of
the guard reads a digest (guard_digests, links_digests: by unfolding).

Main names:
  `guard_digests`, `links_digests`: the guard and its walk do not read the record's digests.
  `asksFiles_give_O`: **the statement above.**
  `asksFilesO_give`, `asksFilesO_at`: the like for the filling with the second hash function as a
    letter (k5AsksFilesO, Att/GuardO.lean): its yes is the guard's yes at the record that publicOfO
    o returns: the seat's own.
  `asksFilesO_older`: at the second hash function itself the two fillings are one list.
    `asksFilesO_of_files`: a yes of the elder filling carries to the new one, test by test, wherever
    publicOfO o returns. `asks_digests`: by unfolding.
  `rowsW_give`, `rowsO_at`, `rows_at`: **the law's line for the door's rows** (K5Asks.masks … held,
    K5Asks.rows: Att/GuardO.lean): the seven rows' yes at (o pol lay KL) is the guard's yes at every
    attention segment of the record that publicOfO o returns. `all_of_rows`: a tool.
So a yes that was asked at publicOf's record speaks of every o at which publicOfO returns. Which of
the two fillings a verifier asks is the choice of that verifier's own files: the elder names
the second hash function beneath the verifier's text; the new one takes it as a letter.
Limits. One direction. The filling's yes holds "publicOf returns at these files" within it: a fact
at the second hash function itself; at an o at which publicOfO returns and publicOf does not, the
filling refuses. Nothing says at which o a record is returned.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.GuardNLaw
import Johnson.Desc.First.Att.GuardO
import Johnson.Desc.Ok.PlanWritten.PublicAtTwo
import Johnson.Desc.Ok.PlanWritten.PublicAtLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open VerifiableInference.PlanWritten (publicOfO publicOfO_two publicOfO_older)
open VerifiableInference.Desc.First.Look (lookAt)

/-- The guard does not read the record's digests. -/
theorem guard_digests (W : Verify.Public) (d : Verify.Digests) (l g : Nat) :
    k5GuardN { W with digests := d } l g = k5GuardN W l g := rfl

/-- Nor does its walk. -/
theorem links_digests (W : Verify.Public) (d : Verify.Digests) :
    attLinksN { W with digests := d } = attLinksN W := rfl

/-- **The guard's yes at the seat's own public record, at every o.** -/
theorem asksFiles_give_O {o : Nat → ByteArray → ByteArray} (pol lay KL : ByteArray)
    (h : ∀ t ∈ k5AsksFilesN pol lay KL, t.2 = true) {W : Verify.Public}
    (hW : publicOfO o pol KL (some lay) = .ok W) :
    ∀ y ∈ attLinksN W, k5GuardN W y.1 y.2 = true := by
  obtain ⟨W₀, h0, H⟩ := asksFiles_give pol lay KL h
  have e := publicOfO_two ((publicOfO_older pol KL (some lay)).trans h0) hW
  intro y hy
  rw [e] at hy ⊢
  rw [links_digests] at hy
  rw [guard_digests]
  exact H y hy

/-! ## The filling with the second hash function as a letter -/

/-- Nor does the list of all segments' tests. -/
theorem asks_digests (W : Verify.Public) (d : Verify.Digests) :
    k5AsksN { W with digests := d } = k5AsksN W := rfl

/-- A yes of every named test of k5AsksFilesO o gives the record and the guard's yes at every
attention segment of it. -/
theorem asksFilesO_give {o : Nat → ByteArray → ByteArray} (pol lay KL : ByteArray)
    (h : ∀ t ∈ k5AsksFilesO o pol lay KL, t.2 = true) :
    ∃ W, publicOfO o pol KL (some lay) = .ok W ∧
      ∀ y ∈ attLinksN W, k5GuardN W y.1 y.2 = true := by
  unfold k5AsksFilesO at h
  cases hW : publicOfO o pol KL (some lay) with
  | error e =>
    rw [hW] at h
    exact absurd (h _ (List.mem_singleton.2 rfl)) (by simp)
  | ok W =>
    rw [hW] at h
    exact ⟨W, rfl, asks_give W h⟩

/-- **The law's line**: at the record that publicOfO o returns: the seat's own. -/
theorem asksFilesO_at {o : Nat → ByteArray → ByteArray} (pol lay KL : ByteArray)
    (h : ∀ t ∈ k5AsksFilesO o pol lay KL, t.2 = true) {W : Verify.Public}
    (hW : publicOfO o pol KL (some lay) = .ok W) :
    ∀ y ∈ attLinksN W, k5GuardN W y.1 y.2 = true := by
  obtain ⟨W', h', H⟩ := asksFilesO_give pol lay KL h
  obtain rfl : W' = W := Except.ok.inj (h'.symm.trans hW)
  exact H

/-- At the second hash function itself the two fillings are one. -/
theorem asksFilesO_older (pol lay KL : ByteArray) :
    k5AsksFilesO OnBytes.secondHashFunction pol lay KL = k5AsksFilesN pol lay KL := by
  unfold k5AsksFilesO k5AsksFilesN
  rw [publicOfO_older]
  cases Model.Verify.publicOf pol KL (some lay) <;> rfl

/-- **What was asked at publicOf's record carries to the filling at o, test by test**, wherever
publicOfO o returns. -/
theorem asksFilesO_of_files {o : Nat → ByteArray → ByteArray} (pol lay KL : ByteArray)
    (h : ∀ t ∈ k5AsksFilesN pol lay KL, t.2 = true) {W : Verify.Public}
    (hW : publicOfO o pol KL (some lay) = .ok W) :
    ∀ t ∈ k5AsksFilesO o pol lay KL, t.2 = true := by
  unfold k5AsksFilesN at h
  cases h0 : Model.Verify.publicOf pol KL (some lay) with
  | error e =>
    rw [h0] at h
    exact absurd (h _ (List.mem_singleton.2 rfl)) (by simp)
  | ok W₀ =>
    rw [h0] at h
    have e := publicOfO_two ((publicOfO_older pol KL (some lay)).trans h0) hW
    unfold k5AsksFilesO
    rw [hW]
    show ∀ t ∈ k5AsksN W, t.2 = true
    rw [e, asks_digests]
    exact h

/-! ## One function a row -/

/-- The seven tests, each by itself, give the whole list's yes: testAt is the list's entries. -/
theorem all_of_rows (a : Attention.Plan) (x : VerifiableInference.Desc.First.Look.Place) (p : Par)
    (h : ∀ k < 7, K5Asks.testAt k a x p = true) : (guardListN a x p).all (·.2) = true := by
  have h0 := h 0 (by omega)
  have h1 := h 1 (by omega)
  have h2 := h 2 (by omega)
  have h3 := h 3 (by omega)
  have h4 := h 4 (by omega)
  have h5 := h 5 (by omega)
  have h6 := h 6 (by omega)
  unfold guardListN
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  exact ⟨h0, h1, h2, h3, h4, h5, h6⟩

/-- **The seven rows at a record give the guard's yes at every attention segment of it.** -/
theorem rowsW_give (W : Verify.Public) (h : ∀ k < 7, K5Asks.rowW k W = true) :
    ∀ y ∈ attLinksN W, k5GuardN W y.1 y.2 = true := by
  intro y hy
  have hk : ∀ k < 7, (match W.A[y.2]?, lookAt W y.1 false with
      | some a, some x => K5Asks.testAt k a x (parN W y.1 a)
      | _, _ => false) = true := fun k hk => List.all_eq_true.1 (h k hk) y hy
  unfold k5GuardN k5ListN
  cases hA : W.A[y.2]? with
  | none =>
    have h0 := hk 0 (by omega)
    rw [hA] at h0
    cases h0
  | some a =>
    cases hx : lookAt W y.1 false with
    | none =>
      have h0 := hk 0 (by omega)
      rw [hA, hx] at h0
      cases h0
    | some x =>
      refine all_of_rows a x _ fun k hk' => ?_
      have h1 := hk k hk'
      rw [hA, hx] at h1
      exact h1

/-- **The law's line, row by row**: the seven functions' yes at (o pol lay KL) is the guard's yes at
the record that publicOfO o returns: the seat's own. -/
theorem rowsO_at {o : Nat → ByteArray → ByteArray} {pol lay KL : ByteArray}
    (h0 : K5Asks.masks o pol lay KL = true) (h1 : K5Asks.usual o pol lay KL = true)
    (h2 : K5Asks.calls o pol lay KL = true) (h3 : K5Asks.nums o pol lay KL = true)
    (h4 : K5Asks.pos o pol lay KL = true) (h5 : K5Asks.units o pol lay KL = true)
    (h6 : K5Asks.held o pol lay KL = true) {W : Verify.Public}
    (hW : publicOfO o pol KL (some lay) = .ok W) :
    ∀ y ∈ attLinksN W, k5GuardN W y.1 y.2 = true := by
  unfold K5Asks.masks K5Asks.rowO at h0
  unfold K5Asks.usual K5Asks.rowO at h1
  unfold K5Asks.calls K5Asks.rowO at h2
  unfold K5Asks.nums K5Asks.rowO at h3
  unfold K5Asks.pos K5Asks.rowO at h4
  unfold K5Asks.units K5Asks.rowO at h5
  unfold K5Asks.held K5Asks.rowO at h6
  rw [hW] at h0 h1 h2 h3 h4 h5 h6
  refine rowsW_give W fun k hk => ?_
  rcases k with _ | _ | _ | _ | _ | _ | _ | k
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · omega

/-- The same from the list of the seven rows with their words. -/
theorem rows_at {o : Nat → ByteArray → ByteArray} {pol lay KL : ByteArray}
    (h : ∀ t ∈ K5Asks.rows o pol lay KL, t.2 = true) {W : Verify.Public}
    (hW : publicOfO o pol KL (some lay) = .ok W) :
    ∀ y ∈ attLinksN W, k5GuardN W y.1 y.2 = true := by
  unfold K5Asks.rows at h
  rw [hW] at h
  refine rowsW_give W fun k hk => ?_
  have hw : k < K5Asks.words.length := hk
  exact h (K5Asks.words[k], K5Asks.rowW k W) (List.mem_map.2 ⟨(K5Asks.words[k], k),
    List.mem_iff_getElem?.2 ⟨k, by rw [List.getElem?_zipIdx, List.getElem?_eq_getElem hw]; simp⟩,
    rfl⟩)

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.all_of_rows
#print axioms VerifiableInference.Desc.First.Att.P.rowsW_give
#print axioms VerifiableInference.Desc.First.Att.P.rowsO_at
#print axioms VerifiableInference.Desc.First.Att.P.rows_at
#print axioms VerifiableInference.Desc.First.Att.P.asks_digests
#print axioms VerifiableInference.Desc.First.Att.P.asksFilesO_give
#print axioms VerifiableInference.Desc.First.Att.P.asksFilesO_at
#print axioms VerifiableInference.Desc.First.Att.P.asksFilesO_older
#print axioms VerifiableInference.Desc.First.Att.P.asksFilesO_of_files
#print axioms VerifiableInference.Desc.First.Att.P.guard_digests
#print axioms VerifiableInference.Desc.First.Att.P.links_digests
#print axioms VerifiableInference.Desc.First.Att.P.asksFiles_give_O
