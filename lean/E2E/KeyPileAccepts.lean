-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyPileAccepts.lean: the rows on the committed matrix are made: the three tests that the
description's text asks of the claims on a lookup's keys (`Key.tableRowsOf`,
Johnson/Desc/Key/TableRows.lean) accept the claims that the lookup's own text lays (`K3.keyClaims`,
Johnson/Desc/First/Look/K3Key.lean), whatever was sent, if the points have the right lengths.
Statements and proofs.

What is shown.
  `mapM_at`: a small fact on lists.
  `keyClaims_at`: where `K3.keyClaims S F home g` returns: there is a claim for each part that was
    heard, and claim number i is the program's `Lkp.keysOf S theta alpha i` at the point that part
    i's key tree left, turned round (the lowest variable first).
  **`rows_made`**: so at `S := Wf.lookupOf id m l`, for parameters that pass the verifier's tests
    `Wf.lookupOk`, `Matrix.ok` and `Wf.fitsMatrix`: if a point was heard for each part, of one
    coordinate for each bit of a key's number, `Key.tableRowsOf m l` returns rows at these claims.
    By `passes_keysOf` and `tableRowsOf_of_passes` (E2E/KeyPasses.lean), which call the library's
    `Wf.Proved.pendOkKeys` (OnBytes/Tie/Pv/Lookup/PendOkKeys.lean).
  `tests_full`: the three tests accept the two lookups of the full size at a matrix of 3,076,096
    rows and 2^18 columns: by an evaluation in Lean's kernel.
  **`rows_made_full`**: so at both lookups of the full size.
With `tableRows_same` (E2E/KeyPile.lean) these rows have the weights and the column points of
`rowOfPoint` at the heard points.

Limits. A test of the verifier's that reads challenges and public values: nothing is shown of any
prover. That a hearing leaves a point for each part, of the right length, and that `keyClaims`
returns (every hidden value has a home), are premises. Nothing on hiding follows from this file.


-/
import E2E.KeyPasses
import E2E.KeyPile
import Johnson.Desc.First.Look.K3Key
import Johnson.Top.H.KeyRangesFull

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace AtPublicFiles.Key
open OnBytes
open OnBytes.Params (WfPart WfLookup)
open VerifiableInference.Desc.Key (tableRowsOf)
open VerifiableInference.Desc.K3 (keyClaims HeardG maskSide)
open Johnson.Pack (lk0Full lk1Full)
open Inst.Model.Layout (kRef)

/-- What a function that may refuse returns along a numbered list, member by member. -/
theorem mapM_at {α β : Type} (f : α × Nat → Option β) :
    ∀ (L : List α) (n : Nat) (R : List β), (L.zipIdx n).mapM f = some R →
      R.length = L.length ∧ ∀ i a, L[i]? = some a → ∃ b, R[i]? = some b ∧ f (a, n + i) = some b
  | [], n, R, e => by
    rw [List.zipIdx_nil, List.mapM_nil] at e
    obtain rfl : [] = R := Option.some.inj e
    exact ⟨rfl, fun i a h => absurd h (by simp)⟩
  | a :: L, n, R, e => by
    rw [List.zipIdx_cons, List.mapM_cons] at e
    cases ha : f (a, n) with
    | none => rw [ha] at e; exact absurd e (by simp)
    | some b =>
      cases hL : (L.zipIdx (n + 1)).mapM f with
      | none => rw [ha, hL] at e; exact absurd e (by simp)
      | some bs =>
        rw [ha, hL] at e
        obtain rfl : b :: bs = R := Option.some.inj e
        obtain ⟨h1, h2⟩ := mapM_at f L (n + 1) bs hL
        refine ⟨by rw [List.length_cons, List.length_cons, h1], fun i x hx => ?_⟩
        cases i with
        | zero =>
          obtain rfl : a = x := Option.some.inj hx
          exact ⟨b, rfl, ha⟩
        | succ i =>
          obtain ⟨y, hy, hf⟩ := h2 i x hx
          exact ⟨y, hy, by rw [← hf]; congr 2; omega⟩

/-- **The claims that the lookup's text lays are the program's, part by part.** -/
theorem keyClaims_at (S : Lkp.Public) (F : OnBytes.Model.Fork) (home : Array Slot) (g : HeardG)
    (keys : List Lkp.Keys) (h : keyClaims S F home g = some keys) :
    keys.length = g.keys.length ∧ ∀ i k, g.keys[i]? = some k → ∃ y : MaskForm × E,
      keys[i]? = some (Lkp.keysOf S g.theta g.alpha i ⟨k.1.toList.reverse, y.1, y.2⟩) := by
  unfold keyClaims at h
  obtain ⟨h1, h2⟩ := mapM_at _ g.keys 0 keys h
  refine ⟨h1, fun i k hk => ?_⟩
  obtain ⟨b, hb, hf⟩ := h2 i k hk
  dsimp only at hf
  cases hy : maskSide F home k.2 with
  | none => rw [hy] at hf; exact absurd hf (by simp)
  | some y =>
    rw [hy, Option.map_some, Nat.zero_add] at hf
    exact ⟨y, by rw [hb, ← Option.some.inj hf]⟩

/-- **The rows on the matrix are made.** -/
theorem rows_made (fBits id : Nat) (m : Wf.Matrix) (l : WfLookup) (F : OnBytes.Model.Fork)
    (home : Array Slot) (g : HeardG) (keys : List Lkp.Keys) (hl : Wf.lookupOk fBits l = true)
    (hm : m.ok = true) (hf : Wf.fitsMatrix m l = true)
    (h : keyClaims (Wf.lookupOf id m l) F home g = some keys)
    (hn : g.keys.length = l.parts.length)
    (hlen : ∀ (i : Nat) (p : WfPart) (k : Array E × OnBytes.Model.Aff), l.parts[i]? = some p →
      g.keys[i]? = some k → k.1.size = m.kCol + p.logPlaces) :
    (tableRowsOf m l keys).isSome = true := by
  obtain ⟨h1, h2⟩ := keyClaims_at _ F home g keys h
  refine AtPublicFiles.AtFiles.tableRowsOf_of_passes m l keys (by rw [h1, hn]) fun x hx => ?_
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hx
  obtain ⟨hp, hk⟩ := List.getElem?_zip_eq_some.1 hi
  have hlt : i < g.keys.length := by
    rw [hn]
    exact (List.getElem?_eq_some_iff.1 hp).1
  obtain ⟨y, hy⟩ := h2 i g.keys[i] (List.getElem?_eq_getElem hlt)
  rw [hk] at hy
  rw [Option.some.inj hy]
  refine AtPublicFiles.AtFiles.passes_keysOf fBits id m l i x.1 g.theta g.alpha _ hl hm hf hp ?_
  show (g.keys[i].1.toList.reverse).length = _
  rw [List.length_reverse, Array.length_toList]
  exact hlen i x.1 g.keys[i] hp (List.getElem?_eq_getElem hlt)

set_option maxRecDepth 1000000 in
/-- The verifier's three tests on the parameters accept the two lookups of the full size. -/
theorem tests_full : Wf.lookupOk 64 lk0Full = true ∧ Wf.lookupOk 64 lk1Full = true ∧
    (⟨kRef, 3076096⟩ : Wf.Matrix).ok = true ∧ Wf.fitsMatrix ⟨kRef, 3076096⟩ lk0Full = true ∧
    Wf.fitsMatrix ⟨kRef, 3076096⟩ lk1Full = true := by decide +kernel

/-- **At both lookups of the full size.** -/
theorem rows_made_full (id : Nat) (F : OnBytes.Model.Fork) (home : Array Slot) (g : HeardG)
    (keys : List Lkp.Keys) :
    (keyClaims (Wf.lookupOf id ⟨kRef, 3076096⟩ lk0Full) F home g = some keys →
      g.keys.length = lk0Full.parts.length →
      (∀ (i : Nat) (p : WfPart) (k : Array E × OnBytes.Model.Aff), lk0Full.parts[i]? = some p →
        g.keys[i]? = some k → k.1.size = kRef + p.logPlaces) →
      (tableRowsOf ⟨kRef, 3076096⟩ lk0Full keys).isSome = true) ∧
    (keyClaims (Wf.lookupOf id ⟨kRef, 3076096⟩ lk1Full) F home g = some keys →
      g.keys.length = lk1Full.parts.length →
      (∀ (i : Nat) (p : WfPart) (k : Array E × OnBytes.Model.Aff), lk1Full.parts[i]? = some p →
        g.keys[i]? = some k → k.1.size = kRef + p.logPlaces) →
      (tableRowsOf ⟨kRef, 3076096⟩ lk1Full keys).isSome = true) :=
  ⟨rows_made 64 id ⟨kRef, 3076096⟩ lk0Full F home g keys tests_full.1 tests_full.2.2.1
      tests_full.2.2.2.1,
    rows_made 64 id ⟨kRef, 3076096⟩ lk1Full F home g keys tests_full.2.1 tests_full.2.2.1
      tests_full.2.2.2.2⟩

end AtPublicFiles.Key

#print axioms AtPublicFiles.Key.mapM_at
#print axioms AtPublicFiles.Key.keyClaims_at
#print axioms AtPublicFiles.Key.rows_made
#print axioms AtPublicFiles.Key.tests_full
#print axioms AtPublicFiles.Key.rows_made_full
