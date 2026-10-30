-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB8/WrittenFull.lean: `writtenOf` (Johnson/G/RoundsOfPlan.lean) lays the written
declared rounds of a key file of full size (`declKeyFull`, Written.lean in this folder) as the
written dry lists (`dryKeyFull`, Johnson/G/DryKeyLit.lean). A general law, and closed statements by
evaluations in Lean's kernel.

How. `writtenOf` goes along each list in the monad of refusals, and counts the roots of the two
earlier chains by a sum. The going along in that monad is not asked of the kernel: `walk e l R` is a
test with code that goes along the declared and the written list at once; a yes gives what
`writtenOf`'s routine returns (`mapM_of_walk`). The sum is asked of the kernel at the shared chain's
68 rounds alone (`roots_shared`). At the first chain the roots are counted over the rounds that
send one (`rootsOf_filter`): the sum along 18,851 rounds is a recursion of that depth.

Main names.
  `walk`, `mapM_of_walk`, `three_ok`, `written_of_walks`: the test and the law.
  `rootsOf_filter`; `roots_first`, `roots_shared`: the first chain sends 6 trees, the shared 11.
  `walk_first`, `walk_shared`, `walk_third`: the three tests say yes.
  `written_full`: **writtenOf "key file" declKeyFull = .ok dryKeyFull.**
  `senders_bent`, `roots_shared_bent`: five senders for six, ten trees for eleven: no.
  `walk_first_bent`, `walk_shared_bent`, `walk_third_bent`: against the first written list less its
    last round; against the shared list with its first round in its last round's place; and
    where the first chain is said to send five trees, the tests say no.

A name that ends in `_bent`: the same test with one value changed, at which it says no: so the test
is seen to be able to fail.

Limits. Both sides are written values. Nothing on a description. Nothing on soundness.

-/
import Johnson.HB.LLHARD.KB8.Written

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB8

open Johnson.G Johnson.G.OfPlan
open OnBytes.Params (Rounds)
open OnBytes.Three (tagRoot tagRun)

/-! ## The law -/

/-- Along the declared and the written list at once: each declared round is laid as the written
one, with the same stored tables; the lists end together. -/
def walk (e : List (List ByteArray × ByteArray)) : List Fmt.DeclaredRound → Rounds → Bool
  | [], [] => true
  | r :: l, x :: R => decide (r.round e = some x.1) && decide (r.stored = x.2) && walk e l R
  | _, _ => false

/-- A yes gives what a routine returns that lays each round so. -/
theorem mapM_of_walk {e : List (List ByteArray × ByteArray)}
    (f : Fmt.DeclaredRound → Except String (Fmt.Round × List Fmt.Stored))
    (hf : ∀ r x, r.round e = some x → f r = .ok (x, r.stored)) :
    ∀ (l : List Fmt.DeclaredRound) (R : Rounds), walk e l R = true → l.mapM f = .ok R
  | [], [], _ => by
    rw [List.mapM_nil]
    rfl
  | r :: l, x :: R, h => by
    simp only [walk, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [List.mapM_cons, hf r x.1 h.1.1, mapM_of_walk f hf l R h.2, h.1.2]
    rfl
  | [], _ :: _, h => by simp [walk] at h
  | _ :: _, [], h => by simp [walk] at h

/-- Three such routines in a row. -/
theorem three_ok {e₁ e₂ e₃ : List (List ByteArray × ByteArray)}
    (f₁ f₂ f₃ : Fmt.DeclaredRound → Except String (Fmt.Round × List Fmt.Stored))
    (h₁ : ∀ r x, r.round e₁ = some x → f₁ r = .ok (x, r.stored))
    (h₂ : ∀ r x, r.round e₂ = some x → f₂ r = .ok (x, r.stored))
    (h₃ : ∀ r x, r.round e₃ = some x → f₃ r = .ok (x, r.stored))
    {D : Decl3} {R : Rounds × Rounds × Rounds} (w₁ : walk e₁ D.1 R.1 = true)
    (w₂ : walk e₂ D.2.1 R.2.1 = true) (w₃ : walk e₃ D.2.2 R.2.2 = true) :
    (do pure (← D.1.mapM f₁, ← D.2.1.mapM f₂, ← D.2.2.mapM f₃) :
      Except String (Rounds × Rounds × Rounds)) = .ok R := by
  rw [mapM_of_walk f₁ h₁ _ _ w₁, mapM_of_walk f₂ h₂ _ _ w₂, mapM_of_walk f₃ h₃ _ _ w₃]
  rfl

/-- **Where the three tests say yes, `writtenOf` returns the written lists.** n₁, n₂: the roots that
the two earlier chains send. -/
theorem written_of_walks {file : String} {D : Decl3} {R : Rounds × Rounds × Rounds} {n₁ n₂ : Nat}
    (r₁ : rootsOf D.1 = n₁) (r₂ : rootsOf D.2.1 = n₂) (w₁ : walk [] D.1 R.1 = true)
    (w₂ : walk [] D.2.1 R.2.1 = true)
    (w₃ : walk [((List.range n₁).map tagRoot, tagRun 1), ((List.range n₂).map tagRoot, tagRun 2)]
      D.2.2 R.2.2 = true) : writtenOf file D = .ok R := by
  subst r₁ r₂
  unfold writtenOf
  refine three_ok _ _ _ ?_ ?_ ?_ w₁ w₂ w₃ <;> intro r x h <;> simp only [h] <;> rfl

/-- The roots are counted over the rounds that send one. -/
theorem rootsOf_filter (l : List Fmt.DeclaredRound) :
    rootsOf l = rootsOf (l.filter fun r => r.entry.roots != 0) := by
  induction l with
  | nil => rfl
  | cons r l ih =>
    unfold rootsOf at ih ⊢
    rw [List.filter_cons]
    by_cases h : r.entry.roots = 0
    · simp [h, ih]
    · simp [h, ih]

/-! ## The closed statements -/

set_option maxRecDepth 1000000 in
/-- The rounds of the first chain that send a root: six, one root each. -/
theorem senders_first : (declKeyFull.1.filter fun r => r.entry.roots != 0).map (·.entry.roots) =
    [1, 1, 1, 1, 1, 1] := by decide +kernel

/-- The first chain sends six trees. -/
theorem roots_first : rootsOf declKeyFull.1 = 6 := by
  rw [rootsOf_filter]
  unfold rootsOf
  rw [senders_first]
  rfl

set_option maxRecDepth 1000000 in
/-- The shared chain sends eleven. -/
theorem roots_shared : rootsOf declKeyFull.2.1 = 11 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The test says yes along the third chain, where the two earlier chains send 6 and 11 trees. -/
theorem walk_third : walk
    [((List.range 6).map tagRoot, tagRun 1), ((List.range 11).map tagRoot, tagRun 2)]
    declKeyFull.2.2 dryKeyFull.2.2 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The test says yes along the shared chain. -/
theorem walk_shared : walk [] declKeyFull.2.1 dryKeyFull.2.1 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The test says yes along the first chain. -/
theorem walk_first : walk [] declKeyFull.1 dryKeyFull.1 = true := by decide +kernel

/-- **`writtenOf` lays the written declared rounds as the written dry lists.** -/
theorem written_full : writtenOf "key file" declKeyFull = .ok dryKeyFull :=
  written_of_walks roots_first roots_shared walk_first walk_shared walk_third

/-! ## The tests can fail -/

set_option maxRecDepth 1000000 in
/-- Five senders for six: no. -/
theorem senders_bent : decide ((declKeyFull.1.filter fun r => r.entry.roots != 0).map
    (·.entry.roots) = [1, 1, 1, 1, 1]) = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Ten trees for eleven: no. -/
theorem roots_shared_bent : decide (rootsOf declKeyFull.2.1 = 10) = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Where the first chain is said to send five trees, its tree number 5 cannot be taken over. -/
theorem walk_third_bent : walk
    [((List.range 5).map tagRoot, tagRun 1), ((List.range 11).map tagRoot, tagRun 2)]
    declKeyFull.2.2 dryKeyFull.2.2 = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Against the shared written list with its first round in its last round's place: the test goes
along 67 members and says no at the last. -/
theorem walk_shared_bent : walk [] declKeyFull.2.1
    (dryKeyFull.2.1.dropLast ++ dryKeyFull.2.1.take 1) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- Against the first written list less its last round. -/
theorem walk_first_bent : walk [] declKeyFull.1 dryKeyFull.1.dropLast = false := by
  decide +kernel

end Johnson.KB8

#print axioms Johnson.KB8.mapM_of_walk
#print axioms Johnson.KB8.three_ok
#print axioms Johnson.KB8.written_of_walks
#print axioms Johnson.KB8.rootsOf_filter
#print axioms Johnson.KB8.senders_first
#print axioms Johnson.KB8.roots_first
#print axioms Johnson.KB8.roots_shared
#print axioms Johnson.KB8.walk_third
#print axioms Johnson.KB8.walk_shared
#print axioms Johnson.KB8.walk_first
#print axioms Johnson.KB8.written_full
#print axioms Johnson.KB8.senders_bent
#print axioms Johnson.KB8.roots_shared_bent
#print axioms Johnson.KB8.walk_third_bent
#print axioms Johnson.KB8.walk_shared_bent
#print axioms Johnson.KB8.walk_first_bent
