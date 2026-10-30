-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/ReadBackPlan.lean: a plan that fits the format's words is read back as it was
spelled.

The program spells a chain's parameter bytes from a plan, the digest of the public files and further
items (`Fmt.paramsBytes`), and reads them back before it uses them (`Given.read`).
OnBytes/Params/ReadBackLaws.lean proves that the digest and the items are read back as they were
spelled; OnBytes/Params/ReadBackAt.lean proves that the plan which is read back has the field of the
plan that was spelled and spells the same bytes, and says that it need not be the same plan: a
number from 2 ^ 64 on is spelled modulo 2 ^ 64. The library proves that its reader of a plan undoes
the spelling of a plan that fits (`Fmt.undoes_plan`, `Fmt.okPlan_of_fit`): `Fmt.Plan.fit` asks that
the plan's five numbers, the number of its entries and the eleven words of each entry are below 2 ^
64, and that each entry's name is within the format's rule for names and has fewer than 2 ^ 64
bytes. This file draws the consequence for the program's reader: on bytes that were spelled from a
plan that fits, `Given.read` returns that plan, whole, if it returns a value. Nothing is asked of
the digest, of the items or of the bytes' length: the plan is read before what these govern.

Main theorems: `paramsRead_plan`, `Given.read_plan`, `rounds_of_noRecord`.
What is not claimed: that a plan fits: that is the hypothesis. No theorem here says that the
planner's plans fit. Of an entry's eleven words the planner bounds three: `planRng` refuses more
than 2 ^ 64 - 32 drawn entries of a matrix, `close` refuses bits of work that with six more do not
fit the nonce, and the search for a number of positions ends at 2 ^ 32 (OnBytes/Params/Planner.lean,
OnBytes/Params/Distance.lean). How the condition comes down to the numbers in the planner's
descriptions of the rounds is not said here. Nothing if the reader refuses. Nothing on bytes that
`Fmt.paramsBytes` has not spelled. For proofs only; the program, that is the Lean port built from
OnBytes/, does not import this file.

-/
import OnBytes.Params.ReadBackAt

set_option autoImplicit false

namespace OnBytes.Params

open Fmt

/-- The library's reader returns the plan that was spelled, if the plan fits. Nothing is asked of
the digest or of the items: the plan is read before them. -/
theorem paramsRead_plan {P : Plan} {cfg : ByteArray} {others : List (String × ByteArray)}
    {x : Fmt.Params} (hf : P.fit = true)
    (h : paramsRead (paramsBytes P cfg others) = some x) : x.plan = P := by
  generalize hv : item versionName (versionValue P.field) = V
  generalize hr : item configName cfg ++ items others = T
  have eb : paramsBytes P cfg others = V ++ P.bytes ++ T := by
    simp only [paramsBytes, paramsHead, hv, ← hr, ByteArray.append_assoc]
  have a := undoes_item _ (version_ok P.field) ByteArray.empty (P.bytes ++ T)
  simp only [hv, ByteArray.empty_append, ByteArray.size_empty, Nat.zero_add] at a
  rw [← ByteArray.append_assoc] at a
  have b := undoes_plan P (okPlan_of_fit P hf) V T
  rw [eb] at h
  unfold paramsRead at h
  rw [a] at h
  simp only at h
  rw [b] at h
  simp only at h
  split at h
  · split at h
    · split at h
      · obtain ⟨y, _, hy⟩ := Option.map_eq_some_iff.1 h
        cases hy
        rfl
      · cases h
    · cases h
  · cases h

/-- **`Given.read` returns the plan that was spelled, if the plan fits.** -/
theorem Given.read_plan {P : Plan} {cfg : ByteArray} {others : List (String × ByteArray)}
    {g : Given} (hf : P.fit = true)
    (h : Given.read (paramsBytes P cfg others) = some g) : g.plan = P := by
  unfold Given.read at h
  rw [paramsReadT_eq] at h
  cases hp : paramsRead (paramsBytes P cfg others) with
  | none =>
    rw [hp] at h
    cases h
  | some x =>
    rw [hp] at h
    simp only [Option.bind_some] at h
    split at h
    · cases h
      exact paramsRead_plan hf hp
    · cases h

/-- A plan without an entry for a table's own sample: all its entries are rounds of the chain. -/
theorem rounds_of_noRecord {P : Plan} (h : (P.entries.find? fun e => e.name == recordName) = none) :
    P.rounds = P.entries := by
  unfold Plan.rounds
  rw [List.filter_eq_self]
  intro e he
  have := List.find?_eq_none.1 h e he
  simpa [bne] using this

end OnBytes.Params
