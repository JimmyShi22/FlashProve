-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/Written/Def.lean: for RoundsWritten.lean (one folder up): what is
evaluated, and the lemmas by which an evaluation on codes and on parts gives the statement on the
whole list. Definitions, statements and proofs.

  `closeRoundOk`, `foldsAt`, `closingsOf`: see RoundsWritten.lean's head.
Limits. Nothing on soundness.

-/
import Johnson.G.DryProofLit
import Fmt.M1Plan
import Fmt.M2Plan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes.Params (Rounds)
open Johnson.G (dryProofFull dryProofSmall)

/-- The test on one written round: if it bears one of the closing's three names, it is the format's
own round of that name, with nothing stored; and a round "BAT" batches 2 to 2^56 rows. -/
def closeRoundOk (r : Fmt.Round × List Fmt.Stored) : Bool :=
  (r.1.entry.name != "BAT" ||
    (decide (r.1 = Fmt.M2.rBatN r.1.entry.rows) && r.2.isEmpty &&
      decide (2 ≤ r.1.entry.rows) && decide (r.1.entry.rows ≤ 2 ^ 56))) &&
  (r.1.entry.name != "FOLD epsilon" ||
    (decide (r.1 = Fmt.M1.rEps "FOLD epsilon") && r.2.isEmpty)) &&
  (r.1.entry.name != "FOLD round" || (decide (r.1 = Fmt.M1.rTwo "FOLD round") && r.2.isEmpty))

/-- How many rounds named "FOLD round" stand at a list's front. -/
def foldsAt : Rounds → Nat
  | [] => 0
  | a :: l => if a.1.entry.name == "FOLD round" then foldsAt l + 1 else 0

/-- **The closings of a list**: at each round "BAT" whose next round is "FOLD epsilon": the rows
that it batches, and how many rounds "FOLD round" follow that one. A round "BAT" with another round
behind it gives (its rows, none). -/
def closingsOf : Rounds → List (Nat × Option Nat)
  | [] => []
  | a :: l =>
    if a.1.entry.name == "BAT" then
      (match l with
        | b :: l' =>
          (a.1.entry.rows, if b.1.entry.name == "FOLD epsilon" then some (foldsAt l') else none)
        | [] => (a.1.entry.rows, none)) :: closingsOf l
    else closingsOf l

/-! ## Through codes: so that the kernel compares numbers along a long list, and names only at the
distinct rounds -/

open Johnson.G (unrunR)

/-- A round's code: 1, 2, 3 for the closing's three names, else 0; and its entry's rows. -/
def codeOf (r : Fmt.Round × List Fmt.Stored) : Nat × Nat :=
  (if r.1.entry.name == "BAT" then 1 else if r.1.entry.name == "FOLD epsilon" then 2
    else if r.1.entry.name == "FOLD round" then 3 else 0, r.1.entry.rows)

/-- `foldsAt` on codes. -/
def foldsC : List (Nat × Nat) → Nat
  | [] => 0
  | a :: l => if a.1 == 3 then foldsC l + 1 else 0

/-- `closingsOf` on codes. -/
def closingsC : List (Nat × Nat) → List (Nat × Option Nat)
  | [] => []
  | a :: l =>
    if a.1 == 1 then
      (match l with
        | b :: l' => (a.2, if b.1 == 2 then some (foldsC l') else none)
        | [] => (a.2, none)) :: closingsC l
    else closingsC l

theorem code_bat (r : Fmt.Round × List Fmt.Stored) :
    ((codeOf r).1 == 1) = (r.1.entry.name == "BAT") := by
  unfold codeOf
  by_cases h1 : r.1.entry.name = "BAT"
  · simp [h1]
  · by_cases h2 : r.1.entry.name = "FOLD epsilon"
    · simp [h2]
    · by_cases h3 : r.1.entry.name = "FOLD round" <;> simp [h1, h2, h3]

theorem code_eps (r : Fmt.Round × List Fmt.Stored) :
    ((codeOf r).1 == 2) = (r.1.entry.name == "FOLD epsilon") := by
  unfold codeOf
  by_cases h1 : r.1.entry.name = "BAT"
  · simp [h1]
  · by_cases h2 : r.1.entry.name = "FOLD epsilon"
    · simp [h2]
    · by_cases h3 : r.1.entry.name = "FOLD round" <;> simp [h1, h2, h3]

theorem code_fold (r : Fmt.Round × List Fmt.Stored) :
    ((codeOf r).1 == 3) = (r.1.entry.name == "FOLD round") := by
  unfold codeOf
  by_cases h1 : r.1.entry.name = "BAT"
  · simp [h1]
  · by_cases h2 : r.1.entry.name = "FOLD epsilon"
    · simp [h2]
    · by_cases h3 : r.1.entry.name = "FOLD round" <;> simp [h1, h2, h3]

theorem foldsAt_eq : ∀ l : Rounds, foldsAt l = foldsC (l.map codeOf)
  | [] => rfl
  | a :: l => by
    simp only [foldsAt, List.map_cons, foldsC, code_fold, foldsAt_eq l]

theorem closingsOf_two (a b : Fmt.Round × List Fmt.Stored) (l : Rounds) :
    closingsOf (a :: b :: l) =
      if a.1.entry.name == "BAT" then
        (a.1.entry.rows,
          if b.1.entry.name == "FOLD epsilon" then some (foldsAt l) else none) ::
            closingsOf (b :: l)
      else closingsOf (b :: l) := by
  rw [closingsOf]

theorem closingsC_two (a b : Nat × Nat) (l : List (Nat × Nat)) :
    closingsC (a :: b :: l) =
      if a.1 == 1 then (a.2, if b.1 == 2 then some (foldsC l) else none) :: closingsC (b :: l)
      else closingsC (b :: l) := by
  rw [closingsC]

theorem closingsOf_eq : ∀ l : Rounds, closingsOf l = closingsC (l.map codeOf)
  | [] => rfl
  | [a] => by
    simp only [closingsOf, List.map_cons, List.map_nil, closingsC, code_bat]
    split <;> rfl
  | a :: b :: l => by
    have ih := closingsOf_eq (b :: l)
    rw [List.map_cons] at ih
    rw [List.map_cons, List.map_cons, closingsOf_two, closingsC_two, code_bat, code_eps,
      foldsAt_eq l, ih]
    rfl

/-- The list's last code is 0: no closing reaches beyond its end. -/
def lastZero : List (Nat × Nat) → Bool
  | [] => false
  | [z] => z.1 == 0
  | _ :: b :: l => lastZero (b :: l)

theorem lastZero_append : ∀ (l1 l2 : List (Nat × Nat)), lastZero l2 = true →
    lastZero (l1 ++ l2) = true
  | [], _, h => h
  | [_], [], h => by simp [lastZero] at h
  | [_], _ :: _, h => h
  | _ :: b :: l, l2, h => lastZero_append (b :: l) l2 h

theorem foldsC_cons (a : Nat × Nat) (l : List (Nat × Nat)) :
    foldsC (a :: l) = if a.1 == 3 then foldsC l + 1 else 0 := by
  rw [foldsC]

theorem foldsC_append : ∀ (l l2 : List (Nat × Nat)), lastZero l = true →
    foldsC (l ++ l2) = foldsC l
  | [], _, h => by simp [lastZero] at h
  | [z], l2, h => by
    have hz : z.1 = 0 := by simpa [lastZero] using h
    simp [foldsC, hz]
  | a :: b :: l, l2, h => by
    have ih := foldsC_append (b :: l) l2 h
    simp only [List.cons_append] at ih ⊢
    rw [foldsC_cons a (b :: (l ++ l2)), foldsC_cons a (b :: l), ih]

/-- **The closings of two lists in a row are the two lists' closings in a row**, if the first list's
last code is 0. -/
theorem closingsC_append : ∀ (l l2 : List (Nat × Nat)), lastZero l = true →
    closingsC (l ++ l2) = closingsC l ++ closingsC l2
  | [], _, h => by simp [lastZero] at h
  | [z], l2, h => by
    have hz : z.1 = 0 := by simpa [lastZero] using h
    cases l2 <;> simp [closingsC, hz]
  | [a, z], l2, h => by
    have hz : z.1 = 0 := by simpa [lastZero] using h
    have ih := closingsC_append [z] l2 h
    simp only [List.cons_append, List.nil_append] at ih ⊢
    rw [closingsC_two a z l2, closingsC_two a z [], ih]
    simp only [hz]
    split <;> rfl
  | a :: b :: c :: l, l2, h => by
    have ih := closingsC_append (b :: c :: l) l2 h
    have hf := foldsC_append (c :: l) l2 h
    simp only [List.cons_append] at ih hf ⊢
    rw [closingsC_two a b (c :: (l ++ l2)), closingsC_two a b (c :: l), ih, hf]
    split <;> rfl

/-- The runs of a list of records, each record under a map. -/
theorem map_unrunR {β : Type} (f : Fmt.Round × List Fmt.Stored → β)
    (recs : List (Fmt.Round × List Fmt.Stored)) (runs : List (Nat × Nat)) :
    (unrunR recs runs).map f =
      runs.flatMap fun x => (((recs.map f)[x.2]?).elim [] (List.replicate x.1)) := by
  unfold unrunR
  rw [List.map_flatMap]
  congr 1
  funext x
  rw [List.getElem?_map]
  cases recs[x.2]? <;> simp

/-- A test holds along the runs if it holds at each run's record. -/
theorem all_unrunR (p : Fmt.Round × List Fmt.Stored → Bool)
    (recs : List (Fmt.Round × List Fmt.Stored)) (runs : List (Nat × Nat))
    (h : (runs.all fun x => ((recs.map p)[x.2]?).getD true) = true) :
    (unrunR recs runs).all p = true := by
  rw [List.all_eq_true]
  intro r hr
  unfold unrunR at hr
  obtain ⟨x, hx, hr⟩ := List.mem_flatMap.1 hr
  have h1 := List.all_eq_true.1 h x hx
  rw [List.getElem?_map] at h1
  cases e : recs[x.2]? with
  | none => rw [e] at hr; simp at hr
  | some y =>
    rw [e] at hr h1
    have : r = y := (List.mem_replicate.1 hr).2
    rw [this]
    exact h1

end VerifiableInference.Desc.First.Close
