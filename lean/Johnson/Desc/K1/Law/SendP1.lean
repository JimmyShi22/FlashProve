-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/SendP1.lean: towards the tie between the kind's decision of a sending and the
sending that is written over the verifier program's own functions (sendP): the seeds are cut alike,
and the rows of one message are the same rows.

Main names: seedOf; seedsOf_cut (Send.seedsOf at the exact length is cutSeeds); mapM_tagged;
rowsFor_range', rowsFor_eq (rowsFor, which calls Send.form, returns the kind's rowsOf).

What is not claimed. The tie itself is not in this file. Nothing on soundness, on an honest prover
or on hiding.

-/
import Johnson.Desc.K1.Law.FormEq

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice

/-- A seed, in the program's record. -/
def seedOf (x : List E × E) : SampleSeed := ⟨x.1, x.2⟩

/-- **At the exact length the program cuts the seeds as the kind does.** -/
theorem seedsOf_cut (v : Nat) : ∀ (n : Nat) (l : List E), l.length = n * (v + 1) →
    Send.seedsOf v n l = some ((cutSeeds v n l).map seedOf)
  | 0, l, h => by
    have : l = [] := List.eq_nil_of_length_eq_zero (by simpa using h)
    subst this
    rfl
  | n + 1, l, h => by
    have hlen : (l.drop v).length = n * (v + 1) + 1 := by
      rw [List.length_drop, h, Nat.succ_mul]
      omega
    cases hd : l.drop v with
    | nil => simp [hd] at hlen
    | cons b rest =>
      have hrest : rest = l.drop (v + 1) := by
        have : (l.drop v).drop 1 = rest := by rw [hd]; rfl
        rw [← this, List.drop_drop]
      have hr : rest.length = n * (v + 1) := by
        rw [hd] at hlen
        simpa using hlen
      have ih := seedsOf_cut v n rest hr
      rw [hrest] at ih
      simp only [Send.seedsOf, hd, cutSeeds, List.headD_cons, List.map_cons, hrest, seedOf]
      rw [ih]
      rfl

/-- A list of pairs each of whose first members is sent to its second. -/
theorem mapM_tagged {α β : Type} (f : α → Option β) : ∀ l : List (α × β),
    (∀ x ∈ l, f x.1 = some x.2) → (l.map Prod.fst).mapM f = some (l.map Prod.snd)
  | [], _ => rfl
  | x :: l, h => by
    have ih := mapM_tagged f l fun y hy => h y (List.mem_cons_of_mem _ hy)
    simp [List.mapM_cons, h x List.mem_cons_self, ih]

variable (codes : Codes) (s : OracleShape) (o : Nat) (seeds : List (List E × E))

/-- The rows of the answers number i, i + 1, …, one after the other. -/
theorem rowsFor_range' (hl : codes.lengthsOk = true) (hs : Blk.shapeOk codes s = true)
    (hp : (Msg.of codes s).padFits = true) : ∀ (k i : Nat) (ys : List E) (acc : Array OnBytes.Row),
    i + k ≤ seeds.length → k ≤ ys.length →
    rowsFor codes s o (seeds.map seedOf) (List.range' i k) ys acc =
      some ((acc.toList ++ ((((seeds.drop i).take k).zip (ys.take k)).zipIdx i).map fun x =>
        sampleRow (Msg.of codes s) o x.1.1.1 x.1.1.2 x.2 x.1.2).toArray, ys.drop k)
  | 0, i, ys, acc, _, _ => by simp [rowsFor]
  | k + 1, i, [], acc, _, h2 => absurd h2 (by simp)
  | k + 1, i, y :: ys, acc, h1, h2 => by
    have hi : i < seeds.length := by omega
    obtain ⟨row, hrow, hup⟩ := Option.map_eq_some_iff.1
      (form_eq codes s o seeds[i].1 seeds[i].2 i y hl hs hp)
    have hseed : (seeds.map seedOf)[i]? = some ⟨seeds[i].1, seeds[i].2⟩ := by
      rw [List.getElem?_map, List.getElem?_eq_getElem hi]
      rfl
    have ih := rowsFor_range' hl hs hp k (i + 1) ys
      (acc.push (sampleRow (Msg.of codes s) o seeds[i].1 seeds[i].2 i y)) (by omega)
      (by simpa using h2)
    have hdrop : seeds.drop i = seeds[i] :: seeds.drop (i + 1) := List.drop_eq_getElem_cons hi
    rw [List.range'_succ]
    simp only [rowsFor, Own.formMade_eq, hseed, hrow, hup, ih, hdrop, List.take_succ_cons,
      List.zip_cons_cons, List.zipIdx_cons, List.map_cons, List.drop_succ_cons, Array.toList_push,
      List.append_assoc, List.singleton_append]

/-- **The rows that are made by the program's function are the kind's rows.** -/
theorem rowsFor_eq (ys : List E) (hl : codes.lengthsOk = true) (hs : Blk.shapeOk codes s = true)
    (hp : (Msg.of codes s).padFits = true) (h1 : s.answers ≤ seeds.length)
    (h2 : s.answers ≤ ys.length) :
    rowsFor codes s o (seeds.map seedOf) (List.range s.answers) ys #[] =
      some (rowsOf codes seeds o s ys, ys.drop s.answers) := by
  rw [List.range_eq_range', rowsFor_range' codes s o seeds hl hs hp s.answers 0 ys #[]
    (by omega) h2]
  simp [rowsOf]

end VerifiableInference.Desc.K1
