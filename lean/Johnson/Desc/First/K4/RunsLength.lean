-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/RunsLength.lean: HOW MANY CLAIMS K4's TWO RUNS LIST. Definitions with code,
statements and proofs.

`frontLen rows g o`: the number for the run "front": a function of what was heard (o), of the
group's number g and of who states the lookup's own claims (rows). It reads of o: the layout's
numbers NI, NN, Lam, LamM, NE AS THE ENVIRONMENT o.v HOLDS THEM (o.v.y), and, where rows is true,
how many claims of its own the lookup has returned (o.H.fo.rows.size).
`front_length`, `formsFrontWith_length`, `formsBack_length`: wherever the listing returns, it has
that many forms; "back" has four. `front_run_length`, `back_run_length`: the same of the block's
runs, at any seat.
The sum's terms, in the list's order: the lookup's own claims (rows) · `normsForms_length` 3 · the
row products' batch and their sumcheck's own claim 2 · `rowsForms_length` 21 NI ·
`termsForms_length` NN Lam + LamM + LamM NE · `gatedForms_length` 6 (two product layers, each its
own claim and `endsForms_length` 2) · `oneHotForms_length` LamM · the leaves' sumcheck's own claim
and `planesParts_length` 2: 3 · in the first group the embedding's 1.

What it is for: «link for proof file»'s law of the batching asks of every run of claims that the
number of its claims is a function of what stands in front of the batching's draw (its premise
RunOk, the clause on the length). At the carried record: Johnson/Desc/First/K4/RunsAtS.lean.

Limits. One direction, from a return. THAT o.v.y IS THE PLACE's P.y IS NOT SAID HERE: the number is
public only for a reader who holds o; or under that tie and, where rows is true, a tie on
o.H.fo.rows.size. That the number is the plan's number of claims (hp.nLin, less what other blocks
list) is not said. Nothing on soundness.
-/
import Johnson.Desc.First.K4.BlockLaws
import OnBytes.Desc.First.K4.ClaimsLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4
open OnBytes
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.K.Kc

/-! ### Lists -/

theorem mapM_length {α β : Type} {f : α → Option β} : ∀ (l : List α) (r : List β),
    l.mapM f = some r → r.length = l.length
  | [], r, h => by
    obtain rfl : [] = r := by simpa using h
    rfl
  | a :: l, r, h => by
    rw [List.mapM_cons] at h
    cases h1 : f a with
    | none => simp [h1] at h
    | some b =>
      cases h2 : l.mapM f with
      | none => simp [h1, h2] at h
      | some r' =>
        obtain rfl : b :: r' = r := by simpa [h1, h2] using h
        rw [List.length_cons, List.length_cons, mapM_length l r' h2]

theorem mapM_mem {α β : Type} {f : α → Option β} : ∀ (l : List α) (r : List β),
    l.mapM f = some r → ∀ y ∈ r, ∃ a, f a = some y
  | [], r, h => by
    obtain rfl : [] = r := by simpa using h
    exact fun _ hy => absurd hy List.not_mem_nil
  | a :: l, r, h => by
    rw [List.mapM_cons] at h
    cases h1 : f a with
    | none => simp [h1] at h
    | some b =>
      cases h2 : l.mapM f with
      | none => simp [h1, h2] at h
      | some r' =>
        obtain rfl : b :: r' = r := by simpa [h1, h2] using h
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact ⟨a, h1⟩
        · exact mapM_mem l r' h2 y hy

theorem flatten_length {α : Type} (k : Nat) : ∀ (L : List (List α)),
    (∀ x ∈ L, x.length = k) → L.flatten.length = k * L.length
  | [], _ => by simp
  | x :: L, h => by
    rw [List.flatten_cons, List.length_append, List.length_cons,
      h x (List.mem_cons.mpr (Or.inl rfl)),
      flatten_length k L fun z hz => h z (List.mem_cons.mpr (Or.inr hz)), Nat.mul_succ,
      Nat.add_comm]

/-! ### Group by group -/

theorem normsForms_length {P : Pub} {v : Env} {H : Heard} {l : List Aff}
    (h : normsForms P v H = some l) : l.length = 3 := by
  unfold normsForms at h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  rw [← Option.some.inj h]
  rfl

theorem rowsForms_length {v : Env} {H : Heard} {l : List Aff}
    (h : rowsForms v H = some l) : l.length = 21 * v.y.NI := by
  unfold rowsForms at h
  obtain ⟨ends, a1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨Ds, a2, h⟩ := Option.bind_eq_some_iff.mp h
  have n1 : ends.length = v.y.NI := by rw [mapM_length _ _ a1, List.length_range]
  have n2 : Ds.length = v.y.NI := by rw [mapM_length _ _ a2, List.length_range]
  have e1 : ∀ x ∈ ends, x.length = 4 := by
    intro x hx
    obtain ⟨i, hi⟩ := mapM_mem _ _ a1 x hx
    obtain ⟨D, _, rfl⟩ := Option.map_eq_some_iff.mp hi
    simp
  rw [← Option.some.inj h, List.length_append, List.length_append, flatten_length 4 ends e1,
    flatten_length 9 _ (by
      intro x hx
      obtain ⟨z, _, rfl⟩ := List.mem_map.mp hx
      simp [P6.carries]),
    flatten_length 8 _ (by
      intro x hx
      obtain ⟨z, _, rfl⟩ := List.mem_map.mp hx
      simp [P6.lines, P6.root, P6.reciprocal]),
    List.length_map, List.length_map, List.length_zipIdx, n1, n2]
  omega

theorem termsForms_length {v : Env} {H : Heard} {l : List Aff}
    (h : termsForms v H = some l) :
    l.length = v.y.NN * v.y.Lam + v.y.LamM + v.y.LamM * v.y.h.NE := by
  unfold termsForms at h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨a, a1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨b, a2, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨c, a3, h⟩ := Option.bind_eq_some_iff.mp h
  rw [← Option.some.inj h, List.length_append, List.length_append, mapM_length _ _ a1,
    mapM_length _ _ a2, mapM_length _ _ a3, List.length_range, List.length_range,
    List.length_range]

theorem endsForms_length {v : Env} {o : Level} {e : Array E} {t rows blocks stride : Nat}
    {lamOf : Nat → Nat} {first : Nat} {l : List Aff}
    (h : endsForms v o e t rows blocks stride lamOf first = some l) : l.length = 2 := by
  unfold endsForms at h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  rw [← Option.some.inj h]
  rfl

theorem gatedForms_length {P : Pub} {v : Env} {hd : Level} {hd2 : Option Level} {l : List Aff}
    (h : gatedForms P v hd hd2 = some l) : l.length = 6 := by
  unfold gatedForms at h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨a, a1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨b, a2, h⟩ := Option.bind_eq_some_iff.mp h
  rw [← Option.some.inj h, List.length_append, List.length_cons, List.length_cons,
    endsForms_length a1, endsForms_length a2]

theorem oneHotForms_length {v : Env} {l : List Aff} (h : oneHotForms v = some l) :
    l.length = v.y.LamM := by
  unfold oneHotForms at h
  rw [mapM_length _ _ h, List.length_range]

theorem planesParts_length {v : Env} {fo : Forest.Heard} {x : Aff × List Aff}
    (h : planesParts v fo = some x) : x.2.length = 2 := by
  unfold planesParts at h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
  rw [← Option.some.inj h]
  rfl

/-! ### The two listings -/

/-- **How many claims the run "front" lists.** -/
def frontLen (rows : Bool) (g : Nat) (o : Own) : Nat :=
  (if rows then o.H.fo.rows.size else 0) + 3 + 2 + 21 * o.v.y.NI +
    (o.v.y.NN * o.v.y.Lam + o.v.y.LamM + o.v.y.LamM * o.v.y.h.NE) + 6 + o.v.y.LamM + 3 +
    (if g == 0 then 1 else 0)

theorem front_length {rows : Bool} {P : Pub} {g : Nat} {o : Own} {rowV rowL : Aff} {l : List Aff}
    (h : front rows P g o rowV rowL = some l) : l.length = frontLen rows g o := by
  obtain ⟨g2, g46, g7, g89, g10, g11, g12, a1, a2, a3, a4, a5, a6, a7, e⟩ := front_some h
  have n0 : (if rows then o.H.fo.rows.toList else []).length =
      if rows then o.H.fo.rows.size else 0 := by
    cases rows <;> simp
  have n12 : g12.length = if g == 0 then 1 else 0 := by
    cases hg : (g == 0) with
    | true =>
      simp only [hg, if_true] at a7 ⊢
      obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp a7
      rfl
    | false =>
      simp only [hg, Bool.false_eq_true, if_false] at a7 ⊢
      rw [← Option.some.inj a7]
      rfl
  rw [e]
  simp only [List.length_append, List.length_cons, List.length_nil, n0, n12,
    normsForms_length a1, rowsForms_length a2, termsForms_length a3, gatedForms_length a4,
    oneHotForms_length a5, planesParts_length a6]
  unfold frontLen
  omega

/-- **Wherever the listing in front returns, it has that many forms.** -/
theorem formsFrontWith_length {rows : Bool} {P : Pub} {g : Nat} {o : Own} {F G : Fork}
    {fs : Array Aff} (h : formsFrontWith rows P g o F = some (fs, G)) :
    fs.size = frontLen rows g o := by
  obtain ⟨_, _, l, _, _, _, _, a, e, _, _, _⟩ := formsFrontWith_some h
  rw [e, List.size_toArray, front_length a]

/-- **The listing behind has four forms.** -/
theorem formsBack_length {o : Own} {F G : Fork} {fs : Array Aff}
    (h : formsBack o F = some (fs, G)) : fs.size = 4 := by
  obtain ⟨_, e, _, _⟩ := formsBack_some h
  rw [e]
  rfl

/-! ### The block's runs -/

/-- **The run "front"**, at any seat: o is what the record holds as heard. -/
theorem front_run_length {T : Type} (L : Seat T) (p : Par)
    (run : Nat → T → Except String (List Aff × T))
    (hr : (block L p).claims.lookup "front" = some run) {n : Nat} {s s' : T} {cl : List Aff}
    (h : run n s = .ok (cl, s')) :
    ∃ o, L.own s = some o ∧ cl.length = frontLen (!p.k3Runs) p.g o := by
  obtain ⟨o, fs, F, ho, hf, e, _⟩ := (front_ok L p run hr n s s' cl).mp h
  refine ⟨o, ho, ?_⟩
  rw [e, Array.length_toList]
  unfold frontOf at hf
  cases hk : p.k3Runs with
  | true =>
    simp only [hk, if_true] at hf
    exact formsFrontWith_length hf
  | false =>
    simp only [hk, Bool.false_eq_true, if_false] at hf
    exact formsFrontWith_length hf

/-- **The run "back"**, at any seat. -/
theorem back_run_length {T : Type} (L : Seat T) (p : Par)
    (run : Nat → T → Except String (List Aff × T))
    (hr : (block L p).claims.lookup "back" = some run) {n : Nat} {s s' : T} {cl : List Aff}
    (h : run n s = .ok (cl, s')) : cl.length = 4 := by
  obtain ⟨o, fs, F, _, hf, e, _⟩ := (back_ok L p run hr n s s' cl).mp h
  rw [e, Array.length_toList]
  exact formsBack_length hf

end OnBytes.Desc.First.K4

#print axioms OnBytes.Desc.First.K4.front_run_length
#print axioms OnBytes.Desc.First.K4.back_run_length
