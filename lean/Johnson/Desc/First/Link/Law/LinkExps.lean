-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/LinkExps.lean: THE TEST ON THE EXPONENTS AT A LINK (`LinkOwes.hok`),
FROM ONE DUTY AN ENTRY OF THE ORDER AND TWO NUMBERS. Theorems: tools for the assembly of the kinds'
laws, over the batching kind's discipline of exponents (Johnson/Desc/First/Batch/Law/ExpsOk.lean,
ExpsRuns.lean).

Why. `hok` asks that the exponents of all the runs' terms in a row differ from each other and are at
most d. No kind can show that alone: a run's exponents begin where the runs in front of it end. The
discipline says it a run at a time: a run's terms stand in its own window of numbers [n, n + len),
or in the window of equations behind the plan's number of claims.

What is said.
  `terms_link`: the terms of a link's two moves are its runs' terms in a row. `PlainE`: an entry's
    duty: at every n its terms' exponents differ and lie in [n, n + len). `plainE_of`: a table entry
    `plainTm vals` has it, if there are at most len values. `rlTies`: the runs that the order names,
    each with its number of equations. `disc_plain`: a stretch of plain entries keeps the
    discipline. `disc_link`: **the discipline along a whole order pre ++ k :: post**, pre and post
    plain, k the one entry with equations. `hok_link`, `hok_order`: **`TermsOk` of the link's terms
    at d**, from that, and TWO NUMBERS: the runs' claims are at most the plan's number; the plan's
    number and the equations' are at most d + 1.

Limits. Tools. The two numbers, each plain entry's duty and the duty of the entry with equations
stay premises. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LinkJoinPay
import Johnson.Desc.First.Batch.Law.ExpsRuns
import Johnson.Desc.First.Batch.Law.PlainRuns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)

variable {α : Type}

/-- The fixed part's type. -/
abbrev Fixed (α : Type) : Type := α × Option Pub9

/-- The terms of a link's two moves are its runs' terms in a row. -/
theorem terms_link (q : Fixed α) (y : Bound Cb.Gl.E) (L : Link S Claim)
    (rl : List (TermedRun S (Fixed α) Cb.Gl.E)) :
    termsOf q y (moves₁ L rl ++ moves₂ (α := α) L) 0 = termsRuns q y rl 0 := by
  simp [moves₁, moves₂, termsOf]

variable (tmOf : ℕ × String → ℕ → Fixed α → Bound Cb.Gl.E → List (ℕ × Cb.Gl.E))
  (lenOf : ℕ × String → Fixed α → ℕ)

/-- An entry's duty: at every n its terms' exponents differ and lie in [n, n + len). -/
def PlainE (q : Fixed α) (y : Bound Cb.Gl.E) (o : ℕ × String) : Prop :=
  ∀ n, ((tmOf o n q y).map (·.1)).Nodup ∧ ∀ x ∈ tmOf o n q y, n ≤ x.1 ∧ x.1 < n + lenOf o q

/-- A table entry of plain claims has it, if there are at most len values. -/
theorem plainE_of (q : Fixed α) (y : Bound Cb.Gl.E) (o : ℕ × String)
    (vals : Fixed α → Bound Cb.Gl.E → List Cb.Gl.E) (ht : tmOf o = plainTm vals)
    (hl : (vals q y).length ≤ lenOf o q) : PlainE tmOf lenOf q y o := by
  intro n
  rw [ht]
  refine ⟨numbered_exps _ n, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := numbered_mem _ n x hx
  exact ⟨h1, Nat.lt_of_lt_of_le h2 (Nat.add_le_add_left hl n)⟩

/-- The runs that a list of entries names, each with its number of equations. -/
def rlTies (L : Link S Claim) (tieOf : ℕ × String → ℕ) (os : List (ℕ × String)) :
    List (TermedRun S (Fixed α) Cb.Gl.E × ℕ) :=
  os.filterMap fun o =>
    ((L.hear[o.1]?).bind fun b => b.claims.lookup o.2).map fun r =>
      (⟨(o.2, r), tmOf o, lenOf o⟩, tieOf o)

theorem rlTies_runs (L : Link S Claim) (tieOf : ℕ × String → ℕ) :
    (rlTies tmOf lenOf L tieOf L.order).map (·.1) = rlOf L tmOf lenOf := by
  unfold rlTies rlOf
  rw [List.map_filterMap]
  congr 1
  funext o
  cases ((L.hear[o.1]?).bind fun b => b.claims.lookup o.2) <;> rfl

theorem rlTies_append (L : Link S Claim) (tieOf : ℕ × String → ℕ) (a b : List (ℕ × String)) :
    rlTies tmOf lenOf L tieOf (a ++ b) =
      rlTies tmOf lenOf L tieOf a ++ rlTies tmOf lenOf L tieOf b := by
  unfold rlTies
  rw [List.filterMap_append]

/-- As moves, with their numbers of equations. -/
def asMoves (l : List (TermedRun S (Fixed α) Cb.Gl.E × ℕ)) :
    List (Termed S (Fixed α) Cb.Gl.E × ℕ) := l.map fun r => (asMove r.1, r.2)

/-- The discipline along two stretches. -/
theorem disc_append (q : Fixed α) (y : Bound Cb.Gl.E) (plan : ℕ) :
    ∀ (a b : List (Termed S (Fixed α) Cb.Gl.E × ℕ)) (n t : ℕ), DiscFrom q y plan a n t →
      DiscFrom q y plan b (n + lenAll q a) (t + tieAll a) → DiscFrom q y plan (a ++ b) n t
  | [], b, n, t, _, h => by simpa [lenAll, tieAll] using h
  | m :: a, b, n, t, h, h' => by
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨h1, h2, disc_append q y plan a b _ _ h3 ?_⟩
    simpa [lenAll, tieAll, Nat.add_assoc] using h'

/-- A stretch of plain entries keeps the discipline, and has no equation. -/
theorem disc_plain (L : Link S Claim) (tieOf : ℕ × String → ℕ) (q : Fixed α)
    (y : Bound Cb.Gl.E) (plan : ℕ) :
    ∀ (os : List (ℕ × String)), (∀ o ∈ os, PlainE tmOf lenOf q y o ∧ tieOf o = 0) → ∀ n t,
      DiscFrom q y plan (asMoves (rlTies tmOf lenOf L tieOf os)) n t ∧
        tieAll (asMoves (rlTies tmOf lenOf L tieOf os)) = 0
  | [], _, _, _ => ⟨trivial, rfl⟩
  | o :: os, h, n, t => by
    have ih := disc_plain L tieOf q y plan os fun o' ho' => h o' (List.mem_cons_of_mem _ ho')
    obtain ⟨hp, h0⟩ := h o List.mem_cons_self
    unfold rlTies
    rw [List.filterMap_cons]
    cases hl : ((L.hear[o.1]?).bind fun b => b.claims.lookup o.2) with
    | none => exact ih n t
    | some r =>
      obtain ⟨p1, p2⟩ := hp n
      refine ⟨⟨p1, fun x hx => Or.inl (p2 x hx), (ih _ _).1⟩, ?_⟩
      show tieOf o + _ = 0
      rw [h0, Nat.zero_add]
      exact (ih n t).2

theorem lenAll_append (q : Fixed α) : ∀ (a b : List (Termed S (Fixed α) Cb.Gl.E × ℕ)),
    lenAll q (a ++ b) = lenAll q a + lenAll q b
  | [], b => by simp [lenAll]
  | m :: a, b => by simp [lenAll, lenAll_append q a b, Nat.add_assoc]

theorem tieAll_append : ∀ (a b : List (Termed S (Fixed α) Cb.Gl.E × ℕ)),
    tieAll (a ++ b) = tieAll a + tieAll b
  | [], b => by simp [tieAll]
  | m :: a, b => by simp [tieAll, tieAll_append a b, Nat.add_assoc]

/-- **THE DISCIPLINE ALONG A WHOLE ORDER**: plain entries, the one entry with equations, plain
entries. hk: that entry's duty, at whatever number it begins so that its claims end within the
plan's number, with no equation in front. The equations are at most that entry's. -/
theorem disc_link (L : Link S Claim) (tieOf : ℕ × String → ℕ) (q : Fixed α) (y : Bound Cb.Gl.E)
    (plan : ℕ) (pre post : List (ℕ × String)) (k : ℕ × String)
    (hpre : ∀ o ∈ pre, PlainE tmOf lenOf q y o ∧ tieOf o = 0)
    (hpost : ∀ o ∈ post, PlainE tmOf lenOf q y o ∧ tieOf o = 0)
    (hk : ∀ n, n + lenOf k q ≤ plan → ((tmOf k n q y).map (·.1)).Nodup ∧
      ∀ x ∈ tmOf k n q y, InWin n (lenOf k q) plan 0 (tieOf k) x.1)
    (hlen : lenAll q (asMoves (rlTies tmOf lenOf L tieOf (pre ++ k :: post))) ≤ plan) :
    DiscFrom q y plan (asMoves (rlTies tmOf lenOf L tieOf (pre ++ k :: post))) 0 0 ∧
      tieAll (asMoves (rlTies tmOf lenOf L tieOf (pre ++ k :: post))) ≤ tieOf k := by
  rw [rlTies_append] at hlen ⊢
  unfold asMoves at hlen ⊢
  rw [List.map_append] at hlen ⊢
  rw [lenAll_append] at hlen
  rw [tieAll_append]
  obtain ⟨d1, t1⟩ := disc_plain tmOf lenOf L tieOf q y plan pre hpre 0 0
  have t1' : tieAll ((rlTies tmOf lenOf L tieOf pre).map fun r => (asMove r.1, r.2)) = 0 := t1
  rw [t1', Nat.zero_add]
  suffices h : DiscFrom q y plan ((rlTies tmOf lenOf L tieOf (k :: post)).map
      fun r => (asMove r.1, r.2)) (0 + lenAll q ((rlTies tmOf lenOf L tieOf pre).map
        fun r => (asMove r.1, r.2))) 0 ∧
      tieAll ((rlTies tmOf lenOf L tieOf (k :: post)).map fun r => (asMove r.1, r.2)) ≤ tieOf k by
    refine ⟨disc_append q y plan _ _ 0 0 d1 ?_, h.2⟩
    rw [t1']
    exact h.1
  have hpo := fun n t => disc_plain tmOf lenOf L tieOf q y plan post hpost n t
  unfold rlTies at hlen ⊢
  rw [List.filterMap_cons] at hlen ⊢
  cases hl : ((L.hear[k.1]?).bind fun b => b.claims.lookup k.2) with
  | none =>
    refine ⟨(hpo _ _).1, ?_⟩
    show tieAll (asMoves (rlTies tmOf lenOf L tieOf post)) ≤ tieOf k
    rw [(hpo 0 0).2]
    exact Nat.zero_le _
  | some r =>
    rw [hl] at hlen
    have hb : 0 + lenAll q ((rlTies tmOf lenOf L tieOf pre).map fun r => (asMove r.1, r.2)) +
        lenOf k q ≤ plan := by
      have e : lenAll q ((rlTies tmOf lenOf L tieOf pre).map fun r => (asMove r.1, r.2)) +
          (lenOf k q + lenAll q (asMoves (rlTies tmOf lenOf L tieOf post))) ≤ plan := hlen
      omega
    obtain ⟨k1, k2⟩ := hk _ hb
    refine ⟨⟨k1, k2, (hpo _ _).1⟩, ?_⟩
    show tieOf k + tieAll (asMoves (rlTies tmOf lenOf L tieOf post)) ≤ tieOf k
    rw [(hpo 0 0).2]
    exact Nat.le_refl _

/-- **hok AT A LINK, FROM THE DISCIPLINE AND TWO NUMBERS.** -/
theorem hok_link (L : Link S Claim) (tieOf : ℕ × String → ℕ) (q : Fixed α) (y : Bound Cb.Gl.E)
    (plan d : ℕ)
    (hD : DiscFrom q y plan (asMoves (rlTies tmOf lenOf L tieOf L.order)) 0 0)
    (hlen : lenRuns q (rlOf L tmOf lenOf) ≤ plan)
    (hd : plan + tieAll (asMoves (rlTies tmOf lenOf L tieOf L.order)) ≤ d + 1) :
    Desc.TermsOk Cb.Gl.E
      (termsOf q y (moves₁ L (rlOf L tmOf lenOf) ++ moves₂ (α := α) L) 0) d := by
  rw [terms_link, ← rlTies_runs tmOf lenOf L tieOf]
  have hp : 0 + lenRuns q ((rlTies tmOf lenOf L tieOf L.order).map (·.1)) ≤ plan := by
    rw [rlTies_runs, Nat.zero_add]
    exact hlen
  obtain ⟨h1, h2⟩ := disc_gather q y plan (rlTies tmOf lenOf L tieOf L.order) 0 0 hD hp
  refine ⟨h1, fun x hx => ?_⟩
  have hd' : plan + tieAll ((rlTies tmOf lenOf L tieOf L.order).map
      fun r => (asMove r.1, r.2)) ≤ d + 1 := hd
  rcases h2 x hx with ⟨_, h⟩ | ⟨_, h⟩ <;> omega

/-- The runs' number of claims, in the discipline's coin. -/
theorem lenAll_runs (L : Link S Claim) (tieOf : ℕ × String → ℕ) (q : Fixed α) :
    lenAll q (asMoves (rlTies tmOf lenOf L tieOf L.order)) = lenRuns q (rlOf L tmOf lenOf) := by
  rw [← rlTies_runs tmOf lenOf L tieOf]
  exact (lenRuns_eq q _).symm

/-- **hok AT A LINK WHOSE ORDER IS pre ++ k :: post, FROM ONE DUTY AN ENTRY AND TWO NUMBERS.** -/
theorem hok_order (L : Link S Claim) (tieOf : ℕ × String → ℕ) (q : Fixed α) (y : Bound Cb.Gl.E)
    (plan d : ℕ) (pre post : List (ℕ × String)) (k : ℕ × String)
    (ho : L.order = pre ++ k :: post)
    (hpre : ∀ o ∈ pre, PlainE tmOf lenOf q y o ∧ tieOf o = 0)
    (hpost : ∀ o ∈ post, PlainE tmOf lenOf q y o ∧ tieOf o = 0)
    (hk : ∀ n, n + lenOf k q ≤ plan → ((tmOf k n q y).map (·.1)).Nodup ∧
      ∀ x ∈ tmOf k n q y, InWin n (lenOf k q) plan 0 (tieOf k) x.1)
    (hlen : lenRuns q (rlOf L tmOf lenOf) ≤ plan) (hd : plan + tieOf k ≤ d + 1) :
    Desc.TermsOk Cb.Gl.E
      (termsOf q y (moves₁ L (rlOf L tmOf lenOf) ++ moves₂ (α := α) L) 0) d := by
  have hl : lenAll q (asMoves (rlTies tmOf lenOf L tieOf (pre ++ k :: post))) ≤ plan := by
    rw [← ho, lenAll_runs]
    exact hlen
  obtain ⟨hD, ht⟩ := disc_link tmOf lenOf L tieOf q y plan pre post k hpre hpost hk hl
  rw [← ho] at hD ht
  exact hok_link tmOf lenOf L tieOf q y plan d hD hlen (by omega)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.terms_link
#print axioms VerifiableInference.Desc.LinkJoin.plainE_of
#print axioms VerifiableInference.Desc.LinkJoin.disc_plain
#print axioms VerifiableInference.Desc.LinkJoin.disc_link
#print axioms VerifiableInference.Desc.LinkJoin.hok_link
#print axioms VerifiableInference.Desc.LinkJoin.hok_order
