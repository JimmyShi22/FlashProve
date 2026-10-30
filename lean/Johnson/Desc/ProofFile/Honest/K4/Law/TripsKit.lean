-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/TripsKit.lean.

What is here. TOOLS: lists of products (weight, first factor, second factor), one list at a point
and one at each of N corners, that stand in one relation member by member: the weights are the same
words; the first factor is one of a list of given values, of a fixed number, at the point and at
each corner, or reads as the combination of the corners' first factors under given coefficients; the
second factor reads as that combination of the corners' second factors. The relation goes through
appending, and through a loop that makes a list for each member of a list and lays them end to end.
Statements and proofs.

  `trip0`, `TripLin`, `TripLin.congr`, `LinAt`   the product of zeros; the relation, of one product
     and of lists
  `LinAt.nil`, `LinAt.one`, `LinAt.congr`, `LinAt.append`   the empty list; one product; two lists
     end to end
  `mapM_cons_some`, `LinAt.mapM`   a loop that makes a list for each member

Limits. Tools on lists; at the reading `Reading.gl`. The coefficients are free letters. Nothing on
any function of a verifier or of an honest part. No property is claimed.
-/
import Johnson.Desc.K4.Honest.Sides
import Johnson.Desc.K4.Honest.Law.CubeTerms
import Mathlib.Data.List.GetD

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (Reading)
open OnBytes.Desc.First.K4.Honest

/-- The product of zeros. -/
abbrev trip0 : Trip := (zeroE, zeroE, zeroE)

/-- **One product at the point and at the corners.** N: the number of corners. q: the coefficients.
e: the given values at the point; shs t: at corner t. o: the number of the given value that the
first factor is; none: it is none. -/
structure TripLin (N : ℕ) (q : ℕ → Cb.Gl.E) (e : Array E) (shs : ℕ → Array E) (x : Trip)
    (xs : ℕ → Trip) (o : Option ℕ) : Prop where
  w : ∀ t, t < N → (xs t).1 = x.1
  aS : ∀ i, o = some i →
    x.2.1 = e.getD i zeroE ∧ ∀ t, t < N → (xs t).2.1 = (shs t).getD i zeroE
  aN : o = none →
    Reading.gl.val x.2.1 = ∑ t ∈ Finset.range N, q t * Reading.gl.val (xs t).2.1
  b : Reading.gl.val x.2.2 = ∑ t ∈ Finset.range N, q t * Reading.gl.val (xs t).2.2

/-- **Lists of products**, member by member. ix: for each member the letter o of `TripLin`. -/
structure LinAt (N : ℕ) (q : ℕ → Cb.Gl.E) (e : Array E) (shs : ℕ → Array E) (l : List Trip)
    (ls : ℕ → List Trip) (ix : List (Option ℕ)) : Prop where
  len : ∀ t, t < N → (ls t).length = l.length
  lix : ix.length = l.length
  at_ : ∀ k, k < l.length →
    TripLin N q e shs (l.getD k trip0) (fun t => (ls t).getD k trip0) (ix.getD k none)

variable {N : ℕ} {q : ℕ → Cb.Gl.E} {e : Array E} {shs : ℕ → Array E}

theorem LinAt.nil (ls : ℕ → List Trip) (h : ∀ t, t < N → ls t = []) :
    LinAt N q e shs [] ls [] :=
  ⟨fun t ht => by rw [h t ht], rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩

/-- The relation reads the corners' products below N alone. -/
theorem TripLin.congr {x : Trip} {xs ys : ℕ → Trip} {o : Option ℕ}
    (h : TripLin N q e shs x xs o) (hy : ∀ t, t < N → ys t = xs t) : TripLin N q e shs x ys o :=
  ⟨fun t ht => by rw [hy t ht]; exact h.w t ht,
    fun i hi => ⟨(h.aS i hi).1, fun t ht => by rw [hy t ht]; exact (h.aS i hi).2 t ht⟩,
    fun ho => (h.aN ho).trans
      (Finset.sum_congr rfl fun t ht => by rw [hy t (Finset.mem_range.mp ht)]),
    h.b.trans (Finset.sum_congr rfl fun t ht => by rw [hy t (Finset.mem_range.mp ht)])⟩

/-- One product. -/
theorem LinAt.one {x : Trip} {xs : ℕ → Trip} {o : Option ℕ} (h : TripLin N q e shs x xs o)
    (ls : ℕ → List Trip) (hl : ∀ t, t < N → ls t = [xs t]) : LinAt N q e shs [x] ls [o] := by
  refine ⟨fun t ht => by rw [hl t ht]; rfl, rfl, fun k hk => ?_⟩
  have hk0 : k = 0 := by
    have : k < 1 := hk
    omega
  subst hk0
  exact h.congr fun t ht => by
    show (ls t).getD 0 trip0 = xs t
    rw [hl t ht]
    rfl

/-- The relation reads the corners' lists below N alone. -/
theorem LinAt.congr {l : List Trip} {fs ls : ℕ → List Trip} {ix : List (Option ℕ)}
    (h : LinAt N q e shs l fs ix) (hl : ∀ t, t < N → ls t = fs t) : LinAt N q e shs l ls ix :=
  ⟨fun t ht => by rw [hl t ht]; exact h.len t ht, h.lix, fun k hk =>
    (h.at_ k hk).congr fun t ht => by
      show (ls t).getD k trip0 = (fs t).getD k trip0
      rw [hl t ht]⟩

/-- **Two lists end to end.** -/
theorem LinAt.append {l₁ l₂ : List Trip} {f₁ f₂ : ℕ → List Trip} {i₁ i₂ : List (Option ℕ)}
    (h₁ : LinAt N q e shs l₁ f₁ i₁) (h₂ : LinAt N q e shs l₂ f₂ i₂) (ls : ℕ → List Trip)
    (hl : ∀ t, t < N → ls t = f₁ t ++ f₂ t) : LinAt N q e shs (l₁ ++ l₂) ls (i₁ ++ i₂) := by
  refine ⟨fun t ht => ?_, ?_, fun k hk => ?_⟩
  · rw [hl t ht, List.length_append, List.length_append, h₁.len t ht, h₂.len t ht]
  · rw [List.length_append, List.length_append, h₁.lix, h₂.lix]
  · by_cases hk1 : k < l₁.length
    · rw [List.getD_append _ _ _ _ hk1, List.getD_append _ _ _ _ (by rw [h₁.lix]; exact hk1)]
      refine (h₁.at_ k hk1).congr fun t ht => ?_
      show (ls t).getD k trip0 = (f₁ t).getD k trip0
      rw [hl t ht, List.getD_append _ _ _ _ (by rw [h₁.len t ht]; exact hk1)]
    · have hk2 : l₁.length ≤ k := Nat.le_of_not_lt hk1
      have hk3 : k - l₁.length < l₂.length := by
        rw [List.length_append] at hk
        omega
      rw [List.getD_append_right _ _ _ _ hk2,
        List.getD_append_right _ _ _ _ (by rw [h₁.lix]; exact hk2), h₁.lix]
      refine (h₂.at_ _ hk3).congr fun t ht => ?_
      show (ls t).getD k trip0 = (f₂ t).getD (k - l₁.length) trip0
      rw [hl t ht, List.getD_append_right _ _ _ _ (by rw [h₁.len t ht]; exact hk2), h₁.len t ht]

/-- A loop that answers, opened at its first member. -/
theorem mapM_cons_some {α β : Type} {f : α → Option β} {a : α} {l : List α} {L : List β}
    (h : (a :: l).mapM f = some L) : ∃ b L', f a = some b ∧ l.mapM f = some L' ∧ L = b :: L' := by
  rw [List.mapM_cons] at h
  obtain ⟨b, hb, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨L', hL, h⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨b, L', hb, hL, (Option.some.inj h).symm⟩

/-- **A loop that makes a list of products for each member of a list, all laid end to end.** fz: at
the point; ft t: at corner t. out: how a member's answer is read as a list. -/
theorem LinAt.mapM {α β : Type} (out : β → List Trip) (fz : α → Option β) (ft : ℕ → α → Option β)
    (ixf : α → List (Option ℕ)) : ∀ (xs : List α),
    (∀ a ∈ xs, ∀ (bz : β) (bt : ℕ → β), fz a = some bz → (∀ t, t < N → ft t a = some (bt t)) →
      LinAt N q e shs (out bz) (fun t => out (bt t)) (ixf a)) →
    ∀ (Lz : List β) (Lt : ℕ → List β), xs.mapM fz = some Lz →
      (∀ t, t < N → xs.mapM (ft t) = some (Lt t)) →
      LinAt N q e shs (Lz.flatMap out) (fun t => (Lt t).flatMap out) (xs.flatMap ixf)
  | [], _, Lz, Lt, hz, ht => by
    have e0 : Lz = [] := (Option.some.inj hz).symm
    rw [e0]
    exact LinAt.nil _ fun t h => by
      have e1 : Lt t = [] := (Option.some.inj (ht t h)).symm
      show (Lt t).flatMap out = []
      rw [e1]
      rfl
  | a :: xs, h, Lz, Lt, hz, ht => by
    obtain ⟨bz, Lz', h1, h2, rfl⟩ := mapM_cons_some hz
    have hc : ∀ t, t < N → ∃ b L', ft t a = some b ∧ xs.mapM (ft t) = some L' ∧ Lt t = b :: L' :=
      fun t htN => mapM_cons_some (ht t htN)
    classical
    let bt : ℕ → β := fun t => if htN : t < N then (hc t htN).choose else bz
    let Lt' : ℕ → List β := fun t => if htN : t < N then (hc t htN).choose_spec.choose else []
    have hbt : ∀ t (htN : t < N), ft t a = some (bt t) ∧ xs.mapM (ft t) = some (Lt' t) ∧
        Lt t = bt t :: Lt' t := by
      intro t htN
      have := (hc t htN).choose_spec.choose_spec
      simp only [bt, Lt', dif_pos htN]
      exact this
    have A := h a (List.mem_cons_self ..) bz bt h1 fun t htN => (hbt t htN).1
    have B := LinAt.mapM out fz ft ixf xs (fun a' ha' => h a' (List.mem_cons_of_mem _ ha')) Lz' Lt'
      h2 fun t htN => (hbt t htN).2.1
    rw [List.flatMap_cons, List.flatMap_cons]
    exact A.append B _ fun t htN => by
      show (Lt t).flatMap out = out (bt t) ++ (Lt' t).flatMap out
      rw [(hbt t htN).2.2, List.flatMap_cons]

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.LinAt.nil
#print axioms ProofFile.Honest.K4.LinAt.one
#print axioms ProofFile.Honest.K4.TripLin.congr
#print axioms ProofFile.Honest.K4.LinAt.congr
#print axioms ProofFile.Honest.K4.LinAt.append
#print axioms ProofFile.Honest.K4.mapM_cons_some
#print axioms ProofFile.Honest.K4.LinAt.mapM
