-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/KeyLaw/Runs.lean: small laws for whoever reads a link of the kind "lookup":
one run in the gathering of a link's claims; each claim on the planes has mu + d pairs, one for each
variable of the table of bits; lists under mapM in Option.

Main names:
  bindB: Except.bind, backward. runIn_ok: one run in claimsIn (claimsInStep with no test behind).
  planesG_pairs, planesG_three: planesG makes three claims, each with mu + d pairs.
  mapM_congr', mapM_map', mapM_range_bind: lists under mapM.

Limits. Nothing on what a claim says.

-/
import Johnson.Desc.First.Look.KeyLaw.Read

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.KeyLaw
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Fork)

theorem bindB {α β : Type} {x : Except String α} {f : α → Except String β} {b : β}
    (h : x.bind f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- One run in the gathering of a link's claims, where no test stands behind a run. -/
theorem runIn_ok {S Cl : Type} {bs : List (Block S Cl)} {o : ℕ × String} {x y : List Cl × S}
    {run : ℕ → S → Except String (List Cl × S)}
    (hl : ((bs[o.1]?).bind fun b => b.claims.lookup o.2) = some run)
    (h : claimsInStep (fun _ _ _ => .ok ()) bs x o = .ok y) :
    ∃ z, run x.1.length x.2 = .ok z ∧ y = (x.1 ++ z.1, z.2) := by
  unfold claimsInStep at h
  rw [hl] at h
  obtain ⟨r, h1, h2⟩ := bindB h
  cases h1
  cases hr : run x.1.length x.2 with
  | error e => rw [hr] at h2; cases h2
  | ok z =>
    rw [hr] at h2
    cases h2
    exact ⟨z, rfl, rfl⟩

/-- Every claim on the planes has mu + d pairs: one for each variable of the table of bits. -/
theorem planesG_pairs {f : Face} {g : HeardG} {H H' : Fork} {t u : Tape} {pl : List PlaneClaim}
    (h : planesG f g H t = some (pl, H', u)) : ∀ c ∈ pl, c.pairs.length = f.mu + f.d := by
  unfold planesG at h
  replace h := bind_some h
  obtain ⟨x, G1, u1, -, h⟩ := h
  cases pure_some h
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl <;> simp [eqPairs]

/-- There are three of them. -/
theorem planesG_three {f : Face} {g : HeardG} {H H' : Fork} {t u : Tape} {pl : List PlaneClaim}
    (h : planesG f g H t = some (pl, H', u)) : ∃ a b c, pl = [a, b, c] := by
  unfold planesG at h
  replace h := bind_some h
  obtain ⟨x, G1, u1, -, h⟩ := h
  cases pure_some h
  exact ⟨_, _, _, rfl⟩

theorem mapM_congr' {α β : Type} {f g : α → Option β} : ∀ (l : List α), (∀ a ∈ l, f a = g a) →
    l.mapM f = l.mapM g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.mapM_cons, List.mapM_cons, h a List.mem_cons_self,
      mapM_congr' l fun b hb => h b (List.mem_cons_of_mem _ hb)]

theorem mapM_map' {α β γ : Type} (g : α → β) (f : β → Option γ) : ∀ (l : List α),
    (l.map g).mapM f = l.mapM fun a => f (g a)
  | [] => rfl
  | a :: l => by
    rw [List.map_cons, List.mapM_cons, List.mapM_cons, mapM_map' g f l]

theorem mapM_range'_bind {α β : Type} (f : α → Option β) : ∀ (l pre : List α),
    (List.range' pre.length l.length).mapM (fun j => ((pre ++ l)[j]?).bind f) = l.mapM f
  | [], _ => rfl
  | a :: l, pre => by
    rw [List.length_cons, List.range'_succ, List.mapM_cons, List.mapM_cons]
    have e : (pre ++ a :: l)[pre.length]? = some a := by simp
    rw [e]
    have ih := mapM_range'_bind f l (pre ++ [a])
    rw [List.length_append, List.length_singleton, List.append_assoc] at ih
    rw [show ([a] ++ l) = a :: l from rfl] at ih
    rw [ih]
    rfl

/-- Member by member, by its number. -/
theorem mapM_range_bind {α β : Type} (f : α → Option β) (l : List α) :
    (List.range l.length).mapM (fun j => (l[j]?).bind f) = l.mapM f := by
  rw [List.range_eq_range']
  exact mapM_range'_bind f l []

end VerifiableInference.Desc.K3.KeyLaw

#print axioms VerifiableInference.Desc.K3.KeyLaw.runIn_ok
#print axioms VerifiableInference.Desc.K3.KeyLaw.planesG_pairs
#print axioms VerifiableInference.Desc.K3.KeyLaw.mapM_range_bind
