-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/Step.lean: the block of a sending by itself, as a step of the fold.

Main names: roundsFit_two, map_ok, step_sendOwn.

What is not claimed. Nothing on a segment's later moment, on the first segment's opening, or on the
blocks at the first chain's record. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.Sound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice

/-! ## The block as a step -/

variable {Cl : Type}

theorem roundsFit_two (a b : Fmt.DeclaredRound) (rs : List Fmt.RoundView)
    (h : roundsFit [a, b] rs = true) : ∃ r₁ r₂, rs = [r₁, r₂] := by
  match rs, h with
  | [r₁, r₂], _ => exact ⟨r₁, r₂, rfl⟩
  | [], h => simp [roundsFit] at h
  | [_], h => simp [roundsFit] at h
  | _ :: _ :: _ :: _, h => simp [roundsFit] at h

theorem map_ok {α β : Type} (x : Except String α) (f : α → β) (b : β) :
    x.map f = .ok b ↔ ∃ a, x = .ok a ∧ f a = b := by
  cases x <;> simp [Except.map]

/-- **The block of a sending by itself, as a step**: it goes on just where its two rounds fit and
asks holds; it takes no column; the record behind is the written one. -/
theorem step_sendOwn (ft : Nat) (P : Par) (s s' : Owing (DState (Array Nat))) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (n : Nat) :
    Block.step ft (sendOwn P : Block _ Cl) s rs cols = .ok (s', n) ↔
      ∃ r₁ r₂, rs = [r₁, r₂] ∧ roundsFit (rounds P) rs = true ∧ asks P s.owed s.held r₁ r₂ ∧
        n = 0 ∧ s' = { owed := none, held := { behind P s.held (seedsOf P r₁) (answersIn r₂) with
          loc := (Array.range P.sent.size).map (· + s.held.st.oracles.size) } } := by
  constructor
  · intro h
    unfold Block.step at h
    obtain ⟨_, h1, h⟩ := (bind_ok _ _ _).1 h
    have h1 : roundsFit (rounds P) rs = true := (need_ok _ _ _).1 h1
    obtain ⟨r₁, r₂, rfl⟩ := roundsFit_two _ _ rs h1
    obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
    obtain ⟨t, h3, h⟩ := (bind_ok _ _ _).1 h
    obtain ⟨x, hx, rfl⟩ := (map_ok _ _ _).1 h3
    obtain ⟨ha, hi, hd⟩ := (decideSend_iff P s.owed s.held x.2 (noDigest r₁) (noDigest r₂) x.1).1 hx
    have hp : (({ owed := none, held := { x.2 with loc := x.1 } } :
        Owing (DState (Array Nat))), 0) = (s', n) := by simpa [pure, Except.pure] using h
    obtain ⟨e1, e2⟩ := Prod.mk.inj hp
    refine ⟨r₁, r₂, rfl, h1, ha, e2.symm, ?_⟩
    rw [← e1, hi, hd]
    rfl
  · rintro ⟨r₁, r₂, rfl, h1, ha, rfl, rfl⟩
    unfold Block.step
    refine (bind_ok _ _ _).2 ⟨(), (need_ok _ _ _).2 h1, ?_⟩
    refine (bind_ok _ _ _).2 ⟨(), (need_ok _ _ _).2 rfl, ?_⟩
    refine (bind_ok _ _ _).2 ⟨_, (map_ok _ _ _).2 ⟨_, (decideSend_iff P s.owed s.held _
      (noDigest r₁) (noDigest r₂) _).2 ⟨ha, rfl, rfl⟩, rfl⟩, rfl⟩

end VerifiableInference.Desc.K1
