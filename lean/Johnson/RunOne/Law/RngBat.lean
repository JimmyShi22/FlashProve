-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/RngBat.lean: WHAT THE KIND K12's BATCHING SAYS WHERE IT RETURNS. Small statements and proofs, over the kind's own text alone.
OBJECT. `First.Close.bat`, the batching that the kind's block calls (Johnson/Desc/First/Close/Closing.lean), where it returns.
USER. Johnson/RunOne/Law/RngAsked.lean (asked_at_bat), RngCond.lean (bat_says), RngAtKeyD.lean (bind_ok).
LETTERS. All free; the one premise is that the batching returns.
  `bind_ok`, `map_ok`, `need_ok`, `got_ok`, `heard_drawn`: what a returning step says.
  `bat_says`: where `bat S g e r` returns (row, L, S'): the group G is there; L is its layout; S' is the statement with the test begun; one element t was drawn; the entry counts the rows; and row is the program's batching of the rows in their fixed order at t.
(The kind's own files have the like of `bat_says`: bat_ok, BatOk.lean.) Nothing on soundness.

-/
import Johnson.Desc.First.Close.Closing
import Johnson.Desc.K12.Law.SwUnfold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.RngBat
open OnBytes OnBytes.Slice
open VerifiableInference.Desc.First.Close (bat heard named got need onSt)

/-! ## 1 What a returning step says -/

theorem bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : x >>= f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem map_ok {ε α β : Type} {x : Except ε α} {f : α → β} {b : β}
    (h : x.map f = .ok b) : ∃ a, x = .ok a ∧ f a = b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, Except.ok.inj h⟩

theorem need_ok {n : String} {b : Bool} {u : Unit} (h : need n b = .ok u) : b = true := by
  cases b with
  | true => rfl
  | false => cases h

theorem got_ok {α : Type} {n : String} {x : Option α} {a : α} (h : got n x = .ok a) :
    x = some a := by
  cases x with
  | none => cases h
  | some c => exact congrArg some (Except.ok.inj h)

/-- Where a round is heard, it has drawn just one element, and that is what is returned. -/
theorem heard_drawn {name : String} {items : Nat} {e : Fmt.Entry} {r : Fmt.RoundView} {roots : Nat}
    {p : List E × E} (h : heard name items e r roots = .ok p) :
    ∃ t, r.drawn.elems = [t] ∧ p.2 = E.ofTriple t := by
  unfold heard at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨xs, _, h⟩ := bind_ok h
  split at h
  · rename_i t ht
    refine ⟨t, ht, ?_⟩
    have e2 : (xs, E.ofTriple t) = p := Except.ok.inj h
    rw [← e2]
  · cases h

/-- **Where the kind's batching returns.** -/
theorem bat_says {S S' : Statement} {g : Nat} {e : Fmt.Entry} {r : Fmt.RoundView} {row : GroupRow}
    {L : GroupLayout} (h : bat S g e r = .ok (row, L, S')) :
    ∃ G t, S.groups[g]? = some G ∧ S.layout g = some L ∧ S' = begun S g G ∧
      r.drawn.elems = [t] ∧ e.rows = (runRows S G).size ∧
      Bat.combine (begun S g G) g ⟨L, runRows S G⟩ (E.ofTriple t) = some row := by
  unfold bat at h
  obtain ⟨_, _, k1⟩ := bind_ok h
  obtain ⟨⟨input, d⟩, h2, k2⟩ := bind_ok k1
  obtain ⟨x, hx, k3⟩ := bind_ok k2
  obtain ⟨_, hn, k4⟩ := bind_ok k3
  obtain ⟨row', hc, k5⟩ := bind_ok k4
  obtain ⟨p, hp, rfl⟩ := map_ok hx
  obtain ⟨t, ht, hpt⟩ := heard_drawn hp
  have hc' := got_ok hc
  have hn' := need_ok hn
  obtain ⟨G, lay, a1, a2, rfl, rfl⟩ := H2K.Sw.beginRunP_ok (got_ok h2)
  cases k5
  refine ⟨G, t, a1, a2, rfl, ht, beq_iff_eq.1 hn', ?_⟩
  rw [← hpt]
  exact hc'

end Johnson.RunOne.Law.RngBat

#print axioms Johnson.RunOne.Law.RngBat.bat_says
