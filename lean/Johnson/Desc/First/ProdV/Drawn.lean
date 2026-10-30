--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/ProdV/Drawn.lean: from bad elements of the field to bad drawn values. The grand
product's law counts sets of elements of a field K; what a round draws is three machine words. At
the library's reading Reading.gl, and among drawn values whose words are below the prime, there are
no more bad drawn values than bad elements.

`gl_inj`: on words below the prime Reading.gl is one-to-one: OnBytes.Slice.readE_inj
(OnBytes/Slice/ProgField.lean) at Reading.gl's own map. `drawn_le`: any list without repeats of
drawn values, each with its words below the prime and read into the set S, is at most as long as S
has members. `full_below`: the part's whole count at the full size against the field's size, in
whole numbers: 64,848 * 2^175 is less than the number of elements of Cb.Gl.E (Cb.Gl.gl_card,
Cb/Gl/GlField.lean). `small_below`: the like at the small proof.

Limits. That a round's element is drawn evenly among the values with words below the prime is the
strict reader's rule of drawing, and is not stated here. readE_inj is a lemma on a pure function:
no routine in a context is reached.
Not claimed: any probability.

-/
import OnBytes.Slice.ProgField
import OnBytes.Model.HideLaws
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Nodup
import Mathlib.Tactic.NormNum
import Johnson.Desc.First.ProdV.RunCount

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.ProdV
open OnBytes OnBytes.Model

theorem gl_inj (a b : E) (ha : okE a = true) (hb : okE b = true)
    (h : Reading.gl.val a = Reading.gl.val b) : a = b :=
  OnBytes.Slice.readE_inj a b ha hb h

theorem drawn_le (S : Finset Cb.Gl.E) (l : List E) (hn : l.Nodup)
    (h : ∀ a ∈ l, okE a = true ∧ Reading.gl.val a ∈ S) : l.length ≤ S.card := by
  classical
  have hinj : (l.map Reading.gl.val).Nodup :=
    List.Nodup.map_on (fun a ha b hb e => gl_inj a b (h a ha).1 (h b hb).1 e) hn
  have hsub : (l.map Reading.gl.val).toFinset ⊆ S := by
    intro x hx
    rw [List.mem_toFinset] at hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact (h a ha).2
  calc l.length = (l.map Reading.gl.val).length := (List.length_map _).symm
    _ = (l.map Reading.gl.val).toFinset.card := (List.toFinset_card_of_nodup hinj).symm
    _ ≤ S.card := Finset.card_le_card hsub

theorem full_below : looksBad fullLooks * 2 ^ 175 < Fintype.card Cb.Gl.E := by
  obtain ⟨_, hc, hlo, _⟩ := Cb.Gl.gl_card
  rw [full_bad, hc]
  exact lt_trans (by norm_num) hlo

theorem small_below : looksBad smallLooks * 2 ^ 177 < Fintype.card Cb.Gl.E := by
  obtain ⟨_, hc, hlo, _⟩ := Cb.Gl.gl_card
  rw [small_bad, hc]
  exact lt_trans (by norm_num) hlo

end VerifiableInference.Desc.First.ProdV

#print axioms VerifiableInference.Desc.First.ProdV.drawn_le
#print axioms VerifiableInference.Desc.First.ProdV.full_below
