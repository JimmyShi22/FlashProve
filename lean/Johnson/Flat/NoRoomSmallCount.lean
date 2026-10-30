-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/NoRoomSmallCount.lean: the count in the rule on a written round that draws matrix
entries alone (Johnson/Flat/NoRoomSmall.lean) is the library's own bound on the bad values of its
smallness test, at 128 combinations.

Why. The rule speaks of the number 4 ^ (c * 128) / 2 ^ 128 and of a shape of written round. The
library's theorem on its own round of the smallness test (`Cb.Pv.Tail.cnt_bad_le`,
Cb/Pv/Tail/Know.lean) bounds the values that can be drawn and lead from messages without cells to
digits that meet all clauses, by the number of all values that can be drawn divided by 2 ^ tau. Here
the two numbers are shown to be one, and the two theorems are joined.

ALL OF THIS FILE IS A TOOL: all seven theorems are tools beneath a row, and none is a row: no
description, no plan and no written round of the one description is named. s, Λ and g are letters;
the written round holds the PRODUCT columns · 128 alone; nothing here reads 128 off a record, a plan
or a description. The same written round has 24,086 · 128 and 48,172 · 64 entries: d cannot tell the
two apart, and s.tau = 128 is for whoever spends a theorem of this file to pay.

Definitions, statements and proofs. s: the sizes of the smallness test (`Cb.Pv.Tail.Size`); Λ: its
letters.
  `card_dr_div`: at s.tau = 128: card (Dr s) / 2 ^ s.tau = 4 ^ (s.columns * 128) / 2 ^ 128.
  `eps_small`: so the error of the library's round (`Cb.Pv.Tail.eps`) is that number.
  `BadDraw Λ x y msg β`: the property that `cnt_bad_le` counts, by name.
  `cnt_bad_le_small`: under `Size.OK` and s.tau = 128 the drawn values with it number at most
    4 ^ (s.columns * 128) / 2 ^ 128.
  `card_vals_eq_dr`, `exists_reading`: at s.tau = 128: a written round that draws s.columns * 128
    matrix entries alone has as many typed values as the test has values that can be drawn; so there
    is a map from the one to the other that is one to one and onto.
  `cnt_bad_typed_le`: under `Size.OK` and s.tau = 128: for ANY finite type V, not the round's typed
    values alone, and EVERY one-to-one map g from V to the values that can be drawn, the members of
    V whose image has the property number at most 4 ^ (s.columns * 128) / 2 ^ 128.
  `small_round_below`: THE TWO JOINED. At such a written round and every such g: the number of typed
    values whose image has the property is a share of at most 2 ^ -128 of the written verifier
    messages (`RoundBelow`, OnBytes/Slice/ManyErr.lean).

Limits. The two theorems speak of two types of values: the format's typed values of a written round
(`Run.Vals`), and the library's own drawn matrices (`Cb.Pv.Tail.Dr`). WHAT IS NOT SHOWN, and is a
premise or a letter here: which map g a description reads its typed values by, that it is one to
one, and that it lays the entries as the format does (which entry belongs to which column and
combination; which pair of bits stands for -1, 0, 1). The count does not depend on that choice; what
the property says of a protocol does. Nor is it shown that a description's round of the smallness
test is the library's round at letters with 128 combinations and these columns, nor `Size.OK`, nor
that a plan's round has the shape. All limits of Cb/Pv/Tail/Know.lean hold here too: above all, the
messages must hold only what is committed before the matrix is drawn. The statement names no
verifier. Nothing on soundness.


-/
import Johnson.Flat.NoRoomSmall
import Cb.Pv.Tail.Know

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace VerifiableInference.Number
open Iop Prob Run OnBytes.Slice Cb.Pv.Tail

/-- The library's number at 128 combinations is the rule's count. -/
theorem card_dr_div (s : Size) (hτ : s.tau = 128) :
    Fintype.card (Dr s) / 2 ^ s.tau = 4 ^ (s.columns * 128) / 2 ^ 128 := by
  rw [card_dr, hτ]

variable {K : Type} [CommRing K] {s : Size} (Λ : Letters K s)

omit [CommRing K] in
/-- The error of the library's round of the smallness test, at 128 combinations. -/
theorem eps_small (hτ : s.tau = 128) :
    eps Λ = ((4 ^ (s.columns * 128) / 2 ^ 128, ()) : ℕ × Unit) := by
  unfold eps
  rw [card_dr_div s hτ]

/-- The drawn matrix β leads from messages without cells to digits that meet all clauses: the
property that `Cb.Pv.Tail.cnt_bad_le` counts. -/
def BadDraw (x : Λ.X) (y : Λ.E.Str) (msg : Λ.M) (β : Dr s) : Prop :=
  ∃ wp, (B Λ).relR ((x, β), y) (msg, wp) ∧ ¬ (A Λ).relR (x, y) (msg, wp)

/-- The library's bound, at 128 combinations, in the rule's count. -/
theorem cnt_bad_le_small (hs : s.OK) (hτ : s.tau = 128) (x : Λ.X) (y : Λ.E.Str) (msg : Λ.M) :
    cnt (BadDraw Λ x y msg) ≤ 4 ^ (s.columns * 128) / 2 ^ 128 :=
  (cnt_bad_le Λ hs x y msg).trans (le_of_eq (card_dr_div s hτ))

/-- A written round that draws s.columns * 128 matrix entries alone has as many typed values as the
smallness test, at 128 combinations, has values that can be drawn. -/
theorem card_vals_eq_dr (s : Size) (hτ : s.tau = 128) {d : PQ.RD}
    (hd : EntriesOnly d (s.columns * 128)) :
    Fintype.card (Vals .two (Fmt.dsOf d.entry d.kind)) = Fintype.card (Dr s) := by
  rw [← Nat.card_eq_fintype_card, card_vals_all, hd.1, ← card_vals_all, card_vals_trits, card_dr,
    hτ]

/-- So some map from the one to the other is one to one and onto. -/
theorem exists_reading (s : Size) (hτ : s.tau = 128) {d : PQ.RD}
    (hd : EntriesOnly d (s.columns * 128)) :
    Nonempty (Vals .two (Fmt.dsOf d.entry d.kind) ≃ Dr s) :=
  ⟨Fintype.equivOfCardEq (card_vals_eq_dr s hτ hd)⟩

/-- Read through any one-to-one map: no more typed values than drawn values have the property. -/
theorem cnt_bad_typed_le (hs : s.OK) (hτ : s.tau = 128) {V : Type} [Fintype V] (g : V → Dr s)
    (hg : Function.Injective g) (x : Λ.X) (y : Λ.E.Str) (msg : Λ.M) :
    cnt (fun v => BadDraw Λ x y msg (g v)) ≤ 4 ^ (s.columns * 128) / 2 ^ 128 := by
  have hfib : ∀ β : Dr s, cnt (fun v => g v = β) ≤ 1 := by
    intro β
    haveI : Subsingleton {v : V // g v = β} :=
      ⟨fun a b => Subtype.ext (hg (a.2.trans b.2.symm))⟩
    exact Finite.card_le_one_iff_subsingleton.2 inferInstance
  have h := cnt_comp_le g hfib (BadDraw Λ x y msg)
  rw [Nat.mul_one] at h
  exact h.trans (cnt_bad_le_small Λ hs hτ x y msg)

/-- **The two joined.** At a written round that draws s.columns * 128 matrix entries alone, without
work, and every one-to-one map from its typed values to the matrices that the smallness test can
draw: the typed values whose matrix leads from messages without cells to digits that meet all
clauses are a share of at most 2 ^ -128 of the round's written verifier messages. -/
theorem small_round_below (hs : s.OK) (hτ : s.tau = 128) {d : PQ.RD}
    (hd : EntriesOnly d (s.columns * 128)) (g : Vals .two (Fmt.dsOf d.entry d.kind) → Dr s)
    (hg : Function.Injective g) (x : Λ.X) (y : Λ.E.Str) (msg : Λ.M) :
    RoundBelow (cnt fun v => BadDraw Λ x y msg (g v)) d ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  (no_room_small s.columns d hd).mono (cnt_bad_typed_le Λ hs hτ g hg x y msg)

end VerifiableInference.Number

#print axioms VerifiableInference.Number.card_dr_div
#print axioms VerifiableInference.Number.eps_small
#print axioms VerifiableInference.Number.cnt_bad_le_small
#print axioms VerifiableInference.Number.card_vals_eq_dr
#print axioms VerifiableInference.Number.exists_reading
#print axioms VerifiableInference.Number.cnt_bad_typed_le
#print axioms VerifiableInference.Number.small_round_below
