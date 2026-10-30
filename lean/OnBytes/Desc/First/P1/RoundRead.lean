-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/P1/RoundRead.lean: ONE WRITTEN ROUND, READ TWICE. A kind's text hears a written
round as plain data: the words that it sends and draws (`flatOf`, OnBytes/K/Kc/Laws.lean). The maps
to the typed rounds read the same written round as elements of the field (`sentT`,
OnBytes/Flat/CarrySProx.lean; `gOne`, `gVec`, `gSeed`, OnBytes/Slice/). Here: THE READING `gl` OF
THE WORDS IS THE TYPED VALUE. Definitions, statements and proofs.

  `AllE d`: every item of the round's message is an element of the extension field.
  `sentE d m`, `drawnE d c`: the words that the written round (m, c) sends and draws, as a view's
    round holds them: `rvT_cons`, `flat_cons`: they are the fields `sent` and `drawn` of the first
    round of the flat tape.
  `sent_at`: under `AllE d`: the reading of the word number i that is sent (the zero word beyond the
    end) is `sentT d m i`.
  `drawn_at`, `drawn_head`, `drawn_vec`: the reading of the word number i that is drawn is the typed
    value number i; so the first is `gOne`, and the first n are `gVec n`. No premise.
  `drawn_seed`: if the reading of the first drawn word is not 0, it is the factor of `gSeed 0`.

NO NEW ARGUMENT: `sentOf_map`, `rvOf_els` (OnBytes/Slice/RoundsOf.lean), `E.triple_ofTriple`.

NEAREST KIN: Johnson/Top/H0/MergeLaw/View.lean (`rvOne`, `sentT_of`, `gOne_of`):
the same tie for the merge's own rounds, under "all items of the round are scalars" as a Boolean
test's yes. This file does not import it (a file under
OnBytes/ outside OnBytes/Dry/ imports none under Johnson/).

Limits. `AllE` is a premise: where a message holds another kind of item the text's `leading` stops
at it and `sentT` goes on. That a plan's rounds have it is not shown here. Both sides read a sent
word by the one function `toE` (OnBytes/Slice/Field.lean:37): whether the word is below the prime is
not asked. Nothing on a tree, a position or a test of work.
-/
import OnBytes.Flat.CarrySProx
import OnBytes.Flat.RoundsTView
import OnBytes.Slice.RoundsMaps
import OnBytes.K.Kc.Laws
import OnBytes.Model.HideLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.P1
open Iop Prob Cb _root_.Run OnBytes.K.Kc OnBytes.Flat OnBytes.Maker OnBytes.Slice

/-- The reading of a word in the library's extension field (OnBytes/Model/HideLaws.lean). -/
abbrev gl : OnBytes.Model.Reading Cb.Gl.E := OnBytes.Model.Reading.gl

/-! ### Lists -/

theorem getD_read {α β : Type} (f : α → β) (l : List α) (i : ℕ) (a : α) (b : β) (h : f a = b) :
    f (l.getD i a) = (l.map f).getD i b := by
  subst h
  exact (List.getD_map ..).symm

theorem headD_eq_getD {α : Type} (l : List α) (a : α) : l.headD a = l.getD 0 a := by
  cases l <;> rfl

/-! ### What a written round sends and draws, as words -/

/-- Every item of the round's message is an element of the extension field. -/
def AllE (d : RDT) : Prop := ∀ it ∈ d.items, it = Fmt.Item.e

/-- The words that a written prover message sends, as a text hears them. -/
def sentE (d : RDT) (m : (wT d).Msg) : List OnBytes.E :=
  leading (PQ.PlainOf.gots (toRD d).items (GPlain.old (b := (toRD d).entry.work) (msgRD d m).2))

/-- The words that a written verifier message draws, as a text hears them. -/
def drawnE (d : RDT) (c : (wT d).Chal) : List OnBytes.E :=
  ((ckP .two).dr (toRD d).entry (toRD d).kind
    (GChal.old (b := (toRD d).entry.work) c)).elems.map OnBytes.E.ofTriple

/-- The view's round of a written round. -/
def rvW (d : RDT) (m : (wT d).Msg) (c : (wT d).Chal) : Fmt.RoundView :=
  ⟨PQ.PlainOf.gots (toRD d).items (GPlain.old (b := (toRD d).entry.work) (msgRD d m).2),
    (ckP .two).dr (toRD d).entry (toRD d).kind (GChal.old (b := (toRD d).entry.work) c)⟩

theorem rvT_cons (d : RDT) (ds : List RDT) (m : (wT d).Msg) (c : (wT d).Chal)
    (τ : Tr (uLT (ckP .two) ds)) :
    rvT (ckP .two) (d :: ds) (m, c, τ) = rvW d m c :: rvT (ckP .two) ds τ := rfl

/-- The flat round of a written round holds these words. -/
theorem flat_cons (d : RDT) (m : (wT d).Msg) (c : (wT d).Chal) (e : Option Fmt.Entry) :
    (flatOf (rvW d m c) e).sent = sentE d m ∧ (flatOf (rvW d m c) e).drawn = drawnE d c :=
  ⟨rfl, rfl⟩

/-! ### The words sent, read -/

theorem gl_ofTriple (x : UInt64 × UInt64 × UInt64) : gl.val (OnBytes.E.ofTriple x) = toE x := rfl

theorem leading_read : ∀ (l : List Fmt.Item) (x : PQ.PlainOf l), (∀ it ∈ l, it = Fmt.Item.e) →
    (leading (PQ.PlainOf.gots l x)).map gl.val = (Fmt.M1.sentOf (PQ.PlainOf.gots l x)).map toE
  | [], _, _ => rfl
  | .e :: l, (x : Fmt.Ext × PQ.PlainOf l), h =>
    congrArg (toE x.1 :: ·) (leading_read l x.2 fun it hi => h it (List.mem_cons_of_mem _ hi))
  | .root :: _, _, h => absurd (h .root List.mem_cons_self) (by decide)
  | .f :: _, _, h => absurd (h .f List.mem_cons_self) (by decide)
  | .word :: _, _, h => absurd (h .word List.mem_cons_self) (by decide)
  | .answer :: _, _, h => absurd (h .answer List.mem_cons_self) (by decide)

theorem sentE_read (d : RDT) (m : (wT d).Msg) (h : AllE d) :
    (sentE d m).map gl.val = ansOf (toRD d) (msgRD d m) :=
  (leading_read _ _ h).trans (sentOf_map _)

/-- **The reading of a sent word is the typed scalar.** -/
theorem sent_at (d : RDT) (m : (wT d).Msg) (h : AllE d) (i : ℕ) :
    gl.val ((sentE d m).getD i OnBytes.zeroE) = sentT d m i := by
  unfold sentT
  rw [← sentE_read d m h]
  exact getD_read _ _ _ _ _ gl.zero

/-! ### The words drawn, read -/

theorem drawnE_read (d : RDT) (m : (wT d).Msg) (c : (wT d).Chal) :
    (drawnE d c).map gl.val = elemsV _ (valsOf (toRD d) c) := by
  unfold drawnE
  rw [List.map_map]
  exact rvOf_els (toRD d) (msgRD d m) c

/-- **The reading of a drawn word is the typed value.** -/
theorem drawn_at (d : RDT) (m : (wT d).Msg) (c : (wT d).Chal) (i : ℕ) :
    gl.val ((drawnE d c).getD i OnBytes.zeroE) = (elemsV _ (valsOf (toRD d) c)).getD i 0 := by
  rw [← drawnE_read d m c]
  exact getD_read _ _ _ _ _ gl.zero

theorem drawn_head (d : RDT) (m : (wT d).Msg) (c : (wT d).Chal) :
    gl.val ((drawnE d c).headD OnBytes.zeroE) = gOne _ (valsOf (toRD d) c) := by
  rw [headD_eq_getD]
  exact drawn_at d m c 0

theorem drawn_vec (d : RDT) (m : (wT d).Msg) (c : (wT d).Chal) (n : ℕ) :
    (fun i : Fin n => gl.val ((drawnE d c).getD i.val OnBytes.zeroE)) =
      gVec n _ (valsOf (toRD d) c) :=
  funext fun i => drawn_at d m c i.val

theorem drawn_seed (d : RDT) (m : (wT d).Msg) (c : (wT d).Chal)
    (h : gl.val ((drawnE d c).headD OnBytes.zeroE) ≠ 0) :
    (gSeed 0 _ (valsOf (toRD d) c)).2.val = gl.val ((drawnE d c).headD OnBytes.zeroE) := by
  have e : gl.val ((drawnE d c).headD OnBytes.zeroE) = (elemsV _ (valsOf (toRD d) c)).getD 0 0 :=
    drawn_head d m c
  show (unitOf ((elemsV _ (valsOf (toRD d) c)).getD 0 0)).val = _
  rw [unitOf_val (by rw [← e]; exact h), e]

end OnBytes.Desc.First.P1

#print axioms OnBytes.Desc.First.P1.rvT_cons
#print axioms OnBytes.Desc.First.P1.sent_at
#print axioms OnBytes.Desc.First.P1.drawn_at
#print axioms OnBytes.Desc.First.P1.drawn_head
#print axioms OnBytes.Desc.First.P1.drawn_vec
#print axioms OnBytes.Desc.First.P1.drawn_seed
