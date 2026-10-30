-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/ExtQAtId.lean: AT A NUMBER WHOSE ROW LAYS NOTHING THE TABLE's EXTRACTOR IS THE
IDENTITY: general in the number, the list of places and the segments' sorts: no kind is named. Two
definitions, four theorems.
Why. The sockets of several kinds' laws at the first chain's table (K3's, K4's, K13's) bear one
premise of one form: "the table's extractor lays nothing at my numbers": ∀ a b w, E k a b w = w.
At the meant E, the table's one extractor `extQAt` (Johnson/Desc/Sound/BordersFill.lean), it was
held by nobody. `extQ_id` (the same file) has it AT A PLACE whose row lays nothing; `extQAt` looks
the place up by the block's number. Here the two are joined, once for all kinds, with a test that
the kernel can evaluate at written lists.
  `extQAt_id_at`: where the list of places has p at number k and p's row lays nothing.
  `extQAt_id_beyond`: beyond the list's end (by `extQAt`'s own text).
  `laysNothingAs links ps k p`: A TEST WITH CODE, WITH THE PLACE PINNED: the list has just p at
  number k, and p's row lays nothing. `extQAt_id_of_pinned`: **where it passes, the extractor is
  the identity at that number.** THIS IS THE ONE FOR A KIND's FILES: a mistyped number or place
  gets false.
  `laysNothingAt links ps k`, `extQAt_id_of_test`: the bare test, without a place. IT DOES NOT SAY
  WHOSE PLACE IT LOOKED AT: it says yes beyond the list's end, and at any other kind's place whose
  row lays nothing (most do): the theorem is true there, but a file that mistypes its number
  learns nothing from it. Safe only beside a line that pins the place.
Silly members. At the empty list of places every number passes the bare test, and `extQAt` is the
identity everywhere: by its text. The pinned test fails there.
Limits. "LAYS NOTHING" IS THE TABLE's OWN FIELD `BlockRow.lays` (Johnson/Desc/First/Borders.lean):
IT IS NO CLAIM ON A KIND's BLOCK: IT DEFINES THE TABLE's EXTRACTOR: the table's CHOICE. No debt
hides in it: whether a kind's law can be proved AT THE IDENTITY is that law's own burden, in the
open, in its socket's other premises. Nothing on whether a piece's own extractor IS the table's
(`EachExtQ`). No probability: no soundness follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.BordersFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Cb Johnson.Pack OnBytes.Slice
open VerifiableInference.Desc.First (ModelPart Numbers)

/-- **A test on the table and the list of places**: the row of the place at number k lays nothing.
Beyond the list: true. -/
def laysNothingAt (links : List ModelPart) (ps : List Place) (k : ℕ) : Bool :=
  match ps[k]? with
  | some p => !(First.rowOf links p).lays
  | none => true

/-- **The test with the place pinned**: the list of places has JUST p at number k, and p's row lays
nothing. A file that mistypes its number, or its place, gets false. -/
def laysNothingAs (links : List ModelPart) (ps : List Place) (k : ℕ) (p : Place) : Bool :=
  (ps[k]? == some p) && !(First.rowOf links p).lays

section
variable (cs : OnBytes.Codes) {Xi P Cells Tok : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : P × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → P × First.S → Option Cells)
  (c₀ : Cells) (tokOf : P × First.S → Tok) {A : Type} {Fr : Frame} (N : Numbers)
  (links : List ModelPart) (ps : List Place) (get : A → P × First.S) (k : ℕ)

/-- Where the list has p at number k and p's row lays nothing. -/
theorem extQAt_id_at (p : Place) (hp : ps[k]? = some p) (h : (First.rowOf links p).lays = false)
    (a b : A × Fr.E.Str) (w : Wit Cells Tok MsgT) :
    extQAt cs G arr smp ms decT c₀ tokOf N links ps get k a b w = w := by
  unfold extQAt
  rw [hp]
  exact extQ_id cs G arr smp ms decT c₀ tokOf N links p h _ _ _ w

/-- Beyond the list's end. -/
theorem extQAt_id_beyond (hp : ps[k]? = none) (a b : A × Fr.E.Str) (w : Wit Cells Tok MsgT) :
    extQAt cs G arr smp ms decT c₀ tokOf N links ps get k a b w = w := by
  unfold extQAt
  rw [hp]

/-- **Where the pinned test passes, the table's extractor is the identity at that number.** -/
theorem extQAt_id_of_pinned (p : Place) (h : laysNothingAs links ps k p = true)
    (a b : A × Fr.E.Str) (w : Wit Cells Tok MsgT) :
    extQAt cs G arr smp ms decT c₀ tokOf N links ps get k a b w = w := by
  unfold laysNothingAs at h
  rw [Bool.and_eq_true] at h
  exact extQAt_id_at cs G arr smp ms decT c₀ tokOf N links ps get k p (eq_of_beq h.1)
    (by simpa using h.2) a b w

/-- Where the bare test passes, the table's extractor is the identity at that number. -/
theorem extQAt_id_of_test (h : laysNothingAt links ps k = true) (a b : A × Fr.E.Str)
    (w : Wit Cells Tok MsgT) : extQAt cs G arr smp ms decT c₀ tokOf N links ps get k a b w = w := by
  unfold laysNothingAt at h
  cases hp : ps[k]? with
  | none => exact extQAt_id_beyond cs G arr smp ms decT c₀ tokOf N links ps get k hp a b w
  | some p =>
    rw [hp] at h
    refine extQAt_id_at cs G arr smp ms decT c₀ tokOf N links ps get k p hp ?_ a b w
    simpa using h

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.extQAt_id_at
#print axioms VerifiableInference.Desc.Sound.extQAt_id_beyond
#print axioms VerifiableInference.Desc.Sound.extQAt_id_of_pinned
#print axioms VerifiableInference.Desc.Sound.extQAt_id_of_test
