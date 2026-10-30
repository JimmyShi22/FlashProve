-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/ExtAtK4.lean: THE TABLE's EXTRACTOR LAYS NOTHING AT K4's TWELVE NUMBERS: hE of
K4's socket (`k04_kindTied_tiled`, Johnson/Road/K4/K04Tied.lean) at the table's one extractor
`extQAt`, at the written lists `linksFull` and `flatPlacesOf linksFull true`. Three theorems.
Why. K04_law's statement is "for all E that lay nothing at the twelve numbers": at the meant E
that premise was held by nobody.
  `k4LaysB`: a test by the kernel: at each g < 12 the row of K4's place lays nothing.
  `k04_lays_nothing`: the same as a sentence.
  `k04_hE`: **∀ g < 12, ∀ a b w, extQAt … linksFull (flatPlacesOf linksFull true) get (28 g + 4) a
  b w = w**, at all the other letters of `extQAt`: by `atK4_full` and `extQAt_id_at`
  (Johnson/Desc/Sound/ExtQAtId.lean).
Limits. At the two written lists alone: WHICH TERM THE TABLE's TOP LAYS FOR ITS EXTRACTOR AT THE
CONSTANT (its letters for the segments' sorts and the places) IS THE TABLE's FILES' TO SAY. The
table's field `lays` is the table's CHOICE of its extractor, no claim on K4's block: whether K4's
law can be proved at the identity is K04_law's own burden (`K4Asks`, `k04_tied`). Nothing on
soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Road.K4.K04Tied
import Johnson.Desc.Sound.ExtQAtId

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Flat OnBytes.Maker Cb Johnson.Pack OnBytes.Slice
open VerifiableInference.Desc (FileDescription Place Wit)
open VerifiableInference.Desc.First (Numbers flatPlacesOf)
open VerifiableInference.Desc.Sound

/-- A test by the kernel: at each of the twelve groups the row of K4's place lays nothing. -/
theorem k4LaysB : (List.range 12).all
    (fun g => !(VerifiableInference.Desc.First.rowOf linksFull (k4PlaceAt g)).lays) = true := by
  decide

/-- At each of the twelve groups the row of K4's place lays nothing. -/
theorem k04_lays_nothing (g : ℕ) (hg : g < 12) :
    (VerifiableInference.Desc.First.rowOf linksFull (k4PlaceAt g)).lays = false := by
  have h := List.all_eq_true.1 k4LaysB g (List.mem_range.2 hg)
  simpa using h

/-- **The table's extractor lays nothing at K4's twelve numbers.** -/
theorem k04_hE (cs : OnBytes.Codes) {Xi P Cells Tok : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
    (smp : P × VerifiableInference.Desc.First.S → (s : Sending) → (i : Fin s.l.length) →
      Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem)
    (decT : (ℕ → Option (ℕ × List UInt64)) → P × VerifiableInference.Desc.First.S → Option Cells)
    (c₀ : Cells) (tokOf : P × VerifiableInference.Desc.First.S → Tok) {A : Type} {Fr : Frame}
    (N : Numbers) (get : A → P × VerifiableInference.Desc.First.S) (g : ℕ) (hg : g < 12)
    (a b : A × Fr.E.Str) (w : Wit Cells Tok MsgT) :
    extQAt cs G arr smp ms decT c₀ tokOf N linksFull (flatPlacesOf linksFull true) get
      (28 * g + 4) a b w = w :=
  extQAt_id_at cs G arr smp ms decT c₀ tokOf N linksFull (flatPlacesOf linksFull true) get
    (28 * g + 4) (k4PlaceAt g) (atK4_full g hg).1 (k04_lays_nothing g hg) a b w

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.k4LaysB
#print axioms OnBytes.Road.K4.k04_lays_nothing
#print axioms OnBytes.Road.K4.k04_hE
