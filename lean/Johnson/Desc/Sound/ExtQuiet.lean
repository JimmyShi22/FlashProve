-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/ExtQuiet.lean: AT A ROW OF THE FIRST CHAIN'S TABLE THAT LAYS NOTHING THE TABLE'S
EXTRACTOR IS THE IDENTITY. Three lemmas. No protocol's soundness is said.

What is said. `extQAt_quiet`: where the place at block number k lays no seat, no pad and not the
token (three evaluations on the table: `laysSeats`, `laysPads`, `laysTok`), `extQAt … k a b w = w`.
It is the premise hE of `rowOfPart` (RowOfPart.lean).

(Its kin: `extQ_id`, BordersFill.lean: the same at one place, under "the row's mark lays is off".)
`lays_nothing`: a place of any kind but K2, K7, K10, K12 is such a place. `lays_nothing_K6`: so
K6's.

Limits. In `extQAt_quiet` the three evaluations are premises. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.BordersFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Cb Johnson.Pack OnBytes.Slice
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc.First (ModelPart Numbers laysSeats laysPads laysTok)

/-- **A row that lays nothing leaves the witness as it is.** -/
theorem extQAt_quiet (cs : OnBytes.Codes) {Xi P Cells Tok A : Type} (G : FileDescription Xi)
    (arr : ℕ → ℕ → ℕ)
    (smp : P × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → P × First.S → Option Cells)
    (c₀ : Cells) (tokOf : P × First.S → Tok) {Fr : Frame} (N : Numbers) (links : List ModelPart)
    (ps : List Place) (get : A → P × First.S) (k : ℕ) (p : Place) (hp : ps[k]? = some p)
    (h1 : laysSeats N links p = []) (h2 : laysPads N links p = [])
    (h3 : laysTok links p = false) (a b : A × Fr.E.Str) (w : Wit Cells Tok MsgT) :
    extQAt cs G arr smp ms decT c₀ tokOf N links ps get k a b w = w := by
  unfold extQAt
  rw [hp]
  show extQ cs G arr smp ms decT c₀ tokOf N links p (get a.1) (strsOf Fr a.2) (some (get b.1)) w = w
  unfold extQ mineAt minePadAt
  rw [h1, h2, h3]
  have e : (ms.filter fun x => ([] : List (ℕ × ℕ)).contains (x.1.seat x.2)) = [] := by
    apply List.filter_eq_nil_iff.2
    intro x _
    simp
  rw [e]
  exact extAt_none cs G arr smp decT c₀ _ _ w

/-- **A place of any kind but the four that lay (K2: pads; K7: the token; K10, K12: seats) lays
nothing.** -/
theorem lays_nothing (N : Numbers) (links : List ModelPart) (p : Place) (h2 : p.kind ≠ .K2)
    (h7 : p.kind ≠ .K7) (h10 : p.kind ≠ .K10) (h12 : p.kind ≠ .K12) :
    laysSeats N links p = [] ∧ laysPads N links p = [] ∧ laysTok links p = false := by
  refine ⟨?_, ?_, ?_⟩
  · unfold laysSeats
    split
    · rfl
    · split
      · exact absurd ‹p.kind = .K10› h10
      · exact absurd ‹p.kind = .K12› h12
      · rfl
  · unfold laysPads
    split
    · rfl
    · split
      · exact absurd ‹p.kind = .K2› h2
      · rfl
  · unfold laysTok
    rw [beq_eq_false_iff_ne.2 h7, Bool.and_false]

/-- A place of the kind K6 lays nothing. -/
theorem lays_nothing_K6 (N : Numbers) (links : List ModelPart) (p : Place) (h : p.kind = .K6) :
    laysSeats N links p = [] ∧ laysPads N links p = [] ∧ laysTok links p = false :=
  lays_nothing N links p (by rw [h]; decide) (by rw [h]; decide) (by rw [h]; decide)
    (by rw [h]; decide)

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.extQAt_quiet
#print axioms VerifiableInference.Desc.Sound.lays_nothing
#print axioms VerifiableInference.Desc.Sound.lays_nothing_K6
