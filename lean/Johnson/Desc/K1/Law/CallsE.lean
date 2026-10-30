-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/CallsE.lean: K01_law: THE TOP's BINDER hE, PAID AT THE TABLE's OWN EXTRACTOR: at E := extQAt (Johnson/Desc/Sound/BordersFill.lean) the map at each of the fifty later places is the identity: by extQ_id, where the table's row
lays nothing: k01_later_places · laysNone_full [both by the kernel: Johnson/Desc/K1/Law/RowLFull.lean]. On the pattern of extQAt_355 (Johnson/Desc/AtSeats/K13LawTop.lean).
  place_fifty · lays_fifty · extQAt_fifty
Nothing on soundness.
-/
import Johnson.Desc.K1.Law.RowLFull
import Johnson.Desc.Sound.BordersFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Maker Johnson.Pack
open VerifiableInference.Desc.First (S Numbers flatPlacesOf)
open VerifiableInference.Desc.Sound (Frame Mem MsgT linksFull extQAt extQ_id)
open IM (k1Ix k1PlaceL)

theorem place_fifty (l : ℕ) (hl : l < 25) (d : Bool) :
    (flatPlacesOf linksFull true)[14 * l + k1Ix l d + 2]? = some (k1PlaceL l d) :=
  of_decide_eq_true (List.all_eq_true.1
    (List.all_eq_true.1 k01_later_places l (List.mem_range.2 hl)) d (by cases d <;> simp))

theorem lays_fifty (l : ℕ) (hl : l < 25) (d : Bool) :
    (First.rowOf linksFull (k1PlaceL l d)).lays = false := by
  have h := List.all_eq_true.1
    (List.all_eq_true.1 laysNone_full l (List.mem_range.2 hl)) d (by cases d <;> simp)
  simpa using (Bool.and_eq_true_iff.1 h).1

section
variable (cs : OnBytes.Codes) {A Xi Pp Cells Tok : Type} {Fr : Frame} (G : FileDescription Xi)
  (arr : ℕ → ℕ → ℕ)
  (smp : Pp × S → (s : Sound.Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells) (c₀ : Cells)
  (tokOf : Pp × S → Tok)

/-- **The table's own extractor lays nothing at K1's fifty later rows.** -/
theorem extQAt_fifty (N : Numbers) (get : A → Pp × S) (l : ℕ) (hl : l < 25) (d : Bool)
    (a b : A × Fr.E.Str) (w : Desc.Wit Cells Tok MsgT) :
    extQAt cs G arr smp ms decT c₀ tokOf N linksFull (flatPlacesOf linksFull true) get
      (14 * l + k1Ix l d + 2) a b w = w := by
  unfold extQAt
  rw [place_fifty l hl d]
  exact extQ_id cs G arr smp ms decT c₀ tokOf N linksFull _ (lays_fifty l hl d) _ _ _ w

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.extQAt_fifty
