-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- A copy of a working file of this project that is not in this repository: as copied, it parted
-- from it in its import lines alone.
/-
Johnson/Desc/K1/Law/PubAtQuietLook.lean: four Bools of the lookups' layer
(Johnson/Desc/First/Look/K3FillCode.lean) over a step that leaves four readers of the state
(`LookSame`, Johnson/Desc/K1/Law/LookSame.lean) and may write the state's part `tl`.

  `liveIs_quiet`: `liveIsC` is the same, where a link is open.
  `lookOut_quiet`: `lookOutC` at the lookup on the calls is the same.
  `linkFresh_quiet`, `lookIn_quiet`: the yes in front gives the yes behind UNDER ONE PREMISE ON THE
    STATE BEHIND: nothing is heard at the digits' seat there. The two Bools read that seat, and the
    step may write it.

What is not claimed. The premise: Johnson/Desc/K1/Law/QuietLook.lean says what the three quiet steps
lay at that seat. Nothing on `lookOutC` at the lookup on the digits. Nothing on soundness, on an
honest prover or on hiding.

-/
import Johnson.Desc.First.Look.K3FillCode
import Johnson.Desc.K1.Law.LookSame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look (K3Data liveIsC linkFreshC lookInC lookOutC placeAt)
open VerifiableInference.Desc.K3 (k3OnIn k3OnOut heardAt)

/-- The parameters of a lookup say which of the two it is. -/
theorem placeAt_digits {X : Verify.Public} {i : Nat} {dg : Bool} {p : First.Look.P}
    (h : placeAt X i dg = some p) : p.digits = dg := by
  unfold placeAt at h
  obtain ⟨x, _, rfl⟩ := Option.map_eq_some_iff.1 h
  rfl

/-- **"frame.liveIs".** -/
theorem liveIs_quiet (d : K3Data) {s s' : S} (h : LookSame s s') (hl : s.link?.isSome = true) :
    liveIsC d s' = liveIsC d s := by
  obtain ⟨L, hL⟩ := Option.isSome_iff_exists.1 hl
  unfold liveIsC S.live
  rw [h.link, hL]

/-- **linkFresh.** -/
theorem linkFresh_quiet (d : K3Data) (m : Nat) {s s' : S} (h : LookSame s s')
    (hh : (s'.tl?.bind (·.heard)).isNone = true) (h0 : linkFreshC d m s = true) :
    linkFreshC d m s' = true := by
  unfold linkFreshC at h0 ⊢
  rw [h.link, hh]
  simp only [Bool.and_eq_true] at h0
  simpa using h0.2

/-- The lookup's condition behind its block, at the lookup on the calls. -/
theorem k3OnOut_quiet (p : First.Look.P) {s s' : S} (h : LookSame s s') (hp : p.digits = false) :
    k3OnOut p s' = k3OnOut p s := by
  unfold k3OnOut heardAt
  rw [hp, h.fork]
  simp only [Bool.false_eq_true, if_false]
  rw [h.look]

/-- **lookOut**, at the lookup on the calls. -/
theorem lookOut_quiet (d : K3Data) (m : Nat) {s s' : S} (h : LookSame s s') :
    lookOutC d m false s' = lookOutC d m false s := by
  unfold lookOutC
  cases hp : placeAt d.X m false with
  | none => rfl
  | some p =>
    show k3OnOut p s' = k3OnOut p s
    exact k3OnOut_quiet p h (placeAt_digits hp)

/-- The lookup's condition in front of its block. -/
theorem k3OnIn_quiet (p : First.Look.P) {s s' : S} (h : LookSame s s')
    (hh : (s'.tl?.bind (·.heard)).isNone = true) (h0 : k3OnIn p s = true) :
    k3OnIn p s' = true := by
  have hq : (heardAt p.digits s).isNone = true → (heardAt p.digits s').isNone = true := by
    unfold heardAt
    cases p.digits with
    | true => exact fun _ => hh
    | false =>
      simp only [Bool.false_eq_true, if_false]
      rw [h.look]
      exact id
  unfold k3OnIn at h0 ⊢
  rw [h.fork, h.owed]
  cases hs : p.shape with
  | none => rw [hs] at h0; cases h0
  | some hsh =>
    rw [hs] at h0
    simp only [Bool.and_eq_true] at h0 ⊢
    exact ⟨⟨hq h0.1.1, h0.1.2⟩, h0.2⟩

/-- **lookIn.** -/
theorem lookIn_quiet (d : K3Data) (m : Nat) (dg : Bool) {s s' : S} (h : LookSame s s')
    (hh : (s'.tl?.bind (·.heard)).isNone = true) (h0 : lookInC d m dg s = true) :
    lookInC d m dg s' = true := by
  unfold lookInC at h0 ⊢
  cases hp : placeAt d.X m dg with
  | none => rw [hp] at h0; cases h0
  | some p =>
    rw [hp] at h0
    simp only [Option.any_some, Bool.and_eq_true] at h0 ⊢
    rw [h.link]
    exact ⟨k3OnIn_quiet p h hh h0.1, h0.2⟩

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.liveIs_quiet
#print axioms VerifiableInference.Desc.K1.linkFresh_quiet
#print axioms VerifiableInference.Desc.K1.lookOut_quiet
#print axioms VerifiableInference.Desc.K1.lookIn_quiet
