-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K05KindR.lean: kind K5: THE FORM OF THE KIND's SHARE OF THE CHAIN OF PROMISES (KindTiedR, Johnson/Desc/Sound/TiedR.lean) AT THE FULL WRITTEN LIST: it is twelve ties, one at each
place of the kind; and at these places the table's one extractor lays nothing.

Main names:
  `k5_places_full`: in the driver's flat list of places at the full size the places of the kind K5 are just the twelve numbers 14 (2 g + 1) + 4, g < 12, each ⟨1, some (2 g + 1), 3, .K5⟩: one decision of Lean's kernel on the
    written list. `k5_places_bite`: the negative test: the like sentence with eleven groups is false.
  `kindTiedR_of_places`: **TiedAtR at each of the twelve numbers gives KindTiedR … .K5**: general in the numbers, the filling, the condition beside the promise, the extractor and the list of pieces.
  `kindTiedR_to_places`: the converse: so the two say the same.
  `extQAt_k5`: at a place of the kind K5 the table's extractor (extQAt, Johnson/Desc/Sound/BordersFill.lean) is the identity on the witness: the kind's row lays no seat, no pad and no token: at every list of places.
Is it empty here? kindTiedR_of_places' premise is shown at nothing here. A rule over letters.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.TiedR
import Johnson.Desc.Sound.BordersFill

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Door
open OnBytes.Maker OnBytes.Flat KObj Johnson.Pack
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound

/-- The segments' sorts at the full size, written out. -/
abbrev LFullK : List ModelPart := (List.range 12).flatMap (fun _ => [ModelPart.layers, ModelPart.attention]) ++ [.head]
/-- The driver's flat list of places at it. -/
abbrev PFullK : List Place := flatPlacesOf LFullK true

/-- The test: every place of the kind stands at one of n numbers. -/
def k5AllB (n : Nat) : Bool :=
  (List.range PFullK.length).all fun i =>
    match PFullK[i]? with
    | some a => a.kind != KindName.K5 ||
      (List.range n).any fun g => i == 14 * (2 * g + 1) + 4 && decide (a = ⟨1, some (2 * g + 1), 3, .K5⟩)
    | none => true

set_option maxRecDepth 100000 in
theorem k5AllB_full : k5AllB 12 = true := by decide +kernel

set_option maxRecDepth 100000 in
/-- The negative test. -/
theorem k5_places_bite : k5AllB 11 = false := by decide +kernel

/-- **Where the kind stands in the full list of places.** -/
theorem k5_places_full (i : ℕ) (a : Place) (ha : PFullK[i]? = some a) (hk : a.kind = KindName.K5) :
    ∃ g, g < 12 ∧ i = 14 * (2 * g + 1) + 4 ∧ a = ⟨1, some (2 * g + 1), 3, .K5⟩ := by
  have hi : i < PFullK.length := (List.getElem?_eq_some_iff.1 ha).1
  have h := List.all_eq_true.1 k5AllB_full i (List.mem_range.2 hi)
  rw [ha] at h
  have h2 : ((List.range 12).any fun g =>
      i == 14 * (2 * g + 1) + 4 && decide (a = ⟨1, some (2 * g + 1), 3, .K5⟩)) = true := by
    rcases (Bool.or_eq_true _ _).mp h with h1 | h1
    · rw [hk] at h1
      exact absurd h1 (by decide)
    · exact h1
  obtain ⟨g, hg, h3⟩ := List.any_eq_true.1 h2
  obtain ⟨h4, h5⟩ := (Bool.and_eq_true _ _).mp h3
  exact ⟨g, List.mem_range.1 hg, by simpa using h4, by simpa using h5⟩

section
variable {Cl P W : Type} {C : CK} {Fr : Frame} (N : Numbers) (Mg : Meaning P W)
  (Rch : ℕ → (P × First.S) × Fr.E.Str → Prop)
  (E : ℕ → (P × First.S) × Fr.E.Str → (P × First.S) × Fr.E.Str → W → W)
  (l : List (Piece C Fr (P × First.S) Cl W))

/-- **The kind's share is twelve ties.** -/
theorem kindTiedR_of_places
    (H : ∀ g, g < 12 → ∀ q, l[14 * (2 * g + 1) + 4]? = some q →
      TiedAtR N Mg LFullK PFullK (fun a => a) Rch (14 * (2 * g + 1) + 4) (q.withMap (E (14 * (2 * g + 1) + 4)))) :
    KindTiedR N Mg LFullK PFullK Rch E l KindName.K5 := by
  intro i q a hq ha hk
  obtain ⟨g, hg, rfl, -⟩ := k5_places_full i a ha hk
  exact H g hg q hq

set_option maxRecDepth 100000 in
/-- The twelve numbers are places of the kind. -/
theorem k5_at_full : ∀ g, g < 12 → PFullK[14 * (2 * g + 1) + 4]? = some ⟨1, some (2 * g + 1), 3, .K5⟩ := by decide +kernel

/-- The converse. -/
theorem kindTiedR_to_places (H : KindTiedR N Mg LFullK PFullK Rch E l KindName.K5) :
    ∀ g, g < 12 → ∀ q, l[14 * (2 * g + 1) + 4]? = some q →
      TiedAtR N Mg LFullK PFullK (fun a => a) Rch (14 * (2 * g + 1) + 4) (q.withMap (E (14 * (2 * g + 1) + 4))) :=
  fun g hg q hq => H _ q _ hq (k5_at_full g hg) rfl

end

section
variable (cs : OnBytes.Codes) {Xi P Cells Tok : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ)
  (smp : P × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (ms : List Mem) (decT : (ℕ → Option (ℕ × List UInt64)) → P × First.S → Option Cells) (c₀ : Cells) (tokOf : P × First.S → Tok)

/-- **At a place of the kind the table's extractor lays nothing.** -/
theorem extQAt_k5 {A : Type} {Fr : Frame} (N : Numbers) (links : List ModelPart) (ps : List Place) (get : A → P × First.S) (k : ℕ) {p : Place}
    (hp : ps[k]? = some p) (hk : p.kind = KindName.K5) (a b : A × Fr.E.Str) (w : Wit Cells Tok MsgT) :
    extQAt cs G arr smp ms decT c₀ tokOf N links ps get k a b w = w := by
  have h1 : laysSeats N links p = [] := by
    unfold laysSeats
    rw [hk]
    split <;> rfl
  have h2 : laysPads N links p = [] := by
    unfold laysPads
    rw [hk]
    split <;> rfl
  have h3 : laysTok links p = false := by
    unfold laysTok
    rw [hk]
    simp
  unfold extQAt
  rw [hp]
  show extQ cs G arr smp ms decT c₀ tokOf N links p _ _ _ w = w
  unfold extQ mineAt minePadAt
  rw [h1, h2, h3]
  simp [extAt_none]

end

end H2K5.Door

#print axioms H2K5.Door.k5AllB_full
#print axioms H2K5.Door.k5_places_bite
#print axioms H2K5.Door.k5_places_full
#print axioms H2K5.Door.kindTiedR_of_places
#print axioms H2K5.Door.k5_at_full
#print axioms H2K5.Door.kindTiedR_to_places
#print axioms H2K5.Door.extQAt_k5
