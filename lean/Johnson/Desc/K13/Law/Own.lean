-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/Own.lean: which number kind K13's text behind W's commitment lays as the number
of the request's own group (`LinFirst.own`). The statement, a planted copy that fails it, and the
proofs.

The text (Johnson/Desc/K13/Text.lean: `rows`) makes the own group itself, by the ground's
`newGroupP`, and lays the number that this call returns. So the number is read off the record, not
off the plan: it is the number of groups that the statement in front has, and behind the text the
own group is the last one.
Main names:
  `OwnLaw f`: the form of the law, of any text f in the place of `rows`.
  `rowsPlant`: a copy that lays the next number.
  `Spec.plant_fails`: wherever `rows` answers at all, the planted copy does not meet the form.
  `rows_own`: the text meets it. `rows_own_at`: so where the statement in front has as many groups
    as a plan says, the text lays the plan's number.
  `rowsB_own`: the same of the block, at the first chain's state.
Used of `verify-on-bytes`: `withRow`, `withMessageInGroup`, as pure functions. Of the ground: `newGroupP`,
`joinP`, `addRowsP`.

What is not claimed. That the statement in front of the text has as many groups as a plan says: no
plan names that number here, and no block in front is shown to keep such a count. That `rows`
answers somewhere: runs on honest files show it, not this file. Nothing on soundness.

-/
import Johnson.Desc.K13.Law.AtM4

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Slice
open OnBytes.Params (LinShape)
open VerifiableInference.Desc.Ground (newGroupP joinP addRowsP)
open VerifiableInference.Desc.First (S)

/-- **The form of the law**: the number laid is the number of groups of the statement in front, and
behind the text that group is the last one. -/
def OwnLaw (f : LinShape → LinClaim → Array ℕ → St → Ans (LinFirst × St)) : Prop :=
  ∀ Sh claim ids d o, f Sh claim ids d = .ok o →
    o.1.own = d.st.groups.size ∧ o.1.own + 1 = o.2.st.groups.size

/-- A planted copy: as `rows`, but the next number is laid. -/
def rowsPlant (Sh : LinShape) (claim : LinClaim) (ids : Array ℕ) (d : St) : Ans (LinFirst × St) :=
  (rows Sh claim ids d).map fun o => ({ o.1 with own := o.1.own + 1 }, o.2)

/-- Wherever `rows` answers at all, the planted copy does not meet the form. -/
def Spec.plant_fails : Prop :=
  ∀ Sh claim ids d o, rows Sh claim ids d = .ok o → ¬ OwnLaw rowsPlant

/-- The text meets the form. -/
def Spec.rows_own : Prop := OwnLaw rows

/-- A new group gets the number of groups so far, and is one group more. -/
theorem newGroup_size {d : St} {c z : ℕ} {b : ℕ × St} (h : newGroupP d c z = some b) :
    b.1 = d.st.groups.size ∧ b.2.st.groups.size = d.st.groups.size + 1 := by
  unfold newGroupP at h
  split at h
  · obtain rfl := Option.some.inj h
    exact ⟨rfl, Array.size_push _⟩
  · cases h

/-- A joining leaves the number of groups. -/
theorem join_size {d d' : St} {g o : ℕ} {kept : Bool} (h : joinP d g o kept = some d') :
    d'.st.groups.size = d.st.groups.size := by
  unfold joinP at h
  split at h
  · cases hG : d.st.groups[g]? with
    | none =>
      rw [hG] at h
      cases h
    | some G =>
      rw [hG] at h
      obtain rfl := Option.some.inj h
      exact Array.size_modify
  · cases h

/-- So do joinings in a row. -/
theorem joinAll_size (g : ℕ) : ∀ (l : List ℕ) (d d' : St), joinAll g l d = .ok d' →
    d'.st.groups.size = d.st.groups.size
  | [], d, d', h => by rw [pure_ok.1 h]
  | o :: l, d, d', h => by
    simp only [joinAll, bind_ok, there_ok] at h
    obtain ⟨d₁, h1, h2⟩ := h
    rw [joinAll_size g l d₁ d' h2, join_size h1]

/-- **The text meets the form.** -/
theorem rows_own : Spec.rows_own := by
  intro Sh claim ids d o h
  simp only [rows_is, bind_ok, there_ok, pure_ok] at h
  obtain ⟨w, _, b, hb, d₁, h1, d₂, h2, split, _, d₃, h3, mask, _, row, _, d₄, h4, rfl⟩ := h
  obtain ⟨hn, hs⟩ := newGroup_size hb
  obtain ⟨_, _, _, hst⟩ := addRows_one h4
  have e2 : d₂.st.groups.size = d.st.groups.size + 1 := by
    rw [join_size h2, joinAll_size _ _ _ _ h1, hs]
  have e3 : d₃.st.groups.size = d.st.groups.size + 1 := by
    split at h3
    · rw [join_size h3, e2]
    · rw [← Option.some.inj h3, e2]
  have e4 : d₄.st.groups.size = d.st.groups.size + 1 := by
    rw [hst]
    exact Array.size_modify.trans e3
  exact ⟨hn, by show b.1 + 1 = d₄.st.groups.size; rw [hn, e4]⟩

/-- Wherever `rows` answers at all, the planted copy does not meet the form. -/
theorem plant_fails : Spec.plant_fails := by
  intro Sh claim ids d o h hlaw
  have h1 := (rows_own Sh claim ids d o h).1
  have hp : rowsPlant Sh claim ids d = .ok ({ o.1 with own := o.1.own + 1 }, o.2) := by
    unfold rowsPlant
    rw [h]
    rfl
  have h2 : o.1.own + 1 = d.st.groups.size := (hlaw _ _ _ _ _ hp).1
  omega

/-- Where the statement in front has as many groups as a plan says, the text lays the plan's number.
-/
theorem rows_own_at {Sh : LinShape} {claim : LinClaim} {ids : Array ℕ} {d : St}
    {o : LinFirst × St} (n : ℕ) (hn : d.st.groups.size = n) (h : rows Sh claim ids d = .ok o) :
    o.1.own = n := by
  rw [← hn]
  exact (rows_own Sh claim ids d o h).1

/-- **The same of the block**, at the first chain's state. -/
theorem rowsB_own {Cl : Type} {P : Where} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (rowsB (Cl := Cl) atS P).decide s rs gs = .ok s') :
    ∃ l, linAt s' = some l ∧ l.own = s.st.groups.size ∧ l.own + 1 = s'.st.groups.size := by
  obtain ⟨m₀, l, o, owed, _, _, hrows, rfl⟩ := rowsB_at h
  obtain ⟨h1, h2⟩ := rows_own _ _ _ _ _ hrows
  exact ⟨o.1, rfl, h1, h2⟩

end VerifiableInference.Desc.K13.Law
