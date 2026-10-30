-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- The guard around a part that reads the columns that the frame hands: what it leaves of the frame's sentences.
/-
Johnson/Desc/ProofFile/Honest/K12/SimO/Guard.lean: what `Part.needsField` (Honest/K12/FieldGuard.lean) leaves of the frame's sentences. Where the stand's field `opened` holds columns a guarded part plays as the bare part: so `exact` at the bare member gives
`exact` at the guarded member, at a condition that asks the field. General in the kind.

  `steps_needsField`     the steps of a guarded part are its own, guarded (`Step.guarded`, `tell_guarded`, `hear_guarded`, `play_guarded` are K12/FieldGuardLift.lean's, `hear_opened` Honest/WalkOpened.lean's)
  `Member.guarded`, `shows_guarded`   a member with the guard; what it shows
  `stopAt_needsField`    the stops are the bare part's
  `exact_guarded`        **`ExactMember` goes over to the guarded member**, at every condition that gives the bare one's and that the field holds columns
  `guardRow`, `membersOf_guardRow`   a list of parts with the guard at each; its members

Limits. At a stand whose field is none a guarded part errs: nothing here speaks of that. That the field holds columns at a run is the frame's. No property of a prover or of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.FieldGuardLift
import Johnson.Desc.ProofFile.Honest.Small.Field

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open ProofFile.Honest.Small (ExactMember)

variable {S Cl V W X Pb : Type}

/-- The steps of a guarded part are its own, guarded. -/
theorem steps_needsField (p : Part V W X) (name : String) (a : Addr)
    (rs : List (Fmt.DeclaredRound × List VerifiableInference.Desc.Oracle)) (v : Option V) (c : p.Coins) :
    (p.needsField).steps name a rs v c = (p.steps name a rs v c).map Step.guarded := by
  unfold Part.steps
  have hl : (p.needsField).moves.length = p.moves.length := needsField_length p
  rw [hl]
  show ((rs.zip (p.moves.map Move.needsField)).zipIdx.map _) = _
  rw [List.zip_map_right, List.zipIdx_map, List.map_map, List.map_map]
  rfl

/-- A member with the guard at its part. -/
def Member.guarded (u : Member V W X Pb) : Member V W X Pb := { u with part := u.part.needsField }

theorem shows_guarded (σ : Side S Cl V W X Pb) (φ : Face V W Pb) (u : Member V W X Pb) (c : u.part.Coins)
    (m : Mid W X) (ds : List Fmt.Drawn) (asks : List (List (List ℕ)))
    (cs : List VerifiableInference.Desc.OpenedColumn) (h : m.opened = some cs) :
    σ.shows φ u.guarded c m ds asks = σ.shows φ u c m ds asks := by
  unfold Side.shows
  show Option.map _ (play ((u.part.needsField).steps _ _ _ _ c) ds [] m).toOption = _
  rw [steps_needsField, play_guarded _ _ _ _ cs h]
  rfl

theorem stopAt_needsField (p : Part V W X) (v : Option V) (loc ds : List Fmt.Drawn) :
    (p.needsField).stopAt v loc ds = p.stopAt v loc ds := by
  unfold Part.stopAt
  rw [needsField_length]
  rfl

/-- **`exact` at the guarded member.** -/
theorem exact_guarded {φ : Face V W Pb} {σ : Side S Cl V W X Pb} {chain firstTree : ℕ}
    {On On' : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop}
    {bud : ℕ → List Fmt.Drawn → List (List (List ℕ)) → Prop} {u : Member V W X Pb}
    (hOn : ∀ (ca : CsAll u.part.carries) m front, On' u.guarded ca m front →
      On u ca m front ∧ ∃ cs, m.opened = some cs)
    (E : ExactMember φ σ chain firstTree On bud u) :
    ExactMember φ σ chain firstTree On' bud u.guarded := by
  intro ca m front ds asks h1 h2 h3 h4 h5 h6
  obtain ⟨h0, cs, hc⟩ := hOn ca m front h1
  have h6' : u.part.stopAt (φ.sees m.st.input) m.loc ds ≠ some .hid := by
    have e := stopAt_needsField u.part (φ.sees m.st.input) m.loc ds
    intro hh
    exact h6 (e.trans hh)
  have L := E ca m front ds asks h0 h2 h3 h4 h5 h6'
  have e : (fun c : Cs u.part.takes × CsAll u.part.spends => σ.shows φ u.guarded (c.1, c.2, ca) m ds asks) =
      fun c => σ.shows φ u (c.1, c.2, ca) m ds asks :=
    funext fun c => shows_guarded σ φ u (c.1, c.2, ca) m ds asks cs hc
  show (Prob.unif (Cs u.part.takes × CsAll u.part.spends)).map
      (fun c => σ.shows φ u.guarded (c.1, c.2, ca) m ds asks) = _
  rw [e]
  exact L

/-- A list of parts with the guard at each. -/
def guardRow (row : List (Part V W X × Sim Pb)) : List (Part V W X × Sim Pb) :=
  row.map fun x => (x.1.needsField, x.2)

theorem membersOf_guardRow : ∀ (row : List (Part V W X × Sim Pb)) (j : ℕ)
    (rs : List (Fmt.DeclaredRound × List VerifiableInference.Desc.Oracle)),
    membersOf (guardRow row) j rs = (membersOf row j rs).map Member.guarded
  | [], _, _ => rfl
  | x :: l, j, rs => by
    show (⟨j, rs.take (x.1.needsField).moves.length, x.1.needsField, x.2⟩ : Member V W X Pb) ::
        membersOf (guardRow l) (j + 1) (rs.drop (x.1.needsField).moves.length) =
      Member.guarded ⟨j, rs.take x.1.moves.length, x.1, x.2⟩ ::
        (membersOf l (j + 1) (rs.drop x.1.moves.length)).map Member.guarded
    rw [needsField_length, membersOf_guardRow l]
    rfl

end ProofFile.Honest

#print axioms ProofFile.Honest.steps_needsField
#print axioms ProofFile.Honest.Member.guarded
#print axioms ProofFile.Honest.shows_guarded
#print axioms ProofFile.Honest.stopAt_needsField
#print axioms ProofFile.Honest.exact_guarded
#print axioms ProofFile.Honest.guardRow
#print axioms ProofFile.Honest.membersOf_guardRow
