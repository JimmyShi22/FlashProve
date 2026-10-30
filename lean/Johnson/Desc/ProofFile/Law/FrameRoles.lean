--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Law/FrameRoles.lean: which role `roleOf` (Frames1.lean) gives a place, from
the entry of the shape that stands at that place. Theorems only; no file of the description imports
this one.
Why. `chainBy` takes a segment's start, its end and what is joined after its first place from the
supplied blocks of the kind `frame` by their roles. To say which supplied block that is, one has to
evaluate `roleOf` at the block's place.
  `sameSpot`          the test by which `roleOf` looks a place up in the shape
  `roleOf_at`         `roleOf` at a place of a segment, as a function of the entry that is found
  `roleOf_lay_of`, `roleOf_clear_of`, `roleOf_after_of`, `roleOf_behind_of`   its value where the
                      entry bears the name of the segment's start, of its end, of the driver's own
                      block after the batching (no role), or is not of the kind `frame`
  `roleOf_behind_inv`   from the role "joined after the block named n, in segment l" back to the
                      place's segment and the entry's kind and name
  `role_eq_of_beq`, `role_beq_self`   the derived `==` on roles says yes just of equal roles
  `append_ne`         two strings with one front and different ends differ
  `flat_names`        the names and places of the three blocks that `Link.blocksInOrder` (Block.lean) adds
Not here: which entry of the description's shape stands at a given place. That needs the form of
the driver's flat list (Johnson/Desc/First/Driver/PlacesLaw.lean has its places, not its names).

-/
import Johnson.Desc.ProofFile.Law.PureMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Law
open VerifiableInference.Desc (Block Link KindName Place)

/-- The test by which `roleOf` looks the place `p` up in the shape: chain, segment and piece. -/
def sameSpot (p : Place) (b : String × Place) : Bool :=
  b.2.chain == p.chain && b.2.link == p.link && b.2.piece == p.piece

theorem append_ne {a x y : String} (h : x.toList ≠ y.toList) : a ++ x ≠ a ++ y := fun e =>
  h (by
    have e' := congrArg String.toList e
    rw [String.toList_append, String.toList_append] at e'
    exact List.append_cancel_left e')

theorem roleOf_at {shape : List (String × Place)} {p : Place} {e : String × Place} {l : Nat}
    (hf : shape.find? (sameSpot p) = some e) (hl : p.link = some l) :
    roleOf shape p =
      if e.2.kind != KindName.frame then .behind l e.1
      else if e.1 == s!"link {l}" ++ ": laid" then .lay l
      else if e.1 == s!"link {l}" ++ ": cleared" then .clear l
      else .stray := by
  unfold roleOf
  rw [show shape.find? (fun b => b.2.chain == p.chain && b.2.link == p.link &&
      b.2.piece == p.piece) = some e from hf, hl]

theorem roleOf_behind_of {shape : List (String × Place)} {p : Place} {e : String × Place} {l : Nat}
    (hf : shape.find? (sameSpot p) = some e) (hl : p.link = some l)
    (hk : e.2.kind ≠ KindName.frame) : roleOf shape p = .behind l e.1 := by
  rw [roleOf_at hf hl, if_pos (bne_iff_ne.2 hk)]

theorem roleOf_lay_of {shape : List (String × Place)} {p : Place} {e : String × Place} {l : Nat}
    (hf : shape.find? (sameSpot p) = some e) (hl : p.link = some l)
    (hk : e.2.kind = KindName.frame) (hn : e.1 = s!"link {l}" ++ ": laid") :
    roleOf shape p = .lay l := by
  rw [roleOf_at hf hl, hk, hn, if_neg (by simp), if_pos (by simp)]

theorem roleOf_clear_of {shape : List (String × Place)} {p : Place} {e : String × Place} {l : Nat}
    (hf : shape.find? (sameSpot p) = some e) (hl : p.link = some l)
    (hk : e.2.kind = KindName.frame) (hn : e.1 = s!"link {l}" ++ ": cleared") :
    roleOf shape p = .clear l := by
  have h1 : ¬ ((s!"link {l}" ++ ": cleared" == s!"link {l}" ++ ": laid") = true) := fun h =>
    append_ne (by decide) (beq_iff_eq.1 h)
  rw [roleOf_at hf hl, hk, hn, if_neg (by simp), if_neg h1, if_pos (by simp)]

/-- At the driver's own block after the batching no block can be supplied: the place has no role. -/
theorem roleOf_after_of {shape : List (String × Place)} {p : Place} {e : String × Place} {l : Nat}
    (hf : shape.find? (sameSpot p) = some e) (hl : p.link = some l)
    (hk : e.2.kind = KindName.frame) (hn : e.1 = s!"link {l}" ++ ": behind the batching") :
    roleOf shape p = .stray := by
  have h1 : ¬ ((s!"link {l}" ++ ": behind the batching" == s!"link {l}" ++ ": laid") = true) :=
    fun h => append_ne (by decide) (beq_iff_eq.1 h)
  have h2 : ¬ ((s!"link {l}" ++ ": behind the batching" == s!"link {l}" ++ ": cleared") = true) :=
    fun h => append_ne (by decide) (beq_iff_eq.1 h)
  rw [roleOf_at hf hl, hk, hn, if_neg (by simp), if_neg h1, if_neg h2]

/-! ### From the role back to the entry -/

theorem roleOf_none {shape : List (String × Place)} {p : Place}
    (hf : shape.find? (sameSpot p) = none) : roleOf shape p = .stray := by
  unfold roleOf
  rw [show shape.find? (fun b => b.2.chain == p.chain && b.2.link == p.link &&
      b.2.piece == p.piece) = none from hf]

theorem roleOf_outside {shape : List (String × Place)} {p : Place} {e : String × Place}
    (hf : shape.find? (sameSpot p) = some e) (hl : p.link = none) :
    roleOf shape p =
      if e.2.kind != KindName.frame then .stray
      else if e.1 == frontName then .front else .common := by
  unfold roleOf
  rw [show shape.find? (fun b => b.2.chain == p.chain && b.2.link == p.link &&
      b.2.piece == p.piece) = some e from hf, hl]

/-- A place has the role "joined after the block named `n`, in segment `l`" only if it lies in
segment `l` and the shape's entry at its chain, segment and piece is not of the kind `frame` and
bears the name `n`. -/
theorem roleOf_behind_inv {shape : List (String × Place)} {p : Place} {l : Nat} {n : String}
    (h : roleOf shape p = .behind l n) :
    p.link = some l ∧ ∃ e, shape.find? (sameSpot p) = some e ∧ e.2.kind ≠ KindName.frame ∧
      e.1 = n := by
  cases hf : shape.find? (sameSpot p) with
  | none =>
    rw [roleOf_none hf] at h
    cases h
  | some e =>
    match hl : p.link with
    | none =>
      rw [roleOf_outside hf hl] at h
      split at h
      · cases h
      · split at h <;> cases h
    | some l' =>
      rw [roleOf_at hf hl] at h
      split at h
      · rename_i hk
        injection h with h1 h2
        exact ⟨congrArg some h1, e, rfl, bne_iff_ne.1 hk, h2⟩
      · split at h
        · cases h
        · split at h <;> cases h

/-! ### The test of equality on roles -/

/-- `FrameRole` derives its `==`; `chainBy` and `lackingAt` look roles up by it. It says yes only of
equal roles. -/
theorem role_eq_of_beq {a b : FrameRole} (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;>
    first
      | rfl
      | exact Bool.noConfusion (show false = true from h)
      | (simp [BEq.beq, instBEqFrameRole.beq] at h
         simp [h])

theorem role_beq_self (a : FrameRole) : (a == a) = true := by
  cases a <;>
    first
      | rfl
      | simp [BEq.beq, instBEqFrameRole.beq]

/-- The three blocks that `Link.blocksInOrder` adds to a segment's own, by their names and places: the first
of the flat list; the one after the batching; the last. -/
theorem flat_names {σ Cl' : Type} (L : Link σ Cl') :
    ∃ (b0 b1 b2 : Block σ Cl'),
      L.blocksInOrder = b0 :: L.hear ++ [L.batch (VerifiableInference.Desc.claimsInBy L.each L.hear L.order),
                 b1] ++ L.close ++ [b2] ∧
      b0.name = L.name ++ ": laid" ∧ b0.place = ⟨L.chain, some L.number, 0, .frame⟩ ∧
      b1.name = L.name ++ ": behind the batching" ∧
      b1.place = ⟨L.chain, some L.number, L.hear.length + 2, .frame⟩ ∧
      b2.name = L.name ++ ": cleared" ∧
      b2.place = ⟨L.chain, some L.number, L.hear.length + L.close.length + 3, .frame⟩ :=
  ⟨_, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end ProofFile.Law

#print axioms ProofFile.Law.roleOf_at
#print axioms ProofFile.Law.roleOf_clear_of
#print axioms ProofFile.Law.roleOf_after_of
#print axioms ProofFile.Law.flat_names
#print axioms ProofFile.Law.roleOf_behind_inv
#print axioms ProofFile.Law.role_eq_of_beq
