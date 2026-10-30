-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/ShapesAtRecord.lean: what a sending of kind K1 does to the list of the shapes of
the statement's oracle messages: it appends the shapes of the place's notices, in their order, and
turns no older one. Statements with their proofs.

  shapesIn St        the shapes of St's oracle messages, in their order.
  coreStill_shapes   the eight plain functions of the ground that write the statement alone leave
                     that list: one member of CoreStill (Johnson/Desc/CoreKeeps.lean).
  recvP_shapesIn       the receiving appends the notices' shapes.
  (shapesOf P, the shapes of the place's notices: Johnson/Desc/K1/Law/Writes3.lean.)
  decideSend_shapesIn  so does the kind's decision.
  sendAtS_shapesIn, commitAtS_shapesIn, firstAtS_shapesIn   so do the kind's three blocks at the
                     first chain's record.
  prefix_ride        "the list is the first of M" rides over such an appending, where M goes on with
                     what is appended.
What is not claimed. That a plan's list goes on so at a block's place. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.SeatedAtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Ground
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain

/-- The shapes of the statement's oracle messages, in their order. -/
def shapesIn (St : Statement) : List OracleShape := St.oracles.toList.map (·.shape)

/-- A turn of one message that leaves its shape leaves the list. -/
theorem shapes_modify (A : Array OnBytes.Oracle) (o : Nat) (f : OnBytes.Oracle → OnBytes.Oracle)
    (hf : ∀ x, (f x).shape = x.shape) :
    (A.modify o f).toList.map (·.shape) = A.toList.map (·.shape) := by
  apply List.ext_getElem?
  intro i
  simp only [List.getElem?_map, Array.getElem?_toList, Array.getElem?_modify]
  by_cases e : o = i
  · simp only [e, if_true, Option.map_map]
    cases A[i]? with
    | none => rfl
    | some x => exact congrArg some (hf x)
  · simp only [e, if_false]

/-- **The eight leave the list of the messages' shapes.** -/
theorem coreStill_shapes : CoreStill fun a b => shapesIn b.st = shapesIn a.st where
  refl := fun _ => rfl
  trans := fun a b => b.trans a
  newGroup := by
    intro L d d' code maskCode n h
    unfold newGroupP at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      rfl
    · cases h
  admit := by
    intro L d d' o rows h
    unfold admitP at h
    split at h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨x, -, places, -, rfl⟩ := h
      exact shapes_modify _ _ _ fun _ => rfl
    · cases h
  join := by
    intro L d d' g o kept h
    unfold joinP at h
    split at h
    · obtain ⟨G, -, rfl⟩ := Option.map_eq_some_iff.1 h
      exact shapes_modify _ _ _ fun _ => rfl
    · cases h
  addRow := by
    intro L d d' g row h
    unfold addRowP at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      rfl
    · cases h
  takeMask := by
    intro L d d' o n h
    unfold takeMaskP at h
    split at h
    · obtain ⟨l, -, e⟩ := Option.map_eq_some_iff.1 h
      obtain rfl : _ = d' := congrArg Prod.snd e
      exact shapes_modify _ _ _ fun _ => rfl
    · cases h
  closeLedger := by
    intro L d d' o h
    unfold closeLedgerP at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact shapes_modify _ _ _ fun _ => rfl
    · cases h
  spendAsMask := by
    intro L d d' o h
    unfold spendAsMaskP at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact shapes_modify _ _ _ fun _ => rfl
    · cases h
  elsewhere := by
    intro L d d' mine other theirs h
    unfold elsewhereP at h
    split at h
    · obtain ⟨y, -, rfl⟩ := Option.map_eq_some_iff.1 h
      exact shapes_modify _ _ _ fun _ => rfl
    · cases h

end VerifiableInference.Desc.Ground

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Ground (coreOf shapesIn coreStill_shapes)

variable {L Cl : Type}

/-- **The receiving appends the notices' shapes.** -/
theorem recvP_shapesIn (ft : Nat) (d d₁ : DState L) (sent : Array OracleNotice) (ids : Array Nat)
    (h : Ground.recvP ft d sent = some (ids, d₁)) :
    shapesIn d₁.st = shapesIn d.st ++ sent.toList.map (·.shape) := by
  obtain ⟨_, lay, _, _, rfl⟩ := (recvP_iff ft d d₁ sent ids).1 h
  show ((d.st.oracles ++ sent.map fun n => ({ shape := n.shape } : OnBytes.Oracle)).toList.map
    (·.shape)) = _
  simp [shapesIn, Function.comp_def]

/-- **The kind's decision.** -/
theorem decideSend_shapesIn (P : Par) (owed : Option Nat) (d d' : DState L) (r₁ r₂ : Fmt.RoundView)
    (ids : Array Nat) (h : decideSend P owed d [r₁, r₂] = .ok (ids, d')) :
    shapesIn d'.st = shapesIn d.st ++ shapesOf P := by
  obtain ⟨d₁, hr, hl⟩ := decideSend_parts P owed d d' r₁ r₂ ids h
  have e : shapesIn d'.st = shapesIn d₁.st :=
    RelCore.laid_keeps coreStill_shapes _ _ _ _ _ _ (layRows_ok _ _ _ _ _ _ hl)
  rw [e]
  exact recvP_shapesIn _ d d₁ P.sent ids hr

/-- **W's sending.** -/
theorem sendAtS_shapesIn (P : Par) (s s' : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (sendAtS P : Block S Cl).decide s [r₁, r₂] gs = .ok s') :
    shapesIn s'.st = shapesIn s.st ++ shapesOf P := by
  unfold sendAtS at h
  dsimp only at h
  split at h
  · split at h
    · obtain ⟨y, hy, rfl⟩ := (map_ok _ _ _).1 h
      obtain ⟨x, hx, rfl⟩ := (map_ok _ _ _).1 hy
      exact decideSend_shapesIn P _ _ x.2 r₁ r₂ x.1 hx
    · cases h
  · cases h

/-- **A segment's later moment.** -/
theorem commitAtS_shapesIn (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (s s' : S)
    (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s [r₁, r₂] gs = .ok s') :
    shapesIn s'.st = shapesIn s.st ++ shapesOf P := by
  unfold commitAtS at h
  dsimp only at h
  split at h
  · obtain ⟨y, hy, rfl⟩ := (map_ok _ _ _).1 h
    obtain ⟨ids, d₁, f', h2, h3⟩ := commitOwn_ok P link moment arrays _ y _ gs hy
    have e : shapesIn y.held.w.st = shapesIn d₁.st :=
      RelCore.joinOwnP_keeps coreStill_shapes _ _ _ _ _ _ h3
    have hb := decideSend_shapesIn P _ _ d₁ r₁ r₂ ids h2
    rw [(putFork_st _ _).1, (putLink_st _ _).1]
    show shapesIn y.held.w.st = shapesIn s.st ++ shapesOf P
    rw [e]
    exact hb
  · cases h

/-- **The first segment's opening.** -/
theorem firstAtS_shapesIn (q : Params.First) (gp : GPar) (s s' : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (firstSegmentOpening q gp : Block S Cl).decide s [r₁, r₂] gs = .ok s') :
    shapesIn s'.st = shapesIn s.st ++ shapesOf (firstPar q gp) := by
  unfold firstSegmentOpening at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨c, d'⟩, h2, h⟩ := (bind_ok _ _ _).1 h
  obtain rfl := Except.ok.inj h
  obtain ⟨g, d₁, ids, d₂, h3, h4, f₁, own, mine, f₂, h5⟩ := firstOwn_ok _ _ _ _ _ _ _ h2
  have a : shapesIn d₁.st = _ := coreStill_shapes.newGroup _ d₁ _ _ g h3
  have b : shapesIn d'.st = shapesIn d₂.st :=
    RelCore.joinOwnP_keeps coreStill_shapes _ _ _ _ _ _ h5
  have hb := decideSend_shapesIn _ _ d₁ d₂ r₁ r₂ ids h4
  show shapesIn d'.st = shapesIn s.st ++ _
  rw [b, hb, a]
  rfl

/-- **"The list is the first of M" rides over an appending**, where M goes on with what is
appended. -/
theorem prefix_ride {α : Type} (M l l' x : List α) (h : l = M.take l.length)
    (hl : l.length ≤ M.length) (e : l' = l ++ x) (hx : (M.drop l.length).take x.length = x) :
    l' = M.take l'.length ∧ l'.length ≤ M.length := by
  subst e
  have hlen : x.length ≤ M.length - l.length := by
    have := congrArg List.length hx
    rw [List.length_take, List.length_drop] at this
    omega
  refine ⟨?_, by rw [List.length_append]; omega⟩
  rw [List.length_append, List.take_add, ← h, hx]

end VerifiableInference.Desc.K1
