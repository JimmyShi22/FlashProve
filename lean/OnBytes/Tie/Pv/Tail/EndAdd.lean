-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndAdd.lean: the shapes of the arrays that the smallness test adds to a
sub-proof's list (`HTailF2.addTreesF`, OnBytes/Model/Tail.lean).

Definitions, and theorems with their proofs. The routine adds the arrays one after the other at the
end of the list and compares each array's number with the number that the plan of the shapes holds
for it. So where it returns, the array under each such number is the one that was added for it.

Main names:
  `Has F t s`: the state has array t, and its kind and sizes are s (`shapeAt`,
    OnBytes/Tie/Pv/Tail/EndCoef.lean).
  `Grows F G`: every array that F has, G has, with the same kind and sizes.
  `t2AddN_ok`, `t2AddP_ok`: one array is added at the end of the list.
  `forIn_exc`: a loop that can refuse: a property of (the members done so far, the loop's state)
    that every turn that does not refuse carries on.
  `addTreesF_frame`: where the routine returns: each table's vector is a table of one row, with as
    many columns as the caller's list says, and one virtual row (`UShape`,
    OnBytes/Tie/Pv/Tail/EndFrame.lean); the array of the digits has tau rows, 2 mz columns and two
    virtual rows for each block, and two; the array of the planes has 32 rows and three virtual
    rows; and the list has grown.

Limits: nothing on the symbol arrays, on the second list that the routine keeps, or on the record
that it returns (OnBytes/Tie/Pv/Tail/EndSame.lean has `addTreesF_fits`). Nothing on later steps
(OnBytes/Tie/Pv/Tail/EndKeep.lean).


-/
import OnBytes.Tie.Pv.Tail.EndKeep
import OnBytes.Tie.Pv.Tail.EndSame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail.Port

/-- The state has array t, and its kind and sizes are s. -/
def Has (F : Fork) (t : Nat) (s : HKind × Nat × Nat × Nat) : Prop :=
  t < F.trees.size ∧ shapeAt F t = s

/-- Every array that F has, G has, with the same kind and sizes. -/
def Grows (F G : Fork) : Prop := ∀ t s, Has F t s → Has G t s

/-- Every list has grown from itself. -/
theorem Grows.refl (F : Fork) : Grows F F := fun _ _ h => h

/-- `Grows` goes through a state between. -/
theorem Grows.trans {F G H : Fork} (h : Grows F G) (h' : Grows G H) : Grows F H :=
  fun t s x => h' t s (h t s x)

/-- An array added at the end leaves the arrays before it. -/
theorem grows_push {F G : Fork} {X : HTree} (h : G.trees = F.trees.push X) : Grows F G := by
  rintro t s ⟨h1, h2⟩
  refine ⟨by rw [h, Array.size_push]; omega, ?_⟩
  rw [← h2]
  unfold shapeAt
  have e : G.trees.getD t {} = F.trees.getD t {} := by
    rw [h]
    simp [Array.getD, Array.getElem_push, h1, Nat.lt_succ_of_lt h1]
  rw [e]

/-- The array that was added at the end. -/
theorem has_push {F G : Fork} {X : HTree} (h : G.trees = F.trees.push X) :
    Has G F.trees.size (X.kind, X.R, X.K, X.rows.size) := by
  refine ⟨by rw [h, Array.size_push]; omega, ?_⟩
  unfold shapeAt
  have e : G.trees.getD F.trees.size {} = X := by
    rw [h]
    simp [Array.getD]
  rw [e]

/-- One array with nv virtual rows is added at the end of the list. -/
theorem t2AddN_ok {F G : Fork} {T T' : Tail2} {name : String} {R K ec a : Nat} {foreign : Bool}
    {nv got : Nat} (h : t2AddN F T name R K ec a foreign nv = .ok (got, G, T')) :
    got = F.trees.size ∧ Grows F G ∧ Has G got (HKind.table, R, K, nv) := by
  unfold t2AddN at h
  split at h
  · cases h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    refine ⟨rfl, grows_push rfl, ?_, ?_⟩
    · simp
    · simp [shapeAt, Array.getD]

/-- One symbol array is added at the end of the list. -/
theorem t2AddP_ok {F G : Fork} {T T' : Tail2} {name : String} {m k w a : Nat} {foreign : Bool}
    {got : Nat} (h : t2AddP F T name m k w a foreign = .ok (got, G, T')) : Grows F G := by
  unfold t2AddP at h
  split at h
  · cases h
  · split at h
    · cases h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl, -⟩ := h
      exact grows_push rfl

/-- A loop that can refuse: a property of (the members done so far, the loop's state) that every
turn that does not refuse carries on, where no turn ends the loop early. -/
theorem forIn_exc {α β ε : Type} (Inv : List α → β → Prop) (f : α → β → Except ε (ForInStep β))
    (hf : ∀ done a b s, Inv done b → f a b = .ok s → ∃ x, s = .yield x ∧ Inv (done ++ [a]) x) :
    ∀ (l done : List α) (b r : β), forIn l b f = .ok r → Inv done b → Inv (done ++ l) r
  | [], done, b, r, h, h0 => by
    rw [List.forIn_nil] at h
    obtain rfl := Except.ok.inj h
    simpa using h0
  | a :: l, done, b, r, h, h0 => by
    rw [List.forIn_cons] at h
    obtain ⟨s, hs, h⟩ := (excBind_ok _ _ _).1 h
    obtain ⟨x, rfl, hx⟩ := hf done a b s h0 hs
    have := forIn_exc Inv f hf l (done ++ [a]) x r h hx
    simpa using this

/-- The shapes of the arrays that the routine has added. -/
theorem addTreesF_frame (tl tl' : HTailF2) (F F' : Fork) (T T' : Tail2) (nU aTX : Array Nat)
    (hb hbLine : Nat) (h : tl.addTreesF F T nU aTX hb hbLine = .ok (tl', F', T')) :
    (∀ n, n < 3 → ∀ t, tl.ix.U.getD n none = some t → UShape F' t (nU.getD n 0)) ∧
      Has F' tl.ix.ZZ (HKind.table, tl.tau, 2 * tl.mz, 2 * tl.zzBlocks + 2) ∧
      Has F' tl.ix.BZ (HKind.table, 32, tl.bzColumns, 3) ∧ Grows F F' := by
  unfold HTailF2.addTreesF at h
  obtain ⟨_, h⟩ := (ite_throw_ok _ _ _ _).1 h
  obtain ⟨_, h⟩ := (ite_throw_ok _ _ _ _).1 h
  obtain ⟨_, h⟩ := (ite_throw_ok _ _ _ _).1 h
  obtain ⟨_, h⟩ := (ite_throw_ok _ _ _ _).1 h
  obtain ⟨r1, h1, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨r2, h2, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨r3, h3, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨⟨gz, Fz, Tz⟩, hz, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨hgz, h⟩ := (ite_throw_ok _ _ _ _).1 h
  obtain ⟨⟨gb, Fb, Tb⟩, hbz, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨hgb, h⟩ := (ite_throw_ok _ _ _ _).1 h
  obtain ⟨r4, h4, h⟩ := (excBind_ok _ _ _).1 h
  obtain ⟨_, h⟩ := (ite_throw_ok _ _ _ _).1 h
  have e := Except.ok.inj h
  simp only [Prod.mk.injEq] at e
  obtain ⟨-, rfl, -⟩ := e
  -- the vectors of the tables
  have i1 := forIn_exc
    (fun (done : List Nat) (r : MProd Fork Tail2) => Grows F r.fst ∧
      ∀ n ∈ done, ∀ t, tl.ix.U.getD n none = some t → Has r.fst t (HKind.table, 1, nU.getD n 0, 1))
    _ (by
      intro done n r s hI hs
      dsimp only at hs
      cases hU : tl.ix.U.getD n none with
      | none =>
        simp only [hU] at hs
        refine ⟨_, (Except.ok.inj hs).symm, hI.1, ?_⟩
        intro n' hn' t ht
        rcases List.mem_append.1 hn' with hn' | hn'
        · exact hI.2 n' hn' t ht
        · obtain rfl : n' = n := by simpa using hn'
          rw [hU] at ht
          cases ht
      | some want =>
        simp only [hU] at hs
        obtain ⟨⟨got, F1, T1⟩, ha, hs⟩ := (excBind_ok _ _ _).1 hs
        dsimp only at hs
        obtain ⟨hne, hs⟩ := (ite_throw_ok _ _ _ _).1 hs
        obtain ⟨-, hg, hh⟩ := t2AddN_ok ha
        refine ⟨_, (Except.ok.inj hs).symm, hI.1.trans hg, ?_⟩
        intro n' hn' t ht
        rcases List.mem_append.1 hn' with hn' | hn'
        · exact hg _ _ (hI.2 n' hn' t ht)
        · obtain rfl : n' = n := by simpa using hn'
          rw [hU] at ht
          obtain rfl := Option.some.inj ht
          have : got = want := by simpa using hne
          rw [← this]
          exact hh) _ [] _ _ h1 ⟨Grows.refl F, fun _ hn => absurd hn (by simp)⟩
  -- the three loops over symbol arrays
  have i2 := forIn_exc (fun (_ : List Nat) (r : MProd Fork Tail2) => Grows r1.fst r.fst) _ (by
      intro done i r s hI hs
      dsimp only at hs
      obtain ⟨⟨got, F1, T1⟩, ha, hs⟩ := (excBind_ok _ _ _).1 hs
      dsimp only at hs
      obtain ⟨-, hs⟩ := (ite_throw_ok _ _ _ _).1 hs
      exact ⟨_, (Except.ok.inj hs).symm, hI.trans (t2AddP_ok ha)⟩) _ [] _ _ h2 (Grows.refl _)
  have i3 := forIn_exc (fun (_ : List Nat) (r : MProd Fork Tail2) => Grows r2.fst r.fst) _ (by
      intro done i r s hI hs
      dsimp only at hs
      obtain ⟨⟨got, F1, T1⟩, ha, hs⟩ := (excBind_ok _ _ _).1 hs
      dsimp only at hs
      obtain ⟨-, hs⟩ := (ite_throw_ok _ _ _ _).1 hs
      exact ⟨_, (Except.ok.inj hs).symm, hI.trans (t2AddP_ok ha)⟩) _ [] _ _ h3 (Grows.refl _)
  have i4 := forIn_exc (fun (_ : List Nat) (r : MProd Fork Tail2) => Grows Fb r.fst) _ (by
      intro done i r s hI hs
      dsimp only at hs
      obtain ⟨⟨got, F1, T1⟩, ha, hs⟩ := (excBind_ok _ _ _).1 hs
      dsimp only at hs
      obtain ⟨-, hs⟩ := (ite_throw_ok _ _ _ _).1 hs
      exact ⟨_, (Except.ok.inj hs).symm, hI.trans (t2AddP_ok ha)⟩) _ [] _ _ h4 (Grows.refl _)
  obtain ⟨-, gZ, hZ⟩ := t2AddN_ok hz
  obtain ⟨-, gB, hB⟩ := t2AddN_ok hbz
  have ez : gz = tl.ix.ZZ := by simpa using hgz
  have eb : gb = tl.ix.BZ := by simpa using hgb
  have g14 : Grows r1.fst r4.fst := ((i2.trans i3).trans gZ).trans (gB.trans i4)
  refine ⟨?_, ?_, ?_, i1.1.trans g14⟩
  · intro n hn t ht
    have := g14 _ _ (i1.2 n (by simpa using hn) t ht)
    exact ⟨this.1, this.2⟩
  · rw [← ez]
    exact i4 _ _ (gB _ _ hZ)
  · rw [← eb]
    exact i4 _ _ hB

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.addTreesF_frame
