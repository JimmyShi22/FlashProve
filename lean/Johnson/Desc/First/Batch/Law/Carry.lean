-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Law/Carry.lean
(kind K9's soundness lemma): THEOREMS: the data that the tables hold, as a state's
own layout, frame and statement read them (dataAt, Law/Hout.lean), are the same in front of and
behind K9's blocks: what the rule of composition asks under the name "the bound data are carried".
  dataAt_of_same   two states whose segments have the same layout and frame, and whose statements
                   give every table the same numbers of bits, read the same data.
  batch_dataAt     across the step of K9.batch X p f, IF THE FUNCTION f OF CLAIMS KEEPS dataAt (the
                   runs' duty): the draw keeps the segment's check and the statement; the adding
                   turns the ledger alone.
  coefRun_dataAt   across the step that sets the virtual rows' weights (Law/AfterKeeps.lean).
  oneEquation_dataAt   across the step of K9.oneEquation.
  groupHolds_of_same, batch_groupHolds   the like, backward, for "every open row of the segment's
                   group holds on the tables" (GroupHoldsAt).
The hypothesis on the lens: behind a writing, the segment's record and the statement that are read
are those written.

-/
import Johnson.Desc.First.Batch.Law.DoorFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9L
open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9 (Lens Where batch)

variable {T K : Type} [CommRing K]

theorem dataAt_of_same (X : Lens T) (s s' : T) (a a' : K9.Part) (h : X.get? s = some a)
    (h' : X.get? s' = some a') (hr : a'.L.check.rows = a.L.check.rows)
    (hf : a'.L.check.frame = a.L.check.frame) (hb : SameBits a.d.st a'.d.st)
    (tab : Nat → OnBytes.Part → Nat → K) : dataAt X s' tab = dataAt X s tab := by
  simp only [dataAt, h, h', hr, hf]
  exact dataOf_bits _ _ _ _ hb tab

/-- **Across the batching's step.** -/
theorem batch_dataAt (X : Lens T) (p : Where) (f : T → Except String (List Claim × T)) (ft : Nat)
    (s : T) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : T) (k : Nat)
    (tab : Nat → OnBytes.Part → Nat → K)
    (lens : ∀ s a, (X.get? s).isSome = true →
      ∃ a', X.get? (X.set s a) = some a' ∧ a'.L = a.L ∧ a'.d.st = a.d.st)
    (hf : ∀ s₁ cls s₂, f s₁ = .ok (cls, s₂) → dataAt X s₂ tab = dataAt X s₁ tab)
    (h : (batch X p f).step ft s rs cols = .ok (s', k)) : dataAt X s' tab = dataAt X s tab := by
  obtain ⟨r, x, a, o, cls, s₂, b, G, _, _, ha, ho, hfs, hb, _, rfl⟩ :=
    batch_step X p f ft s rs cols s' k h
  have hd := drawnClean_ok _ _ _ _ _ _ _ ho
  have hck : o.L.check = a.L.check := hd.2.2.2.2.2.2.2.2.2.1
  obtain ⟨a₁, h1, l1, d1⟩ :=
    lens s { a with owed := o.owed, L := o.L, F := o.F } (by simp [ha])
  obtain ⟨b', h2, l2, d2⟩ := lens s₂ { b with F := G } (by simp [hb])
  have l1' : a₁.L = o.L := l1
  have d1' : a₁.d.st = a.d.st := d1
  have l2' : b'.L = b.L := l2
  have d2' : b'.d.st = b.d.st := d2
  rw [dataAt_of_same X s₂ _ b b' hb h2 (by rw [l2']) (by rw [l2'])
      (by rw [d2']; exact SameBits.refl _) tab, hf _ _ _ hfs,
    dataAt_of_same X s _ a a₁ ha h1 (by rw [l1', hck]) (by rw [l1', hck])
      (by rw [d1']; exact SameBits.refl _) tab]

/-- Across the step that sets the virtual rows' weights. -/
theorem coefRun_dataAt (X : Lens T) (tailOf : T → HTailF2) (s s' : T)
    (tab : Nat → OnBytes.Part → Nat → K)
    (lens : ∀ s a, (X.get? s).isSome = true →
      ∃ a', X.get? (X.set s a) = some a' ∧ a'.L = a.L ∧ a'.d.st = a.d.st)
    (h : coefRun X tailOf s = .ok s') : dataAt X s' tab = dataAt X s tab := by
  unfold coefRun at h
  obtain ⟨a, ha, h⟩ := ok_bind h
  obtain ⟨G, _, h⟩ := ok_bind h
  have ha' := there_ok ha
  have e : X.set s { a with F := G } = s' := Except.ok.inj h
  obtain ⟨a', h1, l1, d1⟩ := lens s { a with F := G } (by simp [ha'])
  have l1' : a'.L = a.L := l1
  have d1' : a'.d.st = a.d.st := d1
  rw [← e]
  exact dataAt_of_same X s _ a a' ha' h1 (by rw [l1']) (by rw [l1'])
    (by rw [d1']; exact SameBits.refl _) tab

/-- Across the equation's step. -/
theorem oneEquation_dataAt {Cl : Type} (X : Lens T) (p : Where) (ft : Nat) (s : T)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : T) (k : Nat) (tab : Nat → OnBytes.Part → Nat → K)
    (lens : ∀ s a, (X.get? s).isSome = true →
      ∃ a', X.get? (X.set s a) = some a' ∧ a'.L = a.L ∧ a'.d.st = a.d.st)
    (h : (K9.oneEquation (Cl := Cl) X p).step ft s rs cols = .ok (s', k)) :
    dataAt X s' tab = dataAt X s tab := by
  obtain ⟨a, out, ha, hdoor, rfl⟩ := oneEquation_inv X p ft s rs cols s' k h
  obtain ⟨_, _, _, row, d1, _, _, _, hr, ho, _, hL⟩ := door_parts _ _ _ _ _ _ hdoor
  obtain ⟨a', h1, l1, e1⟩ :=
    lens s { a with owed := out.owed, L := out.L, F := out.F, d := out.d } (by simp [ha])
  have l1' : a'.L = a.L := l1.trans hL
  have e1' : a'.d.st = out.d.st := e1
  exact dataAt_of_same X s _ a a' ha h1 (by rw [l1']) (by rw [l1']) (by
    rw [e1', ho]
    exact (asRow_bits _ _ _ _ _ _ hr).trans (withRow_bits _ _ _)) tab

/-! ## "Every open row of the segment's group holds", carried backward -/

theorem groupHolds_of_same (X : Lens T) (ρ : Reading K) (N : Nat) (s s' : T) (a a' : K9.Part)
    (h : X.get? s = some a) (h' : X.get? s' = some a') (hc : a'.L.check = a.L.check)
    (hd : a'.d.st = a.d.st) (tab : Nat → OnBytes.Part → Nat → K)
    (hh : GroupHoldsAt X ρ N s' tab) : GroupHoldsAt X ρ N s tab := by
  intro a2 ha2 G hG row hrow
  have e : a2 = a := Option.some.inj (ha2.symm.trans h)
  subst e
  have h1 := hh a' h' G (by rw [hd, hc]; exact hG) row hrow
  rw [hd] at h1
  exact h1

/-- **Across the batching's step**, if the function f of claims carries it (the runs' duty). -/
theorem batch_groupHolds (X : Lens T) (ρ : Reading K) (N : Nat) (p : Where)
    (f : T → Except String (List Claim × T)) (ft : Nat) (s : T) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) (s' : T) (k : Nat) (tab : Nat → OnBytes.Part → Nat → K)
    (lens : ∀ s a, (X.get? s).isSome = true →
      ∃ a', X.get? (X.set s a) = some a' ∧ a'.L = a.L ∧ a'.d.st = a.d.st)
    (hf : ∀ s₁ cls s₂, f s₁ = .ok (cls, s₂) → GroupHoldsAt X ρ N s₂ tab →
      GroupHoldsAt X ρ N s₁ tab)
    (h : (batch X p f).step ft s rs cols = .ok (s', k)) (hh : GroupHoldsAt X ρ N s' tab) :
    GroupHoldsAt X ρ N s tab := by
  obtain ⟨r, x, a, o, cls, s₂, b, G, _, _, ha, ho, hfs, hb, _, rfl⟩ :=
    batch_step X p f ft s rs cols s' k h
  have hd := drawnClean_ok _ _ _ _ _ _ _ ho
  have hck : o.L.check = a.L.check := hd.2.2.2.2.2.2.2.2.2.1
  obtain ⟨a₁, h1, l1, d1⟩ :=
    lens s { a with owed := o.owed, L := o.L, F := o.F } (by simp [ha])
  obtain ⟨b', h2, l2, d2⟩ := lens s₂ { b with F := G } (by simp [hb])
  have l1' : a₁.L = o.L := l1
  have l2' : b'.L = b.L := l2
  exact groupHolds_of_same X ρ N s _ a a₁ ha h1 (by rw [l1', hck]) d1 tab
    (hf _ _ _ hfs (groupHolds_of_same X ρ N s₂ _ b b' hb h2 (by rw [l2']) d2 tab hh))

end VerifiableInference.Desc.K9L

#print axioms VerifiableInference.Desc.K9L.batch_groupHolds
#print axioms VerifiableInference.Desc.K9L.batch_dataAt
#print axioms VerifiableInference.Desc.K9L.coefRun_dataAt
#print axioms VerifiableInference.Desc.K9L.oneEquation_dataAt
