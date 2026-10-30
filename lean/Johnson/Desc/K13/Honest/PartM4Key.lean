-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Honest/PartM4Key.lean: the laws of Johnson/Desc/K13/Honest/PartM4.lean at two
lenses of the library: the key file's `batchLens` (Johnson/Desc/Key/One.lean) and the proof file's
`atS` (Johnson/Desc/K13/AtS.lean). One definition, and statements with their proofs.

What each lens reads and writes is the library's: `lens_get`, `lens_set`
(Johnson/Desc/Key/KeyLensLaws.lean) and `atS_get` (Johnson/Desc/K13/Law/GoodAny.lean) are called.
Main names:
  `batchPart`: the part that `batchLens.get?` yields at a state that has come to the batching.
  `rowsB_returns_key`: **the law on the shape alone at `batchLens`**: at a state s of the key file's
    first chain with `s.atEnd`, where the guards and the two clauses on pads accept at the shape of
    `batchPart s`: the decision of `rowsB batchLens P` accepts; the state behind is s with `lin` and
    `d` laid anew and the count that is owed without a 0; the shape of the part that is laid is the
    update.
  `rowsB_behind_key`: the same law, said of the part that the lens READS behind: the state behind
    has come to the batching, and the shape of its `batchPart` is the update (`debt_debt`: the count
    that waits, taken twice, is the count that waits).
  `rowsB_carries_key`: wherever that decision accepts, the same is said of the state behind.
  `lensSt_key`: `batchLens` has the library's law on the statement (`LensSt`,
    Johnson/Desc/K13/Keeps.lean).
  `rowsB_returns_atS`: the like at `atS`: so the law of ShapeM4Ready.lean on acceptance is an
    instance.

What is not claimed. What PartM4.lean says is not claimed. Nothing on the sub-protocols that stand
in front of `rowsB` in the key file's "w.1.send". That the tests accept at any state of a run of the
key file's IOP. Nothing on soundness or on hiding.

-/
import Johnson.Desc.K13.Honest.PartM4
import Johnson.Desc.Key.KeyLensLaws
import Johnson.Desc.K13.Law.GoodAny
import Johnson.Desc.K13.Keeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Slice
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Key (ChainState batchLens lens_get lens_set)

variable {β Cl : Type}

/-- The part that `batchLens.get?` yields at a state that has come to the batching. -/
def batchPart (s : ChainState β) : Part :=
  { owed := s.debt, heard := none, indexMasks := s.idx, pile := s.pile, msg := s.msgW
    ids := s.ids, lin := s.lin, d := s.d }

/-- **The law on the shape alone, at the key file's lens.** -/
theorem rowsB_returns_key (P : Where) {s : ChainState β} (he : s.atEnd = true)
    (h : ready4 P.lin (partSh4 (batchPart s)) = true)
    (hq : pads4 P.lin (partSh4 (batchPart s)) = true) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    ∃ p', (rowsB (Cl := Cl) batchLens P).decide s rs gs =
        .ok { s with owed := s.debt, lin := p'.lin, d := p'.d } ∧
      partSh4 p' = stepPart P.lin (partSh4 (batchPart s)) := by
  obtain ⟨p', h1, h2, e1, _, _, _, e5, e6⟩ :=
    rowsB_returns_at (Cl := Cl) batchLens P ((lens_get s _).2 ⟨he, rfl⟩) h hq rs gs
  refine ⟨p', ?_, h2⟩
  rw [h1]
  rw [lens_set, e1, e5, e6]

/-- The count that waits, taken twice, is the count that waits. -/
theorem debt_debt (s : ChainState β) (l : Option LinFirst) (d : St) :
    ({ s with owed := s.debt, lin := l, d := d } : ChainState β).debt = s.debt := by
  show (s.owed.filter (· != 0)).filter (· != 0) = s.owed.filter (· != 0)
  cases h : s.owed with
  | none => rfl
  | some n =>
    by_cases hn : (n != 0) = true
    · simp [Option.filter, hn]
    · simp [Option.filter, hn]

/-- **The law on the shape alone, said of the part that the lens READS behind**: the decision
accepts with a state s' that has come to the batching, and the shape of `batchPart s'` is the
update. -/
theorem rowsB_behind_key (P : Where) {s : ChainState β} (he : s.atEnd = true)
    (h : ready4 P.lin (partSh4 (batchPart s)) = true)
    (hq : pads4 P.lin (partSh4 (batchPart s)) = true) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    ∃ s', (rowsB (Cl := Cl) batchLens P).decide s rs gs = .ok s' ∧ s'.atEnd = true ∧
      partSh4 (batchPart s') = stepPart P.lin (partSh4 (batchPart s)) := by
  obtain ⟨p', h1, h2, e1, _⟩ :=
    rowsB_returns_at (Cl := Cl) batchLens P ((lens_get s _).2 ⟨he, rfl⟩) h hq rs gs
  have h2' : partSh4 p' = stepPart P.lin (partSh4 (batchPart s)) := h2
  have e1' : p'.owed = s.owed.filter (· != 0) := e1
  have e : p'.owed.filter (· != 0) = p'.owed := by
    rw [e1']
    exact debt_debt s none s.d
  refine ⟨_, h1, he, ?_⟩
  rw [← h2']
  show Sh4.mk true p'.ids (p'.lin.map laidSh) (p'.owed.filter (· != 0)) (stSh p'.d.st) =
    Sh4.mk true p'.ids (p'.lin.map laidSh) p'.owed (stSh p'.d.st)
  rw [e]

/-- Wherever that decision accepts. -/
theorem rowsB_carries_key (P : Where) {s s' : ChainState β} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (rowsB (Cl := Cl) batchLens P).decide s rs gs = .ok s') :
    s.atEnd = true ∧ ∃ p', s' = { s with owed := s.debt, lin := p'.lin, d := p'.d } ∧
      partSh4 p' = stepPart P.lin (partSh4 (batchPart s)) := by
  obtain ⟨p, p', hp, rfl, _, h2, e1, _, _, _, e5, e6⟩ := rowsB_carries_at batchLens P h
  obtain ⟨he, rfl⟩ := (lens_get s p).1 hp
  refine ⟨he, p', ?_, h2⟩
  rw [lens_set, e1, e5, e6]

/-- The key file's lens has the library's law on the statement (`LensSt`,
Johnson/Desc/K13/Keeps.lean) at the state's own statement. -/
theorem lensSt_key : LensSt (batchLens (β := β)) fun s => s.d.st where
  enter := by
    intro t t' h
    obtain ⟨_, rfl⟩ := (Key.lens_enter t t').1 h
    rfl
  get := by
    intro t p h
    obtain ⟨_, rfl⟩ := (lens_get t p).1 h
    rfl
  set := fun _ _ _ _ => rfl

/-- The law on the shape alone at `atS`: the guards do not read the count that is owed, so they are
asked at `sh4 s`. -/
theorem rowsB_returns_atS (P : Where) {s : S} (h : ready4 P.lin (sh4 s) = true)
    (hq : pads4 P.lin (sh4 s) = true) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) :
    ∃ p', (rowsB (Cl := Cl) atS P).decide s rs gs = .ok (atS.set s p') := by
  obtain ⟨a, l, hs, hl⟩ := laid_of_ready h
  rw [sh4_mem hs] at h hq
  obtain ⟨p', h1, _⟩ := rowsB_returns_at (Cl := Cl) atS P (Law.atS_get hs) h hq rs gs
  exact ⟨p', h1⟩

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.rowsB_returns_key
#print axioms VerifiableInference.Desc.K13.Honest.debt_debt
#print axioms VerifiableInference.Desc.K13.Honest.rowsB_behind_key
#print axioms VerifiableInference.Desc.K13.Honest.rowsB_carries_key
#print axioms VerifiableInference.Desc.K13.Honest.lensSt_key
#print axioms VerifiableInference.Desc.K13.Honest.rowsB_returns_atS
