-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
One file of the set on the key file's table of joints (Johnson/Desc/Key/KeyBorders.lean).
Johnson/RunOne/KeyYes.lean: THE KEY FILE's FIRST CHAIN AT THE FROZEN F_K (see Johnson/Desc/Key/KeyBorders.lean's head, «AT WHICH CUT»): THE TWO «YES» FACTS THAT KeyThree.keeps_rngRows AND KeyCaller.keeps_caller0 | 1 ASK, PAID AT THE FROZEN TEXTS: layRows one («rng.0.rows») · caller one i x.
THE TWO UNFOLDINGS FOLLOW Johnson/RunOne/Law/AtKeyD.lean's callerD_law | rowsD_law | addRowsFrom_st and SeatsKeyD.lean's takeMaskP_same (at an earlier working state of these files): TYPED AGAIN HERE, after their proofs, because
more is spent here than these say (the whole state behind; the codes; the groups; every oracle message but for its ledger). Over OnBytes.Slice.withRows_group | withRows_oracles (OnBytes/Slice/BlkCalls.lean).
  bindX | needX | namedX      three small laws on Except
  addRowsFrom_st'             rows added one by one: the statement behind them is withRows
  rowsYes                     **PROVED**: RowsYes (layRows one), where the plan has just two lookups
  Gnd A B                     B is A but for oracle messages' ledgers · takeMaskP_gnd | takeMasksInto_gnd | takeMasksP_gnd   **PROVED**
  forkReady                   **PROVED**: the ledger that the caller opens is ready
  callerYes                   **PROVED**: CallerYes (faceOfLkp x).slots (caller one i x)
Nothing on soundness.
-/
import Johnson.RunOne.KeyCaller
import Johnson.Desc.Means.Page
import Johnson.Desc.Book.BookNumbers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows1
open OnBytes OnBytes.Params OnBytes.Slice
open OnBytes.Model (Fork)
open VerifiableInference.Desc VerifiableInference.Desc.Key
open VerifiableInference.Desc.Ground (takeMasksP takeMasksInto takeMaskP addRowsP addRowsFrom addRowP)
open VerifiableInference.Desc.K3 (faceOfLkp homes)
open VerifiableInference.Desc.Key (FirstState Claim Lookup)

theorem bindX {α β : Type} {x : Except String α} {f : α → Except String β} {b : β} (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem needX {n : String} {b : Bool} {u : Unit} (h : need n b = .ok u) : b = true := by
  unfold need at h
  split at h
  · assumption
  · cases h

theorem namedX {α : Type} {n : String} {o : Option α} {a : α} (h : named n o = .ok a) : o = some a := by
  cases o with
  | none => cases h
  | some x => exact congrArg some (Except.ok.inj h)

/-- After AtKeyD.addRowsFrom_st. -/
theorem addRowsFrom_st' {L : Type} (g : Nat) : ∀ (l : List Row) (d d' : _root_.Desc.Plain.DState L), addRowsFrom g l d = some d' → d'.st = withRows d.st g l ∧ d'.book = d.book
  | [], d, d', h => by
    cases h
    exact ⟨rfl, rfl⟩
  | r :: l, d, d', h => by
    have h' : (addRowP d g r).bind (addRowsFrom g l) = some d' := h
    cases h1 : addRowP d g r with
    | none => rw [h1] at h'; cases h'
    | some d1 =>
      rw [h1] at h'
      unfold addRowP at h1
      split at h1
      · cases h1
        exact addRowsFrom_st' g l _ d' h'
      · cases h1

/-- The ground is the one of Johnson/Desc/First/Base/Ground.lean: so Johnson/Desc/Means/Page.lean's own addRowsFrom_keeps serves. -/
theorem addRowsFrom_keeps' {L : Type} (g : Nat) (l : List Row) (d d' : _root_.Desc.Plain.DState L) (h : addRowsFrom g l d = some d') (hI : Means.InOrder d.st) : Means.InOrder d'.st :=
  Means.addRowsFrom_keeps g l d d' h hI

theorem withRows_gsize (g : Nat) : ∀ (l : List Row) (S : Statement), (withRows S g l).groups.size = S.groups.size
  | [], _ => rfl
  | r :: l, S => (withRows_gsize g l (withRow S g r)).trans (by show (S.groups.modify g _).size = _; simp)

theorem tables_of (A B : Statement) (ho : B.oracles = A.oracles) (hc : B.codes = A.codes) : SameTables B A := by
  refine ⟨by rw [ho], fun o part => ?_⟩
  unfold Statement.tableBits Statement.rowBits Statement.placeBits
  rw [ho, hc]

/-- **rng.0.rows' yes**, at the frozen text. -/
theorem rowsYes (one : OneTime) (hn : (lookupsOf one).length = 2) : RowsYes (layRows one) := by
  intro s rs gs s' h
  have h' : (do
      need "rng.0.rows: all lookups have laid their rows" (s.base.rows.length == (lookupsOf one).length)
      need "rng.0.rows: the ranges' group holds no open row and its test has not begun" ((s.d.st.groups[s.grp]?).any fun G => G.rows.isEmpty && !G.inRun)
      let d ← named "rng.0.rows: a row does not fit the ranges' group" (addRowsP s.d s.grp s.base.rows.flatten)
      pure ({ s with d := d } : FirstState) : Except String FirstState) = .ok s' := h
  obtain ⟨_, h1, h'⟩ := bindX h'
  obtain ⟨_, _, h'⟩ := bindX h'
  obtain ⟨d, h3, h'⟩ := bindX h'
  cases h'
  have e3 := namedX h3
  unfold addRowsP at e3
  split at e3
  · obtain ⟨est, ebk⟩ := addRowsFrom_st' _ _ _ _ e3
    have ho := withRows_oracles s.grp s.base.rows.flatten s.d.st
    refine ⟨d, rfl, ⟨tables_of _ _ (est ▸ ho.1) (est ▸ ho.2), est ▸ ho.1, est ▸ ho.2, ebk, est ▸ withRows_gsize s.grp s.base.rows.flatten s.d.st, addRowsFrom_keeps' _ _ _ _ e3, fun Gr hG => ?_, VerifiableInference.Desc.Book.addRowsFrom_roots _ _ _ _ e3⟩, ?_⟩
    · refine ⟨{ Gr with rows := Gr.rows ++ s.base.rows.flatten.toArray }, ?_, by simp, rfl, rfl⟩
      rw [est]
      exact withRows_group _ _ _ _ hG
    · have := needX h1
      rw [hn] at this
      simpa using this
  · cases e3

/-- B is A but for oracle messages' ledgers. -/
structure Gnd (A B : Statement) : Prop where
  tables : SameTables B A
  codes : B.codes = A.codes
  groups : B.groups = A.groups
  oracle : ∀ o : Nat, (B.oracles[o]?).map unl = (A.oracles[o]?).map unl

theorem Gnd.refl (A : Statement) : Gnd A A := ⟨⟨rfl, fun _ _ => rfl⟩, rfl, rfl, fun _ => rfl⟩

theorem Gnd.trans {A B C : Statement} (h : Gnd A B) (h' : Gnd B C) : Gnd A C :=
  ⟨⟨h'.tables.1.trans h.tables.1, fun o p => (h'.tables.2 o p).trans (h.tables.2 o p)⟩, h'.codes.trans h.codes, h'.groups.trans h.groups, fun o => (h'.oracle o).trans (h.oracle o)⟩

/-- After SeatsKeyD.takeMaskP_same. -/
theorem takeMaskP_gnd {L : Type} {d d' : _root_.Desc.Plain.DState L} {o n : Nat} (h : takeMaskP d o = some (n, d')) : Gnd d.st d'.st ∧ d'.book = d.book := by
  unfold takeMaskP at h
  split at h
  · cases hl : (d.st.oracles[o]?).bind (·.ledger) with
    | none => rw [hl] at h; cases h
    | some l =>
      rw [hl] at h
      cases h
      refine ⟨⟨⟨by simp, fun o' part => ?_⟩, rfl, rfl, fun o' => ?_⟩, rfl⟩
      · unfold Statement.tableBits Statement.rowBits Statement.placeBits
        simp only [Array.getElem?_modify]
        by_cases ho : o = o'
        · subst ho
          cases hx : d.st.oracles[o]? <;> simp [hx]
        · simp [ho]
      · simp only [Array.getElem?_modify]
        by_cases ho : o = o'
        · subst ho
          cases hx : d.st.oracles[o]? <;> simp [hx, unl]
        · simp [ho]
  · cases h

theorem takeMasksInto_gnd {L : Type} (o : Nat) : ∀ (n : Nat) (d d' : _root_.Desc.Plain.DState L) (acc : Array Nat) (r : List Nat), takeMasksInto o n d acc = some (r, d') → Gnd d.st d'.st ∧ d'.book = d.book
  | 0, d, d', acc, r, h => by
    cases h
    exact ⟨Gnd.refl _, rfl⟩
  | n + 1, d, d', acc, r, h => by
    unfold takeMasksInto at h
    cases h1 : takeMaskP d o with
    | none => rw [h1] at h; cases h
    | some x =>
      rw [h1] at h
      have q1 := takeMaskP_gnd (n := x.1) (d' := x.2) h1
      have q2 := takeMasksInto_gnd o n x.2 d' _ r h
      exact ⟨q1.1.trans q2.1, q2.2.trans q1.2⟩

theorem takeMasksP_gnd {L : Type} {d : _root_.Desc.Plain.DState L} {o n : Nat} {x : List Nat × _root_.Desc.Plain.DState L} (h : takeMasksP d o n = some x) : Gnd d.st x.2.st ∧ x.2.book = d.book :=
  takeMasksInto_gnd o n d x.2 #[] x.1 h

/-- **The ledger that the caller opens is ready.** (Its content: KeyLaw.ready_slots.) -/
theorem forkReady (n : Nat) (hm : Array Slot) (h : hm.size = n) : ForkReady n (({} : Fork).slots n) hm where
  home := h
  next := rfl
  ns := rfl
  vp := by simp [Fork.slots]
  mf := by simp [Fork.slots]
  got := by simp [Fork.slots]
  free := fun j hj => by
    show (Array.replicate n false).getD j true = false
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate, if_pos hj]
    rfl

/-- **The caller's yes**, at the frozen text. -/
theorem callerYes (one : OneTime) (i : Nat) (x : Lookup) : CallerYes (faceOfLkp x).slots (caller one i x) := by
  intro s rs gs s' h
  have h' : (do
      need "the caller: a ledger is open" s.base.fork.isNone
      need "the caller: the lookups come in their order" (s.base.keys.length == i)
      let o ← named "the caller: the own message's ledger does not hand out the lookup's entries" (takeMasksP s.d one.ranges.messageId ((faceOfLkp x).slots - 2 * (faceOfLkp x).parts.length))
      let k ← named "the caller: the index-mask message's ledger does not hand out the lookup's entries" (takeMasksP o.2 s.idx (2 * (faceOfLkp x).parts.length))
      need "the caller: every hidden value has a home" ((homes (faceOfLkp x) (o.1.map fun j => ⟨one.ranges.messageId, j⟩) (k.1.map fun j => ⟨s.idx, j⟩)).size == (faceOfLkp x).slots)
      pure ({ s with
        d := k.2
        base := { s.base with
          fork := some (({} : Fork).slots (faceOfLkp x).slots)
          heard := none
          home := homes (faceOfLkp x) (o.1.map fun j => ⟨one.ranges.messageId, j⟩) (k.1.map fun j => ⟨s.idx, j⟩) } } : FirstState) : Except String FirstState) = .ok s' := h
  obtain ⟨_, _, h'⟩ := bindX h'
  obtain ⟨_, _, h'⟩ := bindX h'
  obtain ⟨o, h3, h'⟩ := bindX h'
  obtain ⟨k, h4, h'⟩ := bindX h'
  obtain ⟨_, h5, h'⟩ := bindX h'
  cases h'
  have g3 := takeMasksP_gnd (namedX h3)
  have g4 := takeMasksP_gnd (namedX h4)
  have g := g3.1.trans g4.1
  exact ⟨k.2, _, _, rfl, ⟨g.tables, g.codes, g.groups, g4.2.trans g3.2, g.oracle, (VerifiableInference.Desc.Book.takeMasksP_roots o.2 k.2 _ _ k.1 (namedX h4)).trans (VerifiableInference.Desc.Book.takeMasksP_roots s.d o.2 _ _ o.1 (namedX h3))⟩, forkReady _ _ (by simpa using needX h5)⟩

end Johnson.RunOne.KeyRows1

#print axioms Johnson.RunOne.KeyRows1.rowsYes
#print axioms Johnson.RunOne.KeyRows1.callerYes
