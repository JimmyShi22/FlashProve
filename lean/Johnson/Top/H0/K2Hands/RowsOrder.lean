-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hands/RowsOrder.lean: the rows that a code switch lays, in their order, at
ANY
switch: with kept members, with any number of mask rows.

Laws on four pure functions of the hand-written program's file OnBytes/Iop/Cs.lean: switchRows,
switchCarried, switchOldSamples, switchFormOn. The library's OnBytes/Slice/BlkCsRows.lean has
switchRows_eq, switchCarried_eq and switchOldSamples_nil for a switch without a kept member and with
two
mask rows; here the general forms, each both ways.
  switchFormOn_iff     a row as a form on one message's main table: when (readsMain), and which form
                       (formOn). THESE TWO ARE THE PROGRAM's OWN BODY, CUT IN TWO AND NAMED
                       (switchFormOn_eq is by rfl): a name for each half, no second description
  switchCarried_iff    the old claim carried over: each kept form finds its member's place; then the
  row is
                       carriedOf: the lifted main form; the kept forms in their order; the mask
                       rows'
                       vectors in their order; the old target
  switchOldSamples_iff the kept members' old sample rows: by member in the order of the frame, then
  by
                       sample row in the order of sending; each reads its member's main table alone
  switchRows_iff       THE ORDER: the carried claim; the old sample rows; then, draw by draw IN THE
  ORDER
                       DRAWN, the generator rows at the symbols read at that draw (the library's
                       symAtB);
                       the array has one symbol for each row at each listed position; each draw is
                       listed
WHAT THESE ARE NOT: nothing is read in the field here: what a row's coefficients are (switchLift,
switchAddRestE, switchAddKept, switchGenerators) is other files'. No soundness is claimed.

-/
import OnBytes.Slice.BlkCsRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes OnBytes.Slice

/-! ## Two loops that can fail -/

theorem mapM_zip {α β γ : Type} (f : α → Option β) (g : α → β → γ) : ∀ l : List α,
    l.mapM (fun x => (f x).bind fun c => some (g x c)) =
      (l.mapM f).map fun cs => (l.zip cs).map fun p => g p.1 p.2
  | [] => rfl
  | x :: l => by
    rw [List.mapM_cons, List.mapM_cons, mapM_zip f g l]
    cases f x with
    | none => rfl
    | some c =>
      cases l.mapM f with
      | none => rfl
      | some cs => rfl

theorem foldlM_zip {α β ρ : Type} (f : α → Option β) (g : ρ → β → α → ρ) : ∀ (l : List α) (a : ρ),
    l.foldlM (fun r x => (f x).bind fun k => some (g r k x)) a =
      (l.mapM f).map fun ks => (l.zip ks).foldl (fun r p => g r p.2 p.1) a
  | [], _ => rfl
  | x :: l, a => by
    rw [List.foldlM_cons, List.mapM_cons]
    cases f x with
    | none => rfl
    | some k =>
      show l.foldlM _ (g a k x) = _
      rw [foldlM_zip f g l]
      cases l.mapM f with
      | none => rfl
      | some ks => rfl

theorem mapM_ite {α γ : Type} (p : α → Bool) (g : α → γ) : ∀ l : List α,
    l.mapM (fun x => if p x = true then some (g x) else none) =
      if l.all p = true then some (l.map g) else none
  | [] => rfl
  | x :: l => by
    rw [List.mapM_cons, mapM_ite p g l]
    by_cases hx : p x = true
    · by_cases hl : l.all p = true
      · simp [hx, hl]
      · simp [hx, hl]
    · simp [hx]

theorem mapM_idx {β : Type} (idx : Nat → Option Nat) (G : Nat → Nat → β) : ∀ (l : List Nat)
    (r : List β), l.mapM (fun x => (idx x).bind fun i => some (G x i)) = some r ↔
      (∀ x ∈ l, (idx x).isSome = true) ∧ r = l.map fun x => G x ((idx x).getD 0)
  | [], r => by
    constructor
    · intro e
      exact ⟨(fun x hx => by cases hx), (Option.some.inj e).symm⟩
    · rintro ⟨-, rfl⟩
      rfl
  | x :: l, r => by
    rw [List.mapM_cons]
    cases hx : idx x with
    | none =>
      constructor
      · intro e
        cases e
      · rintro ⟨h1, -⟩
        have h2 := h1 x (List.mem_cons_self ..)
        rw [hx] at h2
        cases h2
    | some i =>
      cases hl : l.mapM (fun x => (idx x).bind fun i => some (G x i)) with
      | none =>
        have h := mapM_idx idx G l
        simp only [hl] at h
        simp only [Option.bind_eq_bind, Option.bind_some, Option.bind_none, List.mem_cons,
          forall_eq_or_imp, hx, Option.isSome_some, true_and, List.map_cons, Option.getD_some]
        constructor
        · intro e
          cases e
        · rintro ⟨h1, -⟩
          exact absurd ((h _).2 ⟨h1, rfl⟩) (by simp)
      | some r' =>
        obtain ⟨h1, h2⟩ := (mapM_idx idx G l r').1 hl
        simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq,
          List.mem_cons, forall_eq_or_imp, hx, Option.isSome_some, true_and, List.map_cons,
          Option.getD_some, ← h2]
        exact ⟨fun e => ⟨h1, e.symm⟩, fun e => e.2.symm⟩

/-! ## A row as a form on one main table -/

/-- The row reads the main table of the message o and nothing else. -/
def readsMain (o : Nat) (row : Row) : Bool :=
  (row.terms.all fun t => t.oracle == o && t.part == .main) &&
    (row.units.all fun u => u.oracle == o && u.part == .main) &&
    (row.runs.all fun r => r.oracle == o && r.part == .main) &&
    row.forms.all fun f => f.oracle == o

/-- The form: the tensors; the single entries; the stretches, entry by entry; the forms. -/
def formOn (row : Row) : Form :=
  row.forms.foldl (fun (c : Form) f => c.plus f.c)
    (row.runs.foldl
      (fun (c : Form) r =>
        (List.range r.coeffs.size).foldl
          (fun c j => c.addEntry (r.first + r.step * j) (r.coeffs.get j)) c)
      (row.units.foldl (fun (c : Form) u => c.addEntry u.index u.coeff)
        (row.terms.foldl (fun (c : Form) t => c.add t.v) {})))

theorem switchFormOn_iff (o : Nat) (row : Row) (c : Form) :
    switchFormOn o row = some c ↔ readsMain o row = true ∧ c = formOn row := by
  unfold switchFormOn readsMain formOn
  split
  · rename_i h
    exact ⟨fun e => ⟨h, (Option.some.inj e).symm⟩, fun e => by rw [e.2]⟩
  · rename_i h
    exact ⟨(fun e => by cases e), fun e => absurd e.1 h⟩

theorem switchFormOn_eq (o : Nat) (row : Row) :
    switchFormOn o row = if readsMain o row = true then some (formOn row) else none := rfl

/-! ## The old claim, carried over -/

/-- The place of the member that a kept form reads. -/
def placeOf (W : SwitchFrame) (f : KeptForm) : Option KeptPlace := W.kept.find? (·.old == f.oracle)

/-- The carried row, at the kept forms' places. -/
def carriedOf (W : SwitchFrame) (old : SingleRows) (ks : List KeptPlace) : Row :=
  { (List.range old.masks).foldl
      (fun (r : Row) j =>
        switchAddRestE r W.g W.restPart
          (switchPieces W.places (W.parts.maskAt.getD j 0) (old.d.getD j #[]).size) (old.d.getD j
              #[]))
      ((old.kept.toList.zip ks).foldl (fun (r : Row) p => W.addKept r p.2 p.1.c)
        (({} : Row).addForm W.g
          (switchLift old.c W.code.logEll W.mainCut W.rowBits W.tableBits))) with
    target := old.target }

theorem switchCarried_iff (W : SwitchFrame) (old : SingleRows) (r : Row) :
    switchCarried W old = some r ↔
      ∃ ks, old.kept.toList.mapM (placeOf W) = some ks ∧ r = carriedOf W old ks := by
  have e : switchCarried W old =
      (old.kept.toList.mapM (placeOf W)).map fun ks => carriedOf W old ks := by
    have h := foldlM_zip (placeOf W) (fun (r : Row) k (f : KeptForm) => W.addKept r k f.c)
      old.kept.toList
      (({} : Row).addForm W.g (switchLift old.c W.code.logEll W.mainCut W.rowBits W.tableBits))
    unfold switchCarried
    simp only [← Array.foldlM_toList, Option.bind_eq_bind, Option.pure_def]
    unfold placeOf at h ⊢
    rw [h]
    cases old.kept.toList.mapM fun f => W.kept.find? (·.old == f.oracle) with
    | none => rfl
    | some ks => rfl
  rw [e]
  constructor
  · intro h
    obtain ⟨ks, hk, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨ks, hk, rfl⟩
  · rintro ⟨ks, hk, rfl⟩
    rw [hk]
    rfl

/-! ## The kept members' old sample rows -/

/-- The sample rows of a kept member, in the order of sending. -/
def samplesOf (S : Statement) (k : KeptPlace) : List Row :=
  (S.oracles.getD k.old default).sampleRows.toList

/-- One old sample row, carried over. -/
def sampleRow (W : SwitchFrame) (k : KeptPlace) (sample : Row) : Row :=
  { W.addKept {} k (formOn sample) with target := sample.target }

theorem switchOldSamples_iff (S : Statement) (W : SwitchFrame) (rows : List Row) :
    switchOldSamples S W = some rows ↔
      (∀ k ∈ W.kept, ∀ sample ∈ samplesOf S k, readsMain k.old sample = true) ∧
        rows = W.kept.flatMap fun k => (samplesOf S k).map (sampleRow W k) := by
  have inner : ∀ k : KeptPlace,
      ((S.oracles.getD k.old default).sampleRows.toList.mapM fun (sample : Row) => do
        let c ← switchFormOn k.old sample
        pure ({ W.addKept {} k c with target := sample.target } : Row)) =
      if (samplesOf S k).all (readsMain k.old) = true then
        some ((samplesOf S k).map (sampleRow W k)) else none := by
    intro k
    rw [← mapM_ite (readsMain k.old) (sampleRow W k) (samplesOf S k)]
    unfold samplesOf
    congr 1
    funext sample
    rw [switchFormOn_eq]
    by_cases h : readsMain k.old sample = true
    · simp [h, sampleRow]
    · simp [h]
  unfold switchOldSamples
  simp only [inner]
  rw [mapM_ite (fun k => (samplesOf S k).all (readsMain k.old))
    (fun k => (samplesOf S k).map (sampleRow W k)) W.kept]
  by_cases h : (W.kept.all fun k => (samplesOf S k).all (readsMain k.old)) = true
  · rw [if_pos h]
    simp only [Option.map_some, Option.some.injEq, List.flatMap_def]
    simp only [List.all_eq_true] at h
    exact ⟨fun e => ⟨h, e.symm⟩, fun e => e.2.symm⟩
  · rw [if_neg h]
    simp only [List.all_eq_true] at h
    exact ⟨(fun e => by cases e), fun e => absurd e.1 h⟩

/-! ## All rows, in their order -/

theorem switchRows_iff (S : Statement) (old : SingleRows) (T : SwitchTarget) (g : Nat)
    (anew : Array Nat) (pos : Positions) (y : Array E) (rows : List Row) :
    switchRows S old T g anew pos y = some rows ↔
      y.size = pos.all.size * old.rows ∧ (∀ x ∈ pos.draws.toList, (pos.indexOf x).isSome) ∧
        ∃ W carried samples, switchFrame S old T g anew = some W ∧
          switchCarried W old = some carried ∧ switchOldSamples S W = some samples ∧
          rows = carried :: samples ++ pos.draws.toList.flatMap fun x =>
            switchGenerators W old x (symAtB old pos y x) := by
  have hgen : ∀ (W : SwitchFrame) (gs : List (List Row)),
      (pos.draws.toList.mapM fun x => (pos.indexOf x).bind fun i =>
        some (switchGenerators W old x fun row => y.getD (i * old.rows + row) zeroE)) = some gs ↔
      (∀ x ∈ pos.draws.toList, (pos.indexOf x).isSome = true) ∧
        gs = pos.draws.toList.map fun x => switchGenerators W old x (symAtB old pos y x) :=
    fun W gs => mapM_idx pos.indexOf
      (fun x i => switchGenerators W old x fun row => y.getD (i * old.rows + row) zeroE) _ gs
  unfold switchRows
  by_cases hz : y.size = pos.all.size * old.rows
  · have hg : (y.size == pos.all.size * old.rows) = true := by simpa using hz
    simp only [hg, guard, if_true, Option.bind_eq_bind, Option.pure_def, Option.bind_some,
      Option.bind_eq_some_iff, Option.some.injEq, hgen]
    constructor
    · rintro ⟨W, hW, c, hc, sm, hs, gs, ⟨hi, rfl⟩, rfl⟩
      exact ⟨hz, hi, W, c, sm, hW, hc, hs, by rw [List.flatMap_def]⟩
    · rintro ⟨-, hi, W, c, sm, hW, hc, hs, rfl⟩
      exact ⟨W, hW, c, hc, sm, hs, _, ⟨hi, rfl⟩, by rw [List.flatMap_def]⟩
  · have hg : (y.size == pos.all.size * old.rows) = false := by simpa using hz
    simp only [hg, guard]
    exact ⟨(fun e => by simp at e), fun e => absurd e.1 hz⟩

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.switchFormOn_iff
#print axioms VerifiableInference.Desc.First.K2Hands.switchCarried_iff
#print axioms VerifiableInference.Desc.First.K2Hands.switchOldSamples_iff
#print axioms VerifiableInference.Desc.First.K2Hands.switchRows_iff
