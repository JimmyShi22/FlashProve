-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/RowKinds.lean: code switching (the kind K2): OF WHICH KIND EACH ROW IS THAT
A SWITCH LAYS: the carried claim and the kept members' samples restated are plain rows; the
generators' rows are generator rows. NO BLOCK IMPORTS THIS FILE. Why. The table of joints' fixed
test on a group's list of open rows asks, place by place, the kind of its class: «carried» plain,
«position» generator.
  foldl_kind · foldlM_kind   a loop of steps that leave a row's kind leaves it
  addKept_kind     the adder of a kept member's form leaves it
  carried_kind     switchCarried W old = some c: c is plain
  sampleRow_kind   a kept member's sample restated is plain
  gens_kind        every row of switchGenerators is a generator row
  laid_kinds       over Laid (K2Hands/RowsAt.lean): rows = carried :: samples ++ gens with these
                   kinds
NEAREST KIN, CALLED OR LEFT AS THEY LIE: kind_restE (called) · kind_carriedRow ·
kind_genMain · kind_genMask (OnBytes/Slice/BlkCsRows.lean:597-617): for a switch without kept
members; here the kept members' rows are in. No soundness is claimed.
-/
import Johnson.Top.H0.K2Hands.GenJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Slice H2K.Lift
open VerifiableInference.Desc.First.K2Hands (Laid samplesOf sampleRow)

theorem foldl_kind {α : Type} (f : Row → α → Row) (hf : ∀ r a, (f r a).kind = r.kind) :
    ∀ (l : List α) (r : Row), (l.foldl f r).kind = r.kind
  | [], _ => rfl
  | a :: l, r => by
    rw [List.foldl_cons, foldl_kind f hf l, hf]

theorem foldlM_kind {α : Type} (f : Row → α → Option Row)
    (hf : ∀ r a r', f r a = some r' → r'.kind = r.kind) :
    ∀ (l : List α) (r r' : Row), l.foldlM f r = some r' → r'.kind = r.kind
  | [], r, r', h => by
    cases h
    rfl
  | a :: l, r, r', h => by
    rw [List.foldlM_cons] at h
    obtain ⟨r₁, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    rw [foldlM_kind f hf l r₁ r' h2, hf r a r₁ h1]

theorem addKept_kind (W : SwitchFrame) (r : Row) (k : KeptPlace) (c : Form) :
    (W.addKept r k c).kind = r.kind := by
  unfold SwitchFrame.addKept switchAddKept
  exact foldl_kind (fun (r : Row) (p : PadPlace × Nat) =>
    (r.addUnit k.anew .main p.1.index (negE (c.entry p.1.index))).addUnit W.g W.restPart
      (W.places.get (k.oldPadAt + p.2)) (c.entry p.1.index)) (fun _ _ => rfl) k.pad.zipIdx
    (r.addForm k.anew c)

theorem carried_kind {W : SwitchFrame} {old : SingleRows} {c : Row}
    (h : switchCarried W old = some c) : c.kind = .plain := by
  unfold switchCarried at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
  obtain ⟨b, hb, rfl⟩ := h
  show ((List.range old.masks).foldl _ b).kind = _
  rw [foldl_kind _ fun r j => kind_restE _ _ _ _ r]
  rw [← Array.foldlM_toList] at hb
  rw [foldlM_kind _ (fun r f r' e => by
    obtain ⟨k, _, e'⟩ := Option.bind_eq_some_iff.1 e
    rw [← Option.some.inj e']
    exact addKept_kind W r k f.c) _ _ _ hb]
  rfl

theorem sampleRow_kind (W : SwitchFrame) (k : KeptPlace) (smp : Row) :
    (sampleRow W k smp).kind = .plain := by
  show (W.addKept {} k _).kind = _
  rw [addKept_kind]

theorem keptFrom_kind (W : SwitchFrame) (x : ℕ) (sy : ℕ → E) : ∀ (ks : List KeptPlace) (n : ℕ),
    ∀ r ∈ keptFrom W x sy ks n, r.kind = .generator
  | [], _, _, h => nomatch h
  | k :: ks, n, r, h => by
    rw [keptFrom] at h
    rcases List.mem_append.1 h with h | h
    · obtain ⟨b, _, rfl⟩ := List.mem_map.1 h
      rfl
    · exact keptFrom_kind W x sy ks _ r h

theorem gens_kind (W : SwitchFrame) (old : SingleRows) (x : ℕ) (sy : ℕ → E) :
    ∀ r ∈ switchGenerators W old x sy, r.kind = .generator := by
  intro r h
  rw [switchGenerators_all] at h
  rcases List.mem_append.1 h with h | h
  · rcases List.mem_cons.1 h with rfl | h
    · rfl
    · exact keptFrom_kind W x sy _ _ r h
  · obtain ⟨j, _, rfl⟩ := List.mem_map.1 h
    rfl

theorem laid_kinds {S : Statement} {old : SingleRows} {T : SwitchTarget} {g : Nat}
    {anew : Array Nat} {pos : Positions} {y : Array E} {rows : List Row} {W : SwitchFrame}
    {carried : Row} (L : Laid S old T g anew pos y rows W carried) :
    ∃ samples gens : List Row, rows = carried :: samples ++ gens ∧ carried.kind = .plain ∧
      (∀ r ∈ samples, r.kind = .plain) ∧ ∀ r ∈ gens, r.kind = .generator := by
  refine ⟨_, _, L.rows, carried_kind L.claim, fun r hr => ?_, fun r hr => ?_⟩
  · obtain ⟨k, _, h⟩ := List.mem_flatMap.1 hr
    obtain ⟨smp, _, rfl⟩ := List.mem_map.1 h
    exact sampleRow_kind W k smp
  · obtain ⟨x, _, h⟩ := List.mem_flatMap.1 hr
    exact gens_kind W old x _ r h

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.carried_kind
#print axioms VerifiableInference.Desc.First.K2.gens_kind
#print axioms VerifiableInference.Desc.First.K2.laid_kinds
