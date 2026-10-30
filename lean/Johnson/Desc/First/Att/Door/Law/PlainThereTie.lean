-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Door/Law/PlainThereTie.lean: WHAT THE TEST plainThereB (Johnson/Desc/First/Att/Door/PlainThereB.lean) MEANS, AND WHO MAKES, KEEPS AND SPENDS THE ITEM «K5.plain». Theorems.
  noEntsB_iff · heardPlainB_iff · wideB_iff · plainThereB_iff: AN IFF: the test says yes just where a ledger U is open, h is held as heard, HeardPlain h (Att/Claims/HeardPlain.lean), and U's array number iU3 is there,
    JUST nW wide (the equation also pays a law's width Kc where the planned width is nW).
  plain_made: behind the kind's own block: from its decision's yes at seatSO at a sized ledger, AND hw: the width at the record behind (the hearing's law says nothing of the arrays: another item has the width in front).
  plain_kept: by every step that carries what was heard (CarK5) and keeps the arrays' shapes (Kept5).
  plain_spent: what a law takes: HeardPlain h and the width, as an equation.
  plain_named_first | plain_named_second: so every entry that the forms of "first" | "second" name at that record's ledger is an entry of row 0 of the array iU3, below nW.
  plain_bites: a control: at a record whose ledger has no array number iU3 the test says no.
Limits. Implications; the test has run nowhere. Nothing on soundness.

-/
import Johnson.Desc.First.Att.Door.PlainThereB
import Johnson.Desc.First.Att.Claims.HeardPlain
import Johnson.Desc.First.Att.Claims.WalkShape

set_option autoImplicit false

namespace H2K5.Door
open OnBytes OnBytes.Model
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Heard ParC)
open K5Law

theorem noEntsB_iff (f : Aff) : noEntsB f = true ↔ NoEnts f := by
  unfold noEntsB NoEnts
  exact List.isEmpty_iff

theorem heardPlainB_iff (h : Heard) : heardPlainB h = true ↔ HeardPlain h := by
  unfold heardPlainB
  simp only [Bool.and_eq_true, List.all_eq_true, noEntsB_iff]
  exact ⟨fun ⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩ => ⟨a, b, c, d, e, f, g⟩,
    fun a => ⟨⟨⟨⟨⟨⟨a.units, a.division⟩, a.below⟩, a.on⟩, a.atIndex⟩, a.key⟩, a.cells⟩⟩

theorem wideB_iff (U : Fork) (iU3 nW : ℕ) : wideB U iU3 nW = true ↔ ∃ T, U.trees[iU3]? = some T ∧ T.K = nW := by
  unfold wideB
  cases e : U.trees[iU3]? with
  | none => simp
  | some T => simp

/-- **What the test means.** -/
theorem plainThereB_iff (iU3 nW : ℕ) (s : S) : plainThereB iU3 nW s = true ↔
    ∃ U h, s.fork? = some U ∧ s.heard5? = some h ∧ HeardPlain h ∧ ∃ T, U.trees[iU3]? = some T ∧ T.K = nW := by
  unfold plainThereB
  cases e1 : s.fork? with
  | none => simp
  | some U =>
    cases e2 : s.heard5? with
    | none => simp
    | some h =>
      simp only [Bool.and_eq_true, heardPlainB_iff, wideB_iff]
      exact ⟨fun ⟨a, b⟩ => ⟨U, h, rfl, rfl, a, b⟩, fun ⟨_, _, r1, r2, a, b⟩ => by
        obtain rfl := Option.some.inj r1
        obtain rfl := Option.some.inj r2
        exact ⟨a, b⟩⟩

/-- **MADE, behind the kind's own block.** -/
theorem plain_made {iU3 nW : ℕ} {p : P.Par} {t t₁ : S} {rs : List Fmt.RoundView} (hd : P.decide P.seatSO p t rs = .ok t₁)
    (hz : ∀ F, P.seatSO.ledger t = some F → Road.Sized F)
    (hw : ∀ U, t₁.fork? = some U → ∃ T, U.trees[iU3]? = some T ∧ T.K = nW) : plainThereB iU3 nW t₁ = true := by
  obtain ⟨_, F, h, G, l1, hh, l2⟩ := (P.decide_lays P.seatSO p _ _ _).1 hd
  obtain ⟨a, _, rfl⟩ := P.seatSO_lay l2
  obtain ⟨L, _, _, _, hs, _, _⟩ := P.hear_said hh (hz F l1)
  exact (plainThereB_iff iU3 nW _).2 ⟨G, h, rfl, rfl, heardPlain_of_said hs, hw G rfl⟩

/-- **KEPT, by every step that carries what was heard and keeps the shapes.** -/
theorem plain_kept {iU3 nW : ℕ} {s s' : S} (h : plainThereB iU3 nW s = true) (hc : CarK5 s s') (hk : Kept5 s s') :
    plainThereB iU3 nW s' = true := by
  obtain ⟨U, hh, e1, e2, a, T, hT, hW⟩ := (plainThereB_iff iU3 nW s).1 h
  have hs : shapes? s' = some (U.trees.map fun T => (T.R, T.K)) := by
    rw [hk.2]
    unfold shapes?
    rw [e1]
    rfl
  unfold shapes? at hs
  obtain ⟨U', e1', _⟩ := Option.map_eq_some_iff.1 hs
  have e := tree_of_shapes hk.2 e1 e1' iU3
  rw [hT] at e
  obtain ⟨T', hT', r⟩ := Option.map_eq_some_iff.1 e
  have eK : T'.K = T.K := (Prod.mk.inj r).2
  exact (plainThereB_iff iU3 nW s').2 ⟨U', hh, e1', hc.1 hh e2, a, T', hT', eK.trans hW⟩

/-- **SPENT.** -/
theorem plain_spent {c : ParC} {s : S} (h : plainThereB c.iU3 c.nW s = true) :
    ∃ U hh T, s.fork? = some U ∧ s.heard5? = some hh ∧ HeardPlain hh ∧ U.trees[c.iU3]? = some T ∧ T.K = c.nW := by
  obtain ⟨U, hh, e1, e2, a, T, hT, hW⟩ := (plainThereB_iff c.iU3 c.nW s).1 h
  exact ⟨U, hh, T, e1, e2, a, hT, hW⟩

theorem plain_named_first {c : ParC} {s : S} (h : plainThereB c.iU3 c.nW s = true) {U : Fork} {hh : Heard}
    (e1 : s.fork? = some U) (e2 : s.heard5? = some hh) {g : Forest.Heard} {l : List Aff}
    (e : firstAt c g hh U = some l) : ∀ f ∈ l, ∀ x ∈ f.ents.toList, x.tree = c.iU3 ∧ x.row = 0 ∧ x.idx < c.nW := by
  obtain ⟨U', hh', T, r1, r2, a, hT, hW⟩ := plain_spent h
  obtain rfl := Option.some.inj (r1.symm.trans e1)
  obtain rfl := Option.some.inj (r2.symm.trans e2)
  exact first_named e a hT (Nat.le_of_eq hW.symm)

theorem plain_named_second {c : ParC} {s : S} (h : plainThereB c.iU3 c.nW s = true) {U : Fork} {hh : Heard}
    (e1 : s.fork? = some U) (e2 : s.heard5? = some hh) {g : Forest.Heard} {l : List Aff}
    (e : secondAt c g hh U = some l) : ∀ f ∈ l, ∀ x ∈ f.ents.toList, x.tree = c.iU3 ∧ x.row = 0 ∧ x.idx < c.nW := by
  obtain ⟨U', hh', T, r1, r2, a, hT, hW⟩ := plain_spent h
  obtain rfl := Option.some.inj (r1.symm.trans e1)
  obtain rfl := Option.some.inj (r2.symm.trans e2)
  exact second_named e a hT (Nat.le_of_eq hW.symm)

/-- A control: no array of that number: no. -/
theorem plain_bites {iU3 nW : ℕ} {s : S} {U : Fork} (e1 : s.fork? = some U) (hn : U.trees[iU3]? = none) :
    plainThereB iU3 nW s = false := by
  cases hb : plainThereB iU3 nW s with
  | false => rfl
  | true =>
    obtain ⟨U', _, r1, _, _, T, hT, _⟩ := (plainThereB_iff iU3 nW s).1 hb
    obtain rfl := Option.some.inj (r1.symm.trans e1)
    rw [hn] at hT
    cases hT

end H2K5.Door

#print axioms H2K5.Door.plainThereB_iff
#print axioms H2K5.Door.plain_made
#print axioms H2K5.Door.plain_kept
#print axioms H2K5.Door.plain_spent
#print axioms H2K5.Door.plain_named_first
#print axioms H2K5.Door.plain_bites
