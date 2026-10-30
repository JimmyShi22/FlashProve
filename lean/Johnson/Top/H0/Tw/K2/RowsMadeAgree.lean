-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2/RowsMadeAgree.lean: A YARDSTICK BESIDE K2/RowsCan.lean AND K2/RowsMade.lean: NO
BLOCK IMPORTS THIS FILE. The eight clauses are JUST the conditions under which the program's maker
switchRows returns rows; so rowsMade says, at every input, what switchRows says.
  rowsCan_some      the eight clauses hold ⇒ switchRows … returns · rowsCan_someOwn: the same of the
  description's own maker swRows (one with switchRows by rfl)
  rowsMade_some     rowsMade … = some rows ⇒ rowsCan … holds and switchRows … = some rows
  rowsCan_of_some   switchRows … returns ⇒ the eight clauses hold (the converse)
  rowsCan_iff       rowsCan … = true ⇔ switchRows … returns
  rowsMade_eq       rowsMade S old T g anew pos y = switchRows S old T g anew pos y
THE TIE TO K2's RUNNING TEXT (K2/Switch.lean's [G33]) IS rowsCan_iff WITH rowsCan_someOwn;
rowsMade_eq SERVES THE TEXT THAT CALLS rowsMade (L9/Switch.lean).
No soundness is claimed.
-/
import Johnson.Top.H0.Tw.K2.RowsMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Tw.K2
open OnBytes

/-! ### where the clauses hold the maker returns -/

theorem mapM_some {α β : Type} (f : α → Option β) : ∀ l : List α, (∀ x ∈ l,
    (f x).isSome = true) → (l.mapM f).isSome = true
  | [], _ => by simp
  | a :: l, h => by
    have ha := h a (by simp)
    have hl := mapM_some f l fun x hx => h x (by simp [hx])
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 ha
    obtain ⟨bs, hbs⟩ := Option.isSome_iff_exists.1 hl
    simp [List.mapM_cons, hb, hbs]

theorem foldlM_some {α β : Type} (f : β → α → Option β) : ∀ (l : List α) (b : β), (∀ x ∈ l, ∀ b,
    (f b x).isSome = true) → (l.foldlM f b).isSome = true
  | [], _, _ => by simp
  | a :: l, b, h => by
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 (h a (by simp) b)
    have := foldlM_some f l c fun x hx => h x (by simp [hx])
    simp [List.foldlM_cons, hc, this]

theorem bindSome {α β : Type} (x : Option α) (f : α → β) : (x.bind fun a =>
    some (f a)).isSome = x.isSome := by
  cases x <;> rfl

theorem formOn_some {o : Nat} {row : Row} (h : readsMainOf o row = true) : (switchFormOn o
    row).isSome = true := by
  unfold readsMainOf at h
  unfold switchFormOn
  rw [if_pos h]
  rfl

theorem rowsCan_some {S : Statement} {old : SingleRows} {T : SwitchTarget} {g : Nat} {anew : Array
    Nat} {pos : Positions} {y : Array E}
    (h : rowsCan S old T anew pos y = true) : (switchRows S old T g anew pos y).isSome = true := by
  simp only [rowsCan, rowsCanL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
      decide_eq_true_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have e2 : S.codes.base[old.code]? = some S.codes.base[old.code] := by simp [h2]
  have e3 : S.codes.mask[old.maskCode]? = some S.codes.mask[old.maskCode] := by simp [h3]
  have e4 : S.codes.base[T.shape.code]? = some S.codes.base[T.shape.code] := by simp [h4]
  obtain ⟨W, hW, hK⟩ : ∃ W, switchFrame S old T g anew = some W ∧
      W.kept.map (·.old) = (List.range (switchKept old).size).map fun i =>
          (switchKept old).getD i noId := by
    simp [switchFrame, e2, e3, e4, h5, guard, Function.comp_def]
  have hc : (switchCarried W old).isSome = true := by
    simp [switchCarried]
    rw [bindSome, ← Array.foldlM_toList]
    apply foldlM_some
    intro f hf r
    rw [bindSome, List.find?_isSome]
    obtain ⟨i, hi, he⟩ := List.any_eq_true.1 ((List.all_eq_true.1 h6) f hf)
    have hm : (switchKept old).getD i noId ∈ W.kept.map (·.old) := by
      rw [hK]
      exact List.mem_map.2 ⟨i, hi, rfl⟩
    obtain ⟨k, hk, hko⟩ := List.mem_map.1 hm
    exact ⟨k, hk, by rw [hko]; exact he⟩
  have hs : (switchOldSamples S W).isSome = true := by
    unfold switchOldSamples
    rw [Option.isSome_map]
    apply mapM_some
    intro k hk
    apply mapM_some
    intro sample hsm
    have hm : k.old ∈ W.kept.map (·.old) := List.mem_map.2 ⟨k, hk, rfl⟩
    rw [hK] at hm
    obtain ⟨i, hi, he⟩ := List.mem_map.1 hm
    have h7' := (List.all_eq_true.1 h7) i hi
    rw [he] at h7'
    have := formOn_some ((List.all_eq_true.1 h7') sample hsm)
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 this
    simp [hc]
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 hc
  obtain ⟨s, hs⟩ := Option.isSome_iff_exists.1 hs
  simp [switchRows, h1, hW, hc, hs, guard]
  rw [bindSome]
  apply mapM_some
  intro x hx
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 ((List.all_eq_true.1 h8) x hx)
  simp [Positions.indexOf, hi]

/-- The same of the description's own maker: the two makers are one by rfl
(Johnson/Desc/Own/SwitchRowsAgree.lean: swRows_eq). -/
theorem rowsCan_someOwn {S : Statement} {old : SingleRows} {T : SwitchTarget} {g : Nat} {anew :
    Array Nat} {pos : Positions} {y : Array E}
    (h : rowsCan S old T anew pos y = true) : (VerifiableInference.Desc.Own.swRows S old T g anew
        pos y).isSome = true :=
  rowsCan_some h

theorem rowsMade_some {S : Statement} {old : SingleRows} {T : SwitchTarget} {g : Nat} {anew : Array
    Nat} {pos : Positions} {y : Array E} {rows : List Row}
    (h : rowsMade S old T g anew pos y = some rows) : rowsCan S old T anew pos y = true ∧ switchRows
        S old T g anew pos y = some rows := by
  unfold rowsMade at h
  have e : VerifiableInference.Desc.Own.swRows S old T g anew pos y = switchRows S old T g anew pos
      y := rfl
  rw [e] at h
  split at h
  · rename_i hc
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 (rowsCan_some (g := g) hc)
    rw [hl] at h
    simp only [Option.getD_some, Option.some.injEq] at h
    exact ⟨hc, by rw [hl, h]⟩
  · cases h

/-! ### the converse -/

theorem mapM_some_inv {α β : Type} (f : α → Option β) : ∀ l : List α,
    (l.mapM f).isSome = true → ∀ x ∈ l, (f x).isSome = true
  | [], _ => by simp
  | a :: l, h => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [ha, hl] at h
      | some bs =>
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · simp [ha]
        · exact mapM_some_inv f l (by simp [hl]) x hx

theorem foldlM_some_inv {α β : Type} (f : β → α → Option β) (p : α → Bool) (hp : ∀ b x,
    (f b x).isSome = p x) :
    ∀ (l : List α) (b : β), (l.foldlM f b).isSome = true → ∀ x ∈ l, p x = true
  | [], _, _ => by simp
  | a :: l, b, h => by
    rw [List.foldlM_cons] at h
    cases ha : f b a with
    | none => simp [ha] at h
    | some c =>
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · rw [← hp b x, ha]; rfl
      · exact foldlM_some_inv f p hp l c (by simpa [ha] using h) x hx

theorem formOn_some_inv {o : Nat} {row : Row} (h : (switchFormOn o row).isSome = true) : readsMainOf
    o row = true := by
  unfold switchFormOn at h
  unfold readsMainOf
  split at h
  · assumption
  · cases h

theorem frame_inv {S : Statement} {old : SingleRows} {T : SwitchTarget} {g : Nat} {anew : Array Nat}
    {W : SwitchFrame}
    (h : switchFrame S old T g anew = some W) :
    old.code < S.codes.base.size ∧ old.maskCode < S.codes.mask.size ∧ T.shape.code <
        S.codes.base.size ∧
      (anew.size == (switchKept old).size) = true ∧
      W.kept.map (·.old) = (List.range (switchKept old).size).map fun i =>
          (switchKept old).getD i noId := by
  by_cases h2 : old.code < S.codes.base.size
  case neg => simp [switchFrame, h2] at h
  by_cases h3 : old.maskCode < S.codes.mask.size
  case neg => simp [switchFrame, h2, h3] at h
  by_cases h4 : T.shape.code < S.codes.base.size
  case neg => simp [switchFrame, h2, h3, h4] at h
  by_cases h5 : (anew.size == (switchKept old).size) = true
  case neg =>
    simp [switchFrame, h2, h3, h4, h5, guard] at h
    cases h
  refine ⟨h2, h3, h4, h5, ?_⟩
  simp [switchFrame, h2, h3, h4, h5, guard] at h
  subst h
  simp [Function.comp_def]

theorem rowsCan_of_some {S : Statement} {old : SingleRows} {T : SwitchTarget} {g : Nat} {anew :
    Array Nat} {pos : Positions} {y : Array E}
    (h : (switchRows S old T g anew pos y).isSome = true) : rowsCan S old T anew pos y = true := by
  by_cases h1 : (y.size == pos.all.size * old.rows) = true
  case neg =>
    simp [switchRows, h1, guard] at h
    cases h
  cases hW : switchFrame S old T g anew with
  | none => simp [switchRows, h1, hW, guard] at h
  | some W =>
    obtain ⟨h2, h3, h4, h5, hK⟩ := frame_inv hW
    cases hc : switchCarried W old with
    | none => simp [switchRows, h1, hW, hc, guard] at h
    | some c =>
      cases hs : switchOldSamples S W with
      | none => simp [switchRows, h1, hW, hc, hs, guard] at h
      | some s =>
        simp [switchRows, h1, hW, hc, hs, guard] at h
        rw [bindSome] at h
        have h8 : (pos.draws.toList.all fun x => (pos.all.idxOf? x).isSome) = true := by
          rw [List.all_eq_true]
          intro x hx
          have := mapM_some_inv _ _ h x hx
          rw [bindSome] at this
          exact this
        have h6 : (old.kept.toList.all fun f => (List.range (switchKept old).size).any fun i =>
            (switchKept old).getD i noId == f.oracle) = true := by
          have hc' : (switchCarried W old).isSome = true := by simp [hc]
          simp [switchCarried] at hc'
          rw [bindSome, ← Array.foldlM_toList] at hc'
          have := foldlM_some_inv _ (fun (f : KeptForm) => (W.kept.find? (fun (k : KeptPlace) =>
              k.old == f.oracle)).isSome)
            (fun b x => by rw [bindSome]) _ _ hc'
          rw [List.all_eq_true]
          intro f hf
          obtain ⟨k, hk, hko⟩ := List.find?_isSome.1 (this f hf)
          have hm : k.old ∈ W.kept.map (·.old) := List.mem_map.2 ⟨k, hk, rfl⟩
          rw [hK] at hm
          obtain ⟨i, hi, he⟩ := List.mem_map.1 hm
          exact List.any_eq_true.2 ⟨i, hi, by rw [he]; exact hko⟩
        have h7 : ((List.range (switchKept old).size).all fun i =>
            (S.oracles.getD ((switchKept old).getD i noId) default).sampleRows.toList.all
                (readsMainOf ((switchKept old).getD i noId))) = true := by
          have hs' : (switchOldSamples S W).isSome = true := by simp [hs]
          unfold switchOldSamples at hs'
          rw [Option.isSome_map] at hs'
          rw [List.all_eq_true]
          intro i hi
          have hm : (switchKept old).getD i noId ∈ W.kept.map (·.old) := by
            rw [hK]
            exact List.mem_map.2 ⟨i, hi, rfl⟩
          obtain ⟨k, hk, hko⟩ := List.mem_map.1 hm
          have hk' := mapM_some_inv _ _ hs' k hk
          rw [List.all_eq_true]
          intro sample hsm
          rw [← hko] at hsm ⊢
          have := mapM_some_inv _ _ hk' sample hsm
          apply formOn_some_inv
          cases hq : switchFormOn k.old sample with
          | none => simp [hq] at this
          | some _ => rfl
        simp only [rowsCan, rowsCanL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
            decide_eq_true_eq]
        exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem rowsCan_iff {S : Statement} {old : SingleRows} {T : SwitchTarget} {g : Nat} {anew : Array
    Nat} {pos : Positions} {y : Array E} :
    rowsCan S old T anew pos y = true ↔ (switchRows S old T g anew pos y).isSome = true :=
  ⟨rowsCan_some, rowsCan_of_some⟩

/-- **rowsMade says what switchRows says, at every input.** -/
theorem rowsMade_eq (S : Statement) (old : SingleRows) (T : SwitchTarget) (g : Nat) (anew : Array
    Nat) (pos : Positions) (y : Array E) :
    rowsMade S old T g anew pos y = switchRows S old T g anew pos y := by
  unfold rowsMade
  have e : VerifiableInference.Desc.Own.swRows S old T g anew pos y = switchRows S old T g anew pos
      y := rfl
  rw [e]
  cases hq : switchRows S old T g anew pos y with
  | some l =>
    have : rowsCan S old T anew pos y = true := rowsCan_of_some (g := g) (by simp [hq])
    simp [this]
  | none =>
    have : rowsCan S old T anew pos y = false := by
      cases hr : rowsCan S old T anew pos y with
      | false => rfl
      | true =>
        have := rowsCan_some (g := g) hr
        simp [hq] at this
    simp [this]

end Tw.K2

#print axioms Tw.K2.rowsCan_some
#print axioms Tw.K2.rowsCan_someOwn
#print axioms Tw.K2.rowsMade_some
#print axioms Tw.K2.rowsCan_of_some
#print axioms Tw.K2.rowsMade_eq
