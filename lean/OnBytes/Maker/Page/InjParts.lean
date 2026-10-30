-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/InjParts.lean: a plain part of a file's rounds comes back from what
OnBytes/Maker/Page/Fill.lean reads off it (`partOf`).

One definition that computes, statements and proofs, over OnBytes/Maker/Page/InjRows.lean.

Main names:
  `cases_in`: a plain part of a file's rounds is one of chain 1's, chain 2's or chain 3's.
  `partOf_front0`, `partOf_join0`, `partOf_seam0`: the three parts that are read as nothing.
  `ofSaid_row`, `ofSaid_join`, `ofSaid_seam`: tools on `PartJ.ofSaid`.
  `partOf_row`: which plain parts are read as a written round's.
  `partOf_row_inj`: two plain parts that are read as the same typed round's, with lists of roots
    that fit, the same bytes and the same nonce, are the same, and so are the lists.
  `partOf_front_eq`, `partOf_join_eq`, `partOf_seam_eq`: which plain part is read as a silent
    round's message p.
  `isSlot`: the test "the joining round's part of a slot". `isSlot_eq`: one plain part passes.
    `isSlot_in`: it passes.
Under "there is" stand: in `cases_in` and `partOf_row`: a plain part of the chain's own rounds,
fixed by its equation to z; what it says, fixed by `saidLo` or `saidSh` at it; in `ofSaid_row`: s,
fixed by o = some s.
The tests at the interface's plain parts and the laws at `fillJ`: OnBytes/Maker/Page/FitAt.lean.

What is not claimed. That a verifier's queries pass any test. Nothing on any hash. Nothing on
soundness.


-/
import OnBytes.Maker.Page.InjRows
import OnBytes.Maker.Page.FillLine

set_option autoImplicit false

namespace OnBytes.Maker.Page

open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Joined Rom
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol
open _root_.Run _root_.Run.PQ _root_.Compile.Joined
open TypedOracleCompiler.Run.PQ (toRoots)

section
variable (C : CK) (D : WholeD) {TF TJ T3 : Type} (tF : TF) (tJ : TJ) (t3 : T3)

/-- A plain part of a file's rounds is one of chain 1's, chain 2's or chain 3's rounds. -/
theorem cases_in (z : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann) :
    (∃ y, z = in₁ C D tF tJ t3 y) ∨ (∃ y, z = in₂ C D tF tJ t3 y) ∨
      ∃ y, z = in₃ C D tF tJ t3 y := by
  cases h : splitPB (s := (chainsOf C D tF tJ t3).c₁)
      (u := (chainsOf C D tF tJ t3).c₂ ++ (chainsOf C D tF tJ t3).c₃) (A := (chainsOf C D tF tJ
          t3).A₁)
      (B := RoundSplits.app (chainsOf C D tF tJ t3).A₂ (chainsOf C D tF tJ t3).A₃) z with
  | inl y =>
    exact Or.inl ⟨y, splitPB_inj (s := (chainsOf C D tF tJ t3).c₁)
      (u := (chainsOf C D tF tJ t3).c₂ ++ (chainsOf C D tF tJ t3).c₃) (A := (chainsOf C D tF tJ
          t3).A₁)
      (B := RoundSplits.app (chainsOf C D tF tJ t3).A₂ (chainsOf C D tF tJ t3).A₃) z _
      (h.trans (splitPB_left y).symm)⟩
  | inr y' =>
    cases h2 : splitPB (s := (chainsOf C D tF tJ t3).c₂) (u := (chainsOf C D tF tJ t3).c₃)
      (A := (chainsOf C D tF tJ t3).A₂) (B := (chainsOf C D tF tJ t3).A₃) y' with
    | inl y =>
      have e : y' = PB.left y := splitPB_inj (s := (chainsOf C D tF tJ t3).c₂)
        (u := (chainsOf C D tF tJ t3).c₃) (A := (chainsOf C D tF tJ t3).A₂) (B := (chainsOf C D tF
            tJ t3).A₃) y' _
        (h2.trans (splitPB_left y).symm)
      refine Or.inr (Or.inl ⟨y, splitPB_inj (s := (chainsOf C D tF tJ t3).c₁)
        (u := (chainsOf C D tF tJ t3).c₂ ++ (chainsOf C D tF tJ t3).c₃) (A := (chainsOf C D tF tJ
            t3).A₁)
        (B := RoundSplits.app (chainsOf C D tF tJ t3).A₂ (chainsOf C D tF tJ t3).A₃) z _ (h.trans ?_)⟩)
      rw [e]
      exact (splitPB_right _).symm
    | inr y =>
      have e : y' = PB.right y := splitPB_inj (s := (chainsOf C D tF tJ t3).c₂)
        (u := (chainsOf C D tF tJ t3).c₃) (A := (chainsOf C D tF tJ t3).A₂) (B := (chainsOf C D tF
            tJ t3).A₃) y' _
        (h2.trans (splitPB_right y).symm)
      refine Or.inr (Or.inr ⟨y, splitPB_inj (s := (chainsOf C D tF tJ t3).c₁)
        (u := (chainsOf C D tF tJ t3).c₂ ++ (chainsOf C D tF tJ t3).c₃) (A := (chainsOf C D tF tJ
            t3).A₁)
        (B := RoundSplits.app (chainsOf C D tF tJ t3).A₂ (chainsOf C D tF tJ t3).A₃) z _ (h.trans ?_)⟩)
      rw [e]
      exact (splitPB_right _).symm

theorem partOf_front0 (u : Unit) :
    partOf C D tF tJ t3 (in₁ C D tF tJ t3 (.inl (.inl u))) = .nothing := by
  unfold partOf in₁
  rw [splitPB_left]

theorem partOf_join0 (u : Unit) :
    partOf C D tF tJ t3 (in₂ C D tF tJ t3 (.inl (.inr u))) = .nothing := by
  unfold partOf in₂
  rw [splitPB_right]
  simp only
  rw [splitPB_left]

theorem partOf_seam0 (u : Unit) :
    partOf C D tF tJ t3 (in₃ C D tF tJ t3 (.inl (.inl u))) = .nothing := by
  unfold partOf in₃
  rw [splitPB_right]
  simp only
  rw [splitPB_right]

/-- What `PartJ.ofSaid` says where it is a written round's. -/
theorem ofSaid_row (a : ℕ) (o : Option Said) (i : ℕ) (m : List ByteArray → ByteArray) (n : ℕ)
    (h : (PartJ.ofSaid a o : PartJ TF TJ T3) = .row i m n) :
    ∃ s, o = some s ∧ i = a + 1 + s.k ∧ m = s.msg ∧ n = s.nonce := by
  cases o with
  | none => cases h
  | some s =>
    have h1 : (PartJ.row (a + 1 + s.k) s.msg s.nonce : PartJ TF TJ T3) = .row i m n := h
    injection h1 with e1 e2 e3
    exact ⟨s, rfl, e1.symm, e2.symm, e3.symm⟩

theorem ofSaid_join (a : ℕ) (o : Option Said) (p : TJ) :
    (PartJ.ofSaid a o : PartJ TF TJ T3) ≠ .join p := by
  cases o <;> exact fun h => by cases h

theorem ofSaid_seam (a : ℕ) (o : Option Said) (p : T3) :
    (PartJ.ofSaid a o : PartJ TF TJ T3) ≠ .seam p := by
  cases o <;> exact fun h => by cases h

/-- **Which plain parts are read as a written round's.** -/
theorem partOf_row (z : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann)
    (i : ℕ) (m : List ByteArray → ByteArray) (n : ℕ) (h : partOf C D tF tJ t3 z = .row i m n) :
    (∃ w s, z = in₁ C D tF tJ t3 (.inr w) ∧ saidLo C D.ds₁ w = some s ∧ i = 0 + 1 + s.k ∧
      m = s.msg ∧ n = s.nonce) ∨
    (∃ w s, z = in₂ C D tF tJ t3 (.inr w) ∧ saidSh C D.ds₂ w = some s ∧
      i = D.ds₁.length + 1 + 1 + s.k ∧ m = s.msg ∧ n = s.nonce) ∨
    ∃ w s, z = in₃ C D tF tJ t3 (.inr w) ∧ saidLo C D.ds₃ w = some s ∧
      i = D.ds₁.length + D.ds₂.length + 2 + 1 + s.k ∧ m = s.msg ∧ n = s.nonce := by
  rcases cases_in C D tF tJ t3 z with ⟨y, rfl⟩ | ⟨y, rfl⟩ | ⟨y, rfl⟩
  · obtain ⟨y, rfl⟩ : ∃ x : (Unit ⊕ TF) ⊕ PlainPart (uLT C D.ds₁) (RoundSplits.allLocal (uLT C D.ds₁)), x = y :=
      ⟨y, rfl⟩
    rcases y with (u | p) | w
    · replace h := (partOf_front0 C D tF tJ t3 _).symm.trans h
      cases h
    · replace h := (partOf_front C D tF tJ t3 _).symm.trans h
      cases h
    · replace h := (partOf_one C D tF tJ t3 _).symm.trans h
      obtain ⟨s, hs, a1, a2, a3⟩ := ofSaid_row _ _ _ _ _ h
      exact Or.inl ⟨w, s, rfl, hs, a1, a2, a3⟩
  · obtain ⟨y, rfl⟩ : ∃ x : (TJ ⊕ Unit) ⊕ PlainPart (uLT C D.ds₂) (RoundSplits.const (RAnn.ofShared .sh) (uLT C
                    D.ds₂)), x = y := ⟨y, rfl⟩
    rcases y with (p | u) | w
    · replace h := (partOf_join C D tF tJ t3 _).symm.trans h
      cases h
    · replace h := (partOf_join0 C D tF tJ t3 _).symm.trans h
      cases h
    · replace h := (partOf_two C D tF tJ t3 _).symm.trans h
      obtain ⟨s, hs, a1, a2, a3⟩ := ofSaid_row _ _ _ _ _ h
      exact Or.inr (Or.inl ⟨w, s, rfl, hs, a1, a2, a3⟩)
  · obtain ⟨y, rfl⟩ : ∃ x : (Unit ⊕ T3) ⊕ PlainPart (uLT C D.ds₃) (RoundSplits.allLocal (uLT C D.ds₃)), x = y :=
      ⟨y, rfl⟩
    rcases y with (u | p) | w
    · replace h := (partOf_seam0 C D tF tJ t3 _).symm.trans h
      cases h
    · replace h := (partOf_seam C D tF tJ t3 _).symm.trans h
      cases h
    · replace h := (partOf_three C D tF tJ t3 _).symm.trans h
      obtain ⟨s, hs, a1, a2, a3⟩ := ofSaid_row _ _ _ _ _ h
      exact Or.inr (Or.inr ⟨w, s, rfl, hs, a1, a2, a3⟩)

/-- **A written round's plain part and roots come back.** -/
theorem partOf_row_inj (rt rt' : List (Dig 256))
    (z z' : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann) (i : ℕ)
    (m m' : List ByteArray → ByteArray) (n n' : ℕ) (h : partOf C D tF tJ t3 z = .row i m n)
    (h' : partOf C D tF tJ t3 z' = .row i m' n')
    (hf : ∀ d, rdAt D i = some d →
      (toRoots d.items rt).isSome = true ∧ (toRoots d.items rt').isSome = true)
    (em : m (rt.map digToBytes) = m' (rt'.map digToBytes)) (en : n = n') : rt = rt' ∧ z = z' := by
  rcases partOf_row C D tF tJ t3 z i m n h with ⟨w, s, rfl, hs, hi, rfl, rfl⟩ |
      ⟨w, s, rfl, hs, hi, rfl, rfl⟩ | ⟨w, s, rfl, hs, hi, rfl, rfl⟩ <;>
    rcases partOf_row C D tF tJ t3 z' i m' n' h' with ⟨w', s', rfl, hs', hi', rfl, rfl⟩ |
      ⟨w', s', rfl, hs', hi', rfl, rfl⟩ | ⟨w', s', rfl, hs', hi', rfl, rfl⟩
  · have l := saidLo_lt C _ _ _ hs
    obtain ⟨a, b⟩ := saidLo_inj C rt rt' _ w w' s s' hs hs' (by omega)
      (fun d hd => hf d (by rw [hi, rdAt_one D s.k l]; exact hd)) em en
    exact ⟨a, by rw [b]⟩
  · have l := saidLo_lt C _ _ _ hs
    omega
  · have l := saidLo_lt C _ _ _ hs
    omega
  · have l := saidLo_lt C _ _ _ hs'
    omega
  · have l := saidSh_lt C _ _ _ hs
    obtain ⟨a, b⟩ := saidSh_inj C rt rt' _ w w' s s' hs hs' (by omega)
      (fun d hd => hf d (by rw [hi, rdAt_two D s.k l]; exact hd)) em en
    exact ⟨a, by rw [b]⟩
  · have l := saidSh_lt C _ _ _ hs
    omega
  · have l := saidLo_lt C _ _ _ hs'
    omega
  · have l := saidSh_lt C _ _ _ hs'
    omega
  · obtain ⟨a, b⟩ := saidLo_inj C rt rt' _ w w' s s' hs hs' (by omega)
      (fun d hd => hf d (by rw [hi, rdAt_three D s.k]; exact hd)) em en
    exact ⟨a, by rw [b]⟩

/-- Which plain part is read as the front round's message p. -/
theorem partOf_front_eq (z : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann) (p : TF)
    (h : partOf C D tF tJ t3 z = .front p) : z = in₁ C D tF tJ t3 (.inl (.inr p)) := by
  rcases cases_in C D tF tJ t3 z with ⟨y, rfl⟩ | ⟨y, rfl⟩ | ⟨y, rfl⟩
  · obtain ⟨y, rfl⟩ : ∃ x : (Unit ⊕ TF) ⊕ PlainPart (uLT C D.ds₁) (RoundSplits.allLocal (uLT C D.ds₁)), x = y :=
      ⟨y, rfl⟩
    rcases y with (u | q) | w
    · replace h := (partOf_front0 C D tF tJ t3 _).symm.trans h
      cases h
    · replace h := (partOf_front C D tF tJ t3 _).symm.trans h
      injection h with e
      rw [e]
      rfl
    · replace h := (partOf_one C D tF tJ t3 _).symm.trans h
      exact absurd h (ofSaid_ne_front _ _ _)
  · obtain ⟨y, rfl⟩ : ∃ x : (TJ ⊕ Unit) ⊕ PlainPart (uLT C D.ds₂) (RoundSplits.const (RAnn.ofShared .sh) (uLT C
                    D.ds₂)), x = y := ⟨y, rfl⟩
    rcases y with (q | u) | w
    · replace h := (partOf_join C D tF tJ t3 _).symm.trans h
      cases h
    · replace h := (partOf_join0 C D tF tJ t3 _).symm.trans h
      cases h
    · replace h := (partOf_two C D tF tJ t3 _).symm.trans h
      exact absurd h (ofSaid_ne_front _ _ _)
  · obtain ⟨y, rfl⟩ : ∃ x : (Unit ⊕ T3) ⊕ PlainPart (uLT C D.ds₃) (RoundSplits.allLocal (uLT C D.ds₃)), x = y :=
      ⟨y, rfl⟩
    rcases y with (u | q) | w
    · replace h := (partOf_seam0 C D tF tJ t3 _).symm.trans h
      cases h
    · replace h := (partOf_seam C D tF tJ t3 _).symm.trans h
      cases h
    · replace h := (partOf_three C D tF tJ t3 _).symm.trans h
      exact absurd h (ofSaid_ne_front _ _ _)

/-- Which plain part is read as the joining round's message p. -/
theorem partOf_join_eq (z : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann) (p : TJ)
    (h : partOf C D tF tJ t3 z = .join p) : z = in₂ C D tF tJ t3 (.inl (.inl p)) := by
  rcases cases_in C D tF tJ t3 z with ⟨y, rfl⟩ | ⟨y, rfl⟩ | ⟨y, rfl⟩
  · obtain ⟨y, rfl⟩ : ∃ x : (Unit ⊕ TF) ⊕ PlainPart (uLT C D.ds₁) (RoundSplits.allLocal (uLT C D.ds₁)), x = y :=
      ⟨y, rfl⟩
    rcases y with (u | q) | w
    · replace h := (partOf_front0 C D tF tJ t3 _).symm.trans h
      cases h
    · replace h := (partOf_front C D tF tJ t3 _).symm.trans h
      cases h
    · replace h := (partOf_one C D tF tJ t3 _).symm.trans h
      exact absurd h (ofSaid_join _ _ _)
  · obtain ⟨y, rfl⟩ : ∃ x : (TJ ⊕ Unit) ⊕ PlainPart (uLT C D.ds₂) (RoundSplits.const (RAnn.ofShared .sh) (uLT C
                    D.ds₂)), x = y := ⟨y, rfl⟩
    rcases y with (q | u) | w
    · replace h := (partOf_join C D tF tJ t3 _).symm.trans h
      injection h with e
      rw [e]
      rfl
    · replace h := (partOf_join0 C D tF tJ t3 _).symm.trans h
      cases h
    · replace h := (partOf_two C D tF tJ t3 _).symm.trans h
      exact absurd h (ofSaid_join _ _ _)
  · obtain ⟨y, rfl⟩ : ∃ x : (Unit ⊕ T3) ⊕ PlainPart (uLT C D.ds₃) (RoundSplits.allLocal (uLT C D.ds₃)), x = y :=
      ⟨y, rfl⟩
    rcases y with (u | q) | w
    · replace h := (partOf_seam0 C D tF tJ t3 _).symm.trans h
      cases h
    · replace h := (partOf_seam C D tF tJ t3 _).symm.trans h
      cases h
    · replace h := (partOf_three C D tF tJ t3 _).symm.trans h
      exact absurd h (ofSaid_join _ _ _)

/-- Which plain part is read as the seam's message p. -/
theorem partOf_seam_eq (z : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann) (p : T3)
    (h : partOf C D tF tJ t3 z = .seam p) : z = in₃ C D tF tJ t3 (.inl (.inr p)) := by
  rcases cases_in C D tF tJ t3 z with ⟨y, rfl⟩ | ⟨y, rfl⟩ | ⟨y, rfl⟩
  · obtain ⟨y, rfl⟩ : ∃ x : (Unit ⊕ TF) ⊕ PlainPart (uLT C D.ds₁) (RoundSplits.allLocal (uLT C D.ds₁)), x = y :=
      ⟨y, rfl⟩
    rcases y with (u | q) | w
    · replace h := (partOf_front0 C D tF tJ t3 _).symm.trans h
      cases h
    · replace h := (partOf_front C D tF tJ t3 _).symm.trans h
      cases h
    · replace h := (partOf_one C D tF tJ t3 _).symm.trans h
      exact absurd h (ofSaid_seam _ _ _)
  · obtain ⟨y, rfl⟩ : ∃ x : (TJ ⊕ Unit) ⊕ PlainPart (uLT C D.ds₂) (RoundSplits.const (RAnn.ofShared .sh) (uLT C
                    D.ds₂)), x = y := ⟨y, rfl⟩
    rcases y with (q | u) | w
    · replace h := (partOf_join C D tF tJ t3 _).symm.trans h
      cases h
    · replace h := (partOf_join0 C D tF tJ t3 _).symm.trans h
      cases h
    · replace h := (partOf_two C D tF tJ t3 _).symm.trans h
      exact absurd h (ofSaid_seam _ _ _)
  · obtain ⟨y, rfl⟩ : ∃ x : (Unit ⊕ T3) ⊕ PlainPart (uLT C D.ds₃) (RoundSplits.allLocal (uLT C D.ds₃)), x = y :=
      ⟨y, rfl⟩
    rcases y with (u | q) | w
    · replace h := (partOf_seam0 C D tF tJ t3 _).symm.trans h
      cases h
    · replace h := (partOf_seam C D tF tJ t3 _).symm.trans h
      injection h with e
      rw [e]
      rfl
    · replace h := (partOf_three C D tF tJ t3 _).symm.trans h
      exact absurd h (ofSaid_seam _ _ _)

/-- The test: the joining round's part of a slot. -/
def isSlot (z : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann) : Bool :=
  match splitPB (s := (chainsOf C D tF tJ t3).c₁)
      (u := (chainsOf C D tF tJ t3).c₂ ++ (chainsOf C D tF tJ t3).c₃) (A := (chainsOf C D tF tJ
          t3).A₁)
      (B := RoundSplits.app (chainsOf C D tF tJ t3).A₂ (chainsOf C D tF tJ t3).A₃) z with
  | .inl _ => false
  | .inr z' =>
    match splitPB (s := (chainsOf C D tF tJ t3).c₂) (u := (chainsOf C D tF tJ t3).c₃)
      (A := (chainsOf C D tF tJ t3).A₂) (B := (chainsOf C D tF tJ t3).A₃) z' with
    | .inl z₂ =>
      match (z₂ : (TJ ⊕ Unit) ⊕ PlainPart (uLT C D.ds₂) (RoundSplits.const (RAnn.ofShared .sh) (uLT C D.ds₂)))
          with
      | .inl (.inr _) => true
      | _ => false
    | .inr _ => false

/-- **One plain part passes that test.** -/
theorem isSlot_eq (z : PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann)
    (h : isSlot C D tF tJ t3 z = true) : z = in₂ C D tF tJ t3 (.inl (.inr ())) := by
  rcases cases_in C D tF tJ t3 z with ⟨y, rfl⟩ | ⟨y, rfl⟩ | ⟨y, rfl⟩
  · unfold isSlot in₁ at h
    rw [splitPB_left] at h
    cases h
  · obtain ⟨y, rfl⟩ : ∃ x : (TJ ⊕ Unit) ⊕ PlainPart (uLT C D.ds₂) (RoundSplits.const (RAnn.ofShared .sh) (uLT C
                    D.ds₂)), x = y := ⟨y, rfl⟩
    unfold isSlot in₂ at h
    rw [splitPB_right] at h
    simp only at h
    rw [splitPB_left] at h
    rcases y with (q | u) | w
    · cases h
    · rfl
    · cases h
  · unfold isSlot in₃ at h
    rw [splitPB_right] at h
    simp only at h
    rw [splitPB_right] at h
    cases h

/-- It passes. -/
theorem isSlot_in : isSlot C D tF tJ t3 (in₂ C D tF tJ t3 (.inl (.inr ()))) = true := by
  unfold isSlot in₂
  rw [splitPB_right]
  simp only
  rw [splitPB_left]

end

end OnBytes.Maker.Page
