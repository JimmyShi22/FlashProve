-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/WalksO.lean: what it is for a part's reading to be made of the walks of one look; that
two such parts read one raw string if their looks agree; and that a walk does not see the entries of
a log at strings that its look does not read.

OnBytes/Slice/ByWalks.lean's head says what the first two are for, what is owed beside them and what
a look cannot express; OnBytes/Slice/WalkOff.lean's and OffSetGlue.lean's heads say what the other
four serve. They name no typed oracle and no compiler (of the library they name `Dig`, the type of a
digest; `Merkle.Shape` with its positions; and the log of the one oracle, `Trace (rom lam)`). They
stand here by themselves, over OnBytes/Slice/PartO.lean, Look.lean and AtSet.lean alone, so that a
part made with another compiler than the library's can use them without importing the library's
parts.

Main definition: `PartO.ByWalks`. Main theorems: `sameRaw_of_walks`; `firstAt_offSet`,
`walk_offSet`, `noClash_offSet`; `PartO.ByWalks.raw_offSet`.

What is not claimed. What the heads of these three files do not claim. No probability. Nothing on
any protocol, language, checker or hash function.

-/
import OnBytes.Slice.PartO
import OnBytes.Slice.Look
import OnBytes.Slice.AtSet

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Rom Compile Compile.Batch

variable {lam : ℕ} {γ γ' Sg : Type}

/-- **The part's reading is made of a look's walks**: at each place j the walk to `pos j`, then `sym
j`; then `mk`. Asked at every log, also at one in which two strings have one answer: more than
`SameRaw` needs. -/
structure PartO.ByWalks (s : PartO lam γ Sg) {Lf : Type} (k : Look lam Lf) {t : Merkle.Shape}
    (pos : ℕ → t.Pos) (sym : ℕ → Lf → Option Sg) (mk : (ℕ → Option Sg) → Raw Sg) : Prop where
  /-- the raw string under cm is `mk` of what `sym` makes of the leaves that the walks find -/
  raw_eq : ∀ σ cm, s.raw σ cm = mk fun j => (k.walk σ (pos j) cm).bind (sym j)

/-- **Two parts whose readings are made of the walks of two looks that agree read one raw string**,
under every root, off every log in which no two strings have one answer. ONE map `pos` from places
to positions and ONE way `mk` of making a raw string serve both. Asked of the looks: both read the
same strings as the same vertices; string by string and place by place, what `sym₁` makes of the
first's leaf is what `sym₂` makes of the second's. No typed oracle stands in the statement. No
probability. -/
theorem sameRaw_of_walks {s₁ : PartO lam γ Sg} {s₂ : PartO lam γ' Sg} {Lf₁ Lf₂ : Type}
    {k₁ : Look lam Lf₁} {k₂ : Look lam Lf₂} {t : Merkle.Shape} {pos : ℕ → t.Pos}
    {sym₁ : ℕ → Lf₁ → Option Sg} {sym₂ : ℕ → Lf₂ → Option Sg} {mk : (ℕ → Option Sg) → Raw Sg}
    (h₁ : s₁.ByWalks k₁ pos sym₁ mk) (h₂ : s₂.ByWalks k₂ pos sym₂ mk)
    (hn : ∀ s, k₁.node s = k₂.node s)
    (hl : ∀ j s, (k₁.leaf s).bind (sym₁ j) = (k₂.leaf s).bind (sym₂ j)) : SameRaw s₁ s₂ :=
  fun σ hσ cm => by
    rw [h₁.raw_eq, h₂.raw_eq]
    exact congrArg mk (funext fun j => walk_same k₁ k₂ _ _ hn (hl j) σ hσ (pos j) cm)

/-! ## Walks in a log without the entries at some strings -/

/-- If `view` reads no string of S, its first hit under the answer c is the same in the log and in
the log without the entries at the strings of S. -/
theorem firstAt_offSet {A : Type} (view : List Bool → Option A) (S : Finset (List Bool))
    (h : ∀ s ∈ S, view s = none) (σ : Trace (rom lam)) (c : Dig lam) :
    firstAt view (offSet S σ) c = firstAt view σ c := by
  unfold firstAt offSet
  induction σ with
  | nil => rfl
  | cons e σ ih =>
    obtain ⟨⟨⟩, s, r⟩ := e
    by_cases he : s ∈ S
    · have hf : decide (((⟨(), s, r⟩ : QA (rom lam)).2.1 : List Bool) ∉ S) = false :=
        decide_eq_false (not_not.2 he)
      rw [List.filter_cons_of_neg (by rw [hf]; exact Bool.false_ne_true), List.findSome?_cons, ih]
      have hn : (if logAns (⟨(), s, r⟩ : QA (rom lam)) = c then
          view (⟨(), s, r⟩ : QA (rom lam)).2.1 else none) = none := by
        show (if logAns (⟨(), s, r⟩ : QA (rom lam)) = c then view s else none) = none
        rw [h s he]
        exact ite_self _
      rw [hn]
    · have hf : decide (((⟨(), s, r⟩ : QA (rom lam)).2.1 : List Bool) ∉ S) = true :=
        decide_eq_true he
      rw [List.filter_cons_of_pos
          (p := fun e : QA (rom lam) => decide ((e.2.1 : List Bool) ∉ S)) hf,
        List.findSome?_cons, List.findSome?_cons, ih]

/-- **A walk does not see the entries at strings that its look reads neither as vertices nor as
leaves.** At every position under every digest it finds the same in the log and in the log without
the entries at the strings of S. No condition on the log. -/
theorem walk_offSet {Lf : Type} (k : Look lam Lf) (S : Finset (List Bool))
    (hn : ∀ s ∈ S, k.node s = none) (hl : ∀ s ∈ S, k.leaf s = none) (σ : Trace (rom lam)) :
    ∀ {t : Merkle.Shape} (p : t.Pos) (c : Dig lam), k.walk (offSet S σ) p c = k.walk σ p c
  | _, .here, c => firstAt_offSet k.leaf S hl σ c
  | _, .left p, c => by
    simp only [Look.walk, firstAt_offSet k.node S hn σ c]
    exact congrArg _ (funext fun q => walk_offSet k S hn hl σ p q.1)
  | _, .right p, c => by
    simp only [Look.walk, firstAt_offSet k.node S hn σ c]
    exact congrArg _ (funext fun q => walk_offSet k S hn hl σ p q.2)

/-- A log in which no two strings have one answer stays so without the entries at the strings of
S. -/
theorem noClash_offSet (S : Finset (List Bool)) {σ : Trace (rom lam)} (h : NoClash σ) :
    NoClash (offSet S σ) :=
  h.of_subset fun _ he => (List.mem_filter.1 he).1

/-- A part whose reading is made of a look's walks reads the same off a log without the entries at
strings that the look reads neither as a vertex nor as a leaf. -/
theorem PartO.ByWalks.raw_offSet {lam : ℕ} {γ Sg Lf : Type} {s : PartO lam γ Sg} {k : Look lam Lf}
    {t : Merkle.Shape} {pos : ℕ → t.Pos} {sym : ℕ → Lf → Option Sg}
    {mk : (ℕ → Option Sg) → Raw Sg} (h : s.ByWalks k pos sym mk) (S : Finset (List Bool))
    (hn : ∀ x ∈ S, k.node x = none) (hl : ∀ x ∈ S, k.leaf x = none) (σ : Trace (rom lam))
    (cm : Dig lam) : s.raw (offSet S σ) cm = s.raw σ cm := by
  rw [h.raw_eq, h.raw_eq]
  exact congrArg mk (funext fun j => by rw [walk_offSet k S hn hl])

end OnBytes.Slice
