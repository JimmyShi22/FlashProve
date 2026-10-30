-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/Look.lean: the walk down a hash tree in a log of queries to one oracle on bit
strings, for any way of reading a bit string as a vertex or as a leaf; two such ways that agree find
the same.

The bounds that OnBytes/Slice/PartO.lean joins speak of raw strings that are read off the maker's
log under a root. Each part has its own way of reading. To join them, what is read under one root
must be one thing in all (`SameRaw`). This file has the core of that, with no typed oracle in it.

A `Look` is two functions on bit strings: `node` reads a string as a vertex on two digests, or not;
`leaf` reads it as a leaf of some type, or not. `Look.walk` goes down from a digest along a position
in a tree: at a vertex it takes the first entry of the log with the wanted answer whose string
`node` reads, and goes on at its left or right digest; at the end it takes the first entry with the
wanted answer whose string `leaf` reads.

Main definitions: `Look`, `firstAt`, `Look.walk`.
Main theorem. `walk_same`: let two looks read the same strings as the same vertices, and let what g₁
makes of the first's leaves be, string by string, what g₂ makes of the second's. Then off a log in
which no two strings have one answer (`NoClash`, OnBytes/Slice/OneLog.lean), g₁ of what the first
walk finds is g₂ of what the second finds, at every position under every digest.

What this file gives a compiler whose part is to stand beside another's: if what each reads under a
root is made in ONE way (one tree shape, one map from places to positions, one length, one filling)
of what its own look's walks find, and the two looks agree as `walk_same` asks, the two read one raw
string. That step is OnBytes/Slice/WalksO.lean (`PartO.ByWalks`, `sameRaw_of_walks`). So a compiler
owes one look and one law, that what it reads is so made; and the pair owes that the looks agree.
For the library's compiler: OnBytes/Slice/SameRead.lean (`lookOf`, `extLeaf_eq_walk`). A look's two
functions see the string alone: not the position in the tree, nor a tree's number; a vertex is on
two digests.

Why `NoClash` is asked. The walk takes the first entry with the wanted answer that it can read. A
string may be a leaf that g₁ drops for the first look and no leaf at all for the second. If a second
string had the same answer, the two walks could part. At a vertex that cannot happen.

What is not claimed. That any two looks agree. What g₁ and g₂ leave out (where both give nothing)
may differ between the two sides. Nothing on any protocol, language, checker or hash function; no
probability.

-/
import OnBytes.Slice.OneLog

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Rom Compile Compile.Batch

/-! ## Lists -/

/-- The first hit along a list that was filtered and mapped. -/
theorem findSome_filterMap {E E' A : Type} (f : E → Option E') (h : E' → Option A) :
    ∀ σ : List E, (σ.filterMap f).findSome? h = σ.findSome? fun e => (f e).bind h
  | [] => rfl
  | e :: σ => by
    have ih := findSome_filterMap f h σ
    rw [List.filterMap_cons, List.findSome?_cons]
    cases he : f e with
    | none => simpa using ih
    | some e' =>
      simp only [Option.bind_some, List.findSome?_cons]
      cases h e' with
      | none => exact ih
      | some a => rfl

/-- Two ways to look for a first hit along one list give one result behind two further maps, if they
do so entry by entry and all entries that either way hits are one entry. -/
theorem findSome_bind_congr {E A₁ A₂ B : Type} (h₁ : E → Option A₁) (h₂ : E → Option A₂)
    (g₁ : A₁ → Option B) (g₂ : A₂ → Option B) :
    ∀ σ : List E, (∀ e ∈ σ, (h₁ e).bind g₁ = (h₂ e).bind g₂) →
      (∀ e ∈ σ, ∀ e' ∈ σ, ((h₁ e).isSome ∨ (h₂ e).isSome) → ((h₁ e').isSome ∨ (h₂ e').isSome) →
        e = e') →
      (σ.findSome? h₁).bind g₁ = (σ.findSome? h₂).bind g₂
  | [], _, _ => rfl
  | e :: σ, hP, hQ => by
    have ih := findSome_bind_congr h₁ h₂ g₁ g₂ σ
      (fun x hx => hP x (List.mem_cons_of_mem _ hx))
      (fun x hx y hy => hQ x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy))
    have hPe := hP e List.mem_cons_self
    rw [List.findSome?_cons, List.findSome?_cons]
    cases a : h₁ e with
    | none =>
      cases b : h₂ e with
      | none => exact ih
      | some y =>
        rw [a, b] at hPe
        have hn : σ.findSome? h₁ = none := by
          cases hx : σ.findSome? h₁ with
          | none => rfl
          | some x =>
            obtain ⟨e', he', hx'⟩ := List.exists_of_findSome?_eq_some hx
            have := hQ e List.mem_cons_self e' (List.mem_cons_of_mem _ he')
              (Or.inr (by rw [b]; rfl)) (Or.inl (by rw [hx']; rfl))
            rw [this, hx'] at a
            cases a
        show (σ.findSome? h₁).bind g₁ = (some y).bind g₂
        rw [hn]
        exact hPe
    | some x =>
      cases b : h₂ e with
      | none =>
        rw [a, b] at hPe
        have hn : σ.findSome? h₂ = none := by
          cases hy : σ.findSome? h₂ with
          | none => rfl
          | some y =>
            obtain ⟨e', he', hy'⟩ := List.exists_of_findSome?_eq_some hy
            have := hQ e List.mem_cons_self e' (List.mem_cons_of_mem _ he')
              (Or.inl (by rw [a]; rfl)) (Or.inr (by rw [hy']; rfl))
            rw [this, hy'] at b
            cases b
        show (some x).bind g₁ = (σ.findSome? h₂).bind g₂
        rw [hn]
        exact hPe
      | some y =>
        rw [a, b] at hPe
        exact hPe

/-! ## Looks and walks -/

variable {lam : ℕ}

/-- **A way of reading a bit string** as a vertex on two digests, or as a leaf of the type Lf. -/
structure Look (lam : ℕ) (Lf : Type) where
  /-- the two digests, if the string is read as a vertex -/
  node : List Bool → Option (Dig lam × Dig lam)
  /-- the leaf, if the string is read as one -/
  leaf : List Bool → Option Lf

/-- The answer in an entry of the log, as a digest. -/
def logAns (e : QA (rom lam)) : Dig lam := e.2.2

/-- What `view` makes of the first entry of the log that has the answer c and whose string `view`
reads. -/
def firstAt {A : Type} (view : List Bool → Option A) (σ : Trace (rom lam)) (c : Dig lam) :
    Option A :=
  σ.findSome? fun e => if logAns e = c then view e.2.1 else none

/-- **The walk** down from the digest c along a position in a tree, in the log σ. -/
def Look.walk {Lf : Type} (k : Look lam Lf) (σ : Trace (rom lam)) :
    {t : Merkle.Shape} → t.Pos → Dig lam → Option Lf
  | _, .here, c => firstAt k.leaf σ c
  | _, .left p, c => (firstAt k.node σ c).bind fun q => k.walk σ p q.1
  | _, .right p, c => (firstAt k.node σ c).bind fun q => k.walk σ p q.2

/-- Two views that agree string by string behind two further maps find the same behind these maps,
off a log in which no two strings have one answer. -/
theorem firstAt_same {A₁ A₂ B : Type} (v₁ : List Bool → Option A₁) (v₂ : List Bool → Option A₂)
    (g₁ : A₁ → Option B) (g₂ : A₂ → Option B) (h : ∀ s, (v₁ s).bind g₁ = (v₂ s).bind g₂)
    (σ : Trace (rom lam)) (hσ : NoClash σ) (c : Dig lam) :
    (firstAt v₁ σ c).bind g₁ = (firstAt v₂ σ c).bind g₂ := by
  unfold firstAt
  refine findSome_bind_congr _ _ _ _ σ (fun e _ => ?_) fun e he e' he' a a' => ?_
  · by_cases hc : logAns e = c
    · rw [if_pos hc, if_pos hc]
      exact h e.2.1
    · rw [if_neg hc, if_neg hc]
      rfl
  · have ans : ∀ e : QA (rom lam),
        ((if logAns e = c then v₁ e.2.1 else none).isSome ∨
          (if logAns e = c then v₂ e.2.1 else none).isSome) → logAns e = c := by
      intro e hh
      by_contra hc
      rw [if_neg hc, if_neg hc] at hh
      rcases hh with hh | hh <;> cases hh
    have ha := ans e a
    have ha' := ans e' a'
    have hstr := hσ e he e' he' (ha.trans ha'.symm)
    obtain ⟨v, s, r⟩ := e
    obtain ⟨v', s', r'⟩ := e'
    cases v
    cases v'
    have e1 : s = s' := hstr
    have e2 : r = r' := ha.trans ha'.symm
    rw [e1, e2]

/-- **Two looks that agree find the same.** Asked: both read the same strings as the same vertices;
string by string, what g₁ makes of the first's leaf is what g₂ makes of the second's; no two strings
of the log have one answer. Then at every position under every digest g₁ of what the first walk
finds is g₂ of what the second finds; where the one gives nothing, so does the other. The leaves
that are found may differ. No probability. -/
theorem walk_same {Lf₁ Lf₂ B : Type} (k₁ : Look lam Lf₁) (k₂ : Look lam Lf₂) (g₁ : Lf₁ → Option B)
    (g₂ : Lf₂ → Option B) (hn : ∀ s, k₁.node s = k₂.node s)
    (hl : ∀ s, (k₁.leaf s).bind g₁ = (k₂.leaf s).bind g₂) (σ : Trace (rom lam))
    (hσ : NoClash σ) :
    ∀ {t : Merkle.Shape} (p : t.Pos) (c : Dig lam),
      (k₁.walk σ p c).bind g₁ = (k₂.walk σ p c).bind g₂
  | _, .here, c => firstAt_same _ _ g₁ g₂ hl σ hσ c
  | _, .left p, c => by
    have e : k₁.node = k₂.node := funext hn
    simp only [Look.walk, e, Option.bind_assoc]
    exact congrArg _ (funext fun q => walk_same k₁ k₂ g₁ g₂ hn hl σ hσ p q.1)
  | _, .right p, c => by
    have e : k₁.node = k₂.node := funext hn
    simp only [Look.walk, e, Option.bind_assoc]
    exact congrArg _ (funext fun q => walk_same k₁ k₂ g₁ g₂ hn hl σ hσ p q.2)

end OnBytes.Slice
