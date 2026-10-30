-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/CodingImpl.lean: the family of oracles of the compiled scheme with batches over a single oracle
on strings, in which a point of a real oracle is written as its own code, with nothing in front.

Definitions, theorems. Generic in the code; all data compute (no definition here is marked as
without code).
A point is an oracle's name, a query to it and the number of a block of the answer (`Pts`,
Compile/Batch/ImplOf.lean). The real points (`RealPts`) are those of `leaf`, `node`, `rleaf`,
`rnode`, `fb` and `g`; the ghost points (`GhostPts`) those of the names `fbw`, which no algorithm of
the scheme asks (Compile/Batch/Oracles.lean); the spare strings are the points of the oracle
`other`. `OracleCoding` (Rom/Family.lean) has the number of blocks of each answer and a bijection between
points and all bit strings.

Why: Compile/Batch/ImplOf.lean builds such a family (`OracleCoding`) from a code c of the typed points of
the real oracles; there a point is written true :: c.put ... A format that fixes the oracle's
strings to the byte leaves no room for that bit. Here the same construction is made with the hotel
of Run/HotelEsc.lean: an escape e, a string with which no code begins, makes room for the spare
strings.

Main names:
  `codeEquivE`, `implE lam K L c cG e he hp : OracleCoding (spec lam K L) lam`.
  `codeE_real`: the string of a real point is c.put of it (by definition).
  `codeE_other`: a spare string is written as itself unless it is copies of e and then a code, or is
    of the form that makes room for a ghost point.
  `implE_leaf`, `implE_node`: one block for a leaf, one for a node (what the top theorems ask of an
    encoding).
  `implA lam K L c e he hp`: the same from one code c of the real and the ghost points together,
    with one hotel. Why: in `implE` the ghost points get their room among the spare strings by
    Rom/Hotel.lean, so that a spare string of the form false .. false true (a ghost point's code) is
    moved. Whether a given string of the format is of that form depends on the ghost points' code.
    In `implA` a spare string is written as itself under one condition, which can be read off its
    first bytes: it is no code, and does not begin with the escape (`codeA_other`, `freeE_of`). So
    the calls of the hash that no typed query of the verifier makes (a parser's calls) are queries
    to the spare oracle at the format's own strings.
In which order the blocks of a chain answer stand in the format is no matter to `implE` and `implA`:
a point of a chain query is (protocol, query, number of a block), and c.put may write any block of
the format for it, as long as it stays a code.
  `blockAt work K` is the order that the format in hand has. The typed answer is K blocks of
    verifier message and then the chain's next value. The format has the next value first, or, in a
    round with work, second after the test block, which is taken to be the first of the K (at K = 0
    there is no such block, and the one number stays 0).

Notation:
  `lam`: the bits of a digest or a block (`Dig`, Iop/Wire.lean);
  `L`: an interface (`BatchProtocol`, Iop/Batch.lean);
  `spec lam K L`: the family of oracles of the compiled scheme with batches
    (Compile/Batch/Oracles.lean);
  `StrCode A`: an explicit injective code with a parser (Rom/Hotel.lean);
  `cG`: such a code of the ghost points (`GhostPts`);
  `cG.free s`: s is not of the form false^k ++ true :: put a (Rom/Hotel.lean);
  `c.freeE e he s`: s is not copies of the escape and then a code (Run/HotelEsc.lean).

Limits: this file does not say which code; which escape; that the single oracle is any hash.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Compile.Batch.ImplOf
import Run.HotelEsc

set_option autoImplicit false

namespace Compile.Batch
open Iop Rom

variable {I X : Type}

/-- How a point is written as a string. -/
def codeEquivE (lam K : ℕ) (L : BatchProtocol I X) (c : StrCode (RealPts lam K L))
    (cG : StrCode (GhostPts lam K L)) (e : List Bool) (he : e ≠ []) (hp : ∀ a t, c.put a ≠ e ++ t) :
    Pts lam K L ≃ List Bool :=
  (ptsEquiv lam K L).trans ((Equiv.sumCongr (Equiv.refl _) cG.hotel).trans (c.hotelE e he hp))

/-- The family over one oracle. -/
def implE (lam K : ℕ) (L : BatchProtocol I X) (c : StrCode (RealPts lam K L))
    (cG : StrCode (GhostPts lam K L)) (e : List Bool) (he : e ≠ []) (hp : ∀ a t, c.put a ≠ e ++ t) :
    OracleCoding (spec lam K L) lam where
  blocks := blk K
  rng := rngEquiv lam K
  code := fun o q j => codeEquivE lam K L c cG e he hp ⟨o, q, j⟩
  inv := (codeEquivE lam K L c cG e he hp).symm
  inv_code := fun x => (codeEquivE lam K L c cG e he hp).symm_apply_apply x
  code_inv := fun s => (codeEquivE lam K L c cG e he hp).apply_symm_apply s

section
variable (lam K : ℕ) (L : BatchProtocol I X) (c : StrCode (RealPts lam K L)) (cG : StrCode (GhostPts lam K L))
  (e : List Bool) (he : e ≠ []) (hp : ∀ a t, c.put a ≠ e ++ t)

/-- The string of a real point is its code. -/
theorem codeE_real (x : RealPts lam K L) :
    codeEquivE lam K L c cG e he hp (ptsOf lam K L (.inl x)) = c.put x := by
  rcases x with (q | (q | (q | (q | (⟨t, q, j⟩ | ⟨t, q⟩))))) <;> rfl

theorem codeE_leaf (q : LeafIn L) (j : Fin 1) :
    (implE lam K L c cG e he hp).code .leaf q j = c.put (.inl q) := rfl

theorem codeE_node (q : Bits × Bits) (j : Fin 1) :
    (implE lam K L c cG e he hp).code .node q j = c.put (.inr (.inl q)) := rfl

theorem codeE_fb (t : Tag) (q : FbIn lam L t) (j : Fin (K + 1)) :
    (implE lam K L c cG e he hp).code (.fb t) q j =
      c.put (.inr (.inr (.inr (.inr (.inl ⟨t, q, j⟩))))) := rfl

theorem codeE_g (t : Tag) (q : JoiningRoundQuery lam L t) (j : Fin 1) :
    (implE lam K L c cG e he hp).code (.g t) q j =
      c.put (.inr (.inr (.inr (.inr (.inr ⟨t, q⟩))))) := rfl

/-- A spare string is written as itself, unless room had to be made at it (`hG`, `hf`; `he`, `hp`
are those of `implE`). -/
theorem codeE_other (s : List Bool) (j : Fin 1)
    (hG : cG.free s = true) (hf : c.freeE e he s = true) :
    (implE lam K L c cG e he hp).code .other s j = s := by
  show c.hotelE e he hp (.inr (cG.enc (.inr s))) = s
  rw [show cG.enc (.inr s) = s from if_pos hG]
  exact c.hotelE_free e he hp s hf

theorem implE_leaf : (implE lam K L c cG e he hp).blocks .leaf = 1 := rfl

theorem implE_node : (implE lam K L c cG e he hp).blocks .node = 1 := rfl

end

/-! ## The same with the ghost points on the code's side -/

/-- Real and ghost points together. -/
abbrev AllPts (lam K : ℕ) (L : BatchProtocol I X) : Type := RealPts lam K L ⊕ GhostPts lam K L

/-- How a point is written as a string, from one code of the real and the ghost points. -/
def codeEquivA (lam K : ℕ) (L : BatchProtocol I X) (c : StrCode (AllPts lam K L)) (e : List Bool)
    (he : e ≠ []) (hp : ∀ a t, c.put a ≠ e ++ t) : Pts lam K L ≃ List Bool :=
  (ptsEquiv lam K L).trans ((Equiv.sumAssoc _ _ _).symm.trans (c.hotelE e he hp))

/-- The family over one oracle, one hotel. -/
def implA (lam K : ℕ) (L : BatchProtocol I X) (c : StrCode (AllPts lam K L)) (e : List Bool)
    (he : e ≠ []) (hp : ∀ a t, c.put a ≠ e ++ t) : OracleCoding (spec lam K L) lam where
  blocks := blk K
  rng := rngEquiv lam K
  code := fun o q j => codeEquivA lam K L c e he hp ⟨o, q, j⟩
  inv := (codeEquivA lam K L c e he hp).symm
  inv_code := fun x => (codeEquivA lam K L c e he hp).symm_apply_apply x
  code_inv := fun s => (codeEquivA lam K L c e he hp).apply_symm_apply s

section
variable (lam K : ℕ) (L : BatchProtocol I X) (c : StrCode (AllPts lam K L)) (e : List Bool)
  (he : e ≠ []) (hp : ∀ a t, c.put a ≠ e ++ t)

theorem codeA_leaf (q : LeafIn L) (j : Fin 1) :
    (implA lam K L c e he hp).code .leaf q j = c.put (.inl (.inl q)) := rfl

theorem codeA_node (q : Bits × Bits) (j : Fin 1) :
    (implA lam K L c e he hp).code .node q j = c.put (.inl (.inr (.inl q))) := rfl

theorem codeA_fb (t : Tag) (q : FbIn lam L t) (j : Fin (K + 1)) :
    (implA lam K L c e he hp).code (.fb t) q j =
      c.put (.inl (.inr (.inr (.inr (.inr (.inl ⟨t, q, j⟩)))))) := rfl

/-- A spare string is written as itself, unless it is copies of the escape and then a code: one
condition (`hf`; `he`, `hp` are those of `implA`). -/
theorem codeA_other (s : List Bool) (j : Fin 1) (hf : c.freeE e he s = true) :
    (implA lam K L c e he hp).code .other s j = s :=
  c.hotelE_free e he hp s hf

/-- A string that is no code and does not begin with the escape is free. -/
theorem freeE_of (s : List Bool) (h : c.parse s = none) (hs : StrCode.strip e s = none) :
    c.freeE e he s = true :=
  StrCode.freeE_none he h hs

theorem implA_leaf : (implA lam K L c e he hp).blocks .leaf = 1 := rfl

theorem implA_node : (implA lam K L c e he hp).blocks .node = 1 := rfl

end

/-- The number, in the format's row of blocks, of the typed block j of a chain answer, if 0 < K or
the round has no work (`blockNo_eq`, Run/CodingPut.lean). -/
def blockTo : (work : Bool) → (K : ℕ) → Fin (K + 1) → Fin (K + 1)
  | false, K, j => if _h : j.val = K then ⟨0, Nat.succ_pos K⟩ else ⟨j.val + 1, by omega⟩
  | true, 0, j => j
  | true, K + 1, j =>
    if _h : j.val = K + 1 then ⟨1, by omega⟩
    else if _h0 : j.val = 0 then ⟨0, by omega⟩
    else ⟨j.val + 1, by omega⟩

/-- The typed block that `blockTo` sends to the number b. -/
def blockOf : (work : Bool) → (K : ℕ) → Fin (K + 1) → Fin (K + 1)
  | false, K, b => if _h : b.val = 0 then ⟨K, by omega⟩ else ⟨b.val - 1, by omega⟩
  | true, 0, b => b
  | true, K + 1, b =>
    if _h : b.val = 0 then ⟨0, by omega⟩
    else if _h1 : b.val = 1 then ⟨K + 1, by omega⟩
    else ⟨b.val - 1, by omega⟩

theorem blockOf_blockTo :
    ∀ (work : Bool) (K : ℕ) (j : Fin (K + 1)), blockOf work K (blockTo work K j) = j
  | false, K, ⟨j, hj⟩ => by
      apply Fin.ext
      simp only [blockTo, blockOf]
      split_ifs <;> simp_all
  | true, 0, _ => rfl
  | true, K + 1, ⟨j, hj⟩ => by
      apply Fin.ext
      simp only [blockTo, blockOf]
      split_ifs <;> simp_all

theorem blockTo_blockOf :
    ∀ (work : Bool) (K : ℕ) (b : Fin (K + 1)), blockTo work K (blockOf work K b) = b
  | false, K, ⟨b, hb⟩ => by
      apply Fin.ext
      by_cases h0 : b = 0
      · subst h0
        simp [blockTo, blockOf]
      · have h1 : b - 1 ≠ K := by omega
        simp [blockTo, blockOf, h0, h1]
        omega
  | true, 0, _ => rfl
  | true, K + 1, ⟨b, hb⟩ => by
      apply Fin.ext
      by_cases h0 : b = 0
      · subst h0
        simp [blockTo, blockOf]
      · by_cases h1 : b = 1
        · subst h1
          simp [blockTo, blockOf]
        · have h2 : b - 1 ≠ K + 1 := by omega
          have h3 : b - 1 ≠ 0 := by omega
          simp [blockTo, blockOf, h0, h1, h2, h3]
          omega

/-- The order of a chain answer's blocks, as a permutation. -/
def blockAt (work : Bool) (K : ℕ) : Equiv.Perm (Fin (K + 1)) :=
  ⟨blockTo work K, blockOf work K, blockOf_blockTo work K, blockTo_blockOf work K⟩

end Compile.Batch
