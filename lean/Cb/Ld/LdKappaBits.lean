-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdKappaBits.lean: "every round's error, counting its proof-of-work bits, is at most κ", with
the bits as a plain list of numbers: the kit.

Definitions and theorems: equivalences, but for two implications; framework only: nothing of a
protocol; nothing is evaluated.
A list of errors (`Err`) holds one number for each round, a count, not a probability: how many
values of that round's verifier message may let a prover that has lost (`Doomed`) escape. (Both
names: Iop/Rbr.lean; `Err s` itself is a tuple of natural numbers.) These errors are numbers that a
link lists (the data fields `LinkA.err`, `Link.P.err`): that a link is sound at the numbers that it
lists is no statement of this file.

Why: `Nums.BelowG` (Cond/ObjBits.lean) takes a vector of proof-of-work bits: for each round of
five composed shapes a number of bits (`GBits`, Iop/GBits.lean: a tuple whose type depends on the
shape). To say which rounds have proof of work one has to walk the composition. A plain list of
numbers goes through a composition by ++, and needs no transport along an equation between terms.

Main names:
  `Err.BelowB ε B κ`: B has as many entries as ε has rounds, and round by round:
    e ≤ κ · (2^b · number of values), with e the round's error, b its entry of B and the values
    those of its verifier message.
  `belowB_iff_G`: `Err.BelowG g ε κ ↔ Err.BelowB ε g.toList κ` (`Err.BelowG`: Iop/Grind.lean).
  `belowB_exists`: `Err.BelowB ε B κ` → there is a vector g with `g.toList = B` (and so
    `Err.BelowG g ε κ`).
  `belowB_app`: `Err.BelowB (Err.app ε ε') B κ` ↔ B = B₁ ++ B₂ with `Err.BelowB ε B₁ κ`,
    `Err.BelowB ε' B₂ κ`.
  `belowB_zero`: `Err.BelowB ε` (as many zeros as ε has rounds) κ ↔ `Err.Below ε κ`
  (Iop/InteractiveOracleProof.lean).
  `belowB_allLe`: all entries of `g.toList` are at most n ⇒ so are g's bits (`g.AllLe n`).
  `IOR.Chain.BelowB`, `IOR.ChainA.BelowB`: `c.BelowB B κ` (c a chain; a chain for a batch);
    `chain_belowB`, `chainA_belowB`: ↔ the chain as one link; `chain_belowB_append`,
    `chainA_belowB_append`: two chains in a row.

Limits: This file says nothing on the value of any number.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdKappaBat
import Iop.GBitsLe

set_option autoImplicit false

namespace Iop
open scoped ENNReal

/-- the bits, in the order of the rounds -/
def GBits.toList : {s : Shape} → GBits s → List ℕ
  | [], _ => []
  | _ :: _, (b, g) => b :: GBits.toList g

/-- Round by round, counting the bits of a plain list. -/
def Err.BelowB : {s : Shape} → Err s → List ℕ → ℝ≥0∞ → Prop
  | [], _, B, _ => B = []
  | _ :: _, _, [], _ => False
  | r :: _, (e, ε), b :: B, c =>
    (e : ℝ≥0∞) ≤ c * ((2 : ℝ≥0∞) ^ b * (Fintype.card r.Chal : ℝ≥0∞)) ∧ Err.BelowB ε B c

theorem belowB_iff_G :
    ∀ {s : Shape} (g : GBits s) (ε : Err s) (κ : ℝ≥0∞), Err.BelowG g ε κ ↔ Err.BelowB ε g.toList κ
  | [], _, _, _ => ⟨fun _ => rfl, fun _ => trivial⟩
  | _ :: _, (_, g), (_, ε), κ =>
    ⟨fun h => ⟨h.1, (belowB_iff_G g ε κ).1 h.2⟩, fun h => ⟨h.1, (belowB_iff_G g ε κ).2 h.2⟩⟩

theorem belowB_exists :
    ∀ {s : Shape} (ε : Err s) (B : List ℕ) (κ : ℝ≥0∞),
      Err.BelowB ε B κ → ∃ g : GBits s, g.toList = B
  | [], _, _, _, h => ⟨(), h.symm⟩
  | _ :: _, _, [], _, h => h.elim
  | _ :: _, (_, ε), b :: B, κ, h =>
    let ⟨g, hg⟩ := belowB_exists ε B κ h.2; ⟨(b, g), congrArg (List.cons b) hg⟩

theorem belowB_app :
    ∀ {s t : Shape} (ε : Err s) (ε' : Err t) (B : List ℕ) (κ : ℝ≥0∞),
      Err.BelowB (Err.app ε ε') B κ ↔ ∃ B₁ B₂, B = B₁ ++ B₂ ∧ Err.BelowB ε B₁ κ ∧ Err.BelowB ε' B₂ κ
  | [], _, _, _, B, _ => ⟨fun h => ⟨[], B, rfl, rfl, h⟩, fun ⟨_, _, e, h1, h2⟩ => by
      have h1' : _ = [] := h1
      subst h1'
      rw [e]
      exact h2⟩
  | _ :: _, _, _, _, [], _ => ⟨fun h => h.elim, fun ⟨B₁, _, e, h1, _⟩ => by
      cases B₁ with
      | nil => exact h1
      | cons b B₁ => cases e⟩
  | _ :: _, _, (_, ε), ε', b :: B, κ => ⟨fun h => by
      obtain ⟨B₁, B₂, e, h1, h2⟩ := (belowB_app ε ε' B κ).1 h.2
      exact ⟨b :: B₁, B₂, congrArg (List.cons b) e, ⟨h.1, h1⟩, h2⟩, fun ⟨B₁, B₂, e, h1, h2⟩ => by
      cases B₁ with
      | nil => exact h1.elim
      | cons b' B₁ =>
        obtain ⟨rfl, e'⟩ := List.cons.inj e
        exact ⟨h1.1, (belowB_app ε ε' B κ).2 ⟨B₁, B₂, e', h1.2, h2⟩⟩⟩

theorem belowB_zero :
    ∀ {s : Shape} (ε : Err s) (κ : ℝ≥0∞), Err.BelowB ε (List.replicate s.length 0) κ ↔ Err.Below ε κ
  | [], _, _ => ⟨fun _ => trivial, fun _ => rfl⟩
  | _ :: _, (_, ε), κ =>
    ⟨fun h => ⟨by simpa using h.1, (belowB_zero ε κ).1 h.2⟩,
      fun h => ⟨by simpa using h.1, (belowB_zero ε κ).2 h.2⟩⟩

theorem belowB_allLe (n : ℕ) : ∀ {s : Shape} (g : GBits s), (∀ b ∈ g.toList, b ≤ n) → g.AllLe n
  | [], _, _ => trivial
  | _ :: _, (b, g), h =>
    ⟨h b (List.mem_cons_self), belowB_allLe n g fun b' hb => h b' (List.mem_cons_of_mem b hb)⟩

namespace IOR
variable {K : Type}

/-- the list of bits can be cut into one list for each link so that `Err.BelowB` holds of each
link's errors at its list -/
def Chain.BelowB : {A B : Joint K} → Chain K A B → List ℕ → ℝ≥0∞ → Prop
  | _, _, .one l, L, κ => Err.BelowB l.P.err L κ
  | _, _, .snoc c l, L, κ => ∃ L₁ L₂, L = L₁ ++ L₂ ∧ c.BelowB L₁ κ ∧ Err.BelowB l.P.err L₂ κ

def ChainA.BelowB : {A B : Joint K} → ChainA K A B → List ℕ → ℝ≥0∞ → Prop
  | _, _, .one a, L, κ => Err.BelowB a.err L κ
  | _, _, .snoc c a, L, κ => ∃ L₁ L₂, L = L₁ ++ L₂ ∧ c.BelowB L₁ κ ∧ Err.BelowB a.err L₂ κ

variable {A B C : Joint K}
theorem Chain.belowB_one (l : Link K A B) (L : List ℕ) (κ : ℝ≥0∞) :
    (Chain.one l).BelowB L κ ↔ Err.BelowB l.P.err L κ := by
  rw [Chain.BelowB]
theorem Chain.belowB_snoc (c : Chain K A B) (l : Link K B C) (L : List ℕ) (κ : ℝ≥0∞) :
    (c.snoc l).BelowB L κ ↔ ∃ L₁ L₂, L = L₁ ++ L₂ ∧ c.BelowB L₁ κ ∧ Err.BelowB l.P.err L₂ κ := by
  rw [Chain.BelowB]
theorem ChainA.belowB_one (a : LinkA K A B) (L : List ℕ) (κ : ℝ≥0∞) :
    (ChainA.one a).BelowB L κ ↔ Err.BelowB a.err L κ := by
  rw [ChainA.BelowB]
theorem ChainA.belowB_snoc (c : ChainA K A B) (a : LinkA K B C) (L : List ℕ) (κ : ℝ≥0∞) :
    (c.snoc a).BelowB L κ ↔ ∃ L₁ L₂, L = L₁ ++ L₂ ∧ c.BelowB L₁ κ ∧ Err.BelowB a.err L₂ κ := by
  rw [ChainA.BelowB]

end IOR

open IOR

theorem chain_belowB {K : Type} {A B : Joint K} (c : Chain K A B) (d : A.W) (κ : ℝ≥0∞) :
    ∀ L, Err.BelowB (c.link d).P.err L κ ↔ c.BelowB L κ := by
  induction c with
  | one l => intro L; rw [Chain.link_one, Chain.belowB_one]
  | snoc c l ih =>
      intro L
      rw [Chain.link_snoc, Chain.belowB_snoc]
      refine (belowB_app (c.link d).P.err l.P.err L κ).trans ?_
      exact ⟨fun ⟨L₁, L₂, e, h1, h2⟩ => ⟨L₁, L₂, e, (ih L₁).1 h1, h2⟩,
        fun ⟨L₁, L₂, e, h1, h2⟩ => ⟨L₁, L₂, e, (ih L₁).2 h1, h2⟩⟩

theorem chainA_belowB {K : Type} {A B : Joint K} (c : ChainA K A B) (d : A.W) (κ : ℝ≥0∞) :
    ∀ L, Err.BelowB (c.linkA d).err L κ ↔ c.BelowB L κ := by
  induction c with
  | one a => intro L; rw [ChainA.linkA_one, ChainA.belowB_one]
  | snoc c a ih =>
      intro L
      rw [ChainA.linkA_snoc, ChainA.belowB_snoc]
      refine (belowB_app (c.linkA d).err a.err L κ).trans ?_
      exact ⟨fun ⟨L₁, L₂, e, h1, h2⟩ => ⟨L₁, L₂, e, (ih L₁).1 h1, h2⟩,
        fun ⟨L₁, L₂, e, h1, h2⟩ => ⟨L₁, L₂, e, (ih L₁).2 h1, h2⟩⟩

theorem chain_belowB_append {K : Type} {A B C : Joint K} (c : Chain K A B)
    (c' : Chain K B C) (κ : ℝ≥0∞) :
    ∀ L, (c.append c').BelowB L κ ↔ ∃ L₁ L₂, L = L₁ ++ L₂ ∧ c.BelowB L₁ κ ∧ c'.BelowB L₂ κ := by
  induction c' with
  | one l => intro L; rw [Chain.append_one, Chain.belowB_snoc]; simp only [Chain.belowB_one]
  | snoc c' l ih =>
      intro L
      rw [Chain.append_snoc, Chain.belowB_snoc]
      constructor
      · rintro ⟨M, L₃, e, h, h3⟩
        obtain ⟨L₁, L₂, e', h1, h2⟩ := (ih M).1 h
        exact ⟨L₁, L₂ ++ L₃, by rw [e, e', List.append_assoc], h1,
          (Chain.belowB_snoc _ _ _ _).2 ⟨L₂, L₃, rfl, h2, h3⟩⟩
      · rintro ⟨L₁, M, e, h1, h⟩
        obtain ⟨L₂, L₃, e', h2, h3⟩ := (Chain.belowB_snoc _ _ _ _).1 h
        exact ⟨L₁ ++ L₂, L₃, by rw [e, e', List.append_assoc], (ih _).2 ⟨L₁, L₂, rfl, h1, h2⟩, h3⟩

theorem chainA_belowB_append
    {K : Type} {A B C : Joint K} (c : ChainA K A B) (c' : ChainA K B C) (κ : ℝ≥0∞) :
    ∀ L, (c.append c').BelowB L κ ↔ ∃ L₁ L₂, L = L₁ ++ L₂ ∧ c.BelowB L₁ κ ∧ c'.BelowB L₂ κ := by
  induction c' with
  | one a => intro L; rw [ChainA.append_one, ChainA.belowB_snoc]; simp only [ChainA.belowB_one]
  | snoc c' a ih =>
      intro L
      rw [ChainA.append_snoc, ChainA.belowB_snoc]
      constructor
      · rintro ⟨M, L₃, e, h, h3⟩
        obtain ⟨L₁, L₂, e', h1, h2⟩ := (ih M).1 h
        exact ⟨L₁, L₂ ++ L₃, by rw [e, e', List.append_assoc], h1,
          (ChainA.belowB_snoc _ _ _ _).2 ⟨L₂, L₃, rfl, h2, h3⟩⟩
      · rintro ⟨L₁, M, e, h1, h⟩
        obtain ⟨L₂, L₃, e', h2, h3⟩ := (ChainA.belowB_snoc _ _ _ _).1 h
        exact ⟨L₁ ++ L₂, L₃, by rw [e, e', List.append_assoc], (ih _).2 ⟨L₁, L₂, rfl, h1, h2⟩, h3⟩

end Iop
