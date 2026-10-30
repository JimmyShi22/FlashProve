-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/CoverSparse.lean: THE DEBTS OF A CHAIN ARE OWED AT ITS BUSY
MEMBERS ALONE. `localDebts_of` (Honest/Law/CoverSplit.lean) asks one sentence (`DebtAt`) for each
gated member of a chain. Almost every member is idle: no fall of the chain's list sits at it or at a
member without a round right behind it (`groupOf`, Honest/Law/CoverNone.lean), and no mark at its
place speaks at a typed message of its own rounds. Here: `LocalDebts` from the three zeros of
Honest/Law/CoverPay.lean at the idle members, and from `DebtAt`, as a premise, at the others.

WHAT THIS IS. A lemma on definitions of ours: calls. None of the library's goals.

  `localDebts_sparse`

THE LETTERS. bs: the gated members; rest: the chain's members behind them (at the first chain: the
seal); tail: the fixed challenges behind the last gated member. Zr A b B: «the member b, with A in
front and B behind, is idle»: a letter: whoever calls the lemma picks it. hmk, hq, hfl, hfl': what
is asked at an idle member: its marks are silent; if it has no round and is the last, no fixed
challenge stands behind; if it has a round: no fall sits in its group; if it is the last: at no
member from there on. hbusy: the debt at every other member. hX: as the zeros of
Honest/Law/CoverPay.lean ask: met at a file's first and shared chain, not at the second where an
earlier chain can reject. hall, hlen: the cut and the data's length.

MET FOR NOTHING. At Zr := fun _ _ _ => False the lemma is `localDebts_of`. Limits. Called here at no
description. This file proves nothing about soundness, completeness, hiding or any other property of
the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.CoverNoFall

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Prob
open scoped ENNReal
open VerifiableInference.Desc
open OnBytes.Maker (RDT uLT drawnT)
open _root_.Run.PQ (CK)

variable {S Cl W Y : Type}

/-- **THE SPARSE JOINER.** -/
theorem localDebts_sparse (C : CK) (all bs rest : List (Block S Cl)) (fs : List (Fall S))
    (ms : List Mark) (skip : Nat) (X : List Fmt.Drawn → ChainAt S Cl W Y) (p : Nat → ℝ≥0∞)
    (tail : List Fmt.Drawn)
    (hX : ∀ base a, (X base).start = some a → ∃ (m₀ : Option (Mid W Y)) (s₀ : S)
      (front : List OpenedColumn), m₀.isSome = true ∧ ChainProgress.start (X base).lay all m₀ (some s₀) front = .ok a)
    (hall : all = bs ++ rest) (ds : List RDT)
    (hlen : ds.length = (bs.flatMap (·.rounds)).length)
    (Zr : List (Block S Cl) → Block S Cl → List (Block S Cl) → Prop)
    (hmk : ∀ A b B, bs = A ++ b :: B → Zr A b B →
      ∀ fr (ρ : Iop.Rho (uLT C ((ds.drop (A.flatMap (·.rounds)).length).take b.rounds.length))),
      markOf ms b.place fr (drawnT C _ ρ) = none)
    (hq : ∀ A b, bs = A ++ [b] → Zr A b [] → b.rounds = [] → tail = [])
    (hfl : ∀ A b b' B, bs = A ++ b :: b' :: B → Zr A b (b' :: B) → b.rounds ≠ [] →
      ∀ d ∈ groupOf b (b' :: B ++ rest), ∀ f ∈ fs, f.place ≠ d.place)
    (hfl' : ∀ A b, bs = A ++ [b] → Zr A b [] → b.rounds ≠ [] →
      ∀ d ∈ b :: rest, ∀ f ∈ fs, f.place ≠ d.place)
    (hbusy : ∀ A b B, bs = A ++ b :: B → ¬ Zr A b B →
      DebtAt C all fs ms skip X p (silentQ ms skip bs) b (0 + A.length)
        (0 + (A.flatMap (·.rounds)).length)
        ((ds.drop (A.flatMap (·.rounds)).length).take b.rounds.length)
        (if B.isEmpty then tail else []) B.isEmpty) :
    LocalDebts C all fs ms skip X p tail (silentQ ms skip bs) bs 0 0 ds := by
  refine localDebts_of C all fs ms skip X p tail (silentQ ms skip bs) bs 0 0 ds
    fun A b B e => ?_
  by_cases hz : Zr A b B
  swap
  · exact hbusy A b B e hz
  have hj : bs[0 + A.length]? = some b := by
    rw [Nat.zero_add, e, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  have hn : 0 + (A.flatMap (·.rounds)).length =
      ((bs.take (0 + A.length)).flatMap (·.rounds)).length := by
    rw [Nat.zero_add, Nat.zero_add, e, List.take_left' rfl]
  have hl := stretch_len ds A B b (by rw [← e]; exact hlen)
  have hb : all = A ++ b :: (B ++ rest) := by
    rw [hall, e, List.append_assoc, List.cons_append]
  cases B with
  | nil =>
    have ht : (if ([] : List (Block S Cl)).isEmpty then tail else []) = tail := rfl
    rw [ht]
    by_cases hr : b.rounds = []
    · rw [hq A b e hz hr]
      exact debt_zero_quiet C all fs ms skip X p hX bs hj hn hl hr (hmk A b [] e hz)
    · exact debt_zero_rest C all fs ms skip X p hX bs A ([] ++ rest) hj hn hl hb
        (Nat.zero_add _).symm (List.length_pos_of_ne_nil hr) (hmk A b [] e hz)
        (hfl' A b e hz hr)
  | cons b' B' =>
    have ht : (if (b' :: B').isEmpty then tail else ([] : List Fmt.Drawn)) = [] := rfl
    rw [ht]
    by_cases hr : b.rounds = []
    · exact debt_zero_quiet C all fs ms skip X p hX bs hj hn hl hr (hmk A b (b' :: B') e hz)
    · exact debt_zero C all fs ms skip X p hX bs A (b' :: B' ++ rest) hj hn hl hb
        (Nat.zero_add _).symm (List.length_pos_of_ne_nil hr) (hmk A b (b' :: B') e hz)
        (hfl A b b' B' e hz hr)

end ProofFile.Honest

#print axioms ProofFile.Honest.localDebts_sparse
