-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/Stat.lean: under three public premises, an answer's linear form, evaluated at
stAt P first, is K1's closed form on the entries of the answer's own oracle message. stAt P first is
the value of the library's type Statement at which the honest sender computes its answers. Also: the
sender's tables, by number.
Terms: Johnson/SendSim/At/Sim.lean. Limits of the folder: Johnson/SendSim/Defs.lean.

What this file proves, for every P and first, by unfolding and finite sums.
  value_stAt        Let k < P.sent.size, let oracle message k have a main row or a mask row, and let
                    the point z have at least as many coordinates as that oracle message reads. Let
                    w be any words (Words: entries for all oracle messages, as K1 indexes them).
                    Then the left-hand side of the answer's equation K1.sampleRow, evaluated at stAt
                    P first and w, is K1's closed form K1.Msg.form, which reads only w (first + k).
  stAt_get          For k < P.sent.size, stAt P first has at the number first + k an oracle message
                    of the shape shapeAt P k. stAt_codes, stAt_size: its codes are P's; it has first
                    + P.sent.size oracle messages.
  treeTables_get    Table number τ of treeTables has the length and width of P's tree number τ, and
                    word i of its symbol at a position is word i of the column col, read in the base
                    field. treeTables_length: there are as many tables as P has trees.

How it fits. Johnson/SendSim/At/Answers.lean uses value_stAt for ans_tie, and
Johnson/SendSim/At/Shown.lean uses treeTables_get; both serve shownTie, so rowsExact
(Johnson/SendSim/At/RowsExact.lean) and rowsFresh (Johnson/SendSim/At/RowsFresh.lean). The proof
rests on value_sampleRow (Johnson/SendSim/Tie/Sample.lean). stAt and treeTables are defined in
Johnson/Desc/ProofFile/Honest/K1/Part.lean, K1.sampleRow in Johnson/Desc/K1/Own.lean, K1.Msg.form in
Johnson/Desc/K1/Law/Law.lean, col in Johnson/Prover/Send/Core.lean.
-/
import Johnson.Desc.ProofFile.Honest.K1.Part
import Johnson.SendSim.Tie.Sample

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt col)

theorem stAt_codes (P : K1.Par) (first : ℕ) : (stAt P first).codes = P.codes := rfl

theorem stAt_size (P : K1.Par) (first : ℕ) :
    (stAt P first).oracles.size = first + P.sent.size := by
  simp [stAt, stSent]

/-- For k < P.sent.size, the oracle message of stAt P first with the number first + k has the shape
of oracle message k of P. -/
theorem stAt_get (P : K1.Par) (first k : ℕ) (hk : k < P.sent.size) :
    (stAt P first).oracles[first + k]? = some { shape := shapeAt P k } := by
  simp [stAt, stSent, shapeAt, Array.getElem?_append_right, hk]

/-- If k < P.sent.size, oracle message k has a main row or a mask row, and z has at least as many
coordinates as it reads, then the left-hand side of K1.sampleRow at stAt P first and the words w is
K1.Msg.form on w (first + k). -/
theorem value_stAt (P : K1.Par) (first k : ℕ) (hk : k < P.sent.size) (z : List E) (β : E) (i : ℕ)
    (y : E) (w : Means.Words GE)
    (hne : ((K1.Msg.of P.codes (shapeAt P k)).K != 0 ||
      (K1.Msg.of P.codes (shapeAt P k)).Kzk != 0) = true)
    (hz : (K1.Msg.of P.codes (shapeAt P k)).v ≤ z.length) :
    Means.value rdE (stAt P first)
        (K1.sampleRow (K1.Msg.of P.codes (shapeAt P k)) (first + k) z β i y) w =
      (K1.Msg.of P.codes (shapeAt P k)).form (readL z) (readE β) i (w (first + k)) :=
  value_sampleRow (stAt P first) (first + k) { shape := shapeAt P k } (stAt_get P first k hk) z β i
    y w hne hz

theorem treeTables_length (P : K1.Par) (Vr : ℕ → Rows) :
    (treeTables P Vr).length = P.trees.length := by
  simp [treeTables]

/-- Table number τ of treeTables P Vr, if P has a tree number τ: its length and width are the
tree's, and word i of its symbol at a position is word i of col P Vr τ at that position, read in the
base field (0 beyond the column's length). -/
theorem treeTables_get (P : K1.Par) (Vr : ℕ → Rows) (τ : ℕ) :
    (treeTables P Vr)[τ]? = (P.trees[τ]?).map fun T =>
      { logLength := T.logN, words := T.mainWidth + T.maskWidth
        sym := fun pos i => toF ((col P Vr τ pos).getD i.val 0) } := by
  unfold treeTables
  rw [List.getElem?_map, List.getElem?_zipIdx]
  cases P.trees[τ]? with
  | none => rfl
  | some T => simp

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.stAt_get
#print axioms OnBytes.SendSim.At.value_stAt
#print axioms OnBytes.SendSim.At.treeTables_get
