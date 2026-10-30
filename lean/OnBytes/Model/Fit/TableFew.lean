-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/Fit/TableFew.lean: wherever the program's planner returns at three configuration
files, the shape of the stored tables that enters the commitment ID (Chains.tableShape; that the ID
is formed at it is OnBytes/Model/VerifyStages.lean's text) has at most 4 answers for each row, and
the point of the record's sample has at most 32 coordinates. No premise but the planner's yes.

The shape (Chains.tableShape, OnBytes/Model/VerifyStages.lean) is read back from the parameter bytes
of the key's one-time chain. The reader of the parameter file admits 1 to 4 answers and a table's
code of at most 2 ^ 32 positions (LinesCap, OnBytes/Params/Fit/LinesCap.lean). This file carries
these two ranges from the lines to the shape as read back.

How it goes.
 1. planned's yes is taken apart (planned_parts, PlannedParts.lean in this folder): the lines are
    those that the reader of the parameter file returns, the planner said yes at these lines, and
    the reader of the key's three chains returned the chains in p.
 2. The key's shared chain as read holds the test on the table of the one-time chain
    (KeyChains.read_lin, OnBytes/Model/VerifyShape.lean). The shared chain has two items, "codes"
    and "the test on the table".
 3. Both items are read back as they were spelled (Given.read_items_fit,
    OnBytes/Params/Fit/ReadItems.lean): the names of the made plan's entries fit and none is
    "configuration" (spelt_of_planned, PlanTestsTop.lean in this folder), and both items are short
    (keyItems_short, OnBytes/Params/Fit/StagesFew.lean).
 4. The tables' shape that is read from the second item is made of the item's first six words
    (readLin_index, OnBytes/Params/IndexLaws.lean), which spell the shape that follows from the
    lines (keySized_index, OnBytes/Model/VerifyShape.lean). A number is spelled modulo 2 ^ 64, so
    the number that is read is at most the number that was spelled (indexAt_spell_le).

Main theorems.
 - word_u64n_le, spellIndex_words, indexAt_spell_le: step 4's last sentence, for the answers and for
   the length of a row's message.
 - nameFit_codes, nameFit_test: the two items' names fit, by evaluation in Lean's kernel.
 - **planned_table**: planned pol KL layout = .ok p gives p.chains.tableShape.answers ≤ 4 and
   p.chains.tableShape.cubeBits ≤ 32.

Limits. Two upper bounds and no more: that the shape as read back is the shape that the planner made
is not said here. Nothing where the planner refuses; that it returns at any files is shown by no
term here (at the library's two written example configurations a run while a file compiles shows
it, and that the table there has one answer for each row: TestTableFew.lean in this folder). Where
the line record is 0 the shape has 0 answers. Verify.planned is the planner at the program's own
hash. Nothing on soundness. For proofs only.
The program does not import this file.

-/
import OnBytes.Model.Fit.PlanTestsTop
import OnBytes.Model.VerifyShape
import OnBytes.Params.Fit.StagesFew
import OnBytes.Params.Fit.ReadItems

set_option autoImplicit false

namespace OnBytes.Params

/-- The word that a number's spelling holds is at most the number. -/
theorem word_u64n_le (x : Nat) : (Fmt.wordAt (Fmt.u64n x) 0).toNat ≤ x := by
  unfold Fmt.u64n
  rw [Fmt.wordAt_u64, UInt64.toNat_ofNat']
  exact Nat.mod_le _ _

/-- The spelling of a stored table's shape, word by word. -/
theorem spellIndex_words (I : IndexShape) :
    spellIndex I = Fmt.u64n I.code.logN ++ (Fmt.u64n I.code.ell ++ (Fmt.u64n I.code.r ++
      (Fmt.u64n I.v ++ (Fmt.u64n I.answers ++ Fmt.u64n I.saltBytes)))) := by
  simp only [spellIndex, spellCode, spellRow, spellWord, List.map_cons, List.map_nil,
    Fmt.cat_cons, Fmt.cat_nil, ByteArray.append_empty, ByteArray.append_assoc]

/-- Two numbers of the shape that the six words of a shape's spelling spell are at most the numbers
that were spelled: the answers, and the length of a row's message. -/
theorem indexAt_spell_le (I : IndexShape) :
    (indexAt (spellIndex I)).answers ≤ I.answers ∧
      (indexAt (spellIndex I)).code.ell ≤ I.code.ell := by
  have s8 : ∀ x, (Fmt.u64n x).size = 8 := fun _ => rfl
  constructor
  · show (Fmt.wordAt (spellIndex I) 32).toNat ≤ I.answers
    obtain ⟨pre, hpre⟩ : ∃ pre, pre = Fmt.u64n I.code.logN ++ (Fmt.u64n I.code.ell ++
      (Fmt.u64n I.code.r ++ Fmt.u64n I.v)) := ⟨_, rfl⟩
    have e : spellIndex I = pre ++ Fmt.u64n I.answers ++ Fmt.u64n I.saltBytes := by
      rw [hpre, spellIndex_words]
      simp only [ByteArray.append_assoc]
    have z : pre.size = 32 := by
      have a1 := s8 I.code.logN
      have a2 := s8 I.code.ell
      have a3 := s8 I.code.r
      have a4 := s8 I.v
      rw [hpre]
      simp only [ByteArray.size_append]
      omega
    have w := Fmt.wordAt_mid pre (Fmt.u64n I.answers) (Fmt.u64n I.saltBytes) 0
      (Nat.le_of_eq rfl)
    rw [Nat.add_zero, z] at w
    rw [e, w]
    exact word_u64n_le _
  · show (Fmt.wordAt (spellIndex I) 8).toNat ≤ I.code.ell
    have e : spellIndex I = Fmt.u64n I.code.logN ++ Fmt.u64n I.code.ell ++ (Fmt.u64n I.code.r ++
        (Fmt.u64n I.v ++ (Fmt.u64n I.answers ++ Fmt.u64n I.saltBytes))) := by
      rw [spellIndex_words]
      simp only [ByteArray.append_assoc]
    have w := Fmt.wordAt_mid (Fmt.u64n I.code.logN) (Fmt.u64n I.code.ell) (Fmt.u64n I.code.r ++
        (Fmt.u64n I.v ++ (Fmt.u64n I.answers ++ Fmt.u64n I.saltBytes))) 0 (Nat.le_of_eq rfl)
    rw [Nat.add_zero, s8] at w
    rw [e, w]
    exact word_u64n_le _

/-- The name of a shared chain's first item fits. -/
theorem nameFit_codes : Fmt.nameFit "codes" = true := by decide +kernel

/-- The name of a shared chain's second item fits. -/
theorem nameFit_test : Fmt.nameFit "the test on the table" = true := by decide +kernel

end OnBytes.Params

namespace OnBytes.Model.Verify

/-- **The shape of the stored tables that enters the commitment ID has at most 4 answers, and its
record's point at most 32 coordinates.** -/
theorem planned_table {pol KL : ByteArray} {layout : Option ByteArray} {p : Planned}
    (h : planned pol KL layout = .ok p) :
    p.chains.tableShape.answers ≤ 4 ∧ p.chains.tableShape.cubeBits ≤ 32 := by
  obtain ⟨links, shapes, rest, declared, file, rl, lay, _, hL, _, _, _, hc, hK, _, _, _⟩ :=
    planned_parts h
  have LC := Params.linesCap_of_read hL
  have h32 := (planned_spelled h).1
  have hk := Params.sized_key (Params.configure_plans hc).1
  -- the key's shared chain: its bytes as spelled, and as read
  obtain ⟨P1, P2, P3, _, _, _, ek, _, _, e2, _, _, _, _, _⟩ := Params.configure_bytes hc
  have sp : Params.Spelt P2 :=
    spelt_of_planned h P2 (List.mem_append_left _ (by rw [ek]; simp))
  obtain ⟨_, r2, _, _, _⟩ := Params.KeyChains.read_three hK
  have g2 := Params.Shared.read_given r2
  rw [e2] at g2
  obtain ⟨sc, sl⟩ := Params.keyItems_short hk LC
  have it := Params.Given.read_items_fit sp.1 sp.2 h32 (by
    intro y hy
    simp only [Params.madeLinItems, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact ⟨Params.nameFit_codes, sc⟩
    · exact ⟨Params.nameFit_test, sl⟩) g2
  obtain ⟨c, l, q, w⟩ := Params.Shared.read_lin r2
  rw [it] at q
  simp only [Params.madeLinItems, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at q
  rw [← q.2] at w
  -- the tables' shape as read, and as the lines give it
  have s := Params.readLin_index w
  obtain ⟨T, hT, i⟩ := Params.keySized_index hk
  obtain ⟨a1, a2⟩ := Params.indexAt_spell_le (Params.indexShapeOf (Params.settingOf p.X.P.frame) T)
  have hA : (Params.indexShapeOf (Params.settingOf p.X.P.frame) T).answers ≤ 4 := by
    unfold Params.indexShapeOf
    dsimp only
    exact (Params.setCap_of_lines LC).samples
  have hE : (Params.indexShapeOf (Params.settingOf p.X.P.frame) T).code.ell ≤ 2 ^ 32 := by
    show T.code.ell ≤ 2 ^ 32
    rw [(Params.deriveTable_fields hT).1]
    show p.X.P.frame.tableData ≤ 2 ^ 32
    have hp : 2 ^ p.X.P.frame.tableLogN ≤ 2 ^ 32 := Nat.pow_le_pow_right (by omega) LC.tLogN
    have hf := LC.tFit
    omega
  have e : p.chains.tableShape =
      Params.indexAt (Params.spellIndex
        (Params.indexShapeOf (Params.settingOf p.X.P.frame) T)) := by
    show p.chains.key.oneTime.lin.fold.index = _
    rw [← Params.KeyChains.read_lin hK, s, i]
  rw [e]
  exact ⟨Nat.le_trans a1 hA, Params.ceilLog2_le_of (Nat.le_trans a2 hE)⟩

end OnBytes.Model.Verify

#print axioms OnBytes.Params.indexAt_spell_le
#print axioms OnBytes.Model.Verify.planned_table
