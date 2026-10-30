-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Pend/RowOk.lean: the weights of a pending row meet the conditions on a vector of
product form.

A pending row (Johnson/Desc/First/Pend/Row.lean) holds its weights on the rows of the committed
matrix as a list g of vectors of product form (`Tensor`, OnBytes/Iop/Tensor.lean). `Tensor.ok` asks
of such a vector: at most 63 variables; the written-out slice lies inside its vector; every
written-out variable exists, has the pair (1, 1) and is named once. Here: every vector in the g of
every row that `pendingRowO` returns meets `Tensor.ok`. Statements and proofs; no definition.

Main names:
  `blockOf_ok`: the vector of one aligned block of rows.
  `stretchBlocks_ok`, `memberWeightsOnRows_ok`: the vectors of a stretch of rows.
  `scale_ok`: a vector times a scalar meets the conditions if and only if the vector does.
  `pendingRowO_weights`: the g of a returned row is what `memberWeightsOnRows` returned.
  `pending_rows_weights_ok`: the statement above.
  `ok_can_fail`, `stretch_met`: a vector that fails the conditions; a stretch that has vectors.

Limits. One direction: from a row that was returned; a function that returns no row meets it too.
Nothing on what the vectors' entries are (for that: Johnson/Road/Rows/StretchLaws.lean), on psi, on
the masks or on the target. Nothing on who lays the row, or on whether it stays as it was laid.
Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Road.Rows.StretchLaws
import Johnson.Desc.First.Pend.Row

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Pend
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Road.Rows

/-- No number stands twice in a run of numbers. -/
theorem distinct_run : ∀ (n a : ℕ), distinctNats (List.range' a n) = true
  | 0, _ => rfl
  | n + 1, a => by
    have hn : a ∉ List.range' (a + 1) n := by
      intro hm
      have := (List.mem_range'_1.1 hm).1
      omega
    rw [List.range'_succ]
    show (!(List.range' (a + 1) n).contains a && distinctNats (List.range' (a + 1) n)) = true
    rw [distinct_run n (a + 1)]
    simp [hn]

/-- **The vector of one aligned block of 2^d rows meets the conditions.** -/
theorem blockOf_ok (kRow firstRow : ℕ) (values : Array E) (start d : ℕ) (hk : kRow ≤ 63)
    (hd : d ≤ kRow) (hf : firstRow ≤ start) (he : start + 2 ^ d ≤ firstRow + values.size) :
    (blockOf kRow firstRow values start d).ok = true := by
  unfold blockOf
  by_cases h : d = 0
  · subst h
    rw [if_pos (show ((0 : ℕ) == 0) = true from rfl)]
    obtain ⟨t, ht⟩ : ∃ t, t = ({ scalar := values.getD (start - firstRow) zeroE } :
      Tensor).insertChoice 0 kRow start := ⟨_, rfl⟩
    rw [← ht]
    have hP : t.pairs.length = kRow := by
      rw [ht]
      show (([] : List (E × E)).take 0 ++ choicePairs kRow start ++
        ([] : List (E × E)).drop 0).length = kRow
      simp [choicePairs_length]
    have hD : t.denseVars = [] := by
      rw [ht]
      rfl
    unfold Tensor.ok Tensor.vars
    rw [hP, hD]
    simp [distinctNats, hk]
  · rw [if_neg (by simpa using h)]
    obtain ⟨t, ht⟩ : ∃ t, t = ((({} : Tensor).pushDense d).insertChoice d (kRow - d)
      (start / 2 ^ d)).setValues values (start - firstRow) := ⟨_, rfl⟩
    rw [← ht]
    have hP : t.pairs =
        List.replicate d (oneE, oneE) ++ choicePairs (kRow - d) (start / 2 ^ d) := by
      rw [ht]
      show (([] ++ List.replicate d (oneE, oneE)).take d ++
        choicePairs (kRow - d) (start / 2 ^ d) ++
        ([] ++ List.replicate d (oneE, oneE)).drop d) = _
      simp
    have hD : t.denseVars = List.range' 0 d := by
      rw [ht]
      show ((({} : Tensor).pushDense d).denseVars.map
        fun x => if d ≤ x then x + (kRow - d) else x) = _
      rw [dense_empty]
      conv_rhs => rw [← List.map_id (List.range' 0 d)]
      refine List.map_congr_left fun x hx => ?_
      have := (List.mem_range'_1.1 hx).2
      rw [if_neg (by omega)]
      rfl
    have hV : t.values = values := by
      rw [ht]
      rfl
    have hF : t.first = start - firstRow := by
      rw [ht]
      rfl
    unfold Tensor.ok Tensor.vars
    rw [hP, hD, hV, hF]
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, List.all_eq_true,
      beq_iff_eq]
    refine ⟨⟨⟨?_, Or.inr ?_⟩, fun x hx => ?_⟩, distinct_run d 0⟩
    · rw [List.length_append, List.length_replicate, choicePairs_length]
      omega
    · rw [List.length_range']
      omega
    · have hx' := (List.mem_range'_1.1 hx).2
      rw [List.getElem?_append_left (by rw [List.length_replicate]; omega),
        List.getElem?_replicate, if_pos (by omega)]

/-- The vectors of the blocks from a row on meet the conditions. -/
theorem stretchBlocks_ok (kRow firstRow : ℕ) (values : Array E) (hk : kRow ≤ 63) :
    ∀ (fuel start : ℕ), firstRow ≤ start →
      ∀ t ∈ stretchBlocks kRow firstRow values fuel start, t.ok = true
  | 0, _, _, _, ht => absurd ht List.not_mem_nil
  | fuel + 1, start, h1, t, ht => by
    rw [stretchBlocks_succ] at ht
    by_cases hc : firstRow + values.size ≤ start
    · rw [if_pos hc] at ht
      exact absurd ht List.not_mem_nil
    · rw [if_neg hc] at ht
      obtain ⟨b1, -, b3⟩ := blockBits_spec kRow start (firstRow + values.size) kRow 0
        (Nat.zero_le _) (by simp) (by rw [pow_zero]; omega)
      rcases List.mem_cons.1 ht with rfl | ht
      · exact blockOf_ok kRow firstRow values start _ hk b1 h1 b3
      · exact stretchBlocks_ok kRow firstRow values hk fuel _
          (Nat.le_trans h1 (Nat.le_add_right _ _)) t ht

/-- **Row weights that are written out on a stretch of rows meet the conditions.** -/
theorem memberWeightsOnRows_ok {S : LinShape} {first : ℕ} {values : Array E} {g : List Tensor}
    (h : memberWeightsOnRows S first values = some g) : ∀ t ∈ g, t.ok = true := by
  unfold memberWeightsOnRows at h
  split at h
  · unfold stretchInTheCube at h
    split at h
    · rename_i hc
      have hc' : S.kRow < 63 ∧ first + values.size ≤ 2 ^ S.kRow := by simpa using hc
      dsimp only at h
      split at h
      · obtain rfl := Option.some.inj h
        exact stretchBlocks_ok _ _ _ (by omega) _ _ (Nat.le_refl _)
      · cases h
    · cases h
  · cases h

/-- A vector times a scalar meets the conditions if and only if the vector does. -/
theorem scale_ok (t : Tensor) (x : E) : (t.scale x).ok = t.ok := by
  have h1 : (t.scale x).pairs = t.pairs := by unfold Tensor.scale; rfl
  have h2 : (t.scale x).denseVars = t.denseVars := by unfold Tensor.scale; rfl
  have h3 : (t.scale x).values = t.values := by unfold Tensor.scale; rfl
  have h4 : (t.scale x).first = t.first := by unfold Tensor.scale; rfl
  unfold Tensor.ok Tensor.vars
  rw [h1, h2, h3, h4]

/-- Where two steps in a row say yes, each does. -/
theorem bind_ok {α β : Type} {x : Except String α} {f : α → Except String β} {y : β}
    (h : (x >>= f) = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => exact absurd h (by simp [bind, Except.bind])
  | ok a => exact ⟨a, rfl, h⟩

/-- A refusal in front is a refusal. -/
theorem throw_bind {β γ : Type} (e : String) (f : β → Except String γ) (y : γ) :
    ((throw e : Except String β) >>= f) ≠ .ok y := by
  simp [bind, Except.bind]

/-- A test in front of a step: where the whole says yes, the test held and the step says yes. -/
theorem unless_ok {β : Type} {c : Prop} [Decidable c] {e : String}
    {f : PUnit → Except String β} {y : β}
    (h : (if c then (pure PUnit.unit >>= f) else ((throw e : Except String PUnit) >>= f)) =
      .ok y) : c ∧ f PUnit.unit = .ok y := by
  split at h
  · exact ⟨‹c›, h⟩
  · exact absurd h (throw_bind _ _ _)

/-- The weights of a returned row are what `memberWeightsOnRows` returned. -/
theorem pendingRowO_weights {lay : WsLay} {indexMasks : ℕ} {o : WsForkOut} {claims : ℕ}
    {S : LinShape} {oracles oracles' : Array Oracle} {row : TensorRow}
    (h : pendingRowO lay indexMasks o claims S oracles = .ok (row, oracles')) :
    ∃ (first : ℕ) (values : Array E), memberWeightsOnRows S first values = some row.g := by
  unfold pendingRowO at h
  have h := (unless_ok h).2
  have h := (unless_ok h).2
  have h := (unless_ok h).2
  have h := (unless_ok h).2
  obtain ⟨⟨first, last⟩, -, h⟩ := bind_ok h
  have h := (unless_ok h).2
  have h := (unless_ok h).2
  have h := (unless_ok h).2
  have h := (unless_ok h).2
  obtain ⟨Gamma, -, h⟩ := bind_ok h
  split at h
  · rename_i g hg
    split at h
    · split at h
      · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, -⟩ := h
        exact ⟨_, _, hg⟩
      · exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
    · exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])
  · exact absurd h (by simp [throw, throwThe, MonadExceptOf.throw])

/-- **THE WEIGHTS OF A PENDING ROW MEET THE CONDITIONS ON A VECTOR OF PRODUCT FORM.** -/
theorem pending_rows_weights_ok {lay : WsLay} {indexMasks : ℕ} {o : WsForkOut} {claims : ℕ}
    {S : LinShape} {oracles oracles' : Array Oracle} {row : TensorRow}
    (h : pendingRowO lay indexMasks o claims S oracles = .ok (row, oracles')) :
    ∀ t ∈ row.g, t.ok = true := by
  obtain ⟨_, _, hg⟩ := pendingRowO_weights h
  exact memberWeightsOnRows_ok hg

/-! ### neither empty nor idle -/

/-- The conditions can fail: a written-out variable that does not exist. -/
theorem ok_can_fail : ({ denseVars := [0] } : Tensor).ok = false := by decide

/-- The premise is met: three rows from row 1 on, in the cube of 8 rows: a block of one row and a
block of two, the second with a written-out variable. -/
theorem stretch_met :
    (stretchInTheCube 3 1 #[oneE, oneE, oneE]).map (fun g => g.map fun t => t.denseVars) =
      some [[], [0]] := by decide

end VerifiableInference.Desc.First.Pend

#print axioms VerifiableInference.Desc.First.Pend.pending_rows_weights_ok
#print axioms VerifiableInference.Desc.First.Pend.memberWeightsOnRows_ok
#print axioms VerifiableInference.Desc.First.Pend.scale_ok
#print axioms VerifiableInference.Desc.First.Pend.ok_can_fail
#print axioms VerifiableInference.Desc.First.Pend.stretch_met
