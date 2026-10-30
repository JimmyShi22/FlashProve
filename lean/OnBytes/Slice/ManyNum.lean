-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/ManyNum.lean: the error counts of a chain of any number of stages are at most 2^-128
as shares of their rounds' challenge values, from one or two comparisons of natural numbers for each
stage. Rounds that draw positions may have test bits.

A chain is a `Chain` of OnBytes/Slice/ManyDefs.lean. For each stage four numbers are named
(`StNum`): the bits of a position, the number of draws, the number of hash blocks of the round that
draws the positions, and a least radius.

Main definitions.
 `WkRound d ds B W`  the written round d draws the list ds, has B hash blocks and W test bits.
 `LastNum`, `CsNum`  the comparisons of natural numbers for a base case's second round and for a
                  code switch's second round.
 `Chain.Nums`     the chain's stages and rounds have the numbers of a list, one `StNum` a stage.
 `NumsOK`         the comparisons hold at each member of the list.
Main theorems.
 `wk_elem_round`, `wk_cs_round`, `wk_last_round`   the clause on the count of one round.
 `Chain.small_of_nums`   `Chain.Small` at 2^-128 (OnBytes/Slice/ManyErr.lean).
 `Chain.err_num`, `Chain.errL_num_bat`   every count of a chain with the library's counts is at
                  most 2^-128 as such a share; the second with the batching's count in front.

The rounds that draw positions are asked to have W test bits (`WkRound`). W of the 128 bits are then
work: the comparison has the factor 2^W on its right side. A bound speaks of one round. It is no
bound on the chance of a false proof and not the sum of the rounds.

What this file does not claim: any number; that a description has such rounds; that the radii are
right for the codes; that the prover has lost with these counts.

-/
import OnBytes.Slice.CsErr
import OnBytes.Slice.ManyErr
import OnBytes.Slice.NoWorkRatesTail

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Run
open scoped ENNReal

/-- What the bounds ask of a written round d: it draws the list ds, it has B hash blocks and W test
bits, and its positions have at most 64 bits. -/
structure WkRound (d : PQ.RD) (ds : List Fmt.Draw) (B W : ℕ) : Prop where
  /-- The round's positions have at most 64 bits. -/
  log : d.entry.logN ≤ 64
  /-- What the round draws. -/
  draws : Fmt.dsOf d.entry d.kind = ds
  /-- The round's number of hash blocks. -/
  blocks : (bsRound .two d.entry d.kind).b = B
  /-- The round's number of test bits. -/
  work : d.entry.work = W

/-- The same, with the number of hash blocks as the format's plan counts it from the entry. -/
theorem WkRound.of_plan (d : PQ.RD) (ds : List Fmt.Draw) (B W : ℕ) (hlog : d.entry.logN ≤ 64)
    (hds : Fmt.dsOf d.entry d.kind = ds)
    (hB : Fmt.blocksFor (Fmt.wordsAtMost d.entry d.kind) = B) (hw : d.entry.work = W) :
    WkRound d ds B W :=
  ⟨hlog, hds, (planDraws_law .two d.entry d.kind hlog).2.trans hB, hw⟩

/-- A round without test bits, in the record of OnBytes/Slice/NoWorkRatesRound.lean. -/
theorem WkRound.noWork {d : PQ.RD} {ds : List Fmt.Draw} {B : ℕ} (h : WkRound d ds B 0) :
    NwRound d ds B :=
  ⟨h.log, h.draws, h.blocks, h.work⟩

/-- The comparison for a round that draws t positions of a bits, with B hash blocks and W test
bits, at the radius r and the exponent k: the bias of the sampler times ((2^a - r - 1) / 2^a)^t is
at most 2^W / 2^k. -/
def LastNum (W k a t B r : ℕ) : Prop :=
  (2 ^ 128 + 1) ^ B * (2 ^ a - r - 1) ^ t * 2 ^ k ≤ (2 ^ 128) ^ B * (2 ^ a) ^ t * 2 ^ W

/-- The two comparisons for a round that draws t positions of a bits and one element: that of
`LastNum`, and the whole count, with 1 + 3 t bad elements, with 2^191 in the place of the field's
size. From the two the comparison follows for every size from 2^191 on (`mix_num`). -/
def CsNum (W k a t B r : ℕ) : Prop :=
  LastNum W k a t B r ∧
    (2 ^ 128 + 1) ^ B * (2 ^ a - r - 1) ^ t * 2 ^ k * 2 ^ 191 +
        (2 ^ 128 + 1) ^ B * ((2 ^ a) ^ t * (1 * (1 + 3 * t))) * 2 ^ k ≤
      (2 ^ 128) ^ B * (2 ^ a) ^ t * 2 ^ W * 2 ^ 191

/-- A round that draws one element, with five hash blocks, no test bit and a count e of at most
2^32: the count is at most 2^-128 as a share of its round's challenge values. -/
theorem wk_elem_round (d : PQ.RD) (hd : WkRound d [.elem, .trits 0] 5 0) (e : ℕ)
    (he : e ≤ 2 ^ 32) : RoundBelow e d ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  nw_elem_round d hd.noWork e he

/-- A code switch's second round, at a radius r of at least r0: the count e, given by an equation,
is at most 2^-k as a share of its round's challenge values. The round is asked to have W test bits
(`WkRound`): W of the k bits are work. -/
theorem wk_cs_round (d : PQ.RD) (W k a t B r0 : ℕ)
    (hd : WkRound d (List.replicate t (Fmt.Draw.pos a) ++ [.elem, .trits 0]) B W)
    (hn : CsNum W k a t B r0) (e r : ℕ) (hr : r0 ≤ r)
    (he : e = (2 ^ a - r - 1) ^ t * Fintype.card GE + (2 ^ a) ^ t * (1 * (1 + 3 * t))) :
    RoundBelow e d ((2 : ℝ≥0∞)⁻¹ ^ k) := by
  have hv : nVals (Fmt.dsOf d.entry d.kind) = (2 ^ a) ^ t * Fintype.card GE := by
    rewrite [hd.draws, nVals_rep, nVals_elem_end]
    exact rfl
  exact mix_round d hd.log a t B W k (Fintype.card GE) ((2 ^ a - r - 1) ^ t) (1 * (1 + 3 * t)) e
    hv hd.blocks hd.work card_GE_pos he
    ((mix_mono _ _ _ _ _ _ _ (far_pow_le (2 ^ a) r0 r t hr)).trans
      (mix_num _ _ _ _ _ _ _ (2 ^ 191) _ card_GE_large hn.1 hn.2))

/-- A round that draws t positions of a bits and nothing else, at a radius r of at least r0: the
count e = (2^a - r - 1)^t is at most 2^-k as a share of its round's challenge values. The round is
asked to have W test bits (`WkRound`): W of the k bits are work. -/
theorem wk_last_round (d : PQ.RD) (W k a t B r0 : ℕ)
    (hd : WkRound d (List.replicate t (Fmt.Draw.pos a) ++ [.trits 0]) B W)
    (hn : LastNum W k a t B r0) (e r : ℕ) (hr : r0 ≤ r) (he : e = (2 ^ a - r - 1) ^ t) :
    RoundBelow e d ((2 : ℝ≥0∞)⁻¹ ^ k) := by
  refine entry_pow d hd.log e ((2 ^ a - r0 - 1) ^ t) ((2 ^ a) ^ t) B W k hd.blocks hd.work
    (Nat.pow_pos (Nat.two_pow_pos a)) ?_ hn
  rewrite [hd.draws, nVals_rep, nVals_end, mul_one, he]
  exact Nat.mul_le_mul_right _ (far_pow_le (2 ^ a) r0 r t hr)

/-- A stage's numbers. -/
structure StNum where
  /-- The main code has 2^a positions. -/
  a : ℕ
  /-- The number of positions that are drawn. -/
  t : ℕ
  /-- The number of hash blocks of the round that draws them. -/
  B : ℕ
  /-- The least radius. -/
  r : ℕ

/-- A stage that is folded and switched has the numbers x: its code's positions and its draws; its
radius e is at least x.r and at most 2^30; the fold's two rounds draw one element each and have no
test bit; the code switch's second round draws the positions and one element and has W test
bits. -/
structure StepNums (W : ℕ) (s : Sg) (e : ℕ) (dE dT dC : PQ.RD) (x : StNum) : Prop where
  /-- The main code's positions. -/
  a : s.C.a = x.a
  /-- The number of draws. -/
  t : s.t = x.t
  /-- The radius from below. -/
  lo : x.r ≤ e
  /-- The radius from above. -/
  hi : e ≤ 2 ^ 30
  /-- The fold's first round. -/
  rE : WkRound dE [.elem, .trits 0] 5 0
  /-- The fold's repeated round. -/
  rT : WkRound dT [.elem, .trits 0] 5 0
  /-- The code switch's second round. -/
  rC : WkRound dC (List.replicate x.t (Fmt.Draw.pos x.a) ++ [.elem, .trits 0]) x.B W

/-- The last stage has the numbers x: as `StepNums`, with the base case's first round, which draws
one element, and its second, which draws the positions and has W test bits. -/
structure LastNums (W : ℕ) (s : Sg) (e : ℕ) (dL dB : PQ.RD) (x : StNum) : Prop where
  /-- The main code's positions. -/
  a : s.C.a = x.a
  /-- The number of draws. -/
  t : s.t = x.t
  /-- The radius from below. -/
  lo : x.r ≤ e
  /-- The radius from above. -/
  hi : e ≤ 2 ^ 30
  /-- The base case's first round. -/
  rL : WkRound dL [.elem, .trits 0] 5 0
  /-- The base case's second round. -/
  rB : WkRound dB (List.replicate x.t (Fmt.Draw.pos x.a) ++ [.trits 0]) x.B W

/-- The comparisons at each member of a list of stages' numbers: `CsNum` at all but the last,
`LastNum` at the last. An empty list has none and does not count as good. -/
def NumsOK (W k : ℕ) : List StNum → Prop
  | [] => False
  | [x] => LastNum W k x.a x.t x.B x.r
  | x :: y :: xs => CsNum W k x.a x.t x.B x.r ∧ NumsOK W k (y :: xs)

namespace Chain

/-- The chain's stages and rounds have the numbers of the list, one member a stage, in order. -/
def Nums (W : ℕ) : {s : Sg} → Chain s → List StNum → Prop
  | _, .last s e dL dB _ _ _ => fun L => ∃ x, L = [x] ∧ LastNums W s e dL dB x
  | _, .step s _ _ _ e dE dT _ dC _ _ _ _ _ next => fun L =>
    ∃ x xs, L = x :: xs ∧ StepNums W s e dE dT dC x ∧ next.Nums W xs

/-- A list whose numbers a chain has is not empty. -/
theorem nums_ne_nil (W : ℕ) {s : Sg} (c : Chain s) (L : List StNum) (h : c.Nums W L) :
    L ≠ [] := by
  cases c with
  | last s e dL dB fu fs εb =>
    obtain ⟨x, rfl, _⟩ := h
    exact List.cons_ne_nil _ _
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next =>
    obtain ⟨x, xs, rfl, _⟩ := h
    exact List.cons_ne_nil _ _

/-- The standard base case has the numbers [x], if its stage and rounds have the numbers x. -/
theorem nums_lastStd (W : ℕ) (s : Sg) (e : ℕ) (dL dB : PQ.RD) (x : StNum)
    (hx : LastNums W s e dL dB x) : (lastStd s e dL dB).Nums W [x] :=
  ⟨x, rfl, hx⟩

/-- The standard step to a stage that is not the last has the numbers x :: xs, if its stage and
rounds have the numbers x and what follows has the numbers xs. -/
theorem nums_stepMid (W : ℕ) (s s' : Sg) (hf : CsFit s s') (e : ℕ) (dE dT dS dC : PQ.RD)
    (next : Chain s') (x : StNum) (xs : List StNum) (hx : StepNums W s e dE dT dC x)
    (hn : next.Nums W xs) : (stepMid s s' hf e dE dT dS dC next).Nums W (x :: xs) :=
  ⟨x, xs, rfl, hx, hn⟩

/-- The standard step to the last stage has the numbers x :: xs, if its stage and rounds have the
numbers x and what follows has the numbers xs. -/
theorem nums_stepEnd (W : ℕ) (s s' : Sg) (hf : CsFit s s') (e : ℕ) (dE dT dS dC : PQ.RD)
    (next : Chain s') (x : StNum) (xs : List StNum) (hx : StepNums W s e dE dT dC x)
    (hn : next.Nums W xs) : (stepEnd s s' hf e dE dT dS dC next).Nums W (x :: xs) :=
  ⟨x, xs, rfl, hx, hn⟩

/-- The inequalities of `Small` at 2^-128, for a chain that has the numbers of a list at which the
comparisons hold. The rounds that draw positions are asked to have W test bits (`Chain.Nums`): W of
the 128 bits are work. -/
theorem small_of_nums (W : ℕ) {s : Sg} (c : Chain s) (L : List StNum) (h : c.Nums W L)
    (hn : NumsOK W 128 L) : c.Small ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  have p30 : (2 : ℕ) ^ 30 = 1073741824 := by decide
  have p32 : (2 : ℕ) ^ 32 = 4294967296 := by decide
  induction c generalizing L with
  | last s e dL dB fu fs εb =>
    obtain ⟨x, rfl, hx⟩ := h
    have hi := hx.hi
    refine ⟨wk_elem_round dL hx.rL _ (by omega), ?_⟩
    refine wk_last_round dB W 128 x.a x.t x.B x.r hx.rB hn _ e hx.lo ?_
    rewrite [hx.a, hx.t]
    exact Eq.refl _
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next ih =>
    obtain ⟨x, xs, rfl, hx, hnext⟩ := h
    have hi := hx.hi
    obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil (next.nums_ne_nil W xs hnext)
    refine ⟨wk_elem_round dE hx.rE 1 (by decide), wk_elem_round dT hx.rT _ (by omega),
      fun _ => wk_elem_round dT hx.rT _ (by omega), ?_, ih _ hnext hn.2⟩
    refine wk_cs_round dC W 128 x.a x.t x.B x.r hx.rC hn.1 _ e hx.lo ?_
    rewrite [cs_err2, hx.a, hx.t]
    exact Eq.refl _

/-- Every count of a chain that has the library's counts is at most 2^-128 as a share of its round's
challenge values, if the chain has the numbers of a list at which the comparisons hold. The rounds
that draw positions are asked to have W test bits (`Chain.Nums`): W of the 128 bits are work. -/
theorem err_num (W : ℕ) {s : Sg} (c : Chain s) (L : List StNum) (hp : c.Plain)
    (h : c.Nums W L) (hn : NumsOK W 128 L) : Err.Below c.err ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  c.err_below _ hp (c.small_of_nums W L h hn)

/-- The batching's count and the chain's counts, over the list of the batching's round and the
chain's rounds: each is at most 2^-128 as a share of its round's challenge values. The rounds that
draw positions are asked to have W test bits (`Chain.Nums`): W of the 128 bits are work. Asked
besides what `err_num` asks: the batching's round draws one element and has no test bit, and at most
2^32 rows are batched. -/
theorem errL_num_bat (W : ℕ) {s : Sg} (c : Chain s) (L : List StNum) (hp : c.Plain)
    (h : c.Nums W L) (hn : NumsOK W 128 L) (S : Sz) (dA : PQ.RD)
    (hA : WkRound dA [.elem, .trits 0] 5 0) (hr : S.nRows ≤ 2 ^ 32) :
    Err.Below (s := PQ.uL (ckP .two) (dA :: c.rds)) (batErr S 1 dA, c.errL)
      ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  c.errL_below_bat _ hp (c.small_of_nums W L h hn) S dA (wk_elem_round dA hA _ (by omega))

end Chain

end OnBytes.Slice
