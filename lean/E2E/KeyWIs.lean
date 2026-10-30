-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyWIs.lean: THE PREMISE `WIs` OF THE LIBRARY's LAW ON THE ROW (Eval), AT THE WORDS THAT THE
HONEST SIDE's PART OF A SENDING HAS LAID FOR W. Statements and proofs.

The setting. Behind the batching of the rows on the matrix the prover sends W, said to be gᵀM, and
the verifier lays the row (Eval) on W's oracle message (`linEvalRow`, OnBytes/Iop/Lin.lean). The
library's `eval_back` (Johnson/Desc/K13/Law/Eval.lean, EvalProofs.lean) says: where W's message,
read through its layout, holds gᵀM (`WIs`), the row (Eval) says its claim of the words exactly if
the claim's row is true of the matrix. Its head: "`WIs` is a premise, and nothing here or in this
folder gives it".

What is shown.
  `weightAt_read`: the weight of a row of the matrix in the description's sentences, read, is the
    weight in that law (`weights`, Johnson/Desc/K13/Law/Means.lean).
  `w_sent`: message 0 of W's job has W's shape, and there is such a message.
  **`wIs_held`**: AT W's JOB (`wJob`, E2E/KeySendJobs.lean), at every coin and at both of the part's
    rounds: `WIs` holds of the words that the part has laid (`held`), at the library's own layout of
    W, at the weights that are made of the challenges heard in front of the part (`wWeights`: THE
    JOB's OWN: that they are the verifier's is E2E/KeyEvalSays.lean's `handed_is`), at the matrix by
    bits that spells the input's reader (every vertex of the cube is the bits of a number: there is
    one such matrix).
  **`eval_iff_held`**: so, by `eval_back`: the row (Eval) for a row on the matrix with these weights
    says its claim of the laid words EXACTLY IF that row is true of the matrix and of the laid
    words' mask entries.
  `fit_one_row`: the premise on room, for a W of one main row whose places are as many as the code's
    message has entries. `w_written`: what these two ask of W's shape and code holds at the written
    sizes of the key: by an evaluation in Lean's kernel.

Limits. FOR THE HONEST W ALONE: nothing follows for a W that a cheating prover sends: for soundness
`WIs` stays the premise that the library's head names. That the row on the matrix is true is not
shown here. Premises: W's message gets an OOD sample, has a mask row and stands over the extension
field; room (every entry of W lies in a real row, within the code's message length); the columns'
bits fit the table's. Nothing on hiding follows from this file.


-/
import E2E.KeySendRows
import Johnson.Prover.Send.Held
import Johnson.Desc.K13.Law.EvalProofs
import Johnson.Goal.PlanValues.KeySizedReturns

set_option autoImplicit false

namespace AtPublicFiles.Key
open OnBytes OnBytes.Params OnBytes.Means
open OnBytes.Slice (GF GE readE)
open ProofFile.Honest (State Seen Cs)
open ProofFile.Honest.K1 (SendJob Ride dueR)
open Johnson.Prover.Send (shapeAt held)
open VerifiableInference.Desc.Key (Pieces weightAt)
open VerifiableInference.Desc.K13.Law (WIs weights ρg lowBits EvalIn witOf Holds)
open Lk6.AtPlan (keyFull)

/-- The weight of a row of the matrix, read. -/
theorem weightAt_read (g : List Tensor) (y : ℕ) :
    readE (weightAt g y) = (g.map fun t => readE (t.entry y)).sum := by
  unfold weightAt
  have h : ∀ (l : List Tensor) (s : E), readE (l.foldl (fun s t => addE s (t.entry y)) s) =
      readE s + (l.map fun t => readE (t.entry y)).sum := by
    intro l
    induction l with
    | nil => intro s; simp
    | cons a l ih =>
      intro s
      rw [List.foldl_cons, ih, OnBytes.Slice.readE_add, List.map_cons, List.sum_cons, add_assoc]
  rw [h, OnBytes.Slice.readE_zero, zero_add]

section
variable {W X : Type} (entry : W → Nat → Nat → GF) (one : OneTime) (N : Pieces)
  (groups : List (List Nat)) (first : Nat) (ride : Nat → Option Ride)
  (points : List Fmt.Drawn → Nat → Nat → List E) (a : BattAt)

/-- Message 0 of W's job has W's shape, and there is such a message. -/
theorem w_sent (J : SendJob W X) (hJ : wJob entry one N groups first ride points a = some J) :
    shapeAt J.P 0 = one.lin.w ∧ 0 < J.P.sent.size ∧ J.first = first ∧ J.P.codes = one.codes := by
  unfold wJob at hJ
  cases hm : linMessageW one.lin with
  | none => rw [hm] at hJ; exact absurd hJ (by simp)
  | some msg =>
    rw [hm] at hJ
    obtain rfl := Option.some.inj hJ
    have e0 : (VerifiableInference.Desc.Key.sendingPar one N.w "W and what rides with it" msg
        groups).sent = msg := by
      unfold VerifiableInference.Desc.Key.sendingPar VerifiableInference.Desc.K1.Par.sent
      simp
    have hs : 0 < msg.size := by
      unfold linMessageW at hm
      simp only [bind, Option.bind, pure] at hm
      by_cases h1 : one.lin.masksAhead = true <;> by_cases h2 : one.lin.ownSplitNeeded = true
      all_goals
        simp only [h1, h2, if_true, if_false, Bool.false_eq_true] at hm
        first
          | (obtain rfl := Option.some.inj hm; simp)
          | (cases hq : linMaskNotice one.lin.testOwn one.lin.wLeafClass with
              | none => rw [hq] at hm; exact absurd hm (by simp)
              | some q => rw [hq] at hm; obtain rfl := Option.some.inj hm; simp)
    refine ⟨?_, ?_, rfl, rfl⟩
    · unfold shapeAt
      rw [e0]
      exact w_first one msg hm
    · rw [e0]
      exact hs

/-- **W's message, as the part has laid it, holds gᵀM.** -/
theorem wIs_held (J : SendJob W X) (hJ : wJob entry one N groups first ride points a = some J)
    (hans : one.lin.w.answers ≠ 0) (hmask : one.lin.w.maskRows ≠ 0) (hdeg : one.lin.w.mainDeg = 3)
    (c : Cs (dueR J.P J.ride)) (s : Seen) (t : State W X) (n : Nat) (w₀ : Words GE)
    (mat : Fin one.lin.matrixRows → (Fin one.lin.kCol → Bool) → GE)
    (hmat : ∀ i e, e < 2 ^ one.lin.kCol →
      mat i (lowBits one.lin.kCol e) = algebraMap GF GE (entry t.input i.val e))
    (hbits : one.lin.kCol ≤ (linLayW one.codes one.lin).bits)
    (hfit : ∀ e < 2 ^ one.lin.kCol,
      (linLayW one.codes one.lin).index e % 2 ^ ceilLog2 one.lin.w.mainRows <
          one.lin.w.mainRows ∧
        (linLayW one.codes one.lin).index e / 2 ^ ceilLog2 one.lin.w.mainRows <
          (one.codes.base.getD one.lin.w.code default).ell) :
    WIs mat (held w₀ first J.P (J.rows c s t n))
      (wWeights one points a (t.heard.take (t.heard.length - n))) first
      (linLayW one.codes one.lin) := by
  intro e he
  obtain ⟨hsh, hsz, -, -⟩ := w_sent entry one N groups first ride points a J hJ
  obtain ⟨f1, f2⟩ := hfit e he
  have hnew := Johnson.Prover.Send.held_new w₀ first J.P (J.rows c s t n) 0 hsz .main
    ((linLayW one.codes one.lin).index e)
  rw [Nat.add_zero] at hnew
  rw [hnew, hsh]
  show (if _ then _ else _) = _
  rw [Johnson.Prover.Send.clog_eq, if_pos f1]
  unfold Johnson.Prover.Send.Rows.main
  rw [if_pos (by simpa using hdeg),
    w_rows entry one N groups first ride points a J hJ hans hmask hdeg c s t n _ _ f1 f2]
  unfold Johnson.Prover.Send.laidE
  have hrb : (linLayW one.codes one.lin).rowBits = ceilLog2 one.lin.w.mainRows := rfl
  rw [hrb, Nat.mod_add_div', OnBytes.Slice.entryAt_index _ e
    (lt_of_lt_of_le he (Nat.pow_le_pow_right (by norm_num) hbits))]
  unfold wVec wAt
  rw [if_pos he, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hmat i e he]
  beta_reduce
  rw [weightAt_read]
  rfl

/-- **The row (Eval) says its claim of the laid words exactly if the row on the matrix is true.** -/
theorem eval_iff_held (J : SendJob W X) (hJ : wJob entry one N groups first ride points a = some J)
    (hans : one.lin.w.answers ≠ 0) (hmask : one.lin.w.maskRows ≠ 0) (hdeg : one.lin.w.mainDeg = 3)
    (c : Cs (dueR J.P J.ride)) (s : Seen) (t : State W X) (n : Nat) (w₀ : Words GE)
    (mat : Fin one.lin.matrixRows → (Fin one.lin.kCol → Bool) → GE)
    (hmat : ∀ i e, e < 2 ^ one.lin.kCol →
      mat i (lowBits one.lin.kCol e) = algebraMap GF GE (entry t.input i.val e))
    (hbits : one.lin.kCol ≤ (linLayW one.codes one.lin).bits)
    (hfit : ∀ e < 2 ^ one.lin.kCol,
      (linLayW one.codes one.lin).index e % 2 ^ ceilLog2 one.lin.w.mainRows <
          one.lin.w.mainRows ∧
        (linLayW one.codes one.lin).index e / 2 ^ ceilLog2 one.lin.w.mainRows <
          (one.codes.base.getD one.lin.w.code default).ell)
    (row : TensorRow)
    (hg : row.g = wWeights one points a (t.heard.take (t.heard.length - n))) (r : OnBytes.Row)
    (hr : linEvalRow one.lin (memberClaim row) first (linLayW one.codes one.lin) = some r)
    (St : Statement) (hin : EvalIn St first (linLayW one.codes one.lin) row.masks) :
    Says ρg St r (held w₀ first J.P (J.rows c s t n)) ↔
      Holds ρg (witOf mat (held w₀ first J.P (J.rows c s t n))) row :=
  VerifiableInference.Desc.K13.Law.eval_back one.lin.matrixRows one.lin row first
    (linLayW one.codes one.lin) r St _ mat hbits hr hin
    (hg ▸ wIs_held entry one N groups first ride points a J hJ hans hmask hdeg c s t n w₀ mat hmat
      hbits hfit)

end

/-- The premise on room, for a W of one main row whose places are as many as the code's message has
entries. -/
theorem fit_one_row (one : OneTime) (h1 : one.lin.w.mainRows = 1) (hh : one.lin.wRowsHigh = true)
    (hk : one.lin.kCol ≤ (one.codes.base.getD one.lin.w.code default).logEll)
    (hell : 2 ^ (one.codes.base.getD one.lin.w.code default).logEll =
      (one.codes.base.getD one.lin.w.code default).ell) :
    one.lin.kCol ≤ (linLayW one.codes one.lin).bits ∧ ∀ e < 2 ^ one.lin.kCol,
      (linLayW one.codes one.lin).index e % 2 ^ ceilLog2 one.lin.w.mainRows <
          one.lin.w.mainRows ∧
        (linLayW one.codes one.lin).index e / 2 ^ ceilLog2 one.lin.w.mainRows <
          (one.codes.base.getD one.lin.w.code default).ell := by
  have hc : ceilLog2 one.lin.w.mainRows = 0 := by rw [h1]; rfl
  refine ⟨?_, fun e he => ?_⟩
  · show _ ≤ ceilLog2 one.lin.w.mainRows + (one.codes.base.getD one.lin.w.code default).logEll
    omega
  · have he' : e < 2 ^ (one.codes.base.getD one.lin.w.code default).logEll :=
      lt_of_lt_of_le he (Nat.pow_le_pow_right (by norm_num) hk)
    have hi : (linLayW one.codes one.lin).index e = e := by
      show (if one.lin.wRowsHigh = true then
        e / 2 ^ (one.codes.base.getD one.lin.w.code default).logEll +
          e % 2 ^ (one.codes.base.getD one.lin.w.code default).logEll *
            2 ^ ceilLog2 one.lin.w.mainRows else e) = e
      rw [if_pos hh, hc, Nat.div_eq_of_lt he', Nat.mod_eq_of_lt he', pow_zero, mul_one, zero_add]
    rw [hi, hc, h1, pow_zero, Nat.mod_one, Nat.div_one, ← hell]
    exact ⟨Nat.one_pos, he'⟩

set_option maxRecDepth 1000000 in
/-- What `wIs_held` and `fit_one_row` ask of W's shape and code, at the written sizes of the key. -/
theorem w_written : keyFull.once.shape.w.answers ≠ 0 ∧ keyFull.once.shape.w.maskRows ≠ 0 ∧
    keyFull.once.shape.w.mainDeg = 3 ∧ keyFull.once.shape.w.mainRows = 1 ∧
    keyFull.once.shape.wRowsHigh = true ∧
    keyFull.once.shape.kCol ≤ (keyFull.codes.base.getD keyFull.once.shape.w.code default).logEll ∧
    2 ^ (keyFull.codes.base.getD keyFull.once.shape.w.code default).logEll =
      (keyFull.codes.base.getD keyFull.once.shape.w.code default).ell := by
  decide +kernel

end AtPublicFiles.Key

#print axioms AtPublicFiles.Key.weightAt_read
#print axioms AtPublicFiles.Key.w_sent
#print axioms AtPublicFiles.Key.wIs_held
#print axioms AtPublicFiles.Key.eval_iff_held
#print axioms AtPublicFiles.Key.fit_one_row
#print axioms AtPublicFiles.Key.w_written
