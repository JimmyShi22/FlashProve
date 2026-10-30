-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyEvalSays.lean: THE HONEST STEP BEHIND THE BATCHING OF THE ROWS ON THE MATRIX, IN ONE
STATEMENT: where the pile's rows are true, the row (Eval) says its claim of the words that the
honest side's part of a sending has laid for W. Three calls. Statements and proofs. NOTHING IS
CLAIMED OF ANY PROVER: it is conditional throughout.

The three. (1) The row that the batching hands on is true where the pile's rows are and what was
  heard reads as what the prover with code computes: `code_row`
  (Johnson/Desc/K13/Honest/CodeRow.lean). (2) That row's weights are those of which W's job makes W:
  `rowOf_weights`, `handedWeights_congr` (E2E/KeyPile.lean), under four ties between the verifier's
  run and the challenges heard. (3) So the row (Eval) says its claim of the laid words:
  `eval_iff_held` (E2E/KeyWIs.lean), by the library's `eval_back`.

What is defined.
  `HeardIs one points a pile x h o heard`: THE FOUR TIES, a statement of premises: the pile has the
    weights and column points of `pileOf` at the points made of the challenges heard; the batching's
    sample, the joining element and the sumcheck's point are the challenges at the three public
    rounds. What is shown.
  `handed_is`: under these the handed row's weights are `wWeights` at the challenges heard.
  **`eval_says`**: the statement above, for every statement St that has the row's tables (`EvalIn`).
    The reading is the library's (`Reading.gl`).
  `heardIs_of_pile`: the first tie, where the pile is the one that the verifier's own text lays
    (`pile_same`), at points that are the claims' own.
  **`eval_says_written`**: at one-time public values with the written codes and shape of the key:
    the premises on W's shape, on room and on the columns' bits are paid.
  `evalIn_of`: `EvalIn` from the statement's own entry for W; what it asks of the mask form stays.
    THE LIBRARY GIVES MORE: `EvalIn` whole, from the acceptance of the text behind W's commitment:
    E2E/KeyEvalJoin.lean's `evalIn_of_rows`.

Limits.
- PREMISES, each owed by another: every row of the pile is true at the matrix and the laid words'
  mask entries; `ReadsCode` (what was heard reads as what the prover with code computes);
  `Batt.fits`; the sumcheck's run returns; the four ties; `EvalIn`; the premises of `wIs_held`.
- THE WORDS: those of `held` over any older words w₀: BEHIND W's sending: whoever holds the pile's
  rows' truth and `ReadsCode` in front of it carries them by E2E/KeyEvalJoin.lean, which also joins
  the letters x, fresh, h, o to the batching's own text. That they are the words at which a
  proximity test's law is stated is not shown here.
- One row of those that W's proximity test takes in: nothing on a sample row, a split's row or a
  generator row.
- FOR THE HONEST W ALONE. Nothing on soundness. Nothing on hiding follows from this file.


-/
import E2E.KeyWIs
import Johnson.Desc.K13.Honest.CodeRow

set_option autoImplicit false

namespace AtPublicFiles.Key
open OnBytes OnBytes.Params OnBytes.Means
open OnBytes.Slice (GF GE readE)
open ProofFile.Honest (State Seen Cs)
open ProofFile.Honest.K1 (SendJob Ride dueR)
open Johnson.Prover.Send (held)
open VerifiableInference.Desc.Key (Pieces tableRowsOf)
open VerifiableInference.Desc.K13.Law (ρg lowBits EvalIn witOf Holds)
open VerifiableInference.Desc.K13.Honest (ReadsCode code_row)
open Lk6.AtPlan (keyFull)

/-- **The four ties between the verifier's run of the batching and the challenges heard.** A
statement of premises: it is claimed of nothing. -/
structure HeardIs (one : OneTime) (points : List Fmt.Drawn → Nat → Nat → List E) (a : BattAt)
    (pile : List TensorRow) (x : E) (h : Psc.Heard) (o : Psc.Out) (heard : List Fmt.Drawn) :
    Prop where
  pile : pile.map (fun r => (r.g, r.psi)) =
    (pileOf (Wf.matrixOf one.lin) one.ranges.lookups (points heard)).map fun r => (r.g, r.psi)
  sample : x = elemAt heard a.sigma
  eps : h.eps = elemAt heard a.eps
  point : o.point =
    (List.range (Wf.matrixOf one.lin).kCol).map fun i => elemAt heard (a.first + i)

/-- Under the four ties the handed row's weights are those of which W's job makes W. -/
theorem handed_is (one : OneTime) (points : List Fmt.Drawn → Nat → Nat → List E) (a : BattAt)
    (pile : List TensorRow) (x : E) (fresh : List Slot) (h : Psc.Heard) (o : Psc.Out)
    (heard : List Fmt.Drawn) (hh : HeardIs one points a pile x h o heard)
    (hr : Psc.run (Batt.claimOf pile x) (Batt.summandOf pile x) fresh h = some o) :
    (Batt.rowOf pile o).g = wWeights one points a heard := by
  rw [(rowOf_weights pile x fresh h o hr).1, handedWeights_congr _ _ x h.eps o.point hh.pile,
    hh.sample, hh.eps, hh.point]
  rfl

/-- The first tie, where the pile is the one that the verifier's own text lays, and the points made
of the challenges heard are the claims' own. -/
theorem heardIs_of_pile (one : OneTime) (points : List Fmt.Drawn → Nat → Nat → List E)
    (keys : List (List Lkp.Keys)) (rows : List (List TensorRow)) (heard : List Fmt.Drawn)
    (hn : one.ranges.lookups.length = keys.length)
    (hk : (zipT one.ranges.lookups keys).mapM
      (fun x => tableRowsOf (Wf.matrixOf one.lin) x.1 x.2) = some rows)
    (hp : ∀ i f, points heard i f = ((keys.getD i []).getD f default).point) :
    rows.flatten.map (fun r => (r.g, r.psi)) =
      (pileOf (Wf.matrixOf one.lin) one.ranges.lookups (points heard)).map
        fun r => (r.g, r.psi) := by
  rw [zipT_eq] at hk
  rw [pile_same (Wf.matrixOf one.lin) one.ranges.lookups keys rows 0 hn hk,
    show points heard = fun i f => ((keys.getD i []).getD f default).point from
      funext fun i => funext fun f => hp i f]
  rfl

section
variable {W X : Type} (entry : W → Nat → Nat → GF) (one : OneTime) (N : Pieces)
  (groups : List (List Nat)) (first : Nat) (ride : Nat → Option Ride)
  (points : List Fmt.Drawn → Nat → Nat → List E) (a : BattAt)

/-- **WHERE THE PILE's ROWS ARE TRUE, THE ROW (Eval) SAYS ITS CLAIM OF THE WORDS THAT THE PART HAS
LAID FOR W.** -/
theorem eval_says (J : SendJob W X) (hJ : wJob entry one N groups first ride points a = some J)
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
    (pile : List TensorRow) (fresh : List Slot) (x : E) (h : Psc.Heard) (o : Psc.Out)
    (hf : Batt.fits one.lin.kCol pile = true)
    (hrows : ∀ r ∈ pile, Holds ρg (witOf mat (held w₀ first J.P (J.rows c s t n))) r)
    (hc : ReadsCode ρg (witOf mat (held w₀ first J.P (J.rows c s t n))) pile fresh x h)
    (hr : Psc.run (Batt.claimOf pile x) (Batt.summandOf pile x) fresh h = some o)
    (hh : HeardIs one points a pile x h o (t.heard.take (t.heard.length - n))) (r : OnBytes.Row)
    (he : linEvalRow one.lin (memberClaim (Batt.rowOf pile o)) first
      (linLayW one.codes one.lin) = some r)
    (St : Statement) (hin : EvalIn St first (linLayW one.codes one.lin) (Batt.rowOf pile o).masks) :
    Says ρg St r (held w₀ first J.P (J.rows c s t n)) :=
  (eval_iff_held entry one N groups first ride points a J hJ hans hmask hdeg c s t n w₀ mat hmat
    hbits hfit (Batt.rowOf pile o) (handed_is one points a pile x fresh h o _ hh hr) r he St
    hin).2 (code_row ρg _ pile fresh hf hrows x h o hc hr)

/-- **At the written sizes of the key**: for one-time public values with the written codes and shape
the premises on W's shape, on room and on the columns' bits are paid (`w_written`, `fit_one_row`,
E2E/KeyWIs.lean). -/
theorem eval_says_written (hcodes : one.codes = keyFull.codes) (hlin : one.lin = keyFull.once.shape)
    (J : SendJob W X) (hJ : wJob entry one N groups first ride points a = some J)
    (c : Cs (dueR J.P J.ride)) (s : Seen) (t : State W X) (n : Nat) (w₀ : Words GE)
    (mat : Fin one.lin.matrixRows → (Fin one.lin.kCol → Bool) → GE)
    (hmat : ∀ i e, e < 2 ^ one.lin.kCol →
      mat i (lowBits one.lin.kCol e) = algebraMap GF GE (entry t.input i.val e))
    (pile : List TensorRow) (fresh : List Slot) (x : E) (h : Psc.Heard) (o : Psc.Out)
    (hf : Batt.fits one.lin.kCol pile = true)
    (hrows : ∀ r ∈ pile, Holds ρg (witOf mat (held w₀ first J.P (J.rows c s t n))) r)
    (hc : ReadsCode ρg (witOf mat (held w₀ first J.P (J.rows c s t n))) pile fresh x h)
    (hr : Psc.run (Batt.claimOf pile x) (Batt.summandOf pile x) fresh h = some o)
    (hh : HeardIs one points a pile x h o (t.heard.take (t.heard.length - n))) (r : OnBytes.Row)
    (he : linEvalRow one.lin (memberClaim (Batt.rowOf pile o)) first
      (linLayW one.codes one.lin) = some r)
    (St : Statement) (hin : EvalIn St first (linLayW one.codes one.lin) (Batt.rowOf pile o).masks) :
    Says ρg St r (held w₀ first J.P (J.rows c s t n)) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := w_written
  obtain ⟨hbits, hfit⟩ := fit_one_row one (by rw [hlin]; exact a4) (by rw [hlin]; exact a5)
    (by rw [hlin, hcodes]; exact a6) (by rw [hlin, hcodes]; exact a7)
  exact eval_says entry one N groups first ride points a J hJ (by rw [hlin]; exact a1)
    (by rw [hlin]; exact a2) (by rw [hlin]; exact a3) c s t n w₀ mat hmat hbits hfit pile fresh x h
    o hf hrows hc hr hh r he St hin

end

/-- **`EvalIn` from the statement's own entry for W**: the statement has the one-time public values'
codes, and its oracle message number first has W's shape, with a main row. What is asked of the mask
form stays. -/
theorem evalIn_of (St : Statement) (one : OneTime) (first : Nat) (masks : MaskForm) {y : _}
    (hy : St.oracles[first]? = some y) (hs : y.shape = one.lin.w) (hc : St.codes = one.codes)
    (h0 : 0 < one.lin.w.mainRows)
    (hm : ∀ t ∈ masks, t.1.oracle < St.oracles.size ∧ t.1.index < tableSize St t.1.oracle .mask) :
    EvalIn St first (linLayW one.codes one.lin) masks := by
  refine ⟨(Array.getElem?_eq_some_iff.1 hy).1, ?_, hm⟩
  have hne : (one.lin.w.mainRows == 0) = false := by
    rw [beq_eq_false_iff_ne]
    omega
  unfold tableSize Statement.has Statement.tableBits Statement.rowBits Statement.placeBits
  simp only [hy, hs, hc, OracleShape.rows, h0, decide_true, if_true, hne, Bool.false_eq_true,
    if_false]
  rfl

end AtPublicFiles.Key

#print axioms AtPublicFiles.Key.handed_is
#print axioms AtPublicFiles.Key.heardIs_of_pile
#print axioms AtPublicFiles.Key.eval_says
#print axioms AtPublicFiles.Key.eval_says_written
#print axioms AtPublicFiles.Key.evalIn_of
