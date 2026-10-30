-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyEvalJoin.lean: THE PIECES OF "THE ROW (Eval) SAYS ITS CLAIM OF THE LAID WORDS", JOINED: from
the acceptance of the batching's text and from what the payers in front hold, to the row's claim;
and, apart, what the acceptance of the text behind W's commitment gives. ONE STATEMENT THAT TAKES
BOTH ACCEPTANCES: E2E/KeyEvalBoth.lean. Statements and proofs. NOTHING IS CLAIMED OF ANY PROVER: it
is conditional throughout.

Why. E2E/KeyEvalSays.lean's `eval_says` asks the pile's rows' truth and `ReadsCode` at the words
BEHIND W's sending, at letters x, fresh, h, o; the payers hold them at the words IN FRONT, at what
the batching's text has heard and at the mask entries that it has taken. Here the two are brought
together.

What is shown.
  `maskOf_held`: a sending leaves the mask entries of the oracle messages in front of it.
  **`holds_carried`**, **`readsCode_carried`**: so a row on the matrix whose mask entries lie in
    front is true at the words behind the sending exactly if it is at the words in front; and
    `ReadsCode` passes where the fresh slots lie in front.
  **`eval_says_of_batt`**: THE JOIN: the batching's text accepts its rounds · the challenges heard
    hold these rounds' challenges from base on · the pile has `pileOf`'s weights and column points ·
    AT THE WORDS IN FRONT: every row of the pile is true, and `ReadsCode` holds at the text's own
    letters (what it has heard; the slots that it has taken) · all these mask entries lie in front
    of W ⟹ the row (Eval) that is made of THE ROW WHICH THE TEXT HAS RETURNED says its claim of the
    words behind.
  **`evalIn_of_rows`**: what the library's law on (Eval) asks of the statement (`EvalIn`) IS
    NOBODY's DEBT: where the text behind W's commitment (`K13.rows`) accepts, the library gives it
    whole, at the statement that the text leaves, with the row and its place among the own group's
    open rows (`rows_ok`, `evalIn_of_rowIn`, Johnson/Desc/K13/Law/M4.lean; `evalIn_withRow`,
    `mem_withRow`, M4Proof.lean).
  `formAt_read`, **`holds_iff_tensorRow`**: the law's sentence "the row is true" (`K13.Law.Holds`)
    is the description's own sentence on a row on the matrix (`TensorRowHolds`,
    Johnson/Desc/Key/KeyWords.lean), "the same" read as "the same reading": through
    E2E/KeyRowOnW.lean's `row_iff_w`.

Limits. The pile's rows' truth and `ReadsCode` at the words in front stay premises, each another's.
BETWEEN `evalIn_of_rows` AND `eval_says_of_batt`'s two last premises stand four ties that no
statement of this file names: the shape is the job's; the row is the one that the batching returned;
W's number is the job's first; the codes in front are the job's. In `eval_says_of_batt` the premise
on the default slot is spare (the ledger's number lies below first, and the default slot's is 0).
`holds_iff_tensorRow` is spent by no statement. No written form of the join. The premise on the list
of challenges heard: E2E/KeyHeardTies.lean's Limits. FOR THE HONEST W ALONE. Nothing on soundness.
Nothing on hiding follows from this file.


-/
import E2E.KeyHeardTies
import E2E.KeyRowOnW
import Johnson.Desc.K13.Law.M4Proof
import Johnson.Desc.ProofFile.Honest.K13.Tie

set_option autoImplicit false

namespace AtPublicFiles.Key
open OnBytes OnBytes.Params OnBytes.Means
open OnBytes.Slice (GF GE readE toF)
open ProofFile.Honest (State Seen Cs)
open ProofFile.Honest.K1 (SendJob Ride dueR)
open Johnson.Prover.Send (held Rows)
open VerifiableInference.Desc.Key (Pieces TensorRowHolds weightAt formAt)
open VerifiableInference.Desc.K13 (batt St oneDrawn heard)
open VerifiableInference.Desc.K13.Law (ρg lowBits EvalIn witOf maskOf Holds lhs formVal weights
  colOf Wit)
open VerifiableInference.Desc.K13.Honest (ReadsCode tabsOf)

/-! ## 1. From the words in front of a sending to the words behind it -/

/-- A sending leaves the mask entries of the oracle messages in front of it. -/
theorem maskOf_held (w₀ : Words GE) (first : ℕ) (P : VerifiableInference.Desc.K1.Par)
    (V : ℕ → Rows) (s : Slot) (hs : s.oracle < first) :
    maskOf (held w₀ first P V) s = maskOf w₀ s :=
  Johnson.Prover.Send.held_old w₀ first P V s.oracle .mask s.index
    fun h => absurd h.1 (Nat.not_le.2 hs)

variable {nR k : ℕ}

/-- **A row whose mask entries lie in front of the sending is true behind it exactly if it is in
front.** -/
theorem holds_carried (mat : Fin nR → (Fin k → Bool) → GE) (w₀ : Words GE) (first : ℕ)
    (P : VerifiableInference.Desc.K1.Par) (V : ℕ → Rows) (r : TensorRow)
    (hm : ∀ t ∈ r.masks, t.1.oracle < first) :
    Holds ρg (witOf mat (held w₀ first P V)) r ↔ Holds ρg (witOf mat w₀) r := by
  have e : formVal ρg (witOf mat (held w₀ first P V)).mask r.masks =
      formVal ρg (witOf mat w₀).mask r.masks := by
    unfold formVal
    refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
    show _ * maskOf (held w₀ first P V) t.1 = _ * maskOf w₀ t.1
    rw [maskOf_held w₀ first P V t.1 (hm t ht)]
  unfold VerifiableInference.Desc.K13.Law.Holds lhs
  rw [e]
  rfl

/-- **`ReadsCode` passes** where the fresh slots lie in front of the sending. -/
theorem readsCode_carried (mat : Fin nR → (Fin k → Bool) → GE) (w₀ : Words GE) (first : ℕ)
    (P : VerifiableInference.Desc.K1.Par) (V : ℕ → Rows) (pile : List TensorRow)
    (fresh : List Slot) (x : E) (h : Psc.Heard)
    (hf : ∀ j, (fresh.getD j default).oracle < first)
    (hc : ReadsCode ρg (witOf mat w₀) pile fresh x h) :
    ReadsCode ρg (witOf mat (held w₀ first P V)) pile fresh x h := by
  have e : (fun j => (witOf mat (held w₀ first P V)).mask (fresh.getD j default)) =
      fun j => (witOf mat w₀).mask (fresh.getD j default) :=
    funext fun j => maskOf_held w₀ first P V _ (hf j)
  have et : tabsOf ρg (witOf mat (held w₀ first P V)) pile (ρg.val x) =
      tabsOf ρg (witOf mat w₀) pile (ρg.val x) :=
    ProofFile.Honest.K13.tabsOf_mat rfl pile _
  exact ⟨by rw [e]; exact hc.mu, by rw [e, et]; exact hc.rounds⟩

/-! ## 2. The join -/

section
variable {W X : Type} (entry : W → Nat → Nat → GF) (one : OneTime) (N : Pieces)
  (groups : List (List Nat)) (first : Nat) (ride : Nat → Option Ride)
  (points : List Fmt.Drawn → Nat → Nat → List E)

/-- **FROM THE BATCHING's ACCEPTANCE AND WHAT HOLDS IN FRONT OF W, TO THE ROW (Eval)'s CLAIM AT THE
WORDS BEHIND.** -/
theorem eval_says_of_batt (base : Nat) (J : SendJob W X)
    (hJ : wJob entry one N groups first ride points ⟨base, base + 1, base + 2⟩ = some J)
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
    {owed : Johnson.Desc.First.ForkGround.RowsOwed} {cnt : Nat} {pile : List TensorRow}
    {ledger : Nat} {d : St} {rs : List Fmt.RoundView} {out : TensorRow × St}
    (hb : batt owed one.lin.kCol cnt pile ledger d rs = .ok out)
    (hl : ∀ (i : Nat) (r : Fmt.RoundView), rs[i]? = some r →
      (t.heard.take (t.heard.length - n))[base + i]? = some r.drawn)
    (hp : pile.map (fun r => (r.g, r.psi)) =
      (pileOf (Wf.matrixOf one.lin) one.ranges.lookups
        (points (t.heard.take (t.heard.length - n)))).map fun r => (r.g, r.psi))
    (hrows : ∀ r ∈ pile, Holds ρg (witOf mat w₀) r)
    (hfront : ∀ r ∈ pile, ∀ u ∈ r.masks, u.1.oracle < first) (hled : ledger < first)
    (h0 : (default : Slot).oracle < first)
    (hc : ∀ r rs' x u hd, rs = r :: rs' → oneDrawn "K13.sigma-one-drawn" r = .ok x →
      VerifiableInference.Desc.Ground.takeMasksP d ledger (Batt.masksOf one.lin.kCol) = some u →
      heard rs' = .ok hd →
      ReadsCode ρg (witOf mat w₀) pile (u.1.map fun i => ⟨ledger, i⟩) x hd)
    (r : OnBytes.Row)
    (he : linEvalRow one.lin (memberClaim out.1) first (linLayW one.codes one.lin) = some r)
    (St' : Statement) (hin : EvalIn St' first (linLayW one.codes one.lin) out.1.masks) :
    Says ρg St' r (held w₀ first J.P (J.rows c s t n)) := by
  obtain ⟨r₀, rs', x, u, hd, o, T⟩ := ties_of_batt hb _ base hl
  have ho : out.1 = Batt.rowOf pile o := by rw [T.out]
  rw [ho] at he hin
  have hfr : ∀ j, (((u.1.map fun i => (⟨ledger, i⟩ : Slot))).getD j default).oracle < first := by
    intro j
    by_cases hj : j < (u.1.map fun i => (⟨ledger, i⟩ : Slot)).length
    · rw [List.getD_eq_getElem _ _ hj, List.getElem_map]
      exact hled
    · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt hj)]
      exact h0
  exact eval_says entry one N groups first ride points ⟨base, base + 1, base + 2⟩ J hJ hans hmask
    hdeg c s t n w₀ mat hmat hbits hfit pile _ x hd o T.fits
    (fun q hq => (holds_carried mat w₀ first J.P _ q (hfront q hq)).2 (hrows q hq))
    (readsCode_carried mat w₀ first J.P _ pile _ x hd hfr
      (hc r₀ rs' x u hd T.rounds T.sampled T.taken T.heard))
    T.run (BattTies.heardIs (one := one) (points := points) T hp) r he St' hin

end

/-! ## 3. What the law asks of the statement is given by the text's own acceptance -/

/-- **Where the text behind W's commitment accepts**: the row (Eval) of the claim's row at W's
number and layout; `EvalIn` at the statement that the text leaves; and the row is among the own
group's open rows there. -/
theorem evalIn_of_rows {Sh : LinShape} {row : TensorRow} {ids : Array ℕ} {d : St}
    {o : LinFirst × St}
    (h : VerifiableInference.Desc.K13.rows Sh (memberClaim row) ids d = .ok o)
    (hb : Sh.kCol ≤ (linLayW d.st.codes Sh).bits) :
    ∃ r : OnBytes.Row, ids[0]? = some o.1.w ∧
      linEvalRow Sh (memberClaim row) o.1.w (linLayW d.st.codes Sh) = some r ∧
      EvalIn o.2.st o.1.w (linLayW d.st.codes Sh) row.masks ∧
      ∃ G', o.2.st.groups[o.1.own]? = some G' ∧ r ∈ G'.rows.toList := by
  obtain ⟨d₃, r, G, -, hw, hr, hG, hin, hst, -⟩ := VerifiableInference.Desc.K13.Law.rows_ok h
  obtain ⟨hlen, rfl⟩ := OnBytes.Slice.linEvalRow_inv Sh _ _ _ r hr
  have hlen' : row.psi.length = Sh.kCol := hlen
  refine ⟨_, hw, hr, ?_, ?_⟩
  · rw [hst]
    exact VerifiableInference.Desc.K13.Law.evalIn_withRow _ _
      (VerifiableInference.Desc.K13.Law.evalIn_of_rowIn (by rw [hlen']; exact hb) hin)
  · rw [hst]
    exact VerifiableInference.Desc.K13.Law.mem_withRow _ hG

/-! ## 4. The law's "the row is true" is the description's own sentence -/

/-- A form in mask entries, read. -/
theorem formAt_read (mk : Slot → E) (mask : Slot → GE) (hm : ∀ s, mask s = readE (mk s))
    (f : MaskForm) : readE (formAt mk f) = formVal ρg mask f := by
  unfold formAt formVal
  have h : ∀ (l : MaskForm) (a : E), readE (l.foldl (fun s x => addE s (mulE x.2 (mk x.1))) a) =
      readE a + (l.map fun t => ρg.val t.2 * mask t.1).sum := by
    intro l
    induction l with
    | nil => intro a; simp
    | cons x l ih =>
      intro a
      rw [List.foldl_cons, ih, OnBytes.Slice.readE_add, OnBytes.Slice.readE_mul, List.map_cons,
        List.sum_cons, hm x.1, add_assoc]
      rfl
  rw [h, OnBytes.Slice.readE_zero, zero_add]

/-- **The two sentences on a row on the matrix are one**: at a matrix by bits that spells the matrix
of machine words, and mask entries that are the readings of the machine elements. -/
theorem holds_iff_tensorRow (m : Wf.Matrix) (matF : ℕ → ℕ → F) (mk : Slot → E) (x : TensorRow)
    (mat : Fin m.rows → (Fin m.kCol → Bool) → GE)
    (hmat : ∀ (i : Fin m.rows) (e : ℕ), e < 2 ^ m.kCol →
      mat i (lowBits m.kCol e) = algebraMap GF GE (toF (matF i.val e)))
    (mask : Slot → GE) (hmask : ∀ s, mask s = readE (mk s)) (hpsi : x.psi.length = m.kCol) :
    Holds ρg (⟨mat, mask⟩ : Wit GE m.rows m.kCol) x ↔
      TensorRowHolds (fun a b => readE a = readE b) m matF mk x := by
  rw [row_iff_w, formAt_read mk mask hmask]
  unfold VerifiableInference.Desc.K13.Law.Holds lhs
  have e : Alg.mle (colOf (⟨mat, mask⟩ : Wit GE m.rows m.kCol) (weights ρg m.rows x.g))
      (Johnson.L5.Layers.rd ρg m.kCol x.psi) =
      ∑ c ∈ Finset.range (2 ^ m.kCol), readE ((Tensor.eq x.psi).entry c) *
        wAt (fun y => readE (weightAt x.g y)) (fun y c => toF (matF y c)) m.rows c := by
    unfold Alg.mle
    rw [← VerifiableInference.Desc.K13.Law.sum_lowBits m.kCol fun b =>
      Alg.eqk (Johnson.L5.Layers.rd ρg m.kCol x.psi) b *
        colOf (⟨mat, mask⟩ : Wit GE m.rows m.kCol) (weights ρg m.rows x.g) b]
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [← VerifiableInference.Desc.K13.Law.eqW_rd, OnBytes.Slice.readE_eqList,
      OnBytes.Slice.readE_one, one_mul, List.length_map, hpsi]
    refine congrArg (fun z => _ * z) ?_
    unfold colOf wAt
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    show weights ρg m.rows x.g i * mat i (lowBits m.kCol c) = _
    rw [hmat i c (Finset.mem_range.1 hc)]
    beta_reduce
    rw [weightAt_read]
    rfl
  rw [e]
  rfl

end AtPublicFiles.Key

#print axioms AtPublicFiles.Key.maskOf_held
#print axioms AtPublicFiles.Key.holds_carried
#print axioms AtPublicFiles.Key.readsCode_carried
#print axioms AtPublicFiles.Key.eval_says_of_batt
#print axioms AtPublicFiles.Key.evalIn_of_rows
#print axioms AtPublicFiles.Key.formAt_read
#print axioms AtPublicFiles.Key.holds_iff_tensorRow
