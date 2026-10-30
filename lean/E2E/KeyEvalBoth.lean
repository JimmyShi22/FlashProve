--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyEvalBoth.lean: "THE ROW (Eval) SAYS ITS CLAIM OF THE LAID WORDS", FROM THE ACCEPTANCE OF BOTH
OF THE VERIFIER's TEXTS, AND WITH THE HONEST ROUNDS' PAYER CALLED. Statements and proofs over
E2E/KeyEvalJoin.lean. NOTHING IS CLAIMED OF ANY PROVER: it is conditional throughout.

What is shown.
  **`readsCode_of_moves`**: THE PREMISE ON WHAT WAS HEARD, PAID AT THE HONEST ROUNDS: where the
    rounds that the batching's text is handed are the kind's honest prover's (`movesAtM3`,
    Johnson/Desc/K13/Honest/MovesAtM3.lean) at the slots that the text takes: whatever letters the
    text reads off them, `ReadsCode` holds of these letters: by that prover's own law
    (`codeHeard_reads`, Johnson/Desc/K13/Honest/Accepts.lean).
  **`eval_says_of_both`**: the batching's text accepts · the text behind W's commitment (`K13.rows`)
    accepts at the claim made of THE ROW THAT THE BATCHING HAS RETURNED · FOUR TIES BETWEEN THE TWO
    AND THE JOB, each a premise by name: the shape is the job's (by the statement's form) · the
    codes of the state in front are the job's · W's number is the job's first ⟹ the text has laid a
    row r among its own group's open rows, r is (Eval), and r says its claim, at the statement that
    the text leaves, of the words behind W's sending.

Limits. As E2E/KeyEvalJoin.lean's. The pile's rows' truth at the words in front stays a premise. In
`readsCode_of_moves` the witness is any; that the honest side's part SENDS these rounds is not shown
here. FOR THE HONEST W ALONE. Nothing on soundness. Nothing on hiding follows from this file.


-/
import E2E.KeyEvalJoin
import Johnson.Desc.K13.Honest.Accepts

set_option autoImplicit false

namespace AtPublicFiles.Key
open OnBytes OnBytes.Params OnBytes.Means
open OnBytes.Slice (GF GE readE toF)
open ProofFile.Honest (State Seen Cs)
open ProofFile.Honest.K1 (SendJob Ride dueR)
open Johnson.Prover.Send (held Rows)
open VerifiableInference.Desc.Key (Pieces)
open VerifiableInference.Desc.K13 (batt St oneDrawn heard)
open VerifiableInference.Desc.K13.Law (ρg lowBits EvalIn witOf Wit)
open VerifiableInference.Desc.K13.Honest (ReadsCode movesAtM3 codeHeard_reads codeHeard maskAt
  tabsOf heard_roundsOf)

/-- **At the honest rounds the premise on what was heard is paid.** σ: a section of the reading. -/
theorem readsCode_of_moves {nR k : ℕ} (σ : GE → E) (hσ : ∀ a, ρg.val (σ a) = a) (w : Wit GE nR k)
    (pile : List TensorRow) (ledger : ℕ) (d : St) (t : List ℕ × St)
    (ht : VerifiableInference.Desc.Ground.takeMasksP d ledger (Batt.masksOf k) = some t)
    (x₀ eps : E) (gs : List E) (hg : gs.length = k) :
    ∀ r rs' x u hd,
      movesAtM3 ρg σ w pile (t.1.map fun i => ⟨ledger, i⟩) x₀ eps gs = r :: rs' →
      oneDrawn "K13.sigma-one-drawn" r = .ok x →
      VerifiableInference.Desc.Ground.takeMasksP d ledger (Batt.masksOf k) = some u →
      heard rs' = .ok hd → ReadsCode ρg w pile (u.1.map fun i => ⟨ledger, i⟩) x hd := by
  intro r rs' x u hd hm hx hu hh
  obtain rfl : t = u := Option.some.inj (ht.symm.trans hu)
  obtain ⟨rfl, rfl⟩ := List.cons.inj hm
  obtain rfl : x₀ = x := Except.ok.inj hx
  have e := heard_roundsOf (codeHeard ρg σ (maskAt w (t.1.map fun i => ⟨ledger, i⟩))
    (tabsOf ρg w pile (ρg.val x₀)) k eps gs) rfl
  obtain rfl := Except.ok.inj (e.symm.trans hh)
  exact codeHeard_reads ρg σ hσ w pile _ x₀ eps gs hg

section
variable {W X : Type} (entry : W → Nat → Nat → GF) (one : OneTime) (N : Pieces)
  (groups : List (List Nat)) (first : Nat) (ride : Nat → Option Ride)
  (points : List Fmt.Drawn → Nat → Nat → List E)

/-- **FROM THE ACCEPTANCE OF BOTH TEXTS.** -/
theorem eval_says_of_both (base : Nat) (J : SendJob W X)
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
    (hrows : ∀ r ∈ pile, VerifiableInference.Desc.K13.Law.Holds ρg (witOf mat w₀) r)
    (hfront : ∀ r ∈ pile, ∀ u ∈ r.masks, u.1.oracle < first) (hled : ledger < first)
    (hc : ∀ r rs' x u hd, rs = r :: rs' → oneDrawn "K13.sigma-one-drawn" r = .ok x →
      VerifiableInference.Desc.Ground.takeMasksP d ledger (Batt.masksOf one.lin.kCol) = some u →
      heard rs' = .ok hd →
      ReadsCode ρg (witOf mat w₀) pile (u.1.map fun i => ⟨ledger, i⟩) x hd)
    {ids : Array ℕ} {d' : St} {o' : LinFirst × St}
    (hrw : VerifiableInference.Desc.K13.rows one.lin (memberClaim out.1) ids d' = .ok o')
    (hcodes : d'.st.codes = one.codes) (hw : o'.1.w = first) :
    ∃ (r : OnBytes.Row) (G' : Group),
      linEvalRow one.lin (memberClaim out.1) first (linLayW one.codes one.lin) = some r ∧
      o'.2.st.groups[o'.1.own]? = some G' ∧ r ∈ G'.rows.toList ∧
      Says ρg o'.2.st r (held w₀ first J.P (J.rows c s t n)) := by
  obtain ⟨r, -, he, hin, G', hG, hr⟩ := evalIn_of_rows hrw (by rw [hcodes]; exact hbits)
  rw [hcodes, hw] at he hin
  exact ⟨r, G', he, hG, hr,
    eval_says_of_batt entry one N groups first ride points base J hJ hans hmask hdeg c s t n w₀ mat
      hmat hbits hfit hb hl hp hrows hfront hled (Nat.lt_of_le_of_lt (Nat.zero_le _) hled) hc r he
      _ hin⟩

end

end AtPublicFiles.Key

#print axioms AtPublicFiles.Key.readsCode_of_moves
#print axioms AtPublicFiles.Key.eval_says_of_both
