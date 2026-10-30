-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/PendRow.lean: the text of the pending row and the routine of the program
`verify-on-bytes` on what a sub-proof leaves for the weights' table are tied: where the one returns,
the other returns, and the row is made of that return. Theorems with their proofs. No Mathlib.

`pendingRowO` (Johnson/Desc/First/Pend/Row.lean) is the text that a link's end runs: it has its own
span of rows and its own adding of a claim's weights. `wsPending` (OnBytes/Model/Pending.lean) is
the routine of the program `verify-on-bytes`, of whose return
the laws of the kinds that leave a claim on the weights
speak. General in the layout, in what was left, in the number of claims and in the shape: nothing
here is of one kind.

Main names:
  `span_eq`: `Pend.span` is `wsSpan`. `addClaim_eq`: `Pend.addClaim lay G c` is
    `wsGammaAdd G lay c oneE`. `gamma_eq`: so the two folds over the claims are one.
  `pend_inv`: where `pendingRowO` returns a row r and the messages behind: `wsPending` returns a w;
    the message number im has a ledger l; `takeEntry l` gives an entry c and a ledger l'; r has w's
    weights, point and target, and the one mask entry (message im, entry c) with w's factor; the
    messages behind are those in front with l' laid; and w's point, factor and target are what was
    left: the merge's point reversed, its last challenge, its shown end value.
  `pend_of`: the way back: where `wsPending` returns and the ledger has an entry to give,
    `pendingRowO` returns just that row.

The weights on a stretch of rows as vectors of product form: where the text calls the description's
own routine (Johnson/Desc/Own/Stretch.lean), that routine's agreement with the routine of the
program `verify-on-bytes` (`weightsOnRows_agrees`, StretchAgree.lean beside it) is spent.

Limits. Identities on two texts: no random step. What a row means is not said here. Nothing on
soundness or on hiding.

-/
import Johnson.Desc.First.Pend.Row
import Johnson.Desc.Own.StretchAgree
import OnBytes.Model.Pending

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes OnBytes.Params OnBytes.Model
open VerifiableInference.Desc.First.Pend (pendingRowO span addClaim takeEntry badRows badCount)

/-- The two texts of the span are one function. -/
theorem span_eq (lay : WsLay) (recs : List WsRecClaim) : span lay recs = wsSpan lay recs := by
  unfold span wsSpan
  congr 1
  funext r c
  cases lay.U[c.ui]? <;> rfl

/-- The two texts that add a claim's weights are one function. -/
theorem addClaim_eq (lay : WsLay) (G : Array E) (c : WsRecClaim) :
    addClaim lay G c = wsGammaAdd G lay c oneE := by
  unfold addClaim wsGammaAdd
  cases lay.U[c.ui]? with
  | none => rfl
  | some u =>
    by_cases h1 : ((wsGamma u c oneE).size == u.rows) = true
    · by_cases h2 : (c.f.length == u.g.length) = true
      · by_cases h3 : u.off + u.rows ≤ G.size
        · have h3' : ¬ G.size < u.off + u.rows := by omega
          simp [h1, h2, h3, h3', bind, Except.bind, pure, Except.pure, bne]
        · have h3' : G.size < u.off + u.rows := by omega
          simp [h1, h2, h3, h3', bind, Except.bind, badRows, throw, throwThe, MonadExceptOf.throw,
            bne, pure, Except.pure]
      · simp [h1, h2, bind, Except.bind, badRows, throw, throwThe, MonadExceptOf.throw, bne, pure,
          Except.pure]
    · simp [h1, bind, Except.bind, badRows, throw, throwThe, MonadExceptOf.throw, bne]

/-- The two folds that make the weights on the rows are one. -/
theorem gamma_eq (lay : WsLay) (recs : List WsRecClaim) (G : Array E) :
    recs.foldlM (addClaim lay) G = recs.foldlM (fun G c => wsGammaAdd G lay c oneE) G := by
  congr 1
  funext G c
  exact addClaim_eq lay G c

/-- **Where the text of the pending row returns, the routine of the program `verify-on-bytes`
returns, and the row is made of its return** at the entry that the ledger gives. -/
theorem pend_inv {lay : WsLay} {im : Nat} {o : WsForkOut} {claims : Nat} {S : LinShape}
    {os os' : Array Oracle} {r : TensorRow}
    (h : pendingRowO lay im o claims S os = .ok (r, os')) :
    ∃ w l c l', wsPending lay o claims S = .ok w ∧ (os[im]?).bind (·.ledger) = some l ∧
      takeEntry l = some (c, l') ∧
      r = { g := w.g, psi := w.psi, masks := [(⟨im, c⟩, w.beta)], target := w.target } ∧
      os' = (os.modify im fun x => { x with ledger := some l' }) ∧
      w.psi = o.rm.toList.reverse ∧ w.beta = o.beta ∧ w.target = o.fvp := by
  by_cases t4 : (lay.m0 == S.matrixRows) = true
  case neg =>
    simp [pendingRowO, bind, Except.bind, t4] at h
  by_cases t5 : (!o.recs.isEmpty) = true
  case neg =>
    simp [pendingRowO, bind, Except.bind, pure, Except.pure, t4, t5] at h
  by_cases t6 : (o.recs.length == claims) = true
  case neg =>
    simp [pendingRowO, bind, Except.bind, pure, Except.pure, t4, t5, t6] at h
  by_cases t7 : (o.rm.size == lay.lk) = true
  case neg =>
    simp [pendingRowO, bind, Except.bind, pure, Except.pure, t4, t5, t6, t7] at h
  cases hs : span lay o.recs with
  | error e =>
    simp [pendingRowO, bind, Except.bind, pure, Except.pure, t4, t5, t6, t7, hs] at h
  | ok fl =>
  by_cases t9 : fl.1 < fl.2
  case neg =>
    simp [pendingRowO, bind, Except.bind, pure, Except.pure, t4, t5, t6, t7, hs, t9] at h
  by_cases t10 : fl.2 ≤ lay.m0
  case neg =>
    simp [pendingRowO, bind, Except.bind, pure, Except.pure, t4, t5, t6, t7, hs, t9, t10] at h
  by_cases t11 : S.kRow ≤ 62
  case neg =>
    simp [pendingRowO, bind, Except.bind, pure, Except.pure, t4, t5, t6, t7, hs, t9, t10, t11] at h
  by_cases t12 : lay.m0 ≤ 2 ^ S.kRow
  case neg =>
    simp [pendingRowO, bind, Except.bind, pure, Except.pure, t4, t5, t6, t7, hs, t9, t10, t11,
      t12] at h
  cases hG : o.recs.foldlM (addClaim lay) (Array.replicate fl.2 zeroE) with
  | error e =>
    simp [pendingRowO, bind, Except.bind, pure, Except.pure, t4, t5, t6, t7, hs, t9, t10, t11, t12,
      hG] at h
  | ok Gamma =>
  cases hm : memberWeightsOnRows S fl.1 (Gamma.extract fl.1 fl.2) with
  | none =>
    simp [pendingRowO, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
      t4, t5, t6, t7, hs, t9, t10, t11, t12, hG, hm, ← Own.weightsOnRows_agrees] at h
  | some g =>
  cases hl : (os[im]?).bind (·.ledger) with
  | none =>
    simp [pendingRowO, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
      t4, t5, t6, t7, hs, t9, t10, t11, t12, hG, hm, hl, ← Own.weightsOnRows_agrees] at h
  | some l =>
  cases ht : takeEntry l with
  | none =>
    simp [pendingRowO, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
      t4, t5, t6, t7, hs, t9, t10, t11, t12, hG, hm, hl, ht, ← Own.weightsOnRows_agrees] at h
  | some cl =>
  simp [pendingRowO, bind, Except.bind, pure, Except.pure, t4, t5, t6, t7, hs, t9, t10, t11, t12,
    hG, hm, hl, ht, ← Own.weightsOnRows_agrees] at h
  refine ⟨{ g := g, psi := o.rm.toList.reverse, beta := o.beta, target := o.fvp }, l, cl.1, cl.2,
      ?_,
    rfl, ht, h.1.symm, h.2.symm, rfl, rfl, rfl⟩
  rw [span_eq] at hs
  rw [gamma_eq] at hG
  have c4 : (lay.m0 != S.matrixRows) = false := by simpa [bne] using t4
  have c5 : (o.recs.isEmpty || o.recs.length != claims || o.rm.size != lay.lk) = false := by
    simp only [Bool.or_eq_false_iff, bne, Bool.not_eq_false']
    exact ⟨⟨by simpa using t5, t6⟩, t7⟩
  have c9 : ¬ (fl.2 ≤ fl.1 ∨ lay.m0 < fl.2 ∨ 62 < S.kRow ∨ 2 ^ S.kRow < lay.m0) := by omega
  simp [wsPending, c4, c5, hs, hG, hm, bind, Except.bind, pure, Except.pure]
  exact ⟨⟨⟨t9, t10⟩, t11⟩, t12⟩

/-- **And back**: where the routine of the program `verify-on-bytes` returns and the ledger has an
entry to give, the text of the pending row returns the row made of that return. -/
theorem pend_of {lay : WsLay} {im : Nat} {o : WsForkOut} {claims : Nat} {S : LinShape}
    {os : Array Oracle} {w : WsPending} {l l' : Ledger} {c : Nat}
    (hw : wsPending lay o claims S = .ok w) (hl : (os[im]?).bind (·.ledger) = some l)
    (ht : takeEntry l = some (c, l')) :
    pendingRowO lay im o claims S os =
      .ok ({ g := w.g, psi := w.psi, masks := [(⟨im, c⟩, w.beta)], target := w.target },
        os.modify im fun x => { x with ledger := some l' }) := by
  by_cases c4 : (lay.m0 != S.matrixRows) = true
  case pos =>
    simp [wsPending, bind, Except.bind, c4] at hw
  by_cases c5 : (o.recs.isEmpty || o.recs.length != claims || o.rm.size != lay.lk) = true
  case pos =>
    simp [wsPending, bind, Except.bind, pure, Except.pure, c4, c5] at hw
  cases hs : wsSpan lay o.recs with
  | error e =>
    simp [wsPending, bind, Except.bind, pure, Except.pure, c4, c5, hs] at hw
  | ok fl =>
  by_cases c9 : (decide (fl.2 ≤ fl.1) || decide (lay.m0 < fl.2) || decide (62 < S.kRow) ||
      decide (2 ^ S.kRow < lay.m0)) = true
  case pos =>
    simp [wsPending, bind, Except.bind, pure, Except.pure, c4, c5, hs, c9] at hw
  cases hG : o.recs.foldlM (fun G c => wsGammaAdd G lay c oneE) (Array.replicate fl.2 zeroE) with
  | error e =>
    simp [wsPending, bind, Except.bind, pure, Except.pure, c4, c5, hs, c9, hG] at hw
  | ok Gamma =>
  cases hm : memberWeightsOnRows S fl.1 (Gamma.extract fl.1 fl.2) with
  | none =>
    simp [wsPending, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw,
      c4, c5, hs, c9, hG, hm] at hw
  | some g =>
  simp [wsPending, bind, Except.bind, pure, Except.pure, c4, c5, hs, c9, hG, hm] at hw
  subst hw
  rw [← span_eq] at hs
  rw [← gamma_eq] at hG
  have t4 : (lay.m0 == S.matrixRows) = true := by simpa [bne] using c4
  simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, bne, Bool.not_eq_false',
    decide_eq_true_eq] at c5 c9
  have t5 : (!o.recs.isEmpty) = true := by simp [c5.1.1]
  have t9 : fl.1 < fl.2 := by omega
  have t10 : fl.2 ≤ lay.m0 := by omega
  have t11 : S.kRow ≤ 62 := by omega
  have t12 : lay.m0 ≤ 2 ^ S.kRow := by omega
  simp [pendingRowO, bind, Except.bind, pure, Except.pure, t4, t5, c5.1.2, c5.2, hs, t9, t10, t11,
    t12, hG, hm, hl, ht, ← Own.weightsOnRows_agrees]

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.pend_of
#print axioms VerifiableInference.Desc.First.MergeLaw.pend_inv
