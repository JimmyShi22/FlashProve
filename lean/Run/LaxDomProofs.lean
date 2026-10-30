-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/LaxDomProofs.lean: the proofs of the statements of Run/LaxDom.lean.

Main names (statements and hypotheses: Run/LaxDom.lean):
  `lax_dom`: the lenient parser `parseLaxW` at two hash functions that agree on the domain.
  `lax_HO`: the same parser at `Fmt.HO Fmt.oracle` and at `Fmt.formatHash`.
The domain is `Fmt.hDom`. What is not claimed: Run/LaxDom.lean, the head, 4.

`dom162`, `dom0`: under their hypotheses, a call's data lie in the domain.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.LaxDom

set_option autoImplicit false

namespace Run
open _root_.Fmt (hDom dlen Kind Chain Plan Spec St)

theorem idb {α β : Type} (x : Id α) (f : α → Id β) : (x >>= f) = f x := rfl
theorem idp {α : Type} (a : α) : (pure a : Id α) = a := rfl

section
variable (h h' : HId) (ha : ∀ n t i s b, hDom n t i s b = true → h' n t i s b = h n t i s b)
  (hz : ∀ n t i s b, ByteArray.size (h n t i s b) = dlen n)

theorem dom162 (lab : Nat) (rho : ByteArray) (i : Nat) (msg : ByteArray) (kind : Kind)
    (w nonce j : Nat) (hk : _root_.Fmt.askOK lab rho i msg kind w nonce = true)
    (hi : i < 2 ^ 63) (hm : msg.size + 16 ≤ 2 ^ 32 - 144) :
    hDom 162 lab i rho (msg ++ _root_.Fmt.tail kind w nonce j) = true := by
  simp only [_root_.Fmt.askOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hk
  have hs : (msg ++ _root_.Fmt.tail kind w nonce j).size = msg.size + 16 := by
    simp only [_root_.Fmt.tail, ByteArray.size_append, _root_.Fmt.size_u64n]
  simp only [hDom, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true, hs]
  refine ⟨⟨⟨⟨⟨⟨⟨by decide, hk.1.1.1.1.1.1.1⟩, Or.inl (by decide)⟩, ?_⟩, hm⟩, hk.1.1.1.1.1.1.2⟩,
      Or.inl (by decide)⟩,
    _root_.Fmt.leafOK_other _ _ _ rfl⟩
  simp only [_root_.Fmt.idxOK, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
  exact ⟨⟨hi, Or.inl (by decide)⟩, Or.inl (by decide)⟩

include ha in
theorem fetchFrom_dom (lab : Nat) (rho : ByteArray) (i : Nat) (msg : ByteArray) (kind : Kind)
    (w nonce : Nat) (hd : ∀ j, hDom 162 lab i rho (msg ++ _root_.Fmt.tail kind w nonce j) = true) :
    ∀ (n j : Nat) (acc : Array ByteArray),
      _root_.Fmt.fetchFrom (m := Id) h' lab rho i msg kind w nonce n j acc =
        _root_.Fmt.fetchFrom (m := Id) h lab rho i msg kind w nonce n j acc
  | 0, _, _ => rfl
  | n + 1, j, acc => by
    simp only [_root_.Fmt.fetchFrom, _root_.Fmt.callW, idb]
    rw [ha _ _ _ _ _ (hd j)]
    exact fetchFrom_dom lab rho i msg kind w nonce hd n _ _

include ha in
theorem laxQueryW_dom (c : Chain) (msg : ByteArray) (kind : Kind) (work nonce K : Nat)
    (hi : c.round + 1 < 2 ^ 63) (hm : msg.size + 16 ≤ 2 ^ 32 - 144) :
    laxQueryW (m := Id) h' c msg kind work nonce K =
      laxQueryW (m := Id) h c msg kind work nonce K := by
  unfold laxQueryW
  split
  · rename_i hk
    simp only [_root_.Fmt.fetchW, idb]
    rw [fetchFrom_dom h h' ha c.label c.rho (c.round + 1) msg kind work nonce fun j =>
        dom162 _ _ _ _ _ _ _ j hk hi hm]
  · rfl


/-- What the step without the work test hands on: the next round's number. -/
theorem laxQueryW_round (c : Chain) (msg : ByteArray) (kind : Kind) (work nonce K : Nat)
    (c' : Chain) (vb : Array ByteArray)
    (e : laxQueryW (m := Id) h c msg kind work nonce K = some (c', vb)) :
    c'.round = c.round + 1 := by
  unfold laxQueryW at e
  split at e
  · simp only [idb, idp] at e
    have e' := congrArg (fun o => o.map fun x => x.1.round) e
    exact (Option.some.inj e').symm
  · cases e


theorem slice_size (b : ByteArray) (i n : Nat)
    (x : ByteArray) (e : _root_.Fmt.slice b i n = some x) : x.size ≤ b.size := by
  unfold _root_.Fmt.slice at e
  split at e
  · cases e
    rw [ByteArray.size_extract]
    omega
  · cases e

include ha in
/-- One round. That the round's number goes up by one is `cutStep_round`, below. -/
theorem cutStep_dom (ops : OpsW Id) (P : Plan) (run : Option ByteArray) (b : ByteArray) (s : St)
    (r : _root_.Fmt.Round) (hi : s.chain.round + 1 < 2 ^ 63) (hb : b.size + 16 ≤ 2 ^ 32 - 144) :
    cutStep (m := Id) h' ops P run b s r = cutStep (m := Id) h ops P run b s r := by
  unfold cutStep
  cases hs : _root_.Fmt.slice b s.pos r.entry.msg with
  | none => rfl
  | some msg =>
    dsimp only
    cases _root_.Fmt.whole (_root_.Fmt.readItems P.field r.items) msg with
    | none => rfl
    | some vals =>
      dsimp only
      cases _root_.Fmt.readNonce P r.entry.work b (s.pos + r.entry.msg) with
      | none => rfl
      | some ni =>
        dsimp only
        rw [laxQueryW_dom h h' ha s.chain msg r.kind r.entry.work ni.1 _ hi
            (by have := slice_size b _ _ msg hs; omega)]

theorem cutStep_round (ops : OpsW Id) (P : Plan) (run : Option ByteArray) (b : ByteArray)
    (s s' : St) (r : _root_.Fmt.Round) (e : cutStep (m := Id) h ops P run b s r = some s') :
    s'.chain.round = s.chain.round + 1 := by
  unfold cutStep at e
  split at e
  · cases e
  · split at e
    · cases e
    · split at e
      · cases e
      · rename_i nonce i1 _
        simp only [idb] at e
        cases hq : laxQueryW (m := Id) h s.chain _ r.kind r.entry.work nonce
            ((_root_.Fmt.wordsAtMost r.entry r.kind + 3) / 4) with
        | none => rw [hq] at e; cases e
        | some cv =>
          rw [hq] at e
          dsimp only at e
          split at e
          · cases e
          · split at e
            · cases e
            · cases e
              exact laxQueryW_round h _ _ _ _ _ _ cv.1 cv.2 hq

include ha in
theorem cutFold_dom (ops : OpsW Id) (P : Plan) (run : Option ByteArray)
    (b : ByteArray) (hb : b.size + 16 ≤ 2 ^ 32 - 144) :
    ∀ (rs : List _root_.Fmt.Round) (s : St), s.chain.round + rs.length < 2 ^ 63 →
      cutFold (m := Id) h' ops P run b rs s = cutFold (m := Id) h ops P run b rs s
  | [], _, _ => rfl
  | r :: rs, s, hi => by
    have hi' : s.chain.round + 1 < 2 ^ 63 := by simp only [List.length_cons] at hi; omega
    simp only [cutFold, idb]
    rw [cutStep_dom h h' ha ops P run b s r hi' hb]
    cases hc : cutStep (m := Id) h ops P run b s r with
    | none => rfl
    | some s' =>
      dsimp only
      exact cutFold_dom ops P run b hb rs s'
        (by rw [cutStep_round h ops P run b s s' r hc]; simp only [List.length_cons] at hi; omega)

theorem dom0 (n i : Nat) (bytes : ByteArray)
    (hn : _root_.Fmt.isNumber n = true) (hl : _root_.Fmt.isLeaf n = false)
    (hx : _root_.Fmt.idxOK n i = true) (hb : bytes.size ≤ 2 ^ 32 - 144) :
    hDom n 0 i _root_.Fmt.zero32 bytes = true := by
  simp only [hDom, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true]
  refine ⟨⟨⟨⟨⟨⟨⟨hn, ?_⟩, ?_⟩, hx⟩, hb⟩, ?_⟩, ?_⟩, _root_.Fmt.leafOK_other _ _ _ hl⟩
  · unfold _root_.Fmt.treeBound
    split <;> decide
  · exact Or.inr trivial
  · exact _root_.Fmt.size_zeros 32
  · exact Or.inr rfl

include ha hz in
theorem startChainW_dom (lab : Nat) (pd statement : ByteArray) (rnd : Option ByteArray)
    (hp : pd.size = 32) (hst : statement.size + 88 ≤ 2 ^ 32 - 144) :
    _root_.Fmt.startChainW (m := Id) h' lab pd statement rnd =
      _root_.Fmt.startChainW (m := Id) h lab pd statement rnd := by
  unfold _root_.Fmt.startChainW
  split
  · rename_i hl
    have hx : ∀ n, n = 160 ∨ n = 172 → _root_.Fmt.idxOK n lab = true := by
      intro n hn
      simp only [_root_.Fmt.idxOK, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true]
      rcases hn with rfl | rfl
      · exact ⟨⟨by omega, Or.inl (by decide)⟩, Or.inl (by decide)⟩
      · exact ⟨⟨by omega, Or.inl (by decide)⟩, Or.inl (by decide)⟩
    cases rnd with
    | none =>
      simp only [_root_.Fmt.firstValueW, idb]
      rw [ha _ _ _ _ _ (dom0 160 lab _ (by decide) (by decide) (hx 160 (Or.inl rfl)) (by
        simp only [_root_.Fmt.firstBytes, ByteArray.size_append, _root_.Fmt.size_u64n, hp]
        have : ByteArray.empty.size = 0 := rfl
        omega))]
    | some b =>
      dsimp only
      split
      · rename_i hb32
        simp only [_root_.Fmt.runValueW, _root_.Fmt.firstValueW, idb]
        rw [ha _ _ _ _ _
            (dom0 172 lab (pd ++ b) (by decide) (by decide) (hx 172 (Or.inr rfl))
              (by rw [ByteArray.size_append, hp, hb32]; decide))]
        split
        · rw [ha _ _ _ _ _ (dom0 160 lab _ (by decide) (by decide) (hx 160 (Or.inl rfl)) (by
            simp only [_root_.Fmt.firstBytes, ByteArray.size_append, _root_.Fmt.size_u64n, hp, hz]
            have : ByteArray.empty.size = 0 := rfl
            have : dlen 172 = 32 := rfl
            omega))]
        · rfl
      · rfl
  · rfl

include ha hz in
theorem cutChain_dom (ops : ByteArray → OpsW Id) (S : Spec) (b : ByteArray)
    (i : Nat) (hS : smallB S b = true) :
    cutChain (m := Id) h' ops S b i = cutChain (m := Id) h ops S b i := by
  simp only [smallB, Bool.and_eq_true, decide_eq_true_eq] at hS
  unfold cutChain
  split
  · rfl
  · dsimp only
    split
    · rfl
    · simp only [_root_.Fmt.paramsDigestW, idb]
      rw [ha _ _ _ _ _ (dom0 169 1 S.params (by decide) (by decide) (by decide) hS.1.1.1),
        startChainW_dom h h' ha hz S.label _ S.statement _ (hz _ _ _ _ _) hS.1.1.2]
      cases _root_.Fmt.startChainW
          (m := Id) h S.label (h 169 0 1 _root_.Fmt.zero32 S.params) S.statement _ with
      | none => rfl
      | some hd =>
        dsimp only
        rw [cutFold_dom h h' ha (ops b) S.plan hd.run b hS.1.2 S.rounds _ (by simpa using hS.2)]

include ha hz in
theorem laxWhole_dom (S : Spec) (b : ByteArray) (hS : smallB S b = true) :
    laxWhole (m := Id) h' S b = laxWhole (m := Id) h S b := by
  unfold laxWhole cutWhole
  rw [cutChain_dom h h' ha hz _ S b 0 hS]

include ha hz in
theorem parseLaxW_dom {Y : Type} {E : Iop.ExtSpec} {Q : Iop.BatchInteractiveOracleProof Y E} (S : Spec)
    (T : Typing Q) (b : ByteArray) (hS : smallB S b = true) :
    parseLaxW (m := Id) h' S T b = parseLaxW (m := Id) h S T b := by
  unfold parseLaxW
  rw [laxWhole_dom h h' ha hz S b hS]

end

/-- At the format's oracle. -/
theorem parseLaxW_HO {Y : Type} {E : Iop.ExtSpec} {Q : Iop.BatchInteractiveOracleProof Y E} (S : Spec) (T : Typing Q)
    (b : ByteArray) (hS : smallB S b = true) :
    parseLaxW (m := Id) (_root_.Fmt.HO _root_.Fmt.oracle) S T b =
      parseLaxW (m := Id) _root_.Fmt.formatHash S T b :=
  parseLaxW_dom (h := _root_.Fmt.formatHash) (h' := _root_.Fmt.HO _root_.Fmt.oracle)
    (fun n t i s b hd => _root_.Fmt.HO_oracle n t i s b hd)
    (fun n t i s b => _root_.Fmt.size_H n t i s b) S T b hS

theorem lax_dom : Spec.lax_dom := fun h h' ha hz _ _ _ S T b hS => parseLaxW_dom h h' ha hz S T b hS

theorem lax_HO : Spec.lax_HO := fun _ _ _ S T b hS => parseLaxW_HO S T b hS

end Run
