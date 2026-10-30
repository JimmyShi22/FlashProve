-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/StrictDomProofs.lean: the proofs of the statements of Run/StrictDom.lean.

Main names (statements and hypotheses: Run/StrictDom.lean):
  `strict_dom`: the strict reader `Fmt.wholeChain` at two hash functions that agree on the domain.
  `strict_HO`: the strict verifier at `Fmt.HO Fmt.oracle` and at `Fmt.formatHash`.
  `run_strict`: the strict verifier's acceptance and the run functions `PQ.runLaxSP`, `PQ.runLaxS`.
    A run function's acceptance does not carry over by this statement.
The domain is `Fmt.hDom`. What is not claimed, above all on soundness and on the converse:
Run/StrictDom.lean, the head, 3 and 4.

`readOpens_dom` uses `readOpeningW_dom` (Run/OpenDomProofs.lean); the record of vertices does not
hash.

Terms: lean/GLOSSARY.md.
-/
import Run.StrictDom
import Run.OpenDomProofs
import Run.PageIsRunProofs

set_option autoImplicit false

namespace Run
open _root_.Fmt (hDom dlen Plan Spec Shape Src Chain St Seen Kind)

section
variable (h h' : HId) (ha : ∀ n t i s b, hDom n t i s b = true → h' n t i s b = h n t i s b)
  (hz : ∀ n t i s b, ByteArray.size (h n t i s b) = dlen n)

include ha in
theorem queryW_dom (c : Chain) (msg : ByteArray) (kind : Kind) (work nonce K : Nat)
    (hi : c.round + 1 < 2 ^ 63) (hm : msg.size + 16 ≤ 2 ^ 32 - 144) :
    Chain.queryW (m := Id) h' c msg kind work nonce K =
      Chain.queryW (m := Id) h c msg kind work nonce K := by
  unfold Chain.queryW
  split
  · rename_i hk
    simp only [_root_.Fmt.fetchW, idb]
    rw [fetchFrom_dom h h' ha c.label c.rho (c.round + 1) msg kind work nonce
        (fun j => dom162 _ _ _ _ _ _ _ j hk hi hm)]
  · rfl

theorem queryW_round (c : Chain) (msg : ByteArray) (kind : Kind) (work nonce K : Nat) (c' : Chain)
    (vb : Array ByteArray) (e : Chain.queryW (m := Id) h c msg kind work nonce K = some (c', vb)) :
    c'.round = c.round + 1 := by
  unfold Chain.queryW at e
  split at e
  · simp only [idb, idp] at e
    split at e
    · have e' := congrArg (fun o => o.map fun x => x.1.round) e
      exact (Option.some.inj e').symm
    · cases e
  · cases e

include ha hz in
theorem readOpens_dom (cfg : ByteArray) (P : Plan) (run : Option ByteArray)
    (roots : Array ByteArray) (poss : List Nat) (b : ByteArray) (hc : cfg.size = 32)
    (hr : ∀ x, run = some x → x.size = 32) :
    ∀ (os : List (Shape × Src)), os.all (smallO P.salt) = true →
      ∀ (sn : Seen) (i : Nat), _root_.Fmt.readOpens (m := Id) h' cfg P run roots poss b os sn i =
        _root_.Fmt.readOpens (m := Id) h cfg P run roots poss b os sn i
  | [], _, _, _ => rfl
  | (sh, src) :: os, ho, sn, i => by
    have ho' := Bool.and_eq_true_iff.1
      (by
        simpa [List.all_cons] using ho : (smallO P.salt (sh, src) && os.all (smallO P.salt)) = true)
    have hsh : smallSh P.salt sh = true := (Bool.and_eq_true_iff.1 ho'.1).1
    unfold _root_.Fmt.readOpens
    dsimp only
    split
    · rfl
    · rename_i root start hrs
      have hst : start.size = 32 := by
        cases src with
        | own n =>
          dsimp only at hrs
          split at hrs
          · rename_i r s _ hs
            cases hrs
            exact hr _ rfl
          · cases hrs
        | given r s =>
          cases hrs
          exact beq_iff_eq.1 (Bool.and_eq_true_iff.1 ho'.1).2
      simp only [idb]
      rw [readOpeningW_dom h h' ha hz cfg P.field P.salt sh start _ b i hc hst hsh]
      cases _root_.Fmt.readOpeningW (m := Id) h cfg P.field P.salt sh start
          (_root_.Fmt.listOf (poss.map (· % 2 ^ sh.a))) b i with
      | none => rfl
      | some o =>
        dsimp only
        split
        · split
          · rfl
          · rename_i sn' _
            rw [readOpens_dom cfg P run roots poss b hc hr os ho'.2 sn' o.next]
        · rfl


include ha hz in
theorem step_dom (cfg : ByteArray) (P : Plan) (run : Option ByteArray) (b : ByteArray) (s : St)
    (r : _root_.Fmt.Round) (hi : s.chain.round + 1 < 2 ^ 63) (hb : b.size + 16 ≤ 2 ^ 32 - 144)
    (hc : cfg.size = 32) (hr : ∀ x, run = some x → x.size = 32)
    (ho : r.opens.all (smallO P.salt) = true) :
    _root_.Fmt.step (m := Id) h' cfg P run b s r = _root_.Fmt.step (m := Id) h cfg P run b s r := by
  unfold _root_.Fmt.step
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
        rw [queryW_dom h h' ha s.chain msg r.kind r.entry.work ni.1 _ hi
            (by have := slice_size b _ _ msg hs; omega)]
        simp only [readOpens_dom h h' ha hz cfg P run _ _ b hc hr r.opens ho]

theorem step_round (cfg : ByteArray) (P : Plan) (run : Option ByteArray) (b : ByteArray) (s s' : St)
    (r : _root_.Fmt.Round) (e : _root_.Fmt.step (m := Id) h cfg P run b s r = some s') :
    s'.chain.round = s.chain.round + 1 := by
  unfold _root_.Fmt.step at e
  split at e
  · cases e
  · split at e
    · cases e
    · split at e
      · cases e
      · simp only [idb] at e
        split at e
        · cases e
        · rename_i c vb hq
          split at e
          · cases e
          · split at e
            · cases e
            · cases e
              exact queryW_round h _ _ _ _ _ _ c vb hq

include ha hz in
theorem foldRounds_dom (cfg : ByteArray) (P : Plan) (run : Option ByteArray) (b : ByteArray)
    (hb : b.size + 16 ≤ 2 ^ 32 - 144) (hc : cfg.size = 32) (hr : ∀ x, run = some x → x.size = 32) :
    ∀ (rs : List _root_.Fmt.Round) (s : St), s.chain.round + rs.length < 2 ^ 63 →
      (∀ r ∈ rs, r.opens.all (smallO P.salt) = true) →
      _root_.Fmt.foldRounds (m := Id) h' cfg P run b rs s =
        _root_.Fmt.foldRounds (m := Id) h cfg P run b rs s
  | [], _, _, _ => rfl
  | r :: rs, s, hi, ho => by
    have hi' : s.chain.round + 1 < 2 ^ 63 := by simp only [List.length_cons] at hi; omega
    simp only [_root_.Fmt.foldRounds, idb]
    rw [step_dom h h' ha hz cfg P run b s r hi' hb hc hr (ho r (List.mem_cons_self ..))]
    cases hst : _root_.Fmt.step (m := Id) h cfg P run b s r with
    | none => rfl
    | some s' =>
      dsimp only
      exact foldRounds_dom cfg P run b hb hc hr rs s'
        (by rw [step_round h cfg P run b s s' r hst]; simp only [List.length_cons] at hi; omega)
        (fun r' hr' => ho r' (List.mem_cons_of_mem _ hr'))

include ha hz in
theorem readChain_dom (S : Spec) (seen : Seen) (b : ByteArray) (i : Nat) (hS : smallF S b = true) :
    _root_.Fmt.readChain (m := Id) h' S seen b i = _root_.Fmt.readChain (m := Id) h S seen b i := by
  have h1 := Bool.and_eq_true_iff.1 hS
  have h2 := Bool.and_eq_true_iff.1 h1.1
  have hB := h2.1
  simp only [smallB, Bool.and_eq_true, decide_eq_true_eq] at hB
  unfold _root_.Fmt.readChain
  split
  · rfl
  · dsimp only
    split
    · rfl
    · simp only [_root_.Fmt.paramsDigestW, idb]
      rw [ha _ _ _ _ _ (dom0 169 1 S.params (by decide) (by decide) (by decide) hB.1.1.1),
        startChainW_dom h h' ha hz S.label _ S.statement _ (hz _ _ _ _ _) hB.1.1.2]
      cases hh : _root_.Fmt.startChainW
          (m := Id) h S.label (h 169 0 1 _root_.Fmt.zero32 S.params) S.statement _ with
      | none => rfl
      | some hd =>
        dsimp only
        rw [foldRounds_dom h h' ha hz S.cfg S.plan hd.run b hB.1.2 (beq_iff_eq.1 h2.2)
            (startChainW_run h hz _ _ _ _ hd hh) S.rounds _ (by simpa using hB.2)
            (fun r hr => List.all_eq_true.1 h1.2 r hr)]

include ha hz in
theorem wholeChain_dom (S : Spec) (b : ByteArray) (hS : smallF S b = true) :
    _root_.Fmt.wholeChain (m := Id) h' S b = _root_.Fmt.wholeChain (m := Id) h S b := by
  unfold _root_.Fmt.wholeChain
  rw [readChain_dom h h' ha hz S [] b 0 hS]

include ha hz in
theorem verifyW_dom {Y : Type} (S : Spec) (dec : Y → _root_.Fmt.View → Bool) (y : Y)
    (b : ByteArray) (hS : smallF S b = true) :
    _root_.Fmt.verifyW (m := Id) h' S dec y b = _root_.Fmt.verifyW (m := Id) h S dec y b := by
  unfold _root_.Fmt.verifyW
  rw [wholeChain_dom h h' ha hz S b hS]

end

/-- The format page's strict verifier at the oracle's hash is the one at the format's hash, sizes
within the hash's domain (`smallF S b = true`). -/
theorem verify_HO' {Y : Type} (S : Spec) (dec : Y → _root_.Fmt.View → Bool) (y : Y)
    (b : ByteArray) (hS : smallF S b = true) :
    _root_.Fmt.verifyW (m := Id) (_root_.Fmt.HO _root_.Fmt.oracle) S dec y b =
      _root_.Fmt.verify S dec y b :=
  verifyW_dom (h := _root_.Fmt.formatHash) (h' := _root_.Fmt.HO _root_.Fmt.oracle)
    (fun n t i s b hd => _root_.Fmt.HO_oracle n t i s b hd)
    (fun n t i s b => _root_.Fmt.size_H n t i s b) S dec y b hS

theorem strict_dom : Run.Spec.strict_dom := fun h h' ha hz S b hS =>
  wholeChain_dom h h' ha hz S b hS

theorem strict_HO : Run.Spec.strict_HO := fun _ S dec y b hS => verify_HO' S dec y b hS

theorem run_strict : Run.Spec.run_strict := fun S dec file hok hS hv =>
  PQ.run_half S dec file hok (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 hS).1).1
    ((verify_HO' S (fun (_ : Unit) => dec) () file hS).trans hv)

end Run
