-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/CodingPut.lean: the two ties between the partial codes and the functions: under the hypotheses
below, what the code of a round's chain query writes, and what the code of a leaf query writes, is
the bit string of the format's string of the call to which the functions send that query.

Theorems and proofs. The format page (docs/format/FORMAT.md, which comes with the programs, that is,
with the
C++ implementation that accompanies this Lean code): written at an edition that is not the one that
ships (R2.2, R2.4, R3.1, R5.2, R7.3). The statements speak of the definitions of Fmt/ as they stand
(for the page's sections 2 and 3 that is Fmt/Rules23.lean, in a second edition, also not the one
that ships). Of the five rules, compared by program on the page's texts of several editions other
than the one at which this file was written, the last of them the edition at which Fmt/Rules23.lean
stands: R5.2 has one text throughout; R2.2, R2.4, R3.1 and R7.3 differ between the first two of
them; after that R2.2 stands, R7.3 differs at the next edition, R3.1 at a later one, R2.4 between
the last two of them. Not held against the page that ships.

Why: two descriptions of one map stand in this folder. Run/CodingFn.lean: functions from a typed
query (and the number of a block of its answer) to a hash call of the format (`fbCall`, `leafCall`;
`strOf`: the call's string): by them the verifier is run over a function on the format's strings
(`famOf`). Run/CodingPage162.lean, Run/CodingPage164.lean: partial codes with put, parse and both
laws (`p162`, `pLeaf`): of them the encoding of the queries into a single oracle is made. For a node
the tie follows from `pNode_put` (Run/CodingPage166.lean), where the code stands. For the chain's
first value `pFirst0_put` (Run/CodingPage160.lean) gives the format's string; the tie to `fbCall`
stays a hypothesis for generic data (`PageFit.first`, Run/CodingAgree.lean); at the toy's data
(`firstT_fit`, Run/ToyFit.lean) and at the data made from a chain's description (`firstQ_fit`,
Run/PageQFit.lean) it is proved. Here the other two.

Main names:
  `ChainFit C D` (at any tag; the default is "test"): the hypothesis of fit between the code's data
    (C : ChainD) and the functions' data (D : PageD): the same label, kinds, bits of work; what C.rc
    i writes for (root or none, plain part) is the bits of D.msg i .. and then the 64 bits of the
    word of D.nonce i ..
  `p162_put` asks, of `p162 C K`: 0 < K, ChainFit C D.
  `pLeaf_put` asks, of `pLeaf n p`: the file's salt has a whole number of bytes (n = 8 k); what p
    writes for a symbol with its position is the bits of the leaf's label and then of the column
    with its fill, by D.leaf.
  `blockNo_eq`: the two numberings of the blocks of a chain answer (`blockNo`: a number; `blockTo`:
    a permutation) are one, if 0 < K or the round has no work.

Limits: where the two numberings part: K = 0 with work. An answer without any block of verifier
message, in a round with work: `blockNo` sends the chain value to block 1, `blockTo` (a permutation
of one point) to block 0. The wiring with tests has a block for the test bits in front, so K is at
least 1 wherever a round has work: hence the premise 0 < K.
This file does not say that the two hypotheses of fit hold at a given protocol: that is a matter of
the protocol's data. The converse (that the code writes wherever the functions give a call): it does
not hold: the functions test no lengths. This file does not say anything on the single oracle.

Terms: lean/GLOSSARY.md.
-/
import Run.CodingPage
import Run.CodingFn
import Run.CodingFnTag

set_option autoImplicit false

namespace Run
open Rom Compile Compile.Batch Iop

namespace PCode
variable {A B : Type}

theorem ins_put (p : PCode B) (a : PCode A) (k n : ℕ) (ha : a.Len n)
    (hp : ∀ y s, p.put y = some s → k ≤ s.length) (x : B × A) (t : List Bool)
    (h : (p.ins a k n ha hp).put x = some t) :
    ∃ s w,
      p.put x.1 = some s ∧ a.put x.2 = some w ∧
      t = s.take (s.length - k) ++ (w ++ s.drop (s.length - k)) := by
  have h0 : (p.put x.1).bind
        (fun s => (a.put x.2).map fun w => s.take (s.length - k) ++ (w ++ s.drop (s.length - k))) =
      some t := h
  cases hs : p.put x.1 with
  | none => rw [hs] at h0; cases h0
  | some s =>
      rw [hs] at h0
      have h1 : (a.put x.2).map (fun w => s.take (s.length - k) ++ (w ++ s.drop (s.length - k))) =
          some t := h0
      cases hw : a.put x.2 with
      | none => rw [hw] at h1; cases h1
      | some w =>
          rw [hw] at h1
          exact ⟨s, w, rfl, rfl, (Option.some.inj h1).symm⟩

end PCode

theorem pWord_put_eq (x : ℕ) (s : List Bool) (h : pWord.put x = some s) :
    s = bytesToBits (_root_.Fmt.u64n x) := by
  have h0 : (if x < 2 ^ 64 then some (bytesToBits (_root_.Fmt.u64n x)) else none) = some s := h
  by_cases hx : x < 2 ^ 64
  · rw [if_pos hx] at h0
    exact (Option.some.inj h0).symm
  · rw [if_neg hx] at h0
    cases h0

theorem pBits_put_eq (n : ℕ) (l s : List Bool) (h : (pBits n).put l = some s) :
    s = l ∧ l.length = n := by
  have h0 : (if l.length = n then some l else none) = some s := h
  by_cases hl : l.length = n
  · rw [if_pos hl] at h0
    exact ⟨(Option.some.inj h0).symm, hl⟩
  · rw [if_neg hl] at h0
    cases h0

theorem pKwc_put_eq (kind w c : ℕ) (s : List Bool) (h : (pKwc kind w).put c = some s) :
    s = bytesToBits (_root_.Fmt.u64n (kind + 256 * w + 65536 * c)) := by
  obtain ⟨v, hv, hs⟩ := PCode.pull_put _ _ _ _ _ c s h
  unfold kwcTo at hv
  by_cases hc : kind < 256 ∧ w < 256 ∧ c < 2 ^ 48
  · rw [if_pos hc] at hv
    rw [← Option.some.inj hv] at hs
    exact pWord_put_eq _ s hs
  · rw [if_neg hc] at hv
    cases hv

/-- The two numberings of a chain answer's blocks are one, if the answer has a block of verifier
message or the round has no work (`h`). -/
theorem blockNo_eq (w K : ℕ) (j : Fin (K + 1)) (h : 0 < K ∨ w = 0) :
    blockNo w K j = (blockTo (decide (w ≠ 0)) K j).val := by
  unfold blockNo
  by_cases hw : w = 0
  · subst hw
    simp only [ne_eq, not_true_eq_false, decide_false, blockTo]
    by_cases hj : j.val = K
    · simp [hj]
    · simp [hj]
  · have hK : 0 < K := h.resolve_right hw
    obtain ⟨K, rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    simp only [ne_eq, hw, not_false_eq_true, decide_true, blockTo]
    by_cases hj : j.val = K + 1
    · simp [hj]
    · by_cases h0 : j.val = 0
      · simp [h0]
      · simp [hj, h0]

theorem bits_one (h : UInt8) : bytesToBits ⟨#[h]⟩ = bitsOfByte h := by
  show bitsL [h] = bitsOfByte h
  simp [bitsL]

/-- The bits of the format's string of a call of a round's query, for a start of 32 bytes (`hs`). -/
theorem oStr64_bits (h : UInt8) (tree index : ℕ) (start bytes : ByteArray) (hs : start.size = 32) :
    bytesToBits (_root_.Fmt.oStr h 162 tree index start bytes) =
      bitsOfByte h ++
        (mid32 ++ (bytesToBits start ++
            (bytesToBits (_root_.Fmt.u64n (162 + 65536 * tree)) ++
              (bytesToBits (_root_.Fmt.u64n index) ++ bytesToBits bytes)))) := by
  unfold _root_.Fmt.oStr _root_.Fmt.pblock _root_.Fmt.dlen _root_.Fmt.label mid32
  rw [if_pos rfl, fit32 start hs]
  simp only [bytesToBits_append, List.append_assoc, bits_one]
  rfl

theorem half_bits (b : ℕ) :
    bitsOfByte (if decide (b % 2 = 1) = true then 1 else 0) = bitsOfByte (UInt8.ofNat (b % 2)) := by
  rcases Nat.mod_two_eq_zero_or_one b with h | h <;> simp [h]

variable {I X : Type} {L : BatchProtocol I X} {tg : Tag}

/-- The data of the partial code and the data of the functions fit. -/
structure ChainFit (C : ChainD L tg) (D : PageD L tg) : Prop where
  label : C.label = D.label
  kind  : ∀ i, C.kind i = D.kind i
  work  : ∀ i, C.work i = D.work i
  rc    : ∀ i rt pl s, (C.rc i).put (rt, pl) = some s →
    s = bytesToBits (D.msg i (rt.map digToBytes) pl) ++ bytesToBits (_root_.Fmt.u64n (D.nonce i pl))

/-- The tie for a round's query: if 0 < K (`hK`) and the data fit (`F`), what the partial code
writes is the bits of the format's string of the call. -/
theorem p162_put (C : ChainD L tg) (D : PageD L tg) (K : ℕ) (hK : 0 < K) (F : ChainFit C D)
    (x : FbIn 256 L tg × Fin (K + 1)) (s : List Bool) (h : (p162 C K).put x = some s) :
    ∃ c, fbCall D K x.1 x.2 = some c ∧ s = bytesToBits (strOf c) := by
  obtain ⟨t, ht, hs⟩ := PCode.pull_put _ _ _ _ _ x s h
  obtain ⟨⟨round, head, rt, plain⟩, j⟩ := x
  cases round with
  | zero => cases ht
  | succ i =>
      cases head with
      | f2 xl ρ =>
          cases xl with
          | some _ => cases ht
          | none =>
              rw [← Option.some.inj ht] at hs
              obtain ⟨u, v, hu, hv, rfl⟩ := PCode.cons_put _ _ _ _ _ s hs
              obtain ⟨v1, hv1, rfl⟩ := PCode.pre_put' _ _ _ v hv
              obtain ⟨u2, v2, hu2, hv2, rfl⟩ := PCode.cons_put _ _ _ _ _ v1 hv1
              obtain ⟨v3, hv3, rfl⟩ := PCode.pre_put' _ _ _ v2 hv2
              obtain ⟨u4, v4, hu4, hv4, rfl⟩ := PCode.cons_put _ _ _ _ _ v3 hv3
              obtain ⟨s0, w0, hs0, hw0, rfl⟩ := PCode.ins_put _ _ _ _ _ _ _ v4 hv4
              obtain ⟨e2, hρ⟩ := pBits_put_eq 256 _ u2 hu2
              simp only at e2 hρ
              have e4 := pWord_put_eq _ u4 hu4
              have ew := pKwc_put_eq _ _ _ w0 hw0
              have e0 := F.rc _ _ _ s0 hs0
              have eu : u =
                  bitsOfByte
                    (if decide ((blockTo (decide (C.work (i + 1) ≠ 0)) K j).val % 2 = 1) = true then
                        1
                      else 0) :=
                (Option.some.inj hu).symm
              simp only at e4 ew e0
              have hb : blockNo (D.work (i + 1)) K j =
                  (blockTo (decide (C.work (i + 1) ≠ 0)) K j).val := by
                rw [F.work]
                exact blockNo_eq _ K j (Or.inl hK)
              have hl : (bytesToBits (_root_.Fmt.u64n (D.nonce (i + 1) plain))).length = 64 := by
                rw [length_bytesToBits]
                rfl
              have hlen : s0.length - 64 =
                  (bytesToBits (D.msg (i + 1) (rt.map digToBytes) plain)).length := by
                rw [e0, List.length_append, hl]
                omega
              refine ⟨_, rfl, ?_⟩
              show _ = bytesToBits
                  (_root_.Fmt.oStr _ 162 D.label (i + 1) (bitsToBytes ρ) (roundBytes _ _ _ _ _))
              rw [oStr64_bits _ _ _ _ _ (size_bitsToBytes ρ 32 hρ),
                bytesToBits_bitsToBytes ρ ((whole_iff ρ).2 ⟨32, hρ⟩), hb, ← half_bits,
                ← eu, ← F.label, ← e4, ← e2]
              unfold roundBytes
              rw [bytesToBits_append, bytesToBits_append, ← F.kind, ← F.work, ← ew, hlen, e0,
                List.take_left' rfl, List.drop_left' rfl, List.append_assoc]
      | f1 _ _ _ => cases ht
      | f3 _ _ => cases ht
      | f4 _ _ => cases ht
      | f5 _ => cases ht

/-- The tie for a leaf: if the file's salt has a whole number of bytes (`hn`) and p writes the bits
of the leaf's label and then of the column with its fill, by D.leaf (`fit`), what `pLeaf n p` writes
is the bits of the format's string of the call. -/
theorem pLeaf_put (D : PageD L tg) (n k : ℕ) (hn : n = 8 * k) (p : PCode (SymAny (shapeOf L tg)))
    (fit : ∀ y m, p.put y = some m →
      m = bytesToBits (_root_.Fmt.label 164 (D.leaf y).1 (D.leaf y).2.1) ++
          bytesToBits (D.leaf y).2.2)
    (q : LeafIn L) (s : List Bool) (h : (pLeaf n p).put q = some s) :
    ∃ c, leafCall D q = some c ∧ s = bytesToBits (strOf c) := by
  have h0 : (leafSel q).bind (pSalted pre33 n p).put = some s := h
  cases hq : leafSel (t := tg) q with
  | none => rw [hq] at h0; cases h0
  | some x =>
      rw [hq] at h0
      have eq := leafMk_sel q x hq
      subst eq
      obtain ⟨y, sa⟩ := x
      have h1 : (if sa.length = 256 + n then
              (p.put y).map (fun m => pre33 ++ (sa.take 256 ++ (m ++ sa.drop 256)))
            else none) = some s := h0
      by_cases hl : sa.length = 256 + n
      · rw [if_pos hl] at h1
        cases hm : p.put y with
        | none => rw [hm] at h1; cases h1
        | some m =>
            rw [hm] at h1
            have es : s = pre33 ++ (sa.take 256 ++ (m ++ sa.drop 256)) := (Option.some.inj h1).symm
            have e1 : (sa.take 256).length = 8 * 32 := by rw [List.length_take, hl]; omega
            have e2 : (sa.drop 256).length = 8 * k := by rw [List.length_drop, hl]; omega
            refine ⟨_, leafCall_self D y sa, ?_⟩
            show s = bytesToBits
                (_root_.Fmt.oStr 0 164 (D.leaf y).1 (D.leaf y).2.1 (bitsToBytes (sa.take 256))
                  ((D.leaf y).2.2 ++ bitsToBytes (sa.drop 256)))
            rw [oStr32_bits _ _ _ _ _ (by decide) (size_bitsToBytes _ 32 e1),
              bytesToBits_bitsToBytes _ ((whole_iff _).2 ⟨32, e1⟩),
              bytesToBits_append, bytesToBits_bitsToBytes _ ((whole_iff _).2 ⟨k, e2⟩),
              es, fit y m hm, List.append_assoc]
      · rw [if_neg hl] at h1
        cases h1

end Run
