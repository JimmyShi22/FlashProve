-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/StoredDom.lean: the strict reader with stored tables, at two hashes that agree.

The program runs the strict reader at the format's own hash (`Fmt.formatHash`). The library's theorems on the
compiled verifier speak of the hash that a function on byte strings induces (`Fmt.HO`). At the
function `Fmt.oracle` it agrees with `Fmt.formatHash` on the hash's domain. This file shows that the reader's
calls lie in that domain if file and description are within the bounds `smallFX`, so that the reader
gives one result at both.

Main definition: `smallFX`.
Main theorems: `readChainX_dom`, `readChainX_HO`. The steps follow the reader's own code:
`readStored_dom`, `roundX_dom`, `roundX_round`, `foldRoundsX_dom`.

Not claimed here: anything about a file or a description outside the bounds, and anything about
what the reader accepts.
-/
import Run.StrictDomProofs
import Fmt.Rules8X

set_option autoImplicit false

namespace OnBytes.Tie
open Run

/-- The bounds on file and description that the hash's domain asks for. -/
def smallFX (S : Fmt.SpecX) (b : ByteArray) : Bool :=
  smallF S.base b && S.stored.all fun ts => ts.all fun t => smallSh t.salt t.sh

section
-- "Both hashes" in this section are h and h'. The theorems on both ask that h' agrees with h on the
-- hash's domain (ha) and that h's digests have the format's lengths (hz).
variable (h h' : HId)
  (ha : ∀ n t i s b, Fmt.hDom n t i s b = true → h' n t i s b = h n t i s b)
  (hz : ∀ n t i s b, ByteArray.size (h n t i s b) = Fmt.dlen n)

include ha hz in
/-- Reading one round's stored tables gives one result at both hashes. Each opening is read and
hashed from the configuration's digest, under the table's own length of a salt. The record of met
vertices does not hash. It holds if that digest has 32 bytes and the tables' shapes are small
(`smallSh`). -/
theorem readStored_dom (cfg statement : ByteArray) (P : Fmt.Plan) (poss : List ℕ)
    (b : ByteArray) (hc : cfg.size = 32) :
    ∀ (ts : List Fmt.Stored), (ts.all fun t => smallSh t.salt t.sh) = true →
      ∀ (sn : Fmt.Seen) (i : ℕ),
        Fmt.readStored (m := Id) h' cfg statement P poss b ts sn i
          = Fmt.readStored (m := Id) h cfg statement P poss b ts sn i
  | [], _, _, _ => rfl
  | t :: ts, ho, sn, i => by
    rw [List.all_cons] at ho
    have ho' := Bool.and_eq_true_iff.1 ho
    unfold Fmt.readStored
    simp only [idb]
    rw [readOpeningW_dom h h' ha hz cfg P.field t.salt t.sh cfg _ b i hc hc ho'.1]
    cases Fmt.readOpeningW (m := Id) h cfg P.field t.salt t.sh cfg
        (Fmt.listOf ((Fmt.partOf t poss).map (· % 2 ^ t.sh.a))) b i with
    | none => rfl
    | some o =>
      dsimp only
      split
      · split
        · rfl
        · rename_i sn' _
          rw [readStored_dom cfg statement P poss b hc ts ho'.2 sn' o.next]
      · rfl

include ha hz in
/-- One round gives one result at both hashes: the chain's query, the stored tables' openings, the
chain's own trees' openings. It holds within bounds: the round's number is below 2^63, the file
below about 2^32 bytes, the configuration's digest and the run value have 32 bytes, and all opened
shapes are small (`smallO`, `smallSh`). -/
theorem roundX_dom (cfg statement : ByteArray) (P : Fmt.Plan) (run : Option ByteArray)
    (b : ByteArray) (s : Fmt.St) (r : Fmt.Round) (ts : List Fmt.Stored)
    (hi : s.chain.round + 1 < 2 ^ 63) (hb : b.size + 16 ≤ 2 ^ 32 - 144) (hc : cfg.size = 32)
    (hr : ∀ x, run = some x → x.size = 32) (ho : r.opens.all (smallO P.salt) = true)
    (ht : (ts.all fun t => smallSh t.salt t.sh) = true) :
    Fmt.roundX (m := Id) h' cfg statement P run b s r ts
      = Fmt.roundX (m := Id) h cfg statement P run b s r ts := by
  unfold Fmt.roundX
  cases hs : Fmt.slice b s.pos r.entry.msg with
  | none => rfl
  | some msg =>
    dsimp only
    cases Fmt.whole (Fmt.readItems P.field r.items) msg with
    | none => rfl
    | some vals =>
      dsimp only
      cases Fmt.readNonce P r.entry.work b (s.pos + r.entry.msg) with
      | none => rfl
      | some ni =>
        dsimp only
        have hm : msg.size + 16 ≤ 2 ^ 32 - 144 := by
          have := slice_size b _ _ msg hs
          omega
        rw [queryW_dom h h' ha s.chain msg r.kind r.entry.work ni.1 _ hi hm]
        simp only [readStored_dom h h' ha hz cfg statement P _ b hc ts ht,
          readOpens_dom h h' ha hz cfg P run _ _ b hc hr r.opens ho]

/-- A round that is read moves the chain's count of rounds on by one. -/
theorem roundX_round (cfg statement : ByteArray) (P : Fmt.Plan) (run : Option ByteArray)
    (b : ByteArray) (s s' : Fmt.St) (r : Fmt.Round) (ts : List Fmt.Stored)
    (e : Fmt.roundX (m := Id) h cfg statement P run b s r ts = some s') :
    s'.chain.round = s.chain.round + 1 := by
  unfold Fmt.roundX at e
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
            · split at e
              · cases e
              · cases e
                exact queryW_round h _ _ _ _ _ _ c vb hq

include ha hz in
/-- All rounds, one after the other, give one result at both hashes, within the bounds of
`roundX_dom` for every round. -/
theorem foldRoundsX_dom (cfg statement : ByteArray) (P : Fmt.Plan) (run : Option ByteArray)
    (b : ByteArray) (hb : b.size + 16 ≤ 2 ^ 32 - 144) (hc : cfg.size = 32)
    (hr : ∀ x, run = some x → x.size = 32) :
    ∀ (rs : List (Fmt.Round × List Fmt.Stored)) (s : Fmt.St),
      s.chain.round + rs.length < 2 ^ 63 →
      (∀ r ∈ rs, r.1.opens.all (smallO P.salt) = true ∧
        (r.2.all fun t => smallSh t.salt t.sh) = true) →
      Fmt.foldRoundsX (m := Id) h' cfg statement P run b rs s
        = Fmt.foldRoundsX (m := Id) h cfg statement P run b rs s
  | [], _, _, _ => rfl
  | r :: rs, s, hi, ho => by
    rw [List.length_cons] at hi
    have hi' : s.chain.round + 1 < 2 ^ 63 := by omega
    have hor := ho r List.mem_cons_self
    simp only [Fmt.foldRoundsX, idb]
    rw [roundX_dom h h' ha hz cfg statement P run b s r.1 r.2 hi' hb hc hr hor.1 hor.2]
    cases hst : Fmt.roundX (m := Id) h cfg statement P run b s r.1 r.2 with
    | none => rfl
    | some s' =>
      dsimp only
      have hn : s'.chain.round + rs.length < 2 ^ 63 := by
        rw [roundX_round h cfg statement P run b s s' r.1 r.2 hst]
        omega
      exact foldRoundsX_dom cfg statement P run b hb hc hr rs s' hn
        (fun r' hr' => ho r' (List.mem_cons_of_mem _ hr'))

end

/-- Within `smallFX` the reader gives one result at two hashes that agree on the domain, if the
first hash's digests have the format's lengths. -/
theorem readChainX_dom (h h' : HId)
    (ha : ∀ n t i s b, Fmt.hDom n t i s b = true → h' n t i s b = h n t i s b)
    (hz : ∀ n t i s b, ByteArray.size (h n t i s b) = Fmt.dlen n) (S : Fmt.SpecX)
    (seen : Fmt.Seen) (b : ByteArray) (i : ℕ) (hS : smallFX S b = true) :
    Fmt.readChainX (m := Id) h' S seen b i = Fmt.readChainX (m := Id) h S seen b i := by
  have h0 := Bool.and_eq_true_iff.1 hS
  have h1 := Bool.and_eq_true_iff.1 h0.1
  have h2 := Bool.and_eq_true_iff.1 h1.1
  have hB := h2.1
  simp only [smallB, Bool.and_eq_true, decide_eq_true_eq] at hB
  have hlen : (S.base.rounds.zip S.stored).length ≤ S.base.rounds.length := by
    rw [List.length_zip]
    exact Nat.min_le_left _ _
  have hall : ∀ r ∈ S.base.rounds.zip S.stored,
      r.1.opens.all (smallO S.base.plan.salt) = true ∧
        (r.2.all fun t => smallSh t.salt t.sh) = true := fun r hr =>
    ⟨List.all_eq_true.1 h1.2 r.1 (List.of_mem_zip hr).1,
      List.all_eq_true.1 h0.2 r.2 (List.of_mem_zip hr).2⟩
  unfold Fmt.readChainX
  split
  · rfl
  · dsimp only
    split
    · rfl
    · simp only [Fmt.paramsDigestW, idb]
      rw [ha _ _ _ _ _ (dom0 169 1 S.base.params (by decide) (by decide) (by decide) hB.1.1.1),
        startChainW_dom h h' ha hz S.base.label _ S.base.statement _ (hz _ _ _ _ _) hB.1.1.2]
      cases hh : Fmt.startChainW (m := Id) h S.base.label
          (h 169 0 1 Fmt.zero32 S.base.params) S.base.statement _ with
      | none => rfl
      | some hd =>
        dsimp only
        rw [foldRoundsX_dom h h' ha hz S.base.cfg S.base.statement S.base.plan hd.run b hB.1.2
          (beq_iff_eq.1 h2.2) (startChainW_run h hz _ _ _ _ hd hh) (S.base.rounds.zip S.stored) _
          (by
            have h63 := hB.2
            show 0 + (S.base.rounds.zip S.stored).length < 2 ^ 63
            omega) hall]

/-- Within `smallFX` the reader gives one result at `Fmt.HO Fmt.oracle` and at `Fmt.formatHash`. -/
theorem readChainX_HO (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray) (i : ℕ)
    (hS : smallFX S b = true) :
    Fmt.readChainX (m := Id) (Fmt.HO Fmt.oracle) S seen b i
      = Fmt.readChainX (m := Id) Fmt.formatHash S seen b i :=
  readChainX_dom Fmt.formatHash (Fmt.HO Fmt.oracle) (fun n t i s b hd => Fmt.HO_oracle n t i s b hd)
    (fun n t i s b => Fmt.size_H n t i s b) S seen b i hS

end OnBytes.Tie

#print axioms OnBytes.Tie.readChainX_dom
#print axioms OnBytes.Tie.readChainX_HO
