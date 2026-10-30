-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/SharesS.lean: the forms for one item
(Honest/Thread/Shares.lean) and the hypothesis that a sub-protocol establishes a clause of `rides`
(Honest/Thread/Riders.lean), asked from `ThrS`, the invariant together with `Said`
(Honest/Thread/Said.lean). The rules for a file take the sub-protocols' hypotheses from `ThrS`
(`OwesS`, `YesS`: Honest/Thread/PaysS.lean). At a row whose items are proved by several authors, as
soon as one of them, or the sub-protocol's `Behind`, is proved from `ThrS` alone, the forms from the
invariant alone could not be joined. Here are
their counterparts: weaker hypotheses; each such form gives its counterpart. Definitions, meant as
hypotheses; and conditional lemmas. General in the `Thread` and in `Said`.

  1  `ExchangeAtS`, `exchangeS_iff`, `exchangeAtS_of`   `ExchangeS` at one item
  2  `RidesPastAtS`, `ridesPastS_shares`, `ridesPastAtS_of`   `RidesPastS` at one item
  3  `exchangeAtS_again`   an item owed again: from `BehindS` and `RidesPastAtS`
  4  `LaysAtS`, `laysAtS_of`, `behindS_of_keepsS`   a clause of `rides` established, from `ThrS`

Limits.
  * It is not proved that any of these forms can be met.
  * None is one of the library's goals.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Shares
import Johnson.Desc.ProofFile.Honest.Thread.Riders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place OpenedColumn)

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)
  (Said : Nat → Coins Bk → Mid W X → Prop)

/-! ## 1 `ExchangeS` at one item -/

/-- **`ExchangeS` at one item.** It is a definition, meant as a hypothesis. -/
def ExchangeAtS (b : Nat) (i : T.ι) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', ThrS T Said b k s m E →
    drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' →
    T.Items [i] k s' y.2 (E.add y.1)

theorem exchangeS_iff {b : Nat} :
    ExchangeS T Said b ↔ ∀ i ∈ (T.row b).owes, ExchangeAtS T Said b i := by
  constructor
  · intro h i hi blk hblk k s m E ds y cols s' hA hd hS ds' j hj
    obtain rfl := List.mem_singleton.1 hj
    exact h blk hblk k s m E ds y cols s' hA hd hS ds' j hi
  · intro h blk hblk k s m E ds y cols s' hA hd hS ds' i hi
    exact h i hi blk hblk k s m E ds y cols s' hA hd hS ds' i (List.mem_singleton.2 rfl)

theorem exchangeAtS_of {b : Nat} {i : T.ι} (h : ExchangeAt T b i) : ExchangeAtS T Said b i :=
  fun blk hblk k s m E ds y cols s' hA hd hS => h blk hblk k s m E ds y cols s' hA.1 hd hS

/-! ## 2 `RidesPastS` at one item -/

/-- **`RidesPastS` at one item.** It is a definition, meant as a hypothesis. -/
def RidesPastAtS (b : Nat) (i : T.ι) : Prop :=
  ∀ k s m E s' ps v, ThrS T Said b k s m E → T.keeps b s s' →
    T.means m.st.input i (T.seat k m s) (T.strs E) v →
    T.means m.st.input i (T.seat k m s') (T.strs (E.add ps)) v

theorem ridesPastS_shares {b : Nat}
    (h : ∀ i ∈ T.opened b, i ∉ (T.row b).shuts → i ∉ (T.row b).owes → RidesPastAtS T Said b i) :
    RidesPastS T Said b :=
  fun k s m E s' ps i v hA hK h1 h2 h3 h0 => h i h1 h2 h3 k s m E s' ps v hA hK h0

theorem ridesPastAtS_of {b : Nat} {i : T.ι} (h : RidesPastAt T b i) : RidesPastAtS T Said b i :=
  fun k s m E s' ps v hA hK h0 => h k s m E s' ps v hA.1 hK h0

/-! ## 3 An item owed again -/

/-- **An item that is open before and owed after**, from `ThrS`. A conditional lemma on this
folder's own definitions. It is none of the library's goals. -/
theorem exchangeAtS_again {b : Nat} {i : T.ι} (hi : i ∈ T.opened b) (hB : BehindS T Said b)
    (hR : RidesPastAtS T Said b i) : ExchangeAtS T Said b i := by
  intro blk hblk k s m E ds y cols s' hA hd hS ds' j hj
  obtain rfl := List.mem_singleton.1 hj
  obtain ⟨-, -, hK⟩ := hB blk hblk k s m E ds y cols s' hA hd hS
  have hA' := hA.1
  unfold Thr at hA'
  obtain ⟨-, hF0, -, hI0, -, -, -⟩ := hA'
  have hS' := hS
  unfold Thread.Stepped Thread.Moved at hS'
  obtain ⟨⟨⟨l, -, hy⟩, -⟩, -⟩ := hS'
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  have eh := play_heard _ _ _ _ _ hy
  have hlen := T.heard_length hF0
  have hfr : T.front ≤ m.st.heard.length := by
    rw [hlen]
    exact Nat.le_add_right _ _
  have es : T.seat k y.2 s' = T.seat k m s' := by
    unfold Thread.seat
    rw [ei, eh, List.take_append_of_le_length hfr]
  have h0 := hI0 (ds ++ ds') j hi
  have h3 := hR k s m E s' y.1 _ hA hK h0
  show T.means y.2.st.input j (T.seat k y.2 s') (T.strs (E.add y.1))
    (T.wit k y.2.st.input (y.2.st.heard ++ ds'))
  rw [es, ei, eh, List.append_assoc]
  exact h3

/-! ## 4 A clause of `rides` established, from `ThrS` -/

/-- **Sub-protocol number b establishes the clause**, from `ThrS`. It is a definition, meant as a
hypothesis. -/
def LaysAtS (b : Nat) (c : RiderCl W S) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', ThrS T Said b k s m E →
    drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' →
    c.prop (b + 1) m.st.input s'

theorem laysAtS_of {b : Nat} {c : RiderCl W S} (h : LaysAt T b c) : LaysAtS T Said b c :=
  fun blk hblk k s m E ds y cols s' hA hd hS => h blk hblk k s m E ds y cols s' hA.1 hd hS

/-- `BehindS` from the form, `keeps` and the clauses established, all three from `ThrS`. -/
theorem behindS_of_keepsS {cs : List (RiderCl W S)} {b : Nat}
    (hr : ∀ c w s, T.rides c w s ↔ ridersOf cs c w s)
    (hFK : ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', ThrS T Said b k s m E →
      drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' →
      T.Form (b + 1) k s' y.2 ∧ T.keeps b s s')
    (hst : ∀ c ∈ cs, c.lo ≤ b → b + 1 ≤ c.hi → StaysBy T b c)
    (hl : ∀ c ∈ cs, c.lo = b + 1 → LaysAtS T Said b c) : BehindS T Said b := by
  intro blk hblk k s m E ds y cols s' hA hd hS
  obtain ⟨hF, hK⟩ := hFK blk hblk k s m E ds y cols s' hA hd hS
  have hA' := hA.1
  unfold Thr at hA'
  obtain ⟨-, -, -, -, -, hR0, -⟩ := hA'
  have hS' := hS
  unfold Thread.Stepped Thread.Moved at hS'
  obtain ⟨⟨⟨l, -, hy⟩, -⟩, -⟩ := hS'
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  refine ⟨hF, ?_, hK⟩
  rw [ei]
  exact (hr _ _ _).2 (riders_next ((hr _ _ _).1 hR0)
    (fun c hc h1 h2 h0 => hst c hc h1 h2 _ _ _ hK h0)
    fun c hc e => hl c hc e blk hblk k s m E ds y cols s' hA hd hS)

end ProofFile.Honest

#print axioms ProofFile.Honest.exchangeS_iff
#print axioms ProofFile.Honest.exchangeAtS_of
#print axioms ProofFile.Honest.ridesPastS_shares
#print axioms ProofFile.Honest.ridesPastAtS_of
#print axioms ProofFile.Honest.exchangeAtS_again
#print axioms ProofFile.Honest.laysAtS_of
#print axioms ProofFile.Honest.behindS_of_keepsS
