-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/PaysS.lean: the hypotheses on one sub-protocol
(Honest/Thread/Pays.lean), asked from `ThrS` (Honest/Thread/Said.lean) in place of `Thr`; and lemmas
that they serve the lemma for a whole chain as well as the original ones do. `ThrS T Said b` is the
invariant together with `Said`, a second condition, on what has been shown in the clear so far.
A lemma that relies on a fact which the library has "at reached states" can be obtained from `ThrS`
at `SaidOk` (`reach_below`, Honest/Thread/SaidOk.lean, and its build does not check it), not from
the invariant alone: so it is asked from `ThrS`. Each hypothesis here is the original's definition
with `ThrS T Said b` in place of `Thr T b`: a weaker hypothesis. The price: `Said` has itself to be
carried from border to border (`SaidNext`, Honest/Thread/Said.lean), which is a hypothesis of
`playsOn_of_paysS` and `playsOn_of_owesS`. Definitions, meant as hypotheses; and conditional lemmas
on them. They are general in the `Thread` and in `Said`: no kind is named.

  1  `thr_next_at`   the invariant after a sub-protocol, from what the hypotheses say at the one
     state in question
  2  `PlaysS`, `BehindS`, `ExchangeS`, `RidesPastS`, `AcceptedS`   the five hypotheses, from `ThrS`
  3  `playsS_of`, `behindS_of`, `exchangeS_of`, `ridesPastS_of`, `acceptedS_of`   each original
     gives its counterpart
  4  `playsOn_of_paysS`, `saysYes_of_acceptedS`   `PlaysOn` and `SaysYes` (Honest/Law/ThreadC.lean),
     the two conditions of the lemma for a whole chain, at `ThrS`
  5  `OwesS`, `YesS`, `owesS_of`, `yesS_of`, `playsOn_of_owesS`, `saysYes_of_yesS`   at every
     sub-protocol

Where this comes from. The observation that a `Behind` asked from `ThrS` could be used by no lemma,
the form `BehindS`, and a proof of `playsOn_of_paysS` with that one hypothesis changed, come from
another part of this project. `BehindS` here is that definition; `playsOn_of_paysS` here follows
that proof, with the same change made at `Plays`, `Exchange` and `RidesPast`, over `thr_next_at`.

Limits.
  * It is not proved that the hypotheses can be met.
  * None is one of the library's goals.
  * Hypotheses that the prose above does not name: `drawsFit` (`drawFit` round by round, and as many
    challenges as rounds): `thr_next_at`; `Block.planOk` and `Block.shaped` at every sub-protocol of
    `T.bs` (the library's executable tests): `playsOn_of_owesS`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Said
import Johnson.Desc.ProofFile.Honest.Thread.File

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place OpenedColumn)

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-! ## 1 The invariant after a sub-protocol, pointwise -/

/-- **The invariant after a sub-protocol, from what the hypotheses say at the one state in
question**: `thr_next` (Honest/Thread/PaysLaw.lean) with `Exchange` and `RidesPast` taken at that
state alone. Its proof is that lemma's own. -/
theorem thr_next_at {n b : Nat} {blk : Block S Cl} {k : Coins Bk} {s s' : S} {m : Mid W X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid W X} {cols : List OpenedColumn}
    (hfit : T.fits n = true) (hb : b < n) (hblk : T.bs[b]? = some blk) (hA : Thr T b k s m E)
    (hd : drawsFit blk.rounds ds = true) (hS : T.Stepped blk k s m E ds y cols s')
    (hT : T.Trees (T.fresh b) k y.2 (E.add y.1)) (hF : T.Form (b + 1) k s' y.2)
    (hRd : T.rides (b + 1) y.2.st.input s')
    (hX : T.Items (T.row b).owes k s' y.2 (E.add y.1))
    (hR : ∀ i v, i ∈ T.opened b → i ∉ (T.row b).shuts → i ∉ (T.row b).owes →
      T.means m.st.input i (T.seat k m s) (T.strs E) v →
      T.means m.st.input i (T.seat k m s') (T.strs (E.add y.1)) v)
    (hM : MadeNext T b) : Thr T (b + 1) k s' y.2 (E.add y.1) := by
  have hA' := hA
  unfold Thr at hA'
  obtain ⟨hH0, hF0, -, hI0, hM0, -, hV0⟩ := hA'
  unfold Thread.Hand at hH0
  obtain ⟨hSt, hTr⟩ := hH0
  have hM0' := hM0
  unfold Thread.Made at hM0'
  obtain ⟨-, -, -, hTi, -⟩ := hM0'
  have hS' := hS
  unfold Thread.Stepped Thread.Moved at hS'
  obtain ⟨⟨⟨l, -, hy⟩, -⟩, -⟩ := hS'
  obtain ⟨ei, -, -⟩ := play_mid _ _ _ _ _ hy
  have eh := play_heard _ _ _ _ _ hy
  have hlen := T.heard_length hF0
  obtain ⟨hfx, -⟩ := T.fits_parts hfit
  obtain ⟨hF1, hM1⟩ := hM blk hblk k s m E ds y cols s' hF0 hM0 hd hS
  have hfr : T.front ≤ m.st.heard.length := by
    rw [hlen]
    exact Nat.le_add_right _ _
  have es : T.seat k y.2 s' = T.seat k m s' := by
    unfold Thread.seat
    rw [ei, eh, List.take_append_of_le_length hfr]
  unfold Thr
  refine ⟨?_, hF1, hF, ?_, hM1, hRd, ?_⟩
  · unfold Thread.Hand
    refine ⟨?_, ?_⟩
    · intro i x
      show E.stored i x = T.stored y.2.st.input i x
      rw [ei]
      exact hSt i x
    · intro σ hσ
      by_cases ho : σ ∈ T.hand b
      · refine T.handAt_next ei eh ?_ hTi (hTr σ ho)
        rw [hlen]
        exact hfx b (Nat.le_of_lt hb) σ ho
      · have hm : σ ∈ T.fresh b := List.mem_filter.2 ⟨hσ, by simp [ho]⟩
        exact hT σ hm
  · intro ds' i hi
    by_cases ho : i ∈ (T.row b).owes
    · exact hX ds' i ho
    · have hi' : i ∈ fwdStep (T.opened b) (T.row b) := hi
      rcases mem_fwdStep hi' with h1 | ⟨h1, h2⟩
      · exact absurd h1 ho
      · have h0 := hI0 (ds ++ ds') i h1
        have h3 := hR i _ h1 h2 ho h0
        rw [es, ei, eh, List.append_assoc]
        exact h3
  · rw [ei]
    exact hV0

variable (Said : Nat → Coins Bk → Mid W X → Prop)

/-! ## 2 The five hypotheses, from `ThrS` -/

/-- `Plays`, asked from `ThrS`. A definition, meant as a hypothesis. -/
def PlaysS (b : Nat) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds l, ThrS T Said b k s m E →
    drawsFit blk.rounds ds = true →
    chainStopAt (T.φ.sees m.st.input) [blk] T.hs m.loc ds = none →
    chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees m.st.input) [blk] T.hs = .ok l →
    ∃ y cols, T.Moved blk k m E ds y cols ∧ T.Trees (T.fresh b) k y.2 (E.add y.1)

/-- `Behind`, asked from `ThrS`. A definition, meant as a hypothesis. -/
def BehindS (b : Nat) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', ThrS T Said b k s m E →
    drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' →
    T.Form (b + 1) k s' y.2 ∧ T.rides (b + 1) y.2.st.input s' ∧ T.keeps b s s'

/-- `Exchange`, asked from `ThrS`. A definition, meant as a hypothesis. -/
def ExchangeS (b : Nat) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols s', ThrS T Said b k s m E →
    drawsFit blk.rounds ds = true → T.Stepped blk k s m E ds y cols s' →
    T.Items (T.row b).owes k s' y.2 (E.add y.1)

/-- `RidesPast`, asked from `ThrS`. A definition, meant as a hypothesis. -/
def RidesPastS (b : Nat) : Prop :=
  ∀ k s m E s' ps i v, ThrS T Said b k s m E → T.keeps b s s' → i ∈ T.opened b →
    i ∉ (T.row b).shuts → i ∉ (T.row b).owes →
    T.means m.st.input i (T.seat k m s) (T.strs E) v →
    T.means m.st.input i (T.seat k m s') (T.strs (E.add ps)) v

/-- `Accepted`, asked from `ThrS`. A definition, meant as a hypothesis. -/
def AcceptedS (fall : Nat → S → List Fmt.Drawn → Option String) (b : Nat) : Prop :=
  ∀ blk, T.bs[b]? = some blk → ∀ k s m E ds y cols, ThrS T Said b k s m E →
    drawsFit blk.rounds ds = true →
    chainStopAt (T.φ.sees m.st.input) [blk] T.hs m.loc ds = none → fall b s ds = none →
    T.Moved blk k m E ds y cols → ∃ s', T.Stepped blk k s m E ds y cols s'

/-! ## 3 Each original gives its counterpart -/

theorem playsS_of {b : Nat} (h : Plays T b) : PlaysS T Said b :=
  fun blk hblk k s m E ds l hA => h blk hblk k s m E ds l hA.1

theorem behindS_of {b : Nat} (h : Behind T b) : BehindS T Said b :=
  fun blk hblk k s m E ds y cols s' hA => h blk hblk k s m E ds y cols s' hA.1

theorem exchangeS_of {b : Nat} (h : Exchange T b) : ExchangeS T Said b :=
  fun blk hblk k s m E ds y cols s' hA => h blk hblk k s m E ds y cols s' hA.1

theorem ridesPastS_of {b : Nat} (h : RidesPast T b) : RidesPastS T Said b :=
  fun k s m E s' ps i v hA => h k s m E s' ps i v hA.1

theorem acceptedS_of {fall : Nat → S → List Fmt.Drawn → Option String} {b : Nat}
    (h : Accepted T fall b) : AcceptedS T Said fall b :=
  fun blk hblk k s m E ds y cols hA => h blk hblk k s m E ds y cols hA.1

/-! ## 4 `PlaysOn` and `SaysYes` at `ThrS` -/

/-- **From the hypotheses asked from `ThrS`.** A conditional lemma on this folder's own definitions.
It is none of the library's goals. -/
theorem playsOn_of_paysS {n b : Nat} {blk : Block S Cl} (hfit : T.fits n = true) (hb : b < n)
    (hblk : T.bs[b]? = some blk) (hP : PlaysS T Said b) (hB : BehindS T Said b)
    (hX : ExchangeS T Said b) (hR : RidesPastS T Said b) (hM : MadeNext T b)
    (hS : SaidNext T Said b) :
    PlaysOn T.φ Bk T.chain T.ft T.hs blk (ThrS T Said b) (ThrS T Said (b + 1)) := by
  intro k s m E ds l hA hd hst hl
  obtain ⟨y, cols, hMv, hT⟩ := hP blk hblk k s m E ds l hA hd hst hl
  have hMv' := hMv
  unfold Thread.Moved at hMv'
  obtain ⟨⟨l', hl', hy⟩, hc⟩ := hMv'
  rw [hl] at hl'
  cases hl'
  refine ⟨y, cols, hy, hc, fun s' j hs => ?_⟩
  have hj : j = cols.length :=
    step_takes (yields_drawn _ _ _ _ (play_yields _ _ _ _ _ hy)) hc hs
  subst hj
  have hSt : T.Stepped blk k s m E ds y cols s' := by
    unfold Thread.Stepped
    exact ⟨hMv, hs⟩
  obtain ⟨hF, hRd, hK⟩ := hB blk hblk k s m E ds y cols s' hA hd hSt
  exact ⟨thr_next_at T hfit hb hblk hA.1 hd hSt hT hF hRd
      (hX blk hblk k s m E ds y cols s' hA hd hSt)
      (fun i v h1 h2 h3 h4 => hR k s m E s' y.1 i v hA hK h1 h2 h3 h4) hM,
    hS blk hblk k s m E ds y cols hA.1 hA.2 hd hMv⟩

theorem saysYes_of_acceptedS {b : Nat} {blk : Block S Cl}
    {fall : Nat → S → List Fmt.Drawn → Option String} (hblk : T.bs[b]? = some blk)
    (hA : AcceptedS T Said fall b) :
    SaysYes T.φ Bk T.chain T.ft T.hs blk (fall b) (ThrS T Said b) := by
  intro k s m E ds l y cols h0 hd hst hf hl hy hc
  have hMv : T.Moved blk k m E ds y cols := by
    unfold Thread.Moved
    exact ⟨⟨l, hl, hy⟩, hc⟩
  obtain ⟨s', hS⟩ := hA blk hblk k s m E ds y cols h0 hd hst hf hMv
  unfold Thread.Stepped at hS
  exact ⟨s', cols.length, hS.2⟩

/-! ## 5 At every sub-protocol -/

/-- The four hypotheses that say nothing of a fall, from `ThrS`, at every sub-protocol. (The fifth,
`MadeNext`, is proved once: `made_next`.) A definition, meant as a hypothesis. -/
def OwesS : Prop :=
  ∀ b, b < T.bs.length →
    PlaysS T Said b ∧ BehindS T Said b ∧ ExchangeS T Said b ∧ RidesPastS T Said b

/-- The acceptance, from `ThrS`, at every sub-protocol. A definition, meant as a hypothesis. -/
def YesS (fl : Nat → S → List Fmt.Drawn → Option String) : Prop :=
  ∀ b, b < T.bs.length → AcceptedS T Said fl b

theorem owesS_of (o : Owes T) : OwesS T Said := fun b hb =>
  ⟨playsS_of T Said (o b hb).1, behindS_of T Said (o b hb).2.1, exchangeS_of T Said (o b hb).2.2.1,
    ridesPastS_of T Said (o b hb).2.2.2⟩

theorem yesS_of {fl : Nat → S → List Fmt.Drawn → Option String} (y : Yes T fl) :
    YesS T Said fl := fun b hb => acceptedS_of T Said (y b hb)

/-- `PlaysOn` at every sub-protocol, at `ThrS`. -/
theorem playsOn_of_owesS (hfit : T.fits T.bs.length = true)
    (hsh : ∀ x ∈ T.bs, x.planOk = true ∧ x.shaped = true) (o : OwesS T Said)
    (n : ∀ b, SaidNext T Said b) : ∀ j b, T.bs[j]? = some b →
      PlaysOn T.φ Bk T.chain T.ft T.hs b (ThrS T Said j) (ThrS T Said (j + 1)) := by
  intro j b hb
  have hj := lt_of_member T hb
  obtain ⟨hP, hB, hX, hR⟩ := o j hj
  exact playsOn_of_paysS T Said hfit hj hb hP hB hX hR (made_next T hfit hsh j) (n j)

/-- `SaysYes` at every sub-protocol, at `ThrS`. -/
theorem saysYes_of_yesS {fl : Nat → S → List Fmt.Drawn → Option String} (y : YesS T Said fl) :
    ∀ j b, T.bs[j]? = some b → SaysYes T.φ Bk T.chain T.ft T.hs b (fl j) (ThrS T Said j) := by
  intro j b hb
  exact saysYes_of_acceptedS T Said hb (y j (lt_of_member T hb))

end ProofFile.Honest

#print axioms ProofFile.Honest.thr_next_at
#print axioms ProofFile.Honest.playsS_of
#print axioms ProofFile.Honest.behindS_of
#print axioms ProofFile.Honest.exchangeS_of
#print axioms ProofFile.Honest.ridesPastS_of
#print axioms ProofFile.Honest.acceptedS_of
#print axioms ProofFile.Honest.playsOn_of_paysS
#print axioms ProofFile.Honest.saysYes_of_acceptedS
#print axioms ProofFile.Honest.owesS_of
#print axioms ProofFile.Honest.yesS_of
#print axioms ProofFile.Honest.playsOn_of_owesS
#print axioms ProofFile.Honest.saysYes_of_yesS
