-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/NoHouse/Fill.lean: the structure `NoHouse`
(Honest/Law/NoHouse/Bare.lean) at a sub-protocol without a round, from conditions on its decision
(`NoHouse.ofDecide`). The library describes the first chain's sub-protocols of the kind `frame` in
the form "b.rounds = []" with a condition on `b.decide` (`IM.FlatCase`, Johnson/IMR/FlatCases.lean:
front, laid, behind, cleared). This file has the glue, general in the sub-protocol. The step of a
sub-protocol without a round is its decision at no round and no group. Such a sub-protocol at whose
place no prover's side is defined is `Bare`. And the structure's fields follow from the same
conditions on the decision.

What this is. Lemmas on the library's `Block.step` and on definitions of ours. None of the library's
goals.

  `step_noRound`   without a round, the step accepts exactly where the decision at no round and no
     group does
  `bare_of_quiet`   such a sub-protocol, at whose place no prover's side is defined, is `Bare`
  `noHalf_of_kind`   no prover's side is defined at a place of a kind that no prover's side has
  `NoHouse.ofDecide`   the structure, from conditions on the decision

Beside the library's own lemmas. `quiet_step` (Johnson/Desc/LinkLaw2.lean) says the first at a
`roundlessBlock` as written. `step_noRounds` (Johnson/Desc/LinkLaw7.lean) says it at any sub-protocol
without a round whose decision is a function f of the state alone (hd : ∀ s rs gs, b.decide s rs gs
= f s): a near relative. Here no such hd is asked: the decision is read at no round and no group.
Three of the four forms of `FlatCase`, which state their hd as an "if and only if", need it so. That
"behind the batching" keeps what its runs keep is the library's (`Meaning.K2.link_behind_runs`,
Johnson/Goal/Meaning/RunsKeep.lean; `LinkJoin.holds_runBehind`,
Johnson/Desc/First/Link/Law/TotalMoves.lean) and is not repeated.

Holds vacuously. As `NoHouse`: at an invariant that is false everywhere; its field `yes` at a fall
that fires wherever the decision rejects.

Limits.
  * Nothing is proved of any sub-protocol of the protocol.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.Bare
import Johnson.Top.H0.StepLaws.StepLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-- **Without a round, the step accepts exactly where the decision at no round and no group does.**
-/
theorem step_noRound (ft : Nat) (b : Block S Cl) (hr : b.rounds = []) (s s' : S) :
    b.step ft s [] [] = .ok (s', 0) ↔ b.decide s [] [] = .ok s' := by
  rw [step_iff]
  unfold Block.Fits Block.shown Block.want
  rw [hr]
  constructor
  · rintro ⟨-, h, -⟩
    exact h
  · intro h
    exact ⟨⟨rfl, rfl⟩, h, rfl⟩

/-- A sub-protocol without a round, which declares as many lists of oracle messages as rounds, and
at whose place no prover's side is defined, is `Bare`. -/
theorem bare_of_quiet {hs : List (Placed V W X)} {b : Block S Cl} (hr : b.rounds = [])
    (ho : b.oracles.length = b.rounds.length)
    (hn : (hs.find? fun g => g.place == b.place) = none) : Bare hs b where
  none := hn
  lists := by
    rw [hr] at ho ⊢
    exact List.eq_nil_of_length_eq_zero ho
  plain := fun r h => by
    rw [hr] at h
    cases h

/-- No prover's side is defined at a place of a kind of which there is no prover's side. -/
theorem noHalf_of_kind {hs : List (Placed V W X)} {b : Block S Cl}
    (h : ∀ g ∈ hs, g.place.kind ≠ b.place.kind) :
    (hs.find? fun g => g.place == b.place) = none :=
  List.find?_eq_none.2 fun g hg hp => h g hg (by rw [eq_of_beq hp])

/-- **`NoHouse` at a sub-protocol without a round, from conditions on its decision.** -/
theorem NoHouse.ofDecide {T : Thread Bk S Cl V W X Pb} {Said : Nat → Coins Bk → Mid W X → Prop}
    {fall : Nat → S → List Fmt.Drawn → Option String} {b : Nat} {blk : Block S Cl}
    (seat : T.bs[b]? = some blk) (hr : blk.rounds = [])
    (ho : blk.oracles.length = blk.rounds.length)
    (hn : (T.hs.find? fun g => g.place == blk.place) = none)
    (said : ∀ k m, Said b k m → Said (b + 1) k m)
    (behind : ∀ k s m E s', ThrS T Said b k s m E → blk.decide s [] [] = .ok s' →
      T.Form (b + 1) k s' m ∧ T.rides (b + 1) m.st.input s' ∧ T.keeps b s s')
    (owes : ∀ k s m E s', ThrS T Said b k s m E → blk.decide s [] [] = .ok s' →
      T.Items (T.row b).owes k s' m E)
    (yes : ∀ k s m E, ThrS T Said b k s m E → fall b s [] = none →
      ∃ s', blk.decide s [] [] = .ok s')
    (rides : RidesPastS T Said b) : NoHouse T Said fall b blk := by
  have nil : ∀ ds, drawsFit blk.rounds ds = true → ds = [] := fun ds hd => by
    have e := drawsFit_length _ _ hd
    rw [hr] at e
    exact List.eq_nil_of_length_eq_zero e
  refine ⟨seat, bare_of_quiet hr ho hn, ?_, ?_, ?_, ?_, rides⟩
  · intro k m ds hS hd
    rw [nil ds hd]
    exact said k m hS
  · intro k s m E ds s' hA hd hs
    rw [nil ds hd] at hs ⊢
    exact behind k s m E s' hA ((step_noRound T.ft blk hr s s').1 hs)
  · intro k s m E ds s' hA hd hs
    rw [nil ds hd] at hs ⊢
    exact owes k s m E s' hA ((step_noRound T.ft blk hr s s').1 hs)
  · intro k s m E ds hA hd hf
    rw [nil ds hd] at hf ⊢
    obtain ⟨s', hs'⟩ := yes k s m E hA hf
    exact ⟨s', (step_noRound T.ft blk hr s s').2 hs'⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.step_noRound
#print axioms ProofFile.Honest.bare_of_quiet
#print axioms ProofFile.Honest.noHalf_of_kind
#print axioms ProofFile.Honest.NoHouse.ofDecide
