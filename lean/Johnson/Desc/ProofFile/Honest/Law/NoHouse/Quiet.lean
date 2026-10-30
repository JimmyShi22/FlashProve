-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/NoHouse/Quiet.lean: the hypotheses at a sub-protocol without a
round. At such a sub-protocol of a `Thread`'s flat list (Honest/Thread/Thr.lean) the prover's side
of the step is fixed by the functions of Honest/Frame.lean: nothing is played, nothing is drawn,
nothing is read (`moved_quiet`). So each of the hypotheses of Honest/Thread/PaysS.lean, which are
asked from `ThrS` (Honest/Thread/Said.lean), reduces to a condition on the sub-protocol's own step
at no round and no column, and on the `Thread`'s parameters. The lemmas are general in the `Thread`,
in `Said`, in the sub-protocol's number and in the sub-protocol: no kind is named.

What this is. Conditional lemmas on our own definitions. Their conclusions are definitions of ours,
meant as hypotheses. None of the library's goals.

  0  `moved_quiet`, `thr_tight`, `thr_item`   what the step is there; two clauses of the invariant
  1  `said_quiet`, `behindS_quiet`, `exchangeS_quiet`, `exchangeS_none`, `acceptedS_quiet`
  2  `acceptedS_item`   the acceptance from an open item, where the fall does not fire

`acceptedS_quiet` is `accepted_quiet` (Honest/Thread/FallRow.lean) with the invariant available:
that one asks the step's acceptance at every state. `acceptedS_item` is for a sub-protocol that
tests, and whose acceptance an earlier item has promised: the item's definition is used in its
hypothesis `hm`. `PlaysS` at such a sub-protocol that also declares no oracle message follows from
`plays_quiet` (Honest/Thread/QuietLaw.lean) with `playsS_of`.

Holds vacuously. As every such hypothesis: at an invariant that is false everywhere.
`acceptedS_quiet` and `acceptedS_item`: at a fall that fires wherever the step rejects.

Limits.
  * `RidesPastS` names no sub-protocol: it is no condition on the sub-protocol.
  * Nothing is proved of any sub-protocol of the protocol.
  * The premises' "for all m" run over the state's field `opened` too. At a sub-protocol without a
    round nothing is played and no column is read (`moved_quiet`): `SaidNext` is asked at the state
    that takes no column, which is m (`took_nil`, Honest/Law/RunsFile.lean).
  * Hypotheses that the prose above does not name: `drawsFit` (`drawFit` round by round, and as many
    challenges as rounds): `moved_quiet`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.PaysS
import Johnson.Desc.ProofFile.Honest.Thread.QuietLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place OpenedColumn Strs)

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)

/-! ## 0 What the step is there -/

/-- **At a sub-protocol without a round nothing is drawn, played or read.** -/
theorem moved_quiet {blk : Block S Cl} {k : Coins Bk} {m : Mid W X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid W X} {cols : List OpenedColumn} (hr : blk.rounds = [])
    (hd : drawsFit blk.rounds ds = true) (hM : T.Moved blk k m E ds y cols) :
    ds = [] ∧ y = ([], m) ∧ cols = [] := by
  obtain ⟨⟨l, hl, hy⟩, hc⟩ := hM
  have hl0 : l = [] := by
    have e := steps_decl hl
    rw [List.flatMap_cons, List.flatMap_nil, List.append_nil, hr] at e
    exact List.map_eq_nil_iff.1 e
  have hd0 : ds = [] := by
    have e := drawsFit_length _ _ hd
    rw [hr] at e
    exact List.eq_nil_of_length_eq_zero e
  subst hl0
  subst hd0
  have hy' : (Except.ok ([], m) : Except Refusal (List Played × Mid W X)) = .ok y := hy
  cases hy'
  rw [hr] at hc
  have hc' : (Except.ok [] : Except String (List OpenedColumn)) = .ok cols := hc
  cases hc'
  exact ⟨rfl, rfl, rfl⟩

/-- The invariant's clause (X): no tree of the chain's own is available above those sent. -/
theorem thr_tight {b : Nat} {k : Coins Bk} {s : S} {m : Mid W X} {E : Env} (h : Thr T b k s m E) :
    ∀ n, E.sent ≤ n → E.tree (.own n) = none :=
  h.2.2.2.2.1.2.2.2.1

/-- The invariant's clause (I), at one open item and the challenges heard. -/
theorem thr_item {b : Nat} {k : Coins Bk} {s : S} {m : Mid W X} {E : Env} (h : Thr T b k s m E)
    {i : T.ι} (hi : i ∈ T.opened b) :
    T.means m.st.input i (T.seat k m s) (T.strs E) (T.wit k m.st.input (m.st.heard ++ [])) :=
  h.2.2.2.1 [] i hi

/-! ## 1 The hypotheses -/

section
variable (Said : Nat → Coins Bk → Mid W X → Prop) {b : Nat} {blk : Block S Cl}

theorem said_quiet (hblk : T.bs[b]? = some blk) (hr : blk.rounds = [])
    (h : ∀ k m, Said b k m → Said (b + 1) k m) : SaidNext T Said b := by
  intro blk' hblk' k s m E ds y cols _ hS hd hM
  rw [hblk] at hblk'
  cases hblk'
  obtain ⟨-, rfl, rfl⟩ := moved_quiet T hr hd hM
  show Said (b + 1) k (m.took [])
  rw [took_nil]
  exact h k m hS

/-- **After its acceptance (`BehindS`).** -/
theorem behindS_quiet (hblk : T.bs[b]? = some blk) (hr : blk.rounds = [])
    (h : ∀ k s m E s', ThrS T Said b k s m E → blk.step T.ft s [] [] = .ok (s', 0) →
      T.Form (b + 1) k s' m ∧ T.rides (b + 1) m.st.input s' ∧ T.keeps b s s') :
    BehindS T Said b := by
  intro blk' hblk' k s m E ds y cols s' hA hd hS
  rw [hblk] at hblk'
  cases hblk'
  obtain ⟨hM, hstep⟩ := hS
  obtain ⟨rfl, rfl, rfl⟩ := moved_quiet T hr hd hM
  exact h k s m E s' hA hstep

/-- **The exchange (`ExchangeS`).** -/
theorem exchangeS_quiet (hblk : T.bs[b]? = some blk) (hr : blk.rounds = [])
    (h : ∀ k s m E s', ThrS T Said b k s m E → blk.step T.ft s [] [] = .ok (s', 0) →
      T.Items (T.row b).owes k s' m E) : ExchangeS T Said b := by
  intro blk' hblk' k s m E ds y cols s' hA hd hS
  rw [hblk] at hblk'
  cases hblk'
  obtain ⟨hM, hstep⟩ := hS
  obtain ⟨rfl, rfl, rfl⟩ := moved_quiet T hr hd hM
  show T.Items (T.row b).owes k s' m (E.add [])
  rw [Env.add_nil E (thr_tight T hA.1)]
  exact h k s m E s' hA hstep

/-- Where the list `(T.row b).owes` is empty `ExchangeS` holds, at any sub-protocol. -/
theorem exchangeS_none (h : (T.row b).owes = []) : ExchangeS T Said b := by
  intro blk' _ k s m E ds y cols s' _ _ _ ds' i hi
  rw [h] at hi
  cases hi

/-- **The acceptance (`AcceptedS`)**, with the invariant available. -/
theorem acceptedS_quiet {fall : Nat → S → List Fmt.Drawn → Option String}
    (hblk : T.bs[b]? = some blk) (hr : blk.rounds = [])
    (h : ∀ k s m E, ThrS T Said b k s m E → fall b s [] = none →
      ∃ s', blk.step T.ft s [] [] = .ok (s', 0)) : AcceptedS T Said fall b := by
  intro blk' hblk' k s m E ds y cols hA hd _ hf hM
  rw [hblk] at hblk'
  cases hblk'
  obtain ⟨rfl, rfl, rfl⟩ := moved_quiet T hr hd hM
  obtain ⟨s', hs'⟩ := h k s m E hA hf
  exact ⟨s', hM, hs'⟩

/-! ## 2 The acceptance from an open item -/

/-- **The acceptance from an open item, where the fall does not fire.** `i`: an item that is open
before the sub-protocol. `hm`: what the item says gives the step's acceptance where the fall does
not fire. -/
theorem acceptedS_item {fall : Nat → S → List Fmt.Drawn → Option String}
    (hblk : T.bs[b]? = some blk) (hr : blk.rounds = []) (i : T.ι) (hi : i ∈ T.opened b)
    (hm : ∀ w p s σ v, T.means w i (p, s) σ v → fall b s [] = none →
      ∃ s', blk.step T.ft s [] [] = .ok (s', 0)) : AcceptedS T Said fall b :=
  acceptedS_quiet T Said hblk hr fun _ _ _ _ hA hf => hm _ _ _ _ _ (thr_item T hA.1 hi) hf

end

end ProofFile.Honest

#print axioms ProofFile.Honest.moved_quiet
#print axioms ProofFile.Honest.thr_tight
#print axioms ProofFile.Honest.thr_item
#print axioms ProofFile.Honest.said_quiet
#print axioms ProofFile.Honest.behindS_quiet
#print axioms ProofFile.Honest.exchangeS_quiet
#print axioms ProofFile.Honest.exchangeS_none
#print axioms ProofFile.Honest.acceptedS_quiet
#print axioms ProofFile.Honest.acceptedS_item
