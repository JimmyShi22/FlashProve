-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/ThreadAtChain.lean: the invariant's condition before a round that
a prover's side made, for one chain, from its start. It is `chain_live` (Honest/Law/ThreadAt.lean)
at a chain's own `ChainProgress.start` and `walk` (Honest/Walk.lean): where, after the rounds of the
sub-protocols pre, the walk has produced a round that a prover's side made, the walk over these
sub-protocols' rounds returns; it has produced just these rounds; the next sub-protocol is the next
to be asked, and none of its rounds has been produced; and the invariant before that sub-protocol
holds at the walk's own state of the prover's run, at its own state of the verifier, and at the
tables produced so far.

What this is. A conditional lemma on this folder's own functions, pointwise. It is none of the
library's goals.

  `thread_chain`   the lemma

By what, of others: `K12.live_field` (Honest/K12/LiveField.lean): `y.own`, `y.todo`.

Limits.
  * The sub-protocol before which the condition is stated has a round.
  * Nothing is said of `play`: the walk lengthens the state's field `opened` after each
    sub-protocol, `play` does not (Honest/Law/RunMid.lean, Honest/Law/WalkMid.lean).
  * Among the hypotheses that the prose above does not name: `drawsFit` (`drawFit` round by round,
    and as many challenges as rounds): `thread_chain`.
  * `PlaysOn` is asked at every state that the invariant allows, at every value of the field
    `opened` too: where a sub-protocol of pre has a part that reads the columns and errs at `none`
    (its duty: Honest/Frame.lean, `Seen.opened`), `PlaysOn` at an invariant before it that lets
    `none` through is met only vacuously (Honest/Law/ThreadC.lean, Limits).
  * The lemma proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.ThreadAt
import Johnson.Desc.ProofFile.Honest.Law.WalkMid
import Johnson.Desc.ProofFile.Honest.K12.LiveField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Cl V W Y Pb : Type}

section
variable {φ : Face V W Pb} {Bk : ProverCoinCounts} {hs : List (Placed V W Y)}

/-- **The invariant's condition before a round that a prover's side made.** `pre`: the sub-protocols
before; `b`: the next sub-protocol, which has a round; `t`: those after it. `y`: the walk after the
rounds of `pre`. The first invariant is asked at the state as `ChainProgress.start` lays it: m₀ with
`some front` in the field `opened`. -/
theorem thread_chain (L : Lay) (taken : Nat → Nat → Option (Place × Table))
    (hL : ∀ ps, L.tree ps = (envOf L.stored taken ps).tree) (k : Coins Bk) (v : Option V)
    (pre : List (Block S Cl)) (b : Block S Cl) (t : List (Block S Cl)) (hb : 0 < b.rounds.length)
    (I : Nat → Coins Bk → S → Mid W Y → Env → Prop)
    (hP : ∀ j c, pre[j]? = some c → PlaysOn φ Bk L.chain L.firstTree hs c (I j) (I (j + 1)))
    {a z : ChainProgress S Cl W Y} {ss : List (Step W Y)} {ds : List Fmt.Drawn} (m₀ : Mid W Y) (s₀ : S)
    {front : List OpenedColumn} (ha : ChainProgress.start L (pre ++ b :: t) (some m₀) (some s₀) front = .ok a)
    (hz : walk L ss ds a = .ok z)
    (hss : chainSteps Bk (Bk.rowsOf L.chain) (k.look L.chain) v (pre ++ b :: t) hs = .ok ss)
    (hsee : φ.sees m₀.st.input = v)
    (h0 : I 0 k s₀ { m₀ with opened := some front } (envOf L.stored taken []))
    (hd : drawsFit ((pre ++ b :: t).flatMap (·.rounds)) ds = true)
    (hst : chainStopAt v (pre ++ b :: t) hs m₀.loc ds = none)
    (ht : ∃ p ∈ z.laid.drop (pre.flatMap (·.rounds)).length, p.told = true) :
    ∃ y s m, walk L (ss.take (pre.flatMap (·.rounds)).length)
        (ds.take (pre.flatMap (·.rounds)).length) a = .ok y ∧
      y.laid = z.laid.take (pre.flatMap (·.rounds)).length ∧ y.mid = some m ∧ y.ver = some s ∧
      y.own = [] ∧ y.todo = b :: t ∧
      I pre.length k s m
        (envOf L.stored taken (z.laid.take (pre.flatMap (·.rounds)).length)) := by
  have hp0 := steps_part0 _ _ hss
  rw [chainSteps_append] at hss
  obtain ⟨l₁, hl₁, hss⟩ := exBind_ok hss
  obtain ⟨l₂, hl₂, rfl⟩ := exMap_ok hss
  have hn : l₁.length = (pre.flatMap (·.rounds)).length := by
    rw [← steps_decl hl₁, List.length_map]
  have hlen := walk_len L _ _ a z hz
  rw [List.flatMap_append, drawsFit_append, Bool.and_eq_true] at hd
  rw [chainStopAt_append] at hst
  obtain ⟨st₁, -⟩ := or_none hst
  have hdl : (ds.take (pre.flatMap (·.rounds)).length).length = l₁.length := by
    rw [drawsFit_length _ _ hd.1, hn]
  have hz' : walk L (l₁ ++ l₂) (ds.take (pre.flatMap (·.rounds)).length ++
      ds.drop (pre.flatMap (·.rounds)).length) a = .ok z := by
    rw [List.take_append_drop]
    exact hz
  obtain ⟨z₁, w1, w2⟩ := walk_append_ok l₂ _ l₁ _ a z hdl hz'
  have hal : a.laid = [] := by
    unfold ChainProgress.start at ha
    have g := settle_laid L _ _ a ha
    exact g
  obtain ⟨ps₁, f1, f1'⟩ := walk_laid' L _ _ a z₁ w1
  obtain ⟨ps₂, f2, -⟩ := walk_laid' L _ _ z₁ z w2
  rw [hal, List.nil_append] at f1
  have e1 : ps₁.length = (pre.flatMap (·.rounds)).length := by rw [f1', hn]
  have htake : z.laid.take (pre.flatMap (·.rounds)).length = z₁.laid := by
    rw [f2, f1]
    exact List.take_left' e1
  have hdrop : z.laid.drop (pre.flatMap (·.rounds)).length = ps₂ := by
    rw [f2, f1]
    exact List.drop_left' e1
  rw [hdrop] at ht
  have live := told_live L _ _ z₁ z ps₂ w2 f2 ht
  have X : (ChainProgress.settle L (pre ++ b :: t)
      ⟨some { m₀ with opened := some front }, some s₀, none, [], [], [], pre ++ b :: t, []⟩).bind
      (walk L l₁ (ds.take (pre.flatMap (·.rounds)).length)) = .ok z₁ := by
    have e : ChainProgress.settle L (pre ++ b :: t)
        ⟨some { m₀ with opened := some front }, some s₀, none, [], [], [], pre ++ b :: t, []⟩ =
        .ok a := ha
    rw [e]
    exact w1
  obtain ⟨s', m', v1, q1, i1⟩ := chain_live (φ := φ) (hs := hs) L taken hL k v b t hb pre I hP l₁ _
    z₁ _ s₀ { m₀ with opened := some front } (fun u hu => hp0 u (List.mem_append_left _ hu)) rfl
    rfl rfl hsee h0 st₁ hl₁ hd.1 X live
  obtain ⟨_, _, -, o1, t1, -⟩ := K12.live_field L hL pre b t 0 hb m₀ s₀ front ha w1
    (by rw [hn, Nat.add_zero]) q1
  refine ⟨z₁, s', m', ?_, htake.symm, q1, v1, List.eq_nil_of_length_eq_zero o1, t1, ?_⟩
  · rw [← hn, List.take_left' rfl]
    rw [← hn] at w1
    exact w1
  · rw [htake]
    exact i1

end

end ProofFile.Honest

#print axioms ProofFile.Honest.thread_chain
