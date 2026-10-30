--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Means/Forth/Send.lean: all that a statement claims goes forwards over the two plain
functions of a sending: the receiving of oracle messages, and the admitting of a message's sample
rows, if these rows hold.

It goes on from Johnson/Desc/Means/Forth/Holds.lean.

  recvP_forth     messages that are received claim nothing: a new message has no sample row yet
  admitP_forth    a message's sample rows are written: all that the statement claims behind holds,
                  if these rows hold at the statement behind
  admitP_forth_at the same, if these rows are on the message and hold at the statement in front

What is assumed, in each: the function returns a state; the statement in front is in order; all that
it claims holds. In admitP_forth moreover: the new sample rows hold of the words, at the statement
behind the admitting. No theorem of this file shows that of any answers. Behind admitP_forth alone a
caller cannot show the statement in order (admitP_keeps, Johnson/Desc/Means/Page.lean, asks that the
rows are on the message): admitP_forth_at is the one from which a caller can go on.
The words m are the same in front and behind: those at the new messages' numbers stand in m already.
A caller whose words grow with each sending goes from the words in front to the words behind by
allMet_agree (Johnson/Desc/Means/Forth/AllMet.lean), and then calls these lemmas at the words
behind. What is not claimed. Nothing on a verifier's decision, on soundness or on hiding.

-/
import Johnson.Desc.Means.Forth.Holds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means
open VerifiableInference.Desc.Ground Desc.Plain

variable {K : Type} [CommRing K] (ρ : OnBytes.Model.Reading K) {m : Words K} {Lc : Type}

/-- If recvP returns a state, the statement in front is in order and all that it claims holds, all
that the statement behind claims holds: a message that is received has no sample row yet. -/
theorem recvP_forth {d d' : DState Lc} {first : Nat} {sent : Array OracleNotice} {ids : Array Nat}
    (h : recvP first d sent = some (ids, d')) (hI : InOrder d.st) (hH : Holds ρ d.st m) :
    Holds ρ d'.st m := by
  unfold recvP at h
  split at h
  · obtain ⟨lay, _, e⟩ := Option.map_eq_some_iff.1 h
    obtain rfl : _ = d' := congrArg Prod.snd e
    refine holds_forth ρ hI (extends_stSent d.st sent) (fun g G hG r hr => Or.inl ⟨G, hG, hr⟩)
      (fun o x' hx' r hr => ?_) hH
    have hx'' : (Slice.stSent d.st sent).oracles[o]? = some x' := hx'
    by_cases ho : o < d.st.oracles.size
    · rw [Slice.stSent_old d.st sent o ho] at hx''
      exact Or.inl ⟨x', hx'', hr⟩
    · obtain ⟨i, rfl⟩ : ∃ i, o = d.st.oracles.size + i := ⟨o - d.st.oracles.size, by omega⟩
      rw [Slice.stSent_new] at hx''
      obtain ⟨n, _, rfl⟩ := Option.map_eq_some_iff.1 hx''
      simp at hr
  · cases h

/-- **If admitP returns a state, the statement in front is in order, all that it claims holds, and
the sample rows that are written hold at the statement behind, all that the statement behind claims
holds.** That these rows hold is a premise. -/
theorem admitP_forth {d d' : DState Lc} {o : Nat} {rows : Array Row}
    (h : admitP d o rows = some d') (hI : InOrder d.st) (hH : Holds ρ d.st m)
    (hs : ∀ r ∈ rows.toList, Says ρ d'.st r m) : Holds ρ d'.st m := by
  unfold admitP at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨x, _, places, _, rfl⟩ := h
    refine holds_forth ρ hI (extends_admitted d.st o x.shape places rows)
      (fun g G hG r hr => Or.inl ⟨G, hG, hr⟩) (fun o' x' hx' r hr => ?_) hH
    have hx'' : (d.st.oracles.modify o fun y => { y with
        sampled := true, sampleRows := rows, pad := places.map fun q => (q.part, q.index),
        ledger := Slice.freshLedger d.st.codes x.shape })[o']? = some x' := hx'
    obtain ⟨x0, hx0, c⟩ := elem_of_modify o' x' hx''
    rcases c with rfl | rfl
    · exact Or.inl ⟨_, hx0, hr⟩
    · exact Or.inr (hs r hr)
  · cases h

/-- The same with the premise at the statement in front: the rows are on the message, and hold. -/
theorem admitP_forth_at {d d' : DState Lc} {o : Nat} {rows : Array Row}
    (h : admitP d o rows = some d') (hI : InOrder d.st) (hH : Holds ρ d.st m)
    (hr : ∀ r ∈ rows.toList, RowOn d.st o r) (hs : ∀ r ∈ rows.toList, Says ρ d.st r m) :
    Holds ρ d'.st m := by
  refine admitP_forth ρ h hI hH fun r hm => ?_
  unfold admitP at h
  split at h
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨x, _, places, _, rfl⟩ := h
    exact (says_extends ρ (extends_admitted d.st o x.shape places rows) (hr r hm) m).2 (hs r hm)
  · cases h

end OnBytes.Means

#print axioms OnBytes.Means.recvP_forth
#print axioms OnBytes.Means.admitP_forth
#print axioms OnBytes.Means.admitP_forth_at
