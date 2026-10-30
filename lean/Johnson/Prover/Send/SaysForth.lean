--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Prover/Send/SaysForth.lean: THE SHARED "SENDING" (the kind K1), THE PROVER's SIDE: all that
the statement claims (Holds, Johnson/Desc/Means/Holds.lean) goes forwards over the sending. Two
statements and their proofs, in a file of their own because they call holds_forth
(Johnson/Desc/Means/Forth/Holds.lean).

  send_holds   Holds at the words in front, a statement in order, round 2 holds just the answers of
               Core.lean: Holds behind the sending at the held words
  send_holds_of_yes   the same at the record that any yes of K1.decideSend returns

The like for Claims, and the letters: Johnson/Prover/Send/Says.lean.
Limits: as there. Nothing on soundness, or on what any entry shows or does not show.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Send.Says
import Johnson.Desc.Means.Forth.Holds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Send
open OnBytes OnBytes.Slice OnBytes.Means Cb VerifiableInference.Desc
open _root_.Desc.Plain (DState)

variable {L : Type}

/-- **Holds goes forwards over the sending.** -/
theorem send_holds (P : K1.Par) (d : DState L) (r₁ r₂ : Fmt.RoundView) (w : Words GE) (V : ℕ → Rows)
    (hans : r₂.vals = (answers P (stSent d.st P.sent) d.st.oracles.size
      (held w d.st.oracles.size P V) (K1.seedsOf P r₁)).map .answer)
    (hI : InOrder d.st) (hH : Holds rdE d.st w) :
    Holds rdE (K1.behind P d (K1.seedsOf P r₁) (K1.answersIn r₂)).st
      (held w d.st.oracles.size P V) := by
  refine holds_forth rdE hI (ext_behind P d _ _) (fun g G hG r hr => Or.inl ⟨G, hG, hr⟩)
    (fun o x hx r hr => ?_)
    ⟨fun g G hG r hr => (says_held d.st P w V G r (hI.rows g G hG r hr)).2 (hH.rows g G hG r hr),
      fun o x hx r hr => (says_held d.st P w V _ r (hI.samples o x hx r hr)).2
        (hH.samples o x hx r hr)⟩
  rcases number_cases P d _ _ o x hx with ⟨_, hx'⟩ | ⟨k, hk, rfl⟩
  · exact Or.inl ⟨x, hx', hr⟩
  · exact Or.inr (send_says P d r₁ r₂ w V hans k x hk hx r hr)

/-- The same behind any yes of K1's decision: the record behind a yes is K1.behind. -/
theorem send_holds_of_yes (P : K1.Par) (owed : Option ℕ) (d x : DState L) (r₁ r₂ : Fmt.RoundView)
    (ids : Array ℕ) (w : Words GE) (V : ℕ → Rows)
    (hyes : K1.decideSend P owed d [r₁, r₂] = .ok (ids, x))
    (hans : r₂.vals = (answers P (stSent d.st P.sent) d.st.oracles.size
      (held w d.st.oracles.size P V)
      (K1.cutSeeds P.coordinates P.seeds (r₁.drawn.elems.map E.ofTriple))).map .answer)
    (hI : InOrder d.st) (hH : Holds rdE d.st w) :
    Holds rdE x.st (held w d.st.oracles.size P V) := by
  obtain ⟨_, _, rfl⟩ := (K1.decideSend_iff P owed d x r₁ r₂ ids).1 hyes
  exact send_holds P d r₁ r₂ w V hans hI hH

end Johnson.Prover.Send

#print axioms Johnson.Prover.Send.send_holds
#print axioms Johnson.Prover.Send.send_holds_of_yes
