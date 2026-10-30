-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/PileIs.lean: THE LAW ON THE PILE's FILLER THAT IS ASKED OF THE
VERIFIER's OWN FOLD (`PileIs`: its definition lies in Johnson/Desc/K13/Honest/PileDefs.lean) GIVES
`RowsTie` (ExchangeAtM3.lean of this folder) AS THAT IS TYPED. One conditional lemma, and one
equation.

Why. That the filler yields what the verifier's state holds was asked as `RowsTie`, from the thread
at the border in front of the batching. W's data wants the same one border on, where that thread is
not at hand. The thread says how the state was made: it is the fold of the sub-protocols' own steps
over what was shown. So the law is asked of that fold: it names no coin, no stand of the prover's
run and no table.
Main names:
  `rowsTie_of_pileIs`: **`PileIs` at the thread's own list, first state and border, at n := the
    number of rounds in front of the border, gives `RowsTie`.** `RowsTie` stays as it is typed. The
    proof spends three of the thread's clauses: how the state was made; that the challenges heard
    have the rounds' form, for their number; that the state bears no mark.
  `roundsTo_eq_roundsAhead`: the frame's `roundsTo` is `roundsAhead`
    (Johnson/Desc/K13/Honest/FoldCut.lean), by unfolding.

What is not claimed. That any filler meets `PileIs`: `pileBySites` is a filler's text up to its list
of sites and its parameter: no list of sites and no parameter has a text. That nothing else of the
thread bears on a row's weights and point. It is none of the library's goals. Nothing on soundness,
completeness or hiding.
-/
import Johnson.Desc.K13.Honest.PileDefs
import Johnson.Desc.K13.Honest.FoldCut
import Johnson.Desc.ProofFile.Honest.K13.ExchangeAtM3
import Johnson.Desc.ProofFile.Honest.Law.Along

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes
open VerifiableInference.Desc (Block foldBlocks)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Honest (rowReads PileIs)
open ProofFile.Honest.FirstThread (Letters)

variable {Cl Xi : Type}

variable {Bk : ProverCoinCounts} {W₀ Rc Tr X Pp Cells Tok M : Type}

/-- The frame's count of the rounds in front of a border is FoldCut.lean's. -/
theorem roundsTo_eq_roundsAhead {S' : Type} (bs : List (Block S' Cl)) (j : Nat) :
    roundsTo bs j = VerifiableInference.Desc.K13.Honest.roundsAhead bs j := rfl

/-- **It gives `RowsTie`, as that is typed.** -/
theorem rowsTie_of_pileIs (L : Letters Bk Cl W₀ Rc Xi Tr X Pp Cells Tok M) (b : Nat)
    (pile : PileOf Xi) (asked : Xi → E)
    (h : PileIs L.bs (fun x => L.first (L.pubOf x)) b (roundsTo L.bs b) pile asked) :
    RowsTie L b pile asked := by
  intro k s m En hT hR d
  unfold Thr at hT
  obtain ⟨-, hF, hP, -, hM, -, -⟩ := hT
  unfold Thread.Made at hM
  obtain ⟨hseen, -, -, -, s₀, cols, hb, -, hf⟩ := hM
  have hb' : s₀ = L.first (L.pubOf m.st.input.x) := hb
  subst hb'
  have hf' : foldBlocks 0 (L.bs.take b) (L.first (L.pubOf m.st.input.x)) m.seen cols =
      .ok (s, [], []) := hf
  have hfail : s.failed = none := Option.isNone_iff_eq_none.1 hP.1
  have hlen : m.st.heard.length = roundsTo L.bs b := drawsFit_length _ _ hF
  have hall : m.seen.take (roundsTo L.bs b) = m.seen := by
    apply List.take_of_length_le
    rw [← hlen, ← hseen, List.length_map]
  have q := h m.st.input.x m.seen cols s [] [] hf' hfail hR [d]
  rw [hall, hseen] at q
  exact q

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.roundsTo_eq_roundsAhead
#print axioms ProofFile.Honest.K13.rowsTie_of_pileIs
