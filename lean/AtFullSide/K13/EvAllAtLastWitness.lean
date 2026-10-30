-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K13/EvAllAtLastWitness.lean: kind K13 (the members' batching): the meaning `evAll`
(Johnson/Desc/ProofFile/Honest/K14/EvAtLastStart.lean) of the last chain's item "ev", at the first
chain's last state, OF THE LAST CHAIN's WITNESS (`lastWitness`,
Johnson/Desc/ProofFile/Honest/Thread/TheFirstThread.lean): the first chain's Script's witness with
the shared chain's sampled messages laid over it. The full size, and the hash function
`OnBytes.secondHashFunction`, alone. Statements with their proofs; no definition.

Main names.
  `evAll_of_words`: `evAll` goes from one witness to another that gives every message of the first
    chain's last statement the same words.
  `k13_evAll_at_lastWitness`: **wherever the first chain's thread as it is written (`firstThread`)
    holds at its last border, `evAll` holds of the last chain's witness**, at every continuation of
    the challenges. From the head at the return and the thread alone.

How. `k13_evAll_of_thread` (EvAllAtEnd.lean of this folder) has `evAll` of the first Script's
witness. In the first chain's last book every message that has a seat sits in a tree whose number is
below the first chain's count of trees (`head_seats_below`,
Johnson/Desc/ProofFile/Honest/K14/FirstSeatsBelow.lean), and below that count the overlay leaves a
message's table and pad (`wordsBy_first`,
Johnson/Desc/ProofFile/Honest/K14/FirstAtLastWitness.lean); a row's sentence reads the words of the
statement's own messages alone (`says_below`, Johnson/Desc/Sound/EvalKept.lean).

Limits. Conditional on the head and on the thread's invariant at border 358. THAT THE INVARIANT
HOLDS THERE AT ANY RUN IS NOT SHOWN HERE. That the statement is laid into a last chain's thread as
its item "ev" at border 0 is not shown here: z, y and the continuation are variables so that it can
be. The words hold values of the index's own entries: these statements are not to stand in front of
a law over coins.

What is not claimed. Neither is one of the library's goals. Nothing on soundness, completeness or
hiding.
-/
import AtFullSide.K13.EvAllAtEnd
import Johnson.Desc.ProofFile.Honest.K14.FirstAtLastWitness
import Johnson.Desc.ProofFile.Honest.K14.FirstSeatsBelow
import Johnson.Desc.Sound.EvalKept

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K13
open OnBytes
open ProofFile.Honest
open VerifiableInference.Desc (Strs Wit)
open VerifiableInference.Desc.Sound (MsgT wordsFirst seatBy noFirst says_below)
open P5J (TS)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts IndexReaders firstThread lastWitness)
open ProofFile.Honest.K14 (evAll wordsBy_first head_seats_below)

/-- `evAll` goes from one witness to another that gives every message the same words, read through
the first chain's last state's own book. -/
theorem evAll_of_words {P S₁ Cells Tok : Type} {arr : ℕ → ℕ → ℕ}
    {fs : P × S₁ → VerifiableInference.Desc.First.S} {q : P × S₁} {y : Strs}
    {v v' : Wit Cells Tok MsgT}
    (hw : ∀ o, o < (fs q).st.oracles.size → ∀ part i,
      wordsFirst arr (fs q).st (fs q).book v' o part i =
        wordsFirst arr (fs q).st (fs q).book v o part i)
    (h : evAll arr fs q y v) : evAll arr fs q y v' := by
  intro l G hl hG r hr
  exact (says_below OnBytes.Model.Reading.gl (fs q).st r
    fun o ho part i => (hw o ho part i).symm).1 (h l G hl hG r hr)

/-- **Wherever the first chain's thread holds at its last border, every open row of the own group
holds of the words of the last chain's witness**, at every continuation of the challenges. No
premise but the head at the return and the thread's invariant at that border, which holds (Eval)'s
sentence among its clauses. -/
theorem k13_evAll_at_lastWitness {W₀ Rc Tr X₀ X' : Type} {files : VerifierAndGoals.PublicFiles}
    {A : OnlineProverWithDescription W₀ Rc Tr X₀ X'} (hd : HeadAtReturn files A) (first : FirstThreadParts A)
    (reads : IndexReaders W₀ Rc) (w : Local W₀ Rc ProofFile.Inst Tr) {k : Coins A.B} {s : TS}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {En : Env}
    (hT : Thr (firstThread hd first w) 358 k s m En)
    (ds' : List Fmt.Drawn) (z : ProofFile.InstPub) (y : Strs) :
    evAll (P5J.At.arr A.Z) (fun q : ProofFile.InstPub × TS => q.2) (z, s) y
      (lastWitness hd first reads k m.st.input (m.st.heard ++ ds')) :=
  evAll_of_words (fs := fun q : ProofFile.InstPub × TS => q.2) (q := (z, s))
    (fun o _ part i => wordsBy_first hd first reads k m.st.input (m.st.heard ++ ds')
      (seatBy noFirst s.book) s.st o
      (head_seats_below hd.head A.H first.script _ _ _ _ _ _ _ _ _ w
        (le_of_eq (len358 hd.head).symm) hT o) part i)
    (k13_evAll_of_thread hd.head A.H first.script _ _ _ _ _ _ _ _ _ w hT ds' z y)

end AtFullSide.K13

#print axioms AtFullSide.K13.evAll_of_words
#print axioms AtFullSide.K13.k13_evAll_at_lastWitness
