-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Small/FormParts.lean: WHAT THE FIRST CHAIN's THREAD
(Honest/Thread/First.lean) GIVES OF THE TABLE's PROMISE AT A BORDER, CLAUSE BY CLAUSE. Statements
with their proofs.

What it is not. Nothing proves that the thread, or its clause on the promise, holds at any run: the
last two theorems and the example are CONDITIONAL on them. Every field of the letters is a letter.
No letter of any sub-protocol, border or size stands in the file: it is GENERAL IN THE FIRST CHAIN's
LETTERS and in the border. Nothing is claimed on soundness, completeness or hiding.

  `honestLike_honest`   the honest letters over a meaning are like it
                        (Honest/Small/PromiseParts.lean)
  `formP_iff`           the thread's clause on the promise is the library's `onAt` at the honest
                        letters, at the open sets under the library's names `openQ`, `pubQ`, at any
                        strings: both ways, by unfolding
  `partsAt_of_formP`    CONDITIONAL on that clause and "no mark": the eight clauses that read the
                        state, at the meaning `L.MgP` itself
  `partsAt_of_thr`      CONDITIONAL on the thread at the border: no mark, and the eight clauses
At the end, an example without a name: the statement of `thr_pub` (Honest/Thread/FormLaw.lean, which
this file does not import), out of `partsAt_of_thr`: the clause pub gives as much. That clause also
holds the public items that are tied to open items.

Written by the authors of the honest side of the output head's own rounds (K6), in the frame's
folder, not by the frame's authors.
All names stand in the namespace ProofFile.Honest.Small: a caller opens it.
-/
import Johnson.Desc.ProofFile.Honest.Small.PromiseParts
import Johnson.Desc.ProofFile.Honest.Thread.First

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Small
open VerifiableInference.Desc (Place Strs)
open VerifiableInference.Desc.First (S ModelPart Item Numbers Meaning onAt pubSets)
open VerifiableInference.Desc.Sound (openQ pubQ)
open ProofFile.Honest.FirstThread (Letters honest noStrs)

/-- **The honest letters over a meaning are like it.** -/
theorem honestLike_honest {P Wt : Type} (Mg : Meaning P Wt)
    (ans : Nat → Nat → P × S → Strs → Wt → Prop) (test : Nat → S → Option String) :
    HonestLike Mg (honest Mg ans test) :=
  ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ => trivial, fun _ _ _ => trivial, fun _ _ _ _ => trivial⟩

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok M : Type}

/-- **The thread's clause on the promise is the library's `onAt` at the honest letters** (`L.mgP`),
at every border, at the table's open sets as the library names them, at any strings. -/
theorem formP_iff (L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok M) (b : Nat) (a : P × S)
    (y : Strs) :
    L.thread.formP b a ↔
      onAt L.N L.mgP L.links L.ps[b]? (openQ L.links L.ps b) (pubQ L.mgP.more L.links L.ps b) a y :=
  Iff.rfl

/-- **The promise's clauses, at the meaning of which its public fields are read**: at every border,
at a state without a mark. -/
theorem partsAt_of_formP (L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok M) (b : Nat) (a : P × S)
    (h : L.thread.formP b a) (hm : a.2.failed = none) : PartsAt L.N L.MgP L.links L.ps b a :=
  partsAt_of_onAt (honestLike_honest L.MgP L.ans L.test) L.links L.ps b a noStrs h hm

/-- **Wherever the thread holds: no mark, and the promise's clauses.** -/
theorem partsAt_of_thr (L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok M) {b : Nat} {k : Coins Bk}
    {s : S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} (hT : Thr L.thread b k s m E) :
    s.failed = none ∧ PartsAt L.N L.MgP L.links L.ps b (L.pubOf m.st.input.x, s) := by
  unfold Thr at hT
  obtain ⟨-, -, ⟨hf, hP⟩, -, -, -, -⟩ := hT
  have hf' : s.failed.isNone = true := hf
  have hm : s.failed = none := Option.isNone_iff_eq_none.1 hf'
  exact ⟨hm, partsAt_of_formP L b (L.pubOf m.st.input.x, s) hP hm⟩

/-- So every public item that is open at the border has its test true of the state, wherever the
thread holds: the clause pub gives as much as `thr_pub` (Honest/Thread/FormLaw.lean) states. -/
example (L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok M) {b : Nat} {k : Coins Bk}
    {s : S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} (hT : Thr L.thread b k s m E)
    {q : VerifiableInference.Desc.First.Pub}
    (hq : q ∈ ((pubSets L.mgP.more L.links L.ps)[b]?).getD []) :
    L.mgP.pub q (L.pubOf m.st.input.x, s) = true :=
  (partsAt_of_thr L hT).2.pub q (List.mem_append_left _ hq)

end ProofFile.Honest.Small

#print axioms ProofFile.Honest.Small.honestLike_honest
#print axioms ProofFile.Honest.Small.formP_iff
#print axioms ProofFile.Honest.Small.partsAt_of_formP
#print axioms ProofFile.Honest.Small.partsAt_of_thr
