-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PageIsProofs.lean: three of the four main statements of Run/PageIs.lean are proved
(`pi_formula`, `pi_half`, `pi_kits`), and their standing hypothesis holds at the format's oracle
(`Fmt.oracle`, Fmt/Rules23.lean: the single oracle on all byte strings, 32 bytes an answer, realised
by BLAKE2b), at both choices of challenge types in use, for every description within the limits of
the generic construction. Many statements of this library are written twice: a definition in the
namespace `Spec` states a proposition, and a theorem of the same name outside that namespace proves
it (lean/GLOSSARY.md).

Here the three are put together from their parts; no part is left as a hypothesis.

1. What the file contains. Theorems only.

2. What is checked when the file compiles. The proofs; there are no tests (#guard) here.

3. Theorems.
   `pi_formula`: the compiled verifier behind the lenient reader = (if the lenient reader hands out
      nothing: false; if it hands out o: every round's proof-of-work test ∧ every opening walks to
      the root that was sent ∧ dec on o's view). From `pi_facts` (Run/PageIsReaders.lean),
      `pi_chain` (Run/PageIsChain.lean), `pi_after` (Run/PageIsAfter.lean), by `formula_of`
      (Run/PageIsTopProofs.lean; so `half_of`, `kits_of`).
   `pi_half`: (F1) What the format's strict verifier with the decision accepts (Fmt/M1View.lean:
      verifyW at Fmt.HO O), the compiled verifier behind the lenient reader accepts.
   `pi_kits`: two choices of challenge types (the parameter C : CK; "kit" in names) that both fit
      give one verdict on every file.
   Each holds under PiFit O S C K chal: O's answers have 32 bytes; S lies within the limits of the
   generic construction (`PQ.ok`); the view that the choice of challenge types gives of the wiring's
   message is the format's draw on the first blocks (`KitFits`); every round's blocks number at most
   K. Each holds for every decision and every file.
   That `PiFit` holds at the format's oracle, at both choices of challenge types in use, wherever ok
   S does (this file gives no description with ok S = true):
   `bs_blocks`: a round's sampler has the format's number of blocks.
   `kit_ck`, `kit_pull`: `KitFits` holds of challenges as sampled values (`ck`, `chalOf`) and of
      challenges as hash blocks (`ckP`, `chalP`), at every field and every K (Run/PlanPull.lean:
      `planPull_view`; Run/PlanDraws.lean: `planDraws_tie`).
   `room_kOf`: every round's blocks number at most kOf S.
   `fit_ck`, `fit_pull`: ok S = true → PiFit Fmt.oracle S .. at (ck S.plan.field, kOf S, chalOf ..)
      and at (ckP S.plan.field, kOf S, chalP ..).
   `two_kits`: ok S = true → laxV Fmt.oracle S with challenges as sampled values = laxV Fmt.oracle S
      with challenges as hash blocks, for every decision and every file.

   Which way `pi_half` carries. If the format's strict verifier accepts a file, the compiled
   verifier behind the lenient reader accepts it. The compiled verifier's acceptance does not carry
   over by this statement. (F1) is the direction by which a soundness statement on the compiled
   verifier would reach the format's verifier. Whatever such a statement says of the strings that
   the compiled verifier accepts holds of all that the format's verifier accepts. That the compiled
   verifier may accept more costs nothing there. The converse is the direction by which a
   completeness statement on the compiled verifier would reach the format's verifier.

4. What is not claimed.
   `pi_core` (F2), the equation of the two sides, is not proved in this file. It is proved in
   Run/PageIsCoreProofs.lean, under `PiFit`, for files whose roots differ. So the converse of
   `pi_half`, "what the compiled verifier behind the lenient reader accepts, the format's strict
   verifier accepts", is not shown here.
   Neither a soundness nor a completeness statement exists in Run/ or Fmt/ for the protocols on
   whose files the run functions of Run/PageIsRun.lean and Run/PageIsOne.lean [not in this library] have been evaluated,
   beyond conditions that are empty. The empty conditions are the fields `sound` and `low` of the
   record `Met`; their generic forms are `lts_sound`, `metOf` (Run/M1Door.lean) and `lb_sound`,
   `metB` (Run/BatchDoor.lean). The library has the building blocks of such protocols (sum-check,
   folds, code switches, base case: Cb/*/Ld*.lean) with soundness statements. Nothing in Run/ or
   Fmt/ connects the two: these protocols and the building blocks.
   All that the head of Run/PageIs.lean leaves out is left out here too: Fmt.formatHash in the place of
   Fmt.HO O (see Run/StrictDom.lean); that Fmt/Rules8.lean renders the format page.
   `laxV` stands at the typed oracle functions that O induces (`famOf`) and at the evaluable form
   `verifyP` of the compiled verifier. That a given run function (runLaxC, run1C and their fast
   twins) is `laxV` is not said here; see Run/PageIsRun.lean (`run_lax`, for runLaxC, under its two
   tests); Run/PageIsOne.lean [not in this library] compares two run functions over a single oracle (`run1PF`, `run1K`)
   with Fmt.verify and with each other, not with `laxV`.

Sources. No text from outside enters.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.PageIsAfter
import Run.PageIsChain
import Run.PageIsReaders
import Run.PlanPullM1

set_option autoImplicit false

namespace Run.PQ
open Rom Iop Compile Compile.Batch

theorem pi_formula : Spec.pi_formula := formula_of pi_facts pi_chain pi_after

theorem pi_half : Spec.pi_half := half_of pi_formula pi_strict1

theorem pi_kits : Spec.pi_kits := kits_of pi_formula

/-! ### PiFit at the two choices of challenge types in use -/

theorem bs_blocks (f : _root_.Fmt.Fld) (e : _root_.Fmt.Entry) (k : _root_.Fmt.Kind) :
    (bsRound f e k).b = _root_.Fmt.blocksFor (_root_.Fmt.wordsAtMost e k) :=
  congrArg _root_.Fmt.blocksFor (_root_.Fmt.most_list e k)

theorem row_first (K : ℕ) (u : Fin K → Dig 256) :
    ∀ {b b' : ℕ}, b = b' → rowOfDigs (firstBlocks 256 K b u) = rowOfDigs (firstBlocks 256 K b' u)
  | _, _, rfl => rfl

/-- `KitFits` holds of challenges as hash blocks (`ckP`, `chalP`), at every field and every K. -/
theorem kit_pull (f : _root_.Fmt.Fld) (K : ℕ) : KitFits f (ckP f) K (chalP f K) := fun e k u =>
  ((planPull_view f e k (chalP f K e k u)).2).trans
    (congrArg (_root_.Fmt.drawRound f e k) (row_first K u (bs_blocks f e k)))

/-- `KitFits` holds of challenges as sampled values (`ck`, `chalOf`), at every field and every K. -/
theorem kit_ck (f : _root_.Fmt.Fld) (K : ℕ) : KitFits f (ck f) K (chalOf f K) := fun e k u =>
  ((planPull_view f e k (chalP f K e k u)).1.symm.trans
      (planPull_view f e k (chalP f K e k u)).2).trans
    (congrArg (_root_.Fmt.drawRound f e k) (row_first K u (bs_blocks f e k)))

/-- A round of the description has its round of the generic construction (`rdsFrom`), with the same
entry and kind. -/
theorem rds_mem (S : _root_.Fmt.Spec) :
    ∀ (rs : List _root_.Fmt.Round) (sent : ℕ),
      ∀ r ∈ rs, ∃ d ∈ rdsFrom S sent rs, d.entry = r.entry ∧ d.kind = r.kind
  | [], _, _, h => absurd h (List.not_mem_nil)
  | r' :: rs, sent, r, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨_, List.mem_cons_self .., rfl, rfl⟩
    · obtain ⟨d, hd, h1, h2⟩ := rds_mem S rs (sent + r'.entry.roots) r h
      exact ⟨d, List.mem_cons_of_mem _ hd, h1, h2⟩

theorem room_kOf (S : _root_.Fmt.Spec) :
    ∀ r ∈ S.rounds, _root_.Fmt.blocksFor (_root_.Fmt.wordsAtMost r.entry r.kind) ≤ kOf S := by
  intro r hr
  obtain ⟨d, hd, h1, h2⟩ := rds_mem S S.rounds 0 r hr
  rw [← bs_blocks S.plan.field, ← h1, ← h2]
  exact le_kMax (fun e k => (bsRound S.plan.field e k).b) (rds S) d hd

/-- At the format's oracle, within the limits of the generic construction, both choices of challenge
types in use fit: this theorem for sampled values, `fit_pull` for hash blocks. -/
theorem fit_ck (S : _root_.Fmt.Spec) (h : ok S = true) :
    Spec.PiFit _root_.Fmt.oracle S (ck S.plan.field) (kOf S) (chalOf S.plan.field (kOf S)) :=
  ⟨_root_.Fmt.size_oracle, h, kit_ck _ _, room_kOf S⟩

theorem fit_pull (S : _root_.Fmt.Spec) (h : ok S = true) :
    Spec.PiFit _root_.Fmt.oracle S (ckP S.plan.field) (kOf S) (chalP S.plan.field (kOf S)) :=
  ⟨_root_.Fmt.size_oracle, h, kit_pull _ _, room_kOf S⟩

/-- At the format's oracle, within the limits (`ok S`), the two choices of challenge types in use
give one verdict on every file. -/
theorem two_kits (S : _root_.Fmt.Spec) (h : ok S = true) (dec : View → Bool) (file : ByteArray) :
    laxV _root_.Fmt.oracle S (ck S.plan.field) (kOf S) (chalOf S.plan.field (kOf S)) dec file =
      laxV _root_.Fmt.oracle S (ckP S.plan.field) (kOf S) (chalP S.plan.field (kOf S)) dec file :=
  pi_kits _ S _ _ _ _ _ _ dec file (fit_ck S h) (fit_pull S h)

end Run.PQ
