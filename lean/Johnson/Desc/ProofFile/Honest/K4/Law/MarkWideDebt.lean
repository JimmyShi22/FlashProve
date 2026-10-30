-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/MarkWideDebt.lean.

What is here. The wider mark of Law/MarkWide.lean in the form `MarkDebt`
(Honest/Law/CoverJoin.lean): the measure of the member's challenges at which the mark's test speaks
is at most the mark's stated share. AT THE KIT `Run.ckP .two` ALONE, where a round's challenge is a
string of hash blocks. A statement and its proof: one call of the law on a mark that speaks at
listed rounds alone (`markDebt_of_list_blocks`, Johnson/P1K8R/MarkRounds.lean), as for `k4Mark` in
Law/MarkDebt.lean. Its two premises on the mark's text are shown here (`k4MarkWide_speaks`) and in
Law/Mark.lean (`zeroOrOne_elem`). Its premise on the rounds' data, (h1), is shown in
Law/MarkWideElem.lean (`k4_markWide_h1`) at data whose entries are those of the verifier's table of
K4's rounds and whose kinds are their names'. NO COMPARISON OF THE PLAN's NUMBERS IS ASKED: la ≤
muV, which Law/MarkDebt.lean asks, is not a hypothesis here.

Not shown here. A BOUND ON THE MEASURE OF CHALLENGES AT WHICH A TEST SPEAKS: no run, no prover, no
coin, no input is in it. The called law's own limit holds here too: the uniform law on the rounds'
messages is named, not derived. WHAT THE MARK's SILENCE GIVES AT ANY STATE OF THE VERIFIER IS NOT
SHOWN. `k4_markWideDebt` IS CONDITIONAL ON (h1): each listed round of the data ds samples one field
element and nothing else, and its word for the logarithm of a length is at most 64.
`k4_markWideDebt_table` IS CONDITIONAL ON: (hent) the data's entries are the table's; (hkind) each
round's kind is its name's. THAT THE DATA OF ANY DESCRIPTION's MEMBER MEET hent AND hkind IS NOT
SHOWN: by reading, `k4_rounds` (Law/Plays.lean) with the frame's `KindFits` (Honest/Law/Due.lean)
would give both, round by round. The bound is the mark's stated share, a written product: NO NUMBER
IS EVALUATED. P, the sentence on the challenges in front, is free: the statement stands at every P.
No property is claimed. A LAW, NOT A PART: no file that defines a part of the proof file's
description may import this one: as Law/MarkDebt.lean, which it imports, says of itself.

  `k4MarkWide_speaks`   the test speaks only where the called law's own walk over the member's
      challenges does.
  `k4_markWideDebt`   **the sentence.**
  `k4_markWideDebt_table`   **the sentence at the table's own entries.**
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.MarkWideElem
import Johnson.Desc.ProofFile.Honest.K4.Law.MarkDebt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes.Desc.First.K4.Honest
open OnBytes.Maker (RDT)
open VerifiableInference.Desc.First.K8.Honest (OneElem)

/-- CONDITIONAL: on h. **The mark's test speaks only where that walk does.** -/
theorem k4MarkWide_speaks (Q : K4Pub) (fr own : List Fmt.Drawn)
    (h : ((k4MarkWide Q).test fr own).isSome = true) :
    P1K8.anyBad zeroOrOne (fun i => decide (i ∈ k4WideRounds Q)) 0 own = true := by
  have h' : (k4WideTest Q own).isSome = true := by
    rw [← k4MarkWide_test Q fr own]
    exact h
  unfold k4WideTest at h'
  split at h'
  · rename_i hc
    obtain ⟨i, hi, hx⟩ := List.any_eq_true.1 hc
    cases ho : own[i]? with
    | none =>
      rw [ho] at hx
      cases hx
    | some x =>
      rw [ho] at hx
      exact anyBad_at _ _ own 0 i x ho (by rw [Nat.zero_add]; exact decide_eq_true hi) hx
  · cases h'

/-- **THE WIDER MARK's SENTENCE**, at every sentence P on the challenges in front. CONDITIONAL on
(h1): see the head. -/
theorem k4_markWideDebt (Q : K4Pub) (ds : List RDT)
    (h1 : ∀ i d, ds[i]? = some d → i ∈ k4WideRounds Q →
      OneElem d.entry d.kind ∧ d.entry.logN ≤ 64)
    (P : List Fmt.Drawn → Prop) :
    MarkDebt (_root_.Run.ckP .two) (k4MarkWide Q) ds P (k4MarkWide Q).share.val :=
  P1K8.markDebt_of_list_blocks (k4MarkWide Q) zeroOrOne (k4WideRounds Q) ds (k4MarkWide_speaks Q)
    zeroOrOne_elem h1 (k4MarkWide_share Q) P

/-- CONDITIONAL on hent, hkind. **THE WIDER MARK's SENTENCE AT THE TABLE's OWN ENTRIES.** -/
theorem k4_markWideDebt_table (Q : K4Pub) (ds : List RDT)
    (hent : ds.map (·.entry) = OnBytes.Desc.First.K4.entries Q.P Q.hp Q.g)
    (hkind : ∀ d ∈ ds, Fmt.kindOf d.entry.name = some d.kind) (P : List Fmt.Drawn → Prop) :
    MarkDebt (_root_.Run.ckP .two) (k4MarkWide Q) ds P (k4MarkWide Q).share.val :=
  k4_markWideDebt Q ds (k4_markWide_h1 Q ds hent hkind) P

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4MarkWide_speaks
#print axioms ProofFile.Honest.K4.k4_markWideDebt
#print axioms ProofFile.Honest.K4.k4_markWideDebt_table
