-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/FallCount.lean: CONDITIONAL. THE COUNT BENEATH THE FIRST FALL
OF THE LAYERS' OWN ROUNDS (kind K4; `k4Fall`, Honest/K4/Part.lean), AT STRINGS OF HASH BLOCKS.

What is here. Law/Falls.lean has the first fall's sentence (`FallDebt`, Honest/Law/CoverJoin.lean)
from a count at one round, `ZeroAtRound C d q`: at one round's typed challenges those that show 0 as
their first sampled element have at most the measure q. Here that count, at the kit `Run.ckP .two`
(a round's challenge is a string of hash blocks), for a round d that samples one field element and
nothing else: one call of the library's `gate_of_count_blocks` (Johnson/P1K8R/GateOfCount.lean) at
the count 1. THE BOUND, AS A TERM (`k4ZeroBound`): kapSl 128 ^ 3 * 1 / p ^ 3: that lemma's own
factor times, by reading, the fall's stated share (`k4CoinZeroShare`: 1 of p ^ 3), NOT THE SHARE.
Statements and proofs.

  `k4ZeroBound`: the bound's term, under a name. `zeroFirst_elem`: where the test on a challenge
      speaks at a written field element x alone, x is 0.
  `k4_zeroAtRound_blocks`: **the count at one round.**
  `k4_zeroCount_short`: where the member's data have no round of that number, the fall's test
      speaks at no challenge: the count holds at every q.
  `k4_zeroCount_blocks`: the count at the member's rounds, at every q from the bound on.
  `k4_coinZero_debt_blocks`, `k4_coinZero_debt_fits`: **the first fall's sentence at strings of
      hash blocks**, at every q from the bound on; the second with the data tied to the member's
      declared rounds as the frame ties them (`KindFits`, Honest/Law/Due.lean).

Not shown here. h1: THAT THE ROUND OF THE DATA AT WHICH THE FALL's TEST READS SAMPLES ONE FIELD
ELEMENT AND NOTHING ELSE, WITH POSITIONS OF AT MOST 64 BITS: a hypothesis here: `k4_coin_h1`
(Law/CoinRow.lean) has it where the data bear K4's own entries. At which member of a description a
fall is counted: Law/FallAtOwn.lean. The library's lemma's own limit holds here: the uniform law on
one round's messages is named, not derived. NO NUMBER IS EVALUATED: kapSl 128 and p are the
library's definitions, left as they stand. That the bound is below 1. MET FOR NOTHING at q of 1 or
more, at P := fun _ _ => False, and at every member b that does not stand at K4's place: there the
event is empty. All limits of Law/Falls.lean hold here too: no run, no prover, no coin and no input
is in these sentences.
No property is claimed.
A LAW, NOT A PART: no file that defines a part of the proof file's description may import this one:
through Johnson/P1K8R/GateOfCount.lean its imports reach modules under Johnson/Goal/.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.Falls
import Johnson.Desc.ProofFile.Honest.Law.Due
import Johnson.P1K8R.GateOfCount

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open Prob
open scoped ENNReal
open OnBytes (E isZeroE okE)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Maker (RDT uLT drawnT)
open _root_.Run.PQ (CK)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First.K8.Honest (OneElem)

variable {S Cl : Type}

/-- **The bound, as a term**: the library's factor kapSl 128 ^ 3 (Iop/DrawOf.lean) times 1 of p ^ 3,
in the very form in which `gate_of_count_blocks` ends at the count 1. A name for a term: nothing is
evaluated and nothing is claimed by it. -/
noncomputable def k4ZeroBound : ℝ≥0∞ :=
  Iop.kapSl 128 ^ 3 * ((1 : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞)

/-- CONDITIONAL: on h and he. Where the test on a challenge speaks at a written field element x
alone, x is 0. -/
theorem zeroFirst_elem (dr : Fmt.Drawn) (x : Cb.Gl.E) (h : zeroFirst dr = true)
    (he : dr.elems = [OnBytes.Slice.ofE x]) : x = 0 := by
  unfold zeroFirst at h
  rw [he] at h
  have h' : isZeroE (E.ofTriple (OnBytes.Slice.ofE x)) = true := h
  have ok : okE (E.ofTriple (OnBytes.Slice.ofE x)) = true := by
    rw [OnBytes.okE_triple]
    show Fmt.Fld.two.okE (OnBytes.Slice.ofE x) = true
    simp only [Fmt.Fld.okE, OnBytes.Slice.ofE, OnBytes.Slice.ok_ofF, Bool.and_self]
  have ex : OnBytes.Slice.readE (E.ofTriple (OnBytes.Slice.ofE x)) = x :=
    (OnBytes.Slice.readE_ofTriple _).trans (OnBytes.Slice.toE_ofE x)
  exact ex.symm.trans ((OnBytes.Slice.isZeroE_iff _ ok).1 h')

/-- CONDITIONAL: on h1 and hlog. **THE COUNT AT ONE ROUND, AT STRINGS OF HASH BLOCKS.** -/
theorem k4_zeroAtRound_blocks (d : RDT) (h1 : OneElem d.entry d.kind) (hlog : d.entry.logN ≤ 64) :
    ZeroAtRound (_root_.Run.ckP .two) d
      k4ZeroBound := by
  unfold ZeroAtRound k4ZeroBound
  refine le_trans (Prob.pr_mono _ fun ρ hρ => ?_)
    (P1K8.gate_of_count_blocks d h1 hlog (fun dr => zeroFirst dr = true) (fun x => x = 0)
      zeroFirst_elem 1 (Prob.cnt_le_one fun _ _ ha hb => ha.trans hb.symm))
  show ∃ dr, drawnT (_root_.Run.ckP .two) [d] ρ = [dr] ∧ zeroFirst dr = true
  have h2 : ((drawnT (_root_.Run.ckP .two) [d] ρ).head?.any zeroFirst) = true := hρ
  have hl := drawnT_len (_root_.Run.ckP .two) [d] ρ
  cases hx : drawnT (_root_.Run.ckP .two) [d] ρ with
  | nil =>
    rw [hx] at hl
    cases hl
  | cons a l =>
    cases l with
    | nil =>
      rw [hx] at h2
      exact ⟨a, rfl, h2⟩
    | cons c l' =>
      rw [hx] at hl
      simp at hl

/-- CONDITIONAL: on hd. Where the data have no round of that number the fall's test speaks at no
challenge. -/
theorem k4_zeroCount_short (C : CK) (Q : K4Pub) (ds : List RDT)
    (hd : ds[(starts Q).getD 2 0]? = none) (q : ℝ≥0∞) : K4ZeroCount C Q ds q := by
  unfold K4ZeroCount
  refine le_trans (Iop.prRho_empty _ fun ρ hρ => ?_) (zero_le q)
  have h2 : (k4CoinZero Q (drawnT C ds ρ)).isSome = true := hρ
  have hn : (drawnT C ds ρ)[(starts Q).getD 2 0]? = none := by
    rw [List.getElem?_eq_none_iff] at hd ⊢
    rw [drawnT_len C ds ρ]
    exact hd
  rw [k4CoinZero_at, hn] at h2
  cases h2

/-- CONDITIONAL: on h1 and hq. The count at the member's rounds. -/
theorem k4_zeroCount_blocks (Q : K4Pub) (ds : List RDT)
    (h1 : ∀ d, ds[(starts Q).getD 2 0]? = some d → OneElem d.entry d.kind ∧ d.entry.logN ≤ 64)
    (q : ℝ≥0∞)
    (hq : k4ZeroBound ≤ q) :
    K4ZeroCount (_root_.Run.ckP .two) Q ds q := by
  cases hd : ds[(starts Q).getD 2 0]? with
  | none => exact k4_zeroCount_short _ Q ds hd q
  | some d =>
    exact le_trans (k4_zeroCount _ Q ds d hd _ (k4_zeroAtRound_blocks d (h1 d hd).1 (h1 d hd).2)) hq

/-- CONDITIONAL: on hlen, h1 and hq. **THE FIRST FALL's SENTENCE AT STRINGS OF HASH BLOCKS**, at
every member b, every ft, all members t behind, every sentence P, at no fixed challenge behind. -/
theorem k4_coinZero_debt_blocks (Q : K4Pub) (ft : Nat) (b : Block S Cl) (t : List (Block S Cl))
    (dsb : List RDT) (hlen : dsb.length = b.rounds.length)
    (h1 : ∀ d, dsb[(starts Q).getD 2 0]? = some d → OneElem d.entry d.kind ∧ d.entry.logN ≤ 64)
    (q : ℝ≥0∞)
    (hq : k4ZeroBound ≤ q)
    (P : List Fmt.Drawn → S → Prop) :
    FallDebt (_root_.Run.ckP .two) (k4Fall Q) ft b t dsb [] P q :=
  k4_coinZero_debt _ Q ft b t dsb hlen q (k4_zeroCount_blocks Q dsb h1 q hq) P

/-- CONDITIONAL: on hfit, h1 and hq. The same with the data tied to the member's declared rounds. -/
theorem k4_coinZero_debt_fits (Q : K4Pub) (ft : Nat) (b : Block S Cl) (t : List (Block S Cl))
    (dsb : List RDT) (hfit : List.Forall₂ KindFits dsb b.rounds)
    (h1 : ∀ d, dsb[(starts Q).getD 2 0]? = some d → OneElem d.entry d.kind ∧ d.entry.logN ≤ 64)
    (q : ℝ≥0∞)
    (hq : k4ZeroBound ≤ q)
    (P : List Fmt.Drawn → S → Prop) :
    FallDebt (_root_.Run.ckP .two) (k4Fall Q) ft b t dsb [] P q :=
  k4_coinZero_debt_blocks Q ft b t dsb hfit.length_eq h1 q hq P

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.zeroFirst_elem
#print axioms ProofFile.Honest.K4.k4_zeroAtRound_blocks
#print axioms ProofFile.Honest.K4.k4_zeroCount_short
#print axioms ProofFile.Honest.K4.k4_zeroCount_blocks
#print axioms ProofFile.Honest.K4.k4_coinZero_debt_blocks
#print axioms ProofFile.Honest.K4.k4_coinZero_debt_fits
