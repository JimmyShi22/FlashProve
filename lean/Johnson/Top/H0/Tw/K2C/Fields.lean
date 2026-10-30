-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/Fields.lean: the kind «the code switch»: THE BLOCK's FIELDS BESIDE ITS
DECISION, EACH HELD BY A STATEMENT. NO BLOCK IMPORTS THIS FILE.
WHY: the laws on what a yes asks (K2C/Asks | AsksWhole | AsksOpen) speak of «decide» and «planOk»
alone. What the block DECLARES to the fold (its rounds, the oracle messages beneath the roots of
each round, the trees that it opens, that it states no run) stood in no statement: a turn of such
a field left every law green.
  k2_oracles    two rounds: beneath the first round's roots the place's list «sent»; the second
                round has no root
  k2_rounds · k2_before · k2_claims · k2_after · k2_name · k2_place · k2_decide
  rounds_two    the rounds are two: the entry "SEND seed" with the place's work, roots, seeds and
                non-zero draws; the entry "LOC" with its work, answers, positions and range, and
                one opening for each tree of «read», at the chain's own number
  oracles_fit   where the test on the plan says yes, the first round declares as many oracle trees
                as its entry has roots (32 bytes a root)
LIMITS. Each holds by unfolding: these are the text's own words, said once more, so that a turn of
the text is seen. THAT THE DECLARED LIST «sent» IS WHAT THE RUN's SENDING LAYS (tree by tree:
length and width) IS NOT SAID HERE: K2C/SentTrees.lean says it, inside a fence: the list is made
off the plan (Johnson/Desc/ProofFile/Lot/K2OfPlan.lean: oraclesAt, of the program's layTrees at
the plan's codes and announcements); the run's sending lays layTrees' trees at the record's codes
and the front's announcements; that these two pairs are one is the fence of K2C/SendsOn.lean, a
premise there. No soundness is claimed.
-/
import Johnson.Top.H0.Tw.K2C.Kind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block)

variable {Cl : Type}

theorem k2_name (p : P2) : (codeSwitchKind p : Block S Cl).name = p.name := rfl
theorem k2_place (p : P2) : (codeSwitchKind p : Block S Cl).place = p.place := rfl
theorem k2_rounds (p : P2) : (codeSwitchKind p : Block S Cl).rounds = rounds p := rfl
theorem k2_oracles (p : P2) : (codeSwitchKind p : Block S Cl).oracles = [p.sent, []] := rfl
theorem k2_before (p : P2) :
    (codeSwitchKind p : Block S Cl).before = p.read.map fun r => (p.place.chain, r.1) := rfl
theorem k2_decide (p : P2) :
    (codeSwitchKind p : Block S Cl).decide = decideWith _root_.Tw.K2.sendByL8 p := rfl
theorem k2_claims (p : P2) : (codeSwitchKind p : Block S Cl).claims = [] := rfl
theorem k2_after (p : P2) : (codeSwitchKind p : Block S Cl).after = [] := rfl

theorem rounds_two (p : P2) :
    rounds p =
      [ { entry := { name := "SEND seed", work := p.work₁, msg := 32 * p.roots, roots := p.roots,
                     drawE := p.seeds, drawNZ := p.nonZero } },
        { entry := { name := "LOC", work := p.work₂, msg := 24 * p.answers, answers := p.answers,
                     poss := p.positions, logN := p.logN }
          opens := p.read.map fun r => (⟨r.2.1, r.2.2, false, p.firstTree + r.1⟩, .own r.1) } ] :=
  rfl

theorem oracles_fit (p : P2) (h : (codeSwitchKind p : Block S Cl).planOk = true) :
    ∃ e rest, (codeSwitchKind p : Block S Cl).rounds = e :: rest ∧
      ((codeSwitchKind p : Block S Cl).oracles.headD []).length = e.entry.roots := by
  have h' : (Decidable.decide (0 < p.positions) && p.sent.length == p.roots &&
      increasing (p.read.map (·.1)) && Decidable.decide (p.logN ≤ 32)) = true := h
  simp only [Bool.and_eq_true, beq_iff_eq] at h'
  exact ⟨_, _, rounds_two p, h'.1.1.2⟩

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.k2_oracles
#print axioms VerifiableInference.Desc.First.K2.rounds_two
#print axioms VerifiableInference.Desc.First.K2.oracles_fit
