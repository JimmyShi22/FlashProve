-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/BodyHelps.lean: SMALL LAWS ON bodyAll's PIECES
(Johnson/Prover/Link/BodyAll.lean), for the step of the induction. Statements and proofs; each is an
unfolding.

  sentOf_noDigest, drawnOf_noDigest, shows_noDigest   a round without its sealed digest shows and
                    drew the same: so fold_V's premises hold at the rounds as a part is shown them
  rowOf_claim       the row of a record that passes a claim on
  mem_groupAt       a column of groupAt stands at a position of the tree's range and is col there
  mem_keyed_group   so for the columns with their keys (keyed, Johnson/Desc/K12/Join.lean): the form
                    of the premise hcols of hy_stage | hy_first | switch_law
  ansAt_fit         where the two stages fit, ansAt is gAns

Not shown here. Nothing on a decision; nothing on soundness; nothing on what any value that is sent
discloses or does not disclose.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.BodyAll
import Fmt.Rules6Laws

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12

theorem sentOf_noDigest (r : Fmt.RoundView) : sentOf (noDigest r) = sentOf r := rfl
theorem drawnOf_noDigest (r : Fmt.RoundView) : drawnOf (noDigest r) = drawnOf r := rfl

theorem shows_noDigest : ∀ (k : ℕ) (rs : List Fmt.RoundView) (q : RIdx (sVars GE 2 k) → GE)
    (γ : HPt (sVars GE 2 k)), Shows k rs q γ → Shows k (rs.map noDigest) q γ
  | 0, [], _, _, _ => trivial
  | k + 1, _ :: rs, _, γ, h => ⟨h.1, h.2.1, h.2.2.1, shows_noDigest k rs _ γ.2 h.2.2.2⟩
  | 0, _ :: _, _, _, h => h.elim
  | _ + 1, [], _, _, h => h.elim

theorem map_drawnOf_noDigest (rs : List Fmt.RoundView) :
    (rs.map noDigest).map drawnOf = rs.map drawnOf := by
  rw [List.map_map]
  rfl

theorem rowOf_claim {t : T12} {row : GroupRow} {L : GroupLayout} (h : t.pass = .claim row L) :
    rowOf t = row := by
  unfold rowOf
  rw [h]

theorem mem_groupAt (a : ℕ) (poss : List ℕ) (col : ℕ → List UInt64) (c : ℕ × List UInt64)
    (h : c ∈ groupAt a poss col) : c.1 < 2 ^ a ∧ c.2 = col c.1 := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 h
  obtain ⟨y, _, rfl⟩ := List.mem_map.1 ((Fmt.listOf_mem _ _).1 hx)
  exact ⟨Nat.mod_lt _ (Nat.pos_of_ne_zero (by positivity)), rfl⟩

theorem mem_keyed_group (p : P12) (cut : List Fmt.DeclaredRound) (a : ℕ) (poss : List ℕ)
    (col : ℕ → List UInt64) (c : ℕ × ℕ × List UInt64)
    (h : c ∈ keyed p cut [groupAt a poss col]) : c.2.1 < 2 ^ a ∧ c.2.2 = col c.2.1 := by
  obtain ⟨x, hx, hc⟩ := List.mem_flatMap.1 h
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hc
  have hx2 : x.2 = groupAt a poss col := List.mem_singleton.1 (List.of_mem_zip hx).2
  rw [hx2] at hy
  exact mem_groupAt a poss col y hy

theorem ansAt_fit {s s' : Sg} (hf : CsFit s s') (μ' : s.cMid.J → GE) (tl : s.cMid.Q → GE)
    (fr : ℕ → GE) (els : List E) (bits : ℕ) :
    ansAt s s' μ' tl fr els bits =
      gAns hf μ' tl fr (readP _ (els.take bits), unitOf (readE (els.getD bits zeroE))) :=
  dif_pos hf

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.shows_noDigest
#print axioms Johnson.Prover.Link.map_drawnOf_noDigest
#print axioms Johnson.Prover.Link.rowOf_claim
#print axioms Johnson.Prover.Link.mem_groupAt
#print axioms Johnson.Prover.Link.mem_keyed_group
#print axioms Johnson.Prover.Link.ansAt_fit
