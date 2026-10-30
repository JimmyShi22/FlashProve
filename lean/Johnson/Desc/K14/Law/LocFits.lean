--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/LocFits.lean: how many locations "LOC" is shown, and in which range, BY NAME
from the step's own test on the rounds.

The kind K14's function loc (K14/Text.lean) asks neither: it goes over ALL positions that its one
round has drawn, each taken modulo 2 ^ logN: with fewer positions it would go on in silence. Its
laws (K14/Law/GoodLoc.lean: loc_goodIn, loc_goodIn4; LocSound.lean: locSound) take the number as a
letter or a premise (r.drawn.poss = List.ofFn Q; SendsDraws). The number and the range are asked by
the step in which every block runs (Johnson/Desc/Block.lean: Block.step refuses under the name "the
rounds" where roundsFit says no), against the entry that the block itself declares
(K14/Law/RoundsMake.lean: rounds_of_blocks, entry_loc). Here that is a lemma.
  roundsFit_of_step: a step that says yes has passed roundsFit at the block's own rounds
  loc_round: the fourth block declares one round, with the entry number 1 of the kind's page
  loc_fits: where roundsFit says yes at the fourth block's rounds: there is one round; it drew just
      columns positions, each below 2 ^ logN of the index's code; no element; no matrix entry
  loc_reads: so there is Q : Fin columns → Fin (2 ^ logN) with r.drawn.poss = List.ofFn fun i => (Q
      i).val: the laws' premise; the same of the round as decide is shown it (without the digest)
  loc_reads_of_step: from the fourth block's step's yes
  point_fits, zeta_fits: the like for "LIN point" and "LIN zeta": one round; kCol | kRow elements;
      no position

What is not claimed. That a chain runs its blocks by Block.step: that is the fold's text. Nothing on
how the positions are drawn. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K14.Law.RoundsMake

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params Desc.Plain
open VerifiableInference.Desc (Block roundsFit noDigest)

/-- A step that says yes has passed the test on the rounds. -/
theorem roundsFit_of_step {S Cl : Type} (ft : Nat) (b : Block S Cl) (s : S) (rs : List Fmt.RoundView)
    (cols : List VerifiableInference.Desc.OpenedColumn) (z : S × Nat) (h : b.step ft s rs cols = .ok z) :
    roundsFit b.rounds rs = true := by
  by_contra hf
  have hf' : roundsFit b.rounds rs = false := by simpa using hf
  unfold Block.step at h
  rw [hf'] at h
  cases h

/-- A list whose entries are one entry is one round with that entry. -/
theorem one_round {l : List Fmt.DeclaredRound} {e : Fmt.Entry} (h : l.map (·.entry) = [e]) :
    ∃ d, l = [d] ∧ d.entry = e := by
  rcases l with _ | ⟨d, _ | ⟨d', t⟩⟩
  · cases h
  · exact ⟨d, rfl, (List.cons.inj h).1⟩
  · cases (List.cons.inj h).2

/-- What the test on the rounds says of one declared round. -/
theorem fits_one {d : Fmt.DeclaredRound} {rs : List Fmt.RoundView} (h : roundsFit [d] rs = true) :
    ∃ r, rs = [r] ∧ r.drawn.elems.length = d.entry.drawE ∧ r.drawn.poss.length = d.entry.poss ∧
      r.drawn.trits.length = d.entry.trits ∧ ∀ x ∈ r.drawn.poss, x < 2 ^ d.entry.logN := by
  rcases rs with _ | ⟨r, _ | ⟨r', t⟩⟩
  · cases h
  · simp only [roundsFit, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
    exact ⟨r, rfl, by tauto, by tauto, by tauto, by tauto⟩
  · simp [roundsFit] at h

/-- The fourth block declares one round. -/
theorem loc_round (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    ∃ d, b4.rounds = [d] ∧ d.entry = entryAt P 1 :=
  one_round (rounds_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hb).2.1

/-- **"LOC": the number of the locations and their range, from the step's test by name.** -/
theorem loc_fits (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (rs : List Fmt.RoundView)
    (h : roundsFit b4.rounds rs = true) :
    ∃ r, rs = [r] ∧ r.drawn.poss.length = P.S.fold.columns ∧
      (∀ x ∈ r.drawn.poss, x < 2 ^ P.S.fold.index.code.logN) ∧ r.drawn.elems.length = 0 ∧
      r.drawn.trits.length = 0 := by
  obtain ⟨d, hd, he⟩ := loc_round P b1 b2 b3 b4 b5 b6 b7 b8 hb
  rw [hd] at h
  obtain ⟨r, hr, a1, a2, a3, a4⟩ := fits_one h
  obtain ⟨e1, e2, e3, -, e5⟩ := entry_loc P
  rw [he] at a1 a2 a3 a4
  rw [e1] at a1
  rw [e2] at a2
  rw [e3] at a3
  rw [e5] at a4
  exact ⟨r, hr, a2, a4, a1, a3⟩

/-- **The laws' premise on what is read.** -/
theorem loc_reads (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (rs : List Fmt.RoundView)
    (h : roundsFit b4.rounds rs = true) :
    ∃ (r : Fmt.RoundView) (Q : Fin P.S.fold.columns → Fin (2 ^ P.S.fold.index.code.logN)), rs = [r] ∧
      r.drawn.poss = List.ofFn (fun i => (Q i).val) ∧
      (noDigest r).drawn.poss = List.ofFn (fun i => (Q i).val) := by
  obtain ⟨r, hr, hl, hx, -, -⟩ := loc_fits P b1 b2 b3 b4 b5 b6 b7 b8 hb rs h
  have e : r.drawn.poss = List.ofFn (fun i : Fin P.S.fold.columns =>
      r.drawn.poss[i.val]'(by rw [hl]; exact i.isLt)) := by
    refine List.ext_getElem (by rw [List.length_ofFn, hl]) fun i h1 h2 => ?_
    rw [List.getElem_ofFn]
  refine ⟨r, fun i => ⟨r.drawn.poss[i.val]'(by rw [hl]; exact i.isLt),
    hx _ (List.getElem_mem _)⟩, hr, e, e⟩

/-- From the step's yes. -/
theorem loc_reads_of_step (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (ft : Nat) (s : St)
    (rs : List Fmt.RoundView) (cols : List VerifiableInference.Desc.OpenedColumn) (z : St × Nat)
    (h : b4.step ft s rs cols = .ok z) :
    ∃ (r : Fmt.RoundView) (Q : Fin P.S.fold.columns → Fin (2 ^ P.S.fold.index.code.logN)), rs = [r] ∧
      r.drawn.poss = List.ofFn (fun i => (Q i).val) ∧
      (noDigest r).drawn.poss = List.ofFn (fun i => (Q i).val) :=
  loc_reads P b1 b2 b3 b4 b5 b6 b7 b8 hb rs (roundsFit_of_step ft b4 s rs cols z h)

/-- "LIN point": one round; kCol elements; no position. -/
theorem point_fits (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (rs : List Fmt.RoundView)
    (h : roundsFit b1.rounds rs = true) :
    ∃ r, rs = [r] ∧ r.drawn.elems.length = P.S.kCol ∧ r.drawn.poss.length = 0 := by
  obtain ⟨d, hd, he⟩ := one_round (rounds_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hb).1
  rw [hd] at h
  obtain ⟨r, hr, a1, a2, -, -⟩ := fits_one h
  obtain ⟨e1, e2, -, -, -⟩ := entry_point P
  rw [he, e1] at a1
  rw [he, e2] at a2
  exact ⟨r, hr, a1, a2⟩

/-- "LIN zeta": one round; kRow elements; no position. -/
theorem zeta_fits (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (rs : List Fmt.RoundView)
    (h : roundsFit b7.rounds rs = true) :
    ∃ r, rs = [r] ∧ r.drawn.elems.length = P.S.kRow ∧ r.drawn.poss.length = 0 := by
  obtain ⟨d, hd, he⟩ := one_round (rounds_of_blocks P b1 b2 b3 b4 b5 b6 b7 b8 hb).2.2
  rw [hd] at h
  obtain ⟨r, hr, a1, a2, -, -⟩ := fits_one h
  obtain ⟨e1, e2, -, -, -⟩ := entry_zeta P
  rw [he, e1] at a1
  rw [he, e2] at a2
  exact ⟨r, hr, a1, a2⟩

end Desc.K14.Law
