-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/OwnTieLaw.lean: ownTieOk p = true gives its clauses as propositions (the test:
Johnson/Desc/K12/Law/OwnTie.lean).

Statements and proofs.
Main names:
  `ownTie_of_ok`: where the place's fold sends its own mask, the first written round behind "BAT"
    sends the shape that the first switch's last declared opening has, and that opening's source is
    "own", number free.
  `ownNone_of_ok`: elsewhere that round writes no tree.
Limits: No soundness is claimed, and nothing is said on hiding.
It does not say that the first switch's last opening is the place of the mask's tree in the book
(that D.fresh.t is the last of D.ts there): that is the record's. So DeepK.fresh and DeepK.wide
(Johnson/Desc/K12/Law/K12Lemma.lean), at the letter that takes that round with the message's oracle,
are not yet paid by tests alone.
Every theorem of this file is proved outright; what each rests on is printed at the file's end.

-/
import Johnson.Desc.K12.Law.TieLaw
import Johnson.Desc.K12.Law.OwnTie

set_option autoImplicit false
namespace H2K.First
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (WR writtenOf)

theorem ownTie_of_ok (p : P12) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hs : p.nums.stages = a :: rest) (ho : p.nums.ownMask = true) (h : ownTieOk p = true) :
    ∃ (dE : WR) (o : Fmt.Shape × Fmt.TreeSource), (writtenB p)[0]? = some dE ∧
      (opensOf p a.k).getLast? = some o ∧ dE.tree = some o.1 ∧ o.2 = .own p.nums.free := by
  unfold ownTieOk ownTieOn at h
  rw [hs] at h
  dsimp only at h
  rw [if_pos ho] at h
  split at h
  · rename_i dE o e1 e2
    unfold ok at h
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨dE, o, e1, e2, h.1, h.2⟩
  · simp [ok] at h

theorem ownNone_of_ok (p : P12) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hs : p.nums.stages = a :: rest) (ho : p.nums.ownMask = false) (h : ownTieOk p = true) :
    ∃ dE : WR, (writtenB p)[0]? = some dE ∧ dE.tree = none := by
  unfold ownTieOk ownTieOn at h
  rw [hs] at h
  dsimp only at h
  rw [if_neg (by rw [ho]; decide)] at h
  unfold ok at h
  simp only [List.all_cons, List.all_nil, Bool.and_true, Option.any_eq_true,
      Option.isNone_iff_eq_none] at h
  exact h

end H2K.First
