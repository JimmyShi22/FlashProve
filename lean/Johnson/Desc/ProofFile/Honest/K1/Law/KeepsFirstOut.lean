-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/KeepsFirstOut.lean: the kind K1's first segment's opening
(K1.firstSegmentOpening, Johnson/Desc/K1/First.lean) and the groups of the statement: which message is a member
of no group behind its return. Statements and proofs, over the library's read-out of what the
opening does to the groups (K1.Opened, K1.firstAtS_group, Johnson/Desc/K1/Law/GroupAtRecord.lean)
and Johnson/Desc/ProofFile/Honest/K1/Law/Keeps.lean. It imports files of the sealed library alone
beside that.

  first_two_rounds: a return of the opening's decision has two rounds.
  outOf_opened: where one group is opened whose members are the numbers from the statement's size
    on, own of them: a number outside that range that is a member of no group is a member of none
    behind.
  k1_first_out: K1Out at the opening: no group gains a message that is there. It stands BESIDE
    K1FirstKeeps, which does not hold it.
  k1_first_last_out: THE LAST MESSAGE THAT THE OPENING SENDS IS A MEMBER OF NO GROUP BEHIND, where
    no group in front names its number.
  k1_first_groups: every older group is as it was, whole: its open rows too.

Not shown here. ONE WAY, FROM A RETURN of the opening by itself: in a chain a further step without a
round is joined behind it (K1.openingZero, Johnson/Desc/K1/Law/OpeningZero.lean): nothing is said of
that step. k1_first_last_out's premise speaks of a number that is not yet in the statement: it is a
premise on the GROUPS in front: that no group names that number: it is not shown here (where there
is no group in front it holds). That the last message is the index masks' message is not said here
(K1.firstAtS_im, Johnson/Desc/K1/Law/FirstIndexMasks.lean, says which number the test behind finds).
Nothing on soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.ProofFile.Honest.K1.Law.Keeps
import Johnson.Desc.K1.Law.GroupAtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Model
open VerifiableInference.Desc (K1.firstSegmentOpening K1.firstPar)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K1 (OutOf Opened)

variable {Cl : Type}

/-- A return of the opening's decision has two rounds. -/
theorem first_two_rounds {q : Params.First} {gp : _root_.Desc.Plain.GPar} {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (K1.firstSegmentOpening (Cl := Cl) q gp).decide s rs gs = .ok s') : ∃ r₁ r₂, rs = [r₁, r₂] := by
  unfold K1.firstSegmentOpening at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := VerifiableInference.Desc.Keeps.ebind_ok h
  obtain ⟨⟨c, d'⟩, h2, -⟩ := VerifiableInference.Desc.Keeps.ebind_ok h
  obtain ⟨g, d₁, ids, d₂, -, h4, -⟩ := VerifiableInference.Desc.K1.firstOwn_ok _ _ _ _ _ _ _ h2
  match rs, h4 with
  | [r₁, r₂], _ => exact ⟨r₁, r₂, rfl⟩
  | [], h4 => cases h4
  | [_], h4 => cases h4
  | _ :: _ :: _ :: _, h4 => cases h4

/-- **A number outside the new group's range that is a member of no group is a member of none
behind.** -/
theorem outOf_opened {st st' : Statement} {own i : Nat} (O : Opened st own st') (hO : OutOf i st)
    (hi : ¬ (st.oracles.size ≤ i ∧ i < st.oracles.size + own)) : OutOf i st' := by
  intro G' hG' hmem
  obtain ⟨j, hj⟩ := Array.mem_iff_getElem?.1 hG'
  have hlt : j < st'.groups.size := (Array.getElem?_eq_some_iff.1 hj).1
  rw [O.size] at hlt
  by_cases hjo : j < st.groups.size
  · rw [O.older j hjo] at hj
    exact hO G' (Array.mem_iff_getElem?.2 ⟨j, hj⟩) hmem
  · obtain rfl : j = st.groups.size := by omega
    obtain ⟨G, hG, -, -, hm⟩ := O.made
    obtain rfl : G = G' := Option.some.inj (hG.symm.trans hj)
    exact hi ((hm i).1 (Array.mem_toList_iff.2 hmem))

/-- **K1Out at the opening**: no group gains a message that is there. -/
theorem k1_first_out {q : Params.First} {gp : _root_.Desc.Plain.GPar} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : (K1.firstSegmentOpening (Cl := Cl) q gp).decide s rs gs = .ok s') : K1Out s s' := by
  obtain ⟨r₁, r₂, rfl⟩ := first_two_rounds h
  exact fun i hi hO => outOf_opened
    (VerifiableInference.Desc.K1.firstAtS_group q gp s s' r₁ r₂ gs h).1 hO (by omega)

/-- **THE LAST MESSAGE THAT THE OPENING SENDS IS A MEMBER OF NO GROUP BEHIND**, where no group in
front names its number. -/
theorem k1_first_last_out {q : Params.First} {gp : _root_.Desc.Plain.GPar} {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (K1.firstSegmentOpening (Cl := Cl) q gp).decide s rs gs = .ok s')
    (hO : OutOf (s.st.oracles.size + ((K1.firstPar q gp).sent.size - 1)) s.st) :
    OutOf (s.st.oracles.size + ((K1.firstPar q gp).sent.size - 1)) s'.st := by
  obtain ⟨r₁, r₂, rfl⟩ := first_two_rounds h
  obtain ⟨O, -, hlt⟩ := VerifiableInference.Desc.K1.firstAtS_group q gp s s' r₁ r₂ gs h
  exact outOf_opened O hO (by omega)

/-- **Every older group is as it was, whole.** -/
theorem k1_first_groups {q : Params.First} {gp : _root_.Desc.Plain.GPar} {s s' : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (h : (K1.firstSegmentOpening (Cl := Cl) q gp).decide s rs gs = .ok s') :
    ∀ j, j < s.st.groups.size → s'.st.groups[j]? = s.st.groups[j]? := by
  obtain ⟨r₁, r₂, rfl⟩ := first_two_rounds h
  exact (VerifiableInference.Desc.K1.firstAtS_group q gp s s' r₁ r₂ gs h).1.older

end ProofFile.Honest.K1
