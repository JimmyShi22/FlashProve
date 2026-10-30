-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ground/Shape/ClaimsMarks.lean: THE MARK ON THE CONSTRAINTS THAT LIE OPEN (`claimsAtB`,
Johnson/Desc/Ground/Shape/Claims.lean) IS KEPT BY THE ADMITTING AND BY THE COPYING OF A SAMPLE AT A
TIDY STATEMENT, WITH NO FURTHER PREMISE. Claims.lean keeps the mark at these two functions under
"the message that is written is no member of the group". Here that premise is paid by the mark
`stTidyB` (the statement is tidy: Johnson/Desc/Ground/Shape/Marks.lean) and the function's own
accept. No statement here names a kind, a chain or a frame for an honest side. A word, as in
Claims.lean: a constraint that lies open is what the library's clauses' names call an open row.

Main names. `sampled_of_tidy`: at a tidy statement every member of every group is sampled
(`membersSampledS` at the statement's shape). `admit_unsampled`, `elsewhere_unsampled`: where the
function accepts, the message that it writes was not sampled (as the test reads it: a message that
is not there counts as not sampled too). `admit_noMember`, `elsewhere_noMember`: so, at a tidy
statement, it is no member of any group. **`admit_claims_tidy`, `elsewhere_claims_tidy`: at a tidy
statement, where the function accepts, the mark is kept at every group.**

By what. `Tidy.members` (Johnson/Desc/Means/Walk.lean, Johnson/Desc/Means/Entry.lean); the clauses
"not sampled before" and "not sampled here" of the two functions' guards
(Johnson/Desc/First/Base/Ground.lean); `notMember_of_sampled`, `admit_claims`, `elsewhere_claims`
(Claims.lean).

Limits. That both marks, `stTidyB` and `claimsAtB`, go along any run of the ground's thirteen plain
functions, under what Marks.lean asks of the arguments, IS A READING OF LAWS, ONE FOR EACH FUNCTION
AND EACH MARK; THEY ARE JOINED IN NO THEOREM. For `claimsAtB`: Claims.lean's `X_claims` at eleven of
the thirteen, and the two laws here. For `stTidyB`: Marks.lean's `X_tidy` at eleven of the thirteen.
At the other two, the adding of constraints (`addRowsP`) and the taking of mask entries
(`takeMasksP`), the library has the like for `Tidy` itself (`GroundQuiet.addRows`,
`GroundQuiet.takeMasks`, Johnson/Desc/GroundQuiet.lean, at `groundQuiet_tidy`,
Johnson/Desc/Tidy/Stay.lean); laws at these two in the form of `stTidyB` stand in a file that is not
part of this library. Texts of the library that write a statement by themselves are not served.
Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.Ground.Shape.Claims
import Johnson.Desc.Ground.Shape.Marks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Ground.Sh
open OnBytes OnBytes.Slice OnBytes.Means Desc.Plain
open VerifiableInference.Desc VerifiableInference.Desc.Ground

variable {L : Type}

/-- At a tidy statement every member of every group is sampled. -/
theorem sampled_of_tidy {S : Statement} (h : stTidyB S = true) (g : Nat) :
    membersSampledS (stSh S) g = true := by
  have hm := (tidy_of h).members
  unfold membersSampledS
  rw [grp_get]
  cases hG : S.groups[g]? with
  | none => rfl
  | some G =>
    show (G.members.toList.all fun o => ((stSh S).oracles[o]?).any (·.sampled)) = true
    refine List.all_eq_true.2 fun o ho => ?_
    obtain ⟨x, hx, hs⟩ := hm g G hG o ho
    rw [orc_get, hx]
    exact hs

/-- Where the admitting accepts, the message was not sampled. The conclusion is the test's own form:
it holds also of a message that is not there. -/
theorem admit_unsampled (d d' : DState L) (o : Nat) (rows : Array OnBytes.Row)
    (h : admitP d o rows = some d') : ((stSh d.st).oracles[o]?).any (·.sampled) = false := by
  unfold admitP at h
  split at h
  · rename_i hok
    obtain ⟨x, hx, _⟩ := Option.bind_eq_some_iff.1 h
    simp only [Ground.ok, admitL, hx, List.all_cons, List.all_nil, Ground.has, Option.map_some,
      Option.getD_some, Bool.and_eq_true, Bool.not_eq_true'] at hok
    rw [orc_get, hx]
    exact hok.2.2.1
  · cases h

/-- Where the copying of a sample accepts, the message here was not sampled. The conclusion is the
test's own form: it holds also of a message that is not there. -/
theorem elsewhere_unsampled (d d' : DState L) (mine : Nat) (other : Statement) (theirs : Nat)
    (h : elsewhereP d mine other theirs = some d') :
    ((stSh d.st).oracles[mine]?).any (·.sampled) = false := by
  unfold elsewhereP at h
  split at h
  · rename_i hok
    rw [orc_get]
    cases hx : d.st.oracles[mine]? with
    | none => rfl
    | some x =>
      have h4 := List.all_eq_true.1 hok
        ("elsewhere: not sampled here", has d.st.oracles[mine]? (!·.sampled)) (by simp [elsewhereL])
      rw [hx] at h4
      simpa [Ground.has] using h4
  · cases h

/-- At a tidy statement, where the admitting accepts, its message is no member of any group. -/
theorem admit_noMember (d d' : DState L) (o : Nat) (rows : Array OnBytes.Row)
    (h : admitP d o rows = some d') (ht : stTidyB d.st = true) (g : Nat) :
    ∀ G : GrpSh, (stSh d.st).groups[g]? = some G → o ∉ G.members :=
  notMember_of_sampled (sampled_of_tidy ht g) (admit_unsampled d d' o rows h)

/-- At a tidy statement, where the copying of a sample accepts, its message here (mine) is no member
of any group. -/
theorem elsewhere_noMember (d d' : DState L) (mine : Nat) (other : Statement) (theirs : Nat)
    (h : elsewhereP d mine other theirs = some d') (ht : stTidyB d.st = true) (g : Nat) :
    ∀ G : GrpSh, (stSh d.st).groups[g]? = some G → mine ∉ G.members :=
  notMember_of_sampled (sampled_of_tidy ht g) (elsewhere_unsampled d d' mine other theirs h)

/-- **The admitting keeps the mark on the constraints that lie open, at a tidy statement**: where it
accepts, at every group. -/
theorem admit_claims_tidy (d d' : DState L) (o : Nat) (rows : Array OnBytes.Row)
    (h : admitP d o rows = some d') (ht : stTidyB d.st = true) (g : Nat)
    (hc : claimsAtB d.st g = true) : claimsAtB d'.st g = true :=
  admit_claims d d' o rows h g (admit_noMember d d' o rows h ht g) hc

/-- **The copying of a sample keeps it, at a tidy statement**: where it accepts, at every group. -/
theorem elsewhere_claims_tidy (d d' : DState L) (mine : Nat) (other : Statement) (theirs : Nat)
    (h : elsewhereP d mine other theirs = some d') (ht : stTidyB d.st = true) (g : Nat)
    (hc : claimsAtB d.st g = true) : claimsAtB d'.st g = true :=
  elsewhere_claims d d' mine other theirs h g (elsewhere_noMember d d' mine other theirs h ht g) hc

end VerifiableInference.Desc.Ground.Sh

#print axioms VerifiableInference.Desc.Ground.Sh.sampled_of_tidy
#print axioms VerifiableInference.Desc.Ground.Sh.admit_unsampled
#print axioms VerifiableInference.Desc.Ground.Sh.elsewhere_unsampled
#print axioms VerifiableInference.Desc.Ground.Sh.admit_noMember
#print axioms VerifiableInference.Desc.Ground.Sh.elsewhere_noMember
#print axioms VerifiableInference.Desc.Ground.Sh.admit_claims_tidy
#print axioms VerifiableInference.Desc.Ground.Sh.elsewhere_claims_tidy
