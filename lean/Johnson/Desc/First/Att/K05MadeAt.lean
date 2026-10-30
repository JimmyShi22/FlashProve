-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05MadeAt.lean: KIND K5 AT THE TABLE OF JOINTS: TWO OF THE THREE PUBLIC ITEMS THAT K5's
ROW MAKES BY OPENING THEIR ITEMS (formsInT m 3 "own" · formsInT m 2 "join") HOLD BEHIND THE HEARING's LAY, at
one filling of the table's letter Mg.pub at formsInT: "every run that the item stands for (the table's own
runsOf) passes formsInT at the generic reader".

Main names:
  `K5FormsFill Mg π m states own`: A FACT ON THE FILLING: Mg.pub (formsInT m k r) (π, s) is the conjunction,
    over runsOf .attention k r, of formsInT (Readers.ofStates states) own · · s. OFFERED: no filling of that
    letter by its own files is known here.
  `RunsReturn A s att hd G`: what is asked to RETURN at the record behind the lay, and of what the lookup on
    the calls left: the seat's reading · "first" · "second" · "keys" · what was heard at the calls, its form
    for the join (no entry; its slots filled in front) · the join is not yet made · joinF.
  `made_own`, `made_join`: the two items.
  `madeForms_of`: **so k5_t2's premise madeForms (Att/K05T2.lean) shrinks to the item at "planes".**
Premises: K5FormsFill · states 2 = runsN A · the hearing's return at a sized ledger · RunsReturn · GeoFits ·
U3There · (for madeForms_of) the item at "planes".
Limits. A RULE OVER LETTERS. RunsReturn is shown at no record here (Att/K05ReturnsLk.lean gives the returns
under its own premises; the lookups' K3Left gives the two facts on the form for the join; "not yet made" is
nobody's yet). U3There: see Att/K05FormsMade.lean. EMPTY AT: a record at which a run refuses.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05JoinThereAt
import Johnson.Desc.First.Att.K05T2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Model.Road
open VerifiableInference.Desc.First (Pub Meaning runsOf)
open VerifiableInference.Desc.K9 (Readers formsInT RunOf)

/-- A fact on the filling of the table's letter at formsInT. -/
structure K5FormsFill {Pp W : Type} (Mg : Meaning Pp W) (π : Pp) (m : ℕ)
    (states : ℕ → List (RunOf First.S)) (own : List (ℕ × ℕ)) : Prop where
  forms : ∀ k r s, Mg.pub (.formsInT m k r) (π, s) =
    (runsOf .attention k r).all fun x => formsInT (Readers.ofStates states) own x.1 x.2 s

/-- What is asked to return at the record behind the lay, and of what the lookup on the calls left. -/
def RunsReturn (A : Attention.Plan) (s : First.S) (att : First.AttOwn) (hd : Heard) (G : Fork) : Prop :=
  ∃ (i : Runs.In) (K : ℕ) (l₁ l₂ : List Aff) (j : Runs.JoinsP) (kf : Array Aff) (gL : Forest.Heard)
    (y : Aff × Fork × OnBytes.K.Kc.Tape),
    inOf (seatCO (parCOf A)) (parCOf A) (behind s att hd G) = some (i, K) ∧
    Runs.firstRun i K = some (l₁, j) ∧ Runs.secondRun i K = some l₂ ∧
    keysOfK (seatCO (parCOf A)) (parCOf A) (behind s att hd G) = some kf ∧
    att.lookHeard = some gL ∧ gL.cEnd.ents = #[] ∧ Fo.FilledA att.F gL.cEnd ∧
    K3.unpaid G gL.owedJoin = true ∧ Look.joinF gL kf G [] = some y

section
variable {Pp W : Type} {Mg : Meaning Pp W} {π : Pp} {m : ℕ} {states : ℕ → List (RunOf First.S)}
  {own : List (ℕ × ℕ)} {A : Attention.Plan} {s : First.S} {att : First.AttOwn}
  {x : Params.AttentionRounds} {rs : List Fmt.RoundView} {hd : Heard} {G : Fork}

theorem made_own (Ff : K5FormsFill Mg π m states own) (hst : states 2 = runsN A)
    (hh : hear x (att.F, rs, 0) = some (hd, G, [], 0)) (hz : Sized att.F)
    (Rt : RunsReturn A s att hd G) (gf : GeoFits (parCOf A).geo x) (U : U3There own s att (parCOf A)) :
    Mg.pub (.formsInT m 3 "own") (π, behind s att hd G) = true := by
  obtain ⟨i, K, l₁, l₂, j, kf, _, _, hin, h1, h2, hk, _⟩ := Rt
  have h := formsInT_own_behind states A hst own hh hz hin h1 h2 hk gf U
  rw [Ff.forms]
  show ([(2, "first"), (2, "keys"), (2, "second")].all fun x =>
    formsInT (Readers.ofStates states) own x.1 x.2 (behind s att hd G)) = true
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  exact ⟨h "first" (by simp), h "keys" (by simp), h "second" (by simp)⟩

theorem made_join (Ff : K5FormsFill Mg π m states own) (hst : states 2 = runsN A)
    (hh : hear x (att.F, rs, 0) = some (hd, G, [], 0)) (hz : Sized att.F)
    (Rt : RunsReturn A s att hd G) (gf : GeoFits (parCOf A).geo x) (U : U3There own s att (parCOf A)) :
    Mg.pub (.formsInT m 2 "join") (π, behind s att hd G) = true := by
  obtain ⟨i, K, l₁, l₂, j, kf, gL, y, hin, h1, _, hk, hg, hcE, hcF, hun, hj⟩ := Rt
  have h := formsInT_join_behind states A hst own hh hz hin h1 hk gf U hg hcE hcF hun hj
  rw [Ff.forms]
  show ([(2, "join")].all fun x =>
    formsInT (Readers.ofStates states) own x.1 x.2 (behind s att hd G)) = true
  simp only [List.all_cons, List.all_nil, Bool.and_true]
  exact h

/-- **k5_t2's premise madeForms shrinks to the item at "planes".** -/
theorem madeForms_of (Ff : K5FormsFill Mg π m states own) (hst : states 2 = runsN A)
    (hh : hear x (att.F, rs, 0) = some (hd, G, [], 0)) (hz : Sized att.F)
    (Rt : RunsReturn A s att hd G) (gf : GeoFits (parCOf A).geo x) (U : U3There own s att (parCOf A))
    (hplanes : Mg.pub (.formsInT m 2 "planes") (π, behind s att hd G) = true) :
    ∀ q ∈ [Pub.formsInT m 3 "own", Pub.formsInT m 2 "planes", Pub.formsInT m 2 "join"],
      Mg.pub q (π, behind s att hd G) = true := by
  intro q hq
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact made_own Ff hst hh hz Rt gf U
  · exact hplanes
  · exact made_join Ff hst hh hz Rt gf U

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.made_own
#print axioms VerifiableInference.Desc.First.Att.P.made_join
#print axioms VerifiableInference.Desc.First.Att.P.madeForms_of
