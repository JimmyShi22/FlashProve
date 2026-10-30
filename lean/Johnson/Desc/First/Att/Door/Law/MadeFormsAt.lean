-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
-- Johnson/Desc/First/Att/Door/Law/MadeFormsAt.lean: KIND K5: K5AtMg's FIELD madeForms (Johnson/Desc/First/Att/K05AtMg.lean: the public tests tied to the three items that the block's row opens hold behind the lay) AT ANY MEANING Mg WITH Mg.pub = pubAll D base (mgAll_pub, Johnson/Desc/Sound/MgAll.lean, := rfl; the halves with code). Mathlib beneath.
-- BY: formsInT_mono (the test reads of the readers one answer: where "the run itself" answers, and the link's readers give that answer too, the test passes from the one to the other) · the kind's own formsInT_own_behind | formsInT_join_behind (Johnson/Desc/First/Att/K05FormsMadeAt.lean | K05JoinThereAt.lean).
-- WHAT IS LEFT, EACH WITH ITS OWNER: hr3 | hrJ (the composed meaning's letter runs at (m, 3, "own") and (m, 2, "join"): Johnson/Desc/Sound/MgAt/Runs.lean) · hRds (an implication, NOT an equation between two structures of readers; hRds_of_link pays it at the composed meaning's readers of the link) · hst (block 2 states the kind's four runs) · gf (public: the plan's geometry fits) · UNDER THE FIELD's OWN GUARDS: hU (the array of the reads is there: from the kind's item K5.readsThere) · hRt (the four runs return at the state behind the lay, and three facts on what was received from the lookup argument) · hplanes (the lookup argument's run "planes": the test at the state behind the lay): THE LOOKUPS' FILES WITH K5's.
import Johnson.Desc.First.PubAllAt
import Johnson.Desc.First.Att.K05MadeAt
import Johnson.Desc.First.Att.K05T2

set_option autoImplicit false

namespace H2K5.Door
open OnBytes OnBytes.Model OnBytes.Model.Road
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K9 (Readers Read RunOf readerOf formsInT)
open VerifiableInference.Desc.First.Att.P (behind hear Heard onAt_pub fork_front sized_of_B RunsReturn GeoFits U3There parCOf runsN
  formsInT_own_behind formsInT_join_behind)

/-- The test passes from readers to readers that give the same answer wherever the first answer. -/
theorem formsInT_mono {Rd Rd' : Readers} (own : List (Nat × Nat)) (k : Nat) (r : String) (s : S)
    (h : ∀ R, Rd.forms k r s = some R → Rd'.forms k r s = some R) (hv : formsInT Rd own k r s = true) :
    formsInT Rd' own k r s = true := by
  unfold formsInT at hv ⊢
  cases hq : Rd.forms k r s with
  | none =>
    rw [hq] at hv
    cases hs : K9.segAt? s <;> rw [hs] at hv <;> cases hv
  | some R =>
    rw [h R hq]
    rw [hq] at hv
    exact hv

theorem madeForms_at {Pp W : Type} (D : PubData) (base : Pub → Pp × S → Bool) (Mg : Meaning Pp W) (hpub : Mg.pub = pubAll D base)
    (N : Numbers) (links : List ModelPart) (pl : Place) (O : List Item) (Q : List Pub) (Fr : Frame) (m : Nat)
    (own : Params.AttentionRounds) (A : Attention.Plan) (states : Nat → List (RunOf S)) (hled : Pub.ledger m ∈ Q)
    (hr3 : D.runs m 3 "own" = [(2, "first"), (2, "keys"), (2, "second")]) (hrJ : D.runs m 2 "join" = [(2, "join")])
    (hRds : ∀ (name : String) (s : S) (R : Read), (name == "K8.equations") = false →
      readerOf states 2 name s = some R → (D.Rd m).forms 2 name s = some R)
    (hst : states 2 = runsN A) (gf : GeoFits (parCOf A).geo own)
    (hU : ∀ π : Pp, ∀ (s : S) (y : Fr.E.Str) (att : AttOwn), onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) →
      s.failed = none → s.here = .att att → U3There (D.N.sent m 0) s att (parCOf A))
    (hRt : ∀ π : Pp, ∀ (s : S) (y : Fr.E.Str) (att : AttOwn) (hd : Heard) (G : Fork) (rs : List Fmt.RoundView),
      onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none → s.here = .att att →
      hear own (att.F, rs, 0) = some (hd, G, [], 0) → RunsReturn A s att hd G)
    (hplanes : ∀ π : Pp, ∀ (s : S) (y : Fr.E.Str) (att : AttOwn) (hd : Heard) (G : Fork) (rs : List Fmt.RoundView),
      onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none → s.here = .att att →
      hear own (att.F, rs, 0) = some (hd, G, [], 0) → Mg.pub (.formsInT m 2 "planes") (π, behind s att hd G) = true) :
    ∀ π : Pp, ∀ (s : S) (y : Fr.E.Str) (att : AttOwn) (hd : Heard) (G : Fork) (rs : List Fmt.RoundView),
      onAt N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none → s.here = .att att →
      hear own (att.F, rs, 0) = some (hd, G, [], 0) →
      ∀ q ∈ [Pub.formsInT m 3 "own", Pub.formsInT m 2 "planes", Pub.formsInT m 2 "join"],
        Mg.pub q (π, behind s att hd G) = true := by
  intro π s y att hd G rs hon hu e hh q hq
  have hz : s.fork?.any K3.sizedB = true := by
    have := onAt_pub hon hu _ hled
    rwa [hpub] at this
  rw [fork_front e] at hz
  have zz := sized_of_B hz
  have U := hU π s y att hon hu e
  obtain ⟨i, K, l₁, l₂, j, kf, gL, yj, hin, h1, h2, hk, hg, hcE, hcF, hun, hj⟩ := hRt π s y att hd G rs hon hu e hh
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · have h := formsInT_own_behind states A hst (D.N.sent m 0) hh zz hin h1 h2 hk gf U
    rw [hpub, pubAll_formsInT, hr3]
    simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
    exact ⟨formsInT_mono _ 2 "first" _ (fun R => hRds "first" _ R (by decide)) (h "first" (by simp)),
      formsInT_mono _ 2 "keys" _ (fun R => hRds "keys" _ R (by decide)) (h "keys" (by simp)),
      formsInT_mono _ 2 "second" _ (fun R => hRds "second" _ R (by decide)) (h "second" (by simp))⟩
  · exact hplanes π s y att hd G rs hon hu e hh
  · have h := formsInT_join_behind states A hst (D.N.sent m 0) hh zz hin h1 hk gf U hg hcE hcF hun hj
    rw [hpub, pubAll_formsInT, hrJ]
    simp only [List.all_cons, List.all_nil, Bool.and_true]
    exact formsInT_mono _ 2 "join" _ (fun R => hRds "join" _ R (by decide)) h

#print axioms formsInT_mono
#print axioms madeForms_at

end H2K5.Door
