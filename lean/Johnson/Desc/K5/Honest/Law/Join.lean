-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/Join.lean: CONDITIONAL: the frame of the sentence "the form that the run
"join" gathers is worth 0, with each entry of the array of the segment's tables read as the stated
function of the committed cells" (`formsTQ`, Johnson/Desc/Sound/FormsQ.lean), at the verifier's
state just behind the lay of an attention segment's own rounds. The run is the lookup's; it is run
on the segment's four key forms. A joining of the library's lemmas; no algebra is in this file.

The sentence has five clauses: the open segment's part is there; the reader returns the run's
forms; its late slots pass a test; each form passes a public test; each form is worth 0. The first
four are paid by the library's laws on the state behind the lay. The fifth is cut in two. This
side's half: each key form is worth the extension of its call's vector of looked-up values
(`kf_is_ext`, Johnson/Desc/K5/Honest/Law/Keys.lean). The lookup's half is a named premise,
`JoinMeets`: with these four extensions in the key forms' place, the library's left side of the
join (`joinVal`, Cb/Pv/Att/End/Join.lean), at the letters read off what the lookup heard and at the
worth of the form that the lookup left, is 0.

Main names:
  `join_value`      the gathered form is worth `joinVal` at the key forms' worths
  `JoinMeets`       the lookup's half, a premise
  `join_zero`       the gathered form is worth 0, from the two halves
  `join_of_zero`    the sentence, from "the gathered form is worth 0"
  `join_of_runs`    **the sentence, with the runs' returns taken from the library's `RunsReturn`**
                    (Johnson/Desc/First/Att/K05MadeAt.lean)

THE PREMISES OF `join_of_runs`: those of `own_of_runs` (Johnson/Desc/K5/Honest/Law/Own.lean) but
what the claims say; and h0: whatever form the lookup's text returns on the key forms at the state
is worth 0 in the sentence's world: `join_zero` gives that from `kf_is_ext`'s premises and
`JoinMeets`.
TWO FIELDS OF THE OPEN SEGMENT hold what the lookup left: the run "join" reads `lookHeard`; the
claims' reading, and so the key points in `kf_is_ext`, read `g`. They are different fields, and no
statement here ties them. Who joins `kf_is_ext` with `join_zero` needs that the two agree in the key
points. The library's `FrontAll` (Johnson/Desc/First/Att/K05BehindWorth.lean) has that `g` agrees in
five fields, the key points among them (`SeatReadsSame`, Johnson/Desc/First/Att/K05SameRead.lean),
with a letter of its own. Under the library's list of tests in front of the block (`DoorYes`,
Johnson/Desc/First/Att/K05DoorYes.lean) that letter is what `lookHeard` holds (its field `heard`;
`frontAll_of_door`, Johnson/Desc/First/Att/K05FrontOfDoor.lean, hands the same letter on). The
letters of the join and the form that the lookup left are read off `lookHeard` alone.
Limits. `JoinMeets` is shown nowhere here. It is not the table's item on the lookup's key vectors as
that item is written: to draw it from that item one needs rounds for which the lookup's heard values
stand, the worth of the form that the lookup left, and that the item's key vectors are those on the
cells t; none of these is looked at here. Johnson/Desc/K5/Honest/Law/JoinMeetsAtHead.lean draws it
under premises; the third of these needs stays one of them (hKv: the item's key vectors are kvec, a
free letter). That any premise is met at a state of an honest run is not shown here. No property is
claimed by a definition.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05JoinThereAt
import Johnson.Desc.K5.Honest.Law.Keys
import Johnson.Desc.K5.Honest.Law.Own

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model OnBytes.Model.Road
open OnBytes.Road (Numerals)
open VerifiableInference.Desc (First.S First.AttOwn)
open VerifiableInference.Desc.First
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (behind hear runsN GeoFits U3There RunsReturn)
open VerifiableInference.Desc.K9 (Read Readers readerOf)
open VerifiableInference.Desc.Sound (GQ Stated formsTQ MsgQ)
open Cb.Pv.Att.End (joinVal)
open K5Law (qAt)

/-! ## The value -/

section Value
variable {K : Type} [Field K] {ρ : Reading K} {W : World K}

/-- **The gathered form is worth the library's left side of the join at the key forms' worths.** -/
theorem join_value (N : Numerals ρ) {gL : Forest.Heard} {kf : Array Aff} {F : Fork}
    {t : OnBytes.K.Kc.Tape} {y : Aff × Fork × OnBytes.K.Kc.Tape}
    (hj : Look.joinF gL kf F t = some y) (h4 : kf.size = 4) :
    y.1.value ρ W = joinVal (qAt ρ gL)
      (fun c => (kf.getD c.val (Aff.ofConst zeroE)).value ρ W) (gL.cEnd.value ρ W) := by
  rw [(K5Law.joinF_is hj).1]
  exact K5Law.joinW_val N gL kf h4

/-- **The lookup's half**: with the values kv in the key forms' place, the left side of the join, at
the letters read off what the lookup heard and at the worth of the form that the lookup left, is
0. -/
def JoinMeets (ρ : Reading K) (W : World K) (gL : Forest.Heard) (kv : Fin 4 → K) : Prop :=
  joinVal (qAt ρ gL) kv (gL.cEnd.value ρ W) = 0

/-- **The gathered form is worth 0**, from the two halves. -/
theorem join_zero (N : Numerals ρ) {gL : Forest.Heard} {kf : Array Aff} {F : Fork}
    {t : OnBytes.K.Kc.Tape} {y : Aff × Fork × OnBytes.K.Kc.Tape}
    (hj : Look.joinF gL kf F t = some y) {kv : Fin 4 → K}
    (hk : kf.size = 4 ∧ ∀ c : Fin 4, (kf.getD c.val (Aff.ofConst zeroE)).value ρ W = kv c)
    (hm : JoinMeets ρ W gL kv) : y.1.value ρ W = 0 := by
  rw [join_value N hj hk.1, show (fun c : Fin 4 =>
    (kf.getD c.val (Aff.ofConst zeroE)).value ρ W) = kv from funext hk.2]
  exact hm

end Value

/-! ## The frame -/

section
variable {s : First.S} {a : First.AttOwn} {x : Params.AttentionRounds} {rs : List Fmt.RoundView}
  {h : P.Heard} {G : Fork} {i : P.Runs.In} {n : ℕ}

/-- **The sentence, from "the gathered form is worth 0".** Conditional; the premises are those
listed in the file's head, with the runs' returns written out, and h0. -/
theorem join_of_zero (Rd : Readers) (St : Stated) (A : Attention.Plan) (own : List (ℕ × ℕ))
    (hRd : ∀ (name : String) (R : Read), (name == "K8.equations") = false →
      readerOf (fun _ => runsN A) 2 name (behind s a h G) = some R →
      Rd.forms 2 name (behind s a h G) = some R)
    (hh : hear x (a.F, rs, 0) = some (h, G, [], 0)) (hz : OnBytes.Model.Road.Sized a.F)
    (hin : P.inOf (P.seatCO (P.parCOf A)) (P.parCOf A) (behind s a h G) = some (i, n))
    {l₁ : List Aff} {j : P.Runs.JoinsP} (h1 : P.Runs.firstRun i n = some (l₁, j))
    {kf : Array Aff}
    (hk : P.keysOfK (P.seatCO (P.parCOf A)) (P.parCOf A) (behind s a h G) = some kf)
    (gf : GeoFits (P.parCOf A).geo x) (U : U3There own s a (P.parCOf A)) {gL : Forest.Heard}
    (hg : a.lookHeard = some gL) (hcE : gL.cEnd.ents = #[]) (hcF : Fo.FilledA a.F gL.cEnd)
    (hun : VerifiableInference.Desc.K3.unpaid G gL.owedJoin = true)
    {y : Aff × Fork × OnBytes.K.Kc.Tape}
    (hj : Look.joinF gL kf G [] = some y) (rd : ℕ × ℕ → MsgQ)
    (h0 : y.1.value Reading.gl (worldBehind St own s a h G rd) = 0) :
    formsTQ Rd St own 2 "join" (behind s a h G) rd := by
  obtain ⟨k3, hk3⟩ := P.keys_parts hin h1 hk
  have hT := P.k5_join_there own hh hz hin h1 hk3 gf U none hcE hcF hj
  have hG2 : ((behind s a h G).putFork y.2.1).fork? = some (G.paid gL.owedJoin) := by
    rw [P.joinF_ledger hj]
    rfl
  refine formsTQ_of (l := [y.1]) Rd St own rd P.segAt_behind rfl (hRd _ _ rfl
    (P.readerOf_runN' (P.find_join A) (P.joinRun_behind A hg hun hk hj) rfl hG2
      (P.lateOf_paid G _) fun f hf => ?_)) (fun f hf => ?_) fun f hf => ?_
  · obtain rfl := List.mem_singleton.1 hf
    exact P.all_ownRow hT.2
  · obtain rfl := List.mem_singleton.1 hf
    exact hT.1
  · obtain rfl := List.mem_singleton.1 hf
    exact h0

end

/-- **The frame of the sentence on the run "join".** Conditional; the premises are listed in the
file's head. "Worth 0" is asked of whatever form the lookup's text returns on the key forms at the
state behind the lay. -/
theorem join_of_runs (Rd : Readers) (St : Stated) (A : Attention.Plan) (own : List (ℕ × ℕ))
    {s : First.S} {a : First.AttOwn} {x : Params.AttentionRounds} {rs : List Fmt.RoundView} {h : P.Heard}
    {G : Fork}
    (hRd : ∀ (name : String) (R : Read), (name == "K8.equations") = false →
      readerOf (fun _ => runsN A) 2 name (behind s a h G) = some R →
      Rd.forms 2 name (behind s a h G) = some R)
    (hh : hear x (a.F, rs, 0) = some (h, G, [], 0)) (hz : OnBytes.Model.Road.Sized a.F)
    (Rt : RunsReturn A s a h G) (gf : GeoFits (P.parCOf A).geo x)
    (U : U3There own s a (P.parCOf A)) (rd : ℕ × ℕ → MsgQ)
    (h0 : ∀ (gL : Forest.Heard) (kf : Array Aff) (y : Aff × Fork × OnBytes.K.Kc.Tape),
      a.lookHeard = some gL →
      P.keysOfK (P.seatCO (P.parCOf A)) (P.parCOf A) (behind s a h G) = some kf →
      Look.joinF gL kf G [] = some y →
      y.1.value Reading.gl (worldBehind St own s a h G rd) = 0) :
    formsTQ Rd St own 2 "join" (behind s a h G) rd := by
  obtain ⟨i, n, l₁, l₂, j, kf, gL, y, hin, h1, _, hk, hg, hcE, hcF, hun, hj⟩ := Rt
  exact join_of_zero Rd St A own hRd hh hz hin h1 hk gf U hg hcE hcF hun hj rd (h0 gL kf y hg hk hj)

end H2K5.Honest

#print axioms H2K5.Honest.join_value
#print axioms H2K5.Honest.join_zero
#print axioms H2K5.Honest.join_of_zero
#print axioms H2K5.Honest.join_of_runs
