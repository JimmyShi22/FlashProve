-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Honest/FirstYes.lean: THE STAGES' SUB-PROTOCOL ACCEPTS ALL THAT `stagesAll` SHOWS,
WHERE THE FIRST STAGE's THREE PARTS ACCEPT THEIR SHARES AND THE STAGES FROM THE SECOND ON ACCEPT
THEIRS. A joining: statement and proof; every acceptance is a premise. It is the first step of the
induction of Johnson/Prover/Link/BodyYes.lean (`body_yes_of`), which deals every switch one group of
columns; here the first switch is dealt one group for each of a list of trees. It hangs on no frame
for an honest side.

  `aRec2`        the verifier's state behind the switch
  `FirstYes`     WHAT THE FIRST STAGE DELIVERS: the fold, the switch and the batching behind it
                 accept `aFold` | `aSwitch` with `aGroups` | nothing · the next mask has come · four
                 public numbers of the kind's cut, THE SWITCH's OPENINGS BEING AS MANY AS THE TREES
  **`stages_yes_first`**   `FirstYes` · each stage fits the next · the stages' sub-protocol from the
                 second stage on accepts all that `bodyAll` shows there, from the state, the rows
                 and the tree that the first stage leaves ⟹ the stages' sub-protocol accepts all
                 that `stagesAll` shows

By: the library's `stagesFrom_ok` (Johnson/Desc/K12/FrameLaws.lean), an iff; `stages_eq`
(Johnson/Desc/K12/Honest/Stages.lean).

Limits. That any of the premises holds, at any place, is not shown here. `FirstYes` has no member in
this file. Nothing on completeness, on soundness or on what is hidden.


-/
import Johnson.Desc.K12.Honest.Causal
import Johnson.Prover.Link.BodyYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link
open H2K.Pub (sgOf)

section
variable (p : P12) (K : BCoins) (rest : List Fmt.M1.Stage) (j : ℕ) (cur next : Fmt.M1.Stage)
  (l : Laid) (o : ℕ) (t : T12) (P : PS) (trees : List Tree) (D : ℕ → Fmt.Drawn)

/-- The first stage's pieces at the row that the state in front holds. -/
abbrev rfAt : List Fmt.RoundView := aFold K j cur o P (rowOf t) D
abbrev qAt : PS := aNext K rest.isEmpty j cur next o P D
abbrev t1At : T12 := aRec1 p j cur l t (rfAt K j cur o t P D)
abbrev rsAt : List Fmt.RoundView :=
  aSwitch cur o D (aAns p j cur next o D (t1At p K j cur l o t P D) (qAt K rest j cur next o P D))

/-- The verifier's state behind the switch. -/
def aRec2 : T12 :=
  ((guardedProximityTestParts.switch p j cur next rest.isEmpty (((l.drop (1 + cur.k)).take 2).map (·.1))).decide
    (t1At p K j cur l o t P D) ((rsAt p K rest j cur next l o t P D).map noDigest)
    (aGroups cur o trees D)).toOption.getD (t1At p K j cur l o t P D)

abbrev t3At : T12 :=
  aRec3 p rest.isEmpty j cur next l o trees D (t1At p K j cur l o t P D)
    (rsAt p K rest j cur next l o t P D)

/-- **What the first stage delivers.** -/
structure FirstYes : Prop where
  fold : ∃ t₁, (guardedProximityTestParts.fold p j cur ((l.take (1 + cur.k)).map (·.1))).decide t
    ((rfAt K j cur o t P D).map noDigest) [] = .ok t₁
  switch : ∃ t₂, (guardedProximityTestParts.switch p j cur next rest.isEmpty
    (((l.drop (1 + cur.k)).take 2).map (·.1))).decide (t1At p K j cur l o t P D)
    ((rsAt p K rest j cur next l o t P D).map noDigest) (aGroups cur o trees D) = .ok t₂
  behind : ∃ t₃, (guardedProximityTestParts.batBehind p (j + 1) next
    (((l.drop (1 + cur.k)).take 2).map (·.1))).decide
    (aRec2 p K rest j cur next l o t P trees D) [] [] = .ok t₃
  came : (!p.early || guardedProximityTestParts.maskCame (t3At p K rest j cur next l o t P trees D)) = true
  nF : (foldAt guardedProximityTestParts p j cur l : Block T12 Unit).rounds.length =
    1 + ((sgOf cur).h + (sgOf cur).g)
  oF : (foldAt guardedProximityTestParts p j cur l : Block T12 Unit).openings = 0
  nS : (switchAt guardedProximityTestParts p j cur next rest.isEmpty l : Block T12 Unit).rounds.length = 2
  oS : (switchAt guardedProximityTestParts p j cur next rest.isEmpty l : Block T12 Unit).openings = trees.length

/-- **The first step.** -/
theorem stages_yes_first (Y : FirstYes p K rest j cur next l o t P trees D)
    (hfit : FitAll next rest) (t' : T12)
    (ih : (stagesFrom guardedProximityTestParts p (j + 1) next rest (l.drop (cur.k + 3)) : Block T12 Unit).decide
      (t3At p K rest j cur next l o t P trees D)
      ((bodyAll p K rest (j + 1) next (l.drop (cur.k + 3)) (o + ((sgOf cur).h + (sgOf cur).g) + 3)
        (t3At p K rest j cur next l o t P trees D) (qAt K rest j cur next o P D)
        (aCol rest.isEmpty next (qAt K rest j cur next o P D)) D).rs.map noDigest)
      (bodyAll p K rest (j + 1) next (l.drop (cur.k + 3)) (o + ((sgOf cur).h + (sgOf cur).g) + 3)
        (t3At p K rest j cur next l o t P trees D) (qAt K rest j cur next o P D)
        (aCol rest.isEmpty next (qAt K rest j cur next o P D)) D).gs = .ok t') :
    (stagesFrom guardedProximityTestParts p j cur (next :: rest) l : Block T12 Unit).decide t
      ((stagesAll p K (next :: rest) j cur l o t P trees D).rs.map noDigest)
      (stagesAll p K (next :: rest) j cur l o t P trees D).gs = .ok t' := by
  obtain ⟨t₁, h1⟩ := Y.fold
  obtain ⟨t₂, h2⟩ := Y.switch
  obtain ⟨t₃, h3⟩ := Y.behind
  have e1 : t1At p K j cur l o t P D = t₁ := getD_of_ok h1
  have e2 : aRec2 p K rest j cur next l o t P trees D = t₂ := getD_of_ok h2
  have e3 : t3At p K rest j cur next l o t P trees D = t₃ := getD_of_ok h3
  have lF : ((rfAt K j cur o t P D).map noDigest).length = 1 + ((sgOf cur).h + (sgOf cur).g) := by
    rw [List.length_map]; exact length_aFold K j cur o P (rowOf t) D
  have lS : ((rsAt p K rest j cur next l o t P D).map noDigest).length = 2 := rfl
  have lG : (aGroups cur o trees D).length = trees.length := List.length_map _
  rw [← stages_eq p K rest (j + 1) next _ _ _ _ _ D hfit] at ih
  refine (stagesFrom_ok guardedProximityTestParts p j cur next rest l t t' _ _).2 ⟨t₁, t₂, t₃, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Y.nF, Y.oF]
    show (guardedProximityTestParts.fold p j cur _).decide t (((rfAt K j cur o t P D ++
                       rsAt p K rest j cur next l o t P D ++ _).map noDigest).take _) (List.take 0 _) = _
    rw [List.map_append, List.map_append, List.append_assoc, ← lF, List.take_left',
      List.take_zero]
    · exact h1
    · rfl
  · rw [Y.nF, Y.oF, Y.nS, Y.oS]
    show (guardedProximityTestParts.switch p j cur next rest.isEmpty _).decide t₁
      ((((rfAt K j cur o t P D ++ rsAt p K rest j cur next l o t P D ++ _).map
        noDigest).drop _).take 2) (((aGroups cur o trees D ++ _).drop 0).take trees.length) = _
    rw [List.map_append, List.map_append, List.append_assoc, ← lF, List.drop_left' rfl,
      List.take_left' lS, List.drop_zero, List.take_left' lG, ← e1]
    exact h2
  · rw [← e2]; exact h3
  · rw [← e3]; exact Y.came
  · rw [Y.nF, Y.oF, Y.nS, Y.oS, ← e3]
    show (stagesFrom guardedProximityTestParts p (j + 1) next rest _ : Block T12 Unit).decide _
      (((rfAt K j cur o t P D ++ rsAt p K rest j cur next l o t P D ++ _).map
        noDigest).drop _) ((aGroups cur o trees D ++ _).drop (0 + trees.length)) = _
    rw [List.map_append, List.map_append,
      List.drop_left' (by rw [List.length_append, lF, lS]), Nat.zero_add, List.drop_left' lG]
    exact ih

end

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.stages_yes_first
