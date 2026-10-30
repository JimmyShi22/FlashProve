-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ok/PlanWritten/AtDesc.lean: over Johnson/Desc/Ok/PlanWritten/Pinned.lean: THE LAWS OF
THE TEST ON A FILE's DESCRIPTION's DECLARED ROUNDS AND DEPTH (`FileDescription`, Johnson/Desc/Block.lean):
AT THE FULL SIZE's KEY the description's declared rounds, written out, are the written lists, and
its table's depth is 32; AT EVERY OTHER KEY: YES. A yes at the full size's key gives: the data that
the description hands the compiler (`FileDescription.data`, Johnson/Desc/BlockSlot.lean) are the written
data.

ROW OR TOOL. EVERY DECLARATION HERE IS A TOOL: a rule for all descriptions F, all declared rounds D,
all m. No description is named.

Why. The statement of Johnson/Desc/Ok/PlanWritten/Rounds.lean compares what `writtenOf` makes of the
planner's declared rounds. `FileDescription.data F file` is `writtenOf file F.roundsDeclaredByBlocks`, the makers' tests
`okAt` at `F.tableDepth`, and `WholeD.of`. So the written form IS the form by which a description's
rounds reach the compiler, and a test on `writtenOf file F.roundsDeclaredByBlocks` and `F.tableDepth` pins the data.
At the full size's written lists the makers' tests' yes is proved in
Johnson/G/DryProofTestsFull.lean and Johnson/G/DryKeyTests.lean.

Definitions, statements and proofs.
  The tests are defined in Johnson/Desc/Ok/PlanWritten/Test.lean. `declIs file R a D d`: of declared
    rounds D and a depth d: `writtenOf file D` returns R, and d is a. `declIs_iff`: what a yes says,
    both ways. `declIs_unique`: a yes at one pair at most.
  `declPinned file R k D d`: with code: if the key k is the full size's then `declIs file R 32 D d`,
    else true. A `FileDescription` HAS NO FIELD FOR THE MODEL's SIZES: SO THE KEY IS A LETTER k: whoever
    lays the test hands it the key from where the description is made (`keyOf m`,
    Johnson/Desc/Ok/PlanWritten/Rounds.lean: three fields of the strict scan of the PUBLIC parameter
    file).
  `descPinned file R k F`: THE TEST ON A DESCRIPTION: `declPinned` at `F.roundsDeclaredByBlocks` and `F.tableDepth`.
    `tableDepth` is a field of F; `roundsDeclaredByBlocks` is no field: it is the rounds of the three chains' blocks
    in a row, which is what `F.data` reads. The field `F.plans` is not compared. `descPinnedProof k
    F`, `descPinnedKey k F`: at "proof file" and `dryProofFull`; at "key file" and `dryKeyFull`.
  `descPinned_yes`: at the full size's key a yes says: `writtenOf file F.roundsDeclaredByBlocks = .ok R` and
    `F.tableDepth = 32`. `descPinned_other`: at another key: yes.
  `data_of_written`: for every F, file, R and a: `writtenOf file F.roundsDeclaredByBlocks = .ok R`, `F.tableDepth = a`
    and `okAt a (some R) = true` give `F.data file = .ok (WholeD.of a (wholeAt (some R)))`.
    `data_proofFull`, `data_keyFull`: at the full size's written lists and 32: by `okAt_proofFull`
    (Johnson/G/DryProofTestsFull.lean) and `okAt_keyFull` (Johnson/G/DryKeyTests.lean).
  `data_of_pinnedProof`, `data_of_pinnedKey`: A YES AT THE FULL SIZE's KEY GIVES THE WRITTEN DATA:
    `F.data "proof file" = .ok writtenPFull`, and the key file's like.
  TEETH, at the full size's key. `descPinned_plant`: A PLANT IS REFUSED: if F's declared rounds,
    written out, are the proof file's written lists with one number changed (control 1's chain,
    Johnson/Desc/Ok/PlanWritten/Rounds.lean), the test says no. `descPinned_depth`: at another depth
    than 32 it says no. `descPinned_refusal`: where `writtenOf` refuses it says no.
  `computed_written`: the computed data in the form of Johnson/Flat/Dec/FitAtWritten.lean: where
    `roundsAt m` returns the full size's six lists and `depthOf m` returns 32, `dataKAt m` and
    `dataPAt m` return `WholeD.of 32 (wholeAt (some dryKeyFull))` and the like of `dryProofFull`.
  `declPinned_of_plan`: FROM THE TEST ON m TO THE TEST ON THE FIELDS: where `planPinnedFull m` says
    yes, `declPinned` says yes at m's key, at what `declKOf m`, `declPOf m` and `depthOf m` return.
    `desc_of_plan`, `desc_of_plan_key`: FROM THE PLANNER TO A DESCRIPTION, UNDER TWO NAMED PREMISES:
    if F's declared rounds are what `declPOf m` returns and F's depth is what `depthOf m` returns, a
    yes of `planPinnedFull m` at the full size's key gives the written data.
  `descLines`, `rideDesc note pol lay KL`: FOR A RUN: four named Bools, with ONE call of the
    planner. NO DESCRIPTION IS EVALUATED BY IT: it shows that the test's body is no "no to all" at
    what the planner makes; the first two answers count only beside a true third; the fourth is then
    foretold by `declIs_unique`. The four: `declPinned` at the proof file's and at the key file's
    declared rounds as they are made at 32 zero bytes, with the key and the depth made there; that
    the key is the full size's; the plant: `declPinned` at the proof file's lists with one number
    changed. `of_rideDesc`: what the answers true, true, true give.

What of OnBytes/Model/ and OnBytes/Tie/ is used: `Tie.exc_step`, and what
Johnson/Desc/Ok/PlanWritten/Rounds.lean names.

Limits. NO DESCRIPTION IS NAMED: that any description's `roundsDeclaredByBlocks` is what `declPOf m` or `declKOf m`
returns, its `tableDepth` what `depthOf m` returns, and the key that it hands the test `keyOf m`,
are premises or letters here and are shown of no description. `FileDescription.planOk` holds `F.roundsDeclaredByBlocks`
against `F.plans`, not against the planner. A KEY THAT IS NOT `keyOf m` OF THE PUBLIC FILES' m WOULD
OPEN THE ARM "yes": the test is only as good as the key that it is handed. IT PINS NOTHING OUTSIDE
THE FULL SIZE's KEY. Laid among a description's tests, WITH THE KEY OF THE PUBLIC FILES' m, it makes
that description accept, at the sizes L = 48, d = 5120, V = 202048, only a plan whose three written
lists and stored table's depth are the written ones; at other sizes it is what it was, and nothing
is proved there. It is laid nowhere by this file. What is not compared: as in
Johnson/Desc/Ok/PlanWritten/Rounds.lean and Johnson/Desc/Ok/PlanWritten/Pinned.lean (each plan's six
settings, the entry RECORD, the errors' numbers, sizes and codes but for the depth, the entry file;
`F.plans`, `F.fileOk` and every other field of F). No second witness: the written lists were printed
from this library's own planner. The ride was run by nobody known to this file. Nothing on
soundness.


-/
import Johnson.Desc.Ok.PlanWritten.Pinned
import Johnson.Desc.BlockSlot
import Johnson.Flat.Dec.FitAtWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten
open Johnson.G Johnson.G.OfPlan VerifiableInference.Number VerifiableInference.Desc
open OnBytes.Params (Rounds)
open OnBytes.Maker (WholeD dataAt wholeAt okAt dataAt_of_ok)
open OnBytes.Tie (exc_step)

variable {Xi : Type}

/-! ## The test on declared rounds and a depth -/

/-- What a yes says, both ways. -/
theorem declIs_iff (file : String) (R : Rounds × Rounds × Rounds) (a : ℕ) (D : Decl3) (d : ℕ) :
    declIs file R a D d = true ↔ writtenOf file D = .ok R ∧ d = a := by
  unfold declIs
  rw [Bool.and_eq_true_iff]
  constructor
  · rintro ⟨h, hd⟩
    refine ⟨?_, of_decide_eq_true hd⟩
    split at h
    · rename_i x hx
      rw [hx, of_decide_eq_true h]
    · cases h
  · rintro ⟨hw, hd⟩
    rw [hw]
    exact ⟨decide_eq_true rfl, decide_eq_true hd⟩

/-- It says yes at one pair at most. -/
theorem declIs_unique {file : String} {R R' : Rounds × Rounds × Rounds} {a a' : ℕ} {D : Decl3}
    {d : ℕ} (h : declIs file R a D d = true) (hne : R' ≠ R ∨ a' ≠ a) :
    declIs file R' a' D d = false := by
  cases h' : declIs file R' a' D d with
  | false => rfl
  | true =>
    obtain ⟨r, e⟩ := (declIs_iff file R a D d).1 h
    obtain ⟨r', e'⟩ := (declIs_iff file R' a' D d).1 h'
    exact hne.elim (fun n => absurd (Except.ok.inj (r'.symm.trans r)) n)
      (fun n => absurd (e'.symm.trans e) n)

/-- **At the full size's key a yes says**: written out, the description's declared rounds are R, and
its depth is 32. -/
theorem descPinned_yes {file : String} {R : Rounds × Rounds × Rounds} {k : ℕ × ℕ × ℕ}
    {F : FileDescription Xi} (hk : k = fullKey) (h : descPinned file R k F = true) :
    writtenOf file F.roundsDeclaredByBlocks = .ok R ∧ F.tableDepth = 32 := by
  unfold descPinned declPinned at h
  rw [if_pos hk] at h
  exact (declIs_iff _ _ _ _ _).1 h

/-- At another key: yes. -/
theorem descPinned_other {file : String} {R : Rounds × Rounds × Rounds} {k : ℕ × ℕ × ℕ}
    {F : FileDescription Xi} (hk : k ≠ fullKey) : descPinned file R k F = true := by
  unfold descPinned declPinned
  rw [if_neg hk]

/-- At the full size's key it says no wherever the written rounds and the depth are not these. -/
theorem descPinned_no {file : String} {R : Rounds × Rounds × Rounds} {k : ℕ × ℕ × ℕ}
    {F : FileDescription Xi} (hk : k = fullKey)
    (hn : ¬ (writtenOf file F.roundsDeclaredByBlocks = .ok R ∧ F.tableDepth = 32)) :
    descPinned file R k F = false := by
  cases h : descPinned file R k F with
  | false => rfl
  | true => exact absurd (descPinned_yes hk h) hn

/-! ## The data that a description hands the compiler -/

/-- **The data that a description hands the compiler are the data of its written rounds at its
depth**, where the makers' tests pass. -/
theorem data_of_written (F : FileDescription Xi) (file : String) {R : Rounds × Rounds × Rounds} {a : ℕ}
    (hw : writtenOf file F.roundsDeclaredByBlocks = .ok R) (hd : F.tableDepth = a)
    (hok : okAt a (some R) = true) : F.data file = .ok (WholeD.of a (wholeAt (some R))) := by
  subst hd
  unfold FileDescription.data
  refine (exc_step _ hw).trans ?_
  dsimp only
  split
  · rfl
  · rename_i h
    exact absurd hok h

/-- At the full size's written lists of the proof file. -/
theorem data_proofFull (F : FileDescription Xi) (hw : writtenOf "proof file" F.roundsDeclaredByBlocks = .ok dryProofFull)
    (hd : F.tableDepth = 32) :
    F.data "proof file" = .ok writtenPFull :=
  data_of_written F _ hw hd okAt_proofFull

/-- At the full size's written lists of the key file. -/
theorem data_keyFull (F : FileDescription Xi) (hw : writtenOf "key file" F.roundsDeclaredByBlocks = .ok dryKeyFull)
    (hd : F.tableDepth = 32) :
    F.data "key file" = .ok writtenKFull :=
  data_of_written F _ hw hd okAt_keyFull

/-- **A yes at the full size's key gives the written data: the proof file.** -/
theorem data_of_pinnedProof {k : ℕ × ℕ × ℕ} {F : FileDescription Xi} (hk : k = fullKey)
    (h : descPinnedProof k F = true) :
    F.data "proof file" = .ok writtenPFull :=
  data_proofFull F (descPinned_yes hk h).1 (descPinned_yes hk h).2

/-- **The key file.** -/
theorem data_of_pinnedKey {k : ℕ × ℕ × ℕ} {F : FileDescription Xi} (hk : k = fullKey)
    (h : descPinnedKey k F = true) :
    F.data "key file" = .ok writtenKFull :=
  data_keyFull F (descPinned_yes hk h).1 (descPinned_yes hk h).2

/-! ## Teeth -/

/-- The proof file's written lists with one number changed (control 1's second chain). -/
def plantedProof : Rounds × Rounds × Rounds := (dryProofFull.1, dryProofFull.2.1, bentWorkR)

/-- They are another value than the written lists. -/
theorem plantedProof_ne : plantedProof ≠ dryProofFull := fun e =>
  of_decide_eq_false (congrArg (·.1) second_ne)
    (congrArg (fun x : Rounds × Rounds × Rounds => x.2.2) e)

/-- **A tooth: A PLANT IS REFUSED**, at the full size's key. -/
theorem descPinned_plant {k : ℕ × ℕ × ℕ} {F : FileDescription Xi} (hk : k = fullKey)
    (hw : writtenOf "proof file" F.roundsDeclaredByBlocks = .ok plantedProof) : descPinnedProof k F = false :=
  descPinned_no hk fun x => plantedProof_ne (Except.ok.inj (hw.symm.trans x.1))

/-- A tooth: at another depth, at the full size's key. -/
theorem descPinned_depth {file : String} {R : Rounds × Rounds × Rounds} {k : ℕ × ℕ × ℕ}
    {F : FileDescription Xi} (hk : k = fullKey) (hd : F.tableDepth ≠ 32) :
    descPinned file R k F = false :=
  descPinned_no hk fun x => hd x.2

/-- A tooth: where `writtenOf` refuses, at the full size's key. -/
theorem descPinned_refusal {file : String} {R : Rounds × Rounds × Rounds} {k : ℕ × ℕ × ℕ}
    {F : FileDescription Xi} {e : String} (hk : k = fullKey) (hw : writtenOf file F.roundsDeclaredByBlocks = .error e) :
    descPinned file R k F = false :=
  descPinned_no hk fun x => by
    have c := hw.symm.trans x.1
    cases c

/-! ## From the planner -/

/-- **The computed data in the form of Johnson/Flat/Dec/FitAtWritten.lean.** -/
theorem computed_written {m : Made} (hr : roundsAt m = .ok (dryKeyFull, dryProofFull))
    (hd : depthOf m = .ok 32) :
    dataKAt m = .ok writtenKFull ∧
      dataPAt m = .ok writtenPFull := by
  obtain ⟨k, p⟩ := data_of_rounds hr hd
  have k' : dataKAt m = .ok (WholeD.of 32 (dataAt 32 (some dryKeyFull))) := k
  have p' : dataPAt m = .ok (WholeD.of 32 (dataAt 32 (some dryProofFull))) := p
  rw [dataAt_of_ok okAt_keyFull] at k'
  rw [dataAt_of_ok okAt_proofFull] at p'
  exact ⟨k', p'⟩

/-- **From the test on m to the test on the fields**: where `planPinnedFull m` says yes,
`declPinned` says yes at m's key, at what `declKOf m`, `declPOf m` and `depthOf m` return. -/
theorem declPinned_of_plan {m : Made} {DK DP : Decl3} {d : ℕ} (hK : declKOf m = .ok DK)
    (hP : declPOf m = .ok DP) (hD : depthOf m = .ok d) (hy : planPinnedFull m = true) :
    declPinned "key file" dryKeyFull (keyOf m) DK d = true ∧
      declPinned "proof file" dryProofFull (keyOf m) DP d = true := by
  unfold declPinned
  by_cases hk : keyOf m = fullKey
  · rw [if_pos hk, if_pos hk]
    obtain ⟨hr, hd⟩ := pinnedFull_yes hk hy
    obtain ⟨DK', DP', hK', hwK, hP', hwP⟩ := decl_of_roundsAt hr
    have eK : DK' = DK := Except.ok.inj (hK'.symm.trans hK)
    have eP : DP' = DP := Except.ok.inj (hP'.symm.trans hP)
    have ed : d = 32 := Except.ok.inj (hD.symm.trans hd)
    rw [eK] at hwK
    rw [eP] at hwP
    exact ⟨(declIs_iff _ _ _ _ _).2 ⟨hwK, ed⟩, (declIs_iff _ _ _ _ _).2 ⟨hwP, ed⟩⟩
  · rw [if_neg hk, if_neg hk]
    exact ⟨rfl, rfl⟩

/-- **From the planner to a proof file's description, under two named premises**: its declared
rounds are what `declPOf m` returns, and its depth is what `depthOf m` returns. -/
theorem desc_of_plan {m : Made} (F : FileDescription Xi) (hF : declPOf m = .ok F.roundsDeclaredByBlocks)
    (hD : depthOf m = .ok F.tableDepth) (hk : keyOf m = fullKey) (hy : planPinnedFull m = true) :
    F.data "proof file" = .ok writtenPFull := by
  obtain ⟨hr, hd⟩ := pinnedFull_yes hk hy
  obtain ⟨_, DP, _, _, hP, hwP⟩ := decl_of_roundsAt hr
  have e : DP = F.roundsDeclaredByBlocks := Except.ok.inj (hP.symm.trans hF)
  rw [e] at hwP
  exact data_proofFull F hwP (Except.ok.inj (hD.symm.trans hd))

/-- The like for a key file's description and `declKOf m`. -/
theorem desc_of_plan_key {m : Made} (F : FileDescription Xi) (hF : declKOf m = .ok F.roundsDeclaredByBlocks)
    (hD : depthOf m = .ok F.tableDepth) (hk : keyOf m = fullKey) (hy : planPinnedFull m = true) :
    F.data "key file" = .ok writtenKFull := by
  obtain ⟨hr, hd⟩ := pinnedFull_yes hk hy
  obtain ⟨DK, _, hK, hwK, _, _⟩ := decl_of_roundsAt hr
  have e : DK = F.roundsDeclaredByBlocks := Except.ok.inj (hK.symm.trans hF)
  rw [e] at hwK
  exact data_keyFull F hwK (Except.ok.inj (hD.symm.trans hd))

/-! ## A ride for the test on the fields -/

/-- What is made at an anchor for the test on the fields: the key, the two files' declared rounds,
the depth. -/
def fieldsAtZero (pol lay KL : ByteArray) : Except String ((ℕ × ℕ × ℕ) × Decl3 × Decl3 × ℕ) :=
  madeOfAt pol lay KL Fmt.zero32 >>= fun m => declKOf m >>= fun DK => declPOf m >>= fun DP =>
    depthOf m >>= fun d => .ok (keyOf m, DK, DP, d)

/-- The test at the proof file's and at the key file's fields; that the key is the full size's; the
plant. At a refusal all four are false, and the first line holds the refusal's words. -/
def descLines (note : String) (r : Except String ((ℕ × ℕ × ℕ) × Decl3 × Decl3 × ℕ)) :
    List (String × Bool) :=
  match r with
  | .ok y =>
    [(note ++ ": to say true: declPinned at the proof file's declared rounds, key and depth as " ++
        "made at 32 zero bytes", declPinned "proof file" dryProofFull y.1 y.2.2.1 y.2.2.2),
      ("to say true: declPinned at the key file's",
        declPinned "key file" dryKeyFull y.1 y.2.1 y.2.2.2),
      ("to say true: the key is the full size's", decide (y.1 = fullKey)),
      ("the plant, to say false: declPinned at the proof file's lists with one number changed",
        declPinned "proof file" plantedProof y.1 y.2.2.1 y.2.2.2)]
  | .error e =>
    [(note ++ ": refused: " ++ e, false), ("the key file's", false), ("the key", false),
      ("the plant", false)]

/-- **FOR A RUN**: four named Bools, with one call of the planner. NO DESCRIPTION IS EVALUATED: the
test is asked at the declared rounds, the depth and the key that THE PLANNER makes. The plant bends
the written side, not the declared rounds. note: a string that the first line gives back (why: the
head of Johnson/Desc/Ok/PlanWritten/Rounds.lean). -/
@[noinline] def rideDesc (note : String) (pol lay KL : ByteArray) : List (String × Bool) :=
  descLines note (fieldsAtZero pol lay KL)

/-- **What a ride with the answers true, true, true gives**: at the anchor something is made with
the full size's key; its two files' declared rounds, written out, are the written lists; its depth
is 32. -/
theorem of_rideDesc {note : String} {pol lay KL : ByteArray}
    (h : ((rideDesc note pol lay KL).map Prod.snd).take 3 = [true, true, true]) :
    ∃ m DK DP, madeOfAt pol lay KL Fmt.zero32 = .ok m ∧ keyOf m = fullKey ∧
      declKOf m = .ok DK ∧ declPOf m = .ok DP ∧ depthOf m = .ok 32 ∧
      writtenOf "key file" DK = .ok dryKeyFull ∧ writtenOf "proof file" DP = .ok dryProofFull := by
  unfold rideDesc descLines at h
  split at h
  · rename_i y hy
    obtain ⟨h1, h⟩ := List.cons.inj h
    obtain ⟨h2, h⟩ := List.cons.inj h
    obtain ⟨h3, _⟩ := List.cons.inj h
    have hk : y.1 = fullKey := of_decide_eq_true h3
    unfold declPinned at h1 h2
    rw [if_pos hk] at h1 h2
    obtain ⟨w1, d1⟩ := (declIs_iff _ _ _ _ _).1 h1
    obtain ⟨w2, _⟩ := (declIs_iff _ _ _ _ _).1 h2
    unfold fieldsAtZero at hy
    obtain ⟨m, hm, hy⟩ := bind_ok hy
    obtain ⟨DK, hK, hy⟩ := bind_ok hy
    obtain ⟨DP, hP, hy⟩ := bind_ok hy
    obtain ⟨d, hd, hy⟩ := bind_ok hy
    have e : y = (keyOf m, DK, DP, d) := (Except.ok.inj hy).symm
    rw [e] at hk w1 w2 d1
    have ed : d = 32 := d1
    rw [ed] at hd
    exact ⟨m, DK, DP, hm, hk, hK, hP, hd, w2, w1⟩
  · obtain ⟨h1, _⟩ := List.cons.inj h
    cases h1

end VerifiableInference.PlanWritten

#print axioms VerifiableInference.PlanWritten.declIs_iff
#print axioms VerifiableInference.PlanWritten.declIs_unique
#print axioms VerifiableInference.PlanWritten.descPinned_yes
#print axioms VerifiableInference.PlanWritten.descPinned_other
#print axioms VerifiableInference.PlanWritten.descPinned_no
#print axioms VerifiableInference.PlanWritten.data_of_written
#print axioms VerifiableInference.PlanWritten.data_proofFull
#print axioms VerifiableInference.PlanWritten.data_keyFull
#print axioms VerifiableInference.PlanWritten.data_of_pinnedProof
#print axioms VerifiableInference.PlanWritten.data_of_pinnedKey
#print axioms VerifiableInference.PlanWritten.plantedProof_ne
#print axioms VerifiableInference.PlanWritten.descPinned_plant
#print axioms VerifiableInference.PlanWritten.descPinned_depth
#print axioms VerifiableInference.PlanWritten.descPinned_refusal
#print axioms VerifiableInference.PlanWritten.computed_written
#print axioms VerifiableInference.PlanWritten.declPinned_of_plan
#print axioms VerifiableInference.PlanWritten.desc_of_plan
#print axioms VerifiableInference.PlanWritten.desc_of_plan_key
#print axioms VerifiableInference.PlanWritten.of_rideDesc
