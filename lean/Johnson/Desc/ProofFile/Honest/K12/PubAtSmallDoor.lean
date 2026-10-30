-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/PubAtSmallDoor.lean: `doorOf` (JobShared.lean) at the small
made-up chain of SharedSmall.lean (`P3`): theorems for every input, and evaluations at honest
values.

  `bs3`, `blocks_P3`   the eight blocks at `P3`
  `planOk_p`       the block of the test on G_u passes its test on the plan
  `near_small_U`, `near_small_Omega` `nearDoor_U` and `nearDoor_Omega` (PubNear.lean) at `P3`, at
                   the state functions `doorU` and `doorOmega` (NearAtHead.lean)
  `layFits_small_doorU`, `layFits_small_doorOmega`   at `jobAtU` and `jobAtOmega` (JobShared.lean)
                   with these state functions `layFits` is true at the job's own state on entry, for
                   every input and whatever precedes the test. Two facts are joined at one job: what
                   `layFits` reads of that state is one public term (`near_small_U`), and
                   `layFitsNear` is true at that term (`layFitsNear_U`, PubAtSmall.lean)
  `colsU`, `frO`, `colsO` the columns that "LOC" reads, made from the honest rows; the honest rounds
                   with those of the test on G_u behind them; the columns with those that this test
                   reads behind them
  The guards evaluate `doorOf` at these values.

By what. The theorems: `nearDoor_U`, `nearDoor_Omega`, `layFits_near` (PubNear.lean),
`layFitsNear_congr` (NearAtHead.lean), `layFitsNear_U`, `layFitsNear_Omega` (PubAtSmall.lean). The
guards are evaluated by the compiler.

What the guards show. At the honest rounds and columns of JobSharedToy.lean the fold over the eight
blocks returns, so `doorOf` there gives a state that is not its fall-back: its groups have six open
rows and one, with the right sides of JobSharedToy.lean's `door`. With one round fewer, or without
the columns, the fold fails and `doorOf` gives the fall-back. With another word in a column the fold
returns, the open rows are others, and the public part stays. At the test on G_omega: with the
columns that the test on G_u reads handed in as well, the fold over the nine blocks returns, and the
state has the numbers of `doorO`; without them `doorOf` gives the fall-back, `pubNear` stays, and
`pubOf` is another.

Limits. One small made-up plan and one set of honest values. The theorems are also true of the
fall-back: they do not tell a fold that failed from one that returned, and they are no statement
that the state on entry is the verifier's. At G_omega the guards hand `doorOf` columns that are made
with the random values of the test on G_u: they are laid by hand here. The walk (`runC`) hands a
part the columns opened so far (`Seen.opened`); that a seat's letter `cols` takes them from there is
not shown here. At a seat whose letter `cols` gives none of them on, `doorOf` returns its fall-back
there at every honest run. The file imports NearAtHead.lean, and with it Mathlib, for three names.
Nothing on completeness, soundness or hiding.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.PubAtSmall
import Johnson.Desc.ProofFile.Honest.K12.NearAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light.SharedSmall
open OnBytes (TableKey)
open VerifiableInference.Desc (Block OpenedColumn foldBlocks groupsOf)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open Desc.K14 (St blocks first)
open ProofFile.Honest.K12.Light.SharedHonest (rows keyAt symbolAt)
open ProofFile.Honest.K12.Light.SharedToy (fr door doorO light)

variable {W X : Type}

/-! ## 1 For every input -/

/-- The eight blocks at `P3`. -/
def bs3 : List (Block St Unit) := (blocks P3).getD []

theorem blocks_P3 : blocks P3 = some bs3 := by
  have h : ∃ bs, blocks P3 = some bs := by
    unfold blocks
    rw [withU_P3]
    exact ⟨_, rfl⟩
  obtain ⟨bs, h⟩ := h
  unfold bs3
  rw [h]
  rfl

theorem planOk_p : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk = true := by decide +kernel

/-- `nearDoor_U` at `P3`. The state is `doorOf`'s, whose fall-back is made from the same term: where
the fold or `enter` fails, the equation holds by that choice. -/
theorem near_small_U (key : W → TableKey) (cols : W → Front X → List OpenedColumn) (w : W) (fr : Front X) :
    pubNear (doorU P3 bs3 key cols w fr) = nearOf (pubBehind P3 sentU3) 0 :=
  nearDoor_U P3 bs3 blocks_P3 splits_P3 ahead_P3 sentU3 withU_P3 key cols w fr

/-- `nearDoor_Omega` at `P3`. The state is `doorOf`'s, whose fall-back is made from the same term.
-/
theorem near_small_Omega (key : W → TableKey) (cols : W → Front X → List OpenedColumn) (w : W)
    (fr : Front X) :
    pubNear (doorOmega P3 bs3 p key cols w fr) = nearOf (pubBehind P3 sentU3) 1 :=
  nearDoor_Omega P3 bs3 blocks_P3 splits_P3 ahead_P3 sentU3 withU_P3 p planOk_p key cols w fr

/-- The shapes of `pubJob`'s members are the list that it is made of. -/
theorem shapes_pubJob (q : P12) (l : List MemShape) : (pubJob q l).mems.map (·.shape) = l := by
  unfold pubJob
  simp only [List.map_map]
  exact List.map_id' l

/-- **At the test on G_u `layFits` is true at the job's own state on entry**, which is `doorOf`'s,
for every input and whatever precedes the test. Also true of the fall-back: no statement that this
state is the verifier's. -/
theorem layFits_small_doorU (key : W → TableKey) (cols : W → Front X → List OpenedColumn)
    (weights : W → Weights) (rand : W → TableRand) (u? : Option (W → Front X → ℕ → OnBytes.E))
    (w : W) (fr : Front X) :
    (jobAtU ⟨P3, 0⟩ p (doorU P3 bs3 key cols) weights rand u?).layFits
      ((jobAtU ⟨P3, 0⟩ p (doorU P3 bs3 key cols) weights rand u?).rec₀ w fr) = true := by
  show (jobAtU ⟨P3, 0⟩ p (doorU P3 bs3 key cols) weights rand u?).layFits
    (doorU P3 bs3 key cols w fr) = true
  rw [layFits_near, near_small_U,
    layFitsNear_congr (jobAtU ⟨P3, 0⟩ p (doorU P3 bs3 key cols) weights rand u?)
      (pubJob p (shapesAtU ⟨P3, 0⟩ p)) rfl
      ((shapes_atU ⟨P3, 0⟩ p _ weights rand u?).trans (shapes_pubJob _ _).symm)]
  exact layFitsNear_U

/-- **The same at the test on G_omega.** Also true of the fall-back: no statement that this state is
the verifier's. -/
theorem layFits_small_doorOmega (key : W → TableKey) (cols : W → Front X → List OpenedColumn)
    (weights : W → Weights) (rand : W → TableRand)
    (omega? : Option (W → Front X → ℕ → OnBytes.E)) (w : W) (fr : Front X) :
    (jobAtOmega ⟨P3, 0⟩ pO (doorOmega P3 bs3 p key cols) weights rand omega?).layFits
      ((jobAtOmega ⟨P3, 0⟩ pO (doorOmega P3 bs3 p key cols) weights rand omega?).rec₀ w fr) =
        true := by
  show (jobAtOmega ⟨P3, 0⟩ pO (doorOmega P3 bs3 p key cols) weights rand omega?).layFits
    (doorOmega P3 bs3 p key cols w fr) = true
  rw [layFits_near, near_small_Omega,
    layFitsNear_congr (jobAtOmega ⟨P3, 0⟩ pO (doorOmega P3 bs3 p key cols) weights rand omega?)
      (pubJob pO (shapesAtOmega ⟨P3, 0⟩ pO)) rfl
      ((shapes_atOmega ⟨P3, 0⟩ pO _ weights rand omega?).trans (shapes_pubJob _ _).symm)]
  exact layFitsNear_Omega

/-! ## 2 `doorOf` evaluated at honest values -/

/-- Key, position and width of the columns that blocks read at given rounds, in order. -/
def wanted (bs : List (Block St Unit)) (rs : List Fmt.RoundView) : List (ℕ × ℕ × ℕ) :=
  (groupsOf 0 (bs.flatMap (·.rounds)) (rs.map (·.drawn))).flatMap id

/-- The columns that "LOC" reads at the honest rounds: the four rows' symbols. -/
def colsU : List OpenedColumn :=
  (wanted bs3 fr.seen.rounds).map fun x =>
    (x.1, x.2.1, (List.range 4).map fun r => symbolAt (rows 0) r x.2.1)

/-- The state function at the test on G_u, at the honest key and given columns. -/
def doorAtU (cols : List OpenedColumn) : Unit → Front Unit → T12 :=
  doorU P3 bs3 (fun _ => keyAt (rows 0)) fun _ _ => cols

/-- The honest rounds, with those of the test on G_u behind them. The field `opened` is `none`
(`Seen.bare`): the toy stands where no column is handed. -/
def frO : Front Unit :=
  let rs := fr.seen.rounds ++ (light .lib {} 0).rs
  ⟨rs.map (·.drawn), (), Seen.bare rs⟩

/-- The block of the test on G_u, as it is laid into the chain. -/
def onU : Block St Unit := VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts p)

/-- The columns that "LOC" reads, then those that the test on G_u reads. -/
def colsO : List OpenedColumn :=
  colsU ++ ((wanted [onU] (light .lib {} 0).rs).zip ((light .lib {} 0).gs.flatMap id)).map fun x =>
    (x.1.1, x.2.1, x.2.2)

/-- The state function at the test on G_omega, at the honest key and given columns. -/
def doorAtOmega (cols : List OpenedColumn) : Unit → Front Unit → T12 :=
  doorOmega P3 bs3 p (fun _ => keyAt (rows 0)) fun _ _ => cols

/-- The numbers of open rows, group by group. -/
def openRows (t : T12) : List ℕ := t.st.groups.toList.map (·.rows.size)

/-- The open rows' right sides, group by group. -/
def targets (t : T12) : List (List (UInt64 × UInt64 × UInt64)) :=
  t.st.groups.toList.map fun G => G.rows.toList.map (·.target.triple)

/-- The fold returns and leaves no round and no column. -/
def goes (bs : List (Block St Unit)) (rs : List Fmt.RoundView) (cols : List OpenedColumn) : Bool :=
  match foldBlocks 0 bs (first codes2 (keyAt (rows 0))) rs cols with
  | .ok x => x.2.1.isEmpty && x.2.2.isEmpty
  | .error _ => false

/-- The honest rounds but the last. As in `frO`, no column is handed: `Seen.bare`. -/
def frShort : Front Unit :=
  let rs := fr.seen.rounds.dropLast
  ⟨rs.map (·.drawn), (), Seen.bare rs⟩

/-- The columns that "LOC" reads, with 1 added to the first word of the first. -/
def colsTurned : List OpenedColumn :=
  match colsU with
  | c :: l => (c.1, c.2.1, c.2.2.modifyHead (· + 1)) :: l
  | [] => []

-- At G_u. The fold over the eight returns at the honest rounds and columns
#guard goes bs3 fr.seen.rounds colsU && colsU.length == 3
-- so doorOf's state is not its fall-back, which has no open row
#guard openRows (doorAtU colsU () fr) == [6, 1] &&
  openRows (stateOfPub (pubBehind P3 sentU3, 0)) == [0, 0]
-- it has the numbers of JobSharedToy.lean's door, which is made by the eight decisions in a row
#guard targets (doorAtU colsU () fr) == targets door && (doorAtU colsU () fr).roots == door.roots &&
  (doorAtU colsU () fr).g == door.g && (doorAtU colsU () fr).mask == door.mask
#guard pubOf (doorAtU colsU () fr) == pubU
#guard (ProofFile.Honest.K12.Light.SharedToy.job {}).layFits (doorAtU colsU () fr)
-- one round fewer, or no column: the fold fails, and doorOf gives the fall-back
#guard !goes bs3 frShort.seen.rounds colsU && openRows (doorAtU colsU () frShort) == [0, 0]
#guard !goes bs3 fr.seen.rounds [] && openRows (doorAtU [] () fr) == [0, 0]
-- a column with another word: the fold returns; the open rows are others; the public part stays
#guard goes bs3 fr.seen.rounds colsTurned && targets (doorAtU colsTurned () fr) != targets door &&
  pubOf (doorAtU colsTurned () fr) == pubU
-- At G_omega. With the columns that the test on G_u reads handed in, the fold over the nine returns
#guard goes (bs3 ++ [onU]) frO.seen.rounds colsO && colsO.length == 11
#guard openRows (doorAtOmega colsO () frO) == [0, 1, 0, 0] &&
  openRows (stateOfPub (pubBehind P3 sentU3, 1)) == [0, 0]
#guard targets (doorAtOmega colsO () frO) == targets doorO &&
  (doorAtOmega colsO () frO).roots == doorO.roots && (doorAtOmega colsO () frO).g == doorO.g
#guard pubOf (doorAtOmega colsO () frO) == pubO
#guard pubNear (doorAtOmega colsO () frO) == nearOf (pubBehind P3 sentU3) 1
#guard (ProofFile.Honest.K12.Light.SharedToy.jobO 0).layFits (doorAtOmega colsO () frO)
-- without these columns the fold fails, and doorOf gives the fall-back; what layFits reads stays
#guard !goes (bs3 ++ [onU]) frO.seen.rounds colsU && openRows (doorAtOmega colsU () frO) == [0, 0]
#guard pubNear (doorAtOmega colsU () frO) == nearOf (pubBehind P3 sentU3) 1 &&
  pubOf (doorAtOmega colsU () frO) != pubO

end ProofFile.Honest.K12.Light.SharedSmall

#print axioms ProofFile.Honest.K12.Light.SharedSmall.blocks_P3
#print axioms ProofFile.Honest.K12.Light.SharedSmall.planOk_p
#print axioms ProofFile.Honest.K12.Light.SharedSmall.near_small_U
#print axioms ProofFile.Honest.K12.Light.SharedSmall.near_small_Omega
#print axioms ProofFile.Honest.K12.Light.SharedSmall.shapes_pubJob
#print axioms ProofFile.Honest.K12.Light.SharedSmall.layFits_small_doorU
#print axioms ProofFile.Honest.K12.Light.SharedSmall.layFits_small_doorOmega
#print axioms ProofFile.Honest.K12.Light.SharedSmall.bs3
#print axioms ProofFile.Honest.K12.Light.SharedSmall.wanted
#print axioms ProofFile.Honest.K12.Light.SharedSmall.colsU
#print axioms ProofFile.Honest.K12.Light.SharedSmall.doorAtU
#print axioms ProofFile.Honest.K12.Light.SharedSmall.frO
#print axioms ProofFile.Honest.K12.Light.SharedSmall.onU
#print axioms ProofFile.Honest.K12.Light.SharedSmall.colsO
#print axioms ProofFile.Honest.K12.Light.SharedSmall.doorAtOmega
#print axioms ProofFile.Honest.K12.Light.SharedSmall.openRows
#print axioms ProofFile.Honest.K12.Light.SharedSmall.targets
#print axioms ProofFile.Honest.K12.Light.SharedSmall.goes
#print axioms ProofFile.Honest.K12.Light.SharedSmall.frShort
#print axioms ProofFile.Honest.K12.Light.SharedSmall.colsTurned
