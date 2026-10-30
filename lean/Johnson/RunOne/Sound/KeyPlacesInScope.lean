-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Sound/KeyPlacesInScope.lean:
THE KEY FILE's DESCRIPTION's THREE TABLES OF PLACES AND ROUNDS AS CLOSED LITERALS, IN SCOPE: for
every block of each chain, in order: its chain, link, number, kind's label and number of rounds.

FIRST, WHAT A LABEL IS. A TAG IS THE BLOCK's OWN WORD FOR ITS KIND: `place` is a label that the
block's maker or a driver stamps; `wantedOk` holds the labels, in order, against the table `wanted`,
made in other files than the blocks'. WHICH block bears a label no table says.

What is said.
  `W₁`, `W₂`, `W₃`: three written lists of 19, 12 and 4 rows.
  `first_rows_full`, `shared_rows_full`, `second_rows_full`: the tables at `keyFull`'s ranges and
    shape are these lists: by evaluation in the kernel. `first_rows_no`, `shared_rows_no`: two
    controls: with one row's KIND turned the equation is refuted.
  `rounds_of_W`: the lists of rounds `L₁`, `L₂`, `L₃` (Johnson/RunOne/Sound/KeyListsInScope.lean)
    are these tables' second columns: so the two files' literals cannot drift.
  `rows_in_scope`: in scope, at an X that reads the parameter file, at any digest, where the maker
    and the source return and the tests on the plan and `wantedOk` say yes: each chain's rows
    (place, number of rounds) are `W₁`, `W₂`, `W₃`.
  `laid_rows_in_scope`: the same from the yes of `publicOfO o` and then `Key.keyDataAndDecisionAtFixedDigest`, at every o.
  `k3_in_scope`: an example of what is then one evaluation: the rows that bear K3 are numbers 4 and
    10 of the first chain.

Limits. As above; numbers of rounds, not the rounds. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.RunOne.Sound.KeyListsInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Sound

open OnBytes VerifiableInference.Desc
open Lk6.AtPlan (keyFull)
open Johnson.RunOne.Law.KeyInScope (five_in_scope shared_lin_in_scope)

/-- The first chain's rows, at the full size. -/
def W₁ : List (Place × ℕ) :=
  [(⟨1, none, 1, .K1⟩, 2), (⟨1, none, 2, .K1⟩, 2),
    (⟨1, some 0, 0, .frame⟩, 0), (⟨1, some 0, 1, .frame⟩, 0), (⟨1, some 0, 2, .K3⟩, 9581),
    (⟨1, some 0, 3, .frame⟩, 0), (⟨1, some 0, 4, .frame⟩, 0), (⟨1, some 0, 5, .frame⟩, 0),
    (⟨1, some 1, 0, .frame⟩, 0), (⟨1, some 1, 1, .frame⟩, 0), (⟨1, some 1, 2, .K3⟩, 9220),
    (⟨1, some 1, 3, .frame⟩, 0), (⟨1, some 1, 4, .frame⟩, 0), (⟨1, some 1, 5, .frame⟩, 0),
    (⟨1, none, 4, .frame⟩, 0), (⟨1, none, 5, .K12⟩, 23), (⟨1, none, 13, .K13⟩, 20),
    (⟨1, none, 14, .K1⟩, 2), (⟨1, none, 15, .frame⟩, 1)]

/-- The shared chain's. -/
def W₂ : List (Place × ℕ) :=
  [(⟨2, none, 0, .frame⟩, 0), (⟨2, none, 1, .K14⟩, 1), (⟨2, none, 2, .K1⟩, 2),
    (⟨2, none, 3, .K14⟩, 0), (⟨2, none, 4, .K14⟩, 1), (⟨2, none, 5, .K1⟩, 2),
    (⟨2, none, 6, .K14⟩, 0), (⟨2, none, 7, .K14⟩, 1), (⟨2, none, 8, .K14⟩, 1),
    (⟨2, none, 9, .K12⟩, 35), (⟨2, none, 10, .K12⟩, 24), (⟨2, none, 11, .frame⟩, 1)]

/-- The last chain's. -/
def W₃ : List (Place × ℕ) :=
  [(⟨3, none, 0, .K14⟩, 0), (⟨3, none, 1, .frame⟩, 0), (⟨3, none, 2, .K12⟩, 30),
    (⟨3, none, 3, .frame⟩, 0)]

/-- **The first chain's table at the written value**: by evaluation in the kernel. -/
theorem first_rows_full (one : Params.OneTime) (hr : one.ranges = keyFull.ranges.x)
    (hl : one.lin = keyFull.once.shape) : Key.wantedFirst one = W₁ := by
  unfold Key.wantedFirst
  rw [hr, hl]
  decide +kernel

/-- The shared chain's. -/
theorem shared_rows_full : Key.wantedShared keyFull.once.shape = W₂ := by
  decide +kernel

/-- The last chain's. -/
theorem second_rows_full : Key.wantedSecond keyFull.once.shape = W₃ := by
  decide +kernel

/-- A control: with one row's kind turned (the fifth: K3 to K4) the first equation is refuted. -/
theorem first_rows_no (one : Params.OneTime) (hr : one.ranges = keyFull.ranges.x)
    (hl : one.lin = keyFull.once.shape) :
    Key.wantedFirst one ≠ W₁.set 4 (⟨1, some 0, 2, .K4⟩, 9581) := by
  unfold Key.wantedFirst
  rw [hr, hl]
  decide +kernel

/-- A control: the same of the second (the second row: K14 to K13). -/
theorem shared_rows_no :
    Key.wantedShared keyFull.once.shape ≠ W₂.set 1 (⟨2, none, 1, .K13⟩, 1) := by
  decide +kernel

/-- The lists of rounds are these tables' second columns. -/
theorem rounds_of_W : W₁.map (·.2) = L₁ ∧ W₂.map (·.2) = L₂ ∧ W₃.map (·.2) = L₃ := by
  decide

/-- **The three tables as closed literals, in scope, at any digest.** -/
theorem rows_in_scope {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true)
    {Z : Model.Verify.Public} (hP : Johnson.RunOne.Law.AtFreeCfg.ReadOf Zp.pol Z)
    {cfg : ByteArray} {m : Johnson.G.OfPlan.Made} {X : Key.Source} {N : H2U.PlaceNums}
    {P : Key.LaterPlaces} (hm : Key.madeAt Z Zp.lay cfg = .ok m) (hX : Key.sourceOf m = .ok X)
    (hp : (Key.descriptionFromSource X N P).planOk = true) (hw : (Key.descriptionFromSource X N P).wantedOk = true) :
    rowsOf (Key.descriptionFromSource X N P).first.blocksInOrder = W₁ ∧ rowsOf (Key.descriptionFromSource X N P).shared.blocksInOrder = W₂ ∧
      rowsOf (Key.descriptionFromSource X N P).second.blocksInOrder = W₃ := by
  obtain ⟨h₁, h₂, h₃⟩ := desc_lists X N P hp hw
  obtain ⟨-, hr, hl, -, -⟩ := five_in_scope hZ hP hm hX hp
  have hs := shared_lin_in_scope hZ hP hm hX hp
  refine ⟨h₁.trans (first_rows_full _ hr hl), ?_, ?_⟩
  · rw [h₂, hs]
    exact shared_rows_full
  · rw [h₃, hs]
    exact second_rows_full

/-- **The same from the yes of the two in a row**, at every o. -/
theorem laid_rows_in_scope {o : Nat → ByteArray → ByteArray} {Zp : VerifierAndGoals.PublicFiles}
    (hZ : VerifierAndGoals.InScope Zp = true) {D : Maker.WholeD} {r : Key.KeyRun}
    (h : ((VerifiableInference.PlanWritten.publicOfO o Zp.pol Zp.KL (some Zp.lay)).bind fun Z =>
      Key.keyDataAndDecisionAtFixedDigest Z Zp.lay) = .ok (D, r)) :
    ∃ X N P, r = ((Key.descriptionFromSource X N P).pull Key.keyInstanceOfOutOfDomainSample).run ∧
      (Key.descriptionFromSource X N P).data "key file" = .ok D ∧
      rowsOf (Key.descriptionFromSource X N P).first.blocksInOrder = W₁ ∧ rowsOf (Key.descriptionFromSource X N P).shared.blocksInOrder = W₂ ∧
      rowsOf (Key.descriptionFromSource X N P).second.blocksInOrder = W₃ := by
  cases hZ' : VerifiableInference.PlanWritten.publicOfO o Zp.pol Zp.KL (some Zp.lay) with
  | error e =>
    rw [hZ'] at h
    cases h
  | ok Z =>
    rw [hZ'] at h
    obtain ⟨m, X, N, P, hm, hX, -, -, -, hp, hw, -, -, hd, hr⟩ :=
      Key.laidFixed_is Z Zp.lay D r h
    exact ⟨X, N, P, hr, hd, rows_in_scope hZ
      (Johnson.RunOne.Law.ReadAtO.readOf_publicOfO hZ') hm hX hp hw⟩

/-- An example of what is then one evaluation: which rows bear K3. -/
theorem k3_in_scope :
    ((W₁.zipIdx.filter fun x => x.1.1.kind == .K3).map (·.2) = [4, 10]) ∧
      (W₂.all fun x => x.1.kind != .K3) = true ∧ (W₃.all fun x => x.1.kind != .K3) = true := by
  decide

end Johnson.RunOne.Sound

#print axioms Johnson.RunOne.Sound.first_rows_full
#print axioms Johnson.RunOne.Sound.shared_rows_full
#print axioms Johnson.RunOne.Sound.second_rows_full
#print axioms Johnson.RunOne.Sound.first_rows_no
#print axioms Johnson.RunOne.Sound.shared_rows_no
#print axioms Johnson.RunOne.Sound.rounds_of_W
#print axioms Johnson.RunOne.Sound.rows_in_scope
#print axioms Johnson.RunOne.Sound.laid_rows_in_scope
#print axioms Johnson.RunOne.Sound.k3_in_scope
