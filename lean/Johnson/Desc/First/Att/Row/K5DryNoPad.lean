-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Row/K5DryNoPad.lean: kind K5: **THE TWIN OF THE CLAIMS' TESTS ON THE PLAN
(claimsOkT, Johnson/Desc/First/Att/Row/K5DryTwin.lean) IS "THE PADDING KEYS ARE 0" AND THE REST: AN
EQUATION AT EVERY ARGUMENT, WITHOUT A PREMISE.**
General laws. NOTHING IS EVALUATED; NO WRITTEN VALUE IS NAMED.
WHY. The test asks padKeyOk (Johnson/Desc/First/Att/ClaimsOk.lean: at each call that is no
softmax-table call the padding key is 0) TWICE: as its first conjunct, and again as the first line
of paddingLaid (Johnson/Desc/First/Att/RunsP.lean), inside the run "keys": the same Bool, sign for
sign. A padding key is one entry of a call's table (CallG.padKey, Johnson/Desc/First/Att/Geo.lean).
Where padKeyOk is had by a law, the rest (claimsOkQ) can be asked by itself.
WHAT IT DOES NOT REACH: claimsOkQ STILL NAMES padKey IN ONE PLACE: Runs.padTerm (RunsP.lean), called
in callKFD beneath claim4, at the softmax-table calls, inside a form that no test reads. AND
claimsOkQ AT A PLAN IS STILL A WALK AT THAT PLAN: what such a walk costs Lean's kernel where the
plan is no written value is not touched by this file.
A NEIGHBOUR, NO TWIN: K5Law.keys_iff (Johnson/Desc/First/Att/Claims/Top.lean; it proves the sentence
K5Law.Spec.KeysIff): an iff on keysRun's return; here: equations of texts.
THE TEXTS paddingLaidQ · keysRunQ · dryOkQ ARE THE KIND's OWN (dryOkQ: the twin's) WITH THE NAMED
TURN ALONE.

Main names (namespace VerifiableInference.Desc.First.Att.P, beside the texts that they mirror):
  Runs.paddingLaidQ · Runs.paddingLaid_Q · Runs.keysRunQ · Runs.keysRun_Q · dryOkQ · dryOkT_Q
    (each law under padKeyOk = true).
  claimsOkQ · **claimsOkT_Q : claimsOkT c K k3 planesOk nzx =
    (padKeyOk c.geo && claimsOkQ c K k3 planesOk nzx)** · claimsOkAtQ ·
    **claimsOkAtT_Q : claimsOkAtT A = (padKeyOk (geoOf A.S) && claimsOkAtQ A)**.
IS IT EMPTY HERE? The two chief equations have no premise: nothing to meet.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Row.K5DryTwin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes
open OnBytes.Model (Aff)

namespace Runs

/-- paddingLaid's text (Johnson/Desc/First/Att/RunsP.lean) less its first test. -/
def paddingLaidQ (S : Geo) (k3 : PadIn) : W Unit := do
  let some laid := laidPadding S k3 | refuse "internal-forest-pub"
  mustAs "internal-forest-padding-places" (laid == k3.pub)

/-- Where the test on the padding keys accepts, the first test of paddingLaid passes: it is the same
Bool. -/
theorem paddingLaid_Q {S : Geo} (k3 : PadIn) (h : padKeyOk S = true) : paddingLaid S k3 = paddingLaidQ S k3 := by
  have h' : (S.calls.all fun c => c.tab == .kfd || c.padKey == 0) = true := h
  unfold paddingLaid paddingLaidQ
  rw [h']
  rfl

/-- keysRun's text with paddingLaidQ. -/
def keysRunQ (h : In) (k3 : PadIn) (j : JoinsP) : Option (Array Aff) :=
  (gather 0 (do
    allJoined j
    paddingLaidQ h.g k3)).map fun _ => j.kf

theorem keysRun_Q {i : In} (k3 : PadIn) (j : JoinsP) (h : padKeyOk i.g = true) : keysRun i k3 j = keysRunQ i k3 j := by
  unfold keysRun keysRunQ
  rw [paddingLaid_Q k3 h]

end Runs

/-- the dry run's text with keysRunQ. -/
def dryOkQ (c : ParC) (K : Nat) (k3 : Runs.PadIn) (planesOk : Bool) (nzx : Nat) : Bool :=
  let g := c.geo
  (do
    let p ← blankPtsT g
    let t ← tablesPS g c.mats c.nW { zx := zeros nzx, planesOk := planesOk, phiB0 := zeros (2 ^ g.lmb), phiB1 := zeros (2 ^ g.lmb), phiP := zeros (2 ^ g.lmb) } p
    let i : Runs.In := { g := g, p := p, t := t, zk := blankZk g, iU3 := c.iU3 }
    let f ← Runs.firstRun i K
    let _ ← Runs.keysRunQ i k3 f.2
    let _ ← Runs.secondRun i K
    pure ()).isSome

theorem dryOkT_Q (c : ParC) (K : Nat) (k3 : Runs.PadIn) (planesOk : Bool) (nzx : Nat) (h : padKeyOk c.geo = true) :
    dryOkT c K k3 planesOk nzx = dryOkQ c K k3 planesOk nzx := by
  unfold dryOkT dryOkQ
  have e : ∀ (p : Pts) (t : TablesP) (j : Runs.JoinsP),
      Runs.keysRun { g := c.geo, p := p, t := t, zk := blankZk c.geo, iU3 := c.iU3 } k3 j =
        Runs.keysRunQ { g := c.geo, p := p, t := t, zk := blankZk c.geo, iU3 := c.iU3 } k3 j := fun p t j => Runs.keysRun_Q k3 j h
  simp only [e]

/-- the test's text less the test on the padding keys, in both places. -/
def claimsOkQ (c : ParC) (K : Nat) (k3 : Runs.PadIn) (planesOk : Bool) (nzx : Nat) : Bool :=
  Decidable.decide (c.geo.lt ≤ 16) && dryOkQ c K k3 planesOk nzx

/-- **THE TEST IS "THE PADDING KEYS ARE 0" AND THE REST, AT EVERY ARGUMENT.** -/
theorem claimsOkT_Q (c : ParC) (K : Nat) (k3 : Runs.PadIn) (planesOk : Bool) (nzx : Nat) :
    claimsOkT c K k3 planesOk nzx = (padKeyOk c.geo && claimsOkQ c K k3 planesOk nzx) := by
  unfold claimsOkT claimsOkQ
  cases h : padKeyOk c.geo with
  | false => rfl
  | true => rw [dryOkT_Q c K k3 planesOk nzx h, Bool.and_assoc]

/-- claimsOkAtT's text with claimsOkQ. -/
def claimsOkAtQ (A : Attention.Plan) : Bool :=
  claimsOkQ (parCOf A) (((A.seam.Fp.trees[A.iU3]?).map (·.K)).getD 0) (padOfO A.fs)
    (Look.planesOk A.fs A.S.cf.lmb) (A.fs.dT)

/-- **THE LIKE AT A PLAN.** -/
theorem claimsOkAtT_Q (A : Attention.Plan) : claimsOkAtT A = (padKeyOk (geoOf A.S) && claimsOkAtQ A) := by
  unfold claimsOkAtT claimsOkAtQ
  exact claimsOkT_Q _ _ _ _ _

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.Runs.paddingLaid_Q
#print axioms VerifiableInference.Desc.First.Att.P.Runs.keysRun_Q
#print axioms VerifiableInference.Desc.First.Att.P.dryOkT_Q
#print axioms VerifiableInference.Desc.First.Att.P.claimsOkT_Q
#print axioms VerifiableInference.Desc.First.Att.P.claimsOkAtT_Q
