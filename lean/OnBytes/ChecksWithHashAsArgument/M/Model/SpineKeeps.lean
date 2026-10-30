-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ChecksWithHashAsArgument/M/Model/SpineKeeps.lean: a property that pure has and bind keeps passes through the
rest of the spine over m; and two theorems on wholeCall over the monad of trees of queries.
MADE BY A PROGRAM from a file of the same name that this project's authors wrote over an earlier
arrangement of these definitions, which is not in this tree: the program turned names, imports,
opens and the spelling of calls alone. Some declarations differ from what the program made: by the
authors' search and replace, and by hand.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.ChecksWithHashAsArgument.M.Model.SpineHom
import OnBytes.ChecksWithHashAsArgument.M.Entry.RoadLands

set_option autoImplicit false

namespace OnBytes.TwoPort.M.SpineKeeps

open OnBytes.Proof hiding climb readPlace Reading need Reading.fromStart readerName readNamed
    requestItem readTail readProof check
open OnBytes.TwoPort.M.Proof
open OnBytes.Params hiding configurationDigest
open OnBytes.TwoPort.M.Params
open OnBytes.Model hiding Verify.configuration Verify.commonOf Verify.keyStage Verify.leafStage
    Verify.requestRun Verify.requestStage Verify.planned Verify.Planned.common Verify.commonOfCall
    Verify.stagesOf Verify.wholeCall Verify.partCall Verify.keyCall Verify.leafCall Verify.planBytes
open OnBytes.TwoPort.M.Model
open OnBytes.Model.Verify hiding configuration commonOf keyStage leafStage requestRun requestStage
    planned Planned.common commonOfCall stagesOf wholeCall partCall keyCall leafCall planBytes
open OnBytes.TwoPort.M.Model.Verify
open OnBytes.Model.Stages

variable {m : Type → Type} [Monad m] (q : Keeps m)

theorem okR_guard {β : Type} {c : Prop} [Decidable c] (e : String) {g : PUnit → Reading m β}
    (hg : ∀ y, OkR q (g y)) :
    OkR q (if c then throw e >>= g else pure PUnit.unit >>= g) := by
  split
  · exact okR_bind q (okR_throw q _) hg
  · exact okR_bind q (okR_pure q _) hg

theorem okE_namedT {α : Type} {x : ExceptT String m α} (hx : OkE q x) : OkE q (namedT x) := by
  unfold namedT
  exact q.ok_bind _ _ hx fun _ => q.ok_pure _

variable (h : HashM m) (hh : ∀ n t i s b, q.ok (h n t i s b))
include hh

theorem okR_readProof (c : ProofChains) (table : TableName) (copy : Nat) (request words : ByteArray)
    (block : Blk FirstEnd) (file : ByteArray) :
    OkR q (readProof h c table copy request words block file) := by
  unfold readProof
  dsimp only
  split <;> refine okR_bind q (by first | exact okR_throw q _ | exact okR_pure q _) fun x => ?_
  all_goals
    obtain ⟨madeOn, i⟩ := x
    dsimp only
    refine okR_guard q _ fun _ => ?_
    refine okR_guard q _ fun _ => ?_
    refine okR_bind q (RoadKeeps.ok_need q _ _) fun x => ?_
    obtain ⟨rounds1, dry⟩ := x
    refine okR_bind q (RoadKeeps.ok_need q _ _) fun spec1 => ?_
    refine okR_bind q (RoadKeeps.ok_readNamed q h hh _ _ _ _) fun first => ?_
    refine okR_bind q (KeyHom.okR_readTail h q hh _ _ _ _) fun r => ?_
    exact okR_guard q _ fun _ => okR_pure q _

theorem ok_proofCheck (c : ProofChains) (table : TableName) (copy : Nat) (request words : ByteArray)
    (reply : E) (links : Blk LinksResult) (file : ByteArray) :
    q.ok (Proof.check h c table copy request words reply links file) := by
  unfold Proof.check
  dsimp only
  refine q.ok_bind _ _ (RoadKeeps.ok_fromStart q _ (okR_readProof q h hh _ _ _ _ _ _ _)) fun r => ?_
  cases r with
  | error why => exact q.ok_pure _
  | ok r =>
    simp only []
    split <;> exact q.ok_pure _

theorem ok_seedsOf (s : IndexShape) (cfg : ByteArray) (t : TableName) :
    q.ok (Key.seedsOf h s cfg t) := by
  unfold Key.seedsOf
  exact RoadKeeps.ok_recordSeeds q h hh _ _ _ _

theorem ok_commitmentId (s : IndexShape) (cfg : ByteArray) (t : TableName) :
    q.ok (Key.commitmentId h s cfg t) := by
  unfold Key.commitmentId
  exact q.ok_bind _ _ (ok_seedsOf q h hh _ _ _) fun _ => hh _ _ _ _ _

theorem ok_configurationDigest (files : List ByteArray) : q.ok (configurationDigest h files) :=
  hh _ _ _ _ _

theorem ok_configuration (pol layout KL : ByteArray) : q.ok (configuration h pol layout KL) :=
  hh _ _ _ _ _

variable [LawfulMonad m]

theorem okE_commonOf (X : Public) (cfg : ByteArray) (chains : Chains) (built : LinksH)
    (key : ByteArray) (asked : String) : OkE q (commonOf h X cfg chains built key asked) := by
  unfold commonOf
  dsimp only
  split <;> refine okE_bind q (by first | exact okE_pure q _ | exact okE_liftE q _) fun first => ?_
  all_goals
    refine okE_bind q (okE_lift q (ok_commitmentId q h hh _ _ _)) fun id => ?_
    refine okE_bind q (okE_liftE q _) fun _ => ?_
    exact okE_pure q _

theorem okE_keyStage (C : Common) (asked : Nat) (key : ByteArray) :
    OkE q (keyStage h C asked key) := by
  unfold keyStage
  refine okE_bind q (okE_liftE q _) fun a => ?_
  refine okE_bind q (okE_lift q (KeyHom.ok_check h q hh _ _)) fun r => ?_
  cases r with
  | error e => exact okE_liftE q _
  | ok t => exact okE_bind q (okE_liftE q _) fun _ => okE_pure q _

theorem okE_leafStage (C : Common) (asked : Nat) (entry : ByteArray) :
    OkE q (leafStage h C asked entry) := by
  unfold leafStage
  refine okE_bind q (okE_liftE q _) fun a => ?_
  refine okE_bind q (okE_lift q (RoadKeeps.ok_check q h hh _ _ _)) fun r => ?_
  cases r with
  | error e => exact okE_liftE q _
  | ok t => exact okE_bind q (okE_liftE q _) fun _ => okE_pure q _

omit hh [LawfulMonad m] in
/-- The request's item, its digest asked of hr. -/
theorem ok_requestItem (hr : ByteArray → m (Option ByteArray)) (hhr : ∀ x, q.ok (hr x))
    (a b c : ByteArray) : q.ok (Proof.requestItem hr a b c) := by
  unfold Proof.requestItem
  exact q.ok_bind _ _ (hhr _) fun _ => q.ok_pure _

theorem okE_requestRun (hr : ByteArray → m (Option ByteArray)) (hhr : ∀ x, q.ok (hr x)) (C : Common)
    (o : Options) (r : Read) (entry : ByteArray) :
    OkE q (requestRun h hr C o r entry) := by
  unfold requestRun
  dsimp only
  refine okE_bind q (okE_liftE q _) fun _ => ?_
  refine okE_bind q (okE_liftE q _) fun so => ?_
  refine okE_bind q (okE_liftE q _) fun cov => ?_
  refine okE_bind q (okE_liftE q _) fun further => ?_
  refine okE_bind q (okE_liftE q _) fun a => ?_
  refine okE_bind q (okE_lift q (ok_requestItem q hr hhr _ _ _)) fun x => ?_
  split <;> refine okE_bind q (by first | exact okE_pure q _ | exact okE_throw q _) fun item => ?_
  all_goals
    refine okE_bind q (okE_liftE q _) fun _ => ?_
    refine okE_bind q (okE_liftE q _) fun ls => ?_
    refine okE_bind q (okE_lift q (ok_proofCheck q h hh _ _ _ _ _ _ _ _)) fun v => ?_
    exact okE_pure q _

theorem okE_requestStage (hr : ByteArray → m (Option ByteArray)) (hhr : ∀ x, q.ok (hr x))
    (C : Common) (o : Options) (r : Read) (entry : ByteArray) :
    OkE q (requestStage h hr C o r entry) := by
  unfold requestStage
  refine okE_bind q (okE_namedT q (okE_requestRun q h hh hr hhr _ _ _ _)) fun x => ?_
  split
  · exact okE_throw q _
  · exact okE_bind q (okE_liftE q _) fun _ => okE_pure q _

theorem okE_planned (pol KL : ByteArray) (layout : Option ByteArray) :
    OkE q (planned h pol KL layout) := by
  unfold planned
  refine okE_bind q (okE_liftE q _) fun X => ?_
  refine okE_bind q (okE_lift q (ok_configuration q h hh _ _ _)) fun cfg => ?_
  refine okE_bind q (okE_liftE q _) fun chains => ?_
  refine okE_bind q (okE_liftE q _) fun built => ?_
  exact okE_pure q _

theorem okE_common (p : Verify.Planned) (r : Read) : OkE q (Planned.common h p r) :=
  okE_commonOf q h hh _ _ _ _ _ _

theorem okE_commonOfCall (r : Read) : OkE q (commonOfCall h r) := by
  unfold commonOfCall
  exact okE_bind q (okE_namedT q (okE_planned q h hh _ _ _)) fun p => okE_common q h hh p r

theorem ok_stagesOf (hr : ByteArray → m (Option ByteArray)) (hhr : ∀ x, q.ok (hr x)) (o : Options)
    (r : Read) (entry : ByteArray) :
    q.ok (Verify.stagesOf h hr o r entry) := by
  unfold Verify.stagesOf
  refine q.ok_bind _ _ (okE_commonOfCall q h hh r) fun x => ?_
  cases x with
  | error x => exact q.ok_pure _
  | ok C =>
    refine q.ok_bind _ _ (okE_keyStage q h hh C o.bits r.key) fun _ => ?_
    refine q.ok_bind _ _ (okE_leafStage q h hh C o.bits entry) fun _ => ?_
    exact q.ok_bind _ _ (okE_requestStage q h hh hr hhr C o r entry) fun _ => q.ok_pure _

theorem ok_wholeCall (hr : ByteArray → m (Option ByteArray)) (hhr : ∀ x, q.ok (hr x)) (o : Options)
    (f : Files) : q.ok (wholeCall h hr o f) := by
  unfold wholeCall
  split
  · exact q.ok_pure _
  · split
    · exact q.ok_pure _
    · exact q.ok_bind _ _ (ok_stagesOf q h hh hr hhr _ _ _) fun _ => q.ok_pure _

theorem ok_partCall (o : Options) (f : Files) (part : StageName)
    (run : Common → Read → ExceptT Refused m Found) (hr : ∀ C r, OkE q (run C r)) :
    q.ok (partCall h o f part run) := by
  unfold partCall
  split
  · exact q.ok_pure _
  · split
    · exact q.ok_pure _
    · rename_i r _
      refine q.ok_bind _ _ (okE_commonOfCall q h hh r) fun x => ?_
      cases x with
      | error x => exact q.ok_bind _ _ (q.ok_pure _) fun _ => q.ok_pure _
      | ok C =>
        exact q.ok_bind _ _ (hr C r) fun _ => q.ok_bind _ _ (q.ok_pure _) fun _ => q.ok_pure _

theorem ok_keyCall (o : Options) (f : Files) : q.ok (keyCall h o f) :=
  ok_partCall q h hh o f .key _ fun C r => okE_keyStage q h hh C o.bits r.key

theorem ok_leafCall (o : Options) (f : Files) : q.ok (leafCall h o f) := by
  unfold leafCall
  split
  · exact q.ok_pure _
  · exact ok_partCall q h hh o f .leaf _ fun C _ => okE_leafStage q h hh C o.bits _

theorem okE_planBytes (bits : Nat) (policy KL : FileIn) (layout : Option FileIn) :
    OkE q (planBytes h bits policy KL layout) := by
  unfold planBytes
  refine okE_bind q (okE_liftE q _) fun x => ?_
  obtain ⟨pol, KL', layout'⟩ := x
  refine okE_bind q ?_ fun p => ?_
  · exact q.ok_bind _ _ (okE_planned q h hh _ _ _) fun _ => q.ok_pure _
  refine okE_bind q (okE_liftE q _) fun _ => ?_
  exact okE_pure q _

end OnBytes.TwoPort.M.SpineKeeps

namespace OnBytes.TwoPort.M.SpineLands

open _root_.ZKCP
open _root_.Run
open OnBytes.Model hiding Verify.configuration Verify.commonOf Verify.keyStage Verify.leafStage
    Verify.requestRun Verify.requestStage Verify.planned Verify.Planned.common Verify.commonOfCall
    Verify.stagesOf Verify.wholeCall Verify.partCall Verify.keyCall Verify.leafCall Verify.planBytes
open OnBytes.TwoPort.M.Model
open OnBytes.Model.Verify hiding configuration commonOf keyStage leafStage requestRun requestStage
    planned Planned.common commonOfCall stagesOf wholeCall partCall keyCall leafCall planBytes
open OnBytes.TwoPort.M.Model.Verify

/-- The whole call that asks, run at f, is the whole call at the hash over the function that f
induces. -/
theorem wholeCall_det (f : _root_.ZKCP.Oracle 256)
    (hq : ByteArray → _root_.ZKCP.OComp 256 (Option ByteArray)) (o : Options) (x : Files) :
    (wholeCall (Fmt.HM askB) hq o x).det f =
      wholeCall (m := Id) (Fmt.HO (oB f)) (fun b => (hq b).det f) o x := by
  have e := SpineHom.app_wholeCall (detHom f) (Fmt.HM askB) hq o x
  rw [detHom_on_HM] at e
  exact e

/-- The whole call that asks tosses no coin. -/
theorem wholeCall_noCoin (hq : ByteArray → _root_.ZKCP.OComp 256 (Option ByteArray))
    (hhq : ∀ b, (hq b).NoCoin) (o : Options) (x : Files) :
    (wholeCall (Fmt.HM askB) hq o x).NoCoin :=
  SpineKeeps.ok_wholeCall (RoadLands.noCoinKeeps 256) (Fmt.HM askB)
    (fun n t i s b => noCoin_HM n t i s b) hq hhq o x

end OnBytes.TwoPort.M.SpineLands
