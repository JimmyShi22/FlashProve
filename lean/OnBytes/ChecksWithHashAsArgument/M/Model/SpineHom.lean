-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ChecksWithHashAsArgument/M/Model/SpineHom.lean: a morphism of monads passes through the rest of the spine
over m: the proof file's road, the digests, the stages, the calls up to wholeCall.
MADE BY A PROGRAM from a file of the same name that this project's authors wrote over an earlier
arrangement of these definitions, which is not in this tree: the program turned names, imports,
opens and the spelling of calls alone. Some declarations differ from what the program made: by the
authors' search and replace, and by hand.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.ChecksWithHashAsArgument.M.Model.Verify
import OnBytes.ChecksWithHashAsArgument.M.Model.ExceptHom

set_option autoImplicit false

namespace OnBytes.TwoPort.M.SpineHom

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

variable {m n : Type → Type} [Monad m] [Monad n] (φ : Run.Hom m n) (h : HashM m)

/-! ## Guards -/

theorem rel_guard {β : Type} {c : Prop} [Decidable c] (e : String) {g : PUnit → Reading m β}
    {g' : PUnit → Reading n β} (hg : ∀ y, Rel φ (g y) (g' y)) :
    Rel φ (if c then throw e >>= g else pure PUnit.unit >>= g)
      (if c then throw e >>= g' else pure PUnit.unit >>= g') := by
  split
  · exact rel_bind φ (rel_throw φ _) hg
  · exact rel_bind φ (rel_pure φ _) hg

/-! ## The proof file's road -/

theorem rel_readProof (c : ProofChains) (table : TableName) (copy : Nat) (request words : ByteArray)
    (block : Blk FirstEnd) (file : ByteArray) :
    Rel φ (readProof h c table copy request words block file)
      (readProof (φ.on h) c table copy request words block file) := by
  unfold readProof
  dsimp only
  split <;> refine rel_bind φ (by first | exact rel_throw φ _ | exact rel_pure φ _) fun x => ?_
  all_goals
    obtain ⟨madeOn, i⟩ := x
    dsimp only
    refine rel_guard φ _ fun _ => ?_
    refine rel_guard φ _ fun _ => ?_
    refine rel_bind φ (rel_need φ _ _) fun x => ?_
    obtain ⟨rounds1, dry⟩ := x
    refine rel_bind φ (rel_need φ _ _) fun spec1 => ?_
    refine rel_bind φ (rel_readNamed φ h _ _ _ _) fun first => ?_
    refine rel_bind φ (KeyHom.rel_readTail φ h _ _ _ _) fun r => ?_
    exact rel_guard φ _ fun _ => rel_pure φ _

theorem app_proofCheck (c : ProofChains) (table : TableName) (copy : Nat)
    (request words : ByteArray)
    (reply : E) (links : Blk LinksResult) (file : ByteArray) :
    φ.app (Proof.check h c table copy request words reply links file) =
      Proof.check (φ.on h) c table copy request words reply links file := by
  unfold Proof.check
  dsimp only
  simp only [φ.app_bind]
  rw [RoadHom.app_fromStart φ _ _ (rel_readProof φ h _ _ _ _ _ _ _)]
  refine congrArg _ (funext fun r => ?_)
  cases r with
  | error why => exact φ.app_pure _
  | ok r =>
    simp only []
    split <;> exact φ.app_pure _

/-! ## The digests -/

theorem app_seedsOf (s : IndexShape) (cfg : ByteArray) (t : TableName) :
    φ.app (Key.seedsOf h s cfg t) = Key.seedsOf (φ.on h) s cfg t := by
  unfold Key.seedsOf
  exact RoadHom.app_recordSeeds φ h _ _ _ _

theorem app_commitmentId (s : IndexShape) (cfg : ByteArray) (t : TableName) :
    φ.app (Key.commitmentId h s cfg t) = Key.commitmentId (φ.on h) s cfg t := by
  unfold Key.commitmentId
  rw [φ.app_bind, app_seedsOf]
  rfl

theorem app_configurationDigest (files : List ByteArray) :
    φ.app (configurationDigest h files) = configurationDigest (φ.on h) files := rfl

theorem app_configuration (pol layout KL : ByteArray) :
    φ.app (configuration h pol layout KL) = configuration (φ.on h) pol layout KL := rfl

/-! ## The stages -/

theorem relE_namedT {α : Type} {x : ExceptT String m α} {x' : ExceptT String n α}
    (hx : RelE φ x x') : RelE φ (namedT x) (namedT x') := by
  unfold namedT
  refine relE_mk φ ?_
  rw [φ.app_bind, hx]
  refine congrArg _ (funext fun r => ?_)
  exact φ.app_pure _

variable [LawfulMonad m] [LawfulMonad n]

theorem relE_commonOf (X : Public) (cfg : ByteArray) (chains : Chains) (built : LinksH)
    (key : ByteArray) (asked : String) :
    RelE φ (commonOf h X cfg chains built key asked)
      (commonOf (φ.on h) X cfg chains built key asked) := by
  unfold commonOf
  dsimp only
  split <;> refine relE_bind φ (by first | exact relE_pure φ _ | exact relE_liftE φ _) fun first => ?_
  all_goals
    refine relE_bind φ (relE_lift φ (app_commitmentId φ h _ _ _)) fun id => ?_
    refine relE_bind φ (relE_liftE φ _) fun _ => ?_
    exact relE_pure φ _

theorem relE_keyStage (C : Common) (asked : Nat) (key : ByteArray) :
    RelE φ (keyStage h C asked key) (keyStage (φ.on h) C asked key) := by
  unfold keyStage
  refine relE_bind φ (relE_liftE φ _) fun a => ?_
  refine relE_bind φ (relE_lift φ (KeyHom.app_check φ h _ _)) fun r => ?_
  cases r with
  | error e => exact relE_liftE φ _
  | ok t => exact relE_bind φ (relE_liftE φ _) fun _ => relE_pure φ _

theorem relE_leafStage (C : Common) (asked : Nat) (entry : ByteArray) :
    RelE φ (leafStage h C asked entry) (leafStage (φ.on h) C asked entry) := by
  unfold leafStage
  refine relE_bind φ (relE_liftE φ _) fun a => ?_
  refine relE_bind φ (relE_lift φ (RoadHom.app_check φ h _ _ _)) fun r => ?_
  cases r with
  | error e => exact relE_liftE φ _
  | ok t => exact relE_bind φ (relE_liftE φ _) fun _ => relE_pure φ _

omit [LawfulMonad m] [LawfulMonad n] in
/-- The request's item, its digest asked of hr. -/
theorem app_requestItem (hr : ByteArray → m (Option ByteArray)) (a b c : ByteArray) :
    φ.app (Proof.requestItem hr a b c) = Proof.requestItem (fun x => φ.app (hr x)) a b c := by
  unfold Proof.requestItem
  simp only [φ.app_bind, φ.app_pure]

theorem relE_requestRun (hr : ByteArray → m (Option ByteArray)) (C : Common)
    (o : Options) (r : Read)
    (entry : ByteArray) :
    RelE φ (requestRun h hr C o r entry)
      (requestRun (φ.on h) (fun x => φ.app (hr x)) C o r entry) := by
  unfold requestRun
  dsimp only
  refine relE_bind φ (relE_liftE φ _) fun _ => ?_
  refine relE_bind φ (relE_liftE φ _) fun so => ?_
  refine relE_bind φ (relE_liftE φ _) fun cov => ?_
  refine relE_bind φ (relE_liftE φ _) fun further => ?_
  refine relE_bind φ (relE_liftE φ _) fun a => ?_
  refine relE_bind φ (relE_lift φ (app_requestItem φ hr _ _ _)) fun x => ?_
  split <;> refine relE_bind φ (by first | exact relE_pure φ _ | exact relE_throw φ _) fun item => ?_
  all_goals
    refine relE_bind φ (relE_liftE φ _) fun _ => ?_
    refine relE_bind φ (relE_liftE φ _) fun ls => ?_
    refine relE_bind φ (relE_lift φ (app_proofCheck φ h _ _ _ _ _ _ _ _)) fun v => ?_
    exact relE_pure φ _

theorem relE_requestStage (hr : ByteArray → m (Option ByteArray)) (C : Common) (o : Options)
    (r : Read) (entry : ByteArray) :
    RelE φ (requestStage h hr C o r entry)
      (requestStage (φ.on h) (fun x => φ.app (hr x)) C o r entry) := by
  unfold requestStage
  refine relE_bind φ (relE_namedT φ (relE_requestRun φ h hr _ _ _ _)) fun x => ?_
  split
  · exact relE_throw φ _
  · exact relE_bind φ (relE_liftE φ _) fun _ => relE_pure φ _

/-! ## The calls -/

theorem relE_planned (pol KL : ByteArray) (layout : Option ByteArray) :
    RelE φ (planned h pol KL layout) (planned (φ.on h) pol KL layout) := by
  unfold planned
  refine relE_bind φ (relE_liftE φ _) fun X => ?_
  refine relE_bind φ (relE_lift φ (app_configuration φ h _ _ _)) fun cfg => ?_
  refine relE_bind φ (relE_liftE φ _) fun chains => ?_
  refine relE_bind φ (relE_liftE φ _) fun built => ?_
  exact relE_pure φ _

theorem relE_common (p : Verify.Planned) (r : Read) :
    RelE φ (Planned.common h p r) (Planned.common (φ.on h) p r) := relE_commonOf φ h _ _ _ _ _ _

theorem relE_commonOfCall (r : Read) :
    RelE φ (commonOfCall h r) (commonOfCall (φ.on h) r) := by
  unfold commonOfCall
  exact relE_bind φ (relE_namedT φ (relE_planned φ h _ _ _)) fun p => relE_common φ h p r

theorem app_stagesOf (hr : ByteArray → m (Option ByteArray)) (o : Options) (r : Read)
    (entry : ByteArray) :
    φ.app (Verify.stagesOf h hr o r entry) =
      Verify.stagesOf (φ.on h) (fun x => φ.app (hr x)) o r entry := by
  unfold Verify.stagesOf
  rw [φ.app_bind, relE_commonOfCall φ h r]
  refine congrArg _ (funext fun x => ?_)
  cases x with
  | error x => exact φ.app_pure _
  | ok C =>
    simp only [φ.app_bind, φ.app_pure]
    rw [relE_keyStage φ h C o.bits r.key, relE_leafStage φ h C o.bits entry,
      relE_requestStage φ h hr C o r entry]

theorem app_wholeCall (hr : ByteArray → m (Option ByteArray)) (o : Options) (f : Files) :
    φ.app (wholeCall h hr o f) = wholeCall (φ.on h) (fun x => φ.app (hr x)) o f := by
  unfold wholeCall
  split
  · exact φ.app_pure _
  · split
    · exact φ.app_pure _
    · simp only [φ.app_bind, φ.app_pure, app_stagesOf]

theorem app_partCall (o : Options) (f : Files) (part : StageName)
    (run : Common → Read → ExceptT Refused m Found) (run' : Common → Read → ExceptT Refused n Found)
    (hr : ∀ C r, RelE φ (run C r) (run' C r)) :
    φ.app (partCall h o f part run) = partCall (φ.on h) o f part run' := by
  unfold partCall
  split
  · exact φ.app_pure _
  · split
    · exact φ.app_pure _
    · rename_i r _
      simp only [φ.app_bind]
      rw [relE_commonOfCall φ h r]
      refine congrArg _ (funext fun x => ?_)
      cases x with
      | error x => simp only [φ.app_bind, φ.app_pure]
      | ok C =>
        simp only [φ.app_bind, φ.app_pure]
        rw [hr C r]

theorem app_keyCall (o : Options) (f : Files) :
    φ.app (keyCall h o f) = keyCall (φ.on h) o f :=
  app_partCall φ h o f .key _ _ fun C r => relE_keyStage φ h C o.bits r.key

theorem app_leafCall (o : Options) (f : Files) :
    φ.app (leafCall h o f) = leafCall (φ.on h) o f := by
  unfold leafCall
  split
  · exact φ.app_pure _
  · exact app_partCall φ h o f .leaf _ _ fun C _ => relE_leafStage φ h C o.bits _

theorem relE_planBytes (bits : Nat) (policy KL : FileIn) (layout : Option FileIn) :
    RelE φ (planBytes h bits policy KL layout) (planBytes (φ.on h) bits policy KL layout) := by
  unfold planBytes
  refine relE_bind φ (relE_liftE φ _) fun x => ?_
  obtain ⟨pol, KL', layout'⟩ := x
  refine relE_bind φ ?_ fun p => ?_
  · refine relE_mk φ ?_
    rw [φ.app_bind, relE_planned φ h _ _ _]
    refine congrArg _ (funext fun r => ?_)
    exact φ.app_pure _
  refine relE_bind φ (relE_liftE φ _) fun _ => ?_
  exact relE_pure φ _

end OnBytes.TwoPort.M.SpineHom
