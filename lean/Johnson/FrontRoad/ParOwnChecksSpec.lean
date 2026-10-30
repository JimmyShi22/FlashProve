-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/ParOwnChecksSpec.lean: statements only. Nine are on public data alone; the last
two are implications on a prover's sessions, which end in a bound on the measure of the private
aborts. At all public files in scope that can be read, under LaidAt, the planner's test on the range
checks (missedInTheChecks, OnBytes/Params/Gate.lean) passes at the checks of the parameters that
parOwn names (Johnson/FrontRoad/ParOwn.lean), at the four arguments at which the planner itself asks
it. So sessionStops_of_pinned and sessionStops_of_tiedOwn, at parOwn and at these four arguments,
need no premise on that test. Ten are proved in Johnson/FrontRoad/ParOwnChecks.lean; the control
Spec.premises_met_at_full in AtFullSide/Top/LaidAtFull.lean, in the side library.
Terms of this folder: Johnson/FrontRoad/Spec.lean.

What this file has (namespace OnBytes.FrontRoad).
  linesAt, oneTimeAt, columnsFirstAt, batchesAt   the four arguments, read off the public part Zp:
      the parameter file's lines as read (Zp.p.X.P.frame), and three numbers of the sizes in the
      planner's value (Zp.p.chains.made.sized): the columns of the key's test on the table, the
      columns drawn of the first table in a link, the batches that a stored copy covers. They are
      the arguments of the planner's own call (Params.configure, OnBytes/Params/Configure.lean; the
      field checks of Gates, E2E/GateOfConfigure.lean) in the run that made Zp: that of
      ProofFile.Plain.chainsOf (Johnson/Desc/ProofFile/PlanPlain.lean), a copy of the routine
      Verify.chainsOf (OnBytes/Model/VerifyChains.lean) of the verifier in OnBytes/Model/, which is
      the one that this file calls the verifier, at the constant fixedConfigurationDigest and with 0 bits asked, so
      that this call holds the lines' sec against no target. The verifier's own routine returns the
      same value at that constant (pub_chainsOf, Johnson/Desc/ProofFile/Law/PlainIsPlanned.lean:
      Verify.chainsOf Zp.p.X (some lay) fixedConfigurationDigest = .ok Zp.p.chains). A verifier's run hands it the
      digest of the three files in fixedConfigurationDigest's place; that the sizes do not hang on that argument is
      not said here.
  ownPars   the list of the premise hm of sessionStops_of_pinned_own: the parameters that parOwn
      names at the places of the first chain's members without the last.
  k8PlaceAt   the written place of the smallness test at the link l.
  parBent   for a negative test: parOwn with each place's number of combinations raised by 1.
  Spec.k8_places_front   the places of the kind K8 among the first chain's members without the last
      are the twenty-five written ones, in order; the last member is of the kind frame.
  Spec.pars_at_parOwn   what parOwn names along that list: at each link l below 25, in order, the
      pair of k8Par Zp G₀ Xl l and mats l; twenty-five pairs.
  Spec.checks_are_own   the checks of ownPars are the list that the verifier's function
      Verify.rangeChecksOf (OnBytes/Model/VerifySubproofs.lean) gives at Zp.p.X.
  Spec.lines_are_frame   a control: the lines in the planner's sizes are the parameter file's lines
      as read. No other statement here needs it.
  Spec.premises_met_at_full   a control: scope, the reading, protocolDataWellFormed and LaidAt hold together at the
      stored full-size files.
  Spec.planner_passes_at_parOwn   the planner's test says false at the checks of ownPars and the
      four arguments.
  Spec.sessionStops_of_pinned_files, Spec.sessionStops_of_tiedOwn_files   sessionStops_of_pinned_own
      and sessionStops_of_tiedOwn_own (Johnson/FrontRoad/ParOwn.lean) at the four arguments, without
      the premise hm. All their other premises stand.
  Spec.missed_at_none, Spec.none_not_own, Spec.bent_not_own   three negative tests. At the par that
      names none the planner's test says true, at all arguments (a fact on the empty list: Zp, Np
      and cF do not enter). The checks at that par are not the list that Verify.rangeChecksOf gives
      at Zp.p.X. Nor are the checks at parBent. That test tells the number of combinations alone: no
      test here would tell rows laid for columns, or the links in another order.

How it fits. In sessionStops_of_pinned_own the planner's test is a premise, hm, at free arguments l,
oneTime, columnsFirst and batches; at parOwn its list of checks is a function of the public files,
so hm could be false at all of them. Here it is a statement of its own, at the planner's own
arguments (Spec.planner_passes_at_parOwn). Words (member, half, part, public and private abort test,
stated share): Johnson/FrontRoad/SessionStopsPinned.lean. Not one of the release's goal statements.

Limits.
  The nine statements on public data say nothing of any prover; the two implications name none. The
      pin, hR and the premise on the cells or on the trace stay premises of the two implications; no
      parameters are known at which they hold together. No value is given for the bound.
  That any public files meet scope, hr and LaidAt together: Spec.premises_met_at_full says it of the
      stored full-size files (VerifierAndGoals.storedPublicFiles), with protocolDataWellFormed beside them; it is proved in the side
      library (AtFullSide/Top/LaidAtFull.lean, whose head says with which grade each piece comes:
      only a build of the side library shows a break in it, and no independent checker has replayed
      it), since one piece stands there and the main library imports nothing of that library. At the
      second named set (VerifierAndGoals.zGap) the pieces stand in two statements of the side library
      (headMember_zGap, AtFullSide/Top/HeadMemberAtGap.lean: the fields scope, reads and laid of its
      head; theLive_zGap, AtFullSide/Top/LiveAtPolicies.lean); and at all public files a yes of
      protocolDataWellFormed gives LaidAt (laid_of_live, E2E/TiedAtFiles.lean). In one statement a theorem of these
      files has them together at VerifierAndGoals.storedPublicFiles alone. At public files that do not meet the three,
      each statement here that has them as premises holds idly, the two negative tests on that
      function's list among them.
  mats is free, and does not enter the planner's test: the list of checks takes the parameters
      alone.
  It says what the planner asked and what it got. What the test achieves is not treated (the Limits
      of E2E/GateOfConfigure.lean).
  The full size alone: the written list of places (placesW, Johnson/IMR/WrittenList.lean) and the
      twenty-five links are the scope's.
  Nothing is said on hiding, completeness or soundness.
-/
import Johnson.FrontRoad.ParOwn

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open AtPublicFiles.AtFiles AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed
open OnBytes (TableKey)
open OnBytes.Flat (RecFull)
open OnBytes.Params (Lines RangeCheck missedInTheChecks clog2)
open OnBytes.Maker (WholeD)
open OnBytes.Model.Verify (publicOf)
open OnBytes.HonestTrace (Tr cellsC cellsSmall_cellOf ServesAt theTrace meetsAll_theTrace
  servesAt_iff_in_scope TraceHinge)
open Inst.Model (Instance ppref)
open VerifiableInference.Desc (Block Place KindName)
open VerifiableInference.Desc.First.K8 (Par)
open ProofFile.Honest (Prover ProverCoinCounts Sides Ready Coins ready)
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (protocolDataWellFormed)
open P5J

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off within this namespace,
so that no statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

/- Among all that this file imports, the search for this instance runs out of its budget. It is a
proposition, so whichever proof is found, the statements below are the same. -/
local instance (priority := high) nonemptyPadZ_parOwnChecksSpec : Nonempty PadZ :=
  pads_nonempty OnBytes.Slice.frS 402653181

/- The same of this one. -/
local instance (priority := high) nonemptyOfInhabited_parOwnChecksSpec {α : Type} [Inhabited α] :
    Nonempty α := ⟨default⟩

/-- The parameter file's lines as read. -/
def linesAt (Zp : ProofFile.Pub) : Lines := Zp.p.X.P.frame

/-- The columns of the key's test on the table, in the planner's sizes. -/
def oneTimeAt (Zp : ProofFile.Pub) : ℕ := Zp.p.chains.made.sized.key.once.shape.fold.columns

/-- The columns drawn of the first table in a link, in the planner's sizes. -/
def columnsFirstAt (Zp : ProofFile.Pub) : ℕ := Zp.p.chains.made.sized.link.shape.columnsFirst

/-- The batches that a stored copy covers, in the planner's sizes. -/
def batchesAt (Zp : ProofFile.Pub) : ℕ := Zp.p.chains.made.sized.proof.batch.batches

/-- The parameters that parOwn names at the places of the first chain's members without the last:
the list of the premise hm of sessionStops_of_pinned_own. -/
abbrev ownPars (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
    (mats : ℕ → List (ℕ × String × ℕ)) : List Par :=
  ((descZ Zp Np cF).first.blocksInOrder.dropLast.filterMap fun b => parOwn Zp mats b.place).map (·.1)

/-- The written place of the smallness test at the link l. -/
def k8PlaceAt (l : ℕ) : Place :=
  { chain := 1, link := some l, piece := if l = 24 then 6 else 5, kind := KindName.K8 }

/-- For a negative test: parOwn with each place's number of combinations raised by 1. -/
def parBent (Zp : ProofFile.Pub) (mats : ℕ → List (ℕ × String × ℕ)) (a : Place) :
    Option (Par × List (ℕ × String × ℕ)) :=
  (parOwn Zp mats a).map fun P => ({ P.1 with tau := P.1.tau + 1 }, P.2)

/-- **The places of the kind K8 among the first chain's members without the last are the twenty-five
written ones, in order; the last member is of the kind frame.** -/
def Spec.k8_places_front : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl), InScope Z = true →
    ∀ {pp : Inst.Model.ScalesAndPolicy}, readFiles Z = .ok pp → ∀ {D : WholeD} {r : LPFD.Full.RunPF},
    LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF →
    ((descZ Zp Np cF).first.blocksInOrder.dropLast.map (·.place)).filter (fun a => a.kind == KindName.K8) =
        (List.range 25).map k8PlaceAt ∧
      ((descZ Zp Np cF).first.blocksInOrder.getLast?).map (·.place.kind) = some KindName.frame

/-- **What parOwn names along the first chain without its last member**: at each link below 25, in
order, the description's own parameters and mats l; twenty-five pairs. -/
def Spec.pars_at_parOwn : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl), InScope Z = true →
    ∀ {pp : Inst.Model.ScalesAndPolicy}, readFiles Z = .ok pp → ∀ {D : WholeD} {r : LPFD.Full.RunPF},
    LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF →
    ∀ mats : ℕ → List (ℕ × String × ℕ),
    ∃ G₀, ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀ ∧
      ((descZ Zp Np cF).first.blocksInOrder.dropLast.filterMap fun b => parOwn Zp mats b.place) =
        (List.range 25).filterMap (fun l =>
          (G₀.built[l]?).map fun Xl => (ProofFile.k8Par Zp G₀ Xl l, mats l)) ∧
      ((descZ Zp Np cF).first.blocksInOrder.dropLast.filterMap fun b =>
        parOwn Zp mats b.place).length = 25

/-- **The checks of ownPars are the list that the verifier's function Verify.rangeChecksOf gives at
Zp.p.X.** -/
def Spec.checks_are_own : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl), InScope Z = true →
    ∀ {pp : Inst.Model.ScalesAndPolicy}, readFiles Z = .ok pp → ∀ {D : WholeD} {r : LPFD.Full.RunPF},
    LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF →
    ∀ mats : ℕ → List (ℕ × String × ℕ),
    OnBytes.Model.Verify.rangeChecksOf Zp.p.X = some (checksOfPars (ownPars Zp Np cF mats))

/-- A control; it counts as no goal, and no other statement here needs it. The lines in the
planner's sizes are the parameter file's lines as read, so all four arguments can be read off the
one value. Of the premises it wants the field pub of LaidAt alone. -/
def Spec.lines_are_frame : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl), InScope Z = true →
    ∀ {pp : Inst.Model.ScalesAndPolicy}, readFiles Z = .ok pp → ∀ {D : WholeD} {r : LPFD.Full.RunPF},
    LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF →
    Zp.p.chains.made.sized.lines = linesAt Zp

/-- **The planner's test passes at the checks of ownPars, at the planner's own four arguments.** -/
def Spec.planner_passes_at_parOwn : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl), InScope Z = true →
    ∀ {pp : Inst.Model.ScalesAndPolicy}, readFiles Z = .ok pp → ∀ {D : WholeD} {r : LPFD.Full.RunPF},
    LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF →
    ∀ mats : ℕ → List (ℕ × String × ℕ),
    missedInTheChecks (linesAt Zp) (checksOfPars (ownPars Zp Np cF mats)) (oneTimeAt Zp)
      (columnsFirstAt Zp) (batchesAt Zp) = false

/-- A control; it counts as no goal. **The public premises are met together at the stored full-size
files**: scope, the reading, protocolDataWellFormed and LaidAt. So the seven statements on public data that have
scope, the reading and LaidAt as premises do not hold idly. Of the two implications it meets these
four premises alone: their premises on a prover stay open, and they may still hold idly. -/
def Spec.premises_met_at_full : Prop :=
  ∃ (pp : Inst.Model.ScalesAndPolicy) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl),
    InScope VerifierAndGoals.storedPublicFiles = true ∧ readFiles VerifierAndGoals.storedPublicFiles = .ok pp ∧
      protocolDataWellFormed (asDescriptionFiles VerifierAndGoals.storedPublicFiles) = true ∧
      LaidAt OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.lay VerifierAndGoals.storedPublicFiles.KL D r Zp Np cF

/-- A negative test; it counts as no goal. At the par that names none the planner's test says true,
at all arguments. -/
def Spec.missed_at_none : Prop :=
  ∀ (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl) (l : Lines)
    (oneTime columnsFirst batches : ℕ),
    missedInTheChecks l (checksOfPars (((descZ Zp Np cF).first.blocksInOrder.dropLast.filterMap fun b =>
      (fun _ => none : Place → Option (Par × List (ℕ × String × ℕ))) b.place).map (·.1)))
      oneTime columnsFirst batches = true

/-- A negative test; it counts as no goal. The checks at the par that names none are not the list
that Verify.rangeChecksOf gives at Zp.p.X. -/
def Spec.none_not_own : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl), InScope Z = true →
    ∀ {pp : Inst.Model.ScalesAndPolicy}, readFiles Z = .ok pp → ∀ {D : WholeD} {r : LPFD.Full.RunPF},
    LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF →
    OnBytes.Model.Verify.rangeChecksOf Zp.p.X ≠
      some (checksOfPars (((descZ Zp Np cF).first.blocksInOrder.dropLast.filterMap fun b =>
        (fun _ => none : Place → Option (Par × List (ℕ × String × ℕ))) b.place).map (·.1)))

/-- A negative test; it counts as no goal. The checks at parBent are not the list that
Verify.rangeChecksOf gives at Zp.p.X. -/
def Spec.bent_not_own : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl), InScope Z = true →
    ∀ {pp : Inst.Model.ScalesAndPolicy}, readFiles Z = .ok pp → ∀ {D : WholeD} {r : LPFD.Full.RunPF},
    LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF →
    ∀ mats : ℕ → List (ℕ × String × ℕ),
    OnBytes.Model.Verify.rangeChecksOf Zp.p.X ≠
      some (checksOfPars (((descZ Zp Np cF).first.blocksInOrder.dropLast.filterMap fun b =>
        parBent Zp mats b.place).map (·.1)))

/-- **sessionStops_of_pinned_own at the planner's own four arguments, without the premise on the
planner's test.** cells and mats are free. All else that the docstring of sessionStops_of_pinned
says holds here too. -/
def Spec.sessionStops_of_pinned_files : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
    {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
    (run₂ : R₂ → ByteArray) (run₃ : R₃ → ByteArray) {Tr X₀ Xh : Type} (B : ProverCoinCounts)
    (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh)
    (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh)
    (_scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (_hr : readFiles Z = .ok pp) (_live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (_L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {w₀ : FullSizeMatrix} {rc : (protocolAtFiles Z).EncodingRandomness} {x₀ : ProofFile.Inst} {k₀ : Coins B}
    {R : Ready FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh}
    (_hR : ready (descZ Zp Np cF) B (provG Z Zp Np cF B G H) w₀ rc x₀ k₀ = .ok R)
    (_hn : ∀ L ∈ G.first, L.place.kind ≠ KindName.frame)
    (Yes : FullSizeMatrix → XF → Prop) (mats : ℕ → List (ℕ × String × ℕ)) (cells : Tr → ProofFile.Honest.Cells)
    (_h₁ : RowsPinned (parOwn Zp mats) cells (provG Z Zp Np cF B G H).first
      (descZ Zp Np cF).first.blocksInOrder.dropLast)
    (_h₃ : RowsPinned (fun _ => none) cells (provG Z Zp Np cF B G H).second
      (descZ Zp Np cF).second.blocksInOrder)
    (_hP : ∀ n w a, TiedYes Z Zp Np cF run₂ run₃ B G H Yes n w (LPFD.Full.instanceAsPlainRecord a) →
      ∀ tr, H.trace w.1 (LPFD.Full.instanceAsPlainRecord a) = some tr →
        CellsSmallAt (parOwn Zp mats) cells (descZ Zp Np cF).first.blocksInOrder.dropLast
          ⟨w.1, w.2.1, LPFD.Full.instanceAsPlainRecord a, tr⟩)
    (ok : FullSizeMatrix → Prop) (Gs : (protocolAtFiles Z).OutOfDomainSeed → Prop),
    HidSmall (famG Z Zp Np cF run₂ run₃ B G H)
      (fun n w a => TiedIn Z Zp Np cF run₂ run₃ B G H Yes ok Gs n w (LPFD.Full.instanceAsPlainRecord a))
      (ENNReal.ofReal ((2 : ℝ) ^ (-(((linesAt Zp).sec : ℝ) + (clog2 (linesAt Zp).slots : ℝ) +
        (clog2 (max 1 (batchesAt Zp)) : ℝ) +
        (clog2 (plannedCopies (linesAt Zp) (oneTimeAt Zp) (columnsFirstAt Zp)) : ℝ)))) + 0)

/-- **sessionStops_of_tiedOwn_own at the planner's own four arguments, without the premise on the
planner's test.** The reader of cells is cellsC Zp.p.X; the parameters are the description's own;
the premise on the trace is TraceOwn. mats is free. All else that the docstring of
sessionStops_of_tiedOwn says holds here too. -/
def Spec.sessionStops_of_tiedOwn_files : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
    {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
    (run₂ : R₂ → ByteArray) (run₃ : R₃ → ByteArray) {X₀ Xh : Type} (B : ProverCoinCounts)
    (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr X₀ Xh)
    (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh)
    (_scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (_hr : readFiles Z = .ok pp) (_live : protocolDataWellFormed (asDescriptionFiles Z) = true) {D : WholeD}
    {r : LPFD.Full.RunPF} (_L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {w₀ : FullSizeMatrix} {rc : (protocolAtFiles Z).EncodingRandomness} {x₀ : ProofFile.Inst} {k₀ : Coins B}
    {R : Ready FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr X₀ Xh}
    (_hR : ready (descZ Zp Np cF) B (provG Z Zp Np cF B G H) w₀ rc x₀ k₀ = .ok R)
    (_hn : ∀ L ∈ G.first, L.place.kind ≠ KindName.frame)
    (Yes : FullSizeMatrix → XF → Prop) (mats : ℕ → List (ℕ × String × ℕ))
    (_h₁ : RowsPinned (parOwn Zp mats) (cellsC Zp.p.X) (provG Z Zp Np cF B G H).first
      (descZ Zp Np cF).first.blocksInOrder.dropLast)
    (_h₃ : RowsPinned (fun _ => none) (cellsC Zp.p.X) (provG Z Zp Np cF B G H).second
      (descZ Zp Np cF).second.blocksInOrder)
    (_hO : TraceOwn Z Zp Np cF run₂ run₃ B G H Yes)
    (ok : FullSizeMatrix → Prop) (Gs : (protocolAtFiles Z).OutOfDomainSeed → Prop),
    HidSmall (famG Z Zp Np cF run₂ run₃ B G H)
      (fun n w a => TiedIn Z Zp Np cF run₂ run₃ B G H Yes ok Gs n w (LPFD.Full.instanceAsPlainRecord a))
      (ENNReal.ofReal ((2 : ℝ) ^ (-(((linesAt Zp).sec : ℝ) + (clog2 (linesAt Zp).slots : ℝ) +
        (clog2 (max 1 (batchesAt Zp)) : ℝ) +
        (clog2 (plannedCopies (linesAt Zp) (oneTimeAt Zp) (columnsFirstAt Zp)) : ℝ)))) + 0)

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.nonemptyPadZ_parOwnChecksSpec
#print axioms OnBytes.FrontRoad.nonemptyOfInhabited_parOwnChecksSpec
#print axioms OnBytes.FrontRoad.linesAt
#print axioms OnBytes.FrontRoad.oneTimeAt
#print axioms OnBytes.FrontRoad.columnsFirstAt
#print axioms OnBytes.FrontRoad.batchesAt
#print axioms OnBytes.FrontRoad.ownPars
#print axioms OnBytes.FrontRoad.k8PlaceAt
#print axioms OnBytes.FrontRoad.parBent
#print axioms OnBytes.FrontRoad.Spec.k8_places_front
#print axioms OnBytes.FrontRoad.Spec.pars_at_parOwn
#print axioms OnBytes.FrontRoad.Spec.checks_are_own
#print axioms OnBytes.FrontRoad.Spec.lines_are_frame
#print axioms OnBytes.FrontRoad.Spec.planner_passes_at_parOwn
#print axioms OnBytes.FrontRoad.Spec.missed_at_none
#print axioms OnBytes.FrontRoad.Spec.none_not_own
#print axioms OnBytes.FrontRoad.Spec.bent_not_own
#print axioms OnBytes.FrontRoad.Spec.sessionStops_of_pinned_files
#print axioms OnBytes.FrontRoad.Spec.sessionStops_of_tiedOwn_files
#print axioms OnBytes.FrontRoad.Spec.premises_met_at_full
