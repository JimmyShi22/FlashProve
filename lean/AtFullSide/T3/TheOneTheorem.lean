-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/T3/TheOneTheorem.lean: THE PREMISES OF ZERO KNOWLEDGE ON SERVED REQUESTS, IN ONE STATEMENT: AN IMPLICATION.

1.  zeroKnowledgeOnServedRequests_ofRows: from the rows of the online prover and of the offline prover,
    zero knowledge on the served requests at the protocol's honest provers, with the private stops' share of
    the offline and the link proof at 0.
2.  Theorems, so not premises here: that the work bits are the protocol's own; that two indices serve
    one request; the offline description and its names; that the offline prover has no second stop; that
    the online rows' owners are their own.
3.  zeroKnowledgeOnServedRequests_ofRows_atNamedFiles: at the named sets of public files the premises on the
    files are theorems too.
4.  Read it beside completeness, at the same return and the same rows G. On is asked only at parts that a run
    has called, and Good at letters that never hold, so a prover whose early block is always refused would meet
    all later rows with nothing shown. Completeness at the same G is what rules that out; this file does not show it.
5.  OfflineSidesAreWhole is a guard: no proof here uses it. Without it, what is asked behind a block that has no
    side could hold with nothing shown. _start is a guard too: no proof here uses it. Without it no thread has a
    starting state, and the premises on On at the run could hold with nothing shown.
6.  The premises are listed in the statement: this file proves zero knowledge of nothing.
-/
import AtFullSide.T3.AtNamedFiles
import Johnson.T3.OfflineOfKinds
import AtFullSide.T3.OnlineK8AtBase
import Johnson.T3.OfflineQuiet
import AtFullSide.T3.StopsThru
import E2E.CompleteAsIOPServedLaws
import Johnson.T3.RowDebtsBeside
import Johnson.M1.KeyWhole
import AtFullSide.M1.OwnsAt
import AtFullSide.M1.LotsAtReturn

set_option autoImplicit false
set_option maxRecDepth 100000
attribute [-instance] Inst.Model.Scl.ref
noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open Iop Prob AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.AtFiles AtPublicFiles.Committed AtPublicFiles.Cut
open AtPublicFiles.AtFiles.HonestTerm
open ProofFile.Honest (Sides Owed relAt AtHonest OnlineProverWithDescription Cells Coins Ready ready Local Face)
open ProofFile.Honest.Term (tableCoins)
open VerifiableInference.Desc (Chain KindName)
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open OnBytes.Maker (WholeD)
open LPFD.Full (instanceAsPlainRecord XF)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles NamedFiles)
open FlashProve (protocolDataWellFormed committerCoinCountLessOne)
open P5J

local instance (priority := high) oneTheoremPad : Nonempty PadZ := pads_nonempty frS 402653181
local instance (priority := high) oneTheoremValue : Nonempty RunValue := ⟨fun _ => 0⟩
local instance (priority := high) oneTheoremDefault : Inhabited RunValue := ⟨fun _ => 0⟩

variable {files : PublicFiles}

/-- **The online rows' owners are their own**, at what the maker returns at the base filling. -/
theorem owns_base (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    {D : WholeD} {r : LPFD.Full.RunPF} {x : VerifiableInference.Desc.First.Look.Place}
    {A : OnlineProverWithDescription FullSizeMatrix ProofFile.Honest.IndexCommitterCoins Cells Unit Unit} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    {G : Sides A.F A.B FullSizeMatrix ProofFile.Honest.IndexCommitterCoins TableKey Cells Unit Unit} {more : List (String × Bool)}
    (hd : AtHonest OnBytes.secondHashFunction files D r A.Z Np cF x baseFilling A G more) : G.owns = true :=
  (AtFullSide.M1.Own.owns_of_halves G A.H hd.first hd.shared hd.second).trans
    (AtFullSide.M1.Own.owns_at_return ProofFile.Honest.Term.matrixInput OnBytes.HonestTrace.Sz.ref
      ProofFile.Honest.openHonest hd.head scope live hd.made
      (AtFullSide.M1.ahead_at_ret scope live hd.made).1)

/-- **The key file's input in one line**: the parts' test on ranges says yes at what is in range. -/
def SendersTestTheRange (parts : Parts files) : Prop :=
  ∀ i, OnPublicFiles.Flat.InRange i → parts.senders.inRange i = true

/-- What RowDebtsAt asks of the input, from that line. -/
theorem input_of_range (parts : Parts files) (d : OfflineDescription)
    (range : SendersTestTheRange parts) (w₀ rc x)
    (hx : relAt (ansAt (AZ files) PadZ (holdZ files)) (fun i _ => inRange i) wrK w₀ rc x) :
    ((cmKey files).proverAt 0 (parts.prover d)).inRange w₀ = true ∧
      (((cmKey files).proverAt 0 (parts.prover d)).trace w₀ x).isSome = true := by
  obtain ⟨_, _, -, hr⟩ := hx
  exact ⟨range w₀ hr, rfl⟩

/-- **The guard of the offline sides, from the senders bearing their places.** -/
theorem offlineSidesAreWhole_of_atAll (parts : Parts files) (scope : InScope files = true)
    (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    (atAll : ∀ description, offlineDescription files = .ok description →
      (AtPublicFiles.KeyLay.withTests parts.senders description.source description.numbers description.later
        (offlineTestParametersOnU description.later) (offlineTestOnOmega description.later) parts.rangeEntry
        parts.rangeGroups 0).AtAll) :
    OfflineSidesAreWhole parts := by
  intro description hdesc
  obtain ⟨d, hd, hn⟩ := offlineDescription_named files live
  have e : d = description := by
    have h := hd.symm.trans hdesc
    injection h
  subst e
  exact OnBytes.M1.sidesWhole_key scope hn _ (atAll d hdesc)

/-- A lemma toward zeroKnowledgeOnServedRequests_ofSides: the premises in one statement. Online: the prover's rows at the base filling,
the debts of the rows and the online private stops. Offline, at the description that the
public files make: the rows of the parts, that the parts are the rows' prover, Owed at the key file and
that its owners are the rows'. -/
theorem zeroKnowledgeOnServedRequests_ofRows {zHid : ℝ≥0∞}
    (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles files = .ok pp) {D : WholeD} {r : LPFD.Full.RunPF}
    {x : VerifiableInference.Desc.First.Look.Place}
    {A : OnlineProverWithDescription FullSizeMatrix ProofFile.Honest.IndexCommitterCoins Cells Unit Unit} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    {G : Sides A.F A.B FullSizeMatrix ProofFile.Honest.IndexCommitterCoins TableKey Cells Unit Unit} {more : List (String × Bool)}
    (hd : AtHonest OnBytes.secondHashFunction files D r A.Z Np cF x baseFilling A G (baseAsks A ++ more))
    (debts : RowDebtsP A G A.H (ProofFile.Honest.imageRel id (tableCoins files)
      (relAt (ansAt (AZ files) PadZ (holdZ files)) (ServedRequest committerCoinCountLessOne files hr) instanceAsPlainRecord)))
    (hid : HidSmall (onlineProver files)
      (fun _ w a => rangeAtFiles w.1 ∧ (protocolAtFiles files).validB (ServedRequest committerCoinCountLessOne files hr) w a) zHid)
    (_start : ∃ z₀, A.F.okStart (instanceAsPlainRecord z₀) = true)
    (parts : Parts files) (_whole : OfflineSidesAreWhole parts) :
    ∃ d : OfflineDescription, offlineDescription files = .ok d ∧
      ∀ (GK : Sides (keyFileDescription d.source d.numbers d.later) parts.book (Cz files).I
          ((Cz files).Pad × (Cz files).Rnd) TableKey Unit parts.SharedState parts.OwnState)
        (_ : IsProvK files (keyFileDescription d.source d.numbers d.later) parts.book GK (parts.prover d))
        (_ : Owed (keyFileDescription d.source d.numbers d.later) parts.book
          ((cmKey files).proverAt 0 (parts.prover d)) GK.mute
          (relAt (ansAt (AZ files) PadZ (holdZ files)) (fun i _ => inRange i) wrK))
        (_ : GK.owns = true),
        ZeroKnowledgeOnServedRequests files hr (HonestProvers.ofThreeProvers (honestProvers files parts)) 0 0
          zHid := by
  obtain ⟨d, hdesc, hn⟩ := offlineDescription_named files live
  obtain ⟨-, x₀, -, -⟩ := someRequestIsServed_holds files scope hr
  refine ⟨d, hdesc, fun GK isProver owed ownsKey => ?_⟩
  obtain ⟨table, exact, stops⟩ := offlineClauses hdesc parts scope live hn GK isProver x₀ owed ownsKey
    (quiet_parts parts d)
  exact zeroKnowledgeOnServedRequests_fromTheBase files scope live hr hd debts
    (owns_base scope live hd) hid parts _ table exact stops

/-- The online private stops' bound on the served requests, from their bound on the relation. -/
theorem hidSmall_of_window {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles files = .ok pp) {z : ℝ≥0∞}
    (window : ∀ (n : ℕ) (i : FullSizeMatrix) (r : (protocolAtFiles files).EncodingRandomness) (e : (protocolAtFiles files).OutOfDomainSeed) (x : XF), RyesZ files i x →
      prRho (((onlineProver files).at n).Hid (i, r, e) (x, (protocolAtFiles files).recOf i r e)) ≤ z)
    (hS : ∀ i x, ServedRequest committerCoinCountLessOne files hr i x → RyesZ files i x) :
    HidSmall (onlineProver files)
      (fun _ w a => rangeAtFiles w.1 ∧ (protocolAtFiles files).validB (ServedRequest committerCoinCountLessOne files hr) w a) z := by
  rintro n ⟨i, r, e⟩ ⟨x, y⟩ ⟨-, hy, hs⟩
  have hy' : y = (protocolAtFiles files).recOf i r e := hy
  subst hy'
  exact window n i r e x (hS i x hs)

/-- A lemma toward zeroKnowledgeOnServedRequests_ofSides: the form that takes a bound on the online private stops at
every request of the relation. -/
theorem zeroKnowledgeOnServedRequests_atTheNumber {z : ℝ≥0∞}
    (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles files = .ok pp) {D : WholeD} {r : LPFD.Full.RunPF}
    {x : VerifiableInference.Desc.First.Look.Place}
    {A : OnlineProverWithDescription FullSizeMatrix ProofFile.Honest.IndexCommitterCoins Cells Unit Unit} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    {G : Sides A.F A.B FullSizeMatrix ProofFile.Honest.IndexCommitterCoins TableKey Cells Unit Unit} {more : List (String × Bool)}
    (hd : AtHonest OnBytes.secondHashFunction files D r A.Z Np cF x baseFilling A G (baseAsks A ++ more))
    (debts : RowDebtsP A G A.H (ProofFile.Honest.imageRel id (tableCoins files)
      (relAt (ansAt (AZ files) PadZ (holdZ files)) (ServedRequest committerCoinCountLessOne files hr) instanceAsPlainRecord)))
    (window : ∀ (n : ℕ) (i : FullSizeMatrix) (r : (protocolAtFiles files).EncodingRandomness) (e : (protocolAtFiles files).OutOfDomainSeed) (x : XF), RyesZ files i x →
      prRho (((onlineProver files).at n).Hid (i, r, e) (x, (protocolAtFiles files).recOf i r e)) ≤ z)
    (_start : ∃ z₀, A.F.okStart (instanceAsPlainRecord z₀) = true)
    (parts : Parts files) (_whole : OfflineSidesAreWhole parts) :
    ∃ d : OfflineDescription, offlineDescription files = .ok d ∧
      ∀ (GK : Sides (keyFileDescription d.source d.numbers d.later) parts.book (Cz files).I
          ((Cz files).Pad × (Cz files).Rnd) TableKey Unit parts.SharedState parts.OwnState)
        (_ : IsProvK files (keyFileDescription d.source d.numbers d.later) parts.book GK (parts.prover d))
        (_ : Owed (keyFileDescription d.source d.numbers d.later) parts.book
          ((cmKey files).proverAt 0 (parts.prover d)) GK.mute
          (relAt (ansAt (AZ files) PadZ (holdZ files)) (fun i _ => inRange i) wrK))
        (_ : GK.owns = true),
        ZeroKnowledgeOnServedRequests files hr (HonestProvers.ofThreeProvers (honestProvers files parts)) 0 0
          z :=
  zeroKnowledgeOnServedRequests_ofRows scope live hr hd debts
    (hidSmall_of_window hr window fun _ _ h => AtPublicFiles.AtFiles.servedRequest_below committerCoinCountLessOne files scope hr h)
    _start parts _whole

/-- A lemma: zeroKnowledgeOnServedRequests_ofRows at the named sets of public files. -/
theorem zeroKnowledgeOnServedRequests_ofRows_atNamedFiles {zHid : ℝ≥0∞} (named : NamedFiles files)
    {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles files = .ok pp) {D : WholeD} {r : LPFD.Full.RunPF}
    {x : VerifiableInference.Desc.First.Look.Place}
    {A : OnlineProverWithDescription FullSizeMatrix ProofFile.Honest.IndexCommitterCoins Cells Unit Unit} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    {G : Sides A.F A.B FullSizeMatrix ProofFile.Honest.IndexCommitterCoins TableKey Cells Unit Unit} {more : List (String × Bool)}
    (hd : AtHonest OnBytes.secondHashFunction files D r A.Z Np cF x baseFilling A G (baseAsks A ++ more))
    (debts : RowDebtsP A G A.H (ProofFile.Honest.imageRel id (tableCoins files)
      (relAt (ansAt (AZ files) PadZ (holdZ files)) (ServedRequest committerCoinCountLessOne files hr) instanceAsPlainRecord)))
    (hid : HidSmall (onlineProver files)
      (fun _ w a => rangeAtFiles w.1 ∧ (protocolAtFiles files).validB (ServedRequest committerCoinCountLessOne files hr) w a) zHid)
    (_start : ∃ z₀, A.F.okStart (instanceAsPlainRecord z₀) = true)
    (parts : Parts files) (_whole : OfflineSidesAreWhole parts) :
    ∃ d : OfflineDescription, offlineDescription files = .ok d ∧
      ∀ (GK : Sides (keyFileDescription d.source d.numbers d.later) parts.book (Cz files).I
          ((Cz files).Pad × (Cz files).Rnd) TableKey Unit parts.SharedState parts.OwnState)
        (_ : IsProvK files (keyFileDescription d.source d.numbers d.later) parts.book GK (parts.prover d))
        (_ : Owed (keyFileDescription d.source d.numbers d.later) parts.book
          ((cmKey files).proverAt 0 (parts.prover d)) GK.mute
          (relAt (ansAt (AZ files) PadZ (holdZ files)) (fun i _ => inRange i) wrK))
        (_ : GK.owns = true),
        ZeroKnowledgeOnServedRequests files hr (HonestProvers.ofThreeProvers (honestProvers files parts)) 0 0
          zHid :=
  zeroKnowledgeOnServedRequests_ofRows (named_open named).1 (named_open named).2 hr hd debts hid
    _start parts _whole

/-- A lemma: the same, opened by kinds. The online private stops are at their named number, from K8's debt;
the key file's Owed is RowDebtsAt; that the parts are the rows' prover is the stored table and the three
lists of rows. Every premise stands by name. -/
theorem zeroKnowledgeOnServedRequests_ofKinds
    (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles files = .ok pp) {D : WholeD} {r : LPFD.Full.RunPF}
    {x : VerifiableInference.Desc.First.Look.Place}
    {A : OnlineProverWithDescription FullSizeMatrix ProofFile.Honest.IndexCommitterCoins Cells Unit Unit} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    {G : Sides A.F A.B FullSizeMatrix ProofFile.Honest.IndexCommitterCoins TableKey Cells Unit Unit} {more : List (String × Bool)}
    (hd : AtHonest OnBytes.secondHashFunction files D r A.Z Np cF x baseFilling A G (baseAsks A ++ more))
    (debts : RowDebtsP A G A.H (ProofFile.Honest.imageRel id (tableCoins files)
      (relAt (ansAt (AZ files) PadZ (holdZ files)) (ServedRequest committerCoinCountLessOne files hr) instanceAsPlainRecord)))
    {w₀ : FullSizeMatrix} {rc : (protocolAtFiles files).EncodingRandomness} {xx : ProofFile.Inst} {k : Coins A.B}
    {R : Ready FullSizeMatrix (protocolAtFiles files).EncodingRandomness ProofFile.Inst TableKey Cells Unit Unit}
    (hR : ready (descZ A.Z Np cF) A.B (provG files A.Z Np cF A.B (termRows files hd) (termProver files A))
      w₀ rc xx k = .ok R)
    (hn : ∀ L ∈ G.first, L.place.kind ≠ KindName.frame)
    (Pr : Local FullSizeMatrix ProofFile.Honest.IndexCommitterCoins ProofFile.Inst Cells → Prop)
    (hP : ∀ w a, rangeAtFiles w.1 → (protocolAtFiles files).validB (ServedRequest committerCoinCountLessOne files hr) w a →
      ∀ tr, (termProver files A).trace w.1 (instanceAsPlainRecord a) = some tr →
        Pr (termSees files ⟨w.1, w.2.1, instanceAsPlainRecord a, tr⟩))
    (quiet : ∀ side ∈ A.H.first ++ A.H.second, side.place.kind ≠ KindName.K8 →
      ∀ part ∈ side.parts, ∀ input front own, part.hid input front own = none)
    (k₁ : K8Clause Pr Face.own.sees A.H.first (descZ A.Z Np cF).first.blocksInOrder.dropLast (dataZ files).ds₁)
    (k₃ : K8Clause Pr Face.own.sees A.H.second (descZ A.Z Np cF).second.blocksInOrder (dataZ files).ds₃)
    (parts : Parts files) (stored : SendersStoreTheTable parts) (range : SendersTestTheRange parts)
    (_whole : OfflineSidesAreWhole parts) (_start : ∃ z₀, A.F.okStart (instanceAsPlainRecord z₀) = true) :
    ∃ d : OfflineDescription, offlineDescription files = .ok d ∧
      ∀ (GK : Sides (keyFileDescription d.source d.numbers d.later) parts.book (Cz files).I
          ((Cz files).Pad × (Cz files).Rnd) TableKey Unit parts.SharedState parts.OwnState)
        (_ : (parts.prover d).first = GK.first.map fun L => ⟨L.place, L.row.map (·.1)⟩)
        (_ : (parts.prover d).shared = GK.shared.map fun L => ⟨L.place, L.row.map (·.1)⟩)
        (_ : (parts.prover d).second = GK.second.map fun L => ⟨L.place, L.row.map (·.1)⟩)
        (_ : RowDebtsBeside (keyFileDescription d.source d.numbers d.later) parts.book GK
          ((cmKey files).proverAt 0 (parts.prover d))
          (relAt (ansAt (AZ files) PadZ (holdZ files)) (fun i _ => inRange i) wrK))
        (_ : GK.owns = true),
        ZeroKnowledgeOnServedRequests files hr (HonestProvers.ofThreeProvers (honestProvers files parts)) 0 0
          (onlinePrivateStopsAt files A.Z Np cF A.B (termRows files hd) (termProver files A)) := by
  have hid := online_hid_of_k8_atBase files scope live hr hd hR hn Pr hP quiet k₁ k₃
  obtain ⟨d, hdesc, hc⟩ := offlineClauses_of_kinds parts scope live
  obtain ⟨-, x₀, -, -⟩ := someRequestIsServed_holds files scope hr
  refine ⟨d, hdesc, fun GK first shared second rows ownsKey => ?_⟩
  obtain ⟨table, exact, stops⟩ := hc GK
    ⟨key_parts parts d, stored_parts parts d stored, first, shared, second⟩ x₀
    (rows.toAt (input_of_range parts d range)) ownsKey (quiet_parts parts d)
  exact zeroKnowledgeOnServedRequests_fromTheBase files scope live hr hd debts
    (owns_base scope live hd) hid parts _ table exact stops

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.zeroKnowledgeOnServedRequests_ofKinds
#print axioms VerifiableInference.Compilation.offlineSidesAreWhole_of_atAll
#print axioms VerifiableInference.Compilation.input_of_range
#print axioms VerifiableInference.Compilation.owns_base
#print axioms VerifiableInference.Compilation.hidSmall_of_window
#print axioms VerifiableInference.Compilation.zeroKnowledgeOnServedRequests_atTheNumber
#print axioms VerifiableInference.Compilation.zeroKnowledgeOnServedRequests_ofRows
#print axioms VerifiableInference.Compilation.zeroKnowledgeOnServedRequests_ofRows_atNamedFiles
