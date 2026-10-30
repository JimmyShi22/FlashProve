-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/T3/OnlineAtTheTerm.lean: the tie of the zero-knowledge statement (ZeroKnowledgeOnServedRequests) to the protocol's own honest provers (E2E/TheHonestProver.lean).

1.  onlineProver_of_seat: where the maker returns A and the public part gives places and a first chain, the online prover is onlineProversOfCommitter at A.H.
2.  zeroKnowledgeOnServedRequests_atTheProvers: the statement at honestProvers, at a value of Parts. The head AtHonest is at the filling of the online
    prover, at A's own public part. Its premises: the head, the row debts, owns, the measure of the private stops, the work bits, and the
    offline prover's table, simulator, exact clause and stops.
3.  No value of any premise is given here. This file proves zero knowledge of nothing.
-/
import Johnson.T3.OwedOfKinds
import E2E.TheHonestProver
import Johnson.ToldDescR.PureChainOfOpen

set_option autoImplicit false
set_option maxRecDepth 100000
attribute [-instance] Inst.Model.Scl.ref
noncomputable section
open scoped ENNReal

namespace VerifiableInference.Compilation
open Iop Prob AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.AtFiles AtPublicFiles.Committed AtPublicFiles.Cut
open AtPublicFiles.AtFiles.HonestTerm
open ProofFile.Honest (Sides relAt AtHonest Cells halvedAll)
open ProofFile.Honest.Term (OnlineReturn onlineMaker onlineFilling)
open VerifiableInference.Desc (Chain)
open Compile.Lifetime (SimOf)
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open OnBytes.Maker (WholeD)
open LPFD.Full (instanceAsPlainRecord)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (dataAtFiles)
open FlashProve (flashProveData protocolDataWellFormed committerCoinCountLessOne)
open P5J

local instance (priority := high) onlineAtTheTermInstance1 : Nonempty PadZ := pads_nonempty frS 402653181
local instance (priority := high) onlineAtTheTermInstance2 : Nonempty RunValue := ⟨fun _ => 0⟩
local instance (priority := high) onlineAtTheTermInstance3 : Inhabited RunValue := ⟨fun _ => 0⟩

variable (files : PublicFiles)

/-- **The online prover at the seat.** -/
theorem onlineProver_of_seat {A : OnlineReturn files} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    (made : onlineMaker files = .ok A) (places : H2U.placesOfMade A.Z.made = .ok Np)
    (chain : ProofFile.onlineFirstChainAt A.Z = .ok cF) :
    onlineProver files = onlineProverAt A Np cF := by
  unfold onlineProver
  simp only [made, places, chain]

/-- **The head's one further test**: a sub-protocol that declares an item and has no half refuses every run, and every On behind it is idle. -/
def t3Asks (A : OnlineReturn files) : List (String × Bool) :=
  [("a half stands at every sub-protocol that declares an item", halvedAll A.F A.H)]

/-- **The statement at the protocol's honest provers**, from the head at the online prover's filling. The places and the first chain are the head's. -/
theorem zeroKnowledgeOnServedRequests_atTheProvers {zHid a : ℝ≥0∞}
    (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles files = .ok pp) {D : WholeD} {r : LPFD.Full.RunPF}
    {x : VerifiableInference.Desc.First.Look.Place} {A : OnlineReturn files} {Np : H2U.Places4}
    {cF : Chain TS ProofFile.Cl} {G : Sides A.F A.B FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey Cells Unit Unit}
    {more : List (String × Bool)}
    (hd : AtHonest OnBytes.secondHashFunction files D r A.Z Np cF x (onlineFilling files) A G (t3Asks files A ++ more))
    (debts : RowDebtsP A G ((cmAlong (AZ files) PadZ (holdZ files)).proverAt 0 A.H)
      (relAt (ansAt (AZ files) PadZ (holdZ files)) (ServedRequest committerCoinCountLessOne files hr) instanceAsPlainRecord))
    (owns : G.owns = true)
    (hid : HidSmall (onlineProver files)
      (fun _ w a => rangeAtFiles w.1 ∧ (protocolAtFiles files).validB (ServedRequest committerCoinCountLessOne files hr) w a) zHid)
    (faithful : (workAtFiles files).Faithful) (two : TwoIndicesServeOneRequest files hr)
    (parts : Parts files) (offlineSimulator : SimOf (protocolAtFiles files).offline)
    (offlineTable : ∀ i r e, (offlineProver parts).ext (i, r, e) = (protocolAtFiles files).encodeIndex i r)
    (offline : ExactOutsideStops (offlineProver parts)
      (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles files).validT w y) (workAtFiles files).offline.cleared
      offlineSimulator)
    (offlineStops : PrivateStopsAtMost (offlineProver parts)
      (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles files).validT w y) (workAtFiles files).offline a) :
    ZeroKnowledgeOnServedRequests files hr (HonestProvers.ofThreeProvers (honestProvers files parts)) a 0 zHid := by
  obtain ⟨Bs, base, O⟩ := hd.laid.opened
  have e := onlineProver_of_seat files hd.made hd.laid.places (ToldDesc.pureChainAt_of_open O)
  unfold honestProvers
  rw [e] at hid ⊢
  exact zeroKnowledgeOnServedRequests_of_honest files A.Z Np cF runValueBytes runValueBytes scope live
    hr hd debts owns hid faithful two _ offlineSimulator offlineTable offline offlineStops

/-- **The link prover of the protocol's honest provers is the link's home prover.** -/
theorem linkProver_atTheTerm (parts : Parts files) :
    (HonestProvers.ofThreeProvers (honestProvers files parts)).linkProver =
      OnBytes.LinkSim.AtHome.explicitLinkProver committerCoinCountLessOne files := rfl

/-- **The two clauses on the link, at the protocol's own link prover and the link's home simulator**, with no premise. -/
theorem link_atTheTerm (parts : Parts files) :
    ExactOutsideStops (HonestProvers.ofThreeProvers (honestProvers files parts)).linkProver
        (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles files).validL w y) (workAtFiles files).link.cleared
        (OnBytes.LinkSim.AtHome.homeSim files) ∧
      PrivateStopsAtMost (HonestProvers.ofThreeProvers (honestProvers files parts)).linkProver
        (fun w y => rangeAtFiles w.1 ∧ (protocolAtFiles files).validL w y) (workAtFiles files).link 0 :=
  ⟨OnBytes.LinkSim.AtHome.home_exactOutsideStops committerCoinCountLessOne files rangeAtFiles _,
    OnBytes.LinkSim.AtHome.home_stopsAtMost committerCoinCountLessOne files rangeAtFiles _⟩

end VerifiableInference.Compilation

#print axioms VerifiableInference.Compilation.linkProver_atTheTerm
#print axioms VerifiableInference.Compilation.link_atTheTerm
#print axioms VerifiableInference.Compilation.onlineProver_of_seat
#print axioms VerifiableInference.Compilation.t3Asks
#print axioms VerifiableInference.Compilation.zeroKnowledgeOnServedRequests_atTheProvers
