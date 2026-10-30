-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/StopsAtFilesSpec.lean: statements only: the statements of
Johnson/FrontRoad/StopsReadCellsSpec.lean joined at the letters of the implications on the field
sessionStops (PremWDebts, E2E/BridgeDebts.lean): the description descZ Zp Np cF, the prover provG Z
Zp Np cF B G H (E2E/BridgeJoinAtFiles.lean). Under the two pins, hn (no row of the first chain
stands at a place of the kind frame) and hR (ready returns at one input): every private abort test
of every part of every half of that prover's first and second chain answers the same at two inputs
whose traces the pins' reader reads alike. Under the two pins and hn alone: so do the two calls of
chainStopAt of which the sessions' private abort set is made. Proved in
Johnson/FrontRoad/StopsAtFiles.lean.
Terms of this folder: Johnson/FrontRoad/Spec.lean.

What this file has (namespace OnBytes.FrontRoad).
  Spec.first_chain_agree_at   at all public files in scope that can be read, under LaidAt, at every
      par: StopsAgreeAt at the whole first chain of the description, from PinHalvesAt at the chain
      without its last member, where no half stands at a place of the kind frame, at two inputs with
      SameCellsAt.
  Spec.tests_strays   general: where readyTests (Johnson/Desc/ProofFile/Honest/Frame.lean) returns,
      no half of the three chains stands at a place that is no member's. The like on two halves at
      one place is tests_twice (Johnson/Desc/ProofFile/Honest/Law/Rule/FileOkOf.lean).
  Spec.private_stops_read_cells   at all public files in scope that can be read, under LaidAt, at
      every par and every reader cells': from hR, hn, the pin at the first chain without its last
      member at par, and the pin at the second chain at the par that names none: at two inputs u, v
      with SameCellsAt cells' u v, each part of each half of (provG …).first and of (provG …).second
      has a private abort test that answers the same at u and at v, at all challenges.
  Spec.session_stops_read_cells   under the same premises without hR: chainStopAt at the whole first
      chain and at the whole second chain, at provG's halves, is the same at Face.own.sees u and
      Face.own.sees v, at all challenges. These are the two calls in hidB
      (Johnson/Desc/ProofFile/Honest/Record.lean), to which mem_hid_famG
      (Johnson/FrontRoad/SessionHid.lean) ties the sessions' private abort set.
  Spec.last_member_escapes_the_pin   a negative test, general: the pin at a list without its last
      member says nothing of a half at the last member's place. At the empty list in front, one last
      member, and the one half there whose one part's test fires just where the index (of the type
      Bool) is true: the pin holds at the list in front, at every par and reader; no half is a stray
      and no two stand at one place, so what the road takes of hR is met; SameCellsAt holds at two
      inputs that differ in the index alone; StopsAgreeAt fails at the whole list. So the pin, with
      that much of hR, leaves a half at the last member's place free. At the description that member
      is of the kind frame (Spec.k8_places_front, Johnson/FrontRoad/ParOwnChecksSpec.lean), and hn
      shuts such a half out.
  Spec.stray_half_escapes   a negative test, general: at no members and the one half whose one
      part's test reads the index, the pin and StopsAgreeAt hold, the half is a stray, no two halves
      stand at one place, and that part's test answers otherwise at two inputs that differ in the
      index alone. So the premise on strays in Spec.agree_all does work.
  Spec.second_half_escapes   a negative test, general: at one member at whose place par names none,
      a first half without a part and a second half at the same place whose one part's test reads
      the index: PinHalvesAt and StopsAgreeAt hold, no half is a stray, two halves stand at one
      place, and that part's test answers otherwise at two inputs that differ in the index alone. So
      the premise on twice in Spec.agree_all does work.

How it fits. CellsOwnAt cells' (Johnson/FrontRoad/CellsOwnAtSpec.lean) holds of the prover's trace
only what cells' reads of it, and is meant to be named with the two pins at the same reader. For the
field sessionStops, whose set is hidB's, what that naming leans on is Spec.session_stops_read_cells:
it wants hn beside the two pins. For every part of the rows it is Spec.private_stops_read_cells,
which wants hR too. Both are premises of the implications. hR does not stand in for hn: readyTests
does not refuse a half at the last member's place: it is no stray, and no two halves stand there
(Spec.last_member_escapes_the_pin). Under the two pins alone neither statement follows: the first
pin stands at the first chain without its last member. par is a letter, so the statements fit the
implications with a free par (sessionStops_of_pinned, Johnson/FrontRoad/SessionStopsOfPinned.lean;
the ten of Johnson/FrontRoad/SessionStopsOfTrace.lean) and those at parOwn. Words (member, half,
part, public and private abort test, stated share): Johnson/FrontRoad/SessionStopsPinned.lean. Not
one of the release's goal statements.

Limits.
  Nothing is said of any prover: no book, rows and prover are known at which the premises hold
      together.
  All limits of Johnson/FrontRoad/StopsReadCellsSpec.lean hold here. Above all: only the private
      abort tests are treated, not what the parts send, nor the other ways in which a run ends; and
      that index, randomness and instance are free says that the tests do not read these three
      fields, not that a run's stops do not depend on the index: in a run, and in hidB, the trace is
      what the prover's trace function answers at the index and the instance.
  cells' is read by the first pin alone: the pin at the par that names none never reads it. At the
      second chain SameCellsAt is idle: under that pin no test fires at any input. The letters R₂,
      R₃, their four instances, run₂ and run₃ are read by nothing in the two statements on the
      description: they are kept, like the reading, so that the statements fit their callers. Of hR
      the road takes two of readyTests' tests alone (no stray half; no two halves at one place); of
      hn the clause at the last member's place.
  At a par at which one of the pin's clauses on public data fails the first pin fails, and the two
      statements that have it hold idly; so too at public files that do not meet scope, the reading
      and LaidAt. The reading follows from scope; it is kept so that the statements fit their
      callers.
  The shared chain's parts have no input to read in their private abort tests: the type is Empty
      (Spec.shared_sees_none, Spec.unseen_chain_never_stops_privately).
  Nothing is said on hiding, completeness or soundness.
-/
import Johnson.FrontRoad.StopsReadCellsSpec
import Johnson.FrontRoad.SessionHid

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open AtPublicFiles.AtFiles AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed
open OnBytes (TableKey)
open OnBytes.Flat (RecFull)
open OnBytes.Params (Lines missedInTheChecks clog2)
open OnBytes.Maker (WholeD)
open OnBytes.Model.Verify (publicOf)
open OnBytes.HonestTrace (Tr cellsC cellsSmall_cellOf ServesAt theTrace meetsAll_theTrace
  servesAt_iff_in_scope TraceHinge)
open Inst.Model (Instance ppref)
open VerifiableInference.Desc (Block Place KindName)
open VerifiableInference.Desc.First.K8 (Par)
open ProofFile.Honest (Prover ProverCoinCounts Sides Ready Coins ready Placed Local Cells Face chainStopAt)
open ProofFile.Honest.K9 (quietStop)
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (protocolDataWellFormed)
open P5J

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off within this namespace,
so that no statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

/- Among all that this file imports, the search for this instance runs out of its budget. It is a
proposition, so whichever proof is found, the statements below are the same. -/
local instance (priority := high) nonemptyPadZ_stopsAtFilesSpec : Nonempty PadZ :=
  pads_nonempty OnBytes.Slice.frS 402653181

/- The same of this one. -/
local instance (priority := high) nonemptyOfInhabited_stopsAtFilesSpec {α : Type} [Inhabited α] :
    Nonempty α := ⟨default⟩

/-- **The tests agree at the whole first chain of the description, its last member too, at every
par**: at all public files in scope that can be read, under LaidAt: from the pin's clauses on the
halves at the chain without its last member, where no half stands at a place of the kind frame, at
two inputs whose traces cells reads alike. Spec.first_chain_agree
(Johnson/FrontRoad/StopsReadCellsSpec.lean) is its case at parOwn Zp mats, from the whole pin. -/
def Spec.first_chain_agree_at : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl), InScope Z = true →
    ∀ {pp : Inst.Model.ScalesAndPolicy}, readFiles Z = .ok pp → ∀ {D : WholeD} {r : LPFD.Full.RunPF},
    LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF →
    ∀ {W₀ Rc Xi Tr' X : Type} (par : Place → Option (Par × List (ℕ × String × ℕ)))
      (cells : Tr' → Cells) (hs : List (Placed (Local W₀ Rc Xi Tr') (Local W₀ Rc Xi Tr') X))
      (u v : Local W₀ Rc Xi Tr'),
      PinHalvesAt par cells hs (descZ Zp Np cF).first.blocksInOrder.dropLast →
      (∀ g ∈ hs, g.place.kind ≠ KindName.frame) → SameCellsAt cells u v →
      StopsAgreeAt u v hs (descZ Zp Np cF).first.blocksInOrder

/-- **Where the tests that read neither a challenge nor the instance return, no half stands at a
place that is no member's.** -/
def Spec.tests_strays : Prop :=
  ∀ {W₀ Rc Xi Ky Tr' X₀ X : Type} (F : VerifiableInference.Desc.FileDescription Xi) (B : ProverCoinCounts)
    (H : Prover W₀ Rc Xi Ky Tr' X₀ X) (w₀ : W₀), ProofFile.Honest.readyTests F B H w₀ = .ok () →
    ProofFile.Honest.strays F.first.blocksInOrder H.first = [] ∧ ProofFile.Honest.strays F.shared.blocksInOrder H.shared = [] ∧
      ProofFile.Honest.strays F.second.blocksInOrder H.second = []

/-- **Under the two pins, hn and hR, every private abort test of the prover's first and second chain
reads of the input nothing but what the pins' reader yields of the trace**: at two inputs whose
traces cells' reads alike, each part of each half answers the same, at all challenges. -/
def Spec.private_stops_read_cells : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
    {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
    (run₂ : R₂ → ByteArray) (run₃ : R₃ → ByteArray) {Tr' X₀ Xh : Type} (B : ProverCoinCounts)
    (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr' X₀ Xh)
    (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr' X₀ Xh)
    (_scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (_hr : readFiles Z = .ok pp) {D : WholeD}
    {r : LPFD.Full.RunPF} (_L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    {w₀ : FullSizeMatrix} {rc : (protocolAtFiles Z).EncodingRandomness} {x₀ : ProofFile.Inst} {k₀ : Coins B}
    {R : Ready FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr' X₀ Xh}
    (_hR : ready (descZ Zp Np cF) B (provG Z Zp Np cF B G H) w₀ rc x₀ k₀ = .ok R)
    (_hn : ∀ L ∈ G.first, L.place.kind ≠ KindName.frame)
    (par : Place → Option (Par × List (ℕ × String × ℕ))) (cells' : Tr' → ProofFile.Honest.Cells)
    (_h₁ : RowsPinned par cells' (provG Z Zp Np cF B G H).first
      (descZ Zp Np cF).first.blocksInOrder.dropLast)
    (_h₃ : RowsPinned (fun _ => none) cells' (provG Z Zp Np cF B G H).second
      (descZ Zp Np cF).second.blocksInOrder)
    (u v : ProofFile.Honest.Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst Tr'), SameCellsAt cells' u v →
    (∀ g ∈ (provG Z Zp Np cF B G H).first, ∀ p ∈ g.parts, ∀ l o, p.hid u l o = p.hid v l o) ∧
      ∀ g ∈ (provG Z Zp Np cF B G H).second, ∀ p ∈ g.parts, ∀ l o, p.hid u l o = p.hid v l o

/-- **Under the two pins and hn, the two calls of chainStopAt of which the sessions' private abort
set is made read of the input nothing but what the pins' reader yields of the trace.** -/
def Spec.session_stops_read_cells : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)
    {R₂ R₃ : Type} [Fintype R₂] [Nonempty R₂] [Fintype R₃] [Inhabited R₃]
    (run₂ : R₂ → ByteArray) (run₃ : R₃ → ByteArray) {Tr' X₀ Xh : Type} (B : ProverCoinCounts)
    (G : Sides (descZ Zp Np cF) B FullSizeMatrix (protocolAtFiles Z).EncodingRandomness TableKey Tr' X₀ Xh)
    (H : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr' X₀ Xh)
    (_scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy}
    (_hr : readFiles Z = .ok pp) {D : WholeD}
    {r : LPFD.Full.RunPF} (_L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
    (_hn : ∀ L ∈ G.first, L.place.kind ≠ KindName.frame)
    (par : Place → Option (Par × List (ℕ × String × ℕ))) (cells' : Tr' → ProofFile.Honest.Cells)
    (_h₁ : RowsPinned par cells' (provG Z Zp Np cF B G H).first
      (descZ Zp Np cF).first.blocksInOrder.dropLast)
    (_h₃ : RowsPinned (fun _ => none) cells' (provG Z Zp Np cF B G H).second
      (descZ Zp Np cF).second.blocksInOrder)
    (u v : ProofFile.Honest.Local FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst Tr'), SameCellsAt cells' u v →
    (∀ loc ds, chainStopAt (Face.own.sees u) (descZ Zp Np cF).first.blocksInOrder
        (provG Z Zp Np cF B G H).first loc ds =
      chainStopAt (Face.own.sees v) (descZ Zp Np cF).first.blocksInOrder
        (provG Z Zp Np cF B G H).first loc ds) ∧
      ∀ loc ds, chainStopAt (Face.own.sees u) (descZ Zp Np cF).second.blocksInOrder
          (provG Z Zp Np cF B G H).second loc ds =
        chainStopAt (Face.own.sees v) (descZ Zp Np cF).second.blocksInOrder
          (provG Z Zp Np cF B G H).second loc ds

/-- A negative test; it counts as no goal. **The pin at a list without its last member says nothing
of a half at the last member's place.** At the empty list in front and one last member bl, at the
one half at bl's place whose one part's private abort test fires just where the index, of the type
Bool, is true: the pin holds at the list in front, no half is a stray and no two stand at one place,
SameCellsAt holds at two inputs that differ in the index alone, and StopsAgreeAt fails at the whole
list. -/
def Spec.last_member_escapes_the_pin : Prop :=
  ∀ {S Cl Rc Xi Tr' X : Type} (par : Place → Option (Par × List (ℕ × String × ℕ)))
    (cells : Tr' → Cells) (bl : Block S Cl) (sh : ProofFile.Honest.Odds) (rc : Rc) (x : Xi) (tr : Tr'),
    let hs : List (Placed (Local Bool Rc Xi Tr') (Local Bool Rc Xi Tr') X) :=
      [⟨bl.place, [quietStop (fun u _ _ => if u.w₀ then some "" else none) sh]⟩]
    RowsPinned par cells hs ([bl] : List (Block S Cl)).dropLast ∧
      ProofFile.Honest.strays [bl] hs = [] ∧ ProofFile.Honest.twice hs = [] ∧
      SameCellsAt cells ⟨true, rc, x, tr⟩ ⟨false, rc, x, tr⟩ ∧
      ¬ StopsAgreeAt ⟨true, rc, x, tr⟩ ⟨false, rc, x, tr⟩ hs [bl]

/-- A negative test; it counts as no goal. **A half at no member's place escapes the pin and the
functions of stops.** At the empty list of members and the one half, at a place a, whose one part's
private abort test fires just where the index, of the type Bool, is true: the pin holds,
StopsAgreeAt holds at two inputs that differ in the index alone, and that part's test answers
otherwise at the two. The half is a stray: strays is not empty; no two halves stand at one place:
twice is empty. So of the premises of Spec.agree_all the one on strays alone fails here, and its
conclusion fails: that premise does work. -/
def Spec.stray_half_escapes : Prop :=
  ∀ {S Cl Rc Xi Tr' X : Type} (par : Place → Option (Par × List (ℕ × String × ℕ)))
    (cells : Tr' → Cells) (a : Place) (sh : ProofFile.Honest.Odds) (rc : Rc) (x : Xi) (tr : Tr'),
    let hs : List (Placed (Local Bool Rc Xi Tr') (Local Bool Rc Xi Tr') X) :=
      [⟨a, [quietStop (fun u _ _ => if u.w₀ then some "" else none) sh]⟩]
    RowsPinned par cells hs ([] : List (Block S Cl)) ∧
      StopsAgreeAt ⟨true, rc, x, tr⟩ ⟨false, rc, x, tr⟩ hs ([] : List (Block S Cl)) ∧
      ProofFile.Honest.strays ([] : List (Block S Cl)) hs ≠ [] ∧ ProofFile.Honest.twice hs = [] ∧
      ¬ ∀ g ∈ hs, ∀ p ∈ g.parts, ∀ l o,
        p.hid ⟨true, rc, x, tr⟩ l o = p.hid ⟨false, rc, x, tr⟩ l o

/-- A negative test; it counts as no goal. **A half behind another at one place escapes the pin's
clauses on the halves and the functions of stops.** At one member b at whose place par names none,
and two halves at b's place: the first with no part, the second with the one part whose private
abort test fires just where the index, of the type Bool, is true: the pin's clauses on the halves
and StopsAgreeAt hold at two inputs that differ in the index alone, no half is a stray, two halves
stand at one place: twice is not empty; and that part's test answers otherwise at the two. So of the
premises of Spec.agree_all the one on twice alone fails here, and its conclusion fails: that premise
does work. -/
def Spec.second_half_escapes : Prop :=
  ∀ {S Cl Rc Xi Tr' X : Type} (par : Place → Option (Par × List (ℕ × String × ℕ)))
    (cells : Tr' → Cells) (b : Block S Cl) (sh : ProofFile.Honest.Odds) (rc : Rc) (x : Xi) (tr : Tr'),
    par b.place = none →
    let hs : List (Placed (Local Bool Rc Xi Tr') (Local Bool Rc Xi Tr') X) :=
      [⟨b.place, []⟩, ⟨b.place, [quietStop (fun u _ _ => if u.w₀ then some "" else none) sh]⟩]
    PinHalvesAt par cells hs [b] ∧
      StopsAgreeAt ⟨true, rc, x, tr⟩ ⟨false, rc, x, tr⟩ hs [b] ∧
      ProofFile.Honest.strays [b] hs = [] ∧ ProofFile.Honest.twice hs ≠ [] ∧
      ¬ ∀ g ∈ hs, ∀ p ∈ g.parts, ∀ l o,
        p.hid ⟨true, rc, x, tr⟩ l o = p.hid ⟨false, rc, x, tr⟩ l o

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.nonemptyPadZ_stopsAtFilesSpec
#print axioms OnBytes.FrontRoad.nonemptyOfInhabited_stopsAtFilesSpec
#print axioms OnBytes.FrontRoad.Spec.tests_strays
#print axioms OnBytes.FrontRoad.Spec.private_stops_read_cells
#print axioms OnBytes.FrontRoad.Spec.session_stops_read_cells
#print axioms OnBytes.FrontRoad.Spec.last_member_escapes_the_pin
#print axioms OnBytes.FrontRoad.Spec.first_chain_agree_at
#print axioms OnBytes.FrontRoad.Spec.stray_half_escapes
#print axioms OnBytes.FrontRoad.Spec.second_half_escapes
