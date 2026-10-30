-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/StopsReadCellsSpec.lean: definitions and statements only, on a premise's form.
Under the pin (RowsPinned, Johnson/FrontRoad/SessionStopsPinned.lean), and already under its clauses
on the halves (PinHalvesAt, Johnson/FrontRoad/PinPublicSpec.lean), every private abort test of a
part of the first half that stands at a member's place (among these are all the parts that
chainStopAt asks: it asks no part without a move; by inspection, not stated here, they are also the
parts that chainSteps, Johnson/Desc/ProofFile/Honest/Frame.lean, lays into a run's steps; the
sessions' private abort set is made of chainStopAt at the whole first and the whole second chain:
hidB, Johnson/Desc/ProofFile/Honest/Record.lean) reads of the prover's input nothing but what the
pins' reader cells yields of the trace: at two inputs whose traces cells reads alike, and which are
free elsewhere, each such test answers the same, and so does the chain's whole function of stops
(chainStopAt, Johnson/Desc/ProofFile/Honest/Rule.lean). In the shared chain no private abort test is
asked at all. Proved in Johnson/FrontRoad/StopsReadCells.lean.
Terms of this folder: Johnson/FrontRoad/Spec.lean.

What this file has (namespace OnBytes.FrontRoad).
  SameCellsAt cells u v   two inputs of the first or the second chain whose traces the reader cells
      reads alike: cells u.trace = cells v.trace. Index, randomness, instance, and what the traces
      bear beyond cells, are free.
  StopsAgreeAt u v hs bs   at each member of bs, each part of the first half of hs that stands at
      its place has a private abort test that answers the same at u and at v, at all challenges.
  Spec.stops_read_cells   general: PinHalvesAt par cells hs bs and SameCellsAt cells u v give
      StopsAgreeAt u v hs bs.
  Spec.chainStop_of_agree   general: StopsAgreeAt u v hs bs gives chainStopAt (some u) bs hs =
      chainStopAt (some v) bs hs, at all challenges. chainStopAt finds a member's half as the pin
      does: the first half at the member's place.
  Spec.agree_all   general: where every half of hs stands at a member's place (strays bs hs = [])
      and no two at one place (twice hs = []), StopsAgreeAt u v hs bs speaks of every part of every
      half. ready refuses rows at which one of the two lists is not empty.
  Spec.pinned_stops_read_cells   general: so RowsPinned par cells hs bs and SameCellsAt cells u v
      give that equation. At the par that names none and the whole second chain it is the second
      pin's case, at all letters; there SameCellsAt is idle: no test fires at any input.
  Spec.first_chain_agree   at all public files in scope that can be read, under LaidAt: StopsAgreeAt
      at the WHOLE first chain of the description, from the same premises as the next.
  Spec.first_chain_stops_read_cells   at all public files in scope that can be read, under LaidAt:
      the equation of Spec.pinned_stops_read_cells at the WHOLE first chain of the description, its
      last member too, from the pin at the chain without its last member and the premise that no
      half stands at a place of the kind frame (the premise hn of the implications says that of the
      rows, whose places the halves keep: first_provG, Johnson/FrontRoad/SessionHid.lean).
  Spec.unseen_never_stops_privately, Spec.shared_sees_none   general: a part that is given no input
      (none) never stops by its private abort test; in the shared chain the input is never given
      (Face.shared.sees, Johnson/Desc/ProofFile/Honest/Frame.lean), and the type of what could be
      given is Empty.
  Spec.other_stop_not_halves, Spec.firing_not_halves   two negative tests on the premise, general.
      At a member at whose place par names P, the one half whose one part has a test that differs
      from smallStop cells P at some argument does not meet PinHalvesAt: so a part whose test reads
      the trace otherwise fails. At a member at whose place par names none, the one half with the
      one part whose test fires at some argument does not meet it.
  Spec.unseen_chain_never_stops_privately   general: the like of a whole chain: chainStopAt at none
      never answers the private class.
  Spec.differing_not_agree, Spec.index_reader_fails   two negative tests on the conclusion.
      StopsAgreeAt u v fails at the one half whose one part's test answers otherwise at u than at v.
      A written test that reads the index (at the index type Bool: it fires just where the index is
      true): at two inputs that differ in the index alone SameCellsAt holds at every reader,
      StopsAgreeAt fails, and the rows fail PinHalvesAt at every par.

How it fits. CellsOwnAt cells' (Johnson/FrontRoad/CellsOwnAtSpec.lean) holds of the prover's trace
only what cells' reads of it. It is meant to be named with the two pins at the same reader. These
statements say what that naming leans on. Under the pins, where no half stands at a place of the
kind frame (hn), the private abort tests that the two chains' functions of stops ask read the trace
through that reader alone; the pins alone do not give that: neither sees a half at the first chain's
last member's place. For every part of every half, ready's return (hR) is wanted too. The join at
the implications' own letters stands in Johnson/FrontRoad/StopsAtFilesSpec.lean. Words (member,
half, part, public and private abort test, stated share): Johnson/FrontRoad/SessionStopsPinned.lean.
Not one of the release's goal statements.

Limits.
  Nothing is said of any prover: whether any rows meet the pin is not said.
  Only the private abort tests are treated. What the parts SEND may read the whole input, and a move
      may also REFUSE at what it reads of the whole input and of the coins (an error of Move.say,
      which Johnson/Desc/ProofFile/Honest/Frame.lean calls a fault); in a run an earlier fault takes
      the place of a later stop. A run also ends without an output where the trace function answers
      none and where the range test on the index fails (ready): both read the index. So it does
      where the prover's stored tables answer none, or a column of another width, at a position that
      is read (fillCols): that reads the index and the randomness. In the sessions' prover, after a
      sub-protocol that rejects, no part is called and no stop is asked
      (Johnson/Desc/ProofFile/Honest/Walk.lean). hidB itself begins with the trace function's
      answer. None of these is a private abort test; none is treated here, and the list may not be
      whole. At the twenty-five pinned parts the one move sends nothing; of the other members'
      parts' moves the pin says nothing.
  A half that stands at no member's place, or behind another half at the same place, is not treated
      by StopsAgreeAt: chainStopAt never asks it. ready (Johnson/Desc/ProofFile/Honest/Frame.lean)
      refuses rows that have one (strays, twice); where both lists are empty StopsAgreeAt speaks of
      every part of every half (Spec.agree_all).
  The public abort tests (the field bad) read no input, by type.
  At public files that do not meet scope, the reading and LaidAt, Spec.first_chain_agree and
      Spec.first_chain_stops_read_cells hold idly; so too at a mats at which smallFits fails at a
      member of the kind K8, where the pin fails. The reading follows from scope (inScope_readFiles,
      Johnson/Desc/K12/Law/Sizes/StageSizesAtScope.lean); it is kept as a premise so that the
      statement fits its callers.
  That index, randomness and instance are free says that the tests do not read these three fields.
      It does not say that a run's stops do not depend on the index: in a run the trace is what the
      prover's trace function answers at the index and the instance (ready), so what cells yields of
      it may depend on the hidden index, and the tests read the hidden input through it. Nothing is
      said on hiding, completeness or soundness.
-/
import Johnson.FrontRoad.PinPublicSpec
import Johnson.Desc.ProofFile.Honest.Rule

set_option autoImplicit false

namespace OnBytes.FrontRoad
open VerifierAndGoals (PublicFiles InScope readFiles)
open P5J (TS LaidAt)
open OnBytes.Maker (WholeD)
open AtPublicFiles.AtFiles (descZ)
open VerifiableInference.Desc (Block Place KindName)
open VerifiableInference.Desc.First.K8 (Par)
open ProofFile.Honest (Placed Local Common Cells Why Face chainStopAt)
open ProofFile.Honest.K8 (smallStop)
open ProofFile.Honest.K9 (quietStop)

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off within this namespace,
so that no statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

/-- **Two inputs whose traces the reader cells reads alike.** All else of the two is free. -/
def SameCellsAt {W₀ Rc Xi Tr : Type} (cells : Tr → Cells) (u v : Local W₀ Rc Xi Tr) : Prop :=
  cells u.trace = cells v.trace

/-- **At each member, each part of the first half that stands at its place has a private abort test
that answers the same at u and at v**, at all challenges. -/
def StopsAgreeAt {S Cl W₀ Rc Xi Tr X : Type} (u v : Local W₀ Rc Xi Tr)
    (hs : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X))
    (bs : List (Block S Cl)) : Prop :=
  ∀ b ∈ bs, ∀ g, (hs.find? fun g => g.place == b.place) = some g →
    ∀ p ∈ g.parts, ∀ l o, p.hid u l o = p.hid v l o

/-- **Under the pin's clauses on the halves the private abort tests read the trace through cells
alone.** -/
def Spec.stops_read_cells : Prop :=
  ∀ {S Cl W₀ Rc Xi Tr X : Type} (par : Place → Option (Par × List (ℕ × String × ℕ)))
    (cells : Tr → Cells) (hs : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X))
    (bs : List (Block S Cl)) (u v : Local W₀ Rc Xi Tr),
    PinHalvesAt par cells hs bs → SameCellsAt cells u v → StopsAgreeAt u v hs bs

/-- **Where the tests agree, the chain's function of stops is one.** -/
def Spec.chainStop_of_agree : Prop :=
  ∀ {S Cl W₀ Rc Xi Tr X : Type} (hs : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X))
    (bs : List (Block S Cl)) (u v : Local W₀ Rc Xi Tr), StopsAgreeAt u v hs bs →
    ∀ loc ds, chainStopAt (some u) bs hs loc ds = chainStopAt (some v) bs hs loc ds

/-- **Where every half stands at a member's place and no two at one place, that is every part of
every half.** -/
def Spec.agree_all : Prop :=
  ∀ {S Cl W₀ Rc Xi Tr X : Type} (hs : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X))
    (bs : List (Block S Cl)) (u v : Local W₀ Rc Xi Tr),
    ProofFile.Honest.strays bs hs = [] → ProofFile.Honest.twice hs = [] → StopsAgreeAt u v hs bs →
    ∀ g ∈ hs, ∀ p ∈ g.parts, ∀ l o, p.hid u l o = p.hid v l o

/-- **So under the pin the chain's function of stops reads the trace through cells alone.** -/
def Spec.pinned_stops_read_cells : Prop :=
  ∀ {S Cl W₀ Rc Xi Tr X : Type} (par : Place → Option (Par × List (ℕ × String × ℕ)))
    (cells : Tr → Cells) (hs : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X))
    (bs : List (Block S Cl)) (u v : Local W₀ Rc Xi Tr),
    RowsPinned par cells hs bs → SameCellsAt cells u v →
    ∀ loc ds, chainStopAt (some u) bs hs loc ds = chainStopAt (some v) bs hs loc ds

/-- **The tests agree at the whole first chain of the description, its last member too**: at all
public files in scope that can be read, under LaidAt, at every mats: from the pin at the chain
without its last member, where no half stands at a place of the kind frame. -/
def Spec.first_chain_agree : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl), InScope Z = true →
    ∀ {pp : Inst.Model.ScalesAndPolicy}, readFiles Z = .ok pp → ∀ {D : WholeD} {r : LPFD.Full.RunPF},
    LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF →
    ∀ {W₀ Rc Xi Tr X : Type} (mats : ℕ → List (ℕ × String × ℕ)) (cells : Tr → Cells)
      (hs : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)) (u v : Local W₀ Rc Xi Tr),
      RowsPinned (parOwn Zp mats) cells hs (descZ Zp Np cF).first.blocksInOrder.dropLast →
      (∀ g ∈ hs, g.place.kind ≠ KindName.frame) → SameCellsAt cells u v →
      StopsAgreeAt u v hs (descZ Zp Np cF).first.blocksInOrder

/-- **The function of stops of the whole first chain of the description, its last member too, is one
at the two inputs**: at all public files in scope that can be read, under LaidAt, at every mats:
from the pin at the chain without its last member, where no half stands at a place of the kind
frame. -/
def Spec.first_chain_stops_read_cells : Prop :=
  ∀ (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl), InScope Z = true →
    ∀ {pp : Inst.Model.ScalesAndPolicy}, readFiles Z = .ok pp → ∀ {D : WholeD} {r : LPFD.Full.RunPF},
    LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF →
    ∀ {W₀ Rc Xi Tr X : Type} (mats : ℕ → List (ℕ × String × ℕ)) (cells : Tr → Cells)
      (hs : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)) (u v : Local W₀ Rc Xi Tr),
      RowsPinned (parOwn Zp mats) cells hs (descZ Zp Np cF).first.blocksInOrder.dropLast →
      (∀ g ∈ hs, g.place.kind ≠ KindName.frame) → SameCellsAt cells u v →
      ∀ loc ds, chainStopAt (some u) (descZ Zp Np cF).first.blocksInOrder hs loc ds =
        chainStopAt (some v) (descZ Zp Np cF).first.blocksInOrder hs loc ds

/-- **A part that is given no input never stops by its private abort test.** -/
def Spec.unseen_never_stops_privately : Prop :=
  ∀ {V W X : Type} (p : ProofFile.Honest.Part V W X) (loc ds : List Fmt.Drawn),
    p.stopAt none loc ds ≠ some Why.hid

/-- **A chain that is given no input never stops by a private abort test.** -/
def Spec.unseen_chain_never_stops_privately : Prop :=
  ∀ {S Cl V W X : Type} (bs : List (Block S Cl)) (hs : List (Placed V W X))
    (loc ds : List Fmt.Drawn), chainStopAt (none : Option V) bs hs loc ds ≠ some Why.hid

/-- **In the shared chain the input is never given.** -/
def Spec.shared_sees_none : Prop :=
  ∀ {W₀ Rc Ky : Type} (w : Common W₀ Rc Ky), (Face.shared : Face Empty _ Ky).sees w = none

/-- A negative test on the premise; it counts as no goal. At a member at whose place par names
parameters P, the one half whose one part has a private abort test that differs from
smallStop cells P at some argument does not meet PinHalvesAt. -/
def Spec.other_stop_not_halves : Prop :=
  ∀ {S Cl W₀ Rc Xi Tr X : Type} (par : Place → Option (Par × List (ℕ × String × ℕ)))
    (cells : Tr → Cells) (b : Block S Cl) (P : Par × List (ℕ × String × ℕ))
    (p : ProofFile.Honest.Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X) (u : Local W₀ Rc Xi Tr)
    (l o : List Fmt.Drawn),
    par b.place = some P → p.hid u l o ≠ smallStop cells P u l o →
    ¬ PinHalvesAt par cells ([⟨b.place, [p]⟩] : List (Placed _ _ X)) [b]

/-- A negative test; it counts as no goal. At a member at whose place par names none, the one half
with the one part whose private abort test fires at some argument does not meet PinHalvesAt. -/
def Spec.firing_not_halves : Prop :=
  ∀ {S Cl W₀ Rc Xi Tr X : Type} (par : Place → Option (Par × List (ℕ × String × ℕ)))
    (cells : Tr → Cells) (b : Block S Cl)
    (p : ProofFile.Honest.Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X) (u : Local W₀ Rc Xi Tr)
    (l o : List Fmt.Drawn) (e : String),
    par b.place = none → p.hid u l o = some e →
    ¬ PinHalvesAt par cells ([⟨b.place, [p]⟩] : List (Placed _ _ X)) [b]

/-- A negative test; it counts as no goal. At the one half whose one part has a private abort test
that answers otherwise at u than at v, StopsAgreeAt u v fails. -/
def Spec.differing_not_agree : Prop :=
  ∀ {S Cl W₀ Rc Xi Tr X : Type} (b : Block S Cl)
    (p : ProofFile.Honest.Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X) (u v : Local W₀ Rc Xi Tr)
    (l o : List Fmt.Drawn), p.hid u l o ≠ p.hid v l o →
    ¬ StopsAgreeAt u v ([⟨b.place, [p]⟩] : List (Placed _ _ X)) [b]

/-- A negative test; it counts as no goal. A private abort test that reads the index: at the index
type Bool it fires just where the index is true. At two inputs that differ in the index alone
SameCellsAt holds at every reader and StopsAgreeAt fails; and the rows fail PinHalvesAt at every
par. -/
def Spec.index_reader_fails : Prop :=
  ∀ {S Cl Rc Xi Tr X : Type} (par : Place → Option (Par × List (ℕ × String × ℕ)))
    (cells : Tr → Cells) (b : Block S Cl) (sh : ProofFile.Honest.Odds) (rc : Rc) (x : Xi) (tr : Tr),
    let hs : List (Placed (Local Bool Rc Xi Tr) (Local Bool Rc Xi Tr) X) :=
      [⟨b.place, [quietStop (fun u _ _ => if u.w₀ then some "" else none) sh]⟩]
    SameCellsAt cells ⟨true, rc, x, tr⟩ ⟨false, rc, x, tr⟩ ∧
      ¬ StopsAgreeAt ⟨true, rc, x, tr⟩ ⟨false, rc, x, tr⟩ hs [b] ∧ ¬ PinHalvesAt par cells hs [b]

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.SameCellsAt
#print axioms OnBytes.FrontRoad.StopsAgreeAt
#print axioms OnBytes.FrontRoad.Spec.stops_read_cells
#print axioms OnBytes.FrontRoad.Spec.chainStop_of_agree
#print axioms OnBytes.FrontRoad.Spec.pinned_stops_read_cells
#print axioms OnBytes.FrontRoad.Spec.first_chain_stops_read_cells
#print axioms OnBytes.FrontRoad.Spec.unseen_never_stops_privately
#print axioms OnBytes.FrontRoad.Spec.shared_sees_none
#print axioms OnBytes.FrontRoad.Spec.other_stop_not_halves
#print axioms OnBytes.FrontRoad.Spec.firing_not_halves
#print axioms OnBytes.FrontRoad.Spec.agree_all
#print axioms OnBytes.FrontRoad.Spec.first_chain_agree
#print axioms OnBytes.FrontRoad.Spec.unseen_chain_never_stops_privately
#print axioms OnBytes.FrontRoad.Spec.differing_not_agree
#print axioms OnBytes.FrontRoad.Spec.index_reader_fails
