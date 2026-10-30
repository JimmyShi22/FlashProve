-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/SimulatorAtTheBase.lean: what the kind "the code switch" owes to zero knowledge of the
honest prover.

1. The honest prover is honestProvers (E2E/TheHonestProver.lean). Its online part is made by onlineProverFromPublicFiles
   at the filling onlineFilling, which is the base filling onlineProverPartsInUse read through. Nothing
   here crosses from the base filling to the term: that crossing is one law for the whole file.
2. switchSimLotAt is the kind's lot with a simulator beside each part: a value of the type SLot,
   at a reader of the index and of the tables' randomness. baseSimLot is its value at the base
   filling.
3. The first statement: with the simulators forgotten it is the base filling's second lot, and
   where the maker returns at that filling the sides of this kind are its sides, in order.
4. The second: where the maker returns, at any filling, the rows of the lot are at 25 places, no two
   at one place, each of this kind; every block of this kind in the first chain is one of them.
5. The third: at any filling each row seats a side that meets the fields fits, exact and fresh of
   Good, at the description that the maker returns. That this is the description of the term's
   family is the named proposition ReturnIsTheDescription of the term's file, owed there.
6. Good is taken at the condition "never" for its A and B, so its fields plays and acc say nothing
   here; exact and fresh also hold where part and simulator both show nothing. They count only
   beside the statements on what this kind plays at the same 25 places, made apart.
7. exact and fresh are equations of laws over the part's own coins, at every state that meets their
   premises and at every carried coin. The tables' randomness is part of the state: so it is fixed.
8. The fourth: this kind's share of the field bud₁ of BudDebts (Honest/Law/OwedRule.lean). The
   fifth: no part of a row stops. The sixth: where the lot's public test says yes at the state's
   instance, the part shows something at every coin, so exact is no equation of two nothings there.
   The seventh: the test says yes at every instance that the description's okStart admits. That a
   served request passes okStart is the condition left, T1's OkStartAtServedRequests, holder
   unsettled. The eighth: no spending entry of the book names a part of this kind. Of the field owed
   of Owed, On is True at this kind; that the book lends a called part its carried coins and that
   the run reaches it stay with the statements on what it plays.
9. No side of the two other chains stands at a place of this kind: the first statement's end. The
   field fresh of Good here is asked at every address, so it pays what a spender of this kind's
   coins asks of its owner. That this kind has no fall is our reading of its
   block, said here; no Lean says it. Written at T1's sum (stripped).
10. This file proves nothing. Every proposition in it is a definition of type Prop. At the stored
    files the maker returns at the base filling: `baseReturn_atStoredFiles`
    (AtFullSide/HonestTrace/EntersAtStoredFiles.lean).
-/
import E2E.TheHonestProver
import Johnson.Desc.ProofFile.Honest.K2.Rows
import Johnson.Desc.ProofFile.Honest.Thread.RowsByPub
import Johnson.Desc.ProofFile.Honest.Law.OwedRule

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.K2
open ProofFile.Honest ProofFile.Honest.Term ProofFile.Honest.K2
open AtPublicFiles.AtFiles AtPublicFiles.Cut

section
variable {W₀ Rc X₀ X : Type}

/-- **The kind's sides with their simulators**, at a reader of the index and of the tables'
randomness. Its data of the main rows is the filling's. -/
def switchSimLotAt (weights : ProofFile.Pub → W₀ → Weights) (coins : Rc → IndexCommitterCoins) :
    SLot (Local W₀ Rc ProofFile.Inst Cells) (Local W₀ Rc ProofFile.Inst Cells) X ProofFile.Inst :=
  SLot.byPub weights fun wt =>
    SLot.byRows (widerRows OnBytes.HonestTrace.Sz.ref) fun D =>
      switchSLot D fun w => ⟨w.trace, wt w.w₀, coins w.rc⟩

/-- **The rows' places are the kind's places in the first chain**, at what the maker returned at a
filling. -/
def PlacesAreTheKinds (files : VerifierAndGoals.PublicFiles) : Prop :=
  ∀ (W₀ Rc X₀ X : Type) (P : OnlineProverParts W₀ Rc Cells X₀ X) (A : OnlineProverWithDescription W₀ Rc Cells X₀ X),
    onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL P = .ok A →
    (switchPlaces A.Z A.G).length = 25 ∧ ((switchPlaces A.Z A.G).map (·.place)).Nodup ∧
    (∀ p ∈ switchPlaces A.Z A.G, p.place.kind = .K2) ∧
    ∀ b ∈ A.F.first.blocksInOrder, b.place.kind = .K2 → ∃ p ∈ switchPlaces A.Z A.G, p.place = b.place

/-- **Each row seats a side that meets fits, exact and fresh**, at the book and the order of places
of what the maker returned, at every list of falls and every list of earlier reads. -/
def SidesMeetGood (files : VerifierAndGoals.PublicFiles) : Prop :=
  ∀ (W₀ Rc X₀ X : Type) (P : OnlineProverParts W₀ Rc Cells X₀ X) (A : OnlineProverWithDescription W₀ Rc Cells X₀ X),
    onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL P = .ok A →
    ∀ (weights : ProofFile.Pub → W₀ → Weights) (coins : Rc → IndexCommitterCoins),
    ∀ r ∈ (switchSimLotAt (X := X) weights coins).rows A.Z A.G, ∀ fs : List (Fall A.F.S₁),
      ∃ σ, Side.seated A.F.first.blocksInOrder r.place r.row fs = some σ ∧
        ∀ pre, Good pre .own σ A.B (orderOf A.F) 0 0 (fun _ _ _ _ => False)
          (fun _ _ _ _ => False) r.On r.bud

/-- **The bound on the positions read**, in the words of the field bud₁ of BudDebts
(Honest/Law/OwedRule.lean). -/
def PositionsWithinBound (files : VerifierAndGoals.PublicFiles) : Prop :=
  ∀ (W₀ Rc X₀ X : Type) (P : OnlineProverParts W₀ Rc Cells X₀ X) (A : OnlineProverWithDescription W₀ Rc Cells X₀ X),
    onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL P = .ok A →
    ∀ (weights : ProofFile.Pub → W₀ → Weights) (coins : Rc → IndexCommitterCoins),
    ∀ r ∈ (switchSimLotAt (X := X) weights coins).rows A.Z A.G, ∀ σ,
      Side.seated A.F.first.blocksInOrder r.place r.row = some σ → ∀ u ∈ σ.members, ∀ pre t n,
        A.F.first.blocksInOrder = pre ++ σ.block :: t →
        n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number →
        ∀ ρ : Draws, ρ.due A.F = true →
          r.bud u.number ((ρ.first.drop n).take u.rounds.length)
            (asksFrom (treeAsks A.F ρ 0) (u.rounds.map (·.2.length))
              (((rowsOfChain A.F.first.blocksInOrder).take n).map (·.2.length)).sum)

end

/-- **Where the public test says yes the part shows something**, at every coin. -/
def ShowsSomeWhereFit (files : VerifierAndGoals.PublicFiles) : Prop :=
  ∀ (W₀ Rc X₀ X : Type) (P : OnlineProverParts W₀ Rc Cells X₀ X) (A : OnlineProverWithDescription W₀ Rc Cells X₀ X),
    onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL P = .ok A →
    ∀ (weights : ProofFile.Pub → W₀ → Weights) (coins : Rc → IndexCommitterCoins),
    ∀ r ∈ (switchSimLotAt (X := X) weights coins).rows A.Z A.G, ∀ (fs : List (Fall A.F.S₁)) σ,
      Side.seated A.F.first.blocksInOrder r.place r.row fs = some σ → ∀ u ∈ σ.members,
      ∀ (c : u.part.Coins) (m : Mid (Local W₀ Rc ProofFile.Inst Cells) X) (ds : List Fmt.Drawn)
        (asks : List (List (List Nat))), drawsFit (u.rounds.map (·.1)) ds = true →
        (∀ p ∈ switchPlaces A.Z A.G, p.place = r.place →
          publicOk (widerRows OnBytes.HonestTrace.Sz.ref A.Z A.G) A.G.first.layout p
            ((segmentsOf A.Z A.G).take p.link) m.st.input.x = true) →
        σ.shows .own u c m ds asks ≠ none

/-- **The public test says yes at every instance that the description admits.** -/
def PublicTestSaysYes (files : VerifierAndGoals.PublicFiles) : Prop :=
  ∀ (W₀ Rc X₀ X : Type) (P : OnlineProverParts W₀ Rc Cells X₀ X) (A : OnlineProverWithDescription W₀ Rc Cells X₀ X),
    onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL P = .ok A →
    ∀ ξ : ProofFile.Inst, A.F.okStart ξ = true → ∀ p ∈ switchPlaces A.Z A.G,
      publicOk (widerRows OnBytes.HonestTrace.Sz.ref A.Z A.G) A.G.first.layout p
        ((segmentsOf A.Z A.G).take p.link) ξ = true

/-- **No spending entry of the book names a part of this kind.** -/
def KindSpendsNothing (files : VerifierAndGoals.PublicFiles) : Prop :=
  ∀ (W₀ Rc Tr X₀ X : Type) (P : OnlineProverParts W₀ Rc Tr X₀ X) (A : OnlineProverWithDescription W₀ Rc Tr X₀ X),
    onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL P = .ok A →
    ∀ e ∈ A.B.ahead, e.once = true → e.spender.place.kind ≠ .K2

/-- **No part of a row stops**: neither stop says anything, at every argument. -/
def NoPartStops : Prop :=
  ∀ (W₀ Rc X : Type) (weights : ProofFile.Pub → W₀ → Weights) (coins : Rc → IndexCommitterCoins) (Z : ProofFile.Pub)
    (G : ProofFile.Ground), ∀ r ∈ (switchSimLotAt (X := X) weights coins).rows Z G, ∀ x ∈ r.row,
      (∀ l o, x.1.bad l o = none) ∧ ∀ u l o, x.1.hid u l o = none

/-- **The lot at the base prover**: at the matrices, at the tables' own randomness. -/
abbrev baseSimLot : SLot (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit
    ProofFile.Inst :=
  switchSimLotAt matrixInput.weights id

/-- **With the simulators forgotten it is the base filling's second lot.** -/
def LotIsTheFillings : Prop :=
  (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest).lots[1]? =
    some baseSimLot.toHLot

/-- **The sides of this kind at the base filling are the rows' sides, in order**: no other lot lays
a side of the kind. -/
def SidesAreTheRows (files : VerifierAndGoals.PublicFiles) : Prop :=
  ∀ A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit,
    onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest) = .ok A →
    A.H.first.filter (fun x => x.place.kind == .K2) = (baseSimLot.rows A.Z A.G).map (·.half) ∧
      A.H.shared.filter (fun x => x.place.kind == .K2) = [] ∧
      A.H.second.filter (fun x => x.place.kind == .K2) = []

/-- **What a proof of this kind's simulator has to give**, at public files that the library's test
accepts. -/
def SimulatorAtTheBase : Prop :=
  NoPartStops ∧ LotIsTheFillings ∧
  ∀ files : VerifierAndGoals.PublicFiles, VerifierAndGoals.InScope files = true →
    FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true →
    SidesAreTheRows files ∧ PlacesAreTheKinds files ∧ SidesMeetGood files ∧
      PositionsWithinBound files ∧ ShowsSomeWhereFit files ∧ PublicTestSaysYes files ∧
      KindSpendsNothing files

end AtFullSide.K2
