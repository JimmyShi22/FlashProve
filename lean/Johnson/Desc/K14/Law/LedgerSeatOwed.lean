-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerSeatOwed.lean: SEVEN SENTENCES THAT row8_top | k14_law_top STILL BEAR AS
PREMISES AND THAT NOBODY HOLDS, EACH STATED AT THE SEAT. DEFINITIONS ALONE: NOTHING IS PROVED HERE.
As letters (any first chain, any tests) they are false or empty; so each is closed under the
premises that tie the letters: the files are in scope · proofDataAndDecisionOfPublicFiles returns · onlineDescription returns the
proof file's IOP as written in Lean at the seat (seatFF) · pub · placesOfMade.

  seatFF          the IOP as written in Lean at the seat, in fieldF's spelling (fieldF_of_pure,
                  Johnson/Desc/K14/Law/LedgerSeatIs.lean, gives onlineDescription's value in this form).
  SeatTies        the five ties.
  TestsTwoOwed    htl: the shared chain has two proximity tests (N.O is some).
  SealLastOwed    hsl. · PlanOkOwed  hGp. · FlatsOwed  h₁f h₂f h₃f: no chain's list of sub-protocols
                  is empty. · DataIsLaidOwed  hDw with hlaid: the data of seatFF at some file name
                  IS what proofDataAndDecisionOfPublicFiles returns.
  StartByKeyOwed  hG: two instances with one key have one first state of the shared chain.
  ShapesOwed      h₁ h₂ h₃: general in the IOP: the three rows' shapes are the data's lists of
                  rounds.
WHO CALLS THEM: row8_top (Johnson/Desc/K14/Law/Row8Top.lean) · k14_law_top (LedgerLawTop.lean), at
oH := o · mkL := ProofFile.pureRoad.links · Zp := Z · … as seatFF spells.

-/
import Johnson.Desc.K14.Law.LedgerSeatIs
import Johnson.Desc.Sound.FieldOfFills

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Maker OnBytes.Flat _root_.Run _root_.Run.PQ _root_.Iop
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.K12.Seat (tests)

/-- The proof file's IOP as written in Lean at the seat, in fieldF's spelling. -/
abbrev seatFF (o : ProofFile.SecondHashFunctionArgument) (Z : ProofFile.Pub) (N : H2U.Places4) (B' : ProofFile.SecondSeat)
    (c : Chain First.S ProofFile.Cl) : FileDescription ProofFile.Inst :=
  fieldF o ProofFile.pureRoad.links Z (seatN Z N).lot (seatN Z N).start (seatN Z N).ended
    (seatN Z N).okInst (seatN Z N).fileOk (seatN Z N).standIns B' (fun s => s) (ProofFile.startS Z) c
    Z.p.chains (p14Of Z.p.chains (beforePointOf N)) (tests N)

/-- The premises that tie the letters. -/
def SeatTies (o : ProofFile.SecondHashFunctionArgument) (S : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Z : ProofFile.Pub)
    (N : H2U.Places4) (B' : ProofFile.SecondSeat) (c : Chain First.S ProofFile.Cl) : Prop :=
  VerifierAndGoals.InScope S = true ∧ LPFD.Full.proofDataAndDecisionOfPublicFiles o S.pol S.lay S.KL = .ok (D, r) ∧
    ProofFile.onlineDescription o S.pol S.lay S.KL = .ok (seatFF o Z N B' c) ∧
    ProofFile.pureRoad.pub o S.pol S.lay S.KL = .ok Z ∧ H2U.placesOfMade Z.made = .ok N

/-- OWED (htl). -/
def TestsTwoOwed : Prop :=
  ∀ o S D r Z N B' c, SeatTies o S D r Z N B' c → (tests N).length = 2

/-- OWED (hsl). -/
def SealLastOwed : Prop :=
  ∀ o S D r Z N B' c, SeatTies o S D r Z N B' c → (seatFF o Z N B' c).sealLast = true

/-- OWED (hGp). -/
def PlanOkOwed : Prop :=
  ∀ o S D r Z N B' c, SeatTies o S D r Z N B' c → (seatFF o Z N B' c).planOk = true

/-- OWED (h₁f h₂f h₃f). -/
def FlatsOwed : Prop :=
  ∀ o S D r Z N B' c, SeatTies o S D r Z N B' c →
    (∃ c₁ k₁, (seatFF o Z N B' c).first.blocksInOrder = c₁ :: k₁) ∧
      (∃ c₂ k₂, (seatFF o Z N B' c).shared.blocksInOrder = c₂ :: k₂) ∧
      ∃ c₃ k₃, (seatFF o Z N B' c).second.blocksInOrder = c₃ :: k₃

/-- OWED (hDw with hlaid, at one letter). -/
def DataIsLaidOwed : Prop :=
  ∀ o S D r Z N B' c, SeatTies o S D r Z N B' c →
    ∃ file, (seatFF o Z N B' c).data file = .ok D

/-- OWED (hG). -/
def StartByKeyOwed : Prop :=
  ∀ o Z N B' c, LT28.StartTwoByKey (seatFF o Z N B' c)

/-- OWED (h₁ h₂ h₃): general in the IOP as written in Lean. -/
def ShapesOwed : Prop :=
  ∀ (Xi' W : Type) (G : FileDescription ProofFile.Inst) (f : Xi' → ProofFile.Inst) (D : WholeD) (file : String),
    G.data file = .ok D → G.planOk = true →
    ∀ (b₁ : Block G.S₁ G.Cl) (l₁ : List (Block G.S₁ G.Cl)) (b₂ : Block G.S₂ G.Cl)
      (l₂ : List (Block G.S₂ G.Cl)) (b₃ : Block G.S₃ G.Cl) (l₃ : List (Block G.S₃ G.Cl)),
      G.first.blocksInOrder = b₁ :: l₁ → G.shared.blocksInOrder = b₂ :: l₂ → G.second.blocksInOrder = b₃ :: l₃ →
      ∀ rest₁ rest₂ rest₃ (d₀ wEnd : W),
        (rowIOR (atDesc (G.pull f) (piecesAt (ckP .two) (G.pull f) D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂
            rest₃ d₀ wEnd)).p₁ (atDesc (G.pull f) (piecesAt (ckP .two) (G.pull f) D b₁ l₁ b₂ l₂ b₃
            l₃ rest₁ rest₂ rest₃ d₀ wEnd)).l₁).shape = uLT (ckP .two) D.ds₁ ∧
          (rowIOR (atDesc (G.pull f) (piecesAt (ckP .two) (G.pull f) D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂
            rest₃ d₀ wEnd)).p₂ (atDesc (G.pull f) (piecesAt (ckP .two) (G.pull f) D b₁ l₁ b₂ l₂ b₃
            l₃ rest₁ rest₂ rest₃ d₀ wEnd)).l₂).shape = uLT (ckP .two) D.ds₂ ∧
          (rowIOR (atDesc (G.pull f) (piecesAt (ckP .two) (G.pull f) D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂
            rest₃ d₀ wEnd)).p₃ (atDesc (G.pull f) (piecesAt (ckP .two) (G.pull f) D b₁ l₁ b₂ l₂ b₃
            l₃ rest₁ rest₂ rest₃ d₀ wEnd)).l₃).shape = uLT (ckP .two) D.ds₃

end Desc.K14.Law
