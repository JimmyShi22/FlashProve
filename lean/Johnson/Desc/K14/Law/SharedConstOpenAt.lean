-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstOpenAt.lean: THE SHARED TABLE's CONSTANT AT A PROOF FILE's SEAT: THE
OPEN LETTERS (ShOpen, Johnson/Desc/K14/Law/SharedConst.lean) AS Sh.planAt CLOSES THE PARAMETERS.
Seven of the thirteen speak of the verifier's public value Z or want the seat's own types (P₀ :=
ProofFile.InstPub, P₁ := its pair with the first chain's state). SharedConst.lean stays general in its
type letters: they are closed at the seat. HERE the four that want no more than Z and the IOP as
written in Lean; the cells' three (c₀, matC, held) are arguments here and are closed in
Johnson/Desc/K14/Law/SharedConstHeldAt.lean.

  Sh.Open₁ Cells Tok Q THE FIRST TABLE's CONSTANT's FIVE, a field each: N₁ links Mg₁ smp₁ ms₁:
                       what the first table's composed meaning's constant will give
  Sh.seatF o Z N B' cF the IOP as written in Lean, in the form in which the verifier makes it
  Sh.openAt₀ …         ShOpen at the seat: arr := the one numbering over all three chains, off Z
                       (P5T.arrOf (P5T.planSeatsAll Z Z.D)) · get := the pair as it stands · Pw :=
                       K13.whereOf Z · R := "p is a reached last state of the first chain (the
                       predicate EndAt₁ at seatF), AND ITS PUBLIC INSTANCE IS A TYPED INSTANCE's"
                       (∃ z, p.1 = (LPFD.Full.instanceAsPlainRecord z).pub: so its key has the planned sizes) ·
                       the rest from Open₁ · c₀, matC, held: arguments
  Sh.hlin_at           the ledger's top's hlin at the seat, from Written Z x
  Sh.R_of_rch          "reached" at the shared chain (RchAt₂: its second half) and "the public
                       instance is a typed instance's" give R of the handed state
WHAT IS NOT HERE. No law. The six.
What is not claimed. No soundness of a verifier; no level.

-/
import Johnson.Desc.K14.Law.SharedConstAt
import Johnson.Desc.K14.Law.SharedFlat
import Johnson.P5T.PlanSeats
import Johnson.Desc.ProofFile.Lot.K13
import Johnson.Top.H0.Walk.ReachThree
import Johnson.Desc.Laid.ProofInstFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words wordsOn)
open Johnson.Pack
open _root_.Run.PQ (CK)
open Cb Cb.Ood Blocks Cb.Pv Cb.Pv.Lin Cb.Bridge
open VerifiableInference.Desc (Block Strs Wit FileDescription First.S Grows)
open VerifiableInference.Desc.ChainEnd (untestedL Exact)
open VerifiableInference.Desc.K1 (sendPiece sampledAt shapeAt shapesOf condPort errPort seedEntry
  seedMaps)
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Pub pubSets openSets start)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts Seat.onGu Seat.onGomega)
open VerifiableInference.Desc.K12.Coin
open Desc.K14.Law.Fence
open H2K.Pin (NTuple)
open H2K.Pub (johOk batV0 PayPub)
open H2K.First (batOneOk)
open VerifiableInference.Desc.K13.Law (EvalAt laidOf wSitsItem wSitsMore)
open VerifiableInference.Desc.Third (P₁₄)

open Johnson.Desc.First.Walk.Tied (EndAt₁ RchAt₂)

namespace Sh

/-- **The first table's constant's six.** -/
structure Open₁ (Cells Tok : Type) (Q : P14) where
  N₁ : Numbers
  links : List ModelPart
  Mg₁ : Meaning ProofFile.InstPub (Wit Cells Tok MsgT)
  smp₁ : ProofFile.InstPub × First.S → (s : Sending) → (i : Fin s.l.length) →
    Option ((sigOf Q.codes s.l).om i).Smp
  ms₁ : List Mem

/-- **The IOP as written in Lean, in the form in which the verifier makes it.** -/
abbrev seatF (o : ProofFile.SecondHashFunctionArgument) (Z : ProofFile.Pub) (N : H2U.Places4) (B' : ProofFile.SecondSeat)
    (cF : VerifiableInference.Desc.Chain First.S ProofFile.Cl) : FileDescription ProofFile.Inst :=
  ProofFile.fileDescBy o ProofFile.pureRoad.links Z (seatN Z N) B' (fun s => s) (ProofFile.startS Z) cF

variable {Cells Tok : Type} (o : ProofFile.SecondHashFunctionArgument) (Z : ProofFile.Pub) (N : H2U.Places4)
  (B' : ProofFile.SecondSeat) (cF : VerifiableInference.Desc.Chain First.S ProofFile.Cl)

/-- **The open letters at the seat**, but for the cells' three. -/
def openAt₀ (c₀ : Cells) (matC : Cells → Nat → Nat → GE)
    (held : ((ixOf2 (planAt Z N (seatF o Z N B' cF)).Q.par.S.fold 0 2852142980
      (rankLib (planAt Z N (seatF o Z N B' cF)).Q.par.S.fold)).Row ×
      Fin (planAt Z N (seatF o Z N B' cF)).Q.par.S.fold.index.code.ell → GE) → Option Cells)
    (O₁ : Open₁ Cells Tok (planAt Z N (seatF o Z N B' cF)).Q) :
    ShOpen ProofFile.InstPub (ProofFile.InstPub × First.S) Cells Tok (planAt Z N (seatF o Z N B' cF)).Q where
  arr := P5T.arrOf (P5T.planSeatsAll Z Z.D)
  c₀ := c₀
  get := fun a => (a.1, a.2)
  smp₁ := O₁.smp₁
  ms₁ := O₁.ms₁
  N₁ := O₁.N₁
  links := O₁.links
  Mg₁ := O₁.Mg₁
  Pw := VerifiableInference.Desc.K13.whereOf Z
  R := fun p => EndAt₁ (seatF o Z N B' cF) p ∧
    ∃ z : LPFD.Full.XF × RecFull, p.1 = (LPFD.Full.instanceAsPlainRecord z).pub
  matC := matC
  held := held

variable (c₀ : Cells) (matC : Cells → Nat → Nat → GE)
  (held : ((ixOf2 (planAt Z N (seatF o Z N B' cF)).Q.par.S.fold 0 2852142980
    (rankLib (planAt Z N (seatF o Z N B' cF)).Q.par.S.fold)).Row ×
    Fin (planAt Z N (seatF o Z N B' cF)).Q.par.S.fold.index.code.ell → GE) → Option Cells)
  (O₁ : Open₁ Cells Tok (planAt Z N (seatF o Z N B' cF)).Q)

/-- **The top's hlin at the seat.** -/
theorem hlin_at {x : LinSized} (h : Written Z x) :
    (openAt₀ o Z N B' cF c₀ matC held O₁).Pw.lin = (planAt Z N (seatF o Z N B' cF)).Q.par.S := by
  show Z.first.lin = Z.p.chains.made.sized.proof.batch.shape
  rw [h.lin, h.shape]

/-- **"Reached" at the shared chain, at a typed instance, gives R of the handed state.** -/
theorem R_of_rch {Str : Type} (k : ℕ)
    (a : (((seatF o Z N B' cF).XiPub × (seatF o Z N B' cF).S₁) × (seatF o Z N B' cF).S₂) × Str)
    (hR : RchAt₂ (seatF o Z N B' cF) k a)
    (hz : ∃ z : LPFD.Full.XF × RecFull, a.1.1.1 = (LPFD.Full.instanceAsPlainRecord z).pub) :
    (openAt₀ o Z N B' cF c₀ matC held O₁).R a.1.1 := ⟨hR.2, hz⟩

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.hlin_at
#print axioms Desc.K14.Law.Sh.R_of_rch
