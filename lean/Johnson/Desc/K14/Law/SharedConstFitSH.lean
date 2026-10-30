-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstFitSH.lean: THE FIELD SH OF "THE TABLES FIT" (the
structure TablesFitR, Johnson/P5J/TopTablesR.lean), IN THE FIELD's OWN LETTERS, AT THE SHARED
TABLE's CONSTANT AT THE SEAT. SH: at every statement b at the first chain's last border that stands
in the first table's promise and meets Rc, the shared table's book-keeping clause accepts the shared
chain's first state. At the seat Rc := the constant's R: "a reached end of the first chain, at a
typed instance's public part". The second half gives the instance; at a typed full-size instance's
key the clause is a theorem (Sh.shape_start_at).

  Sh.SH_at        **the field SH.** The first table's promise (on₁) and R's first half are not
                  spent.
WHAT STAYS. hA : AtFull Z.p.chains.made (in scope).
What is not claimed. No soundness; no level.

-/
import Johnson.Desc.K14.Law.SharedConstZeroAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

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

namespace Sh

/-- **TablesFitR's field SH, at the constant at the seat.** -/
theorem SH_at {S₃' Y X₁ X₂ Cells Tok : Type} (o : ProofFile.SecondHashFunctionArgument) (Z : ProofFile.Pub)
    (N : H2U.Places4) (B' : ProofFile.SecondSeat)
    (cF : VerifiableInference.Desc.Chain First.S ProofFile.Cl) (c₀ : Cells)
    (matC : Cells → Nat → Nat → GE)
    (held : ((ixOf2 (planAt Z N (seatF o Z N B' cF)).Q.par.S.fold 0 2852142980
      (rankLib (planAt Z N (seatF o Z N B' cF)).Q.par.S.fold)).Row ×
        Fin (planAt Z N (seatF o Z N B' cF)).Q.par.S.fold.index.code.ell → GE) → Option Cells)
    (O₁ : Open₁ Cells Tok (planAt Z N (seatF o Z N B' cF)).Q) (D : WholeD) (all : List LeftT)
    (T : Three (ckP .two) D all Y (ProofFile.InstPub × First.S) ((ProofFile.InstPub × First.S) × St)
      ((ProofFile.InstPub × First.S × St) × S₃') X₁ X₂ ProofFile.Cl (Wit Cells Tok MsgT))
    (Q : Places D all (ProofFile.InstPub × First.S) ((ProofFile.InstPub × First.S) × St)
      ((ProofFile.InstPub × First.S × St) × S₃') (Wit Cells Tok MsgT))
    (R₀ : (ProofFile.InstPub × First.S) × (EAll D all).Str → Wit Cells Tok MsgT → Prop)
    (hA : H2K.Sizes.AtFull Z.p.chains.made) :
    ∀ b : (ProofFile.InstPub × First.S) × (EAll D all).Str,
      (placesM T.ft₁ O₁.N₁ O₁.Mg₁ O₁.links (ps (planAt Z N (seatF o Z N B' cF)) (openAt₀ o Z N B' cF
          c₀ matC held O₁))
        (fun a => (a.1, a.2)) R₀ Q).on₁ (1 + T.l₁.length) b →
      (openAt₀ o Z N B' cF c₀ matC held O₁).R b.1 →
      (pm (planAt Z N (seatF o Z N B' cF)) (openAt₀ o Z N B' cF c₀ matC held O₁)).shape 0 ((seatF o
          Z N B' cF).start₂ b.1.1) = true := by
  intro b _ hr
  obtain ⟨z, hz⟩ := hr.2
  rw [hz]
  exact shape_start_at Z N (seatF o Z N B' cF) (openAt₀ o Z N B' cF c₀ matC held O₁) z hA

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.SH_at
