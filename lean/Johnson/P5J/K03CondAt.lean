-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K03CondAt.lean: the kind "lookup" (K3): THE KIND's NAMED CONDITION `AtMgA.K3Cond h 𝔏`
(Johnson/Goal/Skeleton/Kinds/K3Bridge.lean) AT CLOSED LETTERS, FROM WHAT IS STILL
OWED ALONE: so that what is paid at the constant is seen to fit the condition's own form, and what
is left stands as the premises of one theorem.

Main name: `k03_cond_at`: at seats := `At.seats Zp`, Dl := `K3Asks.sentOf Zp`, floor :=
`k3FloorAt (At.X Zp)`: PAID HERE: "Dl.up is what the parameters send" · the five sentences on the
constant's terms (Johnson/P5J/K03Terms.lean) · `K3PlanR` (Johnson/P5J/K03PlanAt.lean) · `K3Pieces`
at the constant's row (Johnson/P5J/K03PiecesAt.lean).
LEFT, AS PREMISES: "the pieces are the pieces of the description's own three lists" (q₁, q₂, q₃) ·
two rows of the door (tests with code) · the facts along the fold (`K3Fold`) and the four families
of the ledger (`DigOwedR`, `AttOwedR`, `LayOwedR`, `HeadRestR`): `K3LeftR`
(Johnson/Desc/Sound/MgAt/K3OwedLeft.lean).

Limits: it pays none of the ledger's tests, facts along the fold or fields "where the piece
accepts". num, idx, tls, tok, told, arrs, s₀ are letters here. No member of the condition is known.
At secondHashFunction alone. Nothing on soundness by itself; nothing on hiding.


-/
import Johnson.Goal.Skeleton.Kinds.K3Bridge
import Johnson.P5J.K03Terms
import Johnson.P5J.K03PlanAt
import Johnson.P5J.K03PiecesAt
import Johnson.Desc.Sound.MgAt.K3OwedLeft

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open Inst.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain KindName Wit)
open VerifiableInference.Desc.Sound

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **The condition at closed letters, from what is still owed.** -/
theorem k03_cond_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (s₀ : VerifiableInference.Desc.First.S) (num : ℕ → ℕ → ℕ) (idx : ℕ → ℕ → ℕ)
    (tls : ℕ → HTailF2)
    (tok : Wit (CellsQ numsFull.rows (colsAt numsFull)) At.Tok MsgT → Fin ppref.V)
    (told : List (List VerifiableInference.Desc.Oracle)) (arrs : Array (Nat × String))
    (z₀ : ProofFile.InstPub)
    (hDig : VerifiableInference.Desc.K3Asks.digRow (At.X Zp)
      (VerifiableInference.Desc.K3Asks.sentOf Zp) = true)
    (hHead : VerifiableInference.Desc.K3Asks.headRow (At.X Zp) = true)
    (V : K3LeftR
      (Fr := frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
        (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
      (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch Zp.first.codes Zp.first.shape (h.toAtMg.row 𝔏)
      (At.seats Zp) s₀ num idx tls tok told arrs) :
    h.K3Cond 𝔏 :=
  ⟨At.seats Zp, s₀, num, idx, tls, tok, told, arrs, VerifiableInference.Desc.K3Asks.sentOf Zp,
    k3FloorAt (At.X Zp), z₀, k03_hDl_sentOf h, k03_planR_at h hDig hHead,
    k03_pieces_at h.toAtMg 𝔏 q₁ q₂ q₃,
    k3Owed_of_left k03_hM (k03_es h) (k03_hD h) (k03_hd h) k03_hIn V⟩

end P5J

#print axioms P5J.k03_cond_at
