-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K03PiecesAt.lean: the kind "lookup" (K3), at the constant: TWO OF THE
PREMISES IN FRONT OF K03_law's COUNTED FORM (Johnson/P5J/K03Kind.lean) FROM THE ONE HEAD `AtMg`.

Why. The
two theorems that are called are typed at `pureDesc Z A B c`, the constant at `F0T secondHashFunction Zp Np cF`.
The two are one by `rfl`, but without what follows Lean ran the call more than seven minutes and was
stopped. So: the three facts on the description (its data, `sealLast`, `planOk`) are stated
first, AT `pureDesc Zp (seatZ Zp Np) (secondAt Zp Np) cF`; the call has its letters Z, A, B, c by
name; and the witnesses' cells are named as the constant's own free letters have them
(`CellsM numsFull`). And in `k03_base_at` the test bookFit is asked at `First.toldOf`
(Johnson/Desc/First/NumbersAtBlocks.lean), while `k03_fenced` has `Sound.toldOf`
(Johnson/Desc/Sound/PieceFence.lean): two texts of one function (`flatten` · `flatMap id`):
`told_two` says so.

Main names:
  `k03_pieces_at`: `K3Pieces` AT THE CONSTANT's OWN ROW, from the head and "the pieces are the
    pieces of the description's own three lists": so that premise falls (`k03_pieces_seated`,
    Johnson/Desc/First/Look/K3PiecesSeated.lean, called).
  `k03_base_at`: "every sampled tenant that is open in front of a lookup argument lies below its
    piece", at all fifty, at the constant's own row and numbers, under three named tests (blocksOk ·
    bookFit · fenceFit): the sentence of the ledger's fields base and hbaseS, to the letter, and,
    with the pins' openness, of hbase (`k03_fenced`, K3Fenced.lean, called).
  `k03_kind_tight`: `h.Kind 𝔇₀ 𝔏 .K3` from the head, q₁ q₂ q₃, hDl (Dl.up = (h.𝔇 𝔇₀).sent),
    `K3PlanR` and `K3OwedR`.

Limits: `K3PlanR`, `K3OwedR` and the three tests are premises; the ledger is shown at no value and
not shown satisfiable. At secondHashFunction alone. Nothing on soundness by itself; nothing on hiding.


-/
import Johnson.P5J.K03Kind
import Johnson.Desc.First.Look.K3PiecesSeated
import Johnson.Desc.First.Look.K3Fenced

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA OnBytes.Model
open Inst.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain KindName Wit)
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open Johnson.Desc.First.Walk.Tied (RchAt)
open Desc.K14.Law (secondAt seatZ)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- The two texts of "what each block tells" are one function. -/
theorem told_two {St Cl : Type} (bs : List (VerifiableInference.Desc.Block St Cl)) :
    VerifiableInference.Desc.Sound.toldOf bs = VerifiableInference.Desc.First.toldOf bs := by
  unfold VerifiableInference.Desc.Sound.toldOf VerifiableInference.Desc.First.toldOf
  exact List.map_congr_left fun _ _ => List.flatMap_id

set_option maxHeartbeats 4000000 in
/-- **THE FACTS ON THE PIECES, AT THE CONSTANT's OWN ROW, FROM THE ONE HEAD.** -/
theorem k03_pieces_at (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) :
    K3Pieces (At.X Zp) Zp.first.codes Zp.first.shape (h.row 𝔏) := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hD : (pureDesc Zp (seatZ Zp Np) (secondAt Zp Np) cF).data "proof file" =
      .ok (D.at frS.P.T.a) := by
    rw [LaidAt.atDepth h.scope h.laid]; exact h.laid.data
  have hs : (pureDesc Zp (seatZ Zp Np) (secondAt Zp Np) cF).sealLast = true :=
    sealLast_of_planOk (F0T OnBytes.secondHashFunction Zp Np cF) h.laid.planOk
  have hp : (pureDesc Zp (seatZ Zp Np) (secondAt Zp Np) cF).planOk = true := h.laid.planOk
  have e := k03_pieces_seated (Z := Zp) (A := seatZ Zp Np) (B := secondAt Zp Np) (c := cF)
    (Cells := CellsM numsFull) (Tok := At.Tok)
    h.scope h.reads O "proof file" (D.at frS.P.T.a) hD hs 𝔏.c₁ 𝔏.k₁ 𝔏.c₂ 𝔏.k₂ 𝔏.c₃ 𝔏.k₃
    q₁ q₂ q₃ 𝔏.e₁ 𝔏.e₂ 𝔏.e₃ 𝔏.dW 𝔏.wEnd hp
  rw [O.W] at e
  exact e

set_option maxHeartbeats 4000000 in
/-- **EVERY SAMPLED TENANT OF A PIN THAT IS OPEN IN FRONT OF A LOOKUP ARGUMENT SITS BELOW ITS
PIECE's BASE, AT THE CONSTANT's OWN ROW.** That these are all that the lookup reads is not said
here. -/
theorem k03_base_at (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (hb : VerifiableInference.Desc.blocksOk ((F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.map
      (held (P := (F0T OnBytes.secondHashFunction Zp Np cF).XiPub))) = true)
    (hf : VerifiableInference.Desc.First.bookFit (At.N Zp cF)
      (VerifiableInference.Desc.First.flatPlacesOf linksFull true)
      (VerifiableInference.Desc.First.toldOf ((F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.map
        (held (P := (F0T OnBytes.secondHashFunction Zp Np cF).XiPub)))) = true)
    (hg : VerifiableInference.Desc.First.fenceFit (At.N Zp cF) linksFull
      (VerifiableInference.Desc.First.flatPlacesOf linksFull true) = true) :
    ∀ l, l < 25 → ∀ (dd : Bool) q, (h.row 𝔏)[k3K l dd]? = some q →
      ∀ x ∈ VerifiableInference.Desc.First.sampledIn (At.N Zp cF)
        ((VerifiableInference.Desc.First.openSets linksFull
          (VerifiableInference.Desc.First.flatPlacesOf linksFull true)
          (VerifiableInference.Desc.First.start linksFull))[k3K l dd]?.getD []), x.1 < q.base := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hD : (pureDesc Zp (seatZ Zp Np) (secondAt Zp Np) cF).data "proof file" =
      .ok (D.at frS.P.T.a) := by
    rw [LaidAt.atDepth h.scope h.laid]; exact h.laid.data
  have hs : (pureDesc Zp (seatZ Zp Np) (secondAt Zp Np) cF).sealLast = true :=
    sealLast_of_planOk (F0T OnBytes.secondHashFunction Zp Np cF) h.laid.planOk
  exact k03_fenced (Z := Zp) (A := seatZ Zp Np) (B := secondAt Zp Np) (c := cF)
    (Cells := CellsM numsFull) (Tok := At.Tok)
    h.scope h.reads O "proof file" (D.at frS.P.T.a) hD hs 𝔏.c₁ 𝔏.k₁ 𝔏.c₂ 𝔏.k₂ 𝔏.c₃ 𝔏.k₃
    q₁ q₂ q₃ 𝔏.e₁ 𝔏.e₂ 𝔏.e₃ 𝔏.dW 𝔏.wEnd (At.N Zp cF) hb (by rw [told_two]; exact hf) hg

/-- **K03's CONDITION, NAMED: THE PUBLIC PARAMETERS' TESTS AND THE LEDGER WITH EACH DEBT ONCE.** -/
theorem k03_kind_tight (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp))
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    {seats : List (ℕ × ℕ)} {s₀ : VerifiableInference.Desc.First.S} {num : ℕ → ℕ → ℕ}
    {idx : ℕ → ℕ → ℕ} {tls : ℕ → HTailF2}
    {tok : Wit (CellsQ numsFull.rows (colsAt numsFull)) At.Tok MsgT → Fin ppref.V}
    {told : List (List VerifiableInference.Desc.Oracle)} {arrs : Array (Nat × String)}
    {Dl : VerifiableInference.Desc.K3Asks.Sent} {floor : ℕ} (z₀ : ProofFile.InstPub)
    (hDl : Dl.up = (h.𝔇 𝔇₀).sent)
    (hP : letI := k3SizesAt (At.X Zp)
      letI := k3PolicyAt (At.X Zp)
      K3PlanR (At.X Zp) Dl (h.𝔇 𝔇₀).l3 floor)
    (W : K3OwedR (h.𝔇 𝔇₀) mgBase (RchAt (F0T OnBytes.secondHashFunction Zp Np cF)) Zp.first.codes
      Zp.first.shape (h.row 𝔏) seats s₀ num idx tls tok told arrs) :
    h.Kind 𝔇₀ 𝔏 KindName.K3 :=
  k03_kind_owed h 𝔇₀ 𝔏 q₁ q₂ q₃ z₀ hDl hP (k03_pieces_at h 𝔏 q₁ q₂ q₃) W

end P5J

#print axioms P5J.k03_pieces_at
#print axioms P5J.k03_base_at
#print axioms P5J.k03_kind_tight
