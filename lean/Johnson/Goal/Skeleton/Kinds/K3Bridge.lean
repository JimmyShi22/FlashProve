-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Skeleton/Kinds/K3Bridge.lean: the kind K3 (lookup): its files' own named conditions,
gathered into one proposition under the head `P5J.AtMgA`, give the kind's field in the form in which
a kind's law is counted, `P5J.AtMgA.Kind h 𝔏 .K3` (Johnson/P5J/RowsAtAll.lean). Here idx : ℕ
→ ℕ → ℕ. The conditions stand AT THE FORM'S OWN
CONDITION BESIDE THE PROMISE, `h.toAtMg.rch` ("reached, at a typed instance's public part"), not
at every state of `RchAt`: they ask less.

  `AtMgA.K3Cond h 𝔏`: there are letters seats, s₀, num, idx, tls, tok, told, arrs, Dl, floor and a
    public part z₀ with: "Dl.up is what the parameters send", `K3PlanR`, `K3Pieces`, and `K3OwedR`
    (Johnson/Desc/Sound/MgAt/K3Owed.lean) at 𝔇 := h.toAtMg.𝔇 h.𝔇, Mg := mgBase, Rch := h.toAtMg.rch,
    the pieces h.toAtMg.row 𝔏. But for Rch these are the four premises of `P5J.k03_kind_owed`
    (Johnson/P5J/K03Kind.lean) to the letter.
  `k03_kind_all`: the three lists' heads are 𝔏's → `h.K3Cond 𝔏` → `h.Kind 𝔏 .K3`. The proof is
    `P5J.k03_kind`'s own, with `h.toAtMg.rch` in `RchAt`'s place: `k03_law_mgAllX` is
    general in the condition beside the promise.
  `k03_kind_bare`: the same end from K3's files' premises at bare "reached": `k03_kind_owed` and
    `AtMgA.kind_of_reached`.

Limits. IT PAYS NOTHING.

idx has a value for each link. WHETHER THE CONDITION CAN
BE MET IS SHOWN NOWHERE. At
`OnBytes.secondHashFunction` alone. No member is known. No soundness is claimed.

-/
import Johnson.P5J.RowsAtAll
import Johnson.P5J.K03Kind

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J

/- The names in scope are those of Johnson/P5J/K03Kind.lean's second half. -/
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open Inst.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain KindName Wit)
open VerifiableInference.Desc.Sound
open Johnson.Desc.First.Walk.Tied (RchAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **The lookup kind's named conditions, at the closed constant and the form's own condition
beside the promise.** -/
def AtMgA.K3Cond (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok) : Prop :=
  ∃ (seats : List (ℕ × ℕ)) (s₀ : VerifiableInference.Desc.First.S) (num : ℕ → ℕ → ℕ)
    (idx : ℕ → ℕ → ℕ) (tls : ℕ → HTailF2)
    (tok : Wit (CellsQ numsFull.rows (colsAt numsFull)) At.Tok MsgT → Fin ppref.V)
    (told : List (List VerifiableInference.Desc.Oracle)) (arrs : Array (Nat × String))
    (Dl : VerifiableInference.Desc.K3Asks.Sent) (floor : ℕ) (_ : ProofFile.InstPub),
    Dl.up = (h.toAtMg.𝔇 h.𝔇).sent ∧
    (letI := k3SizesAt (At.X Zp)
     letI := k3PolicyAt (At.X Zp)
     K3PlanR (At.X Zp) Dl (h.toAtMg.𝔇 h.𝔇).l3 floor) ∧
    K3Pieces (At.X Zp) Zp.first.codes Zp.first.shape (h.toAtMg.row 𝔏) ∧
    K3OwedR (Fr := frameAt (D.at OnBytes.Slice.frS.P.T.a) (allOf (D.at OnBytes.Slice.frS.P.T.a))
        (D.at OnBytes.Slice.frS.P.T.a).key₁ 0)
      (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch Zp.first.codes
      Zp.first.shape (h.toAtMg.row 𝔏) seats s₀ num idx tls tok told arrs

set_option maxHeartbeats 4000000 in
/-- **The field.** -/
theorem k03_kind_all (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (C : h.K3Cond 𝔏) : h.Kind 𝔏 KindName.K3 := by
  obtain ⟨seats, s₀, num, idx, tls, tok, told, arrs, Dl, floor, z₀, hDl, hP, hQ, W⟩ := C
  obtain ⟨Bs, base, O⟩ := h.toAtMg.laid.opened
  have hT := h.toAtMg.ofDesc 𝔏 q₁ q₂ q₃
  exact k03_law_mgAllX O.W h.toAtMg.scope h.toAtMg.reads O hT (h.toAtMg.𝔇 h.𝔇) mgBase
    h.toAtMg.rch (h.toAtMg.ex 𝔏)
    (fun l hl d a b w => by
      unfold AtMg.ex exF
      exact k03_ext_idle _ _ _ _ _ _ _ _ _ _ l hl d a b w) z₀ hDl hP hQ (k3Rest_of_owed W)

/-- The same end from K3's files' premises at bare "reached". -/
theorem k03_kind_bare (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    {seats : List (ℕ × ℕ)} {s₀ : VerifiableInference.Desc.First.S} {num : ℕ → ℕ → ℕ}
    {idx : ℕ → ℕ → ℕ} {tls : ℕ → HTailF2}
    {tok : Wit (CellsQ numsFull.rows (colsAt numsFull)) At.Tok MsgT → Fin ppref.V}
    {told : List (List VerifiableInference.Desc.Oracle)} {arrs : Array (Nat × String)}
    {Dl : VerifiableInference.Desc.K3Asks.Sent} {floor : ℕ} (z₀ : ProofFile.InstPub)
    (hDl : Dl.up = (h.toAtMg.𝔇 h.𝔇).sent)
    (hP : letI := k3SizesAt (At.X Zp)
      letI := k3PolicyAt (At.X Zp)
      K3PlanR (At.X Zp) Dl (h.toAtMg.𝔇 h.𝔇).l3 floor)
    (hQ : K3Pieces (At.X Zp) Zp.first.codes Zp.first.shape (h.toAtMg.row 𝔏))
    (W : K3OwedR (h.toAtMg.𝔇 h.𝔇) mgBase (RchAt (F0T OnBytes.secondHashFunction Zp Np cF)) Zp.first.codes
      Zp.first.shape (h.toAtMg.row 𝔏) seats s₀ num idx tls tok told arrs) :
    h.Kind 𝔏 KindName.K3 :=
  h.kind_of_reached 𝔏 KindName.K3 (k03_kind_owed h.toAtMg h.𝔇 𝔏 q₁ q₂ q₃ z₀ hDl hP hQ W)

end P5J

#print axioms P5J.k03_kind_all
#print axioms P5J.k03_kind_bare
