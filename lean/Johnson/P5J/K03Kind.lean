-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K03Kind.lean: K03_law IN THE COUNTED FORM's END: the kind "lookup" (K3)'s share of the
chain of promises AT THE CONSTANT: `AtMg.Kind h 𝔇₀ 𝔏 KindName.K3` (Johnson/P5J/RowsAtMg.lean: the
form in which a kind's files end its law: `KindTiedR (At.N Zp cF) (mgAt h 𝔇₀) fullLinks At.ps
(RchAt (F0T o Zp Np cF)) (h.ex 𝔏) (h.row 𝔏) K`), at the second hash function.

Main names:
  `k03_law_mgAllX`: `k03_law_mgAll` (Johnson/Desc/Sound/MgAt/K3Mean.lean) with the public
    parameters as a letter X and "the opening's public parameters are X" as a premise.
  `k03_kind`: under the one head `AtMg OnBytes.secondHashFunction Z D r Zp Np cF` and "the pieces are the pieces
    of the description's own three lists" (q₁, q₂, q₃): `K3PlanR` · `K3Pieces` · `K3RestR` AT THE
    CONSTANT's OWN LETTERS (𝔇 := h.𝔇 𝔇₀ · Mg := mgBase · Rch := `RchAt (F0T …)`, THE ONE "reached" ·
    pieces := h.row 𝔏), with hDl (Dl.up = (h.𝔇 𝔇₀).sent), give `h.Kind 𝔇₀ 𝔏 .K3`.
    PAID HERE: the scope, the files' reading and the
    maker's opening (the head's fields) · `OfDesc` (`AtMg.ofDesc`) · "the table's extractor lays
    nothing at the kind's places" (`k03_ext_idle`) · that the two spellings of the written list,
    of the numbers and of the meaning are one (by unfolding).

  `k03_kind_owed`: the same from `K3OwedR` (Johnson/Desc/Sound/MgAt/K3Owed.lean): THE
    LEDGER WITH EACH DEBT ONCE: this is the kind's condition, named.

idx : ℕ → ℕ → ℕ (a letter of each segment), with the ledger's mend: see
Johnson/Desc/Sound/MgAt/K3Mean.lean's head.

Limits: the three structures are premises: the ledger (`K3RestR`, `K3OwedR`) is shown at no value
and not shown satisfiable. At secondHashFunction alone (the kind's lot is opened there). Nothing on soundness
by itself; nothing on hiding.


-/
import Johnson.P5J.RowsAtMg
import Johnson.Desc.Sound.MgAt.K3Owed
import Johnson.Desc.First.Look.K3ExtIdle

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open Inst.Model Inst.Model.All
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Meaning ModelPart shift)
open VerifiableInference.Desc (Wit KindName)

local notation "PS" => Desc.First.flatPlacesOf linksFull true

/-- **The law at the composed meaning, the public parameters a letter.** -/
theorem k03_law_mgAllX {Pf : VerifierAndGoals.PublicFiles} {pp₀ : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : Desc.FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase}
    {base : List (Desc.Block Desc.First.S ProofFile.Cl)} {c : Desc.Chain Desc.First.S ProofFile.Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    {X : Verify.Public} (hW : Bs.G₀.W = X)
    (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B)
    {Tok Xi : Type} {rows cols nR : ℕ} {D : WholeD} {all : List LeftT} {X₁ X₂ : Type}
    {T : ThreeAt (ckP .two) D all
      (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s) (ProofFile.startS Z) c)
      X₁ X₂ (Wit (CellsQ rows cols) Tok MsgT)}
    (hT : OfDesc _ T) (𝔇 : MgData Xi ProofFile.InstPub Tok rows cols nR X)
    (Mg : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))
    (Rch : ℕ → (ProofFile.InstPub × Desc.First.S) × (frameAt D all D.key₁ T.ft₁).E.Str → Prop)
    (E : ℕ → (ProofFile.InstPub × Desc.First.S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      (ProofFile.InstPub × Desc.First.S) × (frameAt D all D.key₁ T.ft₁).E.Str →
      Wit (CellsQ rows cols) Tok MsgT → Wit (CellsQ rows cols) Tok MsgT)
    (hE : ∀ l, l < 25 → ∀ d : Bool, ∀ a b w, E (k3K l d) a b w = w)
    {seats : List (ℕ × ℕ)} {s₀ : Desc.First.S} {num : ℕ → ℕ → ℕ} {idx : ℕ → ℕ → ℕ}
    {tls : ℕ → HTailF2} {tok : Wit (CellsQ rows cols) Tok MsgT → Fin ppref.V}
    {nx : ℕ → Bool → Desc.Place} {told : List (List Desc.Oracle)}
    {arrs : Array (Nat × String)}
    {Dl : Desc.K3Asks.Sent} {floor : ℕ} (z₀ : ProofFile.InstPub) (hDl : Dl.up = 𝔇.sent)
    (hP : letI := k3SizesAt X
      letI := k3PolicyAt X
      K3PlanR X Dl 𝔇.l3 floor)
    (hQ : K3Pieces X Z.first.codes Z.first.shape (T.p₁ :: T.l₁))
    (R : K3RestR 𝔇 Mg Rch Z.first.codes Z.first.shape (T.p₁ :: T.l₁) seats s₀ num idx tls tok nx
      told arrs) :
    KindTiedR 𝔇.N (mgAll 𝔇 Mg) linksFull PS Rch E (T.p₁ :: T.l₁) KindName.K3 := by
  subst hW
  exact k03_law_mgAll hS hR O hT 𝔇 Mg Rch E hE z₀ hDl hP hQ R

end VerifiableInference.OnPublicFiles

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open Inst.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain KindName Wit)
open VerifiableInference.Desc.Sound
open Johnson.Desc.First.Walk.Tied (RchAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

set_option maxHeartbeats 4000000 in
/-- **K03_law, ENDING IN THE FORM THAT COUNTS.** -/
theorem k03_kind (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub At.Tok numsFull.rows (colsAt numsFull) nR (At.X Zp))
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    {seats : List (ℕ × ℕ)} {s₀ : VerifiableInference.Desc.First.S} {num : ℕ → ℕ → ℕ}
    {idx : ℕ → ℕ → ℕ} {tls : ℕ → HTailF2}
    {tok : Wit (CellsQ numsFull.rows (colsAt numsFull)) At.Tok MsgT → Fin ppref.V}
    {nx : ℕ → Bool → VerifiableInference.Desc.Place}
    {told : List (List VerifiableInference.Desc.Oracle)} {arrs : Array (Nat × String)}
    {Dl : VerifiableInference.Desc.K3Asks.Sent} {floor : ℕ} (z₀ : ProofFile.InstPub)
    (hDl : Dl.up = (h.𝔇 𝔇₀).sent)
    (hP : letI := k3SizesAt (At.X Zp)
      letI := k3PolicyAt (At.X Zp)
      K3PlanR (At.X Zp) Dl (h.𝔇 𝔇₀).l3 floor)
    (hQ : K3Pieces (At.X Zp) Zp.first.codes Zp.first.shape (h.row 𝔏))
    (R : K3RestR (h.𝔇 𝔇₀) mgBase (RchAt (F0T OnBytes.secondHashFunction Zp Np cF)) Zp.first.codes
      Zp.first.shape (h.row 𝔏) seats s₀ num idx tls tok nx told arrs) :
    h.Kind 𝔇₀ 𝔏 KindName.K3 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hT := h.ofDesc 𝔏 q₁ q₂ q₃
  exact k03_law_mgAllX O.W h.scope h.reads O hT (h.𝔇 𝔇₀) mgBase
    (RchAt (F0T OnBytes.secondHashFunction Zp Np cF)) (h.ex 𝔏)
    (fun l hl d a b w => by
      unfold AtMg.ex exF
      exact k03_ext_idle _ _ _ _ _ _ _ _ _ _ l hl d a b w) z₀ hDl hP hQ R

/-- **THE SAME, FROM THE LEDGER WITH EACH DEBT ONCE.** -/
theorem k03_kind_owed (h : AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {nR : ℕ}
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
    (hQ : K3Pieces (At.X Zp) Zp.first.codes Zp.first.shape (h.row 𝔏))
    (W : K3OwedR (h.𝔇 𝔇₀) mgBase (RchAt (F0T OnBytes.secondHashFunction Zp Np cF)) Zp.first.codes
      Zp.first.shape (h.row 𝔏) seats s₀ num idx tls tok told arrs) :
    h.Kind 𝔇₀ 𝔏 KindName.K3 :=
  k03_kind h 𝔇₀ 𝔏 q₁ q₂ q₃ z₀ hDl hP hQ (k3Rest_of_owed W)

end P5J

#print axioms VerifiableInference.OnPublicFiles.k03_law_mgAllX
#print axioms P5J.k03_kind
#print axioms P5J.k03_kind_owed
