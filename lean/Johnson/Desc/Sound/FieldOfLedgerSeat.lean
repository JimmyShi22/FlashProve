-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/FieldOfLedgerSeat.lean: **THE TOP CALL OF THE ROW shared_joint_count, AT THE SEATED IOP AS WRITTEN IN LEAN: THE SHARED TABLE's LETTERS AND THE ROW's PIECES AT THEIR PLAIN TYPES (the shared chain's state Desc.K14.St · the clauses ProofFile.Cl · the slot's part ProofFile.InstPub × First.S).**
Two statements; the second's proof is one call of field_of_ledger_at (FieldOfLedger.lean).
What for. ledger_whole (Johnson/Desc/K14/Law/LedgerWhole.lean) ends in EachLawsBN … at pieces of the type Piece (ckP .two) Fr (P₁ × St) Cl W; the fields speak of ((G.pull f).XiPub × (G.pull f).S₁) × (G.pull f).S₂. At G := ProofFile.seatedAt o Z Np c (the term for what onlineDescription returns: descPure_cut,
Johnson/Desc/Plain/StartThreeAtPure.lean) the two are one by unfolding. Here that is held by Lean ONCE, AT LETTERS: a caller hands ledger_whole's term as it is, at P₁ := ProofFile.InstPub × First.S · Cl := ProofFile.Cl.
  start₂_seated           at the seated value two instances with one key have one first state of the shared chain (field_at_laid's premise StartTwoByKey): no premise.
  **field_of_ledger_seat**   field_of_ledger_at at G := ProofFile.seatedAt o Z Np c, its premise StartTwoByKey struck, the letters Mg | Pm | Oc | e₀ | p | l at the plain types.
Limits. L, Glues, the places' two equations and the facts on what is laid are premises. It closes no row. NO SOUNDNESS.

-/
import Johnson.Desc.Sound.FieldOfLedger
import Johnson.Desc.Plain.StartThreeAtPure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LT28
open OnBytes VerifiableInference.Desc
open VerifiableInference.OnPublicFiles VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Shared
open OnBytes.Flat OnBytes.Maker _root_.Run _root_.Run.PQ _root_.Iop
open Desc.K14 (St first)

/-- At the seated value two instances with one key have one first state of the shared chain. -/
theorem start₂_seated (o : ProofFile.SecondHashFunctionArgument) (Z : ProofFile.Pub) (Np : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) : StartTwoByKey (ProofFile.seatedAt o Z Np c) := by
  intro x x' hk
  show first _ x.pub.key = first _ x'.pub.key
  rw [hk]

variable (o : ProofFile.SecondHashFunctionArgument) (Z : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain First.S ProofFile.Cl)

variable {a : ℕ} (Kc : ConfLetters a) (DP : WholeD) {TFp TJp T3p : Type} (tFp : TFp) (tJp : TJp)
  (t3p : T3p) (N : ℕ) (f : Kc.conf.X × Kc.conf.Rec → ProofFile.Inst) (k : Kc.conf.Rec → OnBytes.TableKey)
  {W : Type}
  (T : ThreeAt (ckP .two) (DP.at a) (allOf (DP.at a)) ((ProofFile.seatedAt o Z Np cF).pull f)
    (((ProofFile.seatedAt o Z Np cF).pull f).XiPub × ((ProofFile.seatedAt o Z Np cF).pull f).S₁) (((ProofFile.seatedAt o Z Np cF).pull f).XiPub × ((ProofFile.seatedAt o Z Np cF).pull f).S₁ × ((ProofFile.seatedAt o Z Np cF).pull f).S₂) W)
  (Pl : PPlaces (DP.at a) (allOf (DP.at a)) (((ProofFile.seatedAt o Z Np cF).pull f).XiPub × ((ProofFile.seatedAt o Z Np cF).pull f).S₁)
    ((((ProofFile.seatedAt o Z Np cF).pull f).XiPub × ((ProofFile.seatedAt o Z Np cF).pull f).S₁) × ((ProofFile.seatedAt o Z Np cF).pull f).S₂)
    ((((ProofFile.seatedAt o Z Np cF).pull f).XiPub × ((ProofFile.seatedAt o Z Np cF).pull f).S₁ × ((ProofFile.seatedAt o Z Np cF).pull f).S₂) × ((ProofFile.seatedAt o Z Np cF).pull f).S₃))
  (h₁ : (rowIOR (atDesc ((ProofFile.seatedAt o Z Np cF).pull f) T).p₁ (atDesc ((ProofFile.seatedAt o Z Np cF).pull f) T).l₁).shape =
    uLT (ckP .two) (DP.at a).ds₁)
  (h₂ : (rowIOR (atDesc ((ProofFile.seatedAt o Z Np cF).pull f) T).p₂ (atDesc ((ProofFile.seatedAt o Z Np cF).pull f) T).l₂).shape =
    uLT (ckP .two) (DP.at a).ds₂)
  (h₃ : (rowIOR (atDesc ((ProofFile.seatedAt o Z Np cF).pull f) T).p₃ (atDesc ((ProofFile.seatedAt o Z Np cF).pull f) T).l₃).shape =
    uLT (ckP .two) (DP.at a).ds₃)
  (M : (Kc.conf.X × Kc.conf.Rec) × (oneExternalString (2 ^ (DP.at a).a) SgX).Str →
    (((ProofFile.seatedAt o Z Np cF).pull f).XiPub × ((ProofFile.seatedAt o Z Np cF).pull f).S₁) × (EAll (DP.at a) (allOf (DP.at a))).Str → Prop)
  (L₁ : (((ProofFile.seatedAt o Z Np cF).pull f).XiPub × ((ProofFile.seatedAt o Z Np cF).pull f).S₁) × (EAll (DP.at a) (allOf (DP.at a))).Str → Prop)
  (L₂ : (((ProofFile.seatedAt o Z Np cF).pull f).XiPub × ((ProofFile.seatedAt o Z Np cF).pull f).S₁ × ((ProofFile.seatedAt o Z Np cF).pull f).S₂) ×
    (EAll (DP.at a) (allOf (DP.at a))).Str → Prop)
  (d : (((ProofFile.seatedAt o Z Np cF).pull f).XiPub × ((ProofFile.seatedAt o Z Np cF).pull f).S₁) × (EAll (DP.at a) (allOf (DP.at a))).Str)

/-- **AT THE SEAT.** -/
theorem field_of_ledger_seat (hk : ∀ x rec, (f (x, rec)).pub.key = k rec)
    (file : String) (hD : (ProofFile.seatedAt o Z Np cF).data file = .ok (DP.at a)) (hp : (ProofFile.seatedAt o Z Np cF).planOk = true)
    (b₁ : Block ((ProofFile.seatedAt o Z Np cF).pull f).S₁ ((ProofFile.seatedAt o Z Np cF).pull f).Cl) (l₁ : List (Block ((ProofFile.seatedAt o Z Np cF).pull f).S₁ ((ProofFile.seatedAt o Z Np cF).pull f).Cl))
    (b₂ : Block ((ProofFile.seatedAt o Z Np cF).pull f).S₂ ((ProofFile.seatedAt o Z Np cF).pull f).Cl) (l₂ : List (Block ((ProofFile.seatedAt o Z Np cF).pull f).S₂ ((ProofFile.seatedAt o Z Np cF).pull f).Cl))
    (b₃ : Block ((ProofFile.seatedAt o Z Np cF).pull f).S₃ ((ProofFile.seatedAt o Z Np cF).pull f).Cl) (l₃ : List (Block ((ProofFile.seatedAt o Z Np cF).pull f).S₃ ((ProofFile.seatedAt o Z Np cF).pull f).Cl))
    (e₁ : ((ProofFile.seatedAt o Z Np cF).pull f).first.blocksInOrder = b₁ :: l₁) (e₂ : ((ProofFile.seatedAt o Z Np cF).pull f).shared.blocksInOrder = b₂ :: l₂)
    (e₃ : ((ProofFile.seatedAt o Z Np cF).pull f).second.blocksInOrder = b₃ :: l₃) (rest₁) (rest₂) (rest₃) (d₀ wEnd : W)
    (hT : T = piecesAt (ckP .two) ((ProofFile.seatedAt o Z Np cF).pull f) (DP.at a) b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d₀ wEnd)
    (Ns : NumbersS) (Mg : MeaningS St (ProofFile.InstPub × First.S) W)
    (Pm : PromMeaning St) (Oc : ProofFile.InstPub × First.S → Strs → Prop)
    (split : Bool)
    (e₀ : ℕ → ActV St (frameAt (DP.at a) (allOf (DP.at a)) (DP.at a).key₂
      (atDesc ((ProofFile.seatedAt o Z Np cF).pull f) T).ft₂) → W → W)
    (p : Piece (ckP .two) (frameAt (DP.at a) (allOf (DP.at a)) (DP.at a).key₂
      (atDesc ((ProofFile.seatedAt o Z Np cF).pull f) T).ft₂) ((ProofFile.InstPub × First.S) × St) ProofFile.Cl W)
    (l : List (Piece (ckP .two) (frameAt (DP.at a) (allOf (DP.at a)) (DP.at a).key₂
      (atDesc ((ProofFile.seatedAt o Z Np cF).pull f) T).ft₂) ((ProofFile.InstPub × First.S) × St) ProofFile.Cl W))
    (hp₂ : (atDesc ((ProofFile.seatedAt o Z Np cF).pull f) T).p₂ = p) (hl₂ : (atDesc ((ProofFile.seatedAt o Z Np cF).pull f) T).l₂ = l)
    (hlo : Ns.lo = (DP.at a).t₁)
    (hon : Pl.on₂ = onQ₂ Ns Pm Oc split p l)
    (hQ : Pl.Q₂ = stepAt Ns Mg Pm Oc split p l (extOf Ns p l e₀))
    (L : EachLawsBN (keyAt Prod.snd Ns.lo p l) (onQ₂ Ns Pm Oc split p l)
      (stepAt Ns Mg Pm Oc split p l (extOf Ns p l e₀)) N 0 (p :: l))
    (Gl : Glues (atDesc ((ProofFile.seatedAt o Z Np cF).pull f) T) Pl M L₁ L₂) :
    (plainP Kc DP tFp tJp t3p ((ProofFile.seatedAt o Z Np cF).pull f) (allOf (DP.at a)) T Pl h₁ h₂ h₃ M L₁ L₂ d).K₂.LeadsBN
      (fun c => keyAt Prod.snd (DP.at a).t₁ (atDesc ((ProofFile.seatedAt o Z Np cF).pull f) T).p₂ (atDesc ((ProofFile.seatedAt o Z Np cF).pull f) T).l₂ 0
        ((atDesc ((ProofFile.seatedAt o Z Np cF).pull f) T).in₂ c.1, c.2))
      (plainP Kc DP tFp tJp t3p ((ProofFile.seatedAt o Z Np cF).pull f) (allOf (DP.at a)) T Pl h₁ h₂ h₃ M L₁ L₂ d).on₁
      (fun c e =>
        (plainP Kc DP tFp tJp t3p ((ProofFile.seatedAt o Z Np cF).pull f) (allOf (DP.at a)) T Pl h₁ h₂ h₃ M L₁ L₂ d).on₂ e ∧
        ((plainP Kc DP tFp tJp t3p ((ProofFile.seatedAt o Z Np cF).pull f) (allOf (DP.at a)) T Pl h₁ h₂ h₃ M L₁ L₂ d).L₂ e →
          (plainP Kc DP tFp tJp t3p ((ProofFile.seatedAt o Z Np cF).pull f) (allOf (DP.at a)) T Pl h₁ h₂ h₃ M L₁ L₂ d).L₁ c))
      N (plainP Kc DP tFp tJp t3p ((ProofFile.seatedAt o Z Np cF).pull f) (allOf (DP.at a)) T Pl h₁ h₂ h₃ M L₁ L₂ d).ε₂ ∧
    ∀ x rec y τ b,
      (plainP Kc DP tFp tJp t3p ((ProofFile.seatedAt o Z Np cF).pull f) (allOf (DP.at a)) T Pl h₁ h₂ h₃ M L₁ L₂ d).out₁
        ((x, rec), y) τ = some b →
      keyAt Prod.snd (DP.at a).t₁ (atDesc ((ProofFile.seatedAt o Z Np cF).pull f) T).p₂ (atDesc ((ProofFile.seatedAt o Z Np cF).pull f) T).l₂ 0
          ((atDesc ((ProofFile.seatedAt o Z Np cF).pull f) T).in₂ b.1, b.2) =
        ((s₂Of (ProofFile.seatedAt o Z Np cF) (k rec) : ((ProofFile.seatedAt o Z Np cF).pull f).S₂), y, fun _ _ => none) :=
  field_of_ledger_at Kc DP tFp tJp t3p N f k (ProofFile.seatedAt o Z Np cF) T Pl h₁ h₂ h₃ M L₁ L₂ d hk (start₂_seated o Z Np cF) file hD
    hp b₁ l₁ b₂ l₂ b₃ l₃ e₁ e₂ e₃ rest₁ rest₂ rest₃ d₀ wEnd hT Ns Mg Pm Oc split e₀ p l hp₂ hl₂ hlo hon hQ L
    Gl

end LT28

#print axioms LT28.start₂_seated
#print axioms LT28.field_of_ledger_seat
