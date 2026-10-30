-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/FieldOfLedger.lean: **THE TOP CALL OF THE ROW shared_joint_count, ITS GENERAL HALF: FROM THE LEDGER's END (the law for N slots at every one of the shared chain's pieces, at the key by make, at a named filling of the shared table's letters) TO THE TWO FIELDS, AT THE TOP's OWN LETTERS.**
Two statements; the first's proof is one call of field_at_laid (StartTwoAtPure.lean) behind three rewritings; the second is the first with the row's head and tail named (field_of_ledger_at).
  **field_of_ledger**   field_at_laid's premises on what is laid · a filling Ns | Mg | Pm | Oc | e₀ of the shared table's letters with Ns.lo = t₁ · the places' two equations (Pl.on₂ is the table's condition onQ₂, Pl.Q₂ is the table's relation stepAt, at that filling)
                        · L : EachLawsBN (keyAt Prod.snd Ns.lo p₂ l₂) (onQ₂ …) (stepAt … (extOf …)) N 0 (p₂ :: l₂) · Glues
                        ⊢ the shared chain's reduction leads, for N slots, at the key by make, from the first border's condition to the second's ∧ all slots of a batch have one key at the shared chain's head.
L IS, SIGN FOR SIGN, THE END OF ledger_whole (Johnson/Desc/K14/Law/LedgerWhole.lean) at f := p₂ and (PT :: MM) := l₂: so the row's top is field_of_ledger … (ledger_whole …).
Against field_of_debts_at_laid (StartTwoAtPure.lean): that one starts at the kinds' plain laws for one statement and makes L inside; this one takes L as it is handed.
Limits. L, Glues and the two equations are premises. It closes no row. NO SOUNDNESS.

-/
import Johnson.Desc.Sound.StartTwoAtPure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LT28
open OnBytes VerifiableInference.Desc
open VerifiableInference.OnPublicFiles VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Shared
open OnBytes.Flat OnBytes.Maker _root_.Run _root_.Run.PQ _root_.Iop

variable {a : ℕ} (Kc : ConfLetters a) (DP : WholeD) {TFp TJp T3p : Type} (tFp : TFp) (tJp : TJp)
  (t3p : T3p) (N : ℕ) (f : Kc.conf.X × Kc.conf.Rec → ProofFile.Inst) (k : Kc.conf.Rec → OnBytes.TableKey)
  (G : FileDescription ProofFile.Inst) {W : Type}
  (T : ThreeAt (ckP .two) (DP.at a) (allOf (DP.at a)) (G.pull f)
    ((G.pull f).XiPub × (G.pull f).S₁) ((G.pull f).XiPub × (G.pull f).S₁ × (G.pull f).S₂) W)
  (Pl : PPlaces (DP.at a) (allOf (DP.at a)) ((G.pull f).XiPub × (G.pull f).S₁)
    (((G.pull f).XiPub × (G.pull f).S₁) × (G.pull f).S₂)
    (((G.pull f).XiPub × (G.pull f).S₁ × (G.pull f).S₂) × (G.pull f).S₃))
  (h₁ : (rowIOR (atDesc (G.pull f) T).p₁ (atDesc (G.pull f) T).l₁).shape =
    uLT (ckP .two) (DP.at a).ds₁)
  (h₂ : (rowIOR (atDesc (G.pull f) T).p₂ (atDesc (G.pull f) T).l₂).shape =
    uLT (ckP .two) (DP.at a).ds₂)
  (h₃ : (rowIOR (atDesc (G.pull f) T).p₃ (atDesc (G.pull f) T).l₃).shape =
    uLT (ckP .two) (DP.at a).ds₃)
  (M : (Kc.conf.X × Kc.conf.Rec) × (oneExternalString (2 ^ (DP.at a).a) SgX).Str →
    ((G.pull f).XiPub × (G.pull f).S₁) × (EAll (DP.at a) (allOf (DP.at a))).Str → Prop)
  (L₁ : ((G.pull f).XiPub × (G.pull f).S₁) × (EAll (DP.at a) (allOf (DP.at a))).Str → Prop)
  (L₂ : ((G.pull f).XiPub × (G.pull f).S₁ × (G.pull f).S₂) ×
    (EAll (DP.at a) (allOf (DP.at a))).Str → Prop)
  (d : ((G.pull f).XiPub × (G.pull f).S₁) × (EAll (DP.at a) (allOf (DP.at a))).Str)

/-- **FROM THE LEDGER's END TO THE TWO FIELDS.** -/
theorem field_of_ledger (hk : ∀ x rec, (f (x, rec)).pub.key = k rec) (hG : StartTwoByKey G)
    (file : String) (hD : G.data file = .ok (DP.at a)) (hp : G.planOk = true)
    (b₁ : Block (G.pull f).S₁ (G.pull f).Cl) (l₁ : List (Block (G.pull f).S₁ (G.pull f).Cl))
    (b₂ : Block (G.pull f).S₂ (G.pull f).Cl) (l₂ : List (Block (G.pull f).S₂ (G.pull f).Cl))
    (b₃ : Block (G.pull f).S₃ (G.pull f).Cl) (l₃ : List (Block (G.pull f).S₃ (G.pull f).Cl))
    (e₁ : (G.pull f).first.blocksInOrder = b₁ :: l₁) (e₂ : (G.pull f).shared.blocksInOrder = b₂ :: l₂)
    (e₃ : (G.pull f).second.blocksInOrder = b₃ :: l₃) (rest₁) (rest₂) (rest₃) (d₀ wEnd : W)
    (hT : T = piecesAt (ckP .two) (G.pull f) (DP.at a) b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d₀ wEnd)
    (Ns : NumbersS) (Mg : MeaningS (G.pull f).S₂ ((G.pull f).XiPub × (G.pull f).S₁) W)
    (Pm : PromMeaning (G.pull f).S₂) (Oc : (G.pull f).XiPub × (G.pull f).S₁ → Strs → Prop)
    (split : Bool)
    (e₀ : ℕ → ActV (G.pull f).S₂ (frameAt (DP.at a) (allOf (DP.at a)) (DP.at a).key₂
      (atDesc (G.pull f) T).ft₂) → W → W)
    (hlo : Ns.lo = (DP.at a).t₁)
    (hon : Pl.on₂ = onQ₂ Ns Pm Oc split (atDesc (G.pull f) T).p₂ (atDesc (G.pull f) T).l₂)
    (hQ : Pl.Q₂ = stepAt Ns Mg Pm Oc split (atDesc (G.pull f) T).p₂ (atDesc (G.pull f) T).l₂
      (extOf Ns (atDesc (G.pull f) T).p₂ (atDesc (G.pull f) T).l₂ e₀))
    (L : EachLawsBN (keyAt Prod.snd Ns.lo (atDesc (G.pull f) T).p₂ (atDesc (G.pull f) T).l₂)
      (onQ₂ Ns Pm Oc split (atDesc (G.pull f) T).p₂ (atDesc (G.pull f) T).l₂)
      (stepAt Ns Mg Pm Oc split (atDesc (G.pull f) T).p₂ (atDesc (G.pull f) T).l₂
        (extOf Ns (atDesc (G.pull f) T).p₂ (atDesc (G.pull f) T).l₂ e₀)) N 0
      ((atDesc (G.pull f) T).p₂ :: (atDesc (G.pull f) T).l₂))
    (Gl : Glues (atDesc (G.pull f) T) Pl M L₁ L₂) :
    (plainP Kc DP tFp tJp t3p (G.pull f) (allOf (DP.at a)) T Pl h₁ h₂ h₃ M L₁ L₂ d).K₂.LeadsBN
      (fun c => keyAt Prod.snd (DP.at a).t₁ (atDesc (G.pull f) T).p₂ (atDesc (G.pull f) T).l₂ 0
        ((atDesc (G.pull f) T).in₂ c.1, c.2))
      (plainP Kc DP tFp tJp t3p (G.pull f) (allOf (DP.at a)) T Pl h₁ h₂ h₃ M L₁ L₂ d).on₁
      (fun c e =>
        (plainP Kc DP tFp tJp t3p (G.pull f) (allOf (DP.at a)) T Pl h₁ h₂ h₃ M L₁ L₂ d).on₂ e ∧
        ((plainP Kc DP tFp tJp t3p (G.pull f) (allOf (DP.at a)) T Pl h₁ h₂ h₃ M L₁ L₂ d).L₂ e →
          (plainP Kc DP tFp tJp t3p (G.pull f) (allOf (DP.at a)) T Pl h₁ h₂ h₃ M L₁ L₂ d).L₁ c))
      N (plainP Kc DP tFp tJp t3p (G.pull f) (allOf (DP.at a)) T Pl h₁ h₂ h₃ M L₁ L₂ d).ε₂ ∧
    ∀ x rec y τ b,
      (plainP Kc DP tFp tJp t3p (G.pull f) (allOf (DP.at a)) T Pl h₁ h₂ h₃ M L₁ L₂ d).out₁
        ((x, rec), y) τ = some b →
      keyAt Prod.snd (DP.at a).t₁ (atDesc (G.pull f) T).p₂ (atDesc (G.pull f) T).l₂ 0
          ((atDesc (G.pull f) T).in₂ b.1, b.2) =
        ((s₂Of G (k rec) : (G.pull f).S₂), y, fun _ _ => none) := by
  refine field_at_laid Kc DP tFp tJp t3p N f k G T Pl h₁ h₂ h₃ M L₁ L₂ d hk hG file hD hp b₁ l₁ b₂ l₂ b₃
    l₃ e₁ e₂ e₃ rest₁ rest₂ rest₃ d₀ wEnd hT ?_ Gl
  rw [hon, hQ, ← hlo]
  exact L

/-- **The same, with the row's head and tail named**: so that a caller hands the ledger's term as it is. -/
theorem field_of_ledger_at (hk : ∀ x rec, (f (x, rec)).pub.key = k rec) (hG : StartTwoByKey G)
    (file : String) (hD : G.data file = .ok (DP.at a)) (hp : G.planOk = true)
    (b₁ : Block (G.pull f).S₁ (G.pull f).Cl) (l₁ : List (Block (G.pull f).S₁ (G.pull f).Cl))
    (b₂ : Block (G.pull f).S₂ (G.pull f).Cl) (l₂ : List (Block (G.pull f).S₂ (G.pull f).Cl))
    (b₃ : Block (G.pull f).S₃ (G.pull f).Cl) (l₃ : List (Block (G.pull f).S₃ (G.pull f).Cl))
    (e₁ : (G.pull f).first.blocksInOrder = b₁ :: l₁) (e₂ : (G.pull f).shared.blocksInOrder = b₂ :: l₂)
    (e₃ : (G.pull f).second.blocksInOrder = b₃ :: l₃) (rest₁) (rest₂) (rest₃) (d₀ wEnd : W)
    (hT : T = piecesAt (ckP .two) (G.pull f) (DP.at a) b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d₀ wEnd)
    (Ns : NumbersS) (Mg : MeaningS (G.pull f).S₂ ((G.pull f).XiPub × (G.pull f).S₁) W)
    (Pm : PromMeaning (G.pull f).S₂) (Oc : (G.pull f).XiPub × (G.pull f).S₁ → Strs → Prop)
    (split : Bool)
    (e₀ : ℕ → ActV (G.pull f).S₂ (frameAt (DP.at a) (allOf (DP.at a)) (DP.at a).key₂
      (atDesc (G.pull f) T).ft₂) → W → W)
    (p : Piece (ckP .two) (frameAt (DP.at a) (allOf (DP.at a)) (DP.at a).key₂
      (atDesc (G.pull f) T).ft₂) (((G.pull f).XiPub × (G.pull f).S₁) × (G.pull f).S₂) (G.pull f).Cl W)
    (l : List (Piece (ckP .two) (frameAt (DP.at a) (allOf (DP.at a)) (DP.at a).key₂
      (atDesc (G.pull f) T).ft₂) (((G.pull f).XiPub × (G.pull f).S₁) × (G.pull f).S₂) (G.pull f).Cl W))
    (hp₂ : (atDesc (G.pull f) T).p₂ = p) (hl₂ : (atDesc (G.pull f) T).l₂ = l)
    (hlo : Ns.lo = (DP.at a).t₁)
    (hon : Pl.on₂ = onQ₂ Ns Pm Oc split p l)
    (hQ : Pl.Q₂ = stepAt Ns Mg Pm Oc split p l (extOf Ns p l e₀))
    (L : EachLawsBN (keyAt Prod.snd Ns.lo p l) (onQ₂ Ns Pm Oc split p l)
      (stepAt Ns Mg Pm Oc split p l (extOf Ns p l e₀)) N 0 (p :: l))
    (Gl : Glues (atDesc (G.pull f) T) Pl M L₁ L₂) :
    (plainP Kc DP tFp tJp t3p (G.pull f) (allOf (DP.at a)) T Pl h₁ h₂ h₃ M L₁ L₂ d).K₂.LeadsBN
      (fun c => keyAt Prod.snd (DP.at a).t₁ (atDesc (G.pull f) T).p₂ (atDesc (G.pull f) T).l₂ 0
        ((atDesc (G.pull f) T).in₂ c.1, c.2))
      (plainP Kc DP tFp tJp t3p (G.pull f) (allOf (DP.at a)) T Pl h₁ h₂ h₃ M L₁ L₂ d).on₁
      (fun c e =>
        (plainP Kc DP tFp tJp t3p (G.pull f) (allOf (DP.at a)) T Pl h₁ h₂ h₃ M L₁ L₂ d).on₂ e ∧
        ((plainP Kc DP tFp tJp t3p (G.pull f) (allOf (DP.at a)) T Pl h₁ h₂ h₃ M L₁ L₂ d).L₂ e →
          (plainP Kc DP tFp tJp t3p (G.pull f) (allOf (DP.at a)) T Pl h₁ h₂ h₃ M L₁ L₂ d).L₁ c))
      N (plainP Kc DP tFp tJp t3p (G.pull f) (allOf (DP.at a)) T Pl h₁ h₂ h₃ M L₁ L₂ d).ε₂ ∧
    ∀ x rec y τ b,
      (plainP Kc DP tFp tJp t3p (G.pull f) (allOf (DP.at a)) T Pl h₁ h₂ h₃ M L₁ L₂ d).out₁
        ((x, rec), y) τ = some b →
      keyAt Prod.snd (DP.at a).t₁ (atDesc (G.pull f) T).p₂ (atDesc (G.pull f) T).l₂ 0
          ((atDesc (G.pull f) T).in₂ b.1, b.2) =
        ((s₂Of G (k rec) : (G.pull f).S₂), y, fun _ _ => none) := by
  subst hp₂ hl₂
  exact field_of_ledger Kc DP tFp tJp t3p N f k G T Pl h₁ h₂ h₃ M L₁ L₂ d hk hG file hD hp b₁ l₁ b₂ l₂ b₃
    l₃ e₁ e₂ e₃ rest₁ rest₂ rest₃ d₀ wEnd hT Ns Mg Pm Oc split e₀ hlo hon hQ L Gl

end LT28

#print axioms LT28.field_of_ledger
#print axioms LT28.field_of_ledger_at
