-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/FieldOfFills.lean: **THE TOP CALL OF THE ROW shared_joint_count, FROM THE LEDGER's END AS ledger_whole_fills_field (Johnson/Desc/K14/Law/LedgerByMakeTop.lean) HAS IT (at the maker's own pieces of the UNPULLED IOP as written in Lean, the key at the data's t₁) TO THE TWO FIELDS.**
Statements; four proofs are rfl, the fifth is one call of field_of_ledger (FieldOfLedger.lean). Two things part this from ledger_whole_fills_field, to be held at the text: T at (G.pull f) and
G := ProofFile.seatedAt … here; F₀ unpulled, at a seat spelled field by field there.
BOTH ARE HELD HERE, BY rfl:
  pull_p₂ | pull_l₂        behind a laying of instances the shared row's head and tail, as the maker cuts them, ARE the unpulled description's: general in the description.
  seated_is_fileDescBy     ProofFile.seatedAt o Z Np cF IS ProofFile.fileDescBy o ProofFile.pureRoad.links Z { lot, σ := St, start, chain, ended, okInst, fileOk, standIns } … with each field ProofFile.sharedAt Z Np's own.
  seated_chain             that seat's chain IS chainOf Z.p.chains (p14Of Z.p.chains (beforePointOf Np)) (K12.Seat.tests Np) K12.Seat.last.
  **field_of_fills**       field_of_ledger with L stated at atDesc G (piecesAt (ckP .two) G …), the key at (DP.at a).t₁: ledger_whole_fills_field's end at F₀ := G, Dw := DP.at a.
Limits. L, Glues, the places' two equations and the facts on what is laid are premises. It closes no row. NO SOUNDNESS.

-/
import Johnson.Desc.Sound.FieldOfLedgerSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LT28
open OnBytes VerifiableInference.Desc
open VerifiableInference.OnPublicFiles VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Shared
open OnBytes.Flat OnBytes.Maker _root_.Run _root_.Run.PQ _root_.Iop

/-- Behind a laying of instances the shared row's head is the unpulled description's. -/
theorem pull_p₂ {Xi' W : Type} (G : FileDescription ProofFile.Inst) (f : Xi' → ProofFile.Inst) (D : WholeD)
    (b₁ : Block G.S₁ G.Cl) (l₁ : List (Block G.S₁ G.Cl)) (b₂ : Block G.S₂ G.Cl)
    (l₂ : List (Block G.S₂ G.Cl)) (b₃ : Block G.S₃ G.Cl) (l₃ : List (Block G.S₃ G.Cl)) (rest₁)
    (rest₂) (rest₃) (d₀ wEnd : W) :
    (atDesc (G.pull f) (piecesAt (ckP .two) (G.pull f) D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d₀
      wEnd)).p₂ =
      (atDesc G (piecesAt (ckP .two) G D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d₀ wEnd)).p₂ := rfl

/-- And its tail. -/
theorem pull_l₂ {Xi' W : Type} (G : FileDescription ProofFile.Inst) (f : Xi' → ProofFile.Inst) (D : WholeD)
    (b₁ : Block G.S₁ G.Cl) (l₁ : List (Block G.S₁ G.Cl)) (b₂ : Block G.S₂ G.Cl)
    (l₂ : List (Block G.S₂ G.Cl)) (b₃ : Block G.S₃ G.Cl) (l₃ : List (Block G.S₃ G.Cl)) (rest₁)
    (rest₂) (rest₃) (d₀ wEnd : W) :
    (atDesc (G.pull f) (piecesAt (ckP .two) (G.pull f) D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d₀
      wEnd)).l₂ =
      (atDesc G (piecesAt (ckP .two) G D b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d₀ wEnd)).l₂ := rfl

/-- The seated value is fileDescBy at a seat spelled field by field. -/
theorem seated_is_fileDescBy (o : ProofFile.SecondHashFunctionArgument) (Z : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain First.S ProofFile.Cl) :
    ProofFile.seatedAt o Z Np cF = ProofFile.fileDescBy o ProofFile.pureRoad.links Z
      { lot := (ProofFile.sharedAt Z Np).lot, σ := Desc.K14.St, start := (ProofFile.sharedAt Z Np).start,
        chain := (ProofFile.sharedAt Z Np).chain, ended := (ProofFile.sharedAt Z Np).ended,
        okInst := (ProofFile.sharedAt Z Np).okInst, fileOk := (ProofFile.sharedAt Z Np).fileOk,
        standIns := (ProofFile.sharedAt Z Np).standIns }
      (P2Third.secondSeatOf Z Np) (fun s => s) (ProofFile.startS Z) cF := rfl

/-- That seat's chain. -/
theorem seated_chain (Z : ProofFile.Pub) (Np : H2U.Places4) :
    (ProofFile.sharedAt Z Np).chain =
      Desc.K14.chainOf Z.p.chains (Desc.K14.p14Of Z.p.chains (Desc.K14.beforePointOf Np))
        (VerifiableInference.Desc.K12.Seat.tests Np) VerifiableInference.Desc.K12.Seat.last := rfl

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

/-- **FROM THE LEDGER's END AT THE UNPULLED PIECES TO THE TWO FIELDS.** -/
theorem field_of_fills (hk : ∀ x rec, (f (x, rec)).pub.key = k rec) (hG : StartTwoByKey G)
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
    (L : EachLawsBN (keyAt Prod.snd (DP.at a).t₁ (atDesc G (piecesAt (ckP .two) G (DP.at a) b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d₀ wEnd)).p₂
        (atDesc G (piecesAt (ckP .two) G (DP.at a) b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d₀ wEnd)).l₂)
      (onQ₂ Ns Pm Oc split (atDesc G (piecesAt (ckP .two) G (DP.at a) b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d₀ wEnd)).p₂
        (atDesc G (piecesAt (ckP .two) G (DP.at a) b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d₀ wEnd)).l₂)
      (stepAt Ns Mg Pm Oc split (atDesc G (piecesAt (ckP .two) G (DP.at a) b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d₀ wEnd)).p₂
        (atDesc G (piecesAt (ckP .two) G (DP.at a) b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d₀ wEnd)).l₂
        (extOf Ns (atDesc G (piecesAt (ckP .two) G (DP.at a) b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d₀ wEnd)).p₂
          (atDesc G (piecesAt (ckP .two) G (DP.at a) b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d₀ wEnd)).l₂ e₀)) N 0
      ((atDesc G (piecesAt (ckP .two) G (DP.at a) b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d₀ wEnd)).p₂ ::
        (atDesc G (piecesAt (ckP .two) G (DP.at a) b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ d₀ wEnd)).l₂))
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
  subst hT
  refine field_of_ledger Kc DP tFp tJp t3p N f k G _ Pl h₁ h₂ h₃ M L₁ L₂ d hk hG file hD hp b₁ l₁ b₂ l₂ b₃
    l₃ e₁ e₂ e₃ rest₁ rest₂ rest₃ d₀ wEnd rfl Ns Mg Pm Oc split e₀ hlo hon hQ ?_ Gl
  rw [hlo]
  exact L

end LT28

#print axioms LT28.pull_p₂
#print axioms LT28.pull_l₂
#print axioms LT28.seated_is_fileDescBy
#print axioms LT28.seated_chain
#print axioms LT28.field_of_fills
