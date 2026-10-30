-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/Fire/Code/The21AtD.lean: at the full size: THE FENCE: what is owed at the tables of KeyTablesR.lean, asked over the goals' scope as ONE statement, and the term from it to what the frame's top asks.
Main names. `The21AtZD A E Z`: at every description that the key file's maker (`fkAtD` → `Key.descAt`, KeyFkAtD.lean) hands out at Z, in scope, and a digest of 32 bytes, whose data are made and whose own tests on the plan say yes: THERE ARE letters, AT ONE SET OF WHICH ALL OF THESE HOLD: the 21 laws · `AtFk` · `FirstLetters` · the three heads · three public facts · six facts on the letters · the pieces' errors are the cap · `keyOwed_of_21Z`: **THE ONE TERM**: it gives `KeyCapOn instKD (FkAtZD Z) A E` · `The21InScopeD` | `keyOwed_of_21D`: the same over all Z: `KeyOwedAtD A E` (KeyAtFkD.lean).
OBJECT: `Key.descriptionFromSource X N P` through the maker's five equations · USER: KeyPublicAtSeat.lean (`letters_of_handed`), Johnson/Goal/Conditions/KeyAtTheSeat.lean · LETTERS: A · E.
Limits. A joining: nothing is paid here. The five equations that the payer holds are those of the maker `Key.descAt`. This file shows `The21AtZD` at no Z. `The21Letters` is had at the seat's one description, in scope, where protocolDataWellFormed says yes (Johnson/Goal/Conditions/KeySoundOfOpenAt.lean, KeyOpenHolds.lean). These tables take the plain Member | PIN | NoColl | hasSmp (Johnson/Desc/Msg.lean) by name, at a letter G. A filling is typed (famG, Johnson/Desc/Key/KeyFillFam.lean: enc a relation, at the seat; over a family of seats) for which, at a shown word, the table's list is held against the library's list at every seat (fam_seals: the upper half; fam_member_of_cand: the lower half's heart). In the abstract alone it is shown that PIN and the promise beside it (hasSmp · NoColl) can be met together at all seats of a family (KeyFillOracles.lean: fam_promise_form_at_oracles; a closed toy beside): under SeatFits (Johnson/Desc/Sound/MsgSig.lean), the library's own test on codes and radii (which the kernel holds at the six real shapes and radii) and a frame that holds the seats' trees at their depths, for all messages that can be sent, at one statement of the rule's own oracles, one record, one witness: at a sample's tie made of the message itself, which reads no record; at a silly laying of the witness's tables; NoColl at a code word alone; of PINW nothing. So the form of PIN · hasSmp · NoColl is not contradictory, and no more. Not shown there: that SeatFits, these shapes and such a frame are F_K's (evaluated in part) · the sample's tie off F_K's real record (a letter of other files) · the laying that is meant · that such a statement lies in a border's whole promise (ties · shapes · rows that hold; a tree not sent is empty there) · that F_K's honest run lays such oracles and record (no theorem). Where no member is shown at F_K's own letters, a law or field at these tables with PIN as an item or NoColl in its promise may be true and empty at the real protocol, and by itself closes nothing. Members at the 21 laws (one example a law, evaluated, not proved): KeyOpenHolds.lean's head. Nothing on soundness.

-/
import Johnson.Top.Fire.Code.The35
import Johnson.Top.Fire.Code.KeyAtFkD

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

open scoped ENNReal

namespace LPFD
open VerifiableInference VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ OnBytes
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key (Xi)
open VerifiableInference.Desc.Key (FirstState)
open Johnson.RunOne.KeyRows23 (BaseSt AtFk Fk fr₁ fr₂ fr₃ On₁ Cl₁ On₂ Cl₂ On₃ Cl₃ oneAt St₂ St₃ seam₁_at_fk seam₂_at_fk ends_at_fk)
open Johnson.RunOne.KeyRows1 (FirstLetters firstOn_of firstClaim_of CollCell ReadsL open₁)
open Johnson.RunOne.KeyRows23 (CellOnly inFront₂ front₂ seat open₃)

/-- **THE LETTERS AND WHAT IS OWED AT THEM, AT ONE DESCRIPTION `Key.descriptionFromSource X N P` AND ONE SET OF DATA**: THERE ARE letters, AT ONE SET OF WHICH ALL OF THESE HOLD: the 21 laws · `AtFk` · `FirstLetters` · the three heads · three public facts · six facts on the letters · the pieces' errors are the cap. -/
def The21Letters {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (DK : WholeD) : Prop :=
  ∃ (Cells M Smp Rec W : Type) (_ : Inhabited Cells) (_ : Inhabited M)
    (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl)) (c₂ : Block (Fk X N P).S₂ (Fk X N P).Cl)
    (k₂ : List (Block (Fk X N P).S₂ (Fk X N P).Cl)) (c₃ : Block (Fk X N P).S₃ (Fk X N P).Cl) (k₃ : List (Block (Fk X N P).S₃ (Fk X N P).Cl))
    (rest₁ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₁ 0) ((Fk X N P).XiPub × (Fk X N P).S₁) W ds)
    (rest₂ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₂ 0) (((Fk X N P).XiPub × (Fk X N P).S₁) × (Fk X N P).S₂) W ds)
    (rest₃ : (i : ℕ) → (ds : List RDT) → Rest (ckP .two)
      (frameAt (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a)) (DK.at frS.P.T.a).key₃ (Fk X N P).lastChainFirstTreeNumber)
      (((Fk X N P).XiPub × (Fk X N P).S₁ × (Fk X N P).S₂) × (Fk X N P).S₃) W ds)
    (dW wEnd : W)
    (B : BaseSt Cells M Smp Rec) (at_ : Where) (R : KRead Cells M) (enc : (ℕ → OnBytes.E) → ℕ → OnBytes.E) (rad : ℕ)
    (coll : Strs → Rec → Prop) (off₂ off₃ : ℕ → ℕ)
    (ρ : RecFull → Rec) (cellsOf : (lettersAt A (relationsAndEncodingOfClaims A E)).conf.Msg → Cells)
    (_ : ((Fk X N P).XiPub × (Fk X N P).S₁) × (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str)
    (x₀ x₁ : Lookup) (bw : Block FirstState Claim),
    The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R enc rad coll off₂ off₃ ∧
    AtFk X B at_ R off₃ ∧
    FirstLetters (fr₁ (DK.at frS.P.T.a)) B.h₁ at_ (oneAt X) R coll VerifiableInference.Desc.Key.keyInstanceOfOutOfDomainSample (Fk X N P).start₁
      (fun y : (oneExternalString (2 ^ (DK.at frS.P.T.a).a) SgX).Str => ((y, fun _ => []) : (EAll (DK.at frS.P.T.a) (allOf (DK.at frS.P.T.a))).Str)) ρ
      (fun y r => (lettersAt A (relationsAndEncodingOfClaims A E)).conf.coll y r.1) (fun y r => (lettersAt A (relationsAndEncodingOfClaims A E)).conf.dcd y r) (lettersAt A (relationsAndEncodingOfClaims A E)).conf.held cellsOf ∧
    (Fk X N P).first.blocksInOrder = c₁ :: k₁ ∧
    (Fk X N P).shared.blocksInOrder = c₂ :: k₂ ∧
    (Fk X N P).second.blocksInOrder = c₃ :: k₃ ∧
    lookupsOf (oneAt X) = [x₀, x₁] ∧
    sendW (oneAt X) pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1))
      (groupsTold X.Y.told.1 (rootsBefore X.Y.D.1 (lastSendRound X.Y.D.1)) (rootsAt X.Y.D.1 (lastSendRound X.Y.D.1))) = some bw ∧
    (inFront₂ X P).length = 10 ∧
    CellOnly coll ∧
    ReadsL B.h₁ ∧
    (∀ n p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁)[n]? = some p → ∀ j ∈ pinned (open₁ 2 n), (at_ j).1 < p.base) ∧
    (∀ p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂)[0]? = some p → ∀ j ∈ pinned seam, (at_ j).1 < p.base) ∧
    (∀ p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₂ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₂)[11]? = some p → ∀ j ∈ pinned end₂, (at_ j).1 < p.base) ∧
    (∀ p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₃ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₃)[1]? = some p → ∀ j ∈ pinned (open₃ 1), (at_ j).1 < p.base) ∧
    AtCap rest₁ ∧
    AtCap rest₂ ∧
    AtCap rest₃

set_option maxHeartbeats 4000000 in
/-- **From them, where the description's data are DK's: the debt at the cap.** -/
theorem keyDebtCap_of_letters {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (DK : WholeD)
    (hD : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a)) (h : The21Letters A E X N P DK) : KeyDebtCap (Fk X N P) instKD A E DK "key file" := by
  obtain ⟨Cells, M, Smp, Rec, W, iC, iM, c₁, k₁, c₂, k₂, c₃, k₃, rest₁, rest₂, rest₃, dW, wEnd, B, at_, R, enc, rad, coll, off₂, off₃, ρ, cellsOf, dS, x₀, x₁, bw,
    H, atFk, first, q₁, q₂, q₃, hl, hw, hin, hc, hG, hb₁, hb₂₀, hb₂₁₁, hb₃₁, a₁, a₂, a₃⟩ := h
  exact keyDebtCap_of_21 X N P A E DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R enc rad coll off₂ off₃ "key file" ρ cellsOf H atFk first q₁ q₂ q₃ x₀ x₁ hl bw hw hin hc hG hb₁ hb₂₀ hb₂₁₁ hb₃₁ hD a₁ a₂ a₃ dS

/-- **WHAT IS OWED AT THE TABLES OF KeyTablesR.lean, AT ONE SET OF PUBLIC FILES Z, AS ONE STATEMENT**: at every description that the maker hands out at Z, where Z is in scope, and a digest of 32 bytes (THE PAYER HOLDS HOW IT WAS MADE: the public values X₀ of Z's three files; the planner's record and the sendings m at X₀, the layout and the digest; the source X, the numbers N and the places P read off m), whose data are made and whose own tests on the plan say yes: `The21Letters`. -/
def The21AtZD {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (Z : OnBytes.K.Pub) : Prop :=
  ∀ (cfg : ByteArray) (X₀ : OnBytes.Model.Verify.Public) (m : Johnson.G.OfPlan.Made)
    (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (DK : WholeD),
    VerifierAndGoals.InScope ⟨Z.pol, Z.lay, Z.KL⟩ = true → cfg.size = 32 → fkAtD Z cfg = .ok (Fk X N P) →
    OnBytes.Model.Verify.publicOf Z.pol Z.KL (some Z.lay) = .ok X₀ → madeAt X₀ Z.lay cfg = .ok m → sourceOf m = .ok X → rangesNumbers m = .ok N → laterPlaces m = .ok P →
    (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a) → (Fk X N P).planOk = true →
    The21Letters A E X N P DK

/-- **THE ONE TERM, AT ONE Z: it gives the debt over the descriptions that the maker hands out at Z.** -/
theorem keyOwed_of_21Z {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (Z : OnBytes.K.Pub)
    (hs : VerifierAndGoals.InScope ⟨Z.pol, Z.lay, Z.KL⟩ = true) (h : The21AtZD A E Z) : KeyCapOn instKD (FkAtZD Z) A E := by
  intro F DK hS hD hp
  obtain ⟨cfg, hcfg, hF⟩ := hS
  obtain ⟨X₀, m, X, N, P, hX₀, hm, hX, hN, hP, rfl⟩ := fkAtD_made Z cfg F hF
  exact keyDebtCap_of_letters A E X N P DK hD (h cfg X₀ m X N P DK hs hcfg hF hX₀ hm hX hN hP hD hp)

/-- The same over the scope: at every Z. (ONE pair of claims and coding is asked over ALL Z.) -/
def The21InScopeD {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) : Prop := ∀ Z, The21AtZD A E Z

theorem keyOwed_of_21D {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (h : The21InScopeD A E) : KeyOwedAtD A E := by
  intro F DK hS hD hp
  obtain ⟨Z, cfg, hs, hcfg, hF⟩ := hS
  exact keyOwed_of_21Z A E Z hs (h Z) F DK ⟨cfg, hcfg, hF⟩ hD hp

end LPFD

#print axioms LPFD.The21Letters
#print axioms LPFD.keyDebtCap_of_letters
#print axioms LPFD.The21AtZD
#print axioms LPFD.keyOwed_of_21Z
#print axioms LPFD.The21InScopeD
#print axioms LPFD.keyOwed_of_21D
