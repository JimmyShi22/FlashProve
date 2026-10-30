-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/Row116Whole.lean: THE KEY FILE's ROW 1.16 (batt.1.batt), WHOLE: THE FIELD r1_16 OF The35 | The21 FROM PREMISES THAT ARE The35's OWN TO THE LETTER, PUBLIC FACTS ON THE PLAN, ONE EQUATION ON A LETTER OF THE FILLING, AND ONE INEQUALITY OF ERRORS. No structure of debts is left.
  (idx0_of_shape HAS MOVED, not a sign turned, to RunOne/KeyStep16.lean; the state's part of seatFacts116_paid's proof stands there as step16_state and is CALLED here)
  seatFacts116_paid   **SeatFacts116, PAID OUTRIGHT**: from ReadsL at the first reading (The35's hG) · PUBLIC: at most noId stages · PUBLIC: PubPile: by seat_says · batt_takes · takeMasksP_gnd · CallGround's laws · KeyBattFacts; border 17's two new clauses by KeyClaimFacts: seat_fit (THE FRONT's OWN TEST, inside the seat's yes, is what ties the pile's masks to message 0: layPile alone does not) · claim_masks0 · pile_ok · claim_ok
  r1_16_whole         **THE FIELD**, FROM: q₁ · hl · hw · hc : CellOnly coll · hG : ReadsL B.h₁ · hb₁ AT 16 (all six: The35's own premises, to the letter) · sealLast · hdata (The21AtSeat hands planOk and hdata) · hst · PubPile (public) · hsame : R.same = sameGl (the filling's letter) · hle (the law's errors at most the maker's rest's, at the stretch that the data have)
  the21_with_16_whole THE FIT, by Lean's own check of types: a The21 with its field r1_16 laid anew by r1_16_whole
IT CLOSES NOTHING: On₁ 16 a IS SHOWN MET BY NOTHING AT F_K's LETTERS: where the promise holds of nothing the row is true and idle.
Nothing on soundness.
-/
import Johnson.Top.Fire.Code.Row116Gives
import Johnson.Desc.Key.KeyClaimFacts

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

open OnBytes.Params (OneTime Setting)
open Johnson.RunOne.KeyRows1
open Johnson.RunOne.KeyRows23 (CellOnly)

section
variable {Cells M Smp Rec : Type} (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces)
    {Xr : Type} (A : (frS.toDecR frZ 402653181).Claims Xr) (E : Coding A) (DK : WholeD) {W : Type}
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


/-- **SeatFacts116, paid outright.** -/
theorem seatFacts116_paid (hG : ReadsL B.h₁) (hst : (oneAt X).ranges.stages.length ≤ noId) (HP : PubPile (oneAt X)) :
    SeatFacts116 X N P DK B at_ R coll where
  dec := by
    intro a rs gs s' ha hs
    have hs' : (batchTableRows (Cl := Claim) (fun x : LookupRecord => x.keys) (oneAt X) pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1))).decide a.1.2 rs gs = .ok s' := hs
    have hstep := step16_state (oneAt X) pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1)) hst HP a.1.2 s' rs gs hs'
    obtain ⟨rows, out, msg, rs', hlay, _, hbt, rfl⟩ := seat_says (Cl := Claim) (fun x : LookupRecord => x.keys) (oneAt X) pieces _ a.1.2 s' rs gs hs'
    obtain ⟨r, htk⟩ := batt_takes _ _ _ _ _ _ _ _ hbt
    obtain ⟨g, hbk⟩ := takeMasksP_gnd htk
    have H : CallGround a.1.2 out.2 := ⟨g.tables, g.codes, g.groups, hbk, g.oracle, VerifiableInference.Desc.Book.takeMasksP_roots _ _ _ _ _ htk⟩
    exact ⟨rides_batt B.h₁ (oneAt X) a.1.2 rows msg out.1 out.2 hG H common (by decide) a.1.1, hstep.1, H.book,
      fun o => sampleIn_call a.1.2 out.2 H o, order_call a.1.2 out.2 H⟩

/-- **THE FIELD r1_16, WHOLE.** -/
theorem r1_16_whole (x₀ x₁ : Lookup) (bw : Block FirstState Claim)
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hl : lookupsOf (oneAt X) = [x₀, x₁])
    (hw : sendW (oneAt X) pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1))
      (groupsTold X.Y.told.1 (rootsBefore X.Y.D.1 (lastSendRound X.Y.D.1)) (rootsAt X.Y.D.1 (lastSendRound X.Y.D.1))) = some bw)
    (hc : CellOnly coll) (hG : ReadsL B.h₁)
    (hb₁ : ∀ p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁)[16]? = some p → ∀ j ∈ pinned (open₁ 2 16), (at_ j).1 < p.base)
    (hs : (Fk X N P).sealLast = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a))
    (hst : (oneAt X).ranges.stages.length ≤ noId) (HP : PubPile (oneAt X)) (hsame : R.same = sameGl)
    (hle : ∀ dZ d0 ds, cutDs (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N P).Cl) (k₁.map held) 16 = dZ :: d0 :: ds →
      Err.le ((K13.Law.mapsOf dZ d0 ds).err (K13.Law.errK (where116 X).rows ds.length)) (rest₁ 16 (dZ :: d0 :: ds)).err) :
    KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 16 := by
  intro p hp
  have hcoll : CollCell coll := fun y y' r e => (hc y y' r e).1
  have hbase : (at_ 0).1 < cutBase 0 (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N P).Cl) (k₁.map held) 16 := by
    have h1 := hb₁ p hp 0 (by rw [pinned_16]; exact List.mem_singleton.2 rfl)
    obtain ⟨b, _, e⟩ := rowAt₁ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd 16 p hp
    rw [e] at h1
    exact h1
  obtain ⟨dZ, d0, ds, hst', hD, hk⟩ := public_of_data X N P DK c₁ k₁ x₀ x₁ bw q₁ hl hw hs hdata
  have W := weight116_of X N P DK c₁ k₁ rest₁ B at_ R coll hsame dZ d0 ds (hle dZ d0 ds hst')
  have HS := seatFacts116_paid X N P DK B at_ R coll hG hst HP
  exact r1_16_of X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R coll x₀ x₁ dZ d0 ds (rw116 X R) q₁
    { hl := hl, long := long_of X N P c₁ k₁ x₀ x₁ hl bw hw q₁, stretch := hst', declared := hD, len := hk, det := W.det
      back := back_of X N P DK c₁ k₁ B at_ R coll dZ d0 ds HS hbase, stays := stays_of X N P DK c₁ k₁ B at_ R coll dZ d0 ds HS hcoll hbase
      pileGives := W.pileGives, givesClaims := W.givesClaims, le := W.le } p hp

/-- **THE FIT, BY LEAN's OWN CHECK OF TYPES**: what r1_16_whole ends in IS the field r1_16 of The21 (and of The35). (It fills nothing else: the other twenty are handed in.) -/
theorem the21_with_16_whole (x₀ x₁ : Lookup) (bw : Block FirstState Claim)
    (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (hl : lookupsOf (oneAt X) = [x₀, x₁])
    (hw : sendW (oneAt X) pieces (rootsBefore X.Y.D.1 (batchRound X.Y.D.1))
      (groupsTold X.Y.told.1 (rootsBefore X.Y.D.1 (lastSendRound X.Y.D.1)) (rootsAt X.Y.D.1 (lastSendRound X.Y.D.1))) = some bw)
    (hc : CellOnly coll) (hG : ReadsL B.h₁)
    (hb₁ : ∀ p, ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁)[16]? = some p → ∀ j ∈ pinned (open₁ 2 16), (at_ j).1 < p.base)
    (hs : (Fk X N P).sealLast = true) (hdata : (Fk X N P).data "key file" = .ok (DK.at frS.P.T.a))
    (hst : (oneAt X).ranges.stages.length ≤ noId) (HP : PubPile (oneAt X)) (hsame : R.same = sameGl)
    (hle : ∀ dZ d0 ds, cutDs (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N P).Cl) (k₁.map held) 16 = dZ :: d0 :: ds →
      Err.le ((K13.Law.mapsOf dZ d0 ds).err (K13.Law.errK (where116 X).rows ds.length)) (rest₁ 16 (dZ :: d0 :: ds)).err)
    (T : The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R enc rad coll off₂ off₃) :
    The21 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R enc rad coll off₂ off₃ :=
  { T with r1_16 := r1_16_whole X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R coll x₀ x₁ bw q₁ hl hw hc hG hb₁ hs hdata hst HP hsame hle }

end

end LPFD

#print axioms LPFD.the21_with_16_whole
#print axioms LPFD.seatFacts116_paid
#print axioms LPFD.r1_16_whole
