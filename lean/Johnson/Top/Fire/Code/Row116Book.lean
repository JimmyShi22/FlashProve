-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/Row116Book.lean: THE KEY FILE's ROW 1.16: THE TWO BOOK-KEEPING FIELDS OF Owed116 (back · stays) PAID FROM FACTS ON THE SEAT's OWN DECISION.
  SeatFacts116   OWED: ONE STATEMENT ON THE SEAT's DECISION (no transcript, no witness), UNDER THE PROMISE IN FRONT (without it the form is the trap that is mended in the premise hback of Johnson/Desc/K13/Law/GoodAny.lean): where On₁ 16 holds of a and batt.1.batt says yes from a's state to s': Rides (Johnson/Desc/Key/KeyQuiet.lean) at the four items of `common` (Row116.lean) · the book-keeping's step 16 → 17 · the book is the same · SampleIn and InOrder ride
  back_of        PAID from SeatFacts116 and «message 0's tree lies below the piece's base»: by piece_decides_at (Johnson/Desc/Plain/PieceYes.lean) · held_decide (Johnson/Desc/Plain/PaidKeeps.lean) · strsStay_of_out (Johnson/Desc/Key/KeyKeeps.lean, over Johnson/Desc/Sound/StringsStay.lean) · emptyRow_back
  stays_of       PAID from the same and CollCell: by onAt_fwd (KeyQuiet.lean) · free₁_step
  Weight116      OWED, THE WEIGHT: det · pileGives · givesClaims, and the numbers: le: at a stretch dZ d0 ds
  (The field r1_16 itself: r1_16_whole, Johnson/Top/Fire/Code/Row116Whole.lean.)
Nothing on soundness.
-/
import Johnson.Top.Fire.Code.Row116Pub
import Johnson.RunOne.KeyTenKeeps
import Johnson.RunOne.KeyStep16

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

theorem pinned_common : pinned common = [0] := by decide
theorem pinned_17 : pinned (open₁ 2 17) = [0] := by decide +kernel
theorem plain_common : ∀ i ∈ common, plain i = true := by decide

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


/-- **OWED: what the seat's own yes does to the state.** -/
structure SeatFacts116 : Prop where
  dec : ∀ (a : (Xi × FirstState) × (fr₁ (DK.at frS.P.T.a)).E.Str) rs gs s', On₁ X N P (DK.at frS.P.T.a) B at_ R coll 16 a → (seat116 X).decide a.1.2 rs gs = .ok s' →
    Rides B.h₁ (readers₁ (oneAt X)) common a.1.1 a.1.2 s' ∧
    (shape₁ (plan₁ (oneAt X)) (readers₁ (oneAt X)) (book₁ (oneAt X)) 2 (slots₁ (oneAt X)) 16 a.1.2 = true →
      shape₁ (plan₁ (oneAt X)) (readers₁ (oneAt X)) (book₁ (oneAt X)) 2 (slots₁ (oneAt X)) 17 s' = true) ∧
    s'.d.book = a.1.2.d.book ∧ (∀ o, Johnson.RunOne.KeyRows23.SampleIn a.1.2.d.st o → Johnson.RunOne.KeyRows23.SampleIn s'.d.st o) ∧ (Means.InOrder a.1.2.d.st → Means.InOrder s'.d.st)

section
variable (dZ d0 : RDT) (ds : List RDT)

/-- What a yes of the law's piece gives: the instance stays, and the seat has said yes. -/
theorem seat_yes (a b' : (Xi × FirstState) × (fr₁ (DK.at frS.P.T.a)).E.Str) (τ) (h : (piece116 (Cells := Cells) (M := M) X N P DK c₁ k₁ dZ d0 ds).ior.red.out a τ = some b') :
    b'.1.1 = a.1.1 ∧ ∃ rs gs, (seat116 X).decide a.1.2 rs gs = .ok b'.1.2 := by
  have hd := piece_decides_at (piece116 (Cells := Cells) (M := M) X N P DK c₁ k₁ dZ d0 ds) a τ b' h
  obtain ⟨e, hs⟩ := held_decide (seat116 X) a.1 _ _ b'.1 hd
  exact ⟨e, _, _, hs⟩

theorem back_of (H : SeatFacts116 X N P DK B at_ R coll)
    (hbase : (at_ 0).1 < cutBase 0 (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N P).Cl) (k₁.map held) 16) :
    ∀ a τ b' w, On₁ X N P (DK.at frS.P.T.a) B at_ R coll 16 a → (piece116 (Cells := Cells) (M := M) X N P DK c₁ k₁ dZ d0 ds).ior.red.out a τ = some b' →
      pin116 X N P DK B at_ R b' w → pin116 X N P DK B at_ R a w := by
  intro a τ b' w ha hb' hw
  obtain ⟨e, rs, gs, hs⟩ := seat_yes X N P DK c₁ k₁ dZ d0 ds a b' τ hb'
  have Fc := (H.dec a rs gs b'.1.2 ha hs).1
  have Hy := strsStay_of_out (Fk X N P) (fr₁ (DK.at frS.P.T.a)) at_ (piece116 (Cells := Cells) (M := M) X N P DK c₁ k₁ dZ d0 ds) common
    (fun k hk => by rw [pinned_common] at hk; obtain rfl := List.mem_singleton.1 hk; exact hbase) a b' τ hb'
  obtain ⟨⟨p, s⟩, y⟩ := a
  obtain ⟨⟨p', s'⟩, y'⟩ := b'
  have e' : p' = p := e
  subst e'
  exact emptyRow_back (Fk X N P) B.h₁ at_ (plan₁ (oneAt X)) R (readers₁ (oneAt X)) (fun _ _ _ => False) (formsAt (plan₁ (oneAt X)) R k3At₁ (oneAt X).ranges)
    (worthAt (plan₁ (oneAt X)) R k3At₁ (oneAt X).ranges (oneAt X).codes) (fun _ _ _ _ _ => False) common plain_common p' s s' _ _ w Fc Hy hw

theorem stays_of (H : SeatFacts116 X N P DK B at_ R coll) (hcoll : CollCell coll)
    (hbase : (at_ 0).1 < cutBase 0 (DK.at frS.P.T.a).ds₁ (held c₁ : Block ((Fk X N P).XiPub × (Fk X N P).S₁) (Fk X N P).Cl) (k₁.map held) 16) :
    ∀ a τ b', On₁ X N P (DK.at frS.P.T.a) B at_ R coll 16 a → (piece116 (Cells := Cells) (M := M) X N P DK c₁ k₁ dZ d0 ds).ior.red.out a τ = some b' →
      On₁ X N P (DK.at frS.P.T.a) B at_ R coll 17 b' := by
  intro a τ b' ha hb'
  have hn : n₁ (oneAt X) = 2 := on₁_two (Fk X N P) (fr₁ (DK.at frS.P.T.a)) B.h₁ at_ (oneAt X) R coll 16 a ha
  obtain ⟨e, rs, gs, hs⟩ := seat_yes X N P DK c₁ k₁ dZ d0 ds a b' τ hb'
  obtain ⟨h1, h2, h3, h5, h6⟩ := H.dec a rs gs b'.1.2 ha hs
  have Hy := strsStay_of_out (Fk X N P) (fr₁ (DK.at frS.P.T.a)) at_ (piece116 (Cells := Cells) (M := M) X N P DK c₁ k₁ dZ d0 ds) (open₁ 2 16)
    (fun k hk => by rw [pinned_16] at hk; obtain rfl := List.mem_singleton.1 hk; exact hbase) a b' τ hb'
  obtain ⟨⟨p, s⟩, y⟩ := a
  obtain ⟨⟨p', s'⟩, y'⟩ := b'
  have e' : p' = p := e
  subst e'
  have ha' : onAt (Fk X N P) B.h₁ at_ (meaning₁At (oneAt X) R) (shape₁ (plan₁ (oneAt X)) (readers₁ (oneAt X)) (book₁ (oneAt X)) (n₁ (oneAt X)) (slots₁ (oneAt X)) 16)
      (free₁ (Fk X N P) B.h₁ at_ (oneAt X) R coll 16) (open₁ (n₁ (oneAt X)) 16) (p', s) (strsOf (fr₁ (DK.at frS.P.T.a)) y) := ha
  show onAt (Fk X N P) B.h₁ at_ (meaning₁At (oneAt X) R) (shape₁ (plan₁ (oneAt X)) (readers₁ (oneAt X)) (book₁ (oneAt X)) (n₁ (oneAt X)) (slots₁ (oneAt X)) 17)
      (free₁ (Fk X N P) B.h₁ at_ (oneAt X) R coll 17) (open₁ (n₁ (oneAt X)) 17) (p', s') (strsOf (fr₁ (DK.at frS.P.T.a)) y')
  rw [hn] at ha' ⊢
  exact onAt_fwd (Fk X N P) B.h₁ at_ (plan₁ (oneAt X)) R (readers₁ (oneAt X)) (fun _ _ _ => False) (formsAt (plan₁ (oneAt X)) R k3At₁ (oneAt X).ranges)
    (worthAt (plan₁ (oneAt X)) R k3At₁ (oneAt X).ranges (oneAt X).codes) (fun _ _ _ _ _ => False) _ _ _ _ (open₁ 2 16) (open₁ 2 17) (pinned_17.trans pinned_16.symm) p' s s' _ _
    h1.marked h1.pins Hy
    (free₁_step (Fk X N P) B.h₁ at_ (oneAt X) R coll 16 17 p' s s' _ _ h1.pins hcoll Hy h3 (pinned_17.trans pinned_16.symm) (by omega) (fun h18 => absurd h18 (by decide)) h5 h6)
    h2 ha'

end

/-- **OWED: THE WEIGHT, and the numbers**, at a stretch. -/
structure Weight116 {nR : ℕ} (dZ d0 : RDT) (ds : List RDT) (rw : Wit Cells Unit M → K13.Law.Wit GE nR (where116 X).lin.kCol) : Prop where
  det : ∀ a p w w', On₁ X N P (DK.at frS.P.T.a) B at_ R coll 16 a → part116 X a.1 = some p → pin116 X N P DK B at_ R a w → pin116 X N P DK B at_ R a w' →
    K13.Law.AgreeAt p.indexMasks (rw w) (rw w')
  pileGives : ∀ a τ b' w, On₁ X N P (DK.at frS.P.T.a) B at_ R coll 16 a → (piece116 (Cells := Cells) (M := M) X N P DK c₁ k₁ dZ d0 ds).ior.red.out a τ = some b' →
    (meaning₁At (oneAt X) R).pile b'.1 (strsOf (fr₁ (DK.at frS.P.T.a)) b'.2) w → ∀ r ∈ row116 b'.1, K13.Law.Holds K13.Law.ρg (rw w) r
  givesClaims : ∀ a τ b' w, On₁ X N P (DK.at frS.P.T.a) B at_ R coll 16 a → (piece116 (Cells := Cells) (M := M) X N P DK c₁ k₁ dZ d0 ds).ior.red.out a τ = some b' →
    (∀ p, part116 X a.1 = some p → ∀ r ∈ p.pile, K13.Law.Holds K13.Law.ρg (rw w) r) →
    ∀ l, l < 2 → (meaning₁At (oneAt X) R).kclaims l a.1 (strsOf (fr₁ (DK.at frS.P.T.a)) a.2) w
  le : Err.le ((K13.Law.mapsOf dZ d0 ds).err (K13.Law.errK (where116 X).rows ds.length)) (rest₁ 16 (dZ :: d0 :: ds)).err

end

end LPFD

#print axioms LPFD.back_of
#print axioms LPFD.stays_of
