-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/Row10Five.lean: THE TRACER ON ROW 1.0, LEVEL 5: Left10b's (e | err | le) PAID BY below_send (Johnson/RunOne/KeySendBelow.lean) FROM TWO BOOLEANS WITH CODE AND «the maker's rest at the first piece is the cap»: what is left is Left10c.
OBJECT: The35.r1_0 · USER: The21's filler · LETTERS: X N P · the maker's cut and rests · B at_ R coll; K: the share's exponent.
  le_of_below   PROVED: shareB K · belowB K · the rest's errors are Err.cap 128 ⟹ Left10b's «le» at e := errPort (par10 X) rad (below_send; the library's Err.le_cap_of_below_inv)
  Left10c       WHAT IS LEFT: as Left10b, with K · share · below · cap in the place of e · err · le
  r1_0_five     PROVED FROM q₁ AND Left10c
Nothing on soundness.
-/
import Johnson.Top.Fire.Code.Row10Paid
import Johnson.RunOne.KeySendBelow

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

open VerifiableInference.Desc.K1 (Par condPort IsSend sendPiece Sealed shapeAt shapesOf sampledAt errPort seedMaps seedEntry seeds_one)
open Johnson.Pack (portOmZ)
open Johnson.RunOne.KeySendErr (shareB belowB below_send)

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


/-- **WHAT IS LEFT OF ROW 1.0, THE ERRORS' SIZE PAID.** -/
structure Left10c where
  d₁ : RDT
  d₂ : RDT
  data : (DK.at frS.P.T.a).ds₁.take c₁.rounds.length = [d₁, d₂]
  entry : d₁.entry = seedEntry (par10 X)
  kind : d₁.kind = .seeds
  rad : ℕ → ℕ
  cond : condPort (par10 X) rad = true
  /-- PUBLIC, A BOOLEAN WITH CODE (Johnson/RunOne/KeySendErr.lean): the bad seeds are a share of at most 2^-K of the seeds -/
  K : ℕ
  share : shareB K (par10 X) rad = true
  /-- PUBLIC, A BOOLEAN WITH CODE (Johnson/RunOne/KeySendBelow.lean): with the sampler's bias over the round's hash blocks the written share is at most 2^-128 -/
  below : belowB K (par10 X) = true
  /-- THE FRAME's: the maker's rest at the first piece has the cap's errors -/
  cap : (rest₁ 0 [d₁, d₂]).err = Err.cap 128 (uLT (ckP .two) [d₁, d₂])
  fOf : (fr₁ (DK.at frS.P.T.a)).E.Str → ∀ k, (portOmZ (par10 X).codes (shapeAt (par10 X) k) (rad k.val)).Str
  fIn : (fr₁ (DK.at frS.P.T.a)).E.Str → (wT d₁).Msg → ∀ k, (portOmZ (par10 X).codes (shapeAt (par10 X) k) (rad k.val)).Str
  words : ∀ y τ, fOf ((sendPiece (W := W) (F := fr₁ (DK.at frS.P.T.a)) (held c₁ : Block (Xi × FirstState) Claim) 0 d₁ d₂ (par10 X).coordinates (errPort (par10 X) rad)).ior.imp y τ) = fIn y τ.1
  hnew : ∀ a τ a', On₁ X N P (DK.at frS.P.T.a) B at_ R coll 0 a →
      (sendPiece (W := W) (F := fr₁ (DK.at frS.P.T.a)) (held c₁ : Block (Xi × FirstState) Claim) 0 d₁ d₂ (par10 X).coordinates (errPort (par10 X) rad)).ior.red.out a τ = some a' →
      ShownAt (Fk X N P) at_ 0 (strsOf (fr₁ (DK.at frS.P.T.a)) a'.2)
  sampled : (oneAt X).indexMasks.shape.answers ≠ 0
  lay : ∀ lay, OnBytes.layTrees (oneAt X).codes #[(oneAt X).indexMasks] = some lay → lay.shapes.size = 1 ∧ lay.tree.getD 0 0 = 0 ∧ lay.part.getD 0 0 = 0
  seat : at_ 0 = (0, 0)
  cell : CollCell coll
  k₀ : Fin (shapesOf (par10 X)).length
  sampledAt : sampledAt (par10 X) k₀
  tieS : ∀ a' : (Xi × FirstState) × (fr₁ (DK.at frS.P.T.a)).E.Str, a'.1.2.d.st.oracles.size = 1 →
      Sealed (par10 X).codes (shapeAt (par10 X) k₀) (rad k₀.val) (fOf a'.2 k₀) a'.1.2.d.st (a'.1.2.d.st.oracles.size - (shapesOf (par10 X)).length + k₀.val) →
      hasSmp B.h₁ (at_ 0).1 (at_ 0).2 a'.1 = true ∧ NoColl (Fk X N P) B.h₁ (at_ 0).1 (at_ 0).2 a'.1 (strsOf (fr₁ (DK.at frS.P.T.a)) a'.2)

/-- **The kind's own written errors lie below the maker's rest's.** -/
theorem le_of_below (H : Left10c X N P DK c₁ rest₁ B at_ R coll) :
    Err.le ((seedMaps H.d₁ H.d₂ (par10 X).coordinates).err ((errPort (par10 X) H.rad, ()) : ℕ × Unit)) (rest₁ 0 [H.d₁, H.d₂]).err :=
  H.cap ▸ Err.le_cap_of_below_inv 128 _
    (below_send H.K (par10 X) H.rad (seeds_one (par10 X) H.rad H.cond) H.d₁ H.d₂ ⟨H.entry, by rw [H.kind]; decide⟩ H.share H.below)

def left10b_of (H : Left10c X N P DK c₁ rest₁ B at_ R coll) : Left10b X N P DK c₁ rest₁ B at_ R coll :=
  { d₁ := H.d₁, d₂ := H.d₂, data := H.data, entry := H.entry, kind := H.kind, rad := H.rad, cond := H.cond
    e := errPort (par10 X) H.rad, err := Nat.le_refl _, le := le_of_below X N P DK c₁ rest₁ B at_ R coll H
    fOf := H.fOf, fIn := H.fIn, words := H.words, hnew := H.hnew, sampled := H.sampled, lay := H.lay, seat := H.seat, cell := H.cell
    k₀ := H.k₀, sampledAt := H.sampledAt, tieS := H.tieS }

/-- **THE FIELD r1_0 OF The35, THE ERRORS' SIZE PAID TOO.** -/
theorem r1_0_five (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (H : Left10c X N P DK c₁ rest₁ B at_ R coll) :
    KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 0 :=
  r1_0_paid X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R coll q₁ (left10b_of X N P DK c₁ rest₁ B at_ R coll H)

end

end LPFD

#print axioms LPFD.le_of_below
#print axioms LPFD.r1_0_five
