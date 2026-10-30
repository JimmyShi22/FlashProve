-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/Row10Paid.lean: THE TRACER ON ROW 1.0, LEVEL 4: THE FIELD r1_0 OF The35 (The35.lean) WITH Left10's (yes) AND (recStays) PAID: what is left is Left10b.
OBJECT: The35.r1_0 · USER: The21's filler · LETTERS: X N P · the maker's cut and rests · B at_ R coll.
  recStays_base   PROVED (by rfl): every BaseSt's first reading takes the stored table's out-of-domain (OOD) sample off the instance alone
  decide10 | rounds10   PROVED: under q₁ the maker's c₁ decides as the description's own first block and declares the sending kind's own two rounds
  Left10b         WHAT IS LEFT: data | entry | kind · rad | cond · e | err | le · fOf | fIn | words · hnew (at New := every leaf of the seat at_ 0 is shown) · FOUR PUBLIC FACTS: sampled · lay · seat (at_ 0 = (0, 0)) · cell (the collision reads the stored table's cells alone) · k₀ | sampledAt | tieS
  one1_of         PROVED: behind the piece the statement has just one message: Left10's one1 paid
  left10_of       PROVED: Left10b gives Left10 (planOkOwn out of cond, by cond_parts, Port6.lean)
  r1_0_paid       PROVED FROM q₁ AND Left10b
Nothing on soundness.
-/
import Johnson.Top.Fire.Code.Row10At
import Johnson.RunOne.KeySendYes

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

open Johnson.RunOne.KeyRows1 (RecStays SendYes₀ sendYes₀ Public10)
open VerifiableInference.Desc.K1 (Par condPort IsSend sendPiece Sealed shapeAt shapesOf sampledAt errPort seedMaps seedEntry cond_parts)
open Johnson.Pack (portOmZ)

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


theorem recStays_base : RecStays B.h₁ := fun _ _ _ => rfl

theorem decide10 (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) : c₁.decide = (send10 X).decide := by
  rw [first_is X N P c₁ k₁ q₁]

theorem rounds10 (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) : c₁.rounds = K1.rounds (par10 X) := by
  rw [first_is X N P c₁ k₁ q₁]
  exact List.append_nil _

/-- **WHAT IS LEFT OF ROW 1.0, (yes) AND (recStays) PAID.** -/
structure Left10b where
  d₁ : RDT
  d₂ : RDT
  data : (DK.at frS.P.T.a).ds₁.take c₁.rounds.length = [d₁, d₂]
  entry : d₁.entry = seedEntry (par10 X)
  kind : d₁.kind = .seeds
  rad : ℕ → ℕ
  cond : condPort (par10 X) rad = true
  e : ℕ
  err : errPort (par10 X) rad ≤ e
  le : Err.le ((seedMaps d₁ d₂ (par10 X).coordinates).err ((e, ()) : ℕ × Unit)) (rest₁ 0 [d₁, d₂]).err
  fOf : (fr₁ (DK.at frS.P.T.a)).E.Str → ∀ k, (portOmZ (par10 X).codes (shapeAt (par10 X) k) (rad k.val)).Str
  fIn : (fr₁ (DK.at frS.P.T.a)).E.Str → (wT d₁).Msg → ∀ k, (portOmZ (par10 X).codes (shapeAt (par10 X) k) (rad k.val)).Str
  words : ∀ y τ, fOf ((sendPiece (W := W) (F := fr₁ (DK.at frS.P.T.a)) (held c₁ : Block (Xi × FirstState) Claim) 0 d₁ d₂ (par10 X).coordinates e).ior.imp y τ) = fIn y τ.1
  /-- (hnew) behind the piece every leaf of the new tenant's word is shown -/
  hnew : ∀ a τ a', On₁ X N P (DK.at frS.P.T.a) B at_ R coll 0 a →
      (sendPiece (W := W) (F := fr₁ (DK.at frS.P.T.a)) (held c₁ : Block (Xi × FirstState) Claim) 0 d₁ d₂ (par10 X).coordinates e).ior.red.out a τ = some a' →
      ShownAt (Fk X N P) at_ 0 (strsOf (fr₁ (DK.at frS.P.T.a)) a'.2)
  /-- PUBLIC: the index masks' message is sampled -/
  sampled : (oneAt X).indexMasks.shape.answers ≠ 0
  /-- PUBLIC: the layout of that one message: one tree; the message is its first part -/
  lay : ∀ lay, OnBytes.layTrees (oneAt X).codes #[(oneAt X).indexMasks] = some lay → lay.shapes.size = 1 ∧ lay.tree.getD 0 0 = 0 ∧ lay.part.getD 0 0 = 0
  /-- PUBLIC: the table's seat of message 0 -/
  seat : at_ 0 = (0, 0)
  /-- a condition on the letter coll -/
  cell : CollCell coll
  k₀ : Fin (shapesOf (par10 X)).length
  sampledAt : sampledAt (par10 X) k₀
  tieS : ∀ a' : (Xi × FirstState) × (fr₁ (DK.at frS.P.T.a)).E.Str, a'.1.2.d.st.oracles.size = 1 →
      Sealed (par10 X).codes (shapeAt (par10 X) k₀) (rad k₀.val) (fOf a'.2 k₀) a'.1.2.d.st (a'.1.2.d.st.oracles.size - (shapesOf (par10 X)).length + k₀.val) →
      hasSmp B.h₁ (at_ 0).1 (at_ 0).2 a'.1 = true ∧ NoColl (Fk X N P) B.h₁ (at_ 0).1 (at_ 0).2 a'.1 (strsOf (fr₁ (DK.at frS.P.T.a)) a'.2)

/-- **Behind the first sending's piece the statement has just one message**: the block's own yes (sent0_of), read off the piece (piece_decides_at | piece_fits_at). -/
theorem one1_of (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (Pb : Public10 (oneAt X) pieces (groupsTold X.Y.told.1 0 (rootsAt X.Y.D.1 0)))
    (pc : Piece (ckP .two) (fr₁ (DK.at frS.P.T.a)) (Xi × FirstState) Claim W) (hpc : pc.b = held c₁)
    (a x : (Xi × FirstState) × (fr₁ (DK.at frS.P.T.a)).E.Str) (τ : _root_.Iop.Tr (uLT (ckP .two) pc.ds))
    (ha : On₁ X N P (DK.at frS.P.T.a) B at_ R coll 0 a) (hx : pc.ior.red.out a τ = some x) : x.1.2.d.st.oracles.size = 1 := by
  have hd := piece_decides_at pc a τ x hx
  have hf := (piece_fits_at pc a τ x hx).1
  rw [hpc] at hd hf
  have hd2 := (held_decide c₁ a.1 _ _ x.1 hd).2
  have hn := Johnson.RunOne.KeyRows1.on₁_two (Fk X N P) (fr₁ (DK.at frS.P.T.a)) B.h₁ at_ (oneAt X) R coll 0 a ha
  have hr := ha.resolve_left (fun hu => hu rfl)
  have h1 : Johnson.RunOne.KeyRows1.shape₁' (oneAt X) 0 a.1.2 = true := by
    have := hr.1
    rw [hn] at this
    exact this
  exact Johnson.RunOne.KeyRows1.size1_of_yes (oneAt X) pieces _ Pb c₁ (decide10 X N P c₁ k₁ q₁) (rounds10 X N P c₁ k₁ q₁) a.1.2 x.1.2 _ _ hf hd2 h1 hr.2.2.1.2.2.2.2.2.2.1

/-- Left10b gives Left10. -/
def left10_of (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (H : Left10b X N P DK c₁ rest₁ B at_ R coll) : Left10 X N P DK c₁ rest₁ B at_ R coll :=
  { d₁ := H.d₁, d₂ := H.d₂, data := H.data, entry := H.entry, kind := H.kind, rad := H.rad, cond := H.cond, e := H.e, err := H.err, le := H.le
    fOf := H.fOf, fIn := H.fIn, words := H.words
    recStays := recStays_base B
    New := ShownAt (Fk X N P) at_ 0
    hnew := H.hnew
    yes := sendYes₀ (Fk X N P) B.h₁ at_ (oneAt X) R coll pieces (groupsTold X.Y.told.1 0 (rootsAt X.Y.D.1 0))
      ⟨(cond_parts (par10 X) H.rad H.cond).1, H.sampled, H.lay⟩ (recStays_base B) H.cell H.seat c₁ (decide10 X N P c₁ k₁ q₁) (rounds10 X N P c₁ k₁ q₁)
    one1 := fun a τ x ha hx => one1_of X N P DK c₁ k₁ B at_ R coll q₁ ⟨(cond_parts (par10 X) H.rad H.cond).1, H.sampled, H.lay⟩ _ rfl a x τ ha hx
    k₀ := H.k₀, sampled := H.sampledAt, tieS := H.tieS }

/-- **THE FIELD r1_0 OF The35, (yes) AND (recStays) PAID.** -/
theorem r1_0_paid (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (H : Left10b X N P DK c₁ rest₁ B at_ R coll) :
    KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 0 :=
  r1_0_at X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R coll q₁ (left10_of X N P DK c₁ k₁ rest₁ B at_ R coll q₁ H)

end

end LPFD

#print axioms LPFD.recStays_base
#print axioms LPFD.rounds10
#print axioms LPFD.r1_0_paid
