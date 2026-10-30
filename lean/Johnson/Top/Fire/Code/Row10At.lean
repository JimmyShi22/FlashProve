-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/Row10At.lean: THE TRACER ON ROW 1.0: THE FIELD r1_0 OF The35 (The35.lean) AT THE KEY FILE's OWN DESCRIPTION, WITH WHAT IS LEFT HERE AS ONE STRUCTURE OF NAMED PREMISES: Left10 (Row10Paid.lean pays a part of it).
OBJECT: The35.r1_0 · USER: The21's filler · LETTERS: X N P · the maker's cut and rests · B at_ R coll.
  par10        the sending kind's parameters at the place: sendingPar (Johnson/Desc/Key/One.lean) at the description's own arguments
  first_is     PROVED: under q₁ the maker's c₁ IS the description's own first block: sendIndexMasks …, as Chain.blocksInOrder lays it (its test on the plan turned alone)
  second_is    PROVED: under q₁ the chain has a second block
  isSend10     PROVED: held c₁ is a sending at par10 (KeyRow10Send.lean): THE SENDING KIND's LAW's PREMISE hS IS PAID
  Left10       WHAT IS LEFT: data (the stretch is two rounds' data; the first has the place's own entry of the seeds) · cond (the sending kind's one Boolean on the plan and the radii) · err | le · the reader of the words · recStays · New | hnew · yes · one1 (behind the block the statement has just one message) · tieS (asked at such statements alone)
  r1_0_at      PROVED FROM q₁ AND Left10
Nothing on soundness.
-/
import Johnson.Top.Fire.Code.Row10House
import Johnson.RunOne.KeyRow10Send

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

open Johnson.RunOne.KeyRows1 (RecStays SendYes₀ isSend_idx isSend_held isSend_of_decide)
open VerifiableInference.Desc.K1 (Par condPort IsSend sendPiece send_goodIn_entry Sealed shapeAt shapesOf sampledAt errPort seedMaps seedEntry seeds_one seed_draws)
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


/-- The sending kind's parameters at the key file's first place. -/
def par10 : Par := sendingPar (oneAt X) pieces.idx "the index masks" #[(oneAt X).indexMasks] (groupsTold X.Y.told.1 0 (rootsAt X.Y.D.1 0))

/-- The description's own first block, in front of Chain.blocksInOrder. -/
def send10 : Block FirstState Claim := sendIndexMasks (oneAt X) pieces (groupsTold X.Y.told.1 0 (rootsAt X.Y.D.1 0))

theorem first_is (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) : c₁ = { send10 X with planOk := (send10 X).planOk && (send10 X).hasNoClaimsAndNothingAfter } := by
  have h := congrArg List.head? q₁
  exact (Option.some.inj h).symm

theorem second_is (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) : ∃ c l, k₁ = c :: l := by
  have h := congrArg List.tail q₁
  exact ⟨_, _, h.symm⟩

theorem isSend10 (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) : IsSend (par10 X) (fun a : Xi × FirstState => a.2.d.st) (held c₁ : Block (Xi × FirstState) Claim) :=
  isSend_held _ _ c₁ (isSend_of_decide _ _ (send10 X) c₁ (by rw [first_is X N P c₁ k₁ q₁]) (isSend_idx _ _ _))

/-- **WHAT IS LEFT OF ROW 1.0.** -/
structure Left10 where
  d₁ : RDT
  d₂ : RDT
  /-- (data) THE FRAME's DATA: the first chain's data begin with two rounds' for the first block; the first has the place's own entry of the seeds -/
  data : (DK.at frS.P.T.a).ds₁.take c₁.rounds.length = [d₁, d₂]
  entry : d₁.entry = seedEntry (par10 X)
  kind : d₁.kind = .seeds
  /-- (cond) THE SENDING KIND's ONE BOOLEAN ON THE PLAN AND THE RADII -/
  rad : ℕ → ℕ
  cond : condPort (par10 X) rad = true
  /-- (err | le) the written count, and that the kind's own errors lie below the maker's rest's -/
  e : ℕ
  err : errPort (par10 X) rad ≤ e
  le : Err.le ((seedMaps d₁ d₂ (par10 X).coordinates).err ((e, ()) : ℕ × Unit)) (rest₁ 0 [d₁, d₂]).err
  /-- (words) the reader of the words off the oracles behind the block: it reads, of the stretch's transcript, the first round's message alone -/
  fOf : (fr₁ (DK.at frS.P.T.a)).E.Str → ∀ k, (portOmZ (par10 X).codes (shapeAt (par10 X) k) (rad k.val)).Str
  fIn : (fr₁ (DK.at frS.P.T.a)).E.Str → (wT d₁).Msg → ∀ k, (portOmZ (par10 X).codes (shapeAt (par10 X) k) (rad k.val)).Str
  words : ∀ y τ, fOf ((sendPiece (W := W) (F := fr₁ (DK.at frS.P.T.a)) (held c₁ : Block (Xi × FirstState) Claim) 0 d₁ d₂ (par10 X).coordinates e).ior.imp y τ) = fIn y τ.1
  /-- (recStays) A CONDITION ON THE READING -/
  recStays : RecStays B.h₁
  /-- (New | hnew) a fact of the piece on the strings behind -/
  New : Strs → Prop
  hnew : ∀ a τ a', On₁ X N P (DK.at frS.P.T.a) B at_ R coll 0 a →
      (sendPiece (W := W) (F := fr₁ (DK.at frS.P.T.a)) (held c₁ : Block (Xi × FirstState) Claim) 0 d₁ d₂ (par10 X).coordinates e).ior.red.out a τ = some a' → New (strsOf (fr₁ (DK.at frS.P.T.a)) a'.2)
  /-- (yes) WHAT THE BLOCK's YES GIVES OF THE RECORD -/
  yes : SendYes₀ (Fk X N P) B.h₁ at_ (oneAt X) R coll New c₁
  /-- (one1) behind the block the statement has just one message -/
  one1 : ∀ a τ x, On₁ X N P (DK.at frS.P.T.a) B at_ R coll 0 a →
      (sendPiece (W := W) (F := fr₁ (DK.at frS.P.T.a)) (held c₁ : Block (Xi × FirstState) Claim) 0 d₁ d₂ (par10 X).coordinates e).ior.red.out a τ = some x → x.1.2.d.st.oracles.size = 1
  /-- (tieS) AT A STATEMENT WITH JUST ONE MESSAGE, «sealed» at the one sampled message gives the table's two facts at its seat -/
  k₀ : Fin (shapesOf (par10 X)).length
  sampled : sampledAt (par10 X) k₀
  tieS : ∀ a' : (Xi × FirstState) × (fr₁ (DK.at frS.P.T.a)).E.Str, a'.1.2.d.st.oracles.size = 1 →
      Sealed (par10 X).codes (shapeAt (par10 X) k₀) (rad k₀.val) (fOf a'.2 k₀) a'.1.2.d.st (a'.1.2.d.st.oracles.size - (shapesOf (par10 X)).length + k₀.val) →
      hasSmp B.h₁ (at_ 0).1 (at_ 0).2 a'.1 = true ∧ NoColl (Fk X N P) B.h₁ (at_ 0).1 (at_ 0).2 a'.1 (strsOf (fr₁ (DK.at frS.P.T.a)) a'.2)

/-- **THE FIELD r1_0 OF The35 AT THE KEY FILE's OWN DESCRIPTION, FROM WHAT IS LEFT.** -/
theorem r1_0_at (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (H : Left10 X N P DK c₁ rest₁ B at_ R coll) :
    KeepsAt (On₁' X N P (DK.at frS.P.T.a) B at_ R coll) (Cl₁ X N P (DK.at frS.P.T.a) B at_ R) ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁) 0 := by
  obtain ⟨c, l, hk⟩ := second_is X N P c₁ k₁ q₁
  have h1 := seeds_one (par10 X) H.rad H.cond
  obtain ⟨a1, a2, a3, a4, a5⟩ := seed_draws (par10 X) h1 H.d₁ H.entry H.kind
  exact r1_0_of X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R coll q₁
    (owed10_of X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R coll c l hk H.d₁ H.d₂ H.data H.recStays (par10 X) H.rad H.cond h1
      (isSend10 X N P c₁ k₁ q₁) a1 a2 a3 a4 a5 H.e H.err H.fOf H.fIn H.words H.le H.New H.hnew H.yes (fun x => x.1.2.d.st.oracles.size = 1) H.one1 H.k₀ H.sampled H.tieS)

end

end LPFD

#print axioms LPFD.first_is
#print axioms LPFD.isSend10
#print axioms LPFD.r1_0_at
