-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/Row10House.lean: THE TRACER ON ROW 1.0, LEVEL 2: OF THE SIX FIELDS OF Owed10 (Row10.lean), (good) IS PAID BY THE SENDING KIND's OWN LAW send_goodIn (Johnson/Desc/K1/Law/GoodSend3.lean: general in the carried record and in the block), AT THAT LAW's OWN PREMISES, WHICH ARE HANDED ON BY NAME; THE STRETCH AND WHAT IS PUT BEHIND ARE READ OFF THE MAKER's OWN CUT (rowAt₁, RowCut.lean); (tie) from the premise tieS (paid further up the counted road: LPFD.tieS_at, Row10Seven.lean).
OBJECT: Owed10 at the description's own first block c₁ · USER: r1_0_of · LETTERS: as Row10.lean's, and that law's: P₁ rad d₁ d₂ e fOf fIn.
  stretch10    PROVED: where the chain has a second block, the maker's first piece stands at base 0, at the first c₁.rounds.length of the chain's data, with nothing put behind
  owed10_of    PROVED: Owed10 from: the stretch is two rounds' data [d₁, d₂] · that law's premises · (le) at the sending kind's written errors · recStays | hnew | yes (this file's own) · On' | hkeep (what is sure behind the block, handed to that law as its letter On') · tieS: WHERE On' HOLDS, «sealed» at the one sampled message k₀ gives hasSmp ∧ NoColl at at_ 0
Nothing on soundness.
-/
import Johnson.Top.Fire.Code.Row10
import Johnson.Desc.K1.Law.GoodSend3
import Johnson.Desc.Key.KeySealTie

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

open Johnson.RunOne.KeyRows1 (RecStays SendYes₀)
open VerifiableInference.Desc.K1 (Par condPort IsSend sendPiece send_goodIn Sealed SeedIs shapeAt shapesOf sampledAt errPort seedMaps)
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


/-- **Where the maker lays the first piece.** -/
theorem stretch10 (c : Block (Fk X N P).S₁ (Fk X N P).Cl) (l : List (Block (Fk X N P).S₁ (Fk X N P).Cl)) (hk : k₁ = c :: l)
    (b : Block FirstState Claim) (base : ℕ) (ds : List RDT) (back : List _root_.Fmt.RoundView)
    (hp : ((atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).p₁ :: (atDesc (Fk X N P) (piecesAt (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd)).l₁)[0]? = some (pieceOf (held b) base ds back (rest₁ 0 ds))) :
    base = 0 ∧ ds = (DK.at frS.P.T.a).ds₁.take c₁.rounds.length ∧ back = [] := by
  obtain ⟨b', -, e⟩ := rowAt₁ (ckP .two) (Fk X N P) (DK.at frS.P.T.a) c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd 0 _ hp
  subst hk
  exact ⟨congrArg Piece.base e, congrArg Piece.ds e, congrArg Piece.back e⟩

/-- **Owed10, its law paid by the sending kind's own (send_goodIn).** -/
theorem owed10_of (c : Block (Fk X N P).S₁ (Fk X N P).Cl) (l : List (Block (Fk X N P).S₁ (Fk X N P).Cl)) (hk : k₁ = c :: l)
    (d₁ d₂ : RDT) (hds : (DK.at frS.P.T.a).ds₁.take c₁.rounds.length = [d₁, d₂])
    (hR : RecStays B.h₁)
    -- THE PREMISES OF THE SENDING KIND's OWN LAW (GoodSend3.lean:136-153), BY NAME
    (P₁ : Par) (rad : ℕ → ℕ) (hC : condPort P₁ rad = true) (h1 : P₁.seeds = 1)
    (hS : IsSend P₁ (fun a : Xi × FirstState => a.2.d.st) (held c₁ : Block (Xi × FirstState) Claim))
    (hpl : PlainDraws (_root_.Fmt.dsOf d₁.entry d₁.kind)) (hE : nE (_root_.Fmt.dsOf d₁.entry d₁.kind) = P₁.coordinates + 1)
    (hP : nP (_root_.Fmt.dsOf d₁.entry d₁.kind) = 0) (hz : IsNZ (_root_.Fmt.dsOf d₁.entry d₁.kind) P₁.coordinates) (hl : d₁.entry.logN ≤ 64)
    (e : ℕ) (he : errPort P₁ rad ≤ e)
    (fOf : (fr₁ (DK.at frS.P.T.a)).E.Str → ∀ k, (portOmZ P₁.codes (shapeAt P₁ k) (rad k.val)).Str)
    (fIn : (fr₁ (DK.at frS.P.T.a)).E.Str → (wT d₁).Msg → ∀ k, (portOmZ P₁.codes (shapeAt P₁ k) (rad k.val)).Str)
    (hf : ∀ y τ, fOf ((sendPiece (W := W) (F := fr₁ (DK.at frS.P.T.a)) (held c₁ : Block (Xi × FirstState) Claim) 0 d₁ d₂ P₁.coordinates e).ior.imp y τ) = fIn y τ.1)
    -- (le) AT THE SENDING KIND's WRITTEN ERRORS
    (hle : Err.le ((seedMaps d₁ d₂ P₁.coordinates).err ((e, ()) : ℕ × Unit)) (rest₁ 0 [d₁, d₂]).err)
    -- THIS FILE's OWN
    (New : Strs → Prop)
    (hnew : ∀ a τ a', On₁ X N P (DK.at frS.P.T.a) B at_ R coll 0 a →
      (sendPiece (W := W) (F := fr₁ (DK.at frS.P.T.a)) (held c₁ : Block (Xi × FirstState) Claim) 0 d₁ d₂ P₁.coordinates e).ior.red.out a τ = some a' → New (strsOf (fr₁ (DK.at frS.P.T.a)) a'.2))
    (yes : SendYes₀ (Fk X N P) B.h₁ at_ (oneAt X) R coll New c₁)
    -- (On' | hkeep) WHAT IS KNOWN FOR CERTAIN BEHIND THE BLOCK, HANDED TO THAT LAW AS ITS OWN LETTER On' (GoodSend3.lean:150-152): without it tieS would be asked at every statement
    (On' : (Xi × FirstState) × (fr₁ (DK.at frS.P.T.a)).E.Str → Prop)
    (hkeep : ∀ a τ x, On₁ X N P (DK.at frS.P.T.a) B at_ R coll 0 a →
      (sendPiece (W := W) (F := fr₁ (DK.at frS.P.T.a)) (held c₁ : Block (Xi × FirstState) Claim) 0 d₁ d₂ P₁.coordinates e).ior.red.out a τ = some x → On' x)
    -- (tieS) WHERE On' HOLDS, «SEALED» AT THE SAMPLED MESSAGE k₀ GIVES THE TABLE's TWO FACTS AT ITS SEAT
    (k₀ : Fin (shapesOf P₁).length) (hk₀ : sampledAt P₁ k₀)
    (tieS : ∀ a' : (Xi × FirstState) × (fr₁ (DK.at frS.P.T.a)).E.Str, On' a' →
      Sealed P₁.codes (shapeAt P₁ k₀) (rad k₀.val) (fOf a'.2 k₀) a'.1.2.d.st (a'.1.2.d.st.oracles.size - (shapesOf P₁).length + k₀.val) →
      hasSmp B.h₁ (at_ 0).1 (at_ 0).2 a'.1 = true ∧ NoColl (Fk X N P) B.h₁ (at_ 0).1 (at_ 0).2 a'.1 (strsOf (fr₁ (DK.at frS.P.T.a)) a'.2)) :
    Owed10 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd B at_ R coll c₁ where
  recStays := hR
  each := fun base ds back hp => by
    obtain ⟨rfl, e2, rfl⟩ := stretch10 X N P DK c₁ k₁ c₂ k₂ c₃ k₃ rest₁ rest₂ rest₃ dW wEnd c l hk c₁ base ds back hp
    have e3 : ds = [d₁, d₂] := e2.trans hds
    subst e3
    refine ⟨⟨fun _ _ w => w, (seedMaps d₁ d₂ P₁.coordinates).err ((e, ()) : ℕ × Unit)⟩, New, _, fun _ _ => True, fun _ _ => True, hle, hnew, yes,
      send_goodIn P₁ rad hC h1 (held c₁ : Block (Xi × FirstState) Claim) (fun a => a.2.d.st) hS 0 d₁ d₂ hpl hE hP hz hl e he fOf fIn hf
        (On₁ X N P (DK.at frS.P.T.a) B at_ R coll 0) On' (fun _ _ => True) (fun _ _ => True) hkeep (fun _ _ _ _ _ _ _ => trivial), ?_⟩
    exact fun a' h => tieS a' h.1 (h.2 k₀ hk₀)

end

end LPFD

#print axioms LPFD.stretch10
#print axioms LPFD.owed10_of
