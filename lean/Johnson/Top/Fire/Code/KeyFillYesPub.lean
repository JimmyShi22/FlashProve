-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/KeyFillYesPub.lean: Johnson/Top/Fire/Code/KeyFillYes.lean's on₁'_of_yes WITH THE START PAID BY TWO PUBLIC FACTS AND THE DATUM AS A BOOL.
  ft_zero       the first frame's first tree is 0 (whoever evaluates runs the step at that tree)
  on₁'_of_ok    ((held c₁).step 0 (x, start₁ x) [r₁, r₂] cols).isOk = true ⟹ ∃ a y', y'.1 = y₀.1 ∧ On₁' X N P D baseK atSix kreadFam coll 1 (a, y')
PAID HERE: the tables' book-keeping at border 0 := start_shape (Johnson/RunOne/KeyTen.lean: the plan has two lookups; the lookups' own message has the number 1) · the start's statement in order := start_order of the same file.
THAT A VIEW EXISTS AT WHICH THE BOOL IS TRUE IS AN EVALUATION's MATTER; THE ORACLES y' ARE BUILT BY US. AN IMPLICATION.
OBJECT: On₁' (KeyTablesR.lean); start_shape | start_order · USER: KeyFillYesOne.lean (on₁'_of_ok) · LETTERS: X N P D · x · r₁ r₂ cols · rad · decT recOf tab coll. Nothing on soundness.
-/
import Johnson.Top.Fire.Code.KeyFillYes
import Johnson.RunOne.KeyTen

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

open VerifiableInference.Desc.Key.Fill (six)
open Johnson.RunOne.KeyRows23 (baseK kreadFam numSix atSix holdsB)
open Johnson.RunOne.KeyRows1 (plan₁ start_shape start_order)
open Johnson.Pack (aOf)

theorem ft_zero (D : WholeD) : (fr₁ D).ft = 0 := rfl

section
variable (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (D : WholeD)
    (c₁ : Block (Fk X N P).S₁ (Fk X N P).Cl) (k₁ : List (Block (Fk X N P).S₁ (Fk X N P).Cl))
    {Cells Rec : Type} [Inhabited Cells] (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells) (recOf : Xi → Option Rec) (tab : Cells → ℕ → ℕ → OnBytes.F) (coll : Strs → Rec → Prop)

/-- **ONE STATEMENT INSIDE On₁' 1 FROM ONE BOOL ON A VIEW.** -/
theorem on₁'_of_ok (q₁ : (Fk X N P).first.blocksInOrder = c₁ :: k₁) (Pb : Public10 (oneAt X) pieces (groupsTold X.Y.told.1 0 (rootsAt X.Y.D.1 0)))
    (rad : ℕ → ℕ) (hC : condPort (par10 X) rad = true)
    (h2 : (lookupsOf (oneAt X)).length = 2) (hid : (oneAt X).ranges.messageId = 1)
    (x : Xi) (T4 : x.key.fits (oneAt X).lin.fold.index = true)
    (r₁ r₂ : _root_.Fmt.RoundView) (cols : List OpenedColumn)
    (hok : ((held c₁ : Block (Xi × FirstState) Claim).step 0 (x, (Fk X N P).start₁ x) [r₁, r₂] cols).isOk = true)
    (k₀ : Fin (shapesOf (par10 X)).length) (hk : sampledAt (par10 X) k₀) (Z2 : (shapesOf (par10 X)).length = 1)
    (tieC : (par10 X).codes = Johnson.Top.H.csKey) (tieS : shapeAt (par10 X) k₀ = Johnson.Top.H.shIdx)
    (t0 t1 t2 : String)
    (n0 : seatFaultAt (Fk X N P) Johnson.Top.H.csKey t0 Johnson.Top.H.shIdx 0 0 = none)
    (n1 : seatFaultAt (Fk X N P) Johnson.Top.H.csKey t1 Johnson.Top.H.shMul 1 0 = none)
    (n2 : seatFaultAt (Fk X N P) Johnson.Top.H.csKey t2 Johnson.Top.H.shW 5 0 = none)
    (f0 : holdsB (fr₁ D) 0 (aOf Johnson.Top.H.csKey Johnson.Top.H.shIdx) = true)
    (f1 : holdsB (fr₁ D) 1 (aOf Johnson.Top.H.csKey Johnson.Top.H.shMul) = true)
    (f2 : holdsB (fr₁ D) 5 (aOf Johnson.Top.H.csKey Johnson.Top.H.shW) = true)
    (y₀ : (fr₁ D).E.Str)
    (r : Rec) (L2 : recOf x = some r) (hcell : CollCell coll) (L2' : ¬ coll (strsOf (fr₁ D) y₀) r) :
    ∃ (a : Xi × FirstState) (y' : (fr₁ D).E.Str), y'.1 = y₀.1 ∧
      On₁' X N P D (baseK Johnson.Top.H.csKey six numSix atSix decT recOf (plan₁ (oneAt X)).orc) atSix (kreadFam Johnson.Top.H.csKey six numSix atSix tab) coll 1 (a, y') := by
  cases hs : (held c₁ : Block (Xi × FirstState) Claim).step 0 (x, (Fk X N P).start₁ x) [r₁, r₂] cols with
  | error e =>
    rw [hs] at hok
    cases hok
  | ok v =>
    obtain ⟨a, n⟩ := v
    obtain ⟨y', hy, h⟩ := on₁'_of_yes X N P D c₁ k₁ decT recOf tab coll q₁ Pb rad hC x (start_shape (oneAt X) h2 hid) (start_order _) T4 a r₁ r₂ cols n hs k₀ hk Z2 tieC tieS
      t0 t1 t2 n0 n1 n2 f0 f1 f2 y₀ r L2 hcell L2'
    exact ⟨a, y', hy, h⟩

end

end LPFD

#print axioms LPFD.ft_zero
#print axioms LPFD.on₁'_of_ok
