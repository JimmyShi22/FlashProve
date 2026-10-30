-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- Statement and proof read once.
/-
AT ANY WITNESS: no Script, filling, prover or thread is named.
Johnson/Desc/ProofFile/Honest/K3/Term/LookupKeyFormsAreTheLibrarysKeysAtAttention.lean: the honest
side of the kind "lookup" (K3): at the lookup on the calls of a group's attention, the key vectors
that the table of joints' item reads off a witness (the field fills of `AtAttention`,
Honest/K3/Law/Thread/ExchangeOuts.lean) have the joint vector of the key vectors on which the honest
lookup runs (`fills_attention`, Honest/K3/Law/Thread/ExchangeFillAt.lean). One theorem, conditional.

Hypotheses that remain. The files are in scope, read, and make the public part; the group is below
twelve; namesFit; the shape is the plan's and passes the library's test; attentionShape is the plan's;
the padding rows (`paddingRowsAtAttentionAreTheLibrarys`, beside this file, pays it in scope).
witnessCellsAreTheTraces: THE ONE TIE ON VALUES: an equation of whole functions: the matrices that the
caller unpacks off the witness's messages are the casts of the trace's at the link. The statement
ties the letter tail to nothing: at the honest trace the tie can be met only at the plan's own record
of the link's smallness test: the caller must bring that record.

Limits. No file shows the tie of any witness. The proof spends it at the addresses of the raw names
alone, never at the planes' matrix. The bound n < 2 ^ shape.v is idle. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeOuts
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeTies
import Johnson.Desc.K5.Honest.Law.KvOfCells
import Johnson.Road.Lane5KvAll
import Johnson.Goal.Meaning.AttScope
import Johnson.Goal.Meaning.AttNumsScope
import Johnson.Goal.Meaning.AttForInScope
import Johnson.Road.Lane5AttTabsEq
import Johnson.HonestTrace.FromCells

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open OnBytes.Model (HTailF2)
open OnBytes.Slice (GE)
open OnBytes.HonestTrace (fromA cellOf NamesFit Tr fsAt)
open OnBytes.Road (Hd.shapeA)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.First.Look (Sent attLay)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.OnPublicFiles

local notation "PlaceL" => VerifiableInference.Desc.First.Look.Place

/-- **At an attention link the item's key vectors have the joint vector of the library's.**
attentionShape: the shape that the table of joints reads at the link (attAt); it is the plan's.
witnessCellsAreTheTraces: THE ONE
TIE ON VALUES: the matrices that the caller reads off the witness's messages are the casts of the
trace's list.
paddingRowsAreTheLibrarys: public: PaddingRowsAtAttentionAreTheLibrarys.lean in this folder. shape:
the site's. -/
theorem lookupKeyFormsAreTheLibrarysKeysAtAttention {Cells Tok : Type}
    {publicFiles : VerifierAndGoals.PublicFiles} {parameters : Inst.Model.ScalesAndPolicy} {layoutFile : Option ByteArray}
    {publicPart : OnBytes.Model.Verify.Public}
    (inScope : VerifierAndGoals.InScope publicFiles = true)
    (filesRead : VerifierAndGoals.readFiles publicFiles = .ok parameters)
    (publicPartMade : OnBytes.Model.Verify.publicOf publicFiles.pol publicFiles.KL layoutFile =
      .ok publicPart)
    {group : Nat} (groupBelowTwelve : group < 12)
    (attentionShape : OnBytes.Attention.Shape)
    (attentionShapeIsThePlans : attentionShape = Hd.shapeA publicPart group)
    (paddingRowsAreTheLibrarys :
      OnBytes.Road.L5.PadEq (Hd.shapeA publicPart group) (fsAt publicPart group))
    (sent : Sent) (letters : K3Letters Cells Tok) (place : PlaceL) (tail : HTailF2)
    (witness : Wit Cells Tok MsgT) (trace : Tr)
    (namesFit : NamesFit publicPart trace)
    (witnessCellsAreTheTraces :
      VerifiableInference.Desc.First.Att.P.matsOfMsg place tail sent letters.rad
        (attMs place sent letters.rad (fun j => letters.seat place.link false j.1) letters.arr
          witness) =
      OnBytes.Road.Rows.Norms.castM (trace (2 * group + 1)))
    (shape : OnBytes.Model.Forest.Shape) (shapeIsThePlans : shape = fsAt publicPart group)
    (shapeIsLawful : FoNums.ok shape = true) (theta : OnBytes.Slice.GE) :
    ∀ n, n < 2 ^ shape.v →
      OnBytes.Ends.jointKey shape
        (Cb.Fo.forK Cb.Gl.E
          (attLay attentionShape place.fs place.lm place.F.next place.ns tail) ()
          (Cb.Fo.zext (attMu place tail sent letters.rad
            (fun j => letters.seat place.link false j.1) letters.arr witness))) theta n =
      OnBytes.Ends.jointKey shape
        (OnBytes.Ends.A.kvA (Hd.shapeA publicPart group) (fsAt publicPart group)
          (fromA publicPart (cellOf publicPart trace) group)) theta n := by
  subst attentionShapeIsThePlans
  subst shapeIsThePlans
  obtain ⟨cf, hh, hc, -, -, -, U⟩ :=
    Meaning.Att.hid_in_scope inScope filesRead publicPartMade groupBelowTwelve
  -- the cells that the caller reads off the witness are the casts of the trace's, at every name
  have hraw : ∀ q : Inst.Model.AttSeg.Raw,
      VerifiableInference.Desc.First.Look.rawOf (Hd.shapeA publicPart group) place.ns tail
        (attMu place tail sent letters.rad (fun j => letters.seat place.link false j.1) letters.arr
          witness) q =
      (Inst.Model.AttSeg.castT
        (OnBytes.Road.L5.cellsA (Hd.shapeA publicPart group) (trace (2 * group + 1))) :
          Inst.Model.AttSeg.Raw → Cb.Gl.E) q := by
    intro q
    rw [H2K5.Honest.raw_is_msg, witnessCellsAreTheTraces]
    rfl
  -- the two families agree at each of the four calls, at every index
  have hfam : ∀ (c : Fin 4) (X : ℕ),
      Cb.Fo.forK Cb.Gl.E
        (attLay (Hd.shapeA publicPart group) place.fs place.lm place.F.next place.ns tail) ()
        (Cb.Fo.zext (attMu place tail sent letters.rad
          (fun j => letters.seat place.link false j.1) letters.arr witness)) c.val X =
      OnBytes.Ends.A.kvA (Hd.shapeA publicPart group) (fsAt publicPart group)
        (fromA publicPart (cellOf publicPart trace) group) c.val X := by
    intro c X
    rw [H2K5.Honest.kv_of_raw place (Hd.shapeA publicPart group) tail _ (fun q _ => hraw q) c X,
      OnBytes.HonestTrace.fromA_cellOf namesFit groupBelowTwelve,
      OnBytes.Road.L5.kvA_eq_keyVec_all (OnBytes.Road.L5.numsA_of_hid hh hc.ldh)
        (OnBytes.Road.L5.laidA_of_hid hh U)
        (OnBytes.Road.L5.inside_of_four (OnBytes.Road.L5.shaped_of_hid hh)
          (OnBytes.Road.L5.tests_of_hid hh).1 (OnBytes.Road.L5.four_of_hid hh U))
        paddingRowsAreTheLibrarys _ c]
    rfl
  have hNC : (fsAt publicPart group).NC = 4 :=
    (Meaning.Att.sameCalls_in_scope inScope filesRead publicPartMade groupBelowTwelve).NC
  obtain ⟨_, hcall, _⟩ := Cb.Fo.ok_parts shapeIsLawful
  intro n _
  unfold OnBytes.Ends.jointKey
  dsimp only
  split
  · rename_i hy
    have hc4 : (fsAt publicPart group).callOf.getD (n % 2 ^ (fsAt publicPart group).rK) 0 < 4 := by
      rw [← hNC]
      exact (hcall _ hy).1
    exact congrArg (fun z => z + _) (hfam ⟨_, hc4⟩ _)
  · rfl


end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.lookupKeyFormsAreTheLibrarysKeysAtAttention
