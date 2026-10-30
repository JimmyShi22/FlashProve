-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/MadeAtJoinB.lean: the second half of the join of `Key.madeAt`'s ledger
(Johnson/AtFull/Made/Ledger.lean): the chains are read back, the segments are built, and `madeAt`
returns. General in the public part X.

What it says.
  `chainsAt x cfg`   the four parts that `chainsOf` returns at the written sizes and plans.
  `chains_join`     c₃ g₁ g₂ g₃ paid, under: `PubFull` · the shapes and sizes as `shapes_join` gives
                    them · the views · `configure`'s return as `configure_join` gives it · 32 bytes.
  `built_join`      h₁ paid, under: `PubFull` · a₂ a₃ a₄ · the views.
  `madeAt_of_rest`  `Key.madeAt X lay cfg` returns, with its value said, under: X is as at the full
                    size (`PubFull`) · twelve plans of each kind (hG hA) · the segments' views are
                    the written ones (hV) · the layout file reads as the written value (b₁) · the
                    range checks are rc, with the written bits (hc hck) · the digest has 32 bytes ·
                    e₁: the proof file's first plan returns the written one · hsc: the 25 links'
                    scalars are the written ones · s₁: what is sent, from the written value.
                    IN NUMBERS: of the ledger's 27 premises 24 are paid; three stay as they were
                    (b₁ · e₁ · s₁); eight hypotheses by field have come in (P, itself four
                    equations · hG · hA · hV · hc · hck · h32 · hsc): eleven binders.
                    s₁ is asked at every x: the ranges sh stand under «∃» in the conclusion, so s₁
                    cannot name the shapes; `sendsFrom` reads the sizes and the seven plans alone
                    (`sendsFrom_free`, Johnson/AtFull/Made/SendsLedger.lean). The entry file's
                    sendings are no part of `madeAt`'s value: s₁ asks only that there are some.

Where the facts used lie, under Johnson/AtFull/Made/ but for the last. key_read_written ·
proof_read_written: ReadsAtWritten.lean · firstWritten_of: ReadsAtFull.lean · fit_at_sized:
FitAtSized.lean · linksFit_full: LinksFitFull.lean · built_at_full: BuiltAtFull.lean · lists_proof:
ListsProof.lean · madeWritten_parts: MadeOfPartsIsWritten.lean · configure_record_read:
OnBytes/Tie/EntryAtCfgRecord.lean.

Limits. A joining: it pays none of its hypotheses. THAT ANY PUBLIC FILES MEET THEM IS SHOWN NOWHERE
HERE. Nothing on soundness.
-/
import Johnson.AtFull.Made.MadeAtJoinA
import Johnson.AtFull.Made.FitAtSized
import Johnson.AtFull.Made.ReadsAtWritten
import Johnson.AtFull.Made.ListsProof
import Johnson.AtFull.Made.MadeOfPartsIsWritten
import OnBytes.Tie.EntryAtCfgRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Model OnBytes.Model.Verify OnBytes.Model.Stages OnBytes.Params
open VerifiableInference.PlanWritten (proofSizedFull FirstWritten MadeWritten request_shape_written)
open VerifiableInference.PlanWritten.Joined (writtenSized)
open VerifiableInference.Number.ByRuns (proofThree keyThree)
open Johnson.G (pricedEntryFull layoutFull)
open Johnson.AtFull.LayoutRead (LW)
open H2K.Sizes (PubFull)
open Lk6.AtPlan (keyFull)

/-- What `chainsOf` returns at the written sizes and plans. -/
def chainsAt (x : Shapes) (cfg : ByteArray) : Chains :=
  { made := madeW x cfg,
    key := keyOf cfg keyFull keyThree.A.plan.plan keyThree.B.plan.plan keyThree.C.plan.plan,
    link := OnBytes.Tie.linkAtCfg Params.recordRead cfg,
    proof := proofOf cfg recordLines x writtenSized proofThree.A.plan.plan proofThree.B.plan.plan
      proofThree.C.plan.plan }

/-- The written identifiers fit the format's words. -/
theorem ids_words : wordsB idsFull = true := by decide +kernel

/-- There are 25 of them. -/
theorem ids_length : idsFull.length = 25 := by decide +kernel

/-- The binding tree's shape at the written lines and sizes. -/
theorem binding_at_sized :
    (⟨Params.clog2 recordLines.slots, writtenSized.set.saltBytes⟩ : LinBindingShape) = ⟨6, 40⟩ :=
  binding_of_two (l := recordLines) (z := writtenSized) (by decide +kernel) (by decide +kernel)

/-- The written first plan of the proof file draws no position by bytes. -/
theorem posB_written : proofThree.A.plan.plan.posB = 0 := by decide +kernel

/-- The pending rows of the sub-proofs at twelve groups. -/
theorem pending_of {X : Public} (P : PubFull X) (sh : Plan.Shape) (rc : List RangeCheck) :
    (xOf X sh rc).sub.pendingRows = 13 := by
  show X.NGr + 1 = 13
  rw [P.groups]

/-- **The chains are read back.** -/
theorem chains_join {X : Public} {lay cfg : ByteArray} {links : Array LinkH} {sh : Plan.Shape}
    {rc : List RangeCheck} (P : PubFull X)
    (hs : shapesOf X (some lay) = .ok (links, xOf X sh rc))
    (c₂ : sized X.P.frame (xOf X sh rc) = .ok writtenSized)
    (hv : links.toList.map viewOf = viewFull)
    (hc : configure X.P.frame (xOf X sh rc) cfg 0 = .ok (madeW (xOf X sh rc) cfg))
    (h32 : cfg.size = 32) :
    chainsOf X (some lay) cfg = .ok (chainsAt (xOf X sh rc) cfg) := by
  have hc' : configure recordLines (xOf X sh rc) cfg 0 = .ok (madeW (xOf X sh rc) cfg) := by
    rw [← P.frame]
    exact hc
  exact chainsOf_of_parts hs c₂ (fit_at_sized hv rfl) hc
    (key_read_written hc' rfl h32 rfl)
    (OnBytes.Tie.configure_record_read h32 hc')
    (proof_read_written hc' rfl h32 rfl binding_at_sized rfl (pending_of P sh rc) ids_words)

/-- The first chain's parameters as read back are the written ones. -/
theorem first_written_join {X : Public} (P : PubFull X) (sh : Plan.Shape) (rc : List RangeCheck)
    (cfg : ByteArray) : FirstWritten (chainsAt (xOf X sh rc) cfg).proof.first :=
  firstWritten_of rfl binding_at_sized rfl (pending_of P sh rc)

/-- **The segments are built.** -/
theorem built_join {X : Public} {cfg : ByteArray} {links₀ links : Array LinkH} {sh : Plan.Shape}
    {rc : List RangeCheck} (P : PubFull X) (a₂ : headLast links₀ = .ok ())
    (a₃ : linksCount links₀ = .ok ())
    (a₄ : declareLinks links₀ X.NGr X.p4 = .ok (links, declaredFull))
    (hv : links.toList.map viewOf = viewFull) :
    buildLinksH links₀ X.NGr X.p4 X.layers.wsLay (chainsAt (xOf X sh rc) cfg).proof.first =
      .ok { links := links } :=
  built_at_full (chains := chainsAt (xOf X sh rc) cfg) a₂ a₃ a₄ hv rfl P.groups P.wsLay codes_tie
    request_shape_written rfl matrixRows_written kCol_tie (pending_of P sh rc) rfl
    posB_written linksFit_full

/-- **`Key.madeAt` RETURNS, WITH ITS VALUE SAID**: of the ledger's 27 premises three stay
(b₁ e₁ s₁); eight hypotheses by field have come in. -/
theorem madeAt_of_rest {X : Public} {lay cfg : ByteArray} {rc : List RangeCheck}
    {k0 k1 k2 p0 p1 p2 : Johnson.G.ChainSends} (P : PubFull X)
    (hG : X.G.size = 12) (hA : X.A.size = 12)
    (hV : (OnBytes.TieK.listedOf X default).map Decl.viewL = Decl.viewsFull)
    (b₁ : Plan.layoutRead lay = some LW) (hc : rangeChecksOf X = some rc)
    (hck : rc.map rangeCheckBits = checksFull.map rangeCheckBits) (h32 : cfg.size = 32)
    (e₁ : firstPlan proofSizedFull (subproofsWith X reqLinksW) = .ok proofThree.A.plan)
    (hsc : ∀ j (_ : j < writtenSized.proof.request.link.length) (hj' : j < scalarsFull.length),
      scalarsOf writtenSized.proof.set
        (forEach (List.range (momentsOf writtenSized.proof.request.link[j])) fun m =>
          (subproofsWith X reqLinksW).plan j m) = .ok scalarsFull[j])
    (s₁ : ∀ x, ∃ en, Johnson.G.sendsFrom (madeW x cfg) = .ok [k0, k1, k2, en, p0, p1, p2]) :
    ∃ (links₀ links : Array LinkH) (sh : Plan.Shape),
      VerifiableInference.Desc.Key.madeAt X lay cfg =
        .ok ⟨{ X := X, cfg := cfg, chains := chainsAt (xOf X sh rc) cfg,
               built := { links := links } }, (k0, k1, k2), (p0, p1, p2)⟩ ∧
      linksOf X default = .ok links₀ ∧
      declareLinks links₀ X.NGr X.p4 = .ok (links, declaredFull) ∧
      links.toList.map viewOf = viewFull ∧
      Plan.shapeOfLayout X.layers.wsLay X.layers.wsLay.lk = some sh ∧
      shapesOf X (some lay) = .ok (links, xOf X sh rc) ∧
      FirstWritten (chainsAt (xOf X sh rc) cfg).proof.first ∧
      MadeWritten (chainsAt (xOf X sh rc) cfg).made := by
  obtain ⟨links₀, links, sh, a₁, a₂, a₃, a₄, hv, hsh, hs, c₂⟩ := shapes_join P hG hA hV b₁ hc
  have R : ShapesRead (xOf X sh rc) proofThree.A.plan :=
    ⟨pending_of P sh rc, ids_length, hck, lists_proof, hsc⟩
  have hcf := configure_join cfg P.frame c₂ e₁ R
  have hch := chains_join P hs c₂ hv hcf h32
  obtain ⟨en, hse⟩ := s₁ (xOf X sh rc)
  refine ⟨links₀, links, sh, ?_, a₁, a₄, hv, hsh, hs, first_written_join P sh rc cfg,
    madeWritten_parts _ cfg⟩
  exact madeAt_of_parts hch a₁ (built_join P a₂ a₃ a₄ hv) hse

#print axioms Johnson.AtFull.Made.ids_words
#print axioms Johnson.AtFull.Made.ids_length
#print axioms Johnson.AtFull.Made.binding_at_sized
#print axioms Johnson.AtFull.Made.posB_written
#print axioms Johnson.AtFull.Made.pending_of
#print axioms Johnson.AtFull.Made.chains_join
#print axioms Johnson.AtFull.Made.first_written_join
#print axioms Johnson.AtFull.Made.built_join
#print axioms Johnson.AtFull.Made.madeAt_of_rest

end Johnson.AtFull.Made
