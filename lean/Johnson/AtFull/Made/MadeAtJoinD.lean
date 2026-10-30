-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/MadeAtJoinD.lean: `Key.madeAt` returns, with what is sent as written values.

What it says.
  `sends_join`      s₁: from the `Configured` of the written sizes and plans, at whatever shapes and
                    digest, `sendsFrom` returns the written sendings of the key file's and the proof
                    file's three chains (`keySendsFull`, `proofSendsFull`) and some sendings of the
                    entry file (`sendsWhole_all`, Johnson/AtFull/Sends/SendsWhole.lean, over five
                    facts on the key file; `free_of_parts`,
                    Johnson/AtFull/Made/MadeOfPartsIsWritten.lean).
  `made_proof_join`, `made_key_join`, `made_sized_join`: the value's `Configured` holds the written
                    three plans of each file and the written sizes. By its definition.
  `madeAt_at_full`  `madeAt_of_arms` (Johnson/AtFull/Made/MadeAtJoinC.lean) with s₁ so paid. Eight
                    binders are left, all on the public part X, the layout file and the digest: X is
                    as at the full size (P) · hG · hA · hV · b₁ · the digest has 32 bytes ·
                    ha : armsB X = true · hc : rangeChecksOf X = some checksFull.

  `madeAt_fields`   the same under «∃ m», by m's fields: X · cfg · key · proof · the sizes · the six
                    plans · the proof file's three plans as read back · `freeOf` of what the planner
                    configured is `writtenMade` · FirstWritten · MadeWritten.

Limits. A joining: it pays none of its eight hypotheses. THAT ANY PUBLIC FILES MEET THEM IS SHOWN
NOWHERE HERE. Nothing on soundness.
-/
import Johnson.AtFull.Made.MadeAtJoinC
import Johnson.AtFull.Sends.SendsWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Model OnBytes.Model.Verify OnBytes.Model.Stages OnBytes.Params
open VerifiableInference.PlanWritten (FirstWritten MadeWritten proofSizedFull)
open Johnson.G (keySendsFull proofSendsFull)
open VerifiableInference.PlanWritten.Joined (writtenSized writtenMade)
open VerifiableInference.Number.ByRuns (proofThree keyThree)
open Johnson.AtFull.LayoutRead (LW)
open H2K.Sizes (PubFull)
open VerifiableInference.Desc.LinkJoin (armsB)

/-- **s₁: what is sent, from the `Configured` of the written sizes and plans.** -/
theorem sends_join (cfg : ByteArray) : ∀ x, ∃ en, Johnson.G.sendsFrom (madeW x cfg) =
    .ok [keySendsFull.1, keySendsFull.2.1, keySendsFull.2.2, en, proofSendsFull.1,
      proofSendsFull.2.1, proofSendsFull.2.2] := by
  obtain ⟨En, h⟩ := Johnson.AtFull.Sends.sendsWhole_all
  exact fun x => ⟨En, h _ (free_of_parts recordLines x cfg writtenSized _ _ _ _ _ _ _)⟩

/-- hm: the three plans of the proof file in the value's `Configured`. By its definition. -/
theorem made_proof_join (x : Shapes) (cfg : ByteArray) :
    (chainsAt x cfg).made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan] := rfl

/-- The three plans of the key file in the value's `Configured`. By its definition. -/
theorem made_key_join (x : Shapes) (cfg : ByteArray) :
    (chainsAt x cfg).made.key = [keyThree.A.plan, keyThree.B.plan, keyThree.C.plan] := rfl

/-- The sizes in the value's `Configured`. By its definition. -/
theorem made_sized_join (x : Shapes) (cfg : ByteArray) :
    (chainsAt x cfg).made.sized = writtenSized := rfl

/-- **`Key.madeAt` RETURNS AT A PUBLIC PART AS AT THE FULL SIZE**: eight hypotheses by field. -/
theorem madeAt_at_full {X : Public} {lay cfg : ByteArray} (P : PubFull X)
    (hG : X.G.size = 12) (hA : X.A.size = 12)
    (hV : (OnBytes.TieK.listedOf X default).map Decl.viewL = Decl.viewsFull)
    (b₁ : Plan.layoutRead lay = some LW) (h32 : cfg.size = 32) (ha : armsB X = true)
    (hc : rangeChecksOf X = some checksFull) :
    ∃ (links₀ links : Array LinkH) (sh : Plan.Shape),
      VerifiableInference.Desc.Key.madeAt X lay cfg =
        .ok ⟨{ X := X, cfg := cfg, chains := chainsAt (xOf X sh checksFull) cfg,
               built := { links := links } },
             (keySendsFull.1, keySendsFull.2.1, keySendsFull.2.2),
             (proofSendsFull.1, proofSendsFull.2.1, proofSendsFull.2.2)⟩ ∧
      linksOf X default = .ok links₀ ∧
      declareLinks links₀ X.NGr X.p4 = .ok (links, declaredFull) ∧
      links.toList.map viewOf = viewFull ∧
      Plan.shapeOfLayout X.layers.wsLay X.layers.wsLay.lk = some sh ∧
      shapesOf X (some lay) = .ok (links, xOf X sh checksFull) ∧
      FirstWritten (chainsAt (xOf X sh checksFull) cfg).proof.first ∧
      MadeWritten (chainsAt (xOf X sh checksFull) cfg).made :=
  madeAt_of_arms P hG hA hV b₁ h32 ha hc (sends_join cfg)

/-- **The same, by the fields of the value**: what the steps behind read of `m`. -/
theorem madeAt_fields {X : Public} {lay cfg : ByteArray} (P : PubFull X)
    (hG : X.G.size = 12) (hA : X.A.size = 12)
    (hV : (OnBytes.TieK.listedOf X default).map Decl.viewL = Decl.viewsFull)
    (b₁ : Plan.layoutRead lay = some LW) (h32 : cfg.size = 32) (ha : armsB X = true)
    (hc : rangeChecksOf X = some checksFull) :
    ∃ m, VerifiableInference.Desc.Key.madeAt X lay cfg = .ok m ∧
      m.p.X = X ∧ m.p.cfg = cfg ∧ m.key = keySendsFull ∧ m.proof = proofSendsFull ∧
      m.p.chains.made.sized = writtenSized ∧
      m.p.chains.made.sized.proof = proofSizedFull ∧
      m.p.chains.made.proof = [proofThree.A.plan, proofThree.B.plan, proofThree.C.plan] ∧
      m.p.chains.made.key = [keyThree.A.plan, keyThree.B.plan, keyThree.C.plan] ∧
      m.p.chains.proof.first.given.plan = proofThree.A.plan.plan ∧
      m.p.chains.proof.shared.given.plan = proofThree.B.plan.plan ∧
      m.p.chains.proof.second.given.plan = proofThree.C.plan.plan ∧
      Johnson.G.MadeFree.freeOf m.p.chains.made = writtenMade ∧
      FirstWritten m.p.chains.proof.first ∧ MadeWritten m.p.chains.made := by
  obtain ⟨_, _, sh, h, -, -, -, -, -, fw, mw⟩ := madeAt_at_full P hG hA hV b₁ h32 ha hc
  exact ⟨_, h, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    free_of_parts recordLines (xOf X sh checksFull) cfg writtenSized _ _ _ _ _ _ _, fw, mw⟩

#print axioms Johnson.AtFull.Made.sends_join
#print axioms Johnson.AtFull.Made.made_proof_join
#print axioms Johnson.AtFull.Made.made_key_join
#print axioms Johnson.AtFull.Made.made_sized_join
#print axioms Johnson.AtFull.Made.madeAt_at_full
#print axioms Johnson.AtFull.Made.madeAt_fields

end Johnson.AtFull.Made
