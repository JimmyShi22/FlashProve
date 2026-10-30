-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/TieStateHeadPlan.lean: TieStateP
(Johnson/Desc/ProofFile/Honest/K1/Law/TiePlanShare.lean) AT THE OUTPUT HEAD's SEGMENT: THE PUBLIC
HALF OF THE SHARE AT THE ITEM "tie 24", AT ANY SIZES. One statement and its proof. No definition. No
witness. The sister of tieStateP_layers (TieStatePlan.lean).

  tieStateP_head   tieStateS_head (Johnson/Desc/ProofFile/Honest/K1/Law/TieStateHead.lean) WITH A
                   LETTER Sz₀ FOR Sz.ref: in hShape and in the end

MADE BY PROGRAM OFF THAT FILE's TEXT: the letter for the constant at three places; the proof does
not read the sizes. That file keeps its own. BY HAND: TieStateP's last conjunct (tl.NM ≤
tl.gtTree.size) IS PAID WITHOUT A NEW PREMISE, off the quiet step's own guard of order at every yes:
closed_ok, orderOk_fixed (Johnson/Desc/K8/ReadsQuietLaws.lean). hquiet is paid by the library's
quiet_of_kind (Johnson/Desc/K1/Law/OwnHeldAtSendings.lean) where the built link has the kind 2.

Limits. Those of TieStateHead.lean: hblk, hU, hquiet and hShape are premises. A law under "Stepped".
Nothing on soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.TieStateHead
import Johnson.Desc.ProofFile.Honest.K1.Law.TiePlanShare

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT roundsFit_len)
open VerifiableInference.Desc.K1 (joined_yes rounds_k1Reads)
open VerifiableInference.Desc.K8.ReadsQuiet (PH head head_ok closed_ok orderOk_fixed)
open OnBytes.HonestTrace (Sz ShapesFit shapesFit_congr tablesLie_head)
open OnBytes.Model.Stages (LinkH)
open ProofFile.Honest.FirstThread (Letters)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr' X' P Cells Tok : Type}

/-- **The public half at the output head's segment, at sizes Sz₀.** -/
theorem tieStateP_head {Sz₀ : Sz} {L : Letters Bk Cl W₀ Rc Xi Tr' X' P Cells Tok MsgT}
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr') X' → Prop} {b : ℕ} {Z : ProofFile.Pub}
    {G : ProofFile.Ground} {X : LinkH} {pr : ℕ} {reads : Option (List ℕ)} {Ph : PH}
    {blk₁ : Block S Cl} (hblk : L.bs[b]? = some blk₁)
    (hU : blk₁.UnderR ((IM.k1Reads Z G 24 X pr reads).retype : Block S Cl))
    (hquiet : IM.k1Quiet G 24 X = head Ph) (hShape : ShapesFit Ph.hp.tl Sz₀ 24) :
    TieStateP L Said Sz₀ b 24 (Ph.hp.nU.getD 2 0) := by
  intro blk hb k s μ E ds y cols s' _ _ hS
  obtain rfl : blk₁ = blk := Option.some.inj (hblk.symm.trans hb)
  unfold Thread.Stepped at hS
  obtain ⟨hfit, -, hdec, -⟩ := Block.step_ok.1 (step_under hU hS.2)
  have hlen : ((roundsOf y.1).map noDigest).length = 2 := by
    rw [List.length_map, roundsFit_len _ _ hfit]
    exact rounds_k1Reads Z G 24 X pr reads
  obtain ⟨r₁, r₂, hr⟩ := List.length_eq_two.1 hlen
  rw [hr] at hdec
  have hdec : (IM.k1Reads Z G 24 X pr reads).decide s [r₁, r₂] _ = .ok s' := hdec
  obtain ⟨s₁, gs₁, rs₂, gs₂, -, h3⟩ :=
    joined_yes _ _ _ _ _ (IM.k1Quiet G 24 X) s s' r₁ r₂ _ hdec
  rw [hquiet] at h3
  obtain ⟨a, cov, x, t, tl', -, hop, -, -, ht, hc, rfl⟩ := head_ok h3
  obtain ⟨-, rfl, -, hord⟩ := closed_ok hc
  refine ⟨{ Ph.hp.tl with funClosed := true, funs := t.funs }, ?_,
    (shapesFit_congr ⟨rfl, rfl, rfl⟩ Sz₀ 24).2 hShape, tablesLie_head ht,
    (orderOk_fixed hord).1.ge⟩
  show (if a.opened then some _ else none) = some _
  rw [if_pos hop]


end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.tieStateP_head
