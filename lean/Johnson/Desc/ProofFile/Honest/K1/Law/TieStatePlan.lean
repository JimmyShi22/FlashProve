-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/TieStatePlan.lean: TieStateP
(Johnson/Desc/ProofFile/Honest/K1/Law/TiePlanShare.lean) AT A LAYERS' SEGMENT: THE PUBLIC HALF OF
THE SHARE AT THE ITEM "tie m", AT ANY SIZES. One statement and its proof. No definition. No witness.

  tieStateP_layers   tieStateS_layers (Johnson/Desc/ProofFile/Honest/K1/Law/TieStateLayers.lean)
                     WITH A LETTER Sz₀ FOR Sz.ref: in hShape and in the end

MADE BY PROGRAM OFF THAT FILE's TEXT: the letter for the constant at three places; the proof does
not read the sizes. That file keeps its own. BY HAND: TieStateP's last conjunct (tl.NM ≤
tl.gtTree.size) IS PAID WITHOUT A NEW PREMISE, off the quiet step's own guard of order at every yes:
closed_ok, orderOk_fixed (Johnson/Desc/K8/ReadsQuietLaws.lean).

THE MEMBER IS A LETTER (since […]). The blocks' class of claims Cl is a letter, and the
reads' member is a letter of the type Block S Cl, with ONE PUBLIC PREMISE: hU: it has the rounds of
the library's own block IM.k1Reads (Johnson/IMR/K1Seat.lean; typed there at Unit), carried to Cl by
Block.retype, and where it says yes that block says the same yes (Block.UnderR, step_under:
Johnson/Desc/Sound/SeatGuardChain.lean). WHY: the true chain's entry at a reads' place is not that
block: it is that block, retyped, under the seat's wrappers: k01_flat_reads
(Johnson/Desc/K1/Law/K01LawTied.lean), alone_underR (Johnson/IMR/SeatForm.lean): by these two hU is
meant to be paid there; NO FILE PAYS IT YET. Of the member the proof spends its rounds and its
decision's yes alone.

Limits. Those of TieStateLayers.lean: hU, hquiet, hShape and OwnHeardS are premises. A law under
"Stepped". Nothing on soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.TieStateLayers
import Johnson.Desc.ProofFile.Honest.K1.Law.TiePlanShare
import Johnson.Desc.Sound.SeatGuardChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT roundsFit_len)
open VerifiableInference.Desc.K1 (joined_yes rounds_k1Reads)
open VerifiableInference.Desc.K8.ReadsQuiet (layers layers_ok closed_ok orderOk_fixed)
open OnBytes.HonestTrace (Sz ShapesFit shapesFit_congr SameSizes tablesLie_hear)
open OnBytes.Model.Layer (HPlan2)
open OnBytes.Model.Stages (LinkH)
open ProofFile.Honest.FirstThread (Letters)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr' X' P Cells Tok : Type}

/-- **The public half at a layers' segment, at sizes Sz₀.** -/
theorem tieStateP_layers {Sz₀ : Sz} {L : Letters Bk Cl W₀ Rc Xi Tr' X' P Cells Tok MsgT}
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr') X' → Prop} {b m g : ℕ} {Z : ProofFile.Pub}
    {G : ProofFile.Ground} {X : LinkH} {pr : ℕ} {reads : Option (List ℕ)} {hp : HPlan2} {pl : Place}
    {blk₁ : Block S Cl} (hblk : L.bs[b]? = some blk₁)
    (hU : blk₁.UnderR ((IM.k1Reads Z G m X pr reads).retype : Block S Cl))
    (hquiet : IM.k1Quiet G m X = layers ⟨pl, hp.tl⟩) (hShape : ShapesFit hp.tl Sz₀ m)
    (hOwn : OwnHeardS L Said b g hp) : TieStateP L Said Sz₀ b m (hp.nU.getD 2 0) := by
  intro blk hb k s μ E ds y cols s' hA hd hS
  obtain rfl : blk₁ = blk := Option.some.inj (hblk.symm.trans hb)
  have hS' := hS
  unfold Thread.Stepped at hS'
  obtain ⟨hfit, -, hdec, -⟩ := Block.step_ok.1 (step_under hU hS'.2)
  have hlen : ((roundsOf y.1).map noDigest).length = 2 := by
    rw [List.length_map, roundsFit_len _ _ hfit]
    exact rounds_k1Reads Z G m X pr reads
  obtain ⟨r₁, r₂, hr⟩ := List.length_eq_two.1 hlen
  rw [hr] at hdec
  have hdec : (IM.k1Reads Z G m X pr reads).decide s [r₁, r₂] _ = .ok s' := hdec
  obtain ⟨s₁, gs₁, rs₂, gs₂, -, h3⟩ :=
    joined_yes _ _ _ _ _ (IM.k1Quiet G m X) s s' r₁ r₂ _ hdec
  rw [hquiet] at h3
  obtain ⟨a, own, tl', -, ho, hc, e⟩ := layers_ok h3
  obtain ⟨-, rfl, -, hord⟩ := closed_ok hc
  have hown : s'.own? = some own := by
    rw [e]
    exact ho
  obtain ⟨Pl, fo, F, t, F', t', hh, hm⟩ := hOwn _ hb k s μ E ds y cols s' hA hd hS own hown
  refine ⟨{ hp.tl with funClosed := true, funs := own.funs }, ?_,
    (shapesFit_congr ⟨rfl, rfl, rfl⟩ Sz₀ m).2 hShape, tablesLie_hear hh hm,
    (orderOk_fixed hord).1.ge⟩
  rw [e]
  rfl

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.tieStateP_layers
