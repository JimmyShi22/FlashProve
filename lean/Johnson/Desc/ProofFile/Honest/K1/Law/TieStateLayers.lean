-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/TieStateLayers.lean: TieStateS
(Johnson/Desc/ProofFile/Honest/K1/Law/TieShare.lean), THE PUBLIC HALF OF THE PREMISES OF THE SHARE
AT THE ITEM "tie m", AT A LAYERS' SEGMENT: FROM THE MEMBER's OWN ACCEPT AND ONE PREMISE FROM THE
PAIR. One definition of a premise's form, one statement and its proof.

  OwnHeardS          from the pair and the member's own step: what the state behind holds as heard
                     by the layers' own rounds is a return of the layers' plain hearing hearFl
                     (OnBytes/Desc/First/K4/Plain.lean) at the plan hp and the group g, at public
                     numbers whose list of matrices has the sizes of the plan's
  tieStateS_layers   under which block the member is (hblk) · which block its quiet half is (hquiet)
                     · the plan's list of matrices has the sizes' shapes (hShape) · OwnHeardS:
                     TieStateS L Said b m nR at nR := the plan's number of reads

THE ROAD is that of Johnson/Desc/ProofFile/Honest/K1/Law/TieStateHead.lean as far as the quiet
block's accept; there layers_ok and closed_ok (Johnson/Desc/K8/ReadsQuietLaws.lean): the record
behind is the plan's with its list closed at the tables that the state holds as heard. THAT THESE
TABLES LIE (TablesLie) DOES NOT COME OF THE MEMBER's ACCEPT: the verifier's own guard there
(Order.orderOk, Johnson/Desc/First/K8/Order.lean) speaks of the link's number, of gtTree's size and
of arrays fixed in front of the draw. It comes of tablesLie_hear
(Johnson/HonestTrace/ReadsLayers.lean), whose premise is OwnHeardS' end.

WHO HAS MET WHAT. OwnHeardS: nobody at a thread. Its kin in the sealed library, at a state reached
by the verifier's walk, in scope: k4_heard_at_front (Johnson/Desc/First/Link/Law/K4AtFront.lean);
SameSizes at a plan that planG returns: sameSizes_plan (Johnson/HonestTrace/ReadsLayers.lean).

No witness stands in either; the run's coins stand as a binder of the threads' form alone.

THE MEMBER IS A LETTER (since […]). The blocks' class of claims Cl is a letter, and the
reads' member is a letter of the type Block S Cl, with ONE PUBLIC PREMISE: hU: it has the rounds of
the library's own block IM.k1Reads (Johnson/IMR/K1Seat.lean; typed there at Unit), carried to Cl by
Block.retype, and where it says yes that block says the same yes (Block.UnderR, step_under:
Johnson/Desc/Sound/SeatGuardChain.lean). WHY: the true chain's entry at a reads' place is not that
block: it is that block, retyped, under the seat's wrappers: k01_flat_reads
(Johnson/Desc/K1/Law/K01LawTied.lean), alone_underR (Johnson/IMR/SeatForm.lean): by these two hU is
meant to be paid there; NO FILE PAYS IT YET. Of the member the proof spends its rounds and its
decision's yes alone.

Limits. NO MEMBER OF OwnHeardS IS GIVEN, AND NO NEGATIVE TEST. It is a definition: nothing is
claimed of it, and no goal file names it. The other four premises are proved here at no letters;
hShape has been evaluated nowhere. g and m are two letters: nothing here says that m = 2 g. Nothing
on soundness, on completeness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.TieShare
import Johnson.HonestTrace.ReadsLayers
import Johnson.Desc.K1.Law.BlocksAtLater
import Johnson.Desc.K1.Law.PubAtLaterIndex
import Johnson.Desc.K8.ReadsQuietLaws
import Johnson.Desc.RunLaws
import Johnson.Desc.Sound.Gather
import Johnson.Desc.Sound.SeatGuardChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT roundsFit_len)
open VerifiableInference.Desc.K1 (joined_yes rounds_k1Reads)
open VerifiableInference.Desc.K8.ReadsQuiet (layers layers_ok closed_ok)
open OnBytes.HonestTrace (Sz ShapesFit shapesFit_congr SameSizes tablesLie_hear)
open OnBytes.Model.Layer (HPlan2)
open OnBytes.Model.Stages (LinkH)
open OnBytes.Desc.First.K4 (hearFl)
open ProofFile.Honest.FirstThread (Letters)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr' X' P Cells Tok : Type}

/-- **From the pair: what the state behind holds as heard is a return of the layers' hearing.**
Public: no witness in it. At a member behind which the state is in no layers' link it asks nothing.
A definition: a premise's form. -/
def OwnHeardS (L : Letters Bk Cl W₀ Rc Xi Tr' X' P Cells Tok MsgT)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr') X' → Prop) (b g : ℕ) (hp : HPlan2) : Prop :=
  ∀ blk, L.bs[b]? = some blk → ∀ k s μ E ds y cols s', ThrS L.thread Said b k s μ E →
    drawsFit blk.rounds ds = true → L.thread.Stepped blk k s μ E ds y cols s' →
    ∀ o, s'.own? = some o → ∃ Pl fo F t F' t', hearFl Pl hp g fo F t = some (o, F', t') ∧
      SameSizes (Pl.tails.getD g {}).mats hp.tl.mats

/-- **The public half at a layers' segment.** -/
theorem tieStateS_layers {L : Letters Bk Cl W₀ Rc Xi Tr' X' P Cells Tok MsgT}
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc Xi Tr') X' → Prop} {b m g : ℕ} {Z : ProofFile.Pub}
    {G : ProofFile.Ground} {X : LinkH} {pr : ℕ} {reads : Option (List ℕ)} {hp : HPlan2} {pl : Place}
    {blk₁ : Block S Cl} (hblk : L.bs[b]? = some blk₁)
    (hU : blk₁.UnderR ((IM.k1Reads Z G m X pr reads).retype : Block S Cl))
    (hquiet : IM.k1Quiet G m X = layers ⟨pl, hp.tl⟩) (hShape : ShapesFit hp.tl Sz.ref m)
    (hOwn : OwnHeardS L Said b g hp) : TieStateS L Said b m (hp.nU.getD 2 0) := by
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
  obtain ⟨-, rfl, -, -⟩ := closed_ok hc
  have hown : s'.own? = some own := by
    rw [e]
    exact ho
  obtain ⟨Pl, fo, F, t, F', t', hh, hm⟩ := hOwn _ hb k s μ E ds y cols s' hA hd hS own hown
  refine ⟨{ hp.tl with funClosed := true, funs := own.funs }, ?_,
    (shapesFit_congr ⟨rfl, rfl, rfl⟩ Sz.ref m).2 hShape, tablesLie_hear hh hm⟩
  rw [e]
  rfl

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.OwnHeardS
#print axioms ProofFile.Honest.K1.tieStateS_layers
