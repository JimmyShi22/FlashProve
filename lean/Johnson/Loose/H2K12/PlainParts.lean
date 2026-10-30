-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.Desc.ProofFile.PlanPlain
import OnBytes.Model.Fit.PlanTestsTop
import Johnson.Desc.Ok.PlanWritten.PublicAtCutMore
import Johnson.Loose.H2K12.LinksKeepAtFacts
import Johnson.Desc.K12.Law.FreeOfMade
/-
Johnson/Loose/H2K12/PlainParts.lean:
WHAT THE LIBRARY's TOPS SPEND OF THE PLANNER's YES, PAID ON THE PLAIN ROAD: the proof file's seated
description takes its public part's «made» from PlanPlain.lean's twins (ProofFile.Plain.planned o ·
ProofFile.PlainG.madeOf o), not from the library's Verify.planned · madeOf. o, THE SECOND HASH FUNCTION,
IS A LETTER THROUGHOUT. ON THE PLAN ALONE. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
WHAT STANDS AGAINST IT. (1) IT STANDS ON TWO OTHER FILES:
Johnson/Desc/Ok/PlanWritten/PublicAtCut.lean | PublicAtCutMore.lean (PublicCut ·
publicCut_of_O · cut_layout | _reads | _G | _H | _A), and on K12's files' own twins of thirteen of
the library's lemmas (H2K12/LinksKeepAtFacts.lean). (2) «THE MADE IS THE MADE» IS NOT PROVED, AND AS
AN EQUATION OF VALUES IT IS FALSE wherever both roads return [by reading]: the record's field built
keeps every link's routine, which the plain road lays as one that refuses at once; and the plain
road lays a constant in the configuration's digest's place. (3) The statements are the library's
ones' at the twins' names, their proofs the library's proofs line for line: they fall when the
library's six take the links' maker as a parameter. (4) At no o is the plain road shown to return.
  plain_shapesOf_sub · plain_chainsOf_parts · plain_parts     the twins' texts read back:
      planned_parts' ten conjuncts (OnBytes/Model/Fit/PlannedParts.lean), with publicOfO o in
      publicOf's place and ProofFile.Plain.shapesOf in shapesOf's.
  linkFacts_of_cut · link_keepsO     AT EVERY o: publicOfO o pol KL layout = .ok X gives the
      library's link_keeps' conclusion at X: by the predicate PublicCut and the thirteen.
  small_of_plain · spelt_of_plain     every entry of the six made plans is Small; the names are in
      order: by the library's lower lemmas (Params.made_small · the caps).
  speltRoots_of_plain · planLike_of_plain     ProofFile.Plain.planned o pol KL layout = .ok m.p gives
      PlanLike m: AT EVERY o: NO OTHER PREMISE. (That the plain road's maker's yes gives the first
      premise, and that the public part's «made» is that maker's return, are the seat's files' own
      lemmas: Johnson/Desc/ProofFile/Law/MakerPublic.lean: madeOf_planned · pubBy_made: called by
      whoever stands over the seat.)
-/
set_option autoImplicit false
namespace H2K.Made
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Model.Verify Johnson.G.OfPlan
open Fo.BatRows (bindE_ok)
open Fo.Pub (ite_unit_ok)

/-- The sub-proofs' record in the shapes (the library's lemma of this statement is private). -/
theorem shapesWith_sub' {X : Public} {links : List Params.ReqLink}
    {layout : Params.ReqLayout} {ids : List Nat} {s : Params.Shapes}
    (h : shapesWith X links layout ids = .ok s) : s.sub = subproofsWith X links := by
  unfold shapesWith at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := bindE_ok h
  have h := ite_unit_ok h
  have h := ite_unit_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain rfl := Except.ok.inj h
  rfl

theorem plain_shapesOf_sub {X : Public} {lay : Option ByteArray} {links : Array Stages.LinkH}
    {shapes : Params.Shapes} (h : ProofFile.Plain.shapesOf X lay = .ok (links, shapes)) :
    ∃ declared file rl layout,
      Plan.reqFrame declared file X.P.frame.answers = some (rl, layout) ∧
        shapes.sub = subproofsWith X rl := by
  unfold ProofFile.Plain.shapesOf at h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨⟨links', declared⟩, _, h⟩ := bindE_ok h
  dsimp only at h
  split at h
  · obtain ⟨file, _, h⟩ := bindE_ok h
    split at h
    · rename_i x hx
      obtain ⟨⟨reqLinks, layout⟩, ex, h⟩ := bindE_ok h
      have e0 : x = (reqLinks, layout) := Except.ok.inj ex
      dsimp only at h
      obtain ⟨s, hs, h⟩ := bindE_ok h
      have e : (links', s) = (links, shapes) := Except.ok.inj h
      rw [← (Prod.mk.inj e).2]
      exact ⟨declared, file, reqLinks, layout, hx.trans (congrArg some e0), shapesWith_sub' hs⟩
    · obtain ⟨_, e, _⟩ := bindE_ok h
      cases e
  · obtain ⟨_, e, _⟩ := bindE_ok h
    cases e

theorem plain_chainsOf_parts {X : Public} {lay : Option ByteArray} {c : ByteArray} {ch : Chains}
    (h : ProofFile.Plain.chainsOf X lay c = .ok ch) :
    ∃ links shapes, ProofFile.Plain.shapesOf X lay = .ok (links, shapes) ∧
      Params.configure X.P.frame shapes c 0 = .ok ch.made ∧
      Params.KeyChains.read ch.made.keyOneTime ch.made.keyShared ch.made.keySecond = some ch.key ∧
      Params.ProofChains.read ch.made.first ch.made.shared ch.made.second = some ch.proof := by
  unfold ProofFile.Plain.chainsOf at h
  obtain ⟨⟨links, shapes⟩, hs, h⟩ := bindE_ok h
  dsimp only at h
  obtain ⟨z, _, h⟩ := bindE_ok h
  obtain ⟨u, _, h⟩ := bindE_ok h
  obtain ⟨made, hm, h⟩ := bindE_ok h
  split at h
  · rename_i key link proof hK hL hP
    cases h
    exact ⟨links, shapes, hs, hm, hK, hP⟩
  · cases h

/-- **What the plain road's planner returns, taken apart by name**: planned_parts' conjuncts. -/
theorem plain_parts {o : Nat → ByteArray → ByteArray} {pol KL : ByteArray}
    {layout : Option ByteArray} {p : Verify.Planned}
    (h : ProofFile.Plain.planned o pol KL layout = .ok p) :
    ∃ links shapes rest declared file rl lay,
      VerifiableInference.PlanWritten.publicOfO o pol KL layout = .ok p.X ∧
      Params.readLines pol = .ok (p.X.P.frame, rest) ∧
      ProofFile.Plain.shapesOf p.X layout = .ok (links, shapes) ∧
      shapes.sub.plan = linkRounds p.X ∧
      shapes.sub.afterLinks = pure () ∧
      Params.configure p.X.P.frame shapes p.cfg 0 = .ok p.chains.made ∧
      Params.KeyChains.read p.chains.made.keyOneTime p.chains.made.keyShared
        p.chains.made.keySecond = some p.chains.key ∧
      Params.ProofChains.read p.chains.made.first p.chains.made.shared p.chains.made.second =
        some p.chains.proof ∧
      Plan.reqFrame declared file p.X.P.frame.answers = some (rl, lay) ∧
      shapes.sub = subproofsWith p.X rl := by
  unfold ProofFile.Plain.planned at h
  obtain ⟨X, hX, h⟩ := bindE_ok h
  obtain ⟨ch, hc, h⟩ := bindE_ok h
  obtain ⟨b, _, h⟩ := bindE_ok h
  cases h
  obtain ⟨links, shapes, hs, hm, hK, hP⟩ := plain_chainsOf_parts hc
  obtain ⟨rest, hr⟩ := polScan_frame (VerifiableInference.PlanWritten.publicOfO_scan hX)
  obtain ⟨declared, file, rl, lay, hf, e⟩ := plain_shapesOf_sub hs
  exact ⟨links, shapes, rest, declared, file, rl, lay, hX, hr, hs, by rw [e]; rfl, by rw [e]; rfl,
    hm, hK, hP, hf, e⟩

/-- The five facts follow from the predicate on the public record that publicOf and publicOfO o pay
alike (Johnson/Desc/Ok/PlanWritten/PublicAtCut.lean | PublicAtCutMore.lean): its
five readbacks, by name. -/
theorem linkFacts_of_cut {pol KL : ByteArray} {X : Public}
    (C : VerifiableInference.PlanWritten.PublicCut pol KL X) : LinkFacts pol KL X :=
  ⟨VerifiableInference.PlanWritten.cut_layout C, VerifiableInference.PlanWritten.cut_reads C,
    VerifiableInference.PlanWritten.cut_G C, VerifiableInference.PlanWritten.cut_H C,
    VerifiableInference.PlanWritten.cut_A C⟩

/-- AT EVERY o: the sub-proofs' rounds at what publicOfO o returns keep every entry small: the
library's link_keeps' conclusion. -/
theorem link_keepsO {o : Nat → ByteArray → ByteArray} {pol KL : ByteArray}
    {layout : Option ByteArray} {X : Public}
    (h : VerifiableInference.PlanWritten.publicOfO o pol KL layout = .ok X) {s : Params.Setting}
    (S : Params.SetCap s) (link moment : Nat) :
    Params.Keeps s Params.Small (linkRounds X link moment) :=
  link_keeps' (linkFacts_of_cut (VerifiableInference.PlanWritten.publicCut_of_O h)) S link moment

/-- **Every entry of the six made plans is Small**, on the plain road. -/
theorem small_of_plain {o : Nat → ByteArray → ByteArray} {pol KL : ByteArray}
    {layout : Option ByteArray} {p : Verify.Planned}
    (h : ProofFile.Plain.planned o pol KL layout = .ok p) :
    ∀ P ∈ p.chains.made.key ++ p.chains.made.proof, ∀ r ∈ P.rounds, Params.Small r.entry := by
  obtain ⟨links, shapes, rest, declared, file, rl, lay, hX, hL, _, h1, h2, hc, _, _, hrf, hsub⟩ :=
    plain_parts h
  have LC := Params.linesCap_of_read hL
  have hz := (Params.configure_plans hc).1
  have hcl : Params.TreeClassCap shapes.sub.links := by
    rw [hsub]
    exact subproofsWith_class p.X hrf
  have S := Params.setCap_of_read hL
  exact Params.made_small hc S (Params.reqCap_of_sized hz LC hcl) (Params.keyCap_of_sized hz LC)
    { plan := fun l m => by rw [h1]; exact link_keepsO hX S l m
      after := by rw [h2]; exact Params.keeps_pure trivial }

theorem spelt_of_plain {o : Nat → ByteArray → ByteArray} {pol KL : ByteArray}
    {layout : Option ByteArray} {p : Verify.Planned}
    (h : ProofFile.Plain.planned o pol KL layout = .ok p) :
    ∀ P ∈ p.chains.made.key ++ p.chains.made.proof, Spelt P :=
  fun P hP => spelt_of_small (small_of_plain h P hP)

theorem speltRoots_of_plain {o : Nat → ByteArray → ByteArray} {pol KL : ByteArray}
    {layout : Option ByteArray} {m : Made}
    (h : ProofFile.Plain.planned o pol KL layout = .ok m.p) :
    ∀ P ∈ m.p.chains.made.proof, SpeltRoots P := by
  intro P hP
  refine ⟨spelt_of_plain h P (List.mem_append_right _ hP), fun e he => ?_⟩
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 (show e ∈ P.rounds.map (·.entry) from he)
  have := (small_of_plain h P (List.mem_append_right _ hP) r hr).2.1
  exact Nat.lt_of_le_of_lt this (by decide)

/-- On the plain road the plans as read back are like the made plans' entries. -/
theorem planLike_of_plain {o : Nat → ByteArray → ByteArray} {pol KL : ByteArray}
    {layout : Option ByteArray} {m : Made}
    (h : ProofFile.Plain.planned o pol KL layout = .ok m.p) : PlanLike m := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hc, _, hP, _, _⟩ := plain_parts h
  exact planLike_of_norm m hc hP (speltRoots_of_plain h)

end H2K.Made

#print axioms H2K.Made.plain_parts
#print axioms H2K.Made.link_keepsO
#print axioms H2K.Made.small_of_plain
#print axioms H2K.Made.planLike_of_plain
