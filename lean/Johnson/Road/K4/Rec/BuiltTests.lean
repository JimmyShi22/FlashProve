-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Rec/BuiltTests.lean: WHAT THE MAKER OF THE BUILT SEGMENTS HAS TESTED, CUT OUT OF ITS
TEXT (buildLinksH, OnBytes/Model/StagesLinks.lean): wherever the plain road returns the public
part Z, three of buildLinksH's own tests have accepted at Z's built segments and at the first
chain's parameters Z.first. Five statements with their proofs. No scope, no written value.

  `buildLinksH_cut`: where buildLinksH returns B: declareLinks returned (B.links, declared) for
    some declared; heldAgainst declared p and linksFit B.links ... accepted. The walk is that of
    Fo.built_cut (OnBytes/Tie/Pv/Lookup/Ends/FoBuiltCut.lean), which keeps other tests.
  `linkLaid_ns`: linkLaid's first test: X.ns + shape.answers ≤ maskRow.
  `linksFit_ns`: so, where linksFit accepts, at EVERY segment X of the list: the code of the
    segments' mask rows is there, and X.ns + shape.answers ≤ its ell.
  `plain_cut`: buildLinksH_cut at the plain road's public part.
  **`built_ns_le`**: where pubPlain o returns Z, at every built segment X: there is
    zk with Z.first.codes.mask[Z.first.shape.maskCode]? = some zk and
    X.ns + Z.first.shape.answers ≤ zk.ell. Premises: the return (an opening's field pub) · hX.
WHO CALLS: the bound on a layers' plan's number of slots (with built_ns_plain,
Johnson/Road/K4/Riders/BuiltNs.lean, and the written codes); the named test readsP (heldAgainst).
Limits. Tests on public data: at no meaning. K04_law, the law of K4's sub-protocol itself, IS NOT
PROVED. Nothing on soundness.


-/
import Johnson.Road.K4.Riders.BuiltNs
import OnBytes.Tie.Pv.Lookup.Ends.FoBuiltCut
import OnBytes.Tie.Pv.Lookup.Ends.FoDeclMoments

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Rec
open OnBytes OnBytes.Params OnBytes.Plan OnBytes.Model OnBytes.Model.Stages
open Fo.ReqF (forIn_done)

/-- **Three of buildLinksH's tests.** -/
theorem buildLinksH_cut {links : Array LinkH} {NGr : Nat} {p4 : Bool} {wsLay : WsLay}
    {p : Params.First} {B : LinksH} (h : buildLinksH links NGr p4 wsLay p = .ok B) :
    ∃ declared, declareLinks links NGr p4 = .ok (B.links, declared) ∧
      heldAgainst declared p = .ok () ∧
      linksFit B.links p.codes p.shape p.layout p.lin.kCol = .ok () := by
  unfold buildLinksH at h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨⟨named, declared⟩, h3, h⟩ := exc_bind h
  dsimp only at h
  obtain ⟨⟨⟩, h4, h⟩ := exc_bind h
  obtain ⟨⟨⟩, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨⟨⟩, _, h⟩ := exc_bind h
  replace h := exc_guard h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨⟨⟩, h10, h⟩ := exc_bind h
  obtain ⟨⟨⟩, _, h⟩ := exc_bind h
  cases h
  exact ⟨declared, h3, h4, h10⟩

/-- linkLaid's first test. -/
theorem linkLaid_ns {shape : ReqShape} {layout : ReqLayout} {maskRow l : Nat} {X : LinkH}
    (h : linkLaid shape layout maskRow l X = .ok ()) : X.ns + shape.answers ≤ maskRow := by
  unfold linkLaid at h
  have k := exc_guard_not h
  omega

/-- **Where linksFit accepts: every segment's scalars and the answers' pads have room.** -/
theorem linksFit_ns {links : Array LinkH} {codes : Codes} {shape : ReqShape}
    {layout : ReqLayout} {kCol : Nat} (h : linksFit links codes shape layout kCol = .ok ())
    {l : Nat} {X : LinkH} (hX : links[l]? = some X) :
    ∃ zk, codes.mask[shape.maskCode]? = some zk ∧ X.ns + shape.answers ≤ zk.ell := by
  unfold linksFit at h
  replace h := exc_guard h
  obtain ⟨_, _, h⟩ := exc_bind h
  unfold linksLaid at h
  split at h
  · rename_i zk hz
    try dsimp only at h
    obtain ⟨_, h, _⟩ := exc_bind h
    have stepL : ∀ (done : List (LinkH × Nat)) (a : LinkH × Nat) (s : PUnit)
        (s' : ForInStep PUnit),
        (∀ b ∈ done, linkLaid shape layout zk.ell b.2 b.1 = .ok ()) →
        (do
          linkLaid shape layout zk.ell a.2 a.1
          pure (ForInStep.yield PUnit.unit) : Except String (ForInStep PUnit)) = .ok s' →
        ∃ t, s' = .yield t ∧
          ∀ b ∈ done ++ [a], linkLaid shape layout zk.ell b.2 b.1 = .ok () := by
      intro done a s s' Is hs
      obtain ⟨⟨⟩, h1, hs⟩ := exc_bind hs
      refine ⟨_, (Except.ok.inj hs).symm, fun b hb => ?_⟩
      rcases List.mem_append.1 hb with hb | hb
      · exact Is b hb
      · obtain rfl : b = a := by simpa using hb
        exact h1
    have I := forIn_done _
      (fun (done : List (LinkH × Nat)) (_ : PUnit) =>
        ∀ b ∈ done, linkLaid shape layout zk.ell b.2 b.1 = .ok ())
      stepL _ [] _ _ (fun _ ha => by cases ha) h
    rw [List.nil_append] at I
    have hm : (links.toList.zipIdx)[l]? = some (X, l) := by
      rw [List.getElem?_zipIdx, Array.getElem?_toList, hX]
      simp
    exact ⟨zk, hz, linkLaid_ns (I (X, l) (List.mem_of_getElem? hm))⟩
  · cases h

/-- The cut, at the plain road's public part. -/
theorem plain_cut {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) :
    ∃ l₀ declared, ProofFile.Plain.linksPlain Z.p.X = .ok l₀ ∧
      declareLinks l₀ Z.p.X.NGr Z.p.X.p4 = .ok (Z.p.built.links, declared) ∧
      heldAgainst declared Z.first = .ok () ∧
      linksFit Z.p.built.links Z.first.codes Z.first.shape Z.first.layout Z.first.lin.kCol =
        .ok () := by
  have hB : ProofFile.Plain.builtOf Z.p.X Z.p.chains = .ok Z.p.built :=
    IM.planned_built (ProofFile.Law.madeOf_planned (ProofFile.Law.pubBy_made
            (show ProofFile.pubBy (ProofFile.PlainG.madeOf o) ProofFile.plainStarts pol lay KL = .ok Z from hZ)))
  obtain ⟨l₀, h₀, hB⟩ := IM.plain_built hB
  obtain ⟨declared, h1, h2, h3⟩ := buildLinksH_cut hB
  exact ⟨l₀, declared, h₀, h1, h2, h3⟩

/-- **Every built segment's number of slots, with the answers' pads, is within the mask row.** -/
theorem built_ns_le {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (hZ : ProofFile.pubPlain o pol lay KL = .ok Z) {l : Nat} {X : LinkH}
    (hX : Z.p.built.links[l]? = some X) :
    ∃ zk, Z.first.codes.mask[Z.first.shape.maskCode]? = some zk ∧
      X.ns + Z.first.shape.answers ≤ zk.ell := by
  obtain ⟨_, _, _, _, _, h3⟩ := plain_cut hZ
  exact linksFit_ns h3 hX

end OnBytes.Road.K4.Rec

#print axioms OnBytes.Road.K4.Rec.buildLinksH_cut
#print axioms OnBytes.Road.K4.Rec.linkLaid_ns
#print axioms OnBytes.Road.K4.Rec.linksFit_ns
#print axioms OnBytes.Road.K4.Rec.plain_cut
#print axioms OnBytes.Road.K4.Rec.built_ns_le
