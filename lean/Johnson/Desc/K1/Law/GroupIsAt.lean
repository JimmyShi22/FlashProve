-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/GroupIsAt.lean: "THE OPEN LINK's CONTEXT's
GROUP IS THE PLAN's": A PUBLIC ITEM WHOSE Bool READS THAT GROUP ALONE IS LEFT BY A YES OF K1's TWO
SORTS OF LATER BLOCK (GI.50); AND OFF THE TABLE OF JOINTS' PROMISE IN FRONT IT GIVES THE BINDER hg
OF k01_later_tied (HG_of). Statements with their proofs.

OBJECT. commitAtS, so laterAt (a link's digits); IM.k1Reads (a link's reads with the quiet step).
USER. (GI.50) an arm of the field pub of FillL at such an item. (HG_of) hg of k01_later_tied
(Johnson/Desc/K1/Law/LaterOne.lean), at links := linksFull, ps := flatPlacesOf linksFull true,
k := noL l d, n := N.groupAt l.
LETTERS. i: the item; gB: its Bool on the group that the open link's context names; hM: the
meaning's pub at i is gB of that group; hgB: gB's yes at a group says that the group is n. MEANT:
other files' named items "K9.groupIs" | "K10.groupIs" at segment m, n := N.groupAt m: THEIR
Bool's TEXT HAS NOT BEEN READ HERE: that it reads the group alone (hM) is to be held against it.
Main names:
  groupOf s        the group, or nothing where no link is open
  LaterGroup B · laterGroup_commitAtS | _laterAt | _joined | _k1Reads   by commitAtS_frame
      (Johnson/Desc/K1/Law/FrameAtLater.lean: a yes turns the frame's moment and own alone) and
      QuietP's clause on the open link (PubAtLaterIndex.lean)
  pub_group_later  **GI.50**: an equation
  hg_of            **HG_of**: by inAt_pub (PubAtLaterCall.lean)
IS IT EMPTY HERE? No item with such a Bool is shown to be laid or open.
What is not claimed. Who makes the item. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.PubAtLaterCall

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open VerifiableInference.Desc.First (S ModelPart Pub Meaning Numbers)
open VerifiableInference.Desc.K13.Law (openAt)
open OnBytes.Model.Stages (LinkH)

variable {Cl Pp W : Type}

/-- The group that the open link's context names (ChainCheck.group is this, by its text); nothing
where no link is open. -/
def groupOf (s : S) : Option ℕ := s.link?.map fun L => L.check.frame.group

/-! ## 1 A later sending leaves it -/

/-- A yes of B on two rounds leaves the group that the open link's context names. -/
def LaterGroup (B : Block S Cl) : Prop :=
  ∀ s s' rs gs, rs.length = 2 → B.decide s rs gs = .ok s' → groupOf s' = groupOf s

theorem laterGroup_commitAtS (P : Par) (link moment : Nat) (arrays : Option (List Nat)) :
    LaterGroup (commitAtS P link moment arrays : Block S Cl) := by
  intro s s' rs gs h2 h
  obtain ⟨r₁, r₂, rfl⟩ := List.length_eq_two.1 h2
  obtain ⟨L, L', hL, hL', hfr, _⟩ := commitAtS_frame P link moment arrays s s' r₁ r₂ gs h
  unfold groupOf
  rw [hL, hL', Option.map_some, Option.map_some, hfr]

/-- The first member: a segment's later moment at the plan's numbers (a link's digits). -/
theorem laterGroup_laterAt (q : Params.First) (gp : _root_.Desc.Plain.GPar)
    (link piece moment : Nat) (arrays : Option (List Nat)) :
    LaterGroup (laterAt q gp link piece moment arrays : Block S Cl) :=
  laterGroup_commitAtS _ _ _ _

theorem laterGroup_joined (P : Par) (link moment : Nat) (arrays : Option (List Nat))
    (nm : String) (q : Block S Cl) (hq : QuietP q) :
    LaterGroup (Block.andThen nm (commitAtS P link moment arrays) q) := by
  intro s s' rs gs h2 h
  obtain ⟨r₁, r₂, rfl⟩ := List.length_eq_two.1 h2
  obtain ⟨s₁, gs₁, rs₂, gs₂, h1, h3⟩ := joined_yes P link moment arrays nm q s s' r₁ r₂ gs h
  have e : groupOf s' = groupOf s₁ := by
    unfold groupOf
    rw [(hq _ _ _ _ h3).2.2.2.1]
  exact e.trans (laterGroup_commitAtS P link moment arrays s s₁ _ gs₁ rfl h1)

/-- The second member: the reads' place's joined block. -/
theorem laterGroup_k1Reads (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : Nat) (X : LinkH) (pr : Nat)
    (reads : Option (List Nat)) : LaterGroup (IM.k1Reads Z G l X pr reads) :=
  laterGroup_joined _ _ _ _ _ _ (quietP_orLoud _ _ _ G l X _)

/-! ## 2 A public item whose Bool reads that group alone -/

/-- **GI.50**: such an item over the block's own yes: an equation. -/
theorem pub_group_later (pub : Pub → Pp × S → Bool) (i : Pub) (gB : Option ℕ → Bool)
    (hM : ∀ a, pub i a = gB (groupOf a.2)) {B : Block S Cl} (hB : LaterGroup B) (x x' : Pp × S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (h2 : rs.length = 2)
    (h : B.decide x.2 rs gs = .ok x'.2) : pub i x' = pub i x := by
  rw [hM, hM, hB _ _ _ _ h2 h]

/-- **HG_of: the top's binder hg OFF THE PROMISE IN FRONT**: where such an item is asked in front of
block k, and its Bool's yes at a group says that the group is n. -/
theorem hg_of (N : Numbers) (Mg : Meaning Pp W) (links : List ModelPart) (ps : List Place) (k : ℕ)
    (i : Pub) (gB : Option ℕ → Bool) (n : ℕ) (hgB : ∀ g, gB (some g) = true → g = n)
    (hM : ∀ a, Mg.pub i a = gB (groupOf a.2))
    (hi : i ∈ (First.pubSets Mg.more links ps)[k]?.getD [] ++
      First.pubOfItems (openAt links ps k)) (z : Pp) :
    ∀ (s : S) y, InAt N Mg links ps k (z, s) y → ∀ L, s.link? = some L →
      L.check.frame.group = n := by
  intro s y hIn L hL
  have h0 := inAt_pub hIn i hi
  rw [hM] at h0
  refine hgB _ ?_
  have e : groupOf s = some L.check.frame.group := by
    unfold groupOf
    rw [hL, Option.map_some]
  rw [← e]
  exact h0

end VerifiableInference.Desc.K1
