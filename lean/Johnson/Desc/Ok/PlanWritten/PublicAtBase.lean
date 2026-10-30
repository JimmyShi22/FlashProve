-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Ok/PlanWritten/PublicAtBase.lean: the library's lemmas that open the text of the public
part of a stage (`publicOf`, OnBytes/Model/VerifyPublic.lean) or of the attention sub-proofs' plans
(`Attention.config`, OnBytes/Model/AttentionConfig.lean), each once more at the texts that take the
second hash function as an argument o (`publicOfO o`, `Attention.configO o`,
Johnson/Desc/Ok/PlanWritten/PublicAt.lean).

Why. A law of the library on what `publicOf` returns rests, at its foot, on a lemma that unfolds
that text and follows its steps. At an argument o other than the second hash function the library's
lemma does not apply. The two texts differ in the argument alone, so the same proof goes through.

What is here. For each such lemma a twin: the statement and the proof are the library's, line for
line, with `publicOfO o` for `publicOf` and `Attention.configO o` for `Attention.config`, and the
twin's name for a lemma of this kind that the proof calls. A twin's name is the source file's name,
a dot, and the lemma's name with an O behind it. The twins were made by a program from the library's
text. Four lemmas of this kind have their twins elsewhere: `publicOfO_scan`
(Johnson/Desc/Ok/PlanWritten/PublicAtLaws.lean); `publicOfO_cut`, `publicOfO_reads`, `configO_at`
(Johnson/Desc/Ok/PlanWritten/PublicAtCut.lean).

The twins, each behind its source file: OnBytes/Flat/CoveredJoin.lean: `CoveredJoin.publicOf_VO`;
OnBytes/Tie/Pv/Lookup/Ends/FoMadePub.lean: `FoMadePub.publicOf_headLayoutO`;
OnBytes/Tie/Pv/Lookup/Ends/FoLayerMu.lean: `FoLayerMu.publicOf_layersO`;
OnBytes/Tie/Pv/Lookup/Ends/FoPublicAFill.lean: `FoPublicAFill.public_scO`;
OnBytes/Tie/Pv/Lookup/Ends/FoPublicAMats.lean: `FoPublicAMats.config_NAsO`;
OnBytes/Tie/Pv/Lookup/Ends/FoPlaneMatPubG.lean: `FoPlaneMatPubG.public_tailsO`;
OnBytes/Tie/PlanAtPolicy.lean: `PlanAtPolicy.publicOf_withPolO`, `PlanAtPolicy.publicOf_hSO`;
Johnson/Road/HeadPub.lean: `HeadPub.public_partsO`; Johnson/Road/HeadL5Grp.lean:
`HeadL5Grp.config_groupsO`, `HeadL5Grp.scalesBoth_of_publicO`, `HeadL5Grp.groups_of_publicO`;
Johnson/Road/HeadLaid.lean: `HeadLaid.layout_of_publicO`; Johnson/Road/HeadMade.lean:
`HeadMade.publicH_of_publicO`; Johnson/Road/HeadDict.lean: `HeadDict.public_plansO`;
Johnson/Thin/Link/PlanV.lean: `PlanV.publicOf_VO`; Johnson/Flat/SizesPlanned.lean:
`SizesPlanned.publicOf_windowO`; Johnson/Top/ExitBuild.lean: `ExitBuild.publicOf_headO`.

Where a proof of the library calls a macro that is local to its file, the macro is written out;
where it calls a private lemma of its file, the library's public lemma with the same statement is
called (`exc_bind`, OnBytes/Params/ConfigureLaws.lean); an alternative of a proof that is never run
is struck, since the linter reports it here.

The statements are tools: they hold of all public files and all arguments o, and no description of
the protocol is named. What of OnBytes/Model/ is used: what the library's lemmas use.

Limits. Which lemmas open one of the two texts was found by a search for "unfold" with the text's
name; a proof that opens a text in another way is not found so. Two more lemmas of this kind stand
in files that import the goals, and have no twin here. A law that only hands the premise "`publicOf`
returns X" down to such a lemma has no twin here. Nothing on soundness.
-/
import Johnson.Desc.Ok.PlanWritten.PublicAtCut
import OnBytes.Flat.CoveredJoin
import OnBytes.Tie.Pv.Lookup.Ends.FoMadePub
import OnBytes.Tie.Pv.Lookup.Ends.FoLayerMu
import OnBytes.Tie.Pv.Lookup.Ends.FoPublicAFill
import OnBytes.Tie.Pv.Lookup.Ends.FoPublicAMats
import OnBytes.Tie.Pv.Lookup.Ends.FoPlaneMatPubG
import OnBytes.Tie.PlanAtPolicy
import Johnson.Road.HeadPub
import Johnson.Road.HeadL5Grp
import Johnson.Road.HeadLaid
import Johnson.Road.HeadMade
import Johnson.Road.HeadDict
import Johnson.Thin.Link.PlanV
import Johnson.Flat.SizesPlanned
import Johnson.Top.ExitBuild

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten

section
open OnBytes OnBytes.Flat
open OnBytes.Model OnBytes.Params

/-- At o: The number of entries of the vocabulary in what the layers' sub-proofs read is the
parameter file's. -/
theorem CoveredJoin.publicOf_VO {o : Nat → ByteArray → ByteArray}
    {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : publicOfO o pol KL layout = .ok X) : X.layers.V = X.P.h.V := by
  unfold publicOfO at h
  obtain ⟨⟨P, y⟩, h0, h⟩ := exc_bind h
  dsimp only at h
  repeat' first
    | (obtain ⟨_, _, h⟩ := exc_bind h)
    | (split at h)
  all_goals (cases h; exact (pubOf_V (by assumption)).1)

end

section
open Fo Fo.Pub
open OnBytes OnBytes.Model Fo.BatRows
variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}

/-- At o: The head's layout in X is what Head.layout returns. -/
theorem FoMadePub.publicOf_headLayoutO {o : Nat → ByteArray → ByteArray}
    (h : publicOfO o pol KL layout = .ok X) :
    Head.layout X.hS X.layers.y.tauFC = .ok X.HLy := by
  unfold publicOfO at h
  obtain ⟨⟨P, y⟩, k1, h⟩ := bindE_ok h
  dsimp only at h
  obtain ⟨sc, k2, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  have h := ite_unit_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨wsLay, _, h⟩ := bindE_ok h
  obtain ⟨rope, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨HLy, kL, h⟩ := bindE_ok h
  obtain ⟨y2, k3, h⟩ := ite_pure_ok h
  obtain ⟨layers, k4, h⟩ := bindE_ok h
  obtain ⟨G, k5, h⟩ := bindE_ok h
  obtain ⟨seen, k6, h⟩ := bindE_ok h
  obtain ⟨owner, k7, h⟩ := bindE_ok h
  obtain ⟨H0, k8, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain rfl := Except.ok.inj h
  have hy : layers.y = y := pubOf_y k4
  dsimp only
  rw [hy]
  exact kL

end

section
open Fo
open OnBytes OnBytes.Model
open OnBytes.Params (exc_bind)

/-- At o: **The layers' public numbers in the public record are what Pub.of has returned.** -/
theorem FoLayerMu.publicOf_layersO {o : Nat → ByteArray → ByteArray}
    {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : publicOfO o pol KL layout = .ok X) :
    ∃ y sc rope wsLay V tokv set, Layer.Pub.of y sc rope wsLay V tokv set = .ok X.layers := by
  unfold publicOfO at h
  obtain ⟨⟨P, y⟩, h0, h⟩ := exc_bind h
  dsimp only at h
  repeat' first
    | (obtain ⟨_, _, h⟩ := exc_bind h)
    | (split at h)
  all_goals (cases h; exact ⟨_, _, _, _, _, _, _, by assumption⟩)

end

section
open Fo Fo.PubA
open OnBytes OnBytes.Model Fo.BatRows _root_.Fo
variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}

/-- At o: The scales in the record's layers. -/
theorem FoPublicAFill.public_scO {o : Nat → ByteArray → ByteArray}
    (h : publicOfO o pol KL layout = .ok X) :
    Layer.scalesOf X.layers.y.h (fileWords KL) = .ok X.layers.sc := by
  unfold publicOfO at h
  obtain ⟨⟨P, y⟩, k1, h⟩ := bindE_ok h
  dsimp only at h
  obtain ⟨sc, k2, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  have h := Pub.ite_unit_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨wsLay, _, h⟩ := bindE_ok h
  obtain ⟨rope, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨HLy, _, h⟩ := bindE_ok h
  obtain ⟨y2, k3, h⟩ := Pub.ite_pure_ok h
  obtain ⟨layers, k4, h⟩ := bindE_ok h
  obtain ⟨G, k5, h⟩ := bindE_ok h
  obtain ⟨seen, k6, h⟩ := bindE_ok h
  obtain ⟨owner, k7, h⟩ := bindE_ok h
  obtain ⟨H0, k8, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain rfl := Except.ok.inj h
  show Layer.scalesOf layers.y.h (fileWords KL) = .ok layers.sc
  rw [Pub.pubOf_y k4, pubOf_sc k4]
  exact k2

end

section
open Fo Fo.PubA
open OnBytes OnBytes.Model Fo.BatRows _root_.Fo Fo.PlaneMat Fo.Pub2
variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}

/-- At o: `config_NAs` (OnBytes/Tie/Pv/Lookup/Ends/FoPublicAMats.lean). -/
theorem FoPublicAMats.config_NAsO {o : Nat → ByteArray → ByteArray}
    {P : PolScan} {y : Layer.Lay} {s : Layer.Scales} {mq : ℕ → ℕ}
    {c : Attention.Config} (h : Attention.configO o P y s mq = .ok c) : 0 < P.h.NAs := by
  unfold Attention.configO at h
  obtain ⟨lines, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, hr, _⟩ := bindE_ok h
  by_contra hn
  have h0 : P.h.NAs = 0 := by omega
  simp [refuseIf, h0] at hr

end

section
open Fo Fo.PlaneMatG
open OnBytes OnBytes.Model Fo.BatRows _root_.Fo
variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}

/-- At o: `public_tails` (OnBytes/Tie/Pv/Lookup/Ends/FoPlaneMatPubG.lean). -/
theorem FoPlaneMatPubG.public_tailsO {o : Nat → ByteArray → ByteArray}
    (h : publicOfO o pol KL layout = .ok X) :
    X.layers.tails = Layer.tailsOf X.layers.y := by
  unfold publicOfO at h
  obtain ⟨⟨P, y⟩, k1, h⟩ := bindE_ok h
  dsimp only at h
  obtain ⟨sc, k2, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  have h := Pub.ite_unit_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨wsLay, _, h⟩ := bindE_ok h
  obtain ⟨rope, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨HLy, _, h⟩ := bindE_ok h
  obtain ⟨y2, k3, h⟩ := Pub.ite_pure_ok h
  obtain ⟨layers, k4, h⟩ := bindE_ok h
  obtain ⟨G, k5, h⟩ := bindE_ok h
  obtain ⟨seen, k6, h⟩ := bindE_ok h
  obtain ⟨owner, k7, h⟩ := bindE_ok h
  obtain ⟨H0, k8, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain rfl := Except.ok.inj h
  exact pubOf_tails k4

end

section
open OnBytes OnBytes.Tie
open OnBytes.Params (exc_bind)
open OnBytes.Model OnBytes.Model.Verify
open OnBytes.Model.Stages

/-- At o: **The public part.** Hypotheses: `publicOf` returns X and X' at the two parameter files,
with one scale file and one layout file; hs: the scan of the second is `X.P.withPol C theta cap`.
Then X' is `X.withPol C theta cap`: an equation of whole records. -/
theorem PlanAtPolicy.publicOf_withPolO {o : Nat → ByteArray → ByteArray}
    {pol pol' KL : ByteArray} {layout : Option ByteArray} {X X' : Public}
    {C theta cap : Nat} (h : publicOfO o pol KL layout = .ok X) (h' : publicOfO o pol' KL layout =
        .ok X')
    (hs : polScan pol' = .ok (X.P.withPol C theta cap)) : X' = X.withPol C theta cap := by
  have hP := publicOfO_scan h
  unfold publicOfO at h h'
  obtain ⟨⟨P, y⟩, h0, h⟩ := exc_bind h
  obtain ⟨⟨P', y'⟩, h0', h'⟩ := exc_bind h'
  have eP : X.P = P := Except.ok.inj (hP.symm.trans (polLayout_scan h0))
  rw [eP] at hs
  obtain ⟨rfl, rfl⟩ := polLayout_withPol h0 h0' hs
  dsimp only at h h'
  obtain ⟨a, ha, h⟩ := exc_bind h
  obtain ⟨a', ha', h'⟩ := exc_bind h'
  have ea : a' = a := Except.ok.inj (ha'.symm.trans ha)
  subst ea
  clear ha ha'
  try dsimp only at h h'
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h'⟩ := exc_bind h'
  try dsimp only at h h'
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h'⟩ := exc_bind h'
  try dsimp only at h h'
  by_cases c3 : y'.h.p3 = true
  · rw [if_pos c3] at h h'
    obtain ⟨_, _, h⟩ := exc_bind h
    obtain ⟨_, _, h'⟩ := exc_bind h'
    try dsimp only at h h'
    obtain ⟨_, _, h⟩ := exc_bind h
    obtain ⟨_, _, h'⟩ := exc_bind h'
    try dsimp only at h h'
    obtain ⟨_, _, h⟩ := exc_bind h
    obtain ⟨_, _, h'⟩ := exc_bind h'
    try dsimp only at h h'
    obtain ⟨_, _, h⟩ := exc_bind h
    obtain ⟨_, _, h'⟩ := exc_bind h'
    try dsimp only at h h'
    obtain ⟨_, _, h⟩ := exc_bind h
    obtain ⟨_, _, h'⟩ := exc_bind h'
    try dsimp only at h h'
    obtain ⟨a, ha, h⟩ := exc_bind h
    obtain ⟨a', ha', h'⟩ := exc_bind h'
    have ea : a' = a := Except.ok.inj (ha'.symm.trans ha)
    subst ea
    clear ha ha'
    try dsimp only at h h'
    obtain ⟨a, ha, h⟩ := exc_bind h
    obtain ⟨a', ha', h'⟩ := exc_bind h'
    have ea : a' = a := Except.ok.inj (ha'.symm.trans ha)
    subst ea
    clear ha ha'
    try dsimp only at h h'
    obtain ⟨_, _, h⟩ := exc_bind h
    obtain ⟨_, _, h'⟩ := exc_bind h'
    try dsimp only at h h'
    obtain ⟨HLy, hL, h⟩ := exc_bind h
    obtain ⟨HLy', hL', h'⟩ := exc_bind h'
    have eL : HLy' = HLy := layout_withPol _ C theta cap _ hL hL'
    subst eL
    by_cases c4 : (y').h.p4 = true
    · rw [if_pos c4] at h h'
      obtain ⟨a, ha, h⟩ := exc_bind h
      obtain ⟨a', ha', h'⟩ := exc_bind h'
      have ea : a' = a := Except.ok.inj (ha'.symm.trans ha)
      subst ea
      clear ha ha'
      try dsimp only at h h'
      obtain ⟨a, ha, h⟩ := exc_bind h
      obtain ⟨a', ha', h'⟩ := exc_bind h'
      have ea : a' = a := Except.ok.inj (ha'.symm.trans ha)
      subst ea
      clear ha ha'
      try dsimp only at h h'
      obtain ⟨a, ha, h⟩ := exc_bind h
      obtain ⟨a', ha', h'⟩ := exc_bind h'
      have ea : a' = a := Except.ok.inj (ha'.symm.trans ha)
      subst ea
      clear ha ha'
      try dsimp only at h h'
      obtain ⟨a, ha, h⟩ := exc_bind h
      obtain ⟨a', ha', h'⟩ := exc_bind h'
      have ea : a' = a := Except.ok.inj (ha'.symm.trans ha)
      subst ea
      clear ha ha'
      try dsimp only at h h'
      obtain ⟨a, ha, h⟩ := exc_bind h
      obtain ⟨a', ha', h'⟩ := exc_bind h'
      have ea : a' = a := Except.ok.inj (ha'.symm.trans ha)
      subst ea
      clear ha ha'
      try dsimp only at h h'
      obtain ⟨a, ha, h⟩ := exc_bind h
      obtain ⟨a', ha', h'⟩ := exc_bind h'
      have ea : a' = a := Except.ok.inj (ha'.symm.trans ha)
      subst ea
      clear ha ha'
      try dsimp only at h h'
      obtain ⟨a, ha, h⟩ := exc_bind h
      obtain ⟨a', ha', h'⟩ := exc_bind h'
      have ea : a' = a := Except.ok.inj (ha'.symm.trans ha)
      subst ea
      clear ha ha'
      try dsimp only at h h'
      obtain ⟨_, _, h⟩ := exc_bind h
      obtain ⟨_, _, h'⟩ := exc_bind h'
      try dsimp only at h h'
      cases h
      cases h'
      rfl
    · rw [if_neg c4] at h h'
      obtain ⟨a, ha, h⟩ := exc_bind h
      obtain ⟨a', ha', h'⟩ := exc_bind h'
      have ea : a' = a := Except.ok.inj (ha'.symm.trans ha)
      subst ea
      clear ha ha'
      try dsimp only at h h'
      obtain ⟨a, ha, h⟩ := exc_bind h
      obtain ⟨a', ha', h'⟩ := exc_bind h'
      have ea : a' = a := Except.ok.inj (ha'.symm.trans ha)
      subst ea
      clear ha ha'
      try dsimp only at h h'
      obtain ⟨a, ha, h⟩ := exc_bind h
      obtain ⟨a', ha', h'⟩ := exc_bind h'
      have ea : a' = a := Except.ok.inj (ha'.symm.trans ha)
      subst ea
      clear ha ha'
      try dsimp only at h h'
      obtain ⟨a, ha, h⟩ := exc_bind h
      obtain ⟨a', ha', h'⟩ := exc_bind h'
      have ea : a' = a := Except.ok.inj (ha'.symm.trans ha)
      subst ea
      clear ha ha'
      try dsimp only at h h'
      obtain ⟨a, ha, h⟩ := exc_bind h
      obtain ⟨a', ha', h'⟩ := exc_bind h'
      have ea : a' = a := Except.ok.inj (ha'.symm.trans ha)
      subst ea
      clear ha ha'
      try dsimp only at h h'
      obtain ⟨a, ha, h⟩ := exc_bind h
      obtain ⟨a', ha', h'⟩ := exc_bind h'
      have ea : a' = a := Except.ok.inj (ha'.symm.trans ha)
      subst ea
      clear ha ha'
      try dsimp only at h h'
      obtain ⟨_, _, h⟩ := exc_bind h
      obtain ⟨_, _, h'⟩ := exc_bind h'
      try dsimp only at h h'
      cases h
      cases h'
      rfl
  · rw [if_neg c3] at h h'
    obtain ⟨_, _, h⟩ := exc_bind h
    obtain ⟨_, _, h'⟩ := exc_bind h'
    try dsimp only at h h'
    obtain ⟨_, _, h⟩ := exc_bind h
    obtain ⟨_, _, h'⟩ := exc_bind h'
    try dsimp only at h h'
    obtain ⟨_, _, h⟩ := exc_bind h
    obtain ⟨_, _, h'⟩ := exc_bind h'
    try dsimp only at h h'
    obtain ⟨_, _, h⟩ := exc_bind h
    obtain ⟨_, _, h'⟩ := exc_bind h'
    try dsimp only at h h'
    obtain ⟨_, _, h⟩ := exc_bind h
    obtain ⟨_, _, h'⟩ := exc_bind h'
    try dsimp only at h h'
    obtain ⟨a, ha, h⟩ := exc_bind h
    obtain ⟨a', ha', h'⟩ := exc_bind h'
    have ea : a' = a := Except.ok.inj (ha'.symm.trans ha)
    subst ea
    clear ha ha'
    try dsimp only at h h'
    obtain ⟨a, ha, h⟩ := exc_bind h
    obtain ⟨a', ha', h'⟩ := exc_bind h'
    have ea : a' = a := Except.ok.inj (ha'.symm.trans ha)
    subst ea
    clear ha ha'
    try dsimp only at h h'
    obtain ⟨_, _, h⟩ := exc_bind h
    obtain ⟨_, _, h'⟩ := exc_bind h'
    try dsimp only at h h'
    obtain ⟨HLy, hL, h⟩ := exc_bind h
    obtain ⟨HLy', hL', h'⟩ := exc_bind h'
    have eL : HLy' = HLy := layout_withPol _ C theta cap _ hL hL'
    subst eL
    by_cases c4 : (y').h.p4 = true
    · rw [if_pos c4] at h h'
      obtain ⟨a, ha, h⟩ := exc_bind h
      obtain ⟨a', ha', h'⟩ := exc_bind h'
      have ea : a' = a := Except.ok.inj (ha'.symm.trans ha)
      subst ea
      clear ha ha'
      try dsimp only at h h'
      obtain ⟨a, ha, h⟩ := exc_bind h
      obtain ⟨a', ha', h'⟩ := exc_bind h'
      have ea : a' = a := Except.ok.inj (ha'.symm.trans ha)
      subst ea
      clear ha ha'
      try dsimp only at h h'
      obtain ⟨a, ha, h⟩ := exc_bind h
      obtain ⟨a', ha', h'⟩ := exc_bind h'
      have ea : a' = a := Except.ok.inj (ha'.symm.trans ha)
      subst ea
      clear ha ha'
      try dsimp only at h h'
      obtain ⟨a, ha, h⟩ := exc_bind h
      obtain ⟨a', ha', h'⟩ := exc_bind h'
      have ea : a' = a := Except.ok.inj (ha'.symm.trans ha)
      subst ea
      clear ha ha'
      try dsimp only at h h'
      obtain ⟨a, ha, h⟩ := exc_bind h
      obtain ⟨a', ha', h'⟩ := exc_bind h'
      have ea : a' = a := Except.ok.inj (ha'.symm.trans ha)
      subst ea
      clear ha ha'
      try dsimp only at h h'
      obtain ⟨a, ha, h⟩ := exc_bind h
      obtain ⟨a', ha', h'⟩ := exc_bind h'
      have ea : a' = a := Except.ok.inj (ha'.symm.trans ha)
      subst ea
      clear ha ha'
      try dsimp only at h h'
      obtain ⟨a, ha, h⟩ := exc_bind h
      obtain ⟨a', ha', h'⟩ := exc_bind h'
      have ea : a' = a := Except.ok.inj (ha'.symm.trans ha)
      subst ea
      clear ha ha'
      try dsimp only at h h'
      obtain ⟨_, _, h⟩ := exc_bind h
      obtain ⟨_, _, h'⟩ := exc_bind h'
      try dsimp only at h h'
      cases h
      cases h'
      rfl
    · rw [if_neg c4] at h h'
      obtain ⟨a, ha, h⟩ := exc_bind h
      obtain ⟨a', ha', h'⟩ := exc_bind h'
      have ea : a' = a := Except.ok.inj (ha'.symm.trans ha)
      subst ea
      clear ha ha'
      try dsimp only at h h'
      obtain ⟨a, ha, h⟩ := exc_bind h
      obtain ⟨a', ha', h'⟩ := exc_bind h'
      have ea : a' = a := Except.ok.inj (ha'.symm.trans ha)
      subst ea
      clear ha ha'
      try dsimp only at h h'
      obtain ⟨a, ha, h⟩ := exc_bind h
      obtain ⟨a', ha', h'⟩ := exc_bind h'
      have ea : a' = a := Except.ok.inj (ha'.symm.trans ha)
      subst ea
      clear ha ha'
      try dsimp only at h h'
      obtain ⟨a, ha, h⟩ := exc_bind h
      obtain ⟨a', ha', h'⟩ := exc_bind h'
      have ea : a' = a := Except.ok.inj (ha'.symm.trans ha)
      subst ea
      clear ha ha'
      try dsimp only at h h'
      obtain ⟨a, ha, h⟩ := exc_bind h
      obtain ⟨a', ha', h'⟩ := exc_bind h'
      have ea : a' = a := Except.ok.inj (ha'.symm.trans ha)
      subst ea
      clear ha ha'
      try dsimp only at h h'
      obtain ⟨a, ha, h⟩ := exc_bind h
      obtain ⟨a', ha', h'⟩ := exc_bind h'
      have ea : a' = a := Except.ok.inj (ha'.symm.trans ha)
      subst ea
      clear ha ha'
      try dsimp only at h h'
      obtain ⟨_, _, h⟩ := exc_bind h
      obtain ⟨_, _, h'⟩ := exc_bind h'
      try dsimp only at h h'
      cases h
      cases h'
      rfl

end

section
open OnBytes OnBytes.Tie
open OnBytes.Params (exc_bind)
open OnBytes.Model OnBytes.Model.Verify
open OnBytes.Model.Stages

/-- At o: **The head's shape has the scan's three numbers.** Hypothesis: `publicOf` returns X. -/
theorem PlanAtPolicy.publicOf_hSO {o : Nat → ByteArray → ByteArray}
    {pol KL : ByteArray} {layout : Option ByteArray} {X : Public}
    (h : publicOfO o pol KL layout = .ok X) :
    X.hS.clipC = X.P.h.clipC ∧ X.hS.theta = X.P.h.theta ∧ X.hS.cap = X.P.h.cap := by
  unfold publicOfO at h
  obtain ⟨⟨P, y⟩, _, h⟩ := exc_bind h
  dsimp only at h
  repeat' first
    | (obtain ⟨_, _, h⟩ := exc_bind h)
    | (split at h)
  all_goals
    cases h
    exact ⟨rfl, rfl, rfl⟩

end

section
open OnBytes OnBytes.Road OnBytes.Road.Hd

/-- At o: **What publicOf has run for the head, and what its value holds.** P, y: the parameter file
as read and the layers' layout, from polLayout. The value holds P, y and the head's shape made of
them. The layers' conditions against wrap-around have passed. The head's layout is what Head.layout
returns for that shape and the layers' table of the clamp. The head's plan is what planH2 returns
for the shape, the layout, the stream's matrix of y and the value's owner, but for its planned
state, which is trimmed: the plan of the smallness test is the same. -/
theorem HeadPub.public_partsO {o : Nat → ByteArray → ByteArray}
    {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}
    (h : publicOfO o pol KL lay = .ok X) :
    ∃ P y, Model.Verify.polLayout pol = .ok (P, y) ∧ X.P = P ∧ X.y = y ∧
      X.hS = Model.Verify.headShape P y ∧
      (∃ sc u, Model.Layer.noWrap y.h sc y.dq = .ok u) ∧
      Model.Head.layout X.hS y.tauFC = .ok X.HLy ∧
      ∃ H, Model.Head.planH2 P.settings X.hS X.HLy (Model.Verify.borderOf y) X.owner y.NGr
        P.lkW = .ok H ∧ X.H.tl = H.tl := by
  unfold publicOfO at h
  obtain ⟨⟨P, y⟩, hpl, h⟩ := ok_of_bind h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  obtain ⟨_, h⟩ := ok_of_ite h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  obtain ⟨⟨A0, hCallsA⟩, h⟩ := ok_of_ite2 h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  cases h
  refine ⟨P, y, hpl, rfl, pubOf_y (by assumption), rfl, ⟨_, _, by assumption⟩, by assumption,
    ⟨?H, ?h1, ?h2⟩⟩
  case h1 => assumption
  case h2 => rfl

end

section
open OnBytes OnBytes.Road OnBytes.Road.Hd

/-- At o: **The plans that Attention.config returns are the values of Attention.group**, one for
each group of layers. -/
theorem HeadL5Grp.config_groupsO {o : Nat → ByteArray → ByteArray}
    {P : Model.PolScan} {y : Model.Layer.Lay} {s : Model.Layer.Scales}
    {midQ : ℕ → ℕ} {c : Attention.Config} (h : Attention.configO o P y s midQ = .ok c) :
    ∃ lines, c.plans.size = y.NGr ∧ ∀ g, g < y.NGr →
      ∃ Xg, c.plans[g]? = some Xg ∧ Attention.group P y s midQ lines g = .ok Xg := by
  unfold Attention.configO at h
  obtain ⟨lines, -, h⟩ := ok_of_bind h
  obtain ⟨-, -, h⟩ := ok_of_bind h
  obtain ⟨-, -, h⟩ := ok_of_bind h
  obtain ⟨plans, hm, h⟩ := ok_of_bind h
  cases plans with
  | nil => cases h
  | cons X0 rest =>
    obtain ⟨-, -, h⟩ := ok_of_bind h
    cases h
    refine ⟨lines, ?_, fun g hg => ?_⟩
    · have k := mapM_length _ _ _ hm
      rw [List.length_range] at k
      show (X0 :: rest).toArray.size = y.NGr
      rw [List.size_toArray]
      exact k
    · obtain ⟨Xg, h1, h2⟩ := mapM_ok _ _ _ hm g g (by simp [hg])
      exact ⟨Xg, by simpa using h1, h2⟩

end

section
open OnBytes OnBytes.Road OnBytes.Road.Hd

/-- At o: The scales in the public part are what the verifier's function reads off the scale file,
and they have passed its tests on them. -/
theorem HeadL5Grp.scalesBoth_of_publicO {o : Nat → ByteArray → ByteArray}
    {pol KL : ByteArray} {lay : Option ByteArray}
    {X : Model.Verify.Public} (h : publicOfO o pol KL lay = .ok X) :
    Model.Layer.scalesOf X.y.h (Model.fileWords KL) = .ok X.layers.sc ∧
      Model.Layer.scalesHeld X.y.h X.layers.sc = .ok () := by
  unfold publicOfO at h
  obtain ⟨⟨P, y⟩, -, h⟩ := ok_of_bind h
  obtain ⟨sc, hsc, h⟩ := ok_of_bind h
  obtain ⟨u, hheld, h⟩ := ok_of_bind h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  obtain ⟨_, h⟩ := ok_of_ite h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  obtain ⟨⟨A0, hCallsA⟩, h⟩ := ok_of_ite2 h
  obtain ⟨layers, hPub, h⟩ := ok_of_bind h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  cases h
  have ey : layers.y = y := pubOf_y hPub
  have es : layers.sc = sc := pubOf_sc hPub
  refine ⟨?_, ?_⟩
  · show Model.Layer.scalesOf layers.y.h (Model.fileWords KL) = .ok layers.sc
    rw [ey, es]
    exact hsc
  · show Model.Layer.scalesHeld layers.y.h layers.sc = .ok ()
    rw [ey, es]
    exact hheld

end

section
open OnBytes OnBytes.Road OnBytes.Road.Hd

/-- At o: **The joint.** At profile 4, each attention plan in the public part of a stage has the
shape of what Attention.group returns for its group, at the parameter file, the layers' layout and
the scales of that public part. It is that value with one record of its seam filled: shape, lookup
shape and what the caller passed are kept. A0: the plans as Attention.config returns them; seenA:
what attentionOwners makes of their seams; the filled record is seenA's. -/
theorem HeadL5Grp.groups_of_publicO {o : Nat → ByteArray → ByteArray}
    {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}
    (h : publicOfO o pol KL lay = .ok X)
    (hp4 : (Model.Verify.layerShape X.P).p4 = true) :
    ∃ (lines : List Attention.Line) (A0 : Array Attention.Plan)
      (seenG seenA : Array Model.Verify.SubPlan),
      Model.Verify.attentionOwners X.y.h.p4 X.y.NGr seenG
        (A0.map fun Z => ⟨Z.seam.tl, Z.seam.Fp, Z.seam.Tp⟩) = .ok seenA ∧
      ∀ g, g < X.y.NGr →
        ∃ Xg Ag s, Attention.group X.P X.y X.layers.sc (midQOf X.y) lines g = .ok Xg ∧
          A0[g]? = some Xg ∧ seenA[g]? = some s ∧ X.A[g]? = some Ag ∧ Ag.S = Xg.S ∧
          Ag.fs = Xg.fs ∧ Ag.inp = Xg.inp ∧ Ag.seam.tl = s.tl ∧ shapeA X g = Xg.S := by
  obtain ⟨P, y, hpl1, eP, -⟩ := HeadPub.public_partsO h
  have hq1 : y.h.p4 = true := by
    rw [layout_shape (layerLayout_of_polLayout hpl1), ← eP]
    exact hp4
  unfold publicOfO at h
  obtain ⟨⟨P', y'⟩, hpl, h⟩ := ok_of_bind h
  have e : (P, y) = (P', y') := Except.ok.inj (hpl1.symm.trans hpl)
  cases e
  obtain ⟨sc, -, h⟩ := ok_of_bind h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  obtain ⟨_, h⟩ := ok_of_ite h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  dsimp only at h
  rw [if_pos hq1] at h
  obtain ⟨c, hcfg, h⟩ := ok_of_bind h
  obtain ⟨⟨A0, hC⟩, hpure, h⟩ := ok_of_bind h
  have e2 : (c.plans, c.hCallsA) = (A0, hC) := Except.ok.inj hpure
  cases e2
  obtain ⟨layers, hPub, h⟩ := ok_of_bind h
  obtain ⟨G, -, h⟩ := ok_of_bind h
  obtain ⟨seenA, hown, h⟩ := ok_of_bind h
  obtain ⟨owner, -, h⟩ := ok_of_bind h
  obtain ⟨H, -, h⟩ := ok_of_bind h
  obtain ⟨-, -, h⟩ := ok_of_bind h
  cases h
  have ey : layers.y = y := pubOf_y hPub
  have es : layers.sc = sc := pubOf_sc hPub
  obtain ⟨lines, hsz, hgrp⟩ := HeadL5Grp.config_groupsO hcfg
  have hs2 : seenA.size = c.plans.size := by rw [owners_size hown, Array.size_map]
  refine ⟨lines, c.plans, G.map fun O => (⟨O.tl, O.Fp, O.Tp⟩ : Model.Verify.SubPlan), seenA, ?_,
    fun g hg => ?_⟩
  · show Model.Verify.attentionOwners layers.y.h.p4 layers.y.NGr _ _ = .ok seenA
    rw [ey]
    exact hown
  have hg' : g < y.NGr := by
    have k : g < layers.y.NGr := hg
    rw [ey] at k
    exact k
  obtain ⟨Xg, h1, h2⟩ := hgrp g hg'
  have hlt : g < seenA.size := by
    rw [hs2, hsz]
    exact hg'
  have hb : seenA[g]? = some seenA[g] := by simp [hlt]
  refine ⟨Xg, _, seenA[g], ?_, h1, hb, zipWith_atA _ _ _ h1 hb, rfl, rfl, rfl, rfl, ?_⟩
  · show Attention.group P layers.y layers.sc (midQOf layers.y) lines g = .ok Xg
    rw [ey, es]
    exact h2
  · unfold shapeA
    dsimp only
    rw [zipWith_atA _ _ _ h1 hb]
    rfl

end

section
open OnBytes OnBytes.Road OnBytes.Road.Hd
open HeadSizes (Sizes)

/-- At o: **The head's layout in the verifier's public part is what the function layout returns**
for the head's shape there and the clamp's table of the layers' layout. P, y: the parameter file as
read, and the layers' layout. -/
theorem HeadLaid.layout_of_publicO {o : Nat → ByteArray → ByteArray}
    {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}
    (h : publicOfO o pol KL lay = .ok X) :
    ∃ P y, Model.Verify.polLayout pol = .ok (P, y) ∧ X.hS = Model.Verify.headShape P y ∧
      Model.Head.layout X.hS y.tauFC = .ok X.HLy := by
  unfold publicOfO at h
  obtain ⟨⟨P, y⟩, hpl, h⟩ := ok_of_bind h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  obtain ⟨_, h⟩ := ok_of_ite h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  obtain ⟨⟨A0, hCallsA⟩, h⟩ := ok_of_ite2 h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  cases h
  exact ⟨P, y, hpl, rfl, by assumption⟩

end

section
open OnBytes OnBytes.Road OnBytes.Road.Hd
open OnBytes.Model (Reading World HTailF2 Fork wsLayOf)
open OnBytes.Model.Layer (Lay)
open OnBytes.Model.Head (HPlanH2 planH2)
open OnBytes.Model.Verify (Public publicOf polLayout borderOf ownerOf layerShape weightShape)

/-- At o: **The public part, taken apart.** -/
theorem HeadMade.publicH_of_publicO {o : Nat → ByteArray → ByteArray}
    {pol KL : ByteArray} {lay : Option ByteArray} {X : Public}
    (h : publicOfO o pol KL lay = .ok X) : PublicH X := by
  unfold publicOfO at h
  obtain ⟨⟨P, y⟩, hpl, h⟩ := ok_of_bind h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  obtain ⟨_, h⟩ := ok_of_either h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  obtain ⟨⟨A0, hCallsA⟩, h⟩ := ok_of_either2 h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  cases h
  obtain ⟨e1, e2⟩ := pub_fields (by assumption)
  have hy := layout_of_polLayout hpl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold Model.Verify.Public.y
    dsimp only
    rw [e1]
    exact hy
  · unfold Model.Verify.Public.y
    dsimp only
    rw [e1, e2]
    assumption
  · unfold Model.Verify.Public.y
    dsimp only
    rw [e1]
    assumption
  · unfold Model.Verify.Public.y
    dsimp only
    rw [e1]
    assumption
  · unfold Model.Verify.Public.y
    dsimp only
    rw [e1]
    refine ⟨?H0, ?a, ?b⟩
    case a => assumption
    case b => rfl

end

section
open OnBytes OnBytes.Road OnBytes.Road.Hd
open Inst.Model (ppref Instance Mat)
open Inst.Model.All (DF)
open OnBytes.Model (TMat T2Foreign HTailF2 Settings)
open OnBytes.Model.Layer (Lay Pub HPlan2 Scales bordersOf planG plansFrom plansG tailsOf matIx)
open OnBytes.Model.Head (HL Border Owner HPlanH2 matsH planH2)
open OnBytes.Model.Verify (Public publicOf borderOf ownerOf)

/-- At o: Two more lines of the verifier's public part, on its own results: the layers' public
numbers are what Pub.of returns on the layout, and the plans of the groups are what plansG returns
on them. -/
theorem HeadDict.public_plansO {o : Nat → ByteArray → ByteArray}
    {pol KL : ByteArray} {lay : Option ByteArray} {X : Public}
    (h : publicOfO o pol KL lay = .ok X) :
    ∃ sc rope wsLay V tokv set, Pub.of X.y sc rope wsLay V tokv set = .ok X.layers ∧
      plansG X.layers = .ok X.G := by
  unfold publicOfO at h
  obtain ⟨⟨P, y⟩, hpl, h⟩ := ok_of_bind h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  obtain ⟨_, h⟩ := ok_of_either h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  obtain ⟨⟨A0, hCallsA⟩, h⟩ := ok_of_either2 h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  cases h
  obtain ⟨e1, -⟩ := pub_fields (by assumption)
  unfold Model.Verify.Public.y
  dsimp only
  rw [e1]
  exact ⟨_, _, _, _, _, _, by assumption, by assumption⟩

end

section
open Cb Cb.Thin Cb.Thin.Link
open OnBytes OnBytes.Model

/-- At o: `Verify.publicOf` makes the layers' public numbers at the shape's V. Lean lays the rest of
that text into both arms of its two ifs, so the binds are opened by a loop and every equation is
kept. -/
theorem PlanV.publicOf_VO {o : Nat → ByteArray → ByteArray}
    {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : publicOfO o pol KL layout = .ok X) : X.layers.V = X.P.h.V := by
  unfold publicOfO at h
  obtain ⟨⟨P, y⟩, -, h⟩ := OnBytes.Params.exc_bind h
  repeat (any_goals (first
    | (obtain ⟨_, _, h⟩ := OnBytes.Params.exc_bind h)
    | (split at h)
    | (dsimp only at h)))
  all_goals
    cases h
    exact pubOf_V (by assumption)

end

section
open OnBytes OnBytes.Flat
open Inst.Model OnBytes.Model OnBytes.Model.Verify
open OnBytes.Params (exc_bind)

/-- At o: **In the public part that the planner makes**: the window is 2 ^ lt of the parameter file
as scanned, lt is at most 16, and the vocabulary is at most 2 ^ 24. -/
theorem SizesPlanned.publicOf_windowO {o : Nat → ByteArray → ByteArray}
    {pol KL : ByteArray} {layout : Option ByteArray} {X : Public}
    (h : publicOfO o pol KL layout = .ok X) :
    X.T = 2 ^ X.P.h.lt ∧ X.P.h.lt ≤ 16 ∧ X.P.h.V ≤ 2 ^ 24 := by
  unfold publicOfO at h
  obtain ⟨⟨P, y⟩, h0, h⟩ := exc_bind h
  obtain ⟨hT, hlt⟩ := polLayout_window h0
  dsimp only at h
  repeat' first
    | (obtain ⟨_, _, h⟩ := exc_bind h)
    | (split at h)
  all_goals
    cases h
    have eL := pub_layout (by assumption)
    have eV : (headShape P y).V ≤ 2 ^ 24 := vocabulary_le (by assumption)
    exact ⟨(congrArg Layer.Lay.T eL).trans hT, hlt, eV⟩

end

section
open OnBytes OnBytes.K
open OnBytes.Shell (Steps opsIO World Event wholeReads kindOf Asked)
open OnBytes OnBytes.Model OnBytes.Model.Verify
open OnBytes.Params (exc_bind)

/-- At o: In the public part the head's lt and V are the parameter file's. -/
theorem ExitBuild.publicOf_headO {o : Nat → ByteArray → ByteArray}
    {pol KL : ByteArray} {layout : Option ByteArray} {X : Public}
    (h : publicOfO o pol KL layout = .ok X) : X.hS.lt = X.P.h.lt ∧ X.hS.V = X.P.h.V := by
  unfold publicOfO at h
  obtain ⟨⟨P, y⟩, _, h⟩ := exc_bind h
  dsimp only at h
  repeat' first
    | (obtain ⟨_, _, h⟩ := exc_bind h)
    | (split at h)
  all_goals (cases h; exact ⟨rfl, rfl⟩)

end

end VerifiableInference.PlanWritten

#print axioms VerifiableInference.PlanWritten.CoveredJoin.publicOf_VO
#print axioms VerifiableInference.PlanWritten.FoMadePub.publicOf_headLayoutO
#print axioms VerifiableInference.PlanWritten.FoLayerMu.publicOf_layersO
#print axioms VerifiableInference.PlanWritten.FoPublicAFill.public_scO
#print axioms VerifiableInference.PlanWritten.FoPublicAMats.config_NAsO
#print axioms VerifiableInference.PlanWritten.FoPlaneMatPubG.public_tailsO
#print axioms VerifiableInference.PlanWritten.PlanAtPolicy.publicOf_withPolO
#print axioms VerifiableInference.PlanWritten.PlanAtPolicy.publicOf_hSO
#print axioms VerifiableInference.PlanWritten.HeadPub.public_partsO
#print axioms VerifiableInference.PlanWritten.HeadL5Grp.config_groupsO
#print axioms VerifiableInference.PlanWritten.HeadL5Grp.scalesBoth_of_publicO
#print axioms VerifiableInference.PlanWritten.HeadL5Grp.groups_of_publicO
#print axioms VerifiableInference.PlanWritten.HeadLaid.layout_of_publicO
#print axioms VerifiableInference.PlanWritten.HeadMade.publicH_of_publicO
#print axioms VerifiableInference.PlanWritten.HeadDict.public_plansO
#print axioms VerifiableInference.PlanWritten.PlanV.publicOf_VO
#print axioms VerifiableInference.PlanWritten.SizesPlanned.publicOf_windowO
#print axioms VerifiableInference.PlanWritten.ExitBuild.publicOf_headO
