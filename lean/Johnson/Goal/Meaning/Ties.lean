-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/Ties.lean: the goals' reader of the public files and the verifier's own reading
of them give one acceptance policy and one table of scales.

Two texts of this library read the parameter file and the scale file.
* The goals' reader (VerifierAndGoals.readFiles, Ladder.lean; it is settingsAtRef,
  Johnson/Flat/SettingsRead.lean) returns pp: a table of scales and a policy. The model, the weights
  and the claim of the top statements are formed at pp.
* The verifier's reading (publicOf, OnBytes/Model/VerifyPublic.lean) returns the public part X. What
  the protocol's checks hold are X's numbers: the policy Hd.polOf X.hS
  (Johnson/Road/HeadLinkLPort.lean) and the table Flat.scalesAt X (Johnson/Flat/ScalesAt.lean).
A law on the protocol's checks ends at X's numbers; the law on the model
(Johnson/Goal/Meaning/NextToken.lean) starts at pp's. This file states and proves that they are the
same numbers. The statement is ReadingsAgree, a closed proposition; the theorem is readings_agree.

What it says. At every set of public files, every layout file or none, where both readings return:
  policy   pp.pol = Hd.polOf X.hS.
  scales   If the parameter file states 48 layers: Cm.Scales.of pp = Flat.scalesAt X.

Why "48 layers" is a premise. The goals' reader takes a parameter file with fewer layers too, and
fills the table's further layers with the reference's numbers (klFileOf); the verifier's table has
other numbers there. So the equation is false without it. It is a test on the scanned file that a
run can make. At the files in the goals' scope it is a theorem: layers_of_scope
(Johnson/Goal/Meaning/ScopeCore.lean), which this file does not import.

What it does not say. That either reading returns at any files. That any check reads or enforces
these numbers. Nothing on a protocol.

How it is proved. policy: hS_of_settings (Johnson/Flat/HeadShapeOfSettings.lean). scales: the proof
of scalesAt_eq (Johnson/Flat/ScalesSame.lean), which is stated for the reader that refuses every
policy but exact match, goes through word for word from what the reader at any policy was made of
(settingsAny_parts).
-/
import Ladder
import Johnson.Flat.HeadShapeOfSettings
import Johnson.Flat.ScalesSame
import Johnson.Road.HeadLinkLPort

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Meaning
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.Flat Inst.Model
open OnBytes OnBytes.Road
open OnBytes.Model.Verify (Public publicOf layerShape)

/-- **The two readings of the public files agree**: one policy; and, at 48 layers, one table of
scales. -/
def ReadingsAgree : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (pp : ScalesAndPolicy) (layout : Option ByteArray) (X : Public),
    VerifierAndGoals.readFiles Z = .ok pp → publicOf Z.pol Z.KL layout = .ok X →
      pp.pol = Hd.polOf X.hS ∧ (X.P.h.L = 48 → Cm.Scales.of pp = Flat.scalesAt X)

/-- The table of scales of settings that the reader at any policy returns, from the public numbers
that it read. -/
theorem scales_of_parts {f : KLFile} {pp : ScalesAndPolicy} (h : ofKL f = some pp) :
    Cm.Scales.of pp = ⟨f.words, ⟨f.MF, f.KF, f.epsF⟩⟩ := by
  unfold ofKL at h
  split at h
  · cases h
    rfl
  · cases h

/-- One table of scales, from the reader at any policy. -/
theorem scalesAt_eq_any {pol KL : ByteArray} {lay : Option ByteArray} {X : Public} {pp : ScalesAndPolicy}
    (h : publicOf pol KL lay = .ok X) (hs : OnBytes.Flat.settingsAny pol KL = .ok pp)
    (hp4 : (layerShape X.P).p4 = true) (hL : X.P.h.L = 48) :
    Cm.Scales.of pp = Flat.scalesAt X := by
  obtain ⟨P, f, hP, hf, ho⟩ := OnBytes.Flat.settingsAny_parts hs
  rw [scales_of_parts ho]
  obtain ⟨P', y, hpl, eP, ey, eS, -⟩ := Hd.public_parts h
  have eP' : P = X.P := by
    have e := (polScan_of_polLayout hpl).symm.trans hP
    rw [eP]
    exact (Except.ok.inj e).symm
  subst eP'
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := klFileOf_fields hf
  have hr := Hd.scales_of_public h
  rw [shape_of_public h] at hr
  have hsc := reader_record hr
  rw [if_pos hp4] at hsc
  have hLs : (layerShape X.P).L = 48 := hL
  have ew : f.words = (fileOf (layerShape X.P) X.layers.sc).words := by
    refine words_congr (fun L j => ?_) (fun e j => ?_) g3 g4
    · rw [g1 L j (by rw [hL]; exact L.isLt), word_same]
      show _ = X.layers.sc.kl L.val j.val
      rw [hsc]
      rfl
    · rw [g2 e j (by rw [hL]; have := e.isLt; omega), word_same]
      show _ = X.layers.sc.klM (2 * e.val + 1) j.val
      rw [hsc]
      show _ = (Model.fileWords KL).getD (13 * (layerShape X.P).L + 3 * ((2 * e.val + 1) / 2) +
        j.val) 0
      have e2 : (2 * e.val + 1) / 2 = e.val := by omega
      rw [e2, hLs, hL]
  have en : (⟨f.MF, f.KF, f.epsF⟩ : NormPar) = Hd.npOf X.hS := by
    rw [g5, g6, g7, eS, ← eP]
    rfl
  show (⟨f.words, ⟨f.MF, f.KF, f.epsF⟩⟩ : Cm.Scales) =
    ⟨(fileOf (layerShape X.P) X.layers.sc).words, Hd.npOf X.hS⟩
  rw [ew, en]

/-- Where the goals' reader returns, the scan inside the verifier's public part has profile 4. -/
theorem p4_of_read {pol KL : ByteArray} {lay : Option ByteArray} {X : Public} {pp : ScalesAndPolicy}
    (h : publicOf pol KL lay = .ok X) (hs : OnBytes.Flat.settingsAtRef pol KL = .ok pp) :
    (layerShape X.P).p4 = true := by
  obtain ⟨S, hS, held⟩ := OnBytes.Flat.settingsAtRef_held hs
  obtain ⟨P', y, hpl, eP, -⟩ := Hd.public_parts h
  have e : S = X.P := by
    have e := (polScan_of_polLayout hpl).symm.trans hS
    rw [eP]
    exact (Except.ok.inj e).symm
  subst e
  have prof : X.P.h.prof = 4 := (OnBytes.Flat.otherLinesHeld_policy held).1
  show (X.P.h.prof == 4) = true
  rw [prof]
  rfl

/-- **The law.** -/
theorem readings_agree : ReadingsAgree := fun _ pp _ X isRead isPublic =>
  ⟨by
    obtain ⟨c, t, k, -⟩ := OnBytes.Flat.hS_of_settings isPublic isRead
    show pp.pol = ⟨X.hS.clipC, X.hS.theta, X.hS.cap⟩
    rw [c, t, k],
   fun layers => scalesAt_eq_any isPublic (OnBytes.Flat.settingsAtRef_eq isRead)
    (p4_of_read isPublic isRead) layers⟩

end VerifiableInference.Meaning

#print axioms VerifiableInference.Meaning.readings_agree
