-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/T3/DigestsInScope.lean: AT ALL PUBLIC FILES IN THE GOALS' SCOPE THE PUBLIC PART HOLDS THE
SAME THREE DIGESTS OF CALL LISTS, and these are the digests that the reader of the request's item
forms from the stored full-size parameter file's call lines. Statements with their proofs; no
definition; nothing is evaluated here.

Why. The verifier compares the item "request" with the public part (`Verify.statementHeld`). Three
groups of eight words of the item are digests of the parameter file's lines call, callA and callH;
the public part holds digests of the lists of lookup calls that its own layouts use. At the stored
full-size files the two sides agree (`Johnson.AtFull.Item.parts_zFull`). In scope only eight numbers
of the parameter file and the scale file are free, and none of the three lists reads them.

Main names.
  `config_digest`       attention's digest is that of the lines that its reader returns
  `digests_of_public`   wherever `publicOf` returns, at profile 4: the three digests, as its text forms them
  `calls_free`          the layers' calls do not hang on the three constants of the normalisations
  `digests_same`        at two sets of public files in scope the three digests are the same
  `digests_in_scope`    so, in scope, they are the item's reader's at the stored file's lines

Limits. Public numbers and texts alone: no run, no coin. No hash is evaluated: on both sides one
text is hashed. The format's second hash function (`OnBytes.secondHashFunction`) alone. It stands over the fact
on the
stored layout file's size, which is shown in the side library.

What is not claimed. This is none of the library's goals. Nothing on soundness, completeness or
hiding.
-/
import Johnson.AtFull.Item.ItemAtFull
import Johnson.AtFull.Public.AtX0All
import Johnson.Goal.Meaning.Pub34Scope
import Johnson.Goal.Meaning.AttScope
import Johnson.Goal.Files.FilesReadProof
import Johnson.Desc.Kinds.Law.TablesPlanInScope
import Johnson.Desc.Ok.PlanWritten.PublicAtLaws
import AtFullSide.Layout.Size

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace AtPublicFiles.Start
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Lay layout)
open OnBytes.Model.Verify (publicOf Public layerShape)
open OnBytes.Proof (callHIfNone)
open Johnson.AtFull.Item (linesW)

/-- Attention's digest of call lines is the digest of what its reader returns on the lines callA. -/
theorem config_digest {P : PolScan} {y : Lay} {s : Layer.Scales} {midQ : ℕ → ℕ}
    {c : Attention.Config} (h : Attention.config P y s midQ = .ok c) :
    ∃ lines, Attention.readLines P.polCallsA = .ok lines ∧
      c.hCallsA = Attention.callsDigest lines := by
  unfold Attention.config at h
  obtain ⟨lines, hl, h⟩ := ok_of_bind h
  obtain ⟨-, -, h⟩ := ok_of_bind h
  obtain ⟨-, -, h⟩ := ok_of_bind h
  obtain ⟨plans, -, h⟩ := ok_of_bind h
  cases plans with
  | nil => cases h
  | cons X0 rest =>
    obtain ⟨-, -, h⟩ := ok_of_bind h
    cases h
    exact ⟨lines, hl, rfl⟩

/-- **The three digests in the public part, as the text of `publicOf` forms them**, at profile 4. -/
theorem digests_of_public {pol KL : ByteArray} {lay : Option ByteArray} {X : Public}
    (h : publicOf pol KL lay = .ok X) (hp4 : (layerShape X.P).p4 = true) :
    X.digests.hCalls = Verify.callsDigest "call" X.y.calls.toList ∧
      (∃ lines, Attention.readLines X.P.polCallsA = .ok lines ∧
        X.digests.hCallsA = Attention.callsDigest lines) ∧
      X.digests.hCallsH = Verify.callsDigest "callH" X.HLy.calls.toList := by
  obtain ⟨P, y, hpl1, eP, -⟩ := Hd.public_parts h
  have hq1 : y.h.p4 = true := by
    rw [layout_shape (Hd.layerLayout_of_polLayout hpl1), ← eP]
    exact hp4
  unfold Model.Verify.publicOf at h
  obtain ⟨⟨P', y'⟩, hpl, h⟩ := ok_of_bind h
  have e : (P, y) = (P', y') := Except.ok.inj (hpl1.symm.trans hpl)
  cases e
  obtain ⟨sc, -, h⟩ := ok_of_bind h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  obtain ⟨_, h⟩ := Hd.ok_of_ite h
  repeat (obtain ⟨_, _, h⟩ := ok_of_bind h)
  dsimp only at h
  rw [if_pos hq1] at h
  obtain ⟨c, hcfg, h⟩ := ok_of_bind h
  obtain ⟨⟨A0, hC⟩, hpure, h⟩ := ok_of_bind h
  have e2 : (c.plans, c.hCallsA) = (A0, hC) := Except.ok.inj hpure
  cases e2
  obtain ⟨layers, hPub, h⟩ := ok_of_bind h
  obtain ⟨G, -, h⟩ := ok_of_bind h
  obtain ⟨seenA, -, h⟩ := ok_of_bind h
  obtain ⟨owner, -, h⟩ := ok_of_bind h
  obtain ⟨H, -, h⟩ := ok_of_bind h
  obtain ⟨-, -, h⟩ := ok_of_bind h
  cases h
  have ey : layers.y = y := Hd.pubOf_y hPub
  refine ⟨?_, config_digest hcfg, rfl⟩
  show Verify.callsDigest "call" y.calls.toList = Verify.callsDigest "call" layers.y.calls.toList
  rw [ey]

/-- **The layers' calls do not hang on the three constants of the normalisations.** The calls are
what the call lines take of the list of segments, placed; that list and the floor of a call's size
read other fields of the shape. -/
theorem calls_free {a b c a' b' c' : ℕ} {pc : List (List String)} {y y' : Lay}
    (L : layout { hKF with eps1 := a, eps2 := b, epsF := c } pc = .ok y)
    (L' : layout { hKF with eps1 := a', eps2 := b', epsF := c' } pc = .ok y') :
    y.calls = y'.calls := by
  unfold layout at L L'
  obtain ⟨y0, h0, h1⟩ := ok_of_bind L
  obtain ⟨y0', h0', h1'⟩ := ok_of_bind L'
  obtain ⟨t, ht, hc⟩ := Meaning.P34.calls_of_base h0
  obtain ⟨t', ht', hc'⟩ := Meaning.P34.calls_of_base h0'
  obtain ⟨-, fo, kbm, rfl⟩ := look_keeps h1
  obtain ⟨-, fo', kbm', rfl⟩ := look_keeps h1'
  obtain rfl : t = t' := Except.ok.inj (ht.symm.trans ht')
  exact hc.trans hc'.symm

variable {Z Z' : VerifierAndGoals.PublicFiles} {pp pp' : Inst.Model.ScalesAndPolicy} {lay lay' : Option ByteArray}
  {X X' : Public}

/-- **At two sets of public files in scope the three digests are the same.** -/
theorem digests_same (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (hZ' : VerifierAndGoals.InScope Z' = true)
    (hR' : VerifierAndGoals.readFiles Z' = .ok pp') (h' : publicOf Z'.pol Z'.KL lay' = .ok X') :
    X.digests.hCalls = X'.digests.hCalls ∧ X.digests.hCallsA = X'.digests.hCallsA ∧
      X.digests.hCallsH = X'.digests.hCallsH := by
  have Q := Meaning.P34.pub34_public hZ hR h
  have Q' := Meaning.P34.pub34_public hZ' hR' h'
  obtain ⟨d1, ⟨l, hl, d2⟩, d3⟩ := digests_of_public h Q.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨d1', ⟨l', hl', d2'⟩, d3'⟩ := digests_of_public h' Q'.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨?_, ?_, ?_⟩
  · have L := Q.1
    have L' := Q'.1
    rw [(Hd.calls_of_scope hZ hR h).1, Meaning.P34.shape_in_scope hZ hR h] at L
    rw [(Hd.calls_of_scope hZ' hR' h').1, Meaning.P34.shape_in_scope hZ' hR' h'] at L'
    rw [d1, d1', calls_free L L']
  · rw [(Hd.calls_of_scope hZ hR h).2.1] at hl
    rw [(Hd.calls_of_scope hZ' hR' h').2.1] at hl'
    obtain rfl : l = l' := Except.ok.inj (hl.symm.trans hl')
    rw [d2, d2']
  · rw [d3, d3', VerifiableInference.Desc.Kinds.Head.Law.InScope.calls_in_scope hZ hR h,
      VerifiableInference.Desc.Kinds.Head.Law.InScope.calls_in_scope hZ' hR' h']

/-- **In scope the public part's three digests are those that the item's reader forms from the
stored full-size parameter file's call lines.** -/
theorem digests_in_scope (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) :
    linesW.calls "call" = some X.digests.hCalls ∧
      linesW.calls "callA" = some X.digests.hCallsA ∧
      linesW.calls "callH" (some callHIfNone) = some X.digests.hCallsH := by
  have hsz := Johnson.Unfolds.Layout.lay_size
  obtain ⟨X₀, hX₀, -⟩ := Johnson.AtFull.Public.publicOfO_zFull_all hsz
  have hP := Johnson.AtFull.Item.parts_zFull hsz hX₀
  rw [Johnson.AtFull.Item.read_zFull] at hP
  have h₀ : publicOf VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ := by
    rw [← VerifiableInference.PlanWritten.publicOfO_older]
    exact hX₀
  obtain ⟨hZ₀, pp₀, hR₀, -⟩ := VerifierAndGoals.filesRead.full
  obtain ⟨e1, e2, e3⟩ := digests_same hZ hR h hZ₀ hR₀ h₀
  rw [e1, e2, e3]
  exact ⟨hP.call, hP.callA, hP.callH⟩

end AtPublicFiles.Start

#print axioms AtPublicFiles.Start.config_digest
#print axioms AtPublicFiles.Start.digests_of_public
#print axioms AtPublicFiles.Start.calls_free
#print axioms AtPublicFiles.Start.digests_same
#print axioms AtPublicFiles.Start.digests_in_scope
