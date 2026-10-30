-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ScalesSame.lean: two readings of the scale file give one table of scales.

scalesOfFiles policy KL (Johnson/Flat/ScalesOf.lean) reads the library's record of public numbers
off the bytes of the scale file and the parameter file, by the format's page. scalesAt X
(Johnson/Flat/ScalesAt.lean) takes the words that the verifier's own reader of the scale file has
laid into the public part X (Model.Layer.scalesOf on Model.fileWords KL, inside publicOf).

Main theorems:
  klWord_lt: a word of a file of 32-bit words is below 2^32.
  word_same: word i of words32, as a number, is word i of fileWords.
  scalesOfFiles_parts: what scalesOfFiles returns: the words and the final normalisation of the
    record klFileOf at the scan of the parameter file.
  scalesAt_eq: if publicOf returns X on the two files and scalesOfFiles returns s on the same two
    files, at profile 4 and 48 layers: s = scalesAt X.
So the table that scalesOfFiles returns, which is lawful (scalesOfFiles_lawful), is the table of the
words that the verifier program itself reads.

Limits: nothing on a protocol. Profile 4 and 48 layers are premises (public numbers of the parameter
file). No pair of files is shown at which both readers return: the theorem is applied nowhere. It
can apply only at a parameter file with 48 layers and the sizes that sizesAt asks; not at the small
configuration. Nothing on the five fixed tables of the integer model.

-/
import Johnson.Flat.ScalesOf
import Johnson.Flat.ScalesAt
import OnBytes.Model.VerifyStages

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.OnPublicFiles.Flat

open Inst.Model
open OnBytes OnBytes.Road
open OnBytes.Model.Verify (Public publicOf layerShape)

/-- n bytes as a number are below 256^n. -/
theorem leNat_lt (b : ByteArray) : ∀ (n i : ℕ), Fmt.leNat b i n < 256 ^ n
  | 0, _ => Nat.one_pos
  | n + 1, i => by
    have h1 := leNat_lt b n (i + 1)
    have h2 : (Fmt.byteAt b i).toNat < 256 := (Fmt.byteAt b i).toNat_lt
    show (Fmt.byteAt b i).toNat + 256 * Fmt.leNat b (i + 1) n < 256 ^ (n + 1)
    rw [pow_succ]
    generalize (256 : ℕ) ^ n = X at h1 ⊢
    omega

/-- A word of a file of 32-bit words is below 2^32. -/
theorem klWord_lt (KL : ByteArray) (i : ℕ) : Model.klWord KL i < 2 ^ 32 := by
  unfold Model.klWord
  split
  · exact lt_of_lt_of_eq (leNat_lt KL 4 (4 * i)) (by norm_num)
  · norm_num

/-- Word i of words32, as a number, is word i of fileWords. -/
theorem word_same (KL : ByteArray) (i : ℕ) :
    ((Model.Verify.words32 KL).getD i 0).toNat = (Model.fileWords KL).getD i 0 := by
  unfold Model.Verify.words32 Model.fileWords
  by_cases hi : i < KL.size / 4
  · have e1 : (((Array.range (KL.size / 4)).map (Model.klWord KL)).map (·.toUInt32)).getD i 0 =
        (Model.klWord KL i).toUInt32 := by simp [Array.getD, hi]
    have e2 : ((Array.range (KL.size / 4)).map (Model.klWord KL)).getD i 0 = Model.klWord KL i := by
      simp [Array.getD, hi]
    rw [e1, e2]
    show (UInt32.ofNat (Model.klWord KL i)).toNat = _
    rw [UInt32.toNat_ofNat']
    exact Nat.mod_eq_of_lt (klWord_lt KL i)
  · have e1 : (((Array.range (KL.size / 4)).map (Model.klWord KL)).map (·.toUInt32)).getD i 0 =
        0 := by simp [Array.getD, hi]
    have e2 : ((Array.range (KL.size / 4)).map (Model.klWord KL)).getD i 0 = 0 := by
      simp [Array.getD, hi]
    rw [e1, e2]
    rfl

/-- The fields of the record that klFileOf returns. -/
theorem klFileOf_fields {h : Model.Hdr} {KL : ByteArray} {f : KLFile}
    (hf : OnBytes.Flat.klFileOf h KL = some f) :
    (∀ (L : Fin 48) (j : Fin 13), L.val < h.L →
      f.lay L j = ((Model.Verify.words32 KL).getD (13 * L.val + j.val) 0).toNat) ∧
    (∀ (e : Fin 24) (j : Fin 3), 2 * e.val + 1 < h.L →
      f.moe e j = ((Model.Verify.words32 KL).getD (13 * h.L + 3 * e.val + j.val) 0).toNat) ∧
    f.eps1 = h.eps.getD 0 0 ∧ f.eps2 = h.eps.getD 1 0 ∧ f.MF = h.MF ∧ f.KF = h.KF ∧
    f.epsF = h.epsF := by
  unfold OnBytes.Flat.klFileOf at hf
  dsimp only at hf
  split at hf
  · cases hf
    exact ⟨fun L j hL => if_pos hL, fun e j he => if_pos he, rfl, rfl, rfl, rfl, rfl⟩
  · cases hf

/-- What scalesOfFiles returns. -/
theorem scalesOfFiles_parts {policy KL : ByteArray} {s : Cm.Scales}
    (h : OnBytes.Flat.scalesOfFiles policy KL = .ok s) :
    ∃ (P : Model.PolScan) (f : KLFile), Model.polScan policy = .ok P ∧
      OnBytes.Flat.klFileOf P.h KL = some f ∧ s = ⟨f.words, ⟨f.MF, f.KF, f.epsF⟩⟩ := by
  unfold OnBytes.Flat.scalesOfFiles at h
  cases h1 : OnBytes.Flat.settingsOfFiles policy KL with
  | error e =>
    rw [h1] at h
    cases h
  | ok pp =>
    rw [h1] at h
    have hs : Cm.Scales.of pp = s := Except.ok.inj h
    unfold OnBytes.Flat.settingsOfFiles at h1
    obtain ⟨_, -, h1⟩ := ok_of_bind h1
    obtain ⟨P, hP, h1⟩ := ok_of_bind h1
    cases h3 : (OnBytes.Flat.klFileOf P.h KL).bind ofKL with
    | none =>
      rw [h3] at h1
      cases h1
    | some q =>
      rw [h3] at h1
      have h4 : (if Lawful q then (pure q : Except String ScalesAndPolicy) else throw "scales-not-lawful") =
          .ok pp := h1
      split at h4
      · have e : q = pp := Except.ok.inj h4
        subst e
        cases hf : OnBytes.Flat.klFileOf P.h KL with
        | none =>
          rw [hf] at h3
          cases h3
        | some f =>
          rw [hf] at h3
          have h5 : ofKL f = some q := h3
          unfold ofKL at h5
          split at h5
          · have e2 := Option.some.inj h5
            refine ⟨P, f, hP, hf, ?_⟩
            rw [← hs, ← e2]
            rfl
          · cases h5
      · cases h4

/-- The scan of the parameter file inside polLayout. -/
theorem polScan_of_polLayout {pol : ByteArray} {P : Model.PolScan} {y : Model.Layer.Lay}
    (hpl : Model.Verify.polLayout pol = .ok (P, y)) : Model.polScan pol = .ok P := by
  unfold Model.Verify.polLayout at hpl
  obtain ⟨P0, hP0, hpl⟩ := ok_of_bind hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨y0, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  cases hpl
  exact hP0

/-- Two records with the same layers' words, experts' words and norms' constants have the same
words. -/
theorem words_congr {f g : KLFile} (h1 : ∀ L j, f.lay L j = g.lay L j)
    (h2 : ∀ e j, f.moe e j = g.moe e j) (h3 : f.eps1 = g.eps1) (h4 : f.eps2 = g.eps2) :
    f.words = g.words := by
  funext L
  unfold KLFile.words
  simp only [h1, h2, h3, h4]

/-- **The two readings of the scale file give one table of scales.** -/
theorem scalesAt_eq {pol KL : ByteArray} {lay : Option ByteArray} {X : Public} {s : Cm.Scales}
    (h : publicOf pol KL lay = .ok X) (hs : OnBytes.Flat.scalesOfFiles pol KL = .ok s)
    (hp4 : (layerShape X.P).p4 = true) (hL : X.P.h.L = 48) : s = scalesAt X := by
  obtain ⟨P, f, hP, hf, rfl⟩ := scalesOfFiles_parts hs
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

end VerifiableInference.OnPublicFiles.Flat

#print axioms VerifiableInference.OnPublicFiles.Flat.word_same
#print axioms VerifiableInference.OnPublicFiles.Flat.scalesOfFiles_parts
#print axioms VerifiableInference.OnPublicFiles.Flat.scalesAt_eq
