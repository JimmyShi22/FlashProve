-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Dec/SoundAtOfWritten.lean: THE ENTRY FILE: FROM "the library's written link, AT A DECISION THAT IS A LETTER, is round-by-round
sound at each instance's pair of records" TO THE FRAME's NAMED PREMISE `SoundAt … decE` (OnBytes/Flat/LinkSib.lean), at the written rounds of
both sizes. Theorems with their proofs.

Why. The library's statements on that stretch (`row13_of`, `fr_row13`, `fr_row13_key`, `soundAt_full` and their small twins:
OnBytes/TypedOracleCompiler/Slice/EntryRow13.lean, EntryRow13JohFull.lean, OnBytes/Flat/LinkSibAt.lean) CONCLUDE AT verify-on-bytes's DECISION
(`(linkVerify …).decides`) and take their premise in the form "the decision's yes gives `linkVerify`'s yes". The frame with the entry
file's three letters asks `SoundAt` at a letter. BENEATH THE FOUR, THE LIBRARY's CARRIER IS GENERAL IN THE DECISION ALREADY
(`entry_hS`, OnBytes/TypedOracleCompiler/Slice/EntryFromLink.lean; `soundAt_at`): so the stretch is said again at a letter by one call of each: no run of
`linkVerify` stands in a statement or a proof here.

Main names (small for full at the small example).
  `soundAt_full_of_written`: any decision decE; any list of counts ε below κ.
  `soundAt_full_of_joh`: at the library's own list of counts: κ := 2^-128, work counted.
  (With `entrySoundOfFullD` | `SmallD` and `SoundAt.mono`: `CompilerSoundnessConditionStatements.entrySound` at the frame with ds := `dsFull`, xs := `frD.xs`, dec := `decOfXFull decE`,
    where 2^-128 ≤ T.εs: two calls; not typed here.)
  `soundAt_full_again`: A CONTROL: the library's `soundAt_full` comes back at decE := `decFullX` by the library's own `fr_link_sound`: the new
    statement's premise H is met where the library's stands.

Every "there is", walked. `SoundAt` begins "there is a list of counts": it is ε carried to the sibling's shape (`entry_hS`'s proof). None else.
THE TWO SILLY MEMBERS. decE := yes to all: H is then false at every ε below a small κ wherever some pair of records and tables is outside the
language [an argument; no theorem]. decE := no to all: H holds for nothing, and the conclusion is of a link that refuses all.

Limits. CONDITIONALS: H IS THE WHOLE LOAD: the theorem on codes, the five rounds' and the proximity test's laws AT THE NEW DECISION stand inside
it: it is shown here of no decision but verify-on-bytes's (the control). The rounds' data are the WRITTEN ones: at other data nothing.
The bound 2^-128 counts work. Nothing on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.Dec.EntrySound

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Flat
open OnBytes.Slice TypedOracleCompiler.Slice TypedOracleCompiler.Run OnBytes.Tie
open OnBytes.Params (recordRead smallRecordRead)
open _root_.Iop (Err InteractiveOracleProof twoExternalStrings)
open _root_.Run (ckP)
open _root_.Run.PQ (View SgX)
open scoped ENNReal

/-! ## The full size -/

set_option maxRecDepth 40000 in
/-- **From the library's written link at a letter to the frame's named premise.** decE: any decision, instance by
instance. H: at each instance's pair of records the library's written link AT THAT DECISION is round-by-round sound
for the entry's language, with one list of counts ε; hb: each count, as a share, is at most κ. -/
theorem soundAt_full_of_written (decE : XE AnsT 29 1 → View → Bool) (κ : ℝ≥0∞)
    (ε : Err (written frS (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frRd 5 :: frC.rds) frD.xs
      fun _ => true).shape) (hb : Err.Below ε κ)
    (H : ∀ x, (written frS (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frRd 5 :: frC.rds) frD.xs
        (decE x)).Sound
      (fun _ y => frS.LangE2T frZ 402653181 (recOf frS 29 1 (anT frS.P.v 1) x) y) ε) :
    SoundAt frS.P.T frS.P.v frS.eM 29 1 decE κ (ckP .two) dsFull frS.P.T.a frD.xs := by
  obtain ⟨hf, hds, ha, hxs⟩ := full_four ByteArray.empty
  have h := soundAt_at frS.P.T frS.P.v frS.eM 29 1 decE κ (entryXD recordGround ByteArray.empty)
    (entry_hS frS 29 1 (anT frS.P.v 1) (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frRd 5 :: frC.rds)
      frD.xs _ hf hds ha hxs decE ε κ hb H)
  rw [(letters_full ByteArray.empty).1, hds, ← dsFull_eq, ha, hxs] at h
  exact h

/-- **The same at the library's own list of counts** (that of the conclusion of its theorem on the link's chain), which
is below 2^-128, work counted (`fr_err_below`). -/
theorem soundAt_full_of_joh (decE : XE AnsT 29 1 → View → Bool)
    (H : ∀ x, (written frS (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frRd 5 :: frC.rds) frD.xs
        (decE x)).Sound
      (fun _ y => frS.LangE2T frZ 402653181 (recOf frS 29 1 (anT frS.P.v 1) x) y)
      (0, coreErrR frS frZ (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frS.badJ frS.e0)
        (frS.badJ frS.e1)
        (fun _ => Cb.listMax (2 ^ frS.P.C.a) (2 ^ frS.P.C.a - (frS.P.C.r + frS.P.C.l) + 1) frS.eU)
        (batErrR frN ((frS.sg 97).lstJ frC.rad) (frRd 5), frC.errL))) :
    SoundAt frS.P.T frS.P.v frS.eM 29 1 decE (((2 : ℝ≥0∞)⁻¹) ^ 128) (ckP .two) dsFull frS.P.T.a
      frD.xs :=
  soundAt_full_of_written decE _ _ (fr_err_below frD.xs fun _ => true) H

set_option maxRecDepth 100000 in
/-- A CONTROL: the library's statement comes back. -/
theorem soundAt_full_again (hA : Cb.BCHKS46At GF GE) :
    SoundAt frS.P.T frS.P.v frS.eM 29 1 decFullX (((2 : ℝ≥0∞)⁻¹) ^ 128) (ckP .two) dsFull
      frS.P.T.a frD.xs :=
  soundAt_full_of_joh decFullX fun x =>
    fr_link_sound (keysOfX frS.P.v 29 1 (anT frS.P.v 1) x).1 (keysOfX frS.P.v 29 1 (anT frS.P.v 1) x).2
      rfl rfl frD.xs _ (fun _ h => h) (recOf frS 29 1 (anT frS.P.v 1) x)
      (fun _ _ => keyHasR_keyOf (recOf frS 29 1 (anT frS.P.v 1) x).1 _ rfl rfl Shapes.zFull_lg 0)
      (fun _ _ => keyHasR_keyOf (recOf frS 29 1 (anT frS.P.v 1) x).2 _ rfl rfl Shapes.zFull_lg 1) hA

/-! ## The small example -/

set_option maxRecDepth 40000 in
/-- **From the library's written link at a letter to the frame's named premise.** decE: any decision, instance by
instance. H: at each instance's pair of records the library's written link AT THAT DECISION is round-by-round sound
for the entry's language, with one list of counts ε; hb: each count, as a share, is at most κ. -/
theorem soundAt_small_of_written (decE : XE AnsT 19 1 → View → Bool) (κ : ℝ≥0∞)
    (ε : Err (written srS (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srRd 5 :: srC.rds) srD.xs
      fun _ => true).shape) (hb : Err.Below ε κ)
    (H : ∀ x, (written srS (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srRd 5 :: srC.rds) srD.xs
        (decE x)).Sound
      (fun _ y => srS.LangE2T srZ 524285 (recOf srS 19 1 (anT srS.P.v 1) x) y) ε) :
    SoundAt srS.P.T srS.P.v srS.eM 19 1 decE κ (ckP .two) dsSmall srS.P.T.a srD.xs := by
  obtain ⟨hf, hds, ha, hxs⟩ := small_four ByteArray.empty
  have h := soundAt_at srS.P.T srS.P.v srS.eM 19 1 decE κ (entryXD smallRecordGround ByteArray.empty)
    (entry_hS srS 19 1 (anT srS.P.v 1) (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srRd 5 :: srC.rds)
      srD.xs _ hf hds ha hxs decE ε κ hb H)
  rw [(letters_small ByteArray.empty).1, hds, ← dsSmall_eq, ha, hxs] at h
  exact h

/-- **The same at the library's own list of counts** (that of the conclusion of its theorem on the link's chain), which
is below 2^-128, work counted (`sr_err_below`). -/
theorem soundAt_small_of_joh (decE : XE AnsT 19 1 → View → Bool)
    (H : ∀ x, (written srS (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srRd 5 :: srC.rds) srD.xs
        (decE x)).Sound
      (fun _ y => srS.LangE2T srZ 524285 (recOf srS 19 1 (anT srS.P.v 1) x) y)
      (0, coreErrR srS srZ (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srS.badJ srS.e0)
        (srS.badJ srS.e1)
        (fun _ => Cb.listMax (2 ^ srS.P.C.a) (2 ^ srS.P.C.a - (srS.P.C.r + srS.P.C.l) + 1) srS.eU)
        (batErrR srN ((srS.sg 97).lstJ srC.rad) (srRd 5), srC.errL))) :
    SoundAt srS.P.T srS.P.v srS.eM 19 1 decE (((2 : ℝ≥0∞)⁻¹) ^ 128) (ckP .two) dsSmall srS.P.T.a
      srD.xs :=
  soundAt_small_of_written decE _ _ (sr_err_below srD.xs fun _ => true) H

end OnBytes.Flat

#print axioms OnBytes.Flat.soundAt_full_of_written
#print axioms OnBytes.Flat.soundAt_full_of_joh
#print axioms OnBytes.Flat.soundAt_full_again
#print axioms OnBytes.Flat.soundAt_small_of_written
#print axioms OnBytes.Flat.soundAt_small_of_joh
