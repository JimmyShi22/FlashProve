-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/E/KObj/KeyFile.lean: the soundness of the key file's protocol from the blocks of two typed
lists.

An object's key-file protocol is "the weights are well formed; then the test at one instance"
(`SubsR.wf`, `SubsR.linOff`, Hiop/RecSubs.lean). Here both are typed lists of bare blocks
(Johnson/E/KObj/Obj.lean). Definitions and proofs, by `rec_sndT_ofK`
(Cb/Thin/Cond/TargetSoundOnly.lean) and the rule for lists (`LK.good`). No library file turns.
Main names:
  `Obj.KeyBlocks`: the hypotheses: every block of each of the two lists has its property.
  `Obj.key_know`: the two items on knowledge soundness of the key file.
  `Obj.key_sndT`: the key file's protocol is round-by-round sound for "the word has a collision at
    the record's seed, or decodes with the record", at the two lists' errors in a row.
  `Obj.keySound_lhr`: the hypothesis `HoleAt.keySound` of Johnson/Top/OnFilesAt.lean , in its own
    words, at L := `(O.S H).lhr`, if every error of both lists is at most εs.
  `Obj.keySound_lhrW`: the same at the passed object `(O.S H).lhrW Nn σT σL σB g`, at εs := κs · κ,
    if σT is good at κs and the two lists' errors, with the work counted, are at most κ.
  `Obj.key_local`: the hypothesis `HoleAt.keyLocal` at `(O.S H).lhr`.
Limits: of the object's other lists (entry file, proof file), of the batch test and of every honest
side nothing is asked. It does not say that any object is the protocol that the programs run, or
that any block has its property.

-/
import Johnson.E.KObj.Obj
import Cb.Thin.Cond.TargetSoundOnly
import Johnson.RecCompile.Join

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace KObj
open Iop Prob Hiop Compile Compile.Batch Compile.Batch.Cms
open scoped ENNReal

/-- THE KEY FILE's NAMED HYPOTHESES -/
structure Obj.KeyBlocks (O : Obj) : Prop where
  /-- «the weights are well formed»: every block has its property -/
  wf     : O.wf.Each PG
  /-- the test at one instance: every block has its property -/
  linOff : O.linOff.Each PG

/-- the two «know» items of the key file, from the blocks -/
theorem Obj.key_know (O : Obj) (H : O.Hon) (h : O.KeyBlocks) :
    PreKnowR (O.S H).off (O.S H).wf O.C.free O.C.RwfR (fun _ _ _ => ()) (O.P H).wf.err ∧
      LinKnowR (O.S H).off (O.S H).linOff (O.S H).dOff (O.P H).linOff.err := by
  refine ⟨(O.wf.good () h.wf).know, ?_⟩
  have g := (know_of_knowInto _ _ _ _ _ _ _ _ _ _).1 (O.linOff.good O.dOff h.linOff).know
  refine know_of_det _ _ _ _ _ _ _ _ _ _ (fun a => O.off.decA O.dOff a.1.1 a.2.2) ?_ g
  rintro a w - ⟨U, -, h2, -⟩
  show w = (O.off.adec a.1.1 a.2.2).getD O.dOff
  rw [h2]
  rfl

/-- (K1) -/
theorem Obj.key_sndT (O : Obj) (H : O.Hon) (h : O.KeyBlocks) :
    (O.S H).lhr.offline.Sound
      (fun rec y => (O.S H).lhr.hasCollisionAt y rec.1 ∨ (O.S H).lhr.decodeIndex y rec ≠ none)
      (Err.app (O.P H).wf.err (O.P H).linOff.err) :=
  rec_sndT_ofK O.C (O.S H) (O.P H) (O.key_know H h).1 (O.key_know H h).2

/-- (K2) the top's hole «keySound», in its own words, at the object's L -/
theorem Obj.keySound_lhr (O : Obj) (H : O.Hon) (h : O.KeyBlocks) (εs : ℝ≥0∞)
    (b1 : Err.Below (O.wf.blk ()).err εs) (b2 : Err.Below (O.linOff.blk O.dOff).err εs) :
    ∃ ε, Err.Below ε εs ∧ (O.S H).lhr.offline.Sound
      (fun rec y => (O.S H).lhr.hasCollisionAt y rec.1 ∨ (O.S H).lhr.decodeIndex y rec ≠ none) ε :=
  ⟨Err.app (O.P H).wf.err (O.P H).linOff.err, Err.Below.app b1 b2, O.key_sndT H h⟩

/-- (K2′) the top's hole «keySound», in its own words, at the passed object -/
theorem Obj.keySound_lhrW (O : Obj) (H : O.Hon) (h : O.KeyBlocks) (Nn : Type) [Inhabited Nn]
    (σT : Samplers (O.S H).lhr.offline.shape) (σL : Samplers (O.S H).lhr.link.shape)
    (σB : Samplers (O.S H).lhr.onlineBatch.loc.shape) (g : (O.S H).Bits) (κs Kt κ : ℝ≥0∞)
    (gdT : σT.Good κs Kt) (b1 : Err.BelowG g.wf (O.wf.blk ()).err κ)
    (b2 : Err.BelowG g.linOff (O.linOff.blk O.dOff).err κ) :
    ∃ ε, Err.Below ε (κs * κ) ∧ ((O.S H).lhrW Nn σT σL σB g).offline.Sound
      (fun rec y => ((O.S H).lhrW Nn σT σL σB g).hasCollisionAt y rec.1 ∨
        ((O.S H).lhrW Nn σT σL σB g).decodeIndex y rec ≠ none) ε :=
  ⟨_, (Err.below_grind_iff _ _ _).2 (Err.BelowG.pull gdT
      ((belowG_app _ _ g.wf g.linOff (O.P H).wf.err (O.P H).linOff.err κ).2 ⟨b1, b2⟩)),
    ((O.key_sndT H h).pull gdT.fib).grind (g.TR.pull _)⟩

/-- (K3) the top's hole «keyLocal» at the object's L -/
theorem Obj.key_local (O : Obj) (H : O.Hon) (h : O.KeyBlocks) : (O.S H).lhr.offline.IsLocal :=
  Iop.isLocal_toProto _ _ _ (Iop.isLocal_seq _ _ _ _ _ _ _ _ (O.wf.good () h.wf).isLocal
    (O.linOff.good O.dOff h.linOff).isLocal)

#print axioms KObj.Obj.key_sndT
#print axioms KObj.Obj.keySound_lhr
#print axioms KObj.Obj.keySound_lhrW
#print axioms KObj.Obj.key_local

end KObj
