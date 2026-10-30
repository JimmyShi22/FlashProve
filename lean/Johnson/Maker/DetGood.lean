-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Maker/DetGood.lean: `key_det_at` and `proof_det_at`
(OnBytes/TypedOracleCompiler/Joined/K/LeftOfChains.lean) for any predicate on readings.

These two theorems ask the seventeen hypotheses of `LeftHoles` of ALL good readings at the public
input: of every file that the program accepts there, whoever wrote it. A hypothesis that holds of
the file at hand and fails at another accepted file then makes the whole statement idle.
`LeftHoles` and `yes_of_leftHoles` take any predicate. So here the caller lays a predicate Good, the
hypotheses are asked of the readings that meet it, and the yes is concluded if the reading of the
file at hand meets it.

  `key_det_good`     a key file: the fixed reading returns data d, with the stored copy's number 0;
                     it is a good reading; and if it meets Good, the compiled verifier has the value
                     yes
  `proof_det_good`   the like for a proof file

The proofs are those of `key_det_at` and `proof_det_at`, with the predicate's proof taken from the
caller.

Not claimed. Any hypothesis of `LeftHoles`. Nothing on soundness.


-/
import OnBytes.TypedOracleCompiler.Joined.K.LeftOfChains

set_option autoImplicit false

namespace OnBytes.Maker

open TypedOracleCompiler.Joined.K OnBytes.TieK

/-- **A key file, at any predicate on readings.** -/
theorem key_det_good (T : TypingA) (F : OnBytes.K.Files) (Good : Dat → Prop)
    (H : LeftHoles T Good (keyShape ⟨F.pol, F.lay, F.KL⟩) (keyCfg ⟨F.pol, F.lay, F.KL⟩))
    (id : String) (table further : Params.TableName)
    (h : OnBytes.K.PortYesAt F id table further) :
    ∃ d, readKeyChains F.pol F.lay F.KL F.key = some (table, d) ∧ d.copy = 0 ∧
      KeyGood ⟨F.pol, F.lay, F.KL⟩ (table, d) ∧
      (Good (table, d) →
        (T.F.verify T.sMT T.sFS (T.cmsAt (table, d)) (T.xAt (table, d))
          (T.prf (table, d))).det T.g = true) := by
  have ho := port_key_chains F id table further h
  obtain ⟨p, _, d, _, _, hp, -, hd, -, h3, sf, hc⟩ := readKeyChains_of F table ho
  have e1 : keyShape ⟨F.pol, F.lay, F.KL⟩ = p.chains.key.oneTime.binding := by
    unfold keyShape
    rw [hp]
  have e2 : keyCfg ⟨F.pol, F.lay, F.KL⟩ = p.chains.key.shared.given.cfg := by
    unfold keyCfg
    rw [hp]
  refine ⟨d, hd, hc, ⟨F, rfl, rfl, rfl, ho, hd⟩, fun hg =>
    yes_of_leftHoles T Good _ _ H (table, d) hg F.key d.r.first.next ?_ h3.seal1_size⟩
  rw [e1, e2]
  exact sf

/-- **A proof file, at any predicate on readings.** -/
theorem proof_det_good (T : TypingA) (F : OnBytes.K.Files) (Good : Dat → Prop)
    (H : LeftHoles T Good (proofShape ⟨F.pol, F.lay, F.KL, F.request, F.y⟩)
      (proofCfg ⟨F.pol, F.lay, F.KL, F.request, F.y⟩))
    (id : String) (table further : Params.TableName)
    (h : OnBytes.K.PortYesAt F id table further) :
    ∃ d, readProofChains F.pol F.lay F.KL F.request F.y F.ent F.entry F.proof =
        some (further, d) ∧ d.copy = F.entry ∧
      ProofGood ⟨F.pol, F.lay, F.KL, F.request, F.y⟩ (further, d) ∧
      (Good (further, d) →
        (T.F.verify T.sMT T.sFS (T.cmsAt (further, d)) (T.xAt (further, d))
          (T.prf (further, d))).det T.g = true) := by
  have ho := port_proof_chains F id table further h
  have he := port_entry F id table further h
  obtain ⟨p, _, _, _, _, _, d, _, _, hp, -, -, -, -, -, hd, -, h3, sf, hc⟩ :=
    readProofChains_of F table further he ho
  have e1 : proofShape ⟨F.pol, F.lay, F.KL, F.request, F.y⟩ = p.chains.proof.first.binding := by
    unfold proofShape
    rw [hp]
  have e2 : proofCfg ⟨F.pol, F.lay, F.KL, F.request, F.y⟩ = p.chains.proof.shared.given.cfg := by
    unfold proofCfg
    rw [hp]
  refine ⟨d, hd, hc, ⟨F, table, rfl, rfl, rfl, rfl, rfl, he, ho, hd⟩, fun hg =>
    yes_of_leftHoles T Good _ _ H (further, d) hg F.proof d.r.first.next ?_ h3.seal1_size⟩
  rw [e1, e2]
  exact sf

end OnBytes.Maker
