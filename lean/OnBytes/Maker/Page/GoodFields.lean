-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/GoodFields.lean: at a good reading of a key file or of a proof file
(OnBytes/TieK/Good.lean) the three descriptions under which the chains were read hold the field in
which the program computes.

OnBytes/Maker/Page/Kits.lean gives the three descriptions' fields from the chains' parameter bytes,
and these from the program's test on the first chain's field and from one setting of the three
chains. At a good reading both lie in what the program has done (`KeyOpened`, `ProofOpened`,
OnBytes/TieK/PortChains.lean).

Main theorems.
  `setting_keyGood`, `setting_proofGood`: the test on the first chain's field (at a proof file with
    the test that the digest of the public files is not 32 zero bytes), and one setting of the three
    chains, at the chains that the planner gives for the reading's public files.
  `fields_keyGood`, `fields_proofGood`: the three fields are `.two`.
  `kits_keyGood`, `kits_proofGood`: so the kit of verifier messages as hash blocks fits them.
No letter stands under "there is" in these statements.
No other file calls `fields_keyGood`, `fields_proofGood`, `kits_keyGood` or `kits_proofGood`.

What is not claimed. That a reading is good. Nothing on soundness.


-/
import OnBytes.Maker.Page.Kits
import OnBytes.TieK.Good

set_option autoImplicit false

namespace OnBytes.Maker.Page

open _root_.Run _root_.Run.PQ
open OnBytes.TieK (KeyPub ProofPub KeyGood ProofGood SameSetting ChainsData)

/-- **A key file: the test on the field, and one setting.** -/
theorem setting_keyGood {u : KeyPub} {d : Params.TableName × ChainsData} (h : KeyGood u d)
    {p : Model.Verify.Planned} (hp : Model.Verify.planned u.pol u.KL (some u.lay) = .ok p) :
    (p.chains.key.oneTime.given.plan.field != .two) = false ∧
      SameSetting p.chains.key.oneTime.given p.chains.key.shared.given ∧
      SameSetting p.chains.key.oneTime.given p.chains.key.second.given := by
  obtain ⟨F, e1, e2, e3, ho, -⟩ := h
  obtain ⟨p', _, _, _, _, _, _, _, _, _, _, _, _, _, _, hp', -, kf, -, hf, -⟩ := ho
  rw [e1, e2, e3] at hp'
  obtain rfl : p' = p := Except.ok.inj (hp'.symm.trans hp)
  exact ⟨hf, kf.sharedSetting, kf.secondSetting⟩

/-- **A key file: the three fields.** -/
theorem fields_keyGood {u : KeyPub} {d : Params.TableName × ChainsData} (h : KeyGood u d) :
    d.2.S1.base.plan.field = .two ∧ d.2.S2.base.plan.field = .two ∧
      d.2.S3.base.plan.field = .two := by
  obtain ⟨F, p, j, real, real2, -, -, -, -, -, hp, -, -, hs, T, -⟩ := h.facts
  obtain ⟨hf, s₂, s₃⟩ := setting_keyGood h hp
  have h₁ : p.chains.key.oneTime.given.plan.field = .two := by
    simpa using hf
  obtain ⟨a₁, a₂, a₃⟩ := fields_of_read T.toRead hs
  exact ⟨a₁.trans h₁, a₂.trans (s₂.field.symm.trans h₁), a₃.trans (s₃.field.symm.trans h₁)⟩

/-- **A key file: the kit fits.** -/
theorem kits_keyGood (K : ℕ) {u : KeyPub} {d : Params.TableName × ChainsData} (h : KeyGood u d) :
    TypedOracleCompiler.Run.PQ.KitFits d.2.S1.base.plan.field (ckP .two) K (chalP .two K) ∧
      TypedOracleCompiler.Run.PQ.KitFits d.2.S2.base.plan.field (ckP .two) K (chalP .two K) ∧
      TypedOracleCompiler.Run.PQ.KitFits d.2.S3.base.plan.field (ckP .two) K (chalP .two K) := by
  obtain ⟨a₁, a₂, a₃⟩ := fields_keyGood h
  exact ⟨kit_at .two K _ a₁, kit_at .two K _ a₂, kit_at .two K _ a₃⟩

/-- **A proof file: the test on the field, and one setting.** -/
theorem setting_proofGood {u : ProofPub} {d : Params.TableName × ChainsData} (h : ProofGood u d)
    {p : Model.Verify.Planned} (hp : Model.Verify.planned u.pol u.KL (some u.lay) = .ok p) :
    (p.chains.proof.first.given.plan.field != .two ||
        p.chains.proof.first.given.cfg == Fmt.zero32) = false ∧
      SameSetting p.chains.proof.first.given p.chains.proof.shared.given ∧
      SameSetting p.chains.proof.first.given p.chains.proof.second.given := by
  obtain ⟨F, table, e1, e2, e3, -, -, -, ho, -⟩ := h
  obtain ⟨p', _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hp', -, kf, -, hf, -⟩ := ho
  rw [e1, e2, e3] at hp'
  obtain rfl : p' = p := Except.ok.inj (hp'.symm.trans hp)
  exact ⟨hf, kf.sharedSetting, kf.secondSetting⟩

/-- **A proof file: the three fields.** -/
theorem fields_proofGood {u : ProofPub} {d : Params.TableName × ChainsData} (h : ProofGood u d) :
    d.2.S1.base.plan.field = .two ∧ d.2.S2.base.plan.field = .two ∧
      d.2.S3.base.plan.field = .two := by
  obtain ⟨F, table, p, so, cov, item, links, i, real, real2, -, -, -, -, -, -, -, -, hp, -, -, -, -,
    -, -, hs, T, -⟩ := h.facts
  obtain ⟨hf, s₂, s₃⟩ := setting_proofGood h hp
  have h₁ : p.chains.proof.first.given.plan.field = .two := by
    rw [Bool.or_eq_false_iff] at hf
    simpa using hf.1
  obtain ⟨a₁, a₂, a₃⟩ := fields_of_read T.toRead hs
  exact ⟨a₁.trans h₁, a₂.trans (s₂.field.symm.trans h₁), a₃.trans (s₃.field.symm.trans h₁)⟩

/-- **A proof file: the kit fits.** -/
theorem kits_proofGood (K : ℕ) {u : ProofPub} {d : Params.TableName × ChainsData}
    (h : ProofGood u d) :
    TypedOracleCompiler.Run.PQ.KitFits d.2.S1.base.plan.field (ckP .two) K (chalP .two K) ∧
      TypedOracleCompiler.Run.PQ.KitFits d.2.S2.base.plan.field (ckP .two) K (chalP .two K) ∧
      TypedOracleCompiler.Run.PQ.KitFits d.2.S3.base.plan.field (ckP .two) K (chalP .two K) := by
  obtain ⟨a₁, a₂, a₃⟩ := fields_proofGood h
  exact ⟨kit_at .two K _ a₁, kit_at .two K _ a₂, kit_at .two K _ a₃⟩

end OnBytes.Maker.Page
