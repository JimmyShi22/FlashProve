-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/OneSetting.lean: the three chains of a key or of a proof whose parameter bytes the
verifier program has read together have one configuration's digest and one number of bytes of a
salt.

Statements and proofs. `Params.KeyChains.read` and `Params.ProofChains.read`
(OnBytes/Params/Chains.lean) refuse chains under different settings (`Params.sameSetting`). Two of
the settings are taken out here.

Main names:
  `sameSetting_spec`: what the test gives: one number of bytes of a salt, one digest.
  `OneSetting g₁ g₂ g₃ cfg sb`: the three have the digest cfg and the number sb.
  `keyChains_setting`, `proofChains_setting`: at a value of the two readers, with cfg and sb the
    shared chain's.
Limits: the program's checks `Key.check` and `Proof.check` take any three chains: that theirs are a
value of these readers is the caller's matter. Nothing on soundness.


-/
import OnBytes.Params.Chains
import Run.PageIsReaders

set_option autoImplicit false

namespace OnBytes.Maker

open _root_.Run.PQ (bytes_beq)

/-- What the test on two chains' settings gives. -/
theorem sameSetting_spec {a b : Params.Given} (h : Params.sameSetting a b = true) :
    a.plan.salt = b.plan.salt ∧ a.cfg = b.cfg := by
  unfold Params.sameSetting at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨-, hs⟩, -⟩, -⟩, -⟩, -⟩, hc⟩ := h
  exact ⟨beq_iff_eq.1 hs, bytes_beq _ _ hc⟩

/-- The three have one configuration's digest and one number of bytes of a salt. -/
structure OneSetting (g₁ g₂ g₃ : Params.Given) (cfg : ByteArray) (sb : ℕ) : Prop where
  c₁ : g₁.cfg = cfg
  c₂ : g₂.cfg = cfg
  c₃ : g₃.cfg = cfg
  s₁ : g₁.plan.salt = sb
  s₂ : g₂.plan.salt = sb
  s₃ : g₃.plan.salt = sb

theorem oneSetting_of {g₁ g₂ g₃ : Params.Given} (h₂ : Params.sameSetting g₁ g₂ = true)
    (h₃ : Params.sameSetting g₁ g₃ = true) : OneSetting g₁ g₂ g₃ g₂.cfg g₂.plan.salt := by
  obtain ⟨a1, a2⟩ := sameSetting_spec h₂
  obtain ⟨b1, b2⟩ := sameSetting_spec h₃
  exact ⟨a2, rfl, b2.symm.trans a2, a1, rfl, b1.symm.trans a1⟩

/-- **A key's three chains, as the program reads their parameter bytes together.** -/
theorem keyChains_setting {x y z : ByteArray} {k : Params.KeyChains}
    (h : Params.KeyChains.read x y z = some k) :
    OneSetting k.oneTime.given k.shared.given k.second.given k.shared.given.cfg
      k.shared.given.plan.salt := by
  unfold Params.KeyChains.read at h
  cases ha : Params.OneTime.read x with
  | none => rw [ha] at h; cases h
  | some a =>
    cases hb : Params.Shared.read y with
    | none => rw [ha, hb] at h; cases h
    | some b =>
      cases hc : Params.Second.read z with
      | none => rw [ha, hb, hc] at h; cases h
      | some c =>
        rw [ha, hb, hc] at h
        have h' : (if (Params.sameSetting a.given b.given && Params.sameSetting a.given c.given &&
            Params.sameItem a.given b.given "codes" &&
            Params.sameItem a.given b.given "the test on the table" &&
            b.given.record.isNone && c.given.record.isNone) = true
          then some (⟨a, b, c⟩ : Params.KeyChains) else none) = some k := h
        split at h'
        · rename_i hq
          obtain rfl := Option.some.inj h'
          simp only [Bool.and_eq_true] at hq
          exact oneSetting_of hq.1.1.1.1.1 hq.1.1.1.1.2
        · cases h'

/-- **A proof's three chains, as the program reads their parameter bytes together.** -/
theorem proofChains_setting {x y z : ByteArray} {c : Params.ProofChains}
    (h : Params.ProofChains.read x y z = some c) :
    OneSetting c.first.given c.shared.given c.second.given c.shared.given.cfg
      c.shared.given.plan.salt := by
  unfold Params.ProofChains.read at h
  cases ha : Params.First.read x with
  | none => rw [ha] at h; cases h
  | some a =>
    cases hb : Params.Shared.read y with
    | none => rw [ha, hb] at h; cases h
    | some b =>
      cases hc : Params.Second.read z with
      | none => rw [ha, hb, hc] at h; cases h
      | some d =>
        rw [ha, hb, hc] at h
        have h' : (if (Params.sameSetting a.given b.given && Params.sameSetting a.given d.given &&
            Params.sameItem a.given b.given "codes" &&
            Params.sameItem a.given b.given "the test on the table" &&
            b.given.record.isNone && d.given.record.isNone) = true
          then some (⟨a, b, d⟩ : Params.ProofChains) else none) = some c := h
        split at h'
        · rename_i hq
          obtain rfl := Option.some.inj h'
          simp only [Bool.and_eq_true] at hq
          exact oneSetting_of hq.1.1.1.1.1 hq.1.1.1.1.2
        · cases h'

end OnBytes.Maker
