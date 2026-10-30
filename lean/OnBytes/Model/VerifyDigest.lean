-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/VerifyDigest.lean: the parameters of the chains, as a call reads them back, hold the
digest of the call's three configuration files.

`planned` (OnBytes/Model/Verify.lean) forms the digest of the three configuration files, has the
parameter bytes of the seven chains spelled under it, and reads these bytes back. The checks of the
key file, the entry file and the proof file use the digest in what was read back. This file proves
that it is the digest in what `planned` returns, for chains whose parameter bytes are fewer than
2^64. That the digest in that value is `Params.configurationDigest` of the three files is a clause
of `planned_entry` (OnBytes/Model/VerifyDerives.lean).

Main theorems.
- `configurationDigest_size`: the digest has 32 bytes.
- `planned_spelled`: the parameter bytes of each of the seven chains in p are spelled under the
  digest in p.
- `planned_link_cfg`, `planned_key_cfg`, `planned_proof_cfg`: the digest that the entry's chain, the
  key's three chains and the proof's three chains hold as read back is the digest in p, if the
  parameter bytes of the entry's chain, of the key's one-time chain and of the proof's first chain
  are fewer than 2^64.

What is not claimed. Nothing on soundness. Of the hash nothing is proved but the digest's length.
Nothing says that `planned` returns a value on some files. That the checks take the digest of the
three configuration files, and the shape of the tables, from nowhere but their chains is read off
the code and is no theorem. The item that `Proof.requestItem` forms holds further digests, of the
scale file, of lines of the parameter file and of the request, by another hash, and four of public
tables, copied from the parameter file's lines: nothing is said of them here. Nothing on the other
values that are read back; for the shape of the stored tables see OnBytes/Model/VerifyShape.lean.
The bound on the parameter bytes is a hypothesis here; OnBytes/Tie/SameChains.lean takes it from a
yes of the checks. For proofs only; the program does not import this file.
-/
import OnBytes.Model.VerifyDerives
import OnBytes.Params.ReadBackLaws
import OnBytes.Hash.HEq
import Fmt.Rules23Laws

set_option autoImplicit false

namespace OnBytes.Params

/-- The digest of the public files, which for a call on a model's files are the three configuration
files, has 32 bytes. -/
theorem configurationDigest_size (files : List ByteArray) :
    (configurationDigest files).size = 32 := by
  unfold configurationDigest
  rw [formatHashFastForm_eq_formatHash]
  exact Fmt.size_H 169 0 2 Fmt.zero32 (Fmt.configBytes files)

/-- The parameter bytes of all seven chains that `configure` returns are spelled under the digest
that it was given. -/
theorem configure_spelled {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : Nat}
    {made : Configured} (h : configure l x cfg bits = .ok made) :
    (∃ P I, made.keyOneTime = Fmt.paramsBytes P cfg I) ∧
      (∃ P I, made.keyShared = Fmt.paramsBytes P cfg I) ∧
      (∃ P I, made.keySecond = Fmt.paramsBytes P cfg I) ∧
      (∃ P I, made.entryLink = Fmt.paramsBytes P cfg I) ∧
      (∃ P I, made.first = Fmt.paramsBytes P cfg I) ∧
      (∃ P I, made.shared = Fmt.paramsBytes P cfg I) ∧
      (∃ P I, made.second = Fmt.paramsBytes P cfg I) := by
  unfold configure at h
  obtain ⟨z, _, h⟩ := exc_bind h
  obtain ⟨proof, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨entry, _, h⟩ := exc_bind h
  split at h
  · obtain ⟨_, _, h⟩ := exc_bind h
    replace h := exc_guard h
    replace h := exc_guard h
    replace h := exc_guard h
    replace h := exc_guard h
    replace h := exc_guard h
    replace h := exc_guard h
    replace h := exc_guard h
    cases h
    exact ⟨⟨_, _, rfl⟩, ⟨_, _, rfl⟩, ⟨_, _, rfl⟩, ⟨_, _, rfl⟩, ⟨_, _, rfl⟩, ⟨_, _, rfl⟩,
      ⟨_, _, rfl⟩⟩
  · cases h

/-- What `Link.read` returns holds what `Given.read` returns on the same bytes. -/
theorem Link.read_given {b : ByteArray} {q : Link} (h : Link.read b = some q) :
    Given.read b = some q.given := by
  unfold Link.read at h
  obtain ⟨g, hg, h⟩ := opt_bind h
  rw [hg]
  split at h
  · obtain ⟨_, _, h⟩ := opt_bind h
    obtain ⟨_, _, h⟩ := opt_bind h
    cases h
    rfl
  · cases h

/-- The same for `OneTime.read`. -/
theorem OneTime.read_given {b : ByteArray} {q : OneTime} (h : OneTime.read b = some q) :
    Given.read b = some q.given := by
  unfold OneTime.read at h
  obtain ⟨g, hg, h⟩ := opt_bind h
  rw [hg]
  split at h
  · obtain ⟨_, _, h⟩ := opt_bind h
    obtain ⟨_, _, h⟩ := opt_bind h
    obtain ⟨_, _, h⟩ := opt_bind h
    obtain ⟨_, _, h⟩ := opt_bind h
    obtain ⟨_, _, h⟩ := opt_bind h
    cases h
    rfl
  · cases h

/-- The same for `First.read`. -/
theorem First.read_given {b : ByteArray} {q : First} (h : First.read b = some q) :
    Given.read b = some q.given := by
  unfold First.read at h
  obtain ⟨g, hg, h⟩ := opt_bind h
  rw [hg]
  split at h
  · obtain ⟨_, _, h⟩ := opt_bind h
    obtain ⟨_, _, h⟩ := opt_bind h
    obtain ⟨_, _, h⟩ := opt_bind h
    obtain ⟨_, _, h⟩ := opt_bind h
    obtain ⟨_, _, h⟩ := opt_bind h
    obtain ⟨_, _, h⟩ := opt_bind h
    obtain ⟨_, _, h⟩ := opt_bind h
    dsimp only at h
    split at h
    · cases h
      rfl
    · cases h
  · cases h

/-- Two byte strings that the test `==` finds equal are equal. -/
theorem bytes_of_beq {a b : ByteArray} (h : (a == b) = true) : a = b := by
  cases a with
  | mk x =>
    cases b with
    | mk y =>
      have h' : (x == y) = true := by
        simpa [BEq.beq, ByteArray.instBEq.beq] using h
      rw [beq_iff_eq.1 h']

/-- Two chains with the same setting hold the same digest. -/
theorem sameSetting_cfg {a b : Given} (h : sameSetting a b = true) : a.cfg = b.cfg := by
  unfold sameSetting at h
  simp only [Bool.and_eq_true] at h
  exact bytes_of_beq h.2

/-- The key's three chains as read: the one-time chain is read from the first string, and the other
two hold its digest. -/
theorem KeyChains.read_parts {a b c : ByteArray} {k : KeyChains}
    (h : KeyChains.read a b c = some k) :
    OneTime.read a = some k.oneTime ∧ k.shared.given.cfg = k.oneTime.given.cfg ∧
      k.second.given.cfg = k.oneTime.given.cfg := by
  unfold KeyChains.read at h
  obtain ⟨x, hx, h⟩ := opt_bind h
  obtain ⟨y, _, h⟩ := opt_bind h
  obtain ⟨z, _, h⟩ := opt_bind h
  split at h
  · rename_i hc
    cases h
    simp only [Bool.and_eq_true] at hc
    exact ⟨hx, (sameSetting_cfg hc.1.1.1.1.1).symm, (sameSetting_cfg hc.1.1.1.1.2).symm⟩
  · cases h

/-- The same for the proof's three chains. -/
theorem ProofChains.read_parts {a b c : ByteArray} {k : ProofChains}
    (h : ProofChains.read a b c = some k) :
    First.read a = some k.first ∧ k.shared.given.cfg = k.first.given.cfg ∧
      k.second.given.cfg = k.first.given.cfg := by
  unfold ProofChains.read at h
  obtain ⟨x, hx, h⟩ := opt_bind h
  obtain ⟨y, _, h⟩ := opt_bind h
  obtain ⟨z, _, h⟩ := opt_bind h
  split at h
  · rename_i hc
    cases h
    simp only [Bool.and_eq_true] at hc
    exact ⟨hx, (sameSetting_cfg hc.1.1.1.1.1).symm, (sameSetting_cfg hc.1.1.1.1.2).symm⟩
  · cases h

end OnBytes.Params

namespace OnBytes.Model.Verify

open OnBytes.Params (exc_bind)

/-- The parameter bytes of each of the seven chains in p are spelled under the digest in p, which
has 32 bytes. -/
theorem planned_spelled {pol KL : ByteArray} {layout : Option ByteArray} {p : Planned}
    (h : planned pol KL layout = .ok p) :
    p.cfg.size = 32 ∧ ∀ c : ChainName, ∃ P I, p.chains.bytes c = Fmt.paramsBytes P p.cfg I := by
  unfold planned at h
  obtain ⟨X, _, h⟩ := exc_bind h
  dsimp only at h
  obtain ⟨chains, hc, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  cases h
  obtain ⟨shapes, hm⟩ := chainsOf_made hc
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := Params.configure_spelled hm
  refine ⟨Params.configurationDigest_size _, fun c => ?_⟩
  cases c
  · exact s1
  · exact s2
  · exact s3
  · exact s4
  · exact s5
  · exact s6
  · exact s7

/-- The digest that the entry's chain holds as read back is the digest in p, if the chain's
parameter bytes are fewer than 2^64. -/
theorem planned_link_cfg {pol KL : ByteArray} {layout : Option ByteArray} {p : Planned}
    (h : planned pol KL layout = .ok p) (hb : (p.chains.bytes .link).size < 2 ^ 64) :
    p.chains.link.given.cfg = p.cfg := by
  obtain ⟨h32, hs⟩ := planned_spelled h
  obtain ⟨P, I, e⟩ := hs .link
  have hr := Params.Link.read_given (planned_read h).2.1
  rw [e] at hr hb
  exact Params.Given.read_cfg hb h32 hr

/-- The digest that the key's three chains hold as read back is the digest in p, if the parameter
bytes of the one-time chain are fewer than 2^64. -/
theorem planned_key_cfg {pol KL : ByteArray} {layout : Option ByteArray} {p : Planned}
    (h : planned pol KL layout = .ok p) (hb : (p.chains.bytes .keyOneTime).size < 2 ^ 64) :
    p.chains.key.oneTime.given.cfg = p.cfg ∧ p.chains.key.shared.given.cfg = p.cfg ∧
      p.chains.key.second.given.cfg = p.cfg := by
  obtain ⟨h32, hs⟩ := planned_spelled h
  obtain ⟨P, I, e⟩ := hs .keyOneTime
  obtain ⟨k1, k2, k3⟩ := Params.KeyChains.read_parts (planned_read h).1
  have hr := Params.OneTime.read_given k1
  rw [e] at hr hb
  have e1 := Params.Given.read_cfg hb h32 hr
  exact ⟨e1, k2.trans e1, k3.trans e1⟩

/-- The digest that the proof's three chains hold as read back is the digest in p, if the parameter
bytes of the first chain are fewer than 2^64. -/
theorem planned_proof_cfg {pol KL : ByteArray} {layout : Option ByteArray} {p : Planned}
    (h : planned pol KL layout = .ok p) (hb : (p.chains.bytes .proofFirst).size < 2 ^ 64) :
    p.chains.proof.first.given.cfg = p.cfg ∧ p.chains.proof.shared.given.cfg = p.cfg ∧
      p.chains.proof.second.given.cfg = p.cfg := by
  obtain ⟨h32, hs⟩ := planned_spelled h
  obtain ⟨P, I, e⟩ := hs .proofFirst
  obtain ⟨k1, k2, k3⟩ := Params.ProofChains.read_parts (planned_read h).2.2
  have hr := Params.First.read_given k1
  rw [e] at hr hb
  have e1 := Params.Given.read_cfg hb h32 hr
  exact ⟨e1, k2.trans e1, k3.trans e1⟩

end OnBytes.Model.Verify

#print axioms OnBytes.Model.Verify.planned_link_cfg
#print axioms OnBytes.Model.Verify.planned_key_cfg
#print axioms OnBytes.Model.Verify.planned_proof_cfg
