-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/VerifyRead.lean: what a yes of `KeyChains.read` and of `ProofChains.read` says of the
three chains that are read.
These two functions read the parameter bytes of a file's three chains (a chain is the
non-interactive form of one protocol): the first (a key's one-time chain), the shared and the
second. They refuse them unless six tests pass: the shared and the second chain have the setting of
the first; the items "codes" and "the test on the table" have the same bytes in the first and the
shared; and neither the shared nor the second has an entry for a table's own sample.
States, for `KeyChains` and under the same five names for `ProofChains`: `read_tests`: the three
chains' own readers returned them, and the six tests passed; `read_each`: each chain is read from
its own string; `read_setting`: the six settings of the plans, and the digest, are the same in all
three; `read_codes`: the first and the shared hold the same codes; `read_record`: the shared and the
second have no entry for a table's own sample. With `sameSetting_fields` and three lemmas on codes.
Under: 1 hypothesis each: for the ten, that the function returns the three chains; for
`sameSetting_fields`, that `sameSetting` says yes; for the three lemmas, that the chain's own reader
returns it.
Does not show: (1) Nothing on soundness. (2) Nothing on the plans' entries, which differ from chain
to chain. (3) Nothing on what the settings, the codes or the digest are. (4) For proofs only; the
program, that is the Lean port built from OnBytes/, does not import this file.
-/
import OnBytes.Model.VerifyShape

set_option autoImplicit false

namespace OnBytes.Params

/-- The six settings of two plans, and the digest of the public files, are equal. -/
structure SameFields (a b : Given) : Prop where
  field : a.plan.field = b.plan.field
  salt : a.plan.salt = b.plan.salt
  nonce : a.plan.nonce = b.plan.nonce
  posB : a.plan.posB = b.plan.posB
  samples : a.plan.samples = b.plan.samples
  saved : a.plan.saved = b.plan.saved
  cfg : a.cfg = b.cfg

/-- What a yes of `sameSetting` says, field by field. -/
theorem sameSetting_fields {a b : Given} (h : sameSetting a b = true) : SameFields a b := by
  have hc := sameSetting_cfg h
  unfold sameSetting at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, hc⟩

/-- What `OneTime.read` returns: its five items, and its codes are read from the fourth. -/
theorem OneTime.read_codes {b : ByteArray} {q : OneTime} (h : OneTime.read b = some q) :
    ∃ m r t c l, q.given.items = [("index-mask message", m), ("ranges", r), ("binding tree", t),
      ("codes", c), ("the test on the table", l)] ∧ readCodes c = some q.codes := by
  unfold OneTime.read at h
  obtain ⟨g, _, h⟩ := opt_bind h
  split at h
  · rename_i m r t c l hi
    obtain ⟨_, _, h⟩ := opt_bind h
    obtain ⟨_, _, h⟩ := opt_bind h
    obtain ⟨_, _, h⟩ := opt_bind h
    obtain ⟨y, hy, h⟩ := opt_bind h
    obtain ⟨_, _, h⟩ := opt_bind h
    cases h
    exact ⟨m, r, t, c, l, hi, hy⟩
  · cases h

/-- What `First.read` returns: its items begin with "codes", and its codes are read from that
item. -/
theorem First.read_codes {b : ByteArray} {q : First} (h : First.read b = some q) :
    ∃ c rest, q.given.items = ("codes", c) :: rest ∧ readCodes c = some q.codes := by
  unfold First.read at h
  obtain ⟨g, _, h⟩ := opt_bind h
  split at h
  · rename_i c l s y i n t more hi
    obtain ⟨w, hw, h⟩ := opt_bind h
    obtain ⟨_, _, h⟩ := opt_bind h
    obtain ⟨_, _, h⟩ := opt_bind h
    obtain ⟨_, _, h⟩ := opt_bind h
    obtain ⟨_, _, h⟩ := opt_bind h
    obtain ⟨_, _, h⟩ := opt_bind h
    obtain ⟨_, _, h⟩ := opt_bind h
    dsimp only at h
    split at h
    · cases h
      exact ⟨c, _, hi, hw⟩
    · cases h
  · cases h

/-- What `Shared.read` returns: its two items, and its codes are read from the first. -/
theorem Shared.read_codes {b : ByteArray} {q : Shared} (h : Shared.read b = some q) :
    ∃ c l, q.given.items = [("codes", c), ("the test on the table", l)] ∧
      readCodes c = some q.codes := by
  unfold Shared.read at h
  obtain ⟨g, _, h⟩ := opt_bind h
  split at h
  · rename_i c l hi
    obtain ⟨y, hy, h⟩ := opt_bind h
    obtain ⟨_, _, h⟩ := opt_bind h
    cases h
    exact ⟨c, l, hi, hy⟩
  · cases h

/-- The six tests of `KeyChains.read`, and the three readings, from its yes. -/
theorem KeyChains.read_tests {a b c : ByteArray} {k : KeyChains}
    (h : KeyChains.read a b c = some k) :
    OneTime.read a = some k.oneTime ∧ Shared.read b = some k.shared ∧
      Second.read c = some k.second ∧
      sameSetting k.oneTime.given k.shared.given = true ∧
      sameSetting k.oneTime.given k.second.given = true ∧
      sameItem k.oneTime.given k.shared.given "codes" = true ∧
      sameItem k.oneTime.given k.shared.given "the test on the table" = true ∧
      k.shared.given.record.isNone = true ∧ k.second.given.record.isNone = true := by
  unfold KeyChains.read at h
  obtain ⟨x, hx, h⟩ := opt_bind h
  obtain ⟨y, hy, h⟩ := opt_bind h
  obtain ⟨z, hz, h⟩ := opt_bind h
  split at h
  · rename_i hc
    cases h
    simp only [Bool.and_eq_true] at hc
    exact ⟨hx, hy, hz, hc.1.1.1.1.1, hc.1.1.1.1.2, hc.1.1.1.2, hc.1.1.2, hc.1.2, hc.2⟩
  · cases h

/-- Each of a key's three chains is read from its own string. -/
theorem KeyChains.read_each {a b c : ByteArray} {k : KeyChains}
    (h : KeyChains.read a b c = some k) :
    OneTime.read a = some k.oneTime ∧ Shared.read b = some k.shared ∧
      Second.read c = some k.second :=
  ⟨(KeyChains.read_tests h).1, (KeyChains.read_tests h).2.1, (KeyChains.read_tests h).2.2.1⟩

/-- A key's shared and second chains have the settings and the digest of its one-time chain. -/
theorem KeyChains.read_setting {a b c : ByteArray} {k : KeyChains}
    (h : KeyChains.read a b c = some k) :
    SameFields k.oneTime.given k.shared.given ∧ SameFields k.oneTime.given k.second.given :=
  ⟨sameSetting_fields (KeyChains.read_tests h).2.2.2.1,
    sameSetting_fields (KeyChains.read_tests h).2.2.2.2.1⟩

/-- A key's shared chain holds the codes of its one-time chain. -/
theorem KeyChains.read_codes {a b c : ByteArray} {k : KeyChains}
    (h : KeyChains.read a b c = some k) : k.shared.codes = k.oneTime.codes := by
  obtain ⟨hx, hy, _, _, _, hc, _⟩ := KeyChains.read_tests h
  obtain ⟨_, _, _, c1, _, q1, w1⟩ := OneTime.read_codes hx
  obtain ⟨c2, _, q2, w2⟩ := Shared.read_codes hy
  have e := sameItem_eq hc (x := c1) (y := c2)
    (by unfold Given.item; rw [q1]; rfl) (by unfold Given.item; rw [q2]; rfl)
  rw [← e, w1] at w2
  exact (Option.some.inj w2).symm

/-- Neither a key's shared chain nor its second chain has an entry for a table's own sample. -/
theorem KeyChains.read_record {a b c : ByteArray} {k : KeyChains}
    (h : KeyChains.read a b c = some k) :
    k.shared.given.record = none ∧ k.second.given.record = none :=
  ⟨Option.isNone_iff_eq_none.1 (KeyChains.read_tests h).2.2.2.2.2.2.2.1,
    Option.isNone_iff_eq_none.1 (KeyChains.read_tests h).2.2.2.2.2.2.2.2⟩

/-- The six tests of `ProofChains.read`, and the three readings, from its yes. -/
theorem ProofChains.read_tests {a b c : ByteArray} {k : ProofChains}
    (h : ProofChains.read a b c = some k) :
    First.read a = some k.first ∧ Shared.read b = some k.shared ∧
      Second.read c = some k.second ∧
      sameSetting k.first.given k.shared.given = true ∧
      sameSetting k.first.given k.second.given = true ∧
      sameItem k.first.given k.shared.given "codes" = true ∧
      sameItem k.first.given k.shared.given "the test on the table" = true ∧
      k.shared.given.record.isNone = true ∧ k.second.given.record.isNone = true := by
  unfold ProofChains.read at h
  obtain ⟨x, hx, h⟩ := opt_bind h
  obtain ⟨y, hy, h⟩ := opt_bind h
  obtain ⟨z, hz, h⟩ := opt_bind h
  split at h
  · rename_i hc
    cases h
    simp only [Bool.and_eq_true] at hc
    exact ⟨hx, hy, hz, hc.1.1.1.1.1, hc.1.1.1.1.2, hc.1.1.1.2, hc.1.1.2, hc.1.2, hc.2⟩
  · cases h

/-- Each of a proof's three chains is read from its own string. -/
theorem ProofChains.read_each {a b c : ByteArray} {k : ProofChains}
    (h : ProofChains.read a b c = some k) :
    First.read a = some k.first ∧ Shared.read b = some k.shared ∧
      Second.read c = some k.second :=
  ⟨(ProofChains.read_tests h).1, (ProofChains.read_tests h).2.1, (ProofChains.read_tests h).2.2.1⟩

/-- A proof's shared and second chains have the settings and the digest of its first chain. -/
theorem ProofChains.read_setting {a b c : ByteArray} {k : ProofChains}
    (h : ProofChains.read a b c = some k) :
    SameFields k.first.given k.shared.given ∧ SameFields k.first.given k.second.given :=
  ⟨sameSetting_fields (ProofChains.read_tests h).2.2.2.1,
    sameSetting_fields (ProofChains.read_tests h).2.2.2.2.1⟩

/-- A proof's shared chain holds the codes of its first chain. -/
theorem ProofChains.read_codes {a b c : ByteArray} {k : ProofChains}
    (h : ProofChains.read a b c = some k) : k.shared.codes = k.first.codes := by
  obtain ⟨hx, hy, _, _, _, hc, _⟩ := ProofChains.read_tests h
  obtain ⟨c1, _, q1, w1⟩ := First.read_codes hx
  obtain ⟨c2, _, q2, w2⟩ := Shared.read_codes hy
  have e := sameItem_eq hc (x := c1) (y := c2)
    (by unfold Given.item; rw [q1]; rfl) (by unfold Given.item; rw [q2]; rfl)
  rw [← e, w1] at w2
  exact (Option.some.inj w2).symm

/-- Neither a proof's shared chain nor its second chain has an entry for a table's own sample. -/
theorem ProofChains.read_record {a b c : ByteArray} {k : ProofChains}
    (h : ProofChains.read a b c = some k) :
    k.shared.given.record = none ∧ k.second.given.record = none :=
  ⟨Option.isNone_iff_eq_none.1 (ProofChains.read_tests h).2.2.2.2.2.2.2.1,
    Option.isNone_iff_eq_none.1 (ProofChains.read_tests h).2.2.2.2.2.2.2.2⟩

end OnBytes.Params
