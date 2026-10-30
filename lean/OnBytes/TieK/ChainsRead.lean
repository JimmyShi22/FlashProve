-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TieK/ChainsRead.lean: what holds of the parameters of a file's chains if they were read from
parameter bytes: every test of the readers in the open, as named facts.

The checks of a key file and of a proof file take the parameters of the file's three chains as an
argument that is already read (`Params.KeyChains`, `Params.ProofChains`). These two types are bare
records: a value of them can be written by hand, and `Key.check` and `Proof.check` take any value.
What ties the three chains to each other is tested where their parameter bytes are read
(`Params.KeyChains.read`, `Params.ProofChains.read`, OnBytes/Params/Chains.lean): one setting and
one digest of the public files in all three; the items "codes" and "the test on the table" byte
for byte the same in the first two; no entry for a table's own sample in the plans of the shared
and the second chain. So a statement on a check's yes that needs one of these ties must take it as
a premise on the value, or take the value as one that a reader has returned. This file opens the
readers: it proves no more than what their texts say, as one statement for each, so that such a
premise has a name and a proof.

The facts.
 'SameSetting a b': the six words of the plans' setting and the digest are equal.
 `OneTimeFacts`, `SharedFacts`, `SecondFacts`, `LinkFacts`, `FirstFacts`: for one chain: the bytes
   pass `Params.Given.read`; the further items have exactly these names in this order; each field is
   what its item's reader returns; for a proof's first chain also the six conditions of
   `Params.First.read`.
 `KeyChainsFacts`, `ProofChainsFacts`: for the three chains of a file: each is read from its own
   bytes; the ties named above, as equations between bytes and between the values read from them.

Main theorems: `sameSetting_open`, `oneTime_read_open`, `shared_read_open`, `second_read_open`,
`link_read_open`, `first_read_open`, `keyChains_read_open`, `proofChains_read_open`,
`planned_chains_open`. The last says that the chains which `Model.Verify.planned` returns, which are
those that the program `verify-on-bytes` hands to its checks, have all these facts at the plan's own
parameter bytes.

What lay already and is used here: `Params.Given.read_bytes`, `Params.Given.read_plan_ok`
(OnBytes/Params/Laws.lean); `Params.bytes_of_beq` (OnBytes/Model/VerifyDigest.lean);
`Params.sameItem_eq`, `Params.KeyChains.read_lin`, `Params.ProofChains.read_lin`
(OnBytes/Model/VerifyShape.lean); `Model.Verify.planned_read` (OnBytes/Model/VerifyLaws.lean).

Not claimed. Nothing on soundness. Nothing ties the chains of one file to those of another: that
the key's, the entry's and the proof's chains hold one digest and one shape of the tables is
`Tie.SameChains` (OnBytes/Tie/SameChains.lean). The binding tree's shape stands in the first chain's
items alone: no reader compares it with anything. Nothing is said of what the items' readers
accept. The program does not import this file.

-/
import OnBytes.Model.VerifyShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.TieK
open OnBytes.Params

/-! ## One setting -/

/-- Two chains' parameter bytes hold the same six words of the plan's setting and the same digest of
the public files. -/
structure SameSetting (a b : Given) : Prop where
  field : a.plan.field = b.plan.field
  salt : a.plan.salt = b.plan.salt
  nonce : a.plan.nonce = b.plan.nonce
  posB : a.plan.posB = b.plan.posB
  samples : a.plan.samples = b.plan.samples
  saved : a.plan.saved = b.plan.saved
  cfg : a.cfg = b.cfg

/-- **What the test `Params.sameSetting` has found if it says yes.** -/
theorem sameSetting_open {a b : Given} (h : sameSetting a b = true) : SameSetting a b := by
  unfold sameSetting at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨eq_of_beq h1, eq_of_beq h2, eq_of_beq h3, eq_of_beq h4, eq_of_beq h5, eq_of_beq h6,
    bytes_of_beq h7⟩

/-- What `Params.Given.read` returns holds the bytes that it read, and a plan that is in order and
has the format's names alone. -/
theorem given_read_open {b : ByteArray} {g : Given} (h : Given.read b = some g) :
    g.bytes = b ∧ g.plan.ok = true ∧ namesKnown g.plan = true :=
  ⟨Given.read_bytes h, Given.read_plan_ok h⟩

/-! ## One chain -/

/-- The facts of a key's one-time chain q that was read from the bytes b. m, r, t, c, l: the values
of its five further items. -/
structure OneTimeFacts (b : ByteArray) (q : OneTime) (m r t c l : ByteArray) : Prop where
  given : Given.read b = some q.given
  items : q.given.items = [("index-mask message", m), ("ranges", r), ("binding tree", t),
    ("codes", c), ("the test on the table", l)]
  indexMasks : readNotice m = some q.indexMasks
  ranges : readRanges r = some q.ranges
  binding : readBinding t = some q.binding
  codes : readCodes c = some q.codes
  lin : readLin l = some q.lin

/-- **What `Params.OneTime.read` has done if it returns.** -/
theorem oneTime_read_open {b : ByteArray} {q : OneTime} (h : OneTime.read b = some q) :
    ∃ m r t c l, OneTimeFacts b q m r t c l := by
  unfold OneTime.read at h
  obtain ⟨g, hg, h⟩ := opt_bind h
  split at h
  · rename_i m r t c l hi
    obtain ⟨_, h1, h⟩ := opt_bind h
    obtain ⟨_, h2, h⟩ := opt_bind h
    obtain ⟨_, h3, h⟩ := opt_bind h
    obtain ⟨_, h4, h⟩ := opt_bind h
    obtain ⟨_, h5, h⟩ := opt_bind h
    cases h
    exact ⟨m, r, t, c, l, ⟨hg, hi, h1, h2, h3, h4, h5⟩⟩
  · cases h

/-- The facts of a shared chain q that was read from the bytes b. c, l: the values of its two
further items. -/
structure SharedFacts (b : ByteArray) (q : Shared) (c l : ByteArray) : Prop where
  given : Given.read b = some q.given
  items : q.given.items = [("codes", c), ("the test on the table", l)]
  codes : readCodes c = some q.codes
  lin : readLin l = some q.lin

/-- **What `Params.Shared.read` has done if it returns.** -/
theorem shared_read_open {b : ByteArray} {q : Shared} (h : Shared.read b = some q) :
    ∃ c l, SharedFacts b q c l := by
  unfold Shared.read at h
  obtain ⟨g, hg, h⟩ := opt_bind h
  split at h
  · rename_i c l hi
    obtain ⟨_, h1, h⟩ := opt_bind h
    obtain ⟨_, h2, h⟩ := opt_bind h
    cases h
    exact ⟨c, l, ⟨hg, hi, h1, h2⟩⟩
  · cases h

/-- The facts of a second chain q that was read from the bytes b: it has no further item. -/
structure SecondFacts (b : ByteArray) (q : Second) : Prop where
  given : Given.read b = some q.given
  items : q.given.items = []

/-- **What `Params.Second.read` has done if it returns.** -/
theorem second_read_open {b : ByteArray} {q : Second} (h : Second.read b = some q) :
    SecondFacts b q := by
  unfold Second.read at h
  obtain ⟨g, hg, h⟩ := opt_bind h
  split at h
  · rename_i he
    cases h
    exact ⟨hg, List.isEmpty_iff.1 he⟩
  · cases h

/-- The facts of a link's chain q that was read from the bytes b. c, l: the values of its two
further items. -/
structure LinkFacts (b : ByteArray) (q : Link) (c l : ByteArray) : Prop where
  given : Given.read b = some q.given
  items : q.given.items = [("codes", c), ("the link", l)]
  codes : readCodes c = some q.codes
  link : readLink l = some q.link

/-- **What `Params.Link.read` has done if it returns.** -/
theorem link_read_open {b : ByteArray} {q : Link} (h : Link.read b = some q) :
    ∃ c l, LinkFacts b q c l := by
  unfold Link.read at h
  obtain ⟨g, hg, h⟩ := opt_bind h
  split at h
  · rename_i c l hi
    obtain ⟨_, h1, h⟩ := opt_bind h
    obtain ⟨_, h2, h⟩ := opt_bind h
    cases h
    exact ⟨c, l, ⟨hg, hi, h1, h2⟩⟩
  · cases h

/-- The facts of a proof's first chain q that was read from the bytes b. c, l, s, y, i, n, t: the
values of its seven own items; the items behind them are `q.more`, unread. The last six fields are
the conditions under which `Params.First.read` returns. -/
structure FirstFacts (b : ByteArray) (q : First) (c l s y i n t : ByteArray) : Prop where
  given : Given.read b = some q.given
  items : q.given.items = ("codes", c) :: ("the test on the table", l) :: ("request's shape", s) ::
    ("layout", y) :: ("links' identifiers", i) :: ("pending rows", n) :: ("binding tree", t) ::
    q.more
  codes : readCodes c = some q.codes
  lin : readLin l = some q.lin
  shape : readReq s = some q.shape
  layout : readLayout y = some q.layout
  identifiers : readWords i = some q.identifiers
  pendingRows : readWord n = some q.pendingRows
  binding : readBinding t = some q.binding
  oneAtStart : q.shape.atStart.length = 1
  plainScalars : q.shape.link.map (·.plain) = List.replicate (q.shape.link.length - 1) 0 ++ [1]
  oneIdentifierEach : q.identifiers.length = q.shape.link.length
  oneLayoutEach : q.layout.link.length = q.shape.link.length
  somePending : 1 ≤ q.pendingRows
  noRecord : q.given.record = none

/-- **What `Params.First.read` has done if it returns.** -/
theorem first_read_open {b : ByteArray} {q : First} (h : First.read b = some q) :
    ∃ c l s y i n t, FirstFacts b q c l s y i n t := by
  unfold First.read at h
  obtain ⟨g, hg, h⟩ := opt_bind h
  split at h
  · rename_i c l s y i n t more hi
    obtain ⟨_, h1, h⟩ := opt_bind h
    obtain ⟨_, h2, h⟩ := opt_bind h
    obtain ⟨_, h3, h⟩ := opt_bind h
    obtain ⟨_, h4, h⟩ := opt_bind h
    obtain ⟨_, h5, h⟩ := opt_bind h
    obtain ⟨_, h6, h⟩ := opt_bind h
    obtain ⟨_, h7, h⟩ := opt_bind h
    dsimp only at h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩ := hc
      exact ⟨c, l, s, y, i, n, t, ⟨hg, hi, h1, h2, h3, h4, h5, h6, h7, c1, c2, c3, c4, c5,
        Option.isNone_iff_eq_none.1 c6⟩⟩
    · cases h
  · cases h

/-! ## The three chains of a file -/

/-- The facts of a key's three chains k that were read from the bytes a, b, c. -/
structure KeyChainsFacts (a b c : ByteArray) (k : KeyChains) : Prop where
  oneTime : OneTime.read a = some k.oneTime
  shared : Shared.read b = some k.shared
  second : Second.read c = some k.second
  sharedSetting : SameSetting k.oneTime.given k.shared.given
  secondSetting : SameSetting k.oneTime.given k.second.given
  /-- the item "codes" has the same bytes in the one-time chain and in the shared chain -/
  codesBytes : k.shared.given.item "codes" = k.oneTime.given.item "codes"
  /-- so has the item "the test on the table" -/
  linBytes : k.shared.given.item "the test on the table" =
    k.oneTime.given.item "the test on the table"
  codes : k.shared.codes = k.oneTime.codes
  lin : k.shared.lin = k.oneTime.lin
  sharedNoRecord : k.shared.given.record = none
  secondNoRecord : k.second.given.record = none

/-- **What `Params.KeyChains.read` has done if it returns.** -/
theorem keyChains_read_open {a b c : ByteArray} {k : KeyChains}
    (h : KeyChains.read a b c = some k) : KeyChainsFacts a b c k := by
  have hl := KeyChains.read_lin h
  unfold KeyChains.read at h
  obtain ⟨x, hx, h⟩ := opt_bind h
  obtain ⟨y, hy, h⟩ := opt_bind h
  obtain ⟨z, hz, h⟩ := opt_bind h
  split at h
  · rename_i hc
    cases h
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩ := hc
    obtain ⟨_, _, _, u1, l1, f1⟩ := oneTime_read_open hx
    obtain ⟨u2, l2, f2⟩ := shared_read_open hy
    have i1 : x.given.item "codes" = some u1 := by
      unfold Given.item
      rw [f1.items]
      rfl
    have i2 : y.given.item "codes" = some u2 := by
      unfold Given.item
      rw [f2.items]
      rfl
    have j1 : x.given.item "the test on the table" = some l1 := by
      unfold Given.item
      rw [f1.items]
      rfl
    have j2 : y.given.item "the test on the table" = some l2 := by
      unfold Given.item
      rw [f2.items]
      rfl
    have e1 : u1 = u2 := sameItem_eq c3 i1 i2
    have e2 : l1 = l2 := sameItem_eq c4 j1 j2
    have w : y.codes = x.codes := by
      have w1 := f1.codes
      have w2 := f2.codes
      rw [← e1, w1] at w2
      exact (Option.some.inj w2).symm
    have b1 : y.given.item "codes" = x.given.item "codes" := by rw [i1, i2, e1]
    have b2 : y.given.item "the test on the table" = x.given.item "the test on the table" := by
      rw [j1, j2, e2]
    exact ⟨hx, hy, hz, sameSetting_open c1, sameSetting_open c2, b1, b2, w, hl,
      Option.isNone_iff_eq_none.1 c5, Option.isNone_iff_eq_none.1 c6⟩
  · cases h

/-- The facts of a proof's three chains k that were read from the bytes a, b, c. That the first
chain's plan has no entry for a table's own sample either is among `FirstFacts`. -/
structure ProofChainsFacts (a b c : ByteArray) (k : ProofChains) : Prop where
  first : First.read a = some k.first
  shared : Shared.read b = some k.shared
  second : Second.read c = some k.second
  sharedSetting : SameSetting k.first.given k.shared.given
  secondSetting : SameSetting k.first.given k.second.given
  /-- the item "codes" has the same bytes in the first chain and in the shared chain -/
  codesBytes : k.shared.given.item "codes" = k.first.given.item "codes"
  /-- so has the item "the test on the table" -/
  linBytes : k.shared.given.item "the test on the table" =
    k.first.given.item "the test on the table"
  codes : k.shared.codes = k.first.codes
  lin : k.shared.lin = k.first.lin
  firstNoRecord : k.first.given.record = none
  sharedNoRecord : k.shared.given.record = none
  secondNoRecord : k.second.given.record = none

/-- **What `Params.ProofChains.read` has done if it returns.** -/
theorem proofChains_read_open {a b c : ByteArray} {k : ProofChains}
    (h : ProofChains.read a b c = some k) : ProofChainsFacts a b c k := by
  have hl := ProofChains.read_lin h
  unfold ProofChains.read at h
  obtain ⟨x, hx, h⟩ := opt_bind h
  obtain ⟨y, hy, h⟩ := opt_bind h
  obtain ⟨z, hz, h⟩ := opt_bind h
  split at h
  · rename_i hc
    cases h
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩, c6⟩ := hc
    obtain ⟨u1, l1, _, _, _, _, _, f1⟩ := first_read_open hx
    obtain ⟨u2, l2, f2⟩ := shared_read_open hy
    have i1 : x.given.item "codes" = some u1 := by
      unfold Given.item
      rw [f1.items]
      rfl
    have i2 : y.given.item "codes" = some u2 := by
      unfold Given.item
      rw [f2.items]
      rfl
    have j1 : x.given.item "the test on the table" = some l1 := by
      unfold Given.item
      rw [f1.items]
      rfl
    have j2 : y.given.item "the test on the table" = some l2 := by
      unfold Given.item
      rw [f2.items]
      rfl
    have e1 : u1 = u2 := sameItem_eq c3 i1 i2
    have e2 : l1 = l2 := sameItem_eq c4 j1 j2
    have w : y.codes = x.codes := by
      have w1 := f1.codes
      have w2 := f2.codes
      rw [← e1, w1] at w2
      exact (Option.some.inj w2).symm
    have b1 : y.given.item "codes" = x.given.item "codes" := by rw [i1, i2, e1]
    have b2 : y.given.item "the test on the table" = x.given.item "the test on the table" := by
      rw [j1, j2, e2]
    exact ⟨hx, hy, hz, sameSetting_open c1, sameSetting_open c2, b1, b2, w, hl, f1.noRecord,
      Option.isNone_iff_eq_none.1 c5, Option.isNone_iff_eq_none.1 c6⟩
  · cases h

/-! ## The chains that the program hands to its checks -/

/-- **The chains that `Model.Verify.planned` returns have all these facts**, at the plan's own
parameter bytes. -/
theorem planned_chains_open {pol KL : ByteArray} {layout : Option ByteArray}
    {p : Model.Verify.Planned} (h : Model.Verify.planned pol KL layout = .ok p) :
    KeyChainsFacts (p.chains.bytes .keyOneTime) (p.chains.bytes .keyShared)
        (p.chains.bytes .keySecond) p.chains.key ∧
      (∃ c l, LinkFacts (p.chains.bytes .link) p.chains.link c l) ∧
      ProofChainsFacts (p.chains.bytes .proofFirst) (p.chains.bytes .proofShared)
        (p.chains.bytes .proofSecond) p.chains.proof := by
  obtain ⟨r1, r2, r3⟩ := Model.Verify.planned_read h
  exact ⟨keyChains_read_open r1, link_read_open r2, proofChains_read_open r3⟩

end OnBytes.TieK
