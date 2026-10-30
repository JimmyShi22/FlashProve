-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TieK/G/SameChainsG.lean: what the program's planner over a monad returns, at the identity
monad and any hash h whose digest of the three public files has 32 bytes, holds one digest, that
one, and one shape of the stored tables, if three of its strings of parameter bytes are short.

"The program" is the Lean program verify-on-bytes. Tie.SameChains p d (OnBytes/Tie/SameChains.lean)
says: the digest in p and in each of the seven chains in p is d; four chains hold the shape of the
stored tables that the entry's chain holds; and the entry's chain in p is read from its parameter
bytes in p. That file shows it of the program's planner's value, at the program's digest
(checks_same). Here it is shown of the planner's text with the digest as an argument (Tie.plannedAt,
OnBytes/Tie/ChainsAtCfg.lean), at every digest of 32 bytes; and so, by
OnBytes/TieK/G/PlannedAtG.lean, of the planner over a monad at h.

Main theorems.
  chainsOf_read: what chainsOf returns, at any digest, holds the chains that the three readers read
    from its own strings of parameter bytes.
  chains_same: at a digest c of 32 bytes, the seven chains that chainsOf returns hold c, the four
    shapes are the entry's chain's, and the entry's chain is read from its own bytes.
  sameChains_at: Tie.SameChains q c of what plannedAt returns at c.
  sameChainsG_small: Tie.SameChains p d of what the planner over a monad returns at h, d the digest
    that h gives on the three public files.
  digest_size_HO: at the hash that is made of a function O with answers of 32 bytes (Fmt.HO O), the
    digest of the public files has 32 bytes.
Asked in chains_same, sameChains_at and sameChainsG_small: the digest has 32 bytes; the parameter
bytes of three chains (the key's one-time chain, the entry's chain, the proof's first chain) are
fewer than 2^64 each. These are the bounds that OnBytes/Model/VerifyDigest.lean and
OnBytes/Model/VerifyShape.lean ask at the program's planner.

The proof of the shapes' part follows OnBytes/Model/VerifyShape.lean's planned_shapes line by line,
with the digest a letter.

Not claimed. That h's answers have 32 bytes. That the three strings are short. The limits of
OnBytes/Tie/SameChains.lean on what SameChains says hold here too. Nothing on soundness. The program
does not import this file.


-/
import OnBytes.TieK.G.PlannedAtG
import OnBytes.Tie.SameChains
import Run.PageIsChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.TieK.G

open OnBytes.TwoPort OnBytes.Model OnBytes.Model.Verify
open OnBytes.Params (exc_bind)
open OnBytes.Tie (plannedAt SameChains)

/-- What chainsOf returns holds the chains that the three readers read from its own strings. -/
theorem chainsOf_read {X : Public} {layout : Option ByteArray} {c : ByteArray} {ch : Chains}
    (h : chainsOf X layout c = .ok ch) :
    Params.KeyChains.read (ch.bytes .keyOneTime) (ch.bytes .keyShared) (ch.bytes .keySecond) =
        some ch.key ∧
      Params.Link.read (ch.bytes .link) = some ch.link ∧
      Params.ProofChains.read (ch.bytes .proofFirst) (ch.bytes .proofShared)
        (ch.bytes .proofSecond) = some ch.proof := by
  unfold chainsOf at h
  obtain ⟨⟨_, _⟩, _, h⟩ := exc_bind h
  dsimp only at h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨made, _, h⟩ := exc_bind h
  split at h
  · rename_i key link proof e1 e2 e3
    cases h
    exact ⟨e1, e2, e3⟩
  · cases h

/-- **One digest and one shape, at any digest of 32 bytes.** -/
theorem chains_same {X : Public} {layout : Option ByteArray} {c : ByteArray} {ch : Chains}
    (h32 : c.size = 32) (h : chainsOf X layout c = .ok ch)
    (hb1 : (ch.bytes .keyOneTime).size < 2 ^ 64) (hb2 : (ch.bytes .link).size < 2 ^ 64)
    (hb3 : (ch.bytes .proofFirst).size < 2 ^ 64) :
    (ch.key.oneTime.given.cfg = c ∧ ch.key.shared.given.cfg = c ∧ ch.key.second.given.cfg = c ∧
      ch.link.given.cfg = c ∧ ch.proof.first.given.cfg = c ∧ ch.proof.shared.given.cfg = c ∧
      ch.proof.second.given.cfg = c) ∧
    (ch.key.oneTime.lin.fold.index = ch.link.link.table ∧
      ch.key.shared.lin.fold.index = ch.link.link.table ∧
      ch.proof.first.lin.fold.index = ch.link.link.table ∧
      ch.proof.shared.lin.fold.index = ch.link.link.table) ∧
    Params.Link.read (ch.bytes .link) = some ch.link := by
  obtain ⟨r1, r2, r3⟩ := chainsOf_read h
  obtain ⟨shapes, hm⟩ := chainsOf_made h
  obtain ⟨hz, ⟨P1, e1⟩, ⟨P2, e2⟩, ⟨P3, a, b, c', d, e, e3⟩⟩ := Params.configure_items hm
  obtain ⟨i1, i2⟩ := Params.sized_index hz
  -- the entry's chain
  have g2 := Params.Link.read_given r2
  have b2 : ch.bytes .link = ch.made.entryLink := rfl
  rw [b2, e2] at g2 hb2
  have c2 := Params.Given.read_cfg hb2 h32 g2
  have t2 := Params.Given.read_items hb2 h32 (by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl <;> (dsimp only; decide)) g2
  obtain ⟨_, l2, q2, w2⟩ := Params.Link.read_link r2
  rw [t2] at q2
  simp only [List.cons.injEq, Prod.mk.injEq, true_and, and_true] at q2
  rw [← q2.2] at w2
  have s2 := Params.readLink_table w2
  -- the key's one-time chain
  obtain ⟨k1, k2, k3⟩ := Params.KeyChains.read_parts r1
  have g1 := Params.OneTime.read_given k1
  have b1 : ch.bytes .keyOneTime = ch.made.keyOneTime := rfl
  rw [b1, e1] at g1 hb1
  have c1 := Params.Given.read_cfg hb1 h32 g1
  have t1 := Params.Given.read_items hb1 h32 (by
    intro y hy
    simp only [Plan.oneTimeItems, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl <;> (dsimp only; decide)) g1
  obtain ⟨_, _, _, _, l1, q1, w1⟩ := Params.OneTime.read_lin k1
  rw [t1] at q1
  simp only [Plan.oneTimeItems, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at q1
  rw [← q1.2.2.2.2] at w1
  have s1 := Params.readLin_index w1
  -- the proof's first chain
  obtain ⟨f1, f2, f3⟩ := Params.ProofChains.read_parts r3
  have g3 := Params.First.read_given f1
  have b3 : ch.bytes .proofFirst = ch.made.first := rfl
  rw [b3, e3] at g3 hb3
  have c3 := Params.Given.read_cfg hb3 h32 g3
  have t3 := Params.Given.read_items hb3 h32 (by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> (dsimp only; decide)) g3
  obtain ⟨_, l3, _, q3, w3⟩ := Params.First.read_lin f1
  rw [t3] at q3
  simp only [List.cons.injEq, Prod.mk.injEq, true_and] at q3
  rw [← q3.2.1] at w3
  have s3 := Params.readLin_index w3
  have u1 : ch.key.oneTime.lin.fold.index = ch.link.link.table := by rw [s1, s2, i1]
  have u3 : ch.proof.first.lin.fold.index = ch.link.link.table := by rw [s3, s2, i2]
  have v1 := Params.KeyChains.read_lin r1
  have v3 := Params.ProofChains.read_lin r3
  exact ⟨⟨c1, k2.trans c1, k3.trans c1, c2, c3, f2.trans c3, f3.trans c3⟩,
    ⟨u1, by rw [v1]; exact u1, u3, by rw [v3]; exact u3⟩, r2⟩

/-- What plannedAt returns at c holds c, and its chains are chainsOf's at its public part and c. -/
theorem plannedAt_parts {pol KL : ByteArray} {layout : Option ByteArray} {c : ByteArray}
    {q : Planned} (h : plannedAt pol KL layout c = .ok q) :
    q.cfg = c ∧ chainsOf q.X layout c = .ok q.chains := by
  unfold plannedAt at h
  obtain ⟨X, _, h⟩ := exc_bind h
  obtain ⟨chains, hch, h⟩ := exc_bind h
  obtain ⟨built, _, h⟩ := exc_bind h
  cases h
  exact ⟨rfl, hch⟩

/-- **SameChains of the planner's text at any digest of 32 bytes.** -/
theorem sameChains_at {pol KL : ByteArray} {layout : Option ByteArray} {c : ByteArray}
    {q : Planned} (h32 : c.size = 32) (h : plannedAt pol KL layout c = .ok q)
    (hb1 : (q.chains.bytes .keyOneTime).size < 2 ^ 64)
    (hb2 : (q.chains.bytes .link).size < 2 ^ 64)
    (hb3 : (q.chains.bytes .proofFirst).size < 2 ^ 64) : SameChains q c := by
  obtain ⟨e0, hch⟩ := plannedAt_parts h
  obtain ⟨⟨a1, a2, a3, a4, a5, a6, a7⟩, s, r⟩ := chains_same h32 hch hb1 hb2 hb3
  exact ⟨⟨e0, a1, a2, a3, a4, a5, a6, a7⟩, s, r⟩

/-- **SameChains of what the planner over a monad returns at h**, at the digest that h gives on the
three public files. -/
theorem sameChainsG_small (h : M.HashM Id) {pol lay KL : ByteArray} {p : Planned}
    (h32 : (M.Params.configurationDigest (m := Id) h [pol, lay, KL] : ByteArray).size = 32)
    (hp : (M.Model.Verify.planned (m := Id) h pol KL (some lay)).run = .ok p)
    (hb1 : (p.chains.bytes .keyOneTime).size < 2 ^ 64)
    (hb2 : (p.chains.bytes .link).size < 2 ^ 64)
    (hb3 : (p.chains.bytes .proofFirst).size < 2 ^ 64) :
    SameChains p (M.Params.configurationDigest (m := Id) h [pol, lay, KL]) := by
  rw [plannedG_at] at hp
  exact sameChains_at h32 hp hb1 hb2 hb3

/-- At the hash that is made of a function with answers of 32 bytes the digest has 32 bytes. -/
theorem digest_size_HO (O : ByteArray → ByteArray) (hO : ∀ x, (O x).size = 32)
    (files : List ByteArray) :
    (M.Params.configurationDigest (m := Id) (Fmt.HO O) files : ByteArray).size = 32 :=
  _root_.Run.PQ.size_HO32 O hO 169 0 2 _ _ (by decide)

end OnBytes.TieK.G
