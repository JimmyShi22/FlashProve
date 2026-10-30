-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/EntryFb.lean: two partial codes of chain queries for an entry's judge: under the tag
of the link's typed chain, and under the tag of the seeds' typed chain; with the facts that a page
asks of them, and what they write at each typed round.

The judge of an entry file with instances (OnBytes/TypedOracleCompiler/Slice/EntryX.lean, EntryXJudge.lean) asks
typed chain queries under two tags. Under `.link` its typed chain is the entry's one chain: a round
in front, which sends nothing and at which the first query is asked, then the written rounds of the
description. Under `.test` the seeds' protocol has two queries, asked once for each of the two outer
roots. This file does for an entry what OnBytes/TypedOracleCompiler/Run/KeyFb.lean does for a key. The sibling is a
second form of the library's soundness road, under OnBytes/TypedOracleCompiler/.
 - `Le D early e`: the interface: `LXE` at bodies that are strings, answers as lists of triples, and
   the seeds' protocol as its Test;
 - `PinsE`: what the strings hold and no typed query does: the configuration's digest; the chain's
   parameter digest and label; what stands behind the root in a table's name;
 - `rcE D i`: the code of (roots, plain part) at the typed round i; `inE D k z`: the plain part of
   the written round k as a plain part of the whole shape; `rcE_at`: at the typed round k + 1 and
   that plain part `rcE` writes what the round's own code writes;
 - `onE`, `backE`, `hbackE`: one chain's arithmetic; `rdE`, `kindE`, `workE`, `ordE`; `linkChain`:
   the data of `Chain162G.ChainG`;
 - `e0`: the first value (OnBytes/TypedOracleCompiler/Run/EntryFirst.lean); `e162`: all written rounds; `fbLink`:
   these two by the typed round; `u0`, `u1`, `fbSeeds`: the seeds' two codes by the typed round;
 - `fbLink_at0`, `fbLink_else`, `fbSeeds_at0`, `fbSeeds_else`: what the two codes write at each
   typed round;
 - `fbLink_is`, `fbSeeds_is`: what is known of every string; `fbE_apart`: no string is written under
   both tags; `fbE_facts`: every string has the tag of 160 or 162 (stated with a third case, 173, as
   the general page asks) and begins with the byte 0 or 1.

Main definitions: `Le`, `PinsE`, `rcE`, `inE`, `linkChain`, `fbLink`, `fbSeeds`.
Main theorems: `rcE_at`, `fbLink_at0`, `fbLink_else`, `fbSeeds_at0`, `fbSeeds_else`, `fbE_apart`,
`fbE_facts`.

Not claimed. CODES, NO PAGE YET. ONE constant `rest` stands behind the root in both tables' names:
two tables whose names differ elsewhere than in the root are not borne. At round 0 only the block of
the typed tail has a string. The order of blocks `ordE` is the library's (tail to block 1 where the
round has work) and, at a round of the kind "sealed" without work, tail to block 1: what that costs
is said in OnBytes/TypedOracleCompiler/Run/Chain162G.lean's head; by the format's page a link's chain has no sealed
round, so that limb is idle here. No pins are given. Nothing on soundness. The compiler under
OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on definitions of
Compile/.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.EntryFirst
import OnBytes.TypedOracleCompiler.Run.KeyFb
import OnBytes.TypedOracleCompiler.Run.PlainIn
import OnBytes.TypedOracleCompiler.Slice.EntryXJudge

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Run.EntryFb
open Rom _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run TypedOracleCompiler.Slice
open TypedOracleCompiler.Run.Chain162G TypedOracleCompiler.Run.KeyRanges TypedOracleCompiler.Run.PlainAt
open TypedOracleCompiler.Run.SeamAt TypedOracleCompiler.Run.Apart TypedOracleCompiler.Run.PlainIn
open TypedOracleCompiler.Run.KeyFb (isEq isEq_iff)
open TypedOracleCompiler.Run.FirstAnswers (T3)
open TypedOracleCompiler.Run.PQ (XD)
open _root_.Run.PQ (inR inR_put)
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run

variable {Sd : Type} (D : XD)
  (early : (List T3 × List T3) × Sd → (List T3 × List T3) × Sd) (e : _root_.Fmt.Entry)

/-- The interface: an entry's frame at bodies that are strings, with the seeds' protocol as its
Test. -/
abbrev Le : BatchProtocolWithLeafBody Unit ((List T3 × List T3) × Sd) :=
  LXE (Bd := List Bool) D early (TSE D e)

/-- The shape of the link's typed chain: a round in front, then the written rounds. -/
abbrev shE : Shape := shapeOf (Le D early e) .link

/-- What the strings hold and no typed query does. The way in which a first query holds an
instance and the seeds' entry stand in the type alone. -/
structure PinsE {Sd : Type} (_D : XD)
    (_early : (List T3 × List T3) × Sd → (List T3 × List T3) × Sd) (_e : _root_.Fmt.Entry) where
  /-- the configuration's digest: the start of vertices and stored leaves -/
  cfg : ByteArray
  /-- it has 32 bytes -/
  hcfg : cfg.size = 32
  /-- the chain's parameter digest -/
  pd : Dig 256
  /-- the chain's label -/
  l : ℕ
  /-- it is not the seeds' chain's -/
  hR : l ≠ _root_.Fmt.recordLabel
  /-- it is below 2 ^ 48 -/
  hlt : l < 2 ^ 48
  /-- what stands behind the root in a table's name -/
  rest : ByteArray

/-! ## Roots and plain part at a typed round -/

/-- The code of (roots, plain part) at the typed round i: nothing at the round in front; then the
written rounds' own codes. -/
def rcE : ℕ → PCode (List (Dig 256) × PlainPart (shE D early e) (annOf (Le D early e) .link))
  | 0 => PCode.empty _
  | i + 1 => inR (PQ.rcL D.C D.ds i)

/-- Its strings have at least 64 bits. -/
theorem rcE_ge : ∀ (i : ℕ) (y : List (Dig 256) × PlainPart (shE D early e) (annOf (Le D early e) .link))
    (s : List Bool), (rcE D early e i).put y = some s → 64 ≤ s.length
  | 0, _, _, h => by cases h
  | i + 1, y, s, h => by
      obtain ⟨y1, h1⟩ := inR_put _ y s h
      exact PQ.rcL_ge D.C D.ds i y1 s h1

/-- The fixed plain part of the round in front. -/
def p0E : PlainPart (shE D early e) (annOf (Le D early e) .link) := .inl (.inr ())

/-- The plain part of the written round k as a plain part of the whole shape. -/
def inE (k : Fin D.ds.length) (z : PlainD (D.ds.get k)) :
    PlainPart (shE D early e) (annOf (Le D early e) .link) := .inr (inLast D.C D.ds k z)

/-- At the typed round k + 1 `rcE` writes the message of the written round k. -/
theorem rcE_at (k : Fin D.ds.length) (r : List (Dig 256)) (z : PlainD (D.ds.get k)) :
    (rcE D early e (k.val + 1)).put (r, inE D early e k z) =
      (PQ.pRound (D.ds.get k).entry.work (D.ds.get k).items).put (r, z) :=
  rcL_at D.C D.ds k r z

/-! ## One chain's arithmetic -/

/-- Whether the typed round i is one of n written rounds. -/
def onE (n i : ℕ) : Bool := decide (1 ≤ i ∧ i ≤ n)

/-- The typed round of a label and an index. -/
def backE (n l l' j : ℕ) : Option ℕ := if l' = l ∧ 1 ≤ j ∧ j ≤ n then some j else none

/-- `backE` finds exactly the rounds that are on. -/
theorem hbackE (n l l' j i : ℕ) :
    backE n l l' j = some i ↔ (onE n i = true ∧ l = l' ∧ i = j) := by
  unfold backE onE
  rw [decide_eq_true_iff]
  constructor
  · intro h
    split_ifs at h with c
    obtain rfl := Option.some.inj h
    exact ⟨c.2, c.1.symm, rfl⟩
  · rintro ⟨ho, rfl, rfl⟩
    exact if_pos ⟨rfl, ho⟩

/-- The written round at the typed round i. -/
def rdE (i : ℕ) : Option PQ.RD := if i = 0 then none else D.ds[i - 1]?

/-- At the typed round k + 1 it is the written round k. -/
theorem rdE_at (k : Fin D.ds.length) : rdE D (k.val + 1) = some (D.ds.get k) := by
  unfold rdE
  rw [if_neg (by omega), Nat.add_sub_cancel]
  exact List.getElem?_eq_getElem k.isLt

/-- Its kind's number; 0 where there is none. -/
def kindE (i : ℕ) : ℕ := ((rdE D i).map fun d => d.kind.num).getD 0

/-- Its bits of work. -/
def workE (i : ℕ) : ℕ := ((rdE D i).map fun d => d.entry.work).getD 0

/-- Whether the typed tail of its answer is block 1 of the format's row. -/
def ordE (i : ℕ) : Bool :=
  ((rdE D i).map fun d => decide (d.entry.work ≠ 0) || decide (d.kind = .sealed)).getD false

variable {D early e} (P : PinsE D early e)

/-- The data of the one code for all hashes under 162 of the link's typed chain. -/
def linkChain : ChainG (Le D early e) .link where
  on := onE D.ds.length
  lab := fun _ => P.l
  idx := id
  back := backE D.ds.length P.l
  hback := fun l j i => hbackE D.ds.length P.l l j i
  ord := ordE D
  kind := kindE D
  work := workE D
  rc := rcE D early e
  hrc := rcE_ge D early e
  mkH := mkF2
  selH := selF2
  hsel := selF2_mkF2
  hmk := mkF2_selF2

variable (dd : Sd) (K : ℕ)

/-- The first value of the link's chain. -/
def e0 : PCode (FbIn 256 (Le D early e) .link) :=
  EntryFirst.firstPE (Le D early e) .link (p0E D early e) (isEq _) dd (isEq dd) P.pd (isEq_iff _)
    (isEq_iff dd) P.l

/-- All written rounds. -/
def e162 : PCode (FbIn 256 (Le D early e) .link × Fin (K + 1)) := p162G (linkChain P) K

/-- What `e0` writes is a string under 160 with the link's label. -/
theorem e0_is (q : FbIn 256 (Le D early e) .link) (s : List Bool) (h : (e0 P dd).put q = some s) :
    Is160 P.l s := is160_of_hdr _ _ (EntryFirst.firstPE_hdr _ _ _ _ _ _ _ _ _ _ q s h)

/-- What `e162` writes is a string under 162 with the link's label. -/
theorem e162_is (x : FbIn 256 (Le D early e) .link × Fin (K + 1)) (s : List Bool)
    (h : (e162 P K).put x = some s) : Is162 P.l s := by
  obtain ⟨hb, ρ, r, hρ, rfl⟩ := p162G_shape _ K x s h
  exact is162_of_shape P.l x.1.round hb ρ r hρ

/-- The code of chain queries under the link's tag, each with a block: two codes by the typed
round. -/
def fbLink : PCode (FbIn 256 (Le D early e) .link × Fin (K + 1)) :=
  split (tailP (e0 P dd) K) (e162 P K) (fun x => decide (x.1.round = 0)) (fun a b s h1 h2 =>
    no_160_162 _ _ P.hlt s (e0_is P dd _ s (tailP_put _ K a s h1).1) (e162_is P K b s h2))

/-- What is known of every string of `fbLink`. -/
theorem fbLink_is (x : FbIn 256 (Le D early e) .link × Fin (K + 1)) (s : List Bool)
    (h : (fbLink P dd K).put x = some s) : Is160 P.l s ∨ Is162 P.l s := by
  rcases split_put _ _ _ _ x s h with h1 | h1
  · exact Or.inl (e0_is P dd _ s (tailP_put _ K x s h1).1)
  · exact Or.inr (e162_is P K x s h1)

/-- At the typed round 0: the first value, at the tail's block. -/
theorem fbLink_at0 (x : FbIn 256 (Le D early e) .link × Fin (K + 1)) (h : x.1.round = 0) :
    (fbLink P dd K).put x = (tailP (e0 P dd) K).put x :=
  split_true _ _ _ _ x (decide_eq_true h)

/-- At every other typed round: the code of the written rounds. -/
theorem fbLink_else (x : FbIn 256 (Le D early e) .link × Fin (K + 1)) (h : x.1.round ≠ 0) :
    (fbLink P dd K).put x = (e162 P K).put x :=
  split_false _ _ _ _ x (decide_eq_false h)

/-! ## The seeds' chain -/

/-- The seeds' chain's first value. -/
def u0 : PCode (FbIn 256 (Le D early e) .test) :=
  FirstName.firstPN P.rest (Le D early e) .test (p0S (L := Le D early e) .test D.C e _ id) (isEq _)
    FirstName.zeroPd (isEq_iff _) _root_.Fmt.recordLabel

/-- The drawing round. It hangs on no pin. -/
def u1 : PCode (FbIn 256 (Le D early e) .test × Fin (K + 1)) :=
  SeedRound.secondPS (Le D early e) .test (p1S (L := Le D early e) .test D.C e _ id) (isEq _)
    (isEq_iff _) K

/-- What `u0` writes is a string under 160 with the seeds' chain's label. -/
theorem u0_is (q : FbIn 256 (Le D early e) .test) (s : List Bool) (h : (u0 P).put q = some s) :
    Is160 _root_.Fmt.recordLabel s :=
  is160_of_hdr _ _ (FirstName.firstPN_hdr _ _ _ _ _ _ _ _ q s h)

/-- What `u1` writes is a string under 162 with the seeds' chain's label. -/
theorem u1_is (x : FbIn 256 (Le D early e) .test × Fin (K + 1)) (s : List Bool)
    (h : (u1 K).put x = some s) : Is162 _root_.Fmt.recordLabel s := by
  obtain ⟨hb, ρ, r, hρ, rfl⟩ := p162_shape _ K x s h
  refine ⟨?_, fun b h0 h1 => ?_⟩
  · unfold lw1
    rw [← List.append_assoc, ← List.append_assoc, List.drop_left'
      (by rw [List.length_append, List.length_append, length_bitsOfByte, length_mid32, hρ])]
    exact List.take_left' (length_u64n _)
  · cases hb
    · exact byte_prefix b 0 h0 _
    · exact byte_prefix b 1 h1 _

/-- The code of chain queries under the seeds' tag, each with a block: two codes by the typed
round. -/
def fbSeeds : PCode (FbIn 256 (Le D early e) .test × Fin (K + 1)) :=
  split (tailP (u0 P) K) (u1 K) (fun x => decide (x.1.round = 0)) (fun a b s h1 h2 =>
    no_160_162 _ _ (by decide) s (u0_is P _ s (tailP_put _ K a s h1).1) (u1_is K b s h2))

/-- What is known of every string of `fbSeeds`. -/
theorem fbSeeds_is (x : FbIn 256 (Le D early e) .test × Fin (K + 1)) (s : List Bool)
    (h : (fbSeeds P K).put x = some s) :
    Is160 _root_.Fmt.recordLabel s ∨ Is162 _root_.Fmt.recordLabel s := by
  rcases split_put _ _ _ _ x s h with h1 | h1
  · exact Or.inl (u0_is P _ s (tailP_put _ K x s h1).1)
  · exact Or.inr (u1_is K x s h1)

/-- Under the seeds' tag at the typed round 0: the seeds' chain's first value, at the tail's
block. -/
theorem fbSeeds_at0 (x : FbIn 256 (Le D early e) .test × Fin (K + 1)) (h : x.1.round = 0) :
    (fbSeeds P K).put x = (tailP (u0 P) K).put x :=
  split_true _ _ _ _ x (decide_eq_true h)

/-- Under the seeds' tag at every other typed round: the drawing round's code. -/
theorem fbSeeds_else (x : FbIn 256 (Le D early e) .test × Fin (K + 1)) (h : x.1.round ≠ 0) :
    (fbSeeds P K).put x = (u1 K).put x :=
  split_false _ _ _ _ x (decide_eq_false h)

/-- No string is written under both tags. -/
theorem fbE_apart (a : FbIn 256 (Le D early e) .test × Fin (K + 1))
    (b : FbIn 256 (Le D early e) .link × Fin (K + 1)) (s : List Bool)
    (h1 : (fbSeeds P K).put a = some s) : (fbLink P dd K).put b ≠ some s := by
  intro h2
  have hr : _root_.Fmt.recordLabel < 2 ^ 48 := by decide
  rcases fbSeeds_is P K a s h1 with g1 | g1 <;> rcases fbLink_is P dd K b s h2 with g2 | g2
  · exact no_160_160 _ _ P.hlt hr P.hR s g2 g1
  · exact no_160_162 _ _ P.hlt s g1 g2
  · exact no_160_162 _ _ hr s g2 g1
  · exact no_162_162 _ _ P.hlt hr P.hR s g2 g1

/-- Every string of either code has the tag of 160 or 162 and begins with the byte 0 or 1. The
statement has a third case, 173: the form that `PageG.realOf` asks; no string here has it. -/
theorem fbE_facts (s : List Bool)
    (h : (∃ x, (fbLink P dd K).put x = some s) ∨ (∃ x, (fbSeeds P K).put x = some s)) :
    (tag16 s = t160 ∨ tag16 s = t162 ∨ tag16 s = t173) ∧
      ∀ b : UInt8, b ≠ 0 → b ≠ 1 → ¬ bitsOfByte b <+: s := by
  have f160 : ∀ l, Is160 l s → (tag16 s = t160 ∨ tag16 s = t162 ∨ tag16 s = t173) ∧
      ∀ b : UInt8, b ≠ 0 → b ≠ 1 → ¬ bitsOfByte b <+: s := fun l g =>
    ⟨Or.inl (tag_160 l s g), fun b h0 _ => g.2.2 b h0⟩
  have f162 : ∀ l, Is162 l s → (tag16 s = t160 ∨ tag16 s = t162 ∨ tag16 s = t173) ∧
      ∀ b : UInt8, b ≠ 0 → b ≠ 1 → ¬ bitsOfByte b <+: s := fun l g =>
    ⟨Or.inr (Or.inl (tag_162 l s g)), g.2⟩
  rcases h with ⟨x, hx⟩ | ⟨x, hx⟩
  · rcases fbLink_is P dd K x s hx with g | g
    · exact f160 _ g
    · exact f162 _ g
  · rcases fbSeeds_is P K x s hx with g | g
    · exact f160 _ g
    · exact f162 _ g

end TypedOracleCompiler.Run.EntryFb
