-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/OwesAt.lean: what the openings of a key file or of a proof file give to a walk over
whole paths (`TreesOwed`, `StoredOwed`: OnBytes/Maker/OwesOfRead.lean), at a value r that the
verifier program's reader has returned.

Statements and proofs. r is the caller's letter: the value of `Key.readKey` or of
`Proof.readProof`, run from the empty record of vertices. R, the three lists of rounds of which the
plain data are made, is the caller's letter too: the value of the dry runs at r's key, written out
here as OnBytes/Maker/Files.lean defines `dryKey` and `dryProof`, at any table's name t0 in the
place of that file's `noTable` (the dry runs do not read the name).

Main names:
  `dry3_shape`: the three lists begin with the first chain's and the shared chain's own rounds.
  `treesOwed_of_readKey`, `storedOwed_of_readKey`: a key file.
  `treesOwed_of_readProof`, `storedOwed_of_readProof`: a proof file, for a first chain's block that
    carries the relation "alike" where no given source is met (OnBytes/Maker/ProofOwn.lean: the
    program's own blocks do).
What is asked besides the reading and the dry runs: `OneSetting` (OnBytes/Maker/OneSetting.lean:
paid where the three chains' parameter bytes were read together); the test `Three.Whole.fits`; for
the stored table `StoredAt` at the three chains and `StoredSecond`.
No letter stands under "there is" in the four statements outside the two records' own fields.
Limits: the tests on the data are premises. All is said at the format's hash. Nothing on
opening-form binding, no two openings of a commitment, correctness of extraction, what a root fixes
beyond the reader's record or whatever else names a committer or a prover. Nothing on soundness.

-/
import OnBytes.Maker.OwesOfRead
import OnBytes.Maker.ProofOwn
import OnBytes.Maker.OneSetting

set_option autoImplicit false

namespace OnBytes.Maker

open OnBytes.Proof OnBytes.TwoLaws OnBytes.TieK
open OnBytes.Params (Rounds)

/-- The three lists begin with the first chain's and the shared chain's own rounds. -/
theorem dry3_shape {p : TailPublic} {key : TableKey} {R₁ R₂ : Rounds} {dry : FirstEnd}
    {dry2 : SharedEnd} {R : Rounds × Rounds × Rounds}
    (h : Three.dry3 p key (R₁, dry) = some R)
    (h2 : (sharedBlock p.lin key).dryRun (sharedStart p) = some (R₂, dry2)) :
    ∃ R₃, R = (R₁, R₂, R₃) := by
  unfold Three.dry3 at h
  rw [h2] at h
  have h' : (((secondBlock p.lin dry.lin
      (dry2.goesOn (Three.tagChain 2 (Three.rootsIn R₂)))).rounds
    (secondStart p dry (Three.tagChain 1 (Three.rootsIn R₁)))).bind fun R₃ =>
      some (R₁, R₂, R₃)) = some R := h
  cases hX : (secondBlock p.lin dry.lin (dry2.goesOn (Three.tagChain 2 (Three.rootsIn R₂)))).rounds
      (secondStart p dry (Three.tagChain 1 (Three.rootsIn R₁))) with
  | none =>
    rw [hX] at h'
    cases h'
  | some Y =>
    rw [hX] at h'
    exact ⟨Y, (Option.some.inj h').symm⟩

/-! ## A key file -/

section
variable (k : Params.KeyChains) (table t0 : Params.TableName) (file : ByteArray) (j : ℕ)
  (r : TailRead) (h : (Key.readKey k table file j).fromStart = .ok r)
  (R : Rounds × Rounds × Rounds)
  (hR : ((Key.oneTime k.oneTime).dryRun (Key.startOf k.oneTime)).bind
    (Three.dry3 (Key.tailPublic k t0) r.key) = some R)
  (m : ℕ) (hf : Three.Whole.fits R.1 R.2.1 R.2.2 m = true) (cfg : ByteArray) (sb : ℕ)
  (hs : OneSetting k.oneTime.given k.shared.given k.second.given cfg sb)
include h hR hf hs

/-- **A key file: what the trees' openings give, at the value r of the program's reader.** -/
theorem treesOwed_of_readKey : TreesOwed (Three.Whole.of R.1 R.2.1 R.2.2) r cfg := by
  obtain ⟨R₁, dry, S₁, seal1, seal2, R₂, dry2, S₂, R₃', S₃, hS₁, T⟩ :=
    threeRead_of_readKey k table file j r h
  have hS₁' : Params.describeWith k.oneTime.given Params.labelOneTime
      (Params.OneTime.statement table) .inFile R₁ 0 = some S₁ := hS₁
  rw [T.first_dry] at hR
  have hd : Three.dry3 (Key.tailPublic k table) r.key (R₁, dry) = some R := hR
  obtain ⟨R₃, rfl⟩ := dry3_shape hd T.shared_dry
  obtain ⟨o₁, b₁⟩ := key_own k.oneTime T.first_dry
  exact treesOwed_of_read T hS₁' (fun e => by cases e) o₁ b₁ R₃ hd m hf cfg hs.c₁ hs.c₂ hs.c₃

/-- **A key file: what the stored table's openings give.** -/
theorem storedOwed_of_readKey (a : ℕ) (a₁ : StoredAt a (Three.Whole.of R.1 R.2.1 R.2.2).ds₁)
    (a₂ : StoredAt a (Three.Whole.of R.1 R.2.1 R.2.2).ds₂)
    (a₃ : StoredAt a (Three.Whole.of R.1 R.2.1 R.2.2).ds₃)
    (h2 : StoredSecond (Three.Whole.of R.1 R.2.1 R.2.2)) :
    StoredOwed (Three.Whole.of R.1 R.2.1 R.2.2) r cfg
      (Params.Shared.statement table r.place.root) := by
  obtain ⟨R₁, dry, S₁, seal1, seal2, R₂, dry2, S₂, R₃', S₃, hS₁, T⟩ :=
    threeRead_of_readKey k table file j r h
  have hS₁' : Params.describeWith k.oneTime.given Params.labelOneTime
      (Params.OneTime.statement table) .inFile R₁ 0 = some S₁ := hS₁
  rw [T.first_dry] at hR
  have hd : Three.dry3 (Key.tailPublic k table) r.key (R₁, dry) = some R := hR
  obtain ⟨R₃, rfl⟩ := dry3_shape hd T.shared_dry
  obtain ⟨-, b₁⟩ := key_own k.oneTime T.first_dry
  have O := storedOwed_of_read T hS₁' b₁ R₃ hd m hf sb a hs.s₁ hs.s₂ hs.s₃ a₁ a₂ a₃ h2
  have ec : (Key.tailPublic k table).shared.given.cfg = cfg := hs.c₂
  rw [ec] at O
  exact O

end

/-! ## A proof file -/

section
variable (c : Params.ProofChains) (table t0 : Params.TableName) (copy : ℕ) (request words :
    ByteArray)
  (block : Blk FirstEnd) (file : ByteArray) (r : TailRead)
  (h : (readProof c table copy request words block file).fromStart = .ok r)
  (hb : Carries (Alike NoGiven true) (FirstEndAlike NoGiven) block block)
  (R : Rounds × Rounds × Rounds)
  (hR : (block.dryRun (firstStart c.first)).bind (Three.dry3 (tailPublic c t0) r.key) = some R)
  (m : ℕ) (hf : Three.Whole.fits R.1 R.2.1 R.2.2 m = true) (cfg : ByteArray) (sb : ℕ)
  (hs : OneSetting c.first.given c.shared.given c.second.given cfg sb)
include h hb hR hf hs

/-- **A proof file: what the trees' openings give, at the value r of the program's reader.** -/
theorem treesOwed_of_readProof : TreesOwed (Three.Whole.of R.1 R.2.1 R.2.2) r cfg := by
  obtain ⟨i, R₁, dry, S₁, seal1, seal2, R₂, dry2, S₂, R₃', S₃, -, hS₁, T⟩ :=
    threeRead_of_readProof c table copy request words block file r h
  have hS₁' : Params.describeWith c.first.given Params.labelFirst
      (Params.First.statement table copy request words) .inFile R₁ 0 = some S₁ := hS₁
  rw [T.first_dry] at hR
  have hd : Three.dry3 (tailPublic c table) r.key (R₁, dry) = some R := hR
  obtain ⟨R₃, rfl⟩ := dry3_shape hd T.shared_dry
  obtain ⟨o₁, b₁⟩ := first_own hb (firstStart_alike c.first) T.first_dry
  exact treesOwed_of_read T hS₁' (fun e => by cases e) o₁ b₁ R₃ hd m hf cfg hs.c₁ hs.c₂ hs.c₃

/-- **A proof file: what the stored table's openings give.** -/
theorem storedOwed_of_readProof (a : ℕ) (a₁ : StoredAt a (Three.Whole.of R.1 R.2.1 R.2.2).ds₁)
    (a₂ : StoredAt a (Three.Whole.of R.1 R.2.1 R.2.2).ds₂)
    (a₃ : StoredAt a (Three.Whole.of R.1 R.2.1 R.2.2).ds₃)
    (h2 : StoredSecond (Three.Whole.of R.1 R.2.1 R.2.2)) :
    StoredOwed (Three.Whole.of R.1 R.2.1 R.2.2) r cfg
      (Params.Shared.statement table r.place.root) := by
  obtain ⟨i, R₁, dry, S₁, seal1, seal2, R₂, dry2, S₂, R₃', S₃, -, hS₁, T⟩ :=
    threeRead_of_readProof c table copy request words block file r h
  have hS₁' : Params.describeWith c.first.given Params.labelFirst
      (Params.First.statement table copy request words) .inFile R₁ 0 = some S₁ := hS₁
  rw [T.first_dry] at hR
  have hd : Three.dry3 (tailPublic c table) r.key (R₁, dry) = some R := hR
  obtain ⟨R₃, rfl⟩ := dry3_shape hd T.shared_dry
  obtain ⟨-, b₁⟩ := first_own hb (firstStart_alike c.first) T.first_dry
  have O := storedOwed_of_read T hS₁' b₁ R₃ hd m hf sb a hs.s₁ hs.s₂ hs.s₃ a₁ a₂ a₃ h2
  have ec : (tailPublic c table).shared.given.cfg = cfg := hs.c₂
  rw [ec] at O
  exact O

end

end OnBytes.Maker
