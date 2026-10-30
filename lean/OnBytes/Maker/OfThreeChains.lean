-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/OfThreeChains.lean: from a yes of the verifier program's check of a key file or of a
proof file to what OnBytes/Maker/AcceptAt.lean asks of the data, of the reading and of the run.

OnBytes/TieK/Chains.lean opens the two checks: if one says yes, there are three descriptions, three
readings and three runs, each named as the program's text makes it (`ThreeChains`). This file takes
that record and gives: the three lists of rounds of which the plain data of the file are made
(`Three.dry3`, `dryKey`, `dryProof`); `ReadFits` at these data; that the first chain has as many
roots as the data count; that the first view ends in a sealing round; that the key and the three
views pass the tests on the words.
Of the program's decision: `judge_of_yes` (one run) and `tailRefusal_none` (the tail's two views)
have its text at runs that end well. That the decision on the three views is a yes is drawn from the
record by no theorem here: `keyRefusal = none` and `proofRefusal = none` are premises
(`chains_of_readKey`, `chains_of_readProof`, `key_read_gives`, `proof_read_gives`), which
`key_check_reads` and `proof_check_reads` take from a yes of the check.

WHICH READING. r is the file as the reader returns it, with all openings, not the lighter form that
the program hands on before it decides on a proof file (the head of OnBytes/Maker/ReadFitsOf.lean).

Main definitions.
  `PortGives a R r S₁ S₂ S₃`: what a yes gives at the three lists of rounds R, in one record.
Main theorems.
  `judge_of_yes`, `tailRefusal_none`: the decision's text at runs that end well.
  `dry3_of_chains`: the three lists of rounds.
  `okRead_of_chains`: the key and the three views pass the tests on the words (`okRead`,
    OnBytes/Maker/Decide3Laws.lean), by `okSeeds_of_tableKey` (OnBytes/Maker/OkSeedsOfKey.lean) and
    `okView_of_read` (OnBytes/Maker/OkWordsOfRead.lean).
  `gives_of_chains`: `PortGives`, from `ThreeChains`, the first chain's description, and the tests.
  `chains_of_readKey`, `chains_of_readProof`: `ThreeChains` at the caller's own reading r: from
    `(Key.readKey k table file j).fromStart = .ok r` and `Key.keyRefusal k table r = none`, and the
    like for a proof file.
  `key_read_gives`, `proof_read_gives`: from the same two premises: the key that was made of the
    table; rounds R with `dryKey k r.key = some R` (`dryProof`); `PortGives` at R and r, if the
    tests pass.
  `key_check_reads`, `proof_check_reads`: a yes of `Key.check` or of `Proof.check` gives these two
    premises, at the reading that the check itself has made.

The tests. `okAt a (some R)` (OnBytes/Maker/Files.lean), `shapesFit` and `sealBare`
(OnBytes/Maker/ViewTests.lean) at the data of R: three hypotheses, which can be evaluated.

What is not claimed. That the tests pass. That the typing returns. Nothing on the verifier's
messages of any transcript. Nothing on soundness.


-/
import OnBytes.Maker.OkSeedsOfKey
import OnBytes.Maker.ReadFitsOf
import OnBytes.TieK.Chains

set_option autoImplicit false

namespace OnBytes.Maker

open OnBytes.Proof OnBytes.TieK
open OnBytes.Params (Rounds)

/-- The decision's step at a run that ends well. -/
theorem judge_of_yes {α : Type} (front : String) {b : Blk α} {s : Start} {v : Fmt.View} {x : α}
    (h : b.runOn s v = .ok x) : judge front b s v = .ok x := by
  unfold judge
  rw [h]

/-- The decision on a tail's two views is a yes, where the two runs end well. -/
theorem tailRefusal_none {p : TailPublic} {real : FirstEnd} {r : TailRead} {real2 : SharedEnd}
    (h2 : (sharedBlock p.lin r.key).runOn (sharedStart p) r.shared.view = .ok real2)
    (h3 : (secondBlock p.lin real.lin (real2.goesOn r.shared)).runOn (secondStart p real r.first)
      r.second.view = .ok ()) : tailRefusal p real r = none := by
  unfold tailRefusal
  rw [judge_of_yes "shared-chain-" h2]
  dsimp only
  rw [judge_of_yes "second-chain-" h3]

/-- **What a yes of the program's check gives**, at the three lists of rounds R. -/
structure PortGives (a : ℕ) (R : Rounds × Rounds × Rounds) (r : TailRead) (S₁ S₂ S₃ : Fmt.SpecX) :
    Prop where
  fits : ReadFits a (Three.Whole.of R.1 R.2.1 R.2.2) r S₁ S₂ S₃
  roots : (Three.Whole.of R.1 R.2.1 R.2.2).t₁ = r.first.roots.length
  sealed : SealedLast r.first.view
  okWords : okRead r = true

section
variable {p : TailPublic} {block1 : Blk FirstEnd} {start1 : Start} {file : ByteArray} {i : ℕ}
  {R₁ : Rounds} {dry : FirstEnd} {S₁ : Fmt.SpecX} {r : TailRead} {seal1 seal2 : ByteArray}
  {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃' : Rounds} {S₃ : Fmt.SpecX}
  {real : FirstEnd} {real2 : SharedEnd} {g₁ : Params.Given} {l₁ : ℕ} {x₁ : ByteArray}
  {n₁ : Fmt.Rand}

/-- **The three lists of rounds of which the data are made**: the first chain's and the shared
chain's as the program's own dry runs state them, the third at made-up names, with the same stored
tables as the rounds under which the third chain was read. -/
theorem dry3_of_chains
    (T : ThreeChains p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃ real real2)
    (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁) :
    ∃ R₃, Three.dry3 p r.key (R₁, dry) = some (R₁, R₂, R₃) ∧ StoredAlike R₃' R₃ := by
  have hr : r.first.roots.length = Three.rootsIn R₁ :=
    readChain_roots hS₁ [] file i r.first T.first_read
  obtain ⟨R₃, h3, hA, -⟩ := secondRounds_tags_some p dry dry2 r.first r.shared (Three.rootsIn R₂)
    R₃' T.second_rounds
  rw [hr] at h3
  refine ⟨R₃, ?_, hA⟩
  unfold Three.dry3
  rw [T.shared_dry]
  show (((secondBlock p.lin dry.lin (dry2.goesOn (Three.tagChain 2 (Three.rootsIn R₂)))).rounds
    (secondStart p dry (Three.tagChain 1 (Three.rootsIn R₁)))).bind fun R₃ =>
      some (R₁, R₂, R₃)) = _
  rw [h3]
  rfl

/-- **The key and the three views of a file that the program has read pass the tests on the
words.** -/
theorem okRead_of_chains
    (T : ThreeChains p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃ real real2) :
    okRead r = true := by
  unfold okRead
  rw [okSeeds_of_tableKey T.key_made, T.first_view, T.shared_view, T.second_view,
    okView_of_read _ _ _ _ _ _ T.first_read, okView_of_read _ _ _ _ _ _ T.shared_read,
    okView_of_read _ _ _ _ _ _ T.second_read]
  rfl

/-- **What a yes gives, from the three chains' record.** -/
theorem gives_of_chains (a : ℕ)
    (T : ThreeChains p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃ real real2)
    (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁) (R₃ : Rounds)
    (hA : StoredAlike R₃' R₃) (hok : okAt a (some (R₁, R₂, R₃)) = true)
    (hsh : shapesFit a (Three.Whole.of R₁ R₂ R₃) = true)
    (hb : sealBare (Three.Whole.of R₁ R₂ R₃) = true) : PortGives a (R₁, R₂, R₃) r S₁ S₂ S₃ := by
  have hfit : Three.Whole.fits R₁ R₂ R₃ 2 = true := (okAt_parts hok).fits
  have hst : storedFit a (Three.Whole.of R₁ R₂ R₃) = true := (okAt_parts hok).stored
  have hne : ∃ x, R₁.getLast? = some x := by
    cases e : R₁.getLast? with
    | some x => exact ⟨x, rfl⟩
    | none =>
      unfold Three.Whole.fits at hfit
      simp only [Bool.and_eq_true] at hfit
      have h5 := List.all_eq_true.1 hfit.1.2 R₁ List.mem_cons_self
      simp only [e] at h5
      cases h5
  obtain ⟨x, hx⟩ := hne
  exact
    { fits := readFits_chain a hS₁ T.shared_spec T.second_spec T.first_read T.shared_read
        T.second_read T.first_view T.shared_view T.second_view hA hst hsh hb
      roots := t₁_chain hS₁ T.first_read
      sealed := sealedLast_chain hS₁ T.first_read T.first_view x hx (bareSeal_of_fits hfit x hx)
      okWords := okRead_of_chains T }

end

/-! ## From the program's own reading -/

/-- A reading from the empty record of vertices that returns. -/
theorem fromStart_ok {α : Type} (x : Reading α) (r : α) (h : x.fromStart = .ok r) :
    ∃ s', x Session.start = .ok (r, s') := by
  unfold Reading.fromStart at h
  cases hq : x Session.start with
  | error e => rw [hq] at h; cases h
  | ok y =>
    rw [hq] at h
    injection h with hy
    exact ⟨y.2, by rw [← hy]⟩

/-- **A key file: the three chains' record at the caller's own reading r.** Every letter under
"there is" is fixed by an equation of the record or by the one on the description. -/
theorem chains_of_readKey (k : Params.KeyChains) (table : Params.TableName) (file : ByteArray)
    (j : ℕ) (r : TailRead) (hr : (Key.readKey k table file j).fromStart = .ok r)
    (hno : Key.keyRefusal k table r = none) :
    ∃ R₁ dry S₁ seal1 seal2 R₂ dry2 S₂ R₃' S₃ real real2,
      k.oneTime.describe table R₁ = some S₁ ∧
      ThreeChains (Key.tailPublic k table) (Key.oneTime k.oneTime) (Key.startOf k.oneTime) file j
        R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃ real real2 := by
  obtain ⟨s', hs'⟩ := fromStart_ok _ _ hr
  obtain ⟨R₁, dry, S₁, s1, f⟩ := readKey_open _ _ _ _ _ _ _ hs'
  unfold Key.keyRefusal at hno
  dsimp only at hno
  split at hno
  · cases hno
  · rename_i real hj
    obtain ⟨real2, hy⟩ := tailRefusal_open _ _ _ hno
    obtain ⟨seal1, seal2, R₂, dry2, S₂, R₃', S₃, t⟩ :=
      threeChains_of _ _ _ _ _ _ _ _ _ _ _ _ _ f.first_dry f.first_read f.tail_read f.whole
        (TieK.judge_ok _ _ _ _ _ hj) hy
    exact ⟨R₁, dry, S₁, seal1, seal2, R₂, dry2, S₂, R₃', S₃, real, real2, f.first_spec, t⟩

/-- **A proof file: the same.** block: the first chain's block. -/
theorem chains_of_readProof (c : Params.ProofChains) (table : Params.TableName) (copy : ℕ)
    (request words : ByteArray) (block : Blk FirstEnd) (file : ByteArray) (r : TailRead)
    (hr : (readProof c table copy request words block file).fromStart = .ok r)
    (hno : proofRefusal c table block r = none) :
    ∃ i R₁ dry S₁ seal1 seal2 R₂ dry2 S₂ R₃' S₃ real real2,
      readProofHead c.first.given.plan.field file = .ok (copy, i) ∧
      c.first.describe table copy request words R₁ = some S₁ ∧
      ThreeChains (tailPublic c table) block (firstStart c.first) file i R₁ dry S₁ r seal1 seal2 R₂
        dry2 S₂ R₃' S₃ real real2 := by
  obtain ⟨s', hs'⟩ := fromStart_ok _ _ hr
  obtain ⟨i, R₁, dry, S₁, s1, f⟩ := readProof_open _ _ _ _ _ _ _ _ _ _ hs'
  rw [proofRefusal_eq] at hno
  split at hno
  · cases hno
  · rename_i real hj
    obtain ⟨real2, hy⟩ := tailRefusal_open _ _ _ hno
    obtain ⟨seal1, seal2, R₂, dry2, S₂, R₃', S₃, t⟩ :=
      threeChains_of _ _ _ _ _ _ _ _ _ _ _ _ _ f.first_dry f.first_read f.tail_read f.whole
        (TieK.judge_ok _ _ _ _ _ hj) hy
    exact ⟨i, R₁, dry, S₁, seal1, seal2, R₂, dry2, S₂, R₃', S₃, real, real2, f.head_read,
      f.first_spec, t⟩

/-- **A key file: what the program's reading and its yes give, at the caller's own reading r.** R is
fixed by the equation on `dryKey`. S₁, S₂, S₃ stand in `PortGives` alone. -/
theorem key_read_gives (a : ℕ) (k : Params.KeyChains) (table : Params.TableName)
    (file : ByteArray) (j : ℕ) (r : TailRead)
    (hr : (Key.readKey k table file j).fromStart = .ok r)
    (hno : Key.keyRefusal k table r = none) :
    tableKey k.shared.given.plan.field k.shared.given.cfg
        (Key.tailPublic k table).lin.fold.index table 0 = some r.key ∧
      ∃ R : Rounds × Rounds × Rounds, dryKey k r.key = some R ∧
        (okAt a (some R) = true → shapesFit a (Three.Whole.of R.1 R.2.1 R.2.2) = true →
          sealBare (Three.Whole.of R.1 R.2.1 R.2.2) = true →
          ∃ S₁ S₂ S₃, PortGives a R r S₁ S₂ S₃) := by
  obtain ⟨R₁, dry, S₁, seal1, seal2, R₂, dry2, S₂, R₃', S₃, real, real2, hS₁, T⟩ :=
    chains_of_readKey k table file j r hr hno
  obtain ⟨R₃, hd, hA⟩ := dry3_of_chains T hS₁
  refine ⟨T.key_made, (R₁, R₂, R₃), ?_, fun hok hsh hb =>
    ⟨S₁, S₂, S₃, gives_of_chains a T hS₁ R₃ hA hok hsh hb⟩⟩
  unfold dryKey
  rw [T.first_dry]
  exact hd

/-- **A proof file: the same.** -/
theorem proof_read_gives (a : ℕ) (c : Params.ProofChains) (table : Params.TableName) (copy : ℕ)
    (request words : ByteArray) (block : Blk FirstEnd) (file : ByteArray) (r : TailRead)
    (hr : (readProof c table copy request words block file).fromStart = .ok r)
    (hno : proofRefusal c table block r = none) :
    tableKey c.shared.given.plan.field c.shared.given.cfg
        (tailPublic c table).lin.fold.index table 0 = some r.key ∧
      ∃ R : Rounds × Rounds × Rounds, dryProof c r.key block = some R ∧
        (okAt a (some R) = true → shapesFit a (Three.Whole.of R.1 R.2.1 R.2.2) = true →
          sealBare (Three.Whole.of R.1 R.2.1 R.2.2) = true →
          ∃ S₁ S₂ S₃, PortGives a R r S₁ S₂ S₃) := by
  obtain ⟨i, R₁, dry, S₁, seal1, seal2, R₂, dry2, S₂, R₃', S₃, real, real2, -, hS₁, T⟩ :=
    chains_of_readProof c table copy request words block file r hr hno
  obtain ⟨R₃, hd, hA⟩ := dry3_of_chains T hS₁
  refine ⟨T.key_made, (R₁, R₂, R₃), ?_, fun hok hsh hb =>
    ⟨S₁, S₂, S₃, gives_of_chains a T hS₁ R₃ hA hok hsh hb⟩⟩
  unfold dryProof
  rw [T.first_dry]
  exact hd

/-! ## From the check's yes to the reading -/

/-- **A key file: a yes of the check is a reading that returns and a decision that says yes.** j and
r are fixed by the two equations. -/
theorem key_check_reads (k : Params.KeyChains) (file : ByteArray) (table : Params.TableName)
    (h : Key.check k file = .ok table) :
    ∃ j r, Key.readTable k.oneTime.lin.fold.index k.oneTime.given.cfg file = .ok (table, j) ∧
      (Key.readKey k table file j).fromStart = .ok r ∧ Key.keyRefusal k table r = none := by
  unfold Key.check at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i table' j hrt
        split at h
        · cases h
        · rename_i t ht
          split at h
          · cases h
          · rename_i hno
            injection h with h'
            subst h'
            exact ⟨j, t, hrt, ht, hno⟩

/-- **A proof file: the same.** r is fixed by the equation. -/
theorem proof_check_reads (c : Params.ProofChains) (table : Params.TableName) (copy : ℕ)
    (request words : ByteArray) (reply : E) (links : Blk LinksResult) (file : ByteArray)
    (h : check c table copy request words reply links file = .accepted) :
    ∃ r, (readProof c table copy request words (firstBlock c.first links reply) file).fromStart =
        .ok r ∧ proofRefusal c table (firstBlock c.first links reply) r = none := by
  unfold check at h
  dsimp only at h
  split at h
  · cases h
  · rename_i r hr
    split at h
    · cases h
    · rename_i hno
      exact ⟨r, hr, hno⟩

end OnBytes.Maker
