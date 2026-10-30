-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/TypeFileOfRead.lean: at a value r that the verifier program's reader of a key file or
of a proof file has returned, the typing of the whole file (`typeFile`,
OnBytes/Maker/TypeFile.lean) returns at that r, under tests on the data and one hypothesis on the
file as read.

Statements and proofs. r is the caller's letter: the value of `Key.readKey` or of
`Proof.readProof`, run from the empty record of vertices: the reading that the program's checks
make themselves, before a proof file's reading is made lighter. This is a law of the reading: no
decision is asked, so the typing returns also at a file that a check refuses at its decision.
OnBytes/Maker/ThreeRead.lean opens such a reading into three descriptions and three readings.
OnBytes/Maker/RoundsAtTags.lean ties the third chain's rounds at the file's own roots to the rounds
at made-up names, from which the plain data are made. OnBytes/Maker/TablesFit.lean and
OnBytes/Maker/DataFitsOf.lean make the two tables return; OnBytes/Maker/TypeReturnsOf.lean lays the
six parts of the typing together.

Main names:
  `storedAt_of_fit`: the test `storedFit` gives `StoredAt` at the three chains.
  `sameItems_of_map`: two lists of rounds with the same items.
  `dry3_alike`: the three lists of rounds of which the data are made, the third with the stored
    tables, the items and the opened trees' shapes of the rounds under which the third chain was
    read.
  `returns_of_read`: `typeReturns` says yes, from `ThreeRead`.
  `typeFile_of_readKey`, `typeFile_of_readProof`: at a value r of the two readers.
Under "there is" in the last two stand R, fixed by `dryKey k r.key = some R` or
`dryProof c r.key block = some R`, and the typed string, fixed by `typeFile .. r = some π`.
What is asked besides the reading: (1) the tests `okAt a (some R)` on the three lists of rounds R,
which can be evaluated; of its parts the first two are used. For a proof file R hangs on the
first chain's block, and so on the request: it is a test for each request. (2) The three plans have
one number sb of bytes of a salt. (3) `SameTwice`: wherever two listed entries stand at one position
of one tree by the data's number, or of the stored table, they hold the same column and the same
salt.
In other words: at a reading that has returned and data that pass the tests, the typing can fail at
one of its own tests alone, `sameTwice`.
Limits: (3) is a hypothesis on the file as read and on the data's numbering. Where it fails, the
file shows two different pairs of a column and a salt with one leaf hash at one shape, start and
position (`sameTwice_or_collidesIn`, OnBytes/Maker/Page/TwiceOrCollide.lean; with `returns_of_read`:
OnBytes/Maker/Page/ReturnsOrCollide.lean), under their premises (`OwnAlone`, `OwnBook`, one
configuration's digest, `ShapeOneE`); nothing on how hard such a pair is to find. That the tests
pass is not proved. That a typed string is there is all that is said: it is there whatever cfg, the
silent rounds' plain parts, the binding leaf's salt and siblings and the decision `run` are. Nothing
is said of what the string holds, nor of any verifier's answer on it. Nothing on soundness.


-/
import OnBytes.Maker.ThreeRead
import OnBytes.Maker.RoundsAtTags
import OnBytes.Maker.Files
import OnBytes.Maker.TypeReturnsOf
import OnBytes.Maker.TypeTestLaws
import OnBytes.Maker.DataFitsOf
import OnBytes.Maker.ReadRuns

set_option autoImplicit false

namespace OnBytes.Maker

open OnBytes.Proof OnBytes.TieK
open _root_.Run _root_.Run.PQ
open OnBytes.Params (Rounds)

/-- The test on the stored tables, chain by chain. -/
theorem storedAt_of_fit {a : ℕ} {W : Three.Whole} (h : storedFit a W = true) :
    StoredAt a W.ds₁ ∧ StoredAt a W.ds₂ ∧ StoredAt a W.ds₃ := by
  unfold storedFit at h
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun d hd t ht => ?_, fun d hd t ht => ?_, fun d hd t ht => ?_⟩
  · have e := List.isEmpty_iff.1 (h1 d (List.mem_append_left _ hd))
    rw [e] at ht
    cases ht
  · have e := List.all_eq_true.1 (h2 d hd) t ht
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at e
    exact e
  · have e := List.isEmpty_iff.1 (h1 d (List.mem_append_right _ hd))
    rw [e] at ht
    cases ht

/-- Two lists of rounds whose lists of items are equal have the same items, member by member. -/
theorem sameItems_of_map : ∀ (l l' : Rounds), l.map (·.1.items) = l'.map (·.1.items) →
    SameItems (l.map (·.1)) (l'.map (·.1))
  | [], [], _ => .nil
  | [], _ :: _, e => by cases e
  | _ :: _, [], e => by cases e
  | x :: l, y :: l', e => by
    rw [List.map_cons, List.map_cons] at e
    obtain ⟨e1, e2⟩ := List.cons.inj e
    exact .cons e1 (sameItems_of_map l l' e2)

section
variable {p : TailPublic} {block1 : Blk FirstEnd} {start1 : Start} {file : ByteArray} {i : ℕ}
  {R₁ : Rounds} {dry : FirstEnd} {S₁ : Fmt.SpecX} {r : TailRead} {seal1 seal2 : ByteArray}
  {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃' : Rounds} {S₃ : Fmt.SpecX}
  {g₁ : Params.Given} {l₁ : ℕ} {x₁ : ByteArray} {n₁ : Fmt.Rand}

/-- **The three lists of rounds of which the data are made**, the third with the stored tables, the
items and the opened trees' shapes of the rounds under which the third chain was read. -/
theorem dry3_alike
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁) :
    ∃ R₃, Three.dry3 p r.key (R₁, dry) = some (R₁, R₂, R₃) ∧ StoredAlike R₃' R₃ ∧
      R₃'.map (·.1.items) = R₃.map (·.1.items) ∧
      R₃'.map (fun x => x.1.opens.map (·.1)) = R₃.map (fun x => x.1.opens.map (·.1)) := by
  have hr : r.first.roots.length = Three.rootsIn R₁ :=
    readChain_roots hS₁ [] file i r.first T.first_read
  obtain ⟨R₃, h3, hA, -, -, hI, hSh, -⟩ := secondRounds_tags_some p dry dry2 r.first r.shared
    (Three.rootsIn R₂) R₃' T.second_rounds
  rw [hr] at h3
  refine ⟨R₃, ?_, hA, hI, hSh⟩
  unfold Three.dry3
  rw [T.shared_dry]
  show (((secondBlock p.lin dry.lin (dry2.goesOn (Three.tagChain 2 (Three.rootsIn R₂)))).rounds
    (secondStart p dry (Three.tagChain 1 (Three.rootsIn R₁)))).bind fun R₃ =>
      some (R₁, R₂, R₃)) = _
  rw [h3]
  rfl

/-- **The typing's six parts return, from the record of the three chains' reading.** -/
theorem returns_of_read (C : CK) (a sb : ℕ) (cfg : ByteArray)
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁) (hn : n₁ ≠ .none) (R₃ : Rounds)
    (hA : StoredAlike R₃' R₃) (hI : R₃'.map (·.1.items) = R₃.map (·.1.items))
    (hSh : R₃'.map (fun x => x.1.opens.map (·.1)) = R₃.map (fun x => x.1.opens.map (·.1)))
    (hok : okAt a (some (R₁, R₂, R₃)) = true) (s₁ : g₁.plan.salt = sb)
    (s₂ : p.shared.given.plan.salt = sb) (s₃ : p.second.given.plan.salt = sb)
    (hT : SameTwice (Three.Whole.of R₁ R₂ R₃) r) :
    typeReturns C a (Three.Whole.of R₁ R₂ R₃) sb cfg r = true := by
  have hfit' : Three.Whole.fits R₁ R₂ R₃ 2 = true := (okAt_parts hok).fits
  have hst' : storedFit a (Three.Whole.of R₁ R₂ R₃) = true := (okAt_parts hok).stored
  obtain ⟨a₁, a₂, a₃⟩ := storedAt_of_fit hst'
  have hS₂ : Params.describeWith p.shared.given p.lab₂
      (Params.Shared.statement p.table r.place.root) (.given r.place.root) R₂ 0 = some S₂ :=
    T.shared_spec
  have hS₃ : Params.describeWith p.second.given p.lab₃
      (Params.Second.statement seal1 seal2) .inFile R₃' (secondFirstTree r.first) = some S₃ :=
    T.second_spec
  have F : FileFits (Three.Whole.of R₁ R₂ R₃) sb a S₁ S₂ S₃ :=
    fileFits_of hfit' hS₁ hS₂ hS₃ hSh hA s₁ s₂ s₃ a₁ a₂ a₃
  have hr₁ : S₁.base.rand ≠ .none := by
    rw [describeWith_rand hS₁]
    exact hn
  have RT : RunsThere r :=
    runsThere_of S₁ S₂ S₃ r file [] r.first.out.seen r.shared.out.seen i r.place.next
      r.shared.next r.first.next r.shared.next r.second.next T.first_read T.shared_read
      T.second_read hr₁ (shared_rand T.shared_spec) (second_rand T.second_spec)
  have h₁ : SameItems (R₁.map (·.1)) S₁.base.rounds := by
    rw [(describeWith_facts hS₁).1]
    exact sameItems_refl _
  have h₂ : SameItems (R₂.map (·.1)) S₂.base.rounds := by
    rw [(describeWith_facts hS₂).1]
    exact sameItems_refl _
  have h₃ : SameItems (R₃.map (·.1)) S₃.base.rounds := by
    rw [(describeWith_facts hS₃).1]
    exact sameItems_of_map R₃ R₃' hI.symm
  exact typeReturns_of C a R₁ R₂ R₃ sb cfg r S₁ S₂ S₃ [] r.first.out.seen r.shared.out.seen file i
    r.place.next r.shared.next r.first.next r.shared.next r.second.next T.first_read T.shared_read
    T.second_read hr₁ h₁ h₂ h₃
    (tabsWFull_of_read _ sb a S₁ S₂ S₃ F r file [] r.first.out.seen r.shared.out.seen i
      r.place.next r.shared.next r.first.next r.shared.next r.second.next T.first_read
      T.shared_read T.second_read RT hT)
    (extWFull_of_read _ sb a cfg S₁ S₂ S₃ F r file [] r.first.out.seen r.shared.out.seen i
      r.place.next r.shared.next r.first.next r.shared.next r.second.next T.first_read
      T.shared_read T.second_read hT)

end

/-- **A key file: at the value r of the program's reader the typing of the whole file returns.**
j: the place behind the table's record, as `Key.readTable` gives it to the program's check. -/
theorem typeFile_of_readKey (C : CK) (a : ℕ) (k : Params.KeyChains) (table : Params.TableName)
    (file : ByteArray) (j : ℕ) (r : TailRead)
    (h : (Key.readKey k table file j).fromStart = .ok r) :
    ∃ R : Rounds × Rounds × Rounds, dryKey k r.key = some R ∧
      ∀ (sb : ℕ) (cfg : ByteArray), okAt a (some R) = true → k.oneTime.given.plan.salt = sb →
        k.shared.given.plan.salt = sb → k.second.given.plan.salt = sb →
        SameTwice (Three.Whole.of R.1 R.2.1 R.2.2) r →
        ∀ {TF TJ T3 Xi : Type} (tF : TF) (tJ : TJ) (t3 : T3) (silent : Xi → TF → TJ → T3 → Bool)
          (run : Xi → View → View → View → Bool) (pF : TF) (pJ : TJ) (p3 : T3) (salt : ByteArray)
          (path : List ByteArray),
          ∃ π, typeFile C a (Three.Whole.of R.1 R.2.1 R.2.2) tF tJ t3 silent run sb cfg pF pJ p3
            salt path r = some π := by
  obtain ⟨R₁, dry, S₁, seal1, seal2, R₂, dry2, S₂, R₃', S₃, hS₁, T⟩ :=
    threeRead_of_readKey k table file j r h
  have hS₁' : Params.describeWith k.oneTime.given Params.labelOneTime
      (Params.OneTime.statement table) .inFile R₁ 0 = some S₁ := hS₁
  obtain ⟨R₃, hd, hA, hI, hSh⟩ := dry3_alike T hS₁'
  refine ⟨(R₁, R₂, R₃), ?_, ?_⟩
  · unfold dryKey
    rw [T.first_dry]
    exact hd
  · intro sb cfg hok s₁ s₂ s₃ hT TF TJ T3 Xi tF tJ t3 silent run pF pJ p3 salt path
    have hret := returns_of_read C a sb cfg T hS₁' (fun e => by cases e) R₃ hA hI hSh hok s₁ s₂
      s₃ hT
    rw [← typeFile_isSome C a _ tF tJ t3 silent run sb cfg pF pJ p3 salt path r] at hret
    exact Option.isSome_iff_exists.1 hret

/-- **A proof file: at the value r of the program's reader the typing of the whole file returns.**
block: the first chain's block; the program's check lays `firstBlock c.first links reply`. -/
theorem typeFile_of_readProof (C : CK) (a : ℕ) (c : Params.ProofChains)
    (table : Params.TableName) (copy : ℕ) (request words : ByteArray) (block : Blk FirstEnd)
    (file : ByteArray) (r : TailRead)
    (h : (readProof c table copy request words block file).fromStart = .ok r) :
    ∃ R : Rounds × Rounds × Rounds, dryProof c r.key block = some R ∧
      ∀ (sb : ℕ) (cfg : ByteArray), okAt a (some R) = true → c.first.given.plan.salt = sb →
        c.shared.given.plan.salt = sb → c.second.given.plan.salt = sb →
        SameTwice (Three.Whole.of R.1 R.2.1 R.2.2) r →
        ∀ {TF TJ T3 Xi : Type} (tF : TF) (tJ : TJ) (t3 : T3) (silent : Xi → TF → TJ → T3 → Bool)
          (run : Xi → View → View → View → Bool) (pF : TF) (pJ : TJ) (p3 : T3) (salt : ByteArray)
          (path : List ByteArray),
          ∃ π, typeFile C a (Three.Whole.of R.1 R.2.1 R.2.2) tF tJ t3 silent run sb cfg pF pJ p3
            salt path r = some π := by
  obtain ⟨i, R₁, dry, S₁, seal1, seal2, R₂, dry2, S₂, R₃', S₃, -, hS₁, T⟩ :=
    threeRead_of_readProof c table copy request words block file r h
  have hS₁' : Params.describeWith c.first.given Params.labelFirst
      (Params.First.statement table copy request words) .inFile R₁ 0 = some S₁ := hS₁
  obtain ⟨R₃, hd, hA, hI, hSh⟩ := dry3_alike T hS₁'
  refine ⟨(R₁, R₂, R₃), ?_, ?_⟩
  · unfold dryProof
    rw [T.first_dry]
    exact hd
  · intro sb cfg hok s₁ s₂ s₃ hT TF TJ T3 Xi tF tJ t3 silent run pF pJ p3 salt path
    have hret := returns_of_read C a sb cfg T hS₁' (fun e => by cases e) R₃ hA hI hSh hok s₁ s₂
      s₃ hT
    rw [← typeFile_isSome C a _ tF tJ t3 silent run sb cfg pF pJ p3 salt path r] at hret
    exact Option.isSome_iff_exists.1 hret

end OnBytes.Maker
