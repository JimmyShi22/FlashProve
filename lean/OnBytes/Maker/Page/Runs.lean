-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/Runs.lean: from the verifier program's own reading of a key file or a proof file,
tests on the data, and the nine fields `GRows` (seven laws on typed oracle functions g, two
conditions on the instance in a query), to what the three chains' values under g hold: the draws and
the first chain's seal.

OnBytes/TypedOracleCompiler/Joined/K/RunsLineRead.lean computes the values that the three chains of a file have
under g, under the 43 hypotheses of its record `ReadL`. This file brings these down, at the
description, the wire record and the typed proof string of a whole file (OnBytes/Maker/). Nine speak
of g or of the instance in a query: they stay (`GRows`, OnBytes/Maker/Page/RunsTools.lean). Of the
other 34: ten hold with no hypothesis; twelve from the reading, the first chain's description, the
equation on `Three.dry3` and the tests `okAt`, and two more from these tests; three from the bounds
`SmallThree`; four from a value of the typing; three from the bound on a round's blocks. With
OnBytes/Maker/DrawsOfLine.lean that gives two of the debts on g of a file's compiled yes.

The data are a letter W with the equation W = `Three.Whole.of` R₁ R₂ R₃, since the types of a
written file's letters hang on its data.

Main theorems.
  `readL_of`: `ReadL`, for any g and any function O on strings: from the test `Three.Whole.fits`;
    the three descriptions' rounds; three yeses of the strict reader over O; no more than K blocks a
    round; two lists of rounds that are not empty; a value of the typing; `GRows`.
  `dry3_alike`: the third list of rounds of which the data are made has the stored tables, entries,
    kinds and items of the rounds under which the third chain was read.
  `ne₃_of_ok`: the description under which the third chain was read has a round.
  `readL_of_read`: `ReadL` at the format's realised oracle, from the record of the program's own
    reading (`ThreeRead`, OnBytes/Maker/ThreeRead.lean).
  `draws_of_read`: `DrawsHeldA` (OnBytes/Maker/AcceptAtA.lean) at whatever values the three chains
    have under g.
  `sealAt_of_read`: g answers the query that holds the chaining value in which the first chain ends
    with that chain's seal as read.

What the last three ask: `ThreeRead` at the caller's reading r; the first chain's description; that
the data are made of the rounds that `Three.dry3` gives at r's key, the third list at made-up names
of the trees that the third chain takes over, not the rounds under which that chain was read; the
bounds that the hash's domain asks for (`SmallThree`, OnBytes/Maker/Page/AtOracle.lean: a test on
each file and its three descriptions); the tests `okAt`; no more than K blocks a round; that the
typing returns; `GRows` at the realised oracle. The last two also: that the kit of verifier messages
fits the three plans' fields (`KitFits`: OnBytes/Maker/Page/Kits.lean), and the three runs' values.

WHICH READING. r is the file as the reader returns it, with all openings. Before it decides on a
proof file the program hands on a lighter form of the first chain, without its openings
(`ChainRead.light`, OnBytes/Chain/Session.lean; handed on in OnBytes/Proof/File.lean): at that form
the typing returns nothing wherever the first chain opens a tree; no law here says so.

LETTERS THAT NOTHING HERE TIES. cfg, sb, salt, path and the three silent rounds' messages pF, pJ, p3
enter through `typeFile` alone (`GRows` speaks of the three messages): nothing here ties cfg to the
digest that the chains' parameter bytes hold, nor sb to the plans' bytes of a salt. salt is the salt
of the request tree's leaf, not a chain's: the typed string's own salt is the first chain's run
value (`value_salt`, OnBytes/Maker/Page/AtValue.lean). f stands in `blocks` alone.

THE TWO SEALS. Nothing in `DrawsHeldA` ties either seal's value. The first: `sealAt_of_read`. The
second: its value enters in the field `s3` of `GRows` alone; no statement here gives the second seal
of the typed run.

What is not claimed. None of these hypotheses: `GRows` above all. That the three chains have values
under g. Nothing on soundness.


-/
import OnBytes.Maker.Page.RunsTools

set_option autoImplicit false

namespace OnBytes.Maker.Page

open Rom TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Joined.K TypedOracleCompiler.Compile.Batch
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ _root_.Compile.Joined
open OnBytes.Params (Rounds)

section
variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {t : Tag} (C : CK) (K : ℕ)
  (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (a : ℕ) (R₁ R₂ R₃ : Rounds)
  {TF TJ T3 Xi : Type} (tF : TF) (tJ : TJ) (t3 : T3) (silent : Xi → TF → TJ → T3 → Bool)
  (run : Xi → View → View → View → Bool)

/-- **`ReadL` at a whole file's description, wire record and typed string, and at the three chains
of a reading r, for any g and O.** -/
theorem readL_of (W : Three.Whole) (hW : W = Three.Whole.of R₁ R₂ R₃)
    (embP : PlainPart (chainsOf C (WholeD.of a W) tF tJ t3).sh (chainsOf C (WholeD.of a W) tF tJ t3).ann →
      PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t)) (xin : Xi → Option X) (cms : List (Dig 256))
    (x : Xi) (π : OneProtocolProof 256 (wholeDesc C (WholeD.of a W) tF tJ t3 silent run).batch)
    (g : Fam (typedOracleFamily 256 (K + 1) L)) (O : ByteArray → ByteArray) (S₁ S₂ S₃ : Fmt.SpecX)
    (r : Proof.TailRead) (R₃' : Rounds) (r₁ r₂ : Fmt.Round × List Fmt.Stored)
    (hfit : Three.Whole.fits R₁ R₂ R₃ 2 = true) (e₁ : R₁.getLast? = some r₁)
    (e₂ : R₂.getLast? = some r₂) (hS₁ : S₁.base.rounds = R₁.map (·.1))
    (hS₂ : S₂.base.rounds = R₂.map (·.1)) (hS₃ : S₃.base.rounds = R₃'.map (·.1))
    (hE : R₃'.map (·.1.entry) = R₃.map (·.1.entry)) (hK : R₃'.map (·.1.kind) = R₃.map (·.1.kind))
    (hI : R₃'.map (·.1.items) = R₃.map (·.1.items))
    (rd₁ : ∃ seen b i j, Fmt.readChainX (m := Id) (Fmt.HO O) S₁ seen b i = some (r.first.out, j))
    (rd₂ : ∃ seen b i j, Fmt.readChainX (m := Id) (Fmt.HO O) S₂ seen b i = some (r.shared.out, j))
    (rd₃ : ∃ seen b i j, Fmt.readChainX (m := Id) (Fmt.HO O) S₃ seen b i = some (r.second.out, j))
    (f : Fmt.Fld)
    (blocks : ∀ d ∈ (WholeD.of a W).ds₁ ++ ((WholeD.of a W).ds₂ ++ (WholeD.of a W).ds₃),
      (bsRound f d.entry d.kind).b ≤ K) (ne₁ : (R₁.map (·.1)).dropLast ≠ [])
    (ne₃ : S₃.base.rounds ≠ []) (pF : TF) (pJ : TJ) (p3 : T3) (tabs : List (ℕ × List (ℕ × Row3)))
    (ext : (oneExternalString (2 ^ (WholeD.of a W).a) SgX).Pos → Option (Opening 256 SgX)) (salt : ByteArray)
    (path : List ByteArray)
    (hπ : toBPrfW C (WholeD.of a W) tF tJ t3 silent run pF pJ p3 tabs ext salt path r = some π)
    (Gr : GRows (L := L) (t := t) (C := C) (K := K) (rF := plainRS TF tF) (rJ := plainRS TJ tJ)
      (r3 := plainRS T3 t3) (aJ := RAnn.ofShared .sh _) (ds₁ := toRDs (WholeD.of a W).ds₁)
      (ds₂ := toRDs (WholeD.of a W).ds₂) (ds₃ := toRDs (WholeD.of a W).ds₃)
      (D := wholeDesc C (WholeD.of a W) tF tJ t3 silent run) embP xin cms x π g O [] [] S₁ S₂ S₃
      r.first.out r.shared.out r.second.out (R₁.map (·.1)).dropLast) :
    ReadL (L := L) (t := t) (C := C) (K := K) (rF := plainRS TF tF) (rJ := plainRS TJ tJ)
      (r3 := plainRS T3 t3) (aJ := RAnn.ofShared .sh _) (ds₁ := toRDs (WholeD.of a W).ds₁)
      (ds₂ := toRDs (WholeD.of a W).ds₂) (ds₃ := toRDs (WholeD.of a W).ds₃)
      (D := wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
      (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) embP xin cms x π g O chal
      (wireSilent (K + 1) TF tF _) (wireSilent (K + 1) TJ tJ _) (wireSilent (K + 1) T3 t3 _) [] []
      [] S₁ S₂ S₃ r.first.out r.shared.out r.second.out (R₁.map (·.1)).dropLast r₁.1 := by
  subst hW
  obtain ⟨f₁, f₂, f₃⟩ := rootsFit_of_fits R₁ R₂ R₃ hfit
  obtain ⟨⟨q₁, w₁, s₁⟩, q₂, w₂, s₂⟩ := seals_of_fits R₁ R₂ R₃ hfit
  cases Option.some.inj (w₁.symm.trans e₁)
  cases Option.some.inj (w₂.symm.trans e₂)
  have hr₁ : S₁.base.rounds = (R₁.map (·.1)).dropLast ++ [r₁.1] := hS₁.trans (rounds_split R₁ r₁ e₁)
  obtain ⟨pl₁, pl₂, pl₃, h1, h2, h3, hp, -⟩ := toBPrfW_parts C (WholeD.of a (Three.Whole.of R₁ R₂
    R₃)) tF tJ t3 pF pJ p3 tabs
    silent run ext salt path r π hπ
  obtain ⟨sn, bb, ii, jj, ee⟩ := rd₁
  have hn : (R₁.map (·.1)).dropLast.length + 1 = r.first.out.rounds.toList.length := by
    rw [rounds_length _ S₁ sn bb ii _ jj ee, hr₁, List.length_append]
    rfl
  have htk := take_dropLast r.first.out.rounds.toList _ hn
  have F₁ := fit₁_of a R₁ R₂ R₃ f₁
  have F₂ : TypedOracleCompiler.Run.PQ.FitL (toRDs (WholeD.of a (Three.Whole.of R₁ R₂ R₃)).ds₂) S₂.base.rounds :=
    hS₂ ▸ fit₂_of a R₁ R₂ R₃ f₂
  have F₃ : TypedOracleCompiler.Run.PQ.FitL (toRDs (WholeD.of a (Three.Whole.of R₁ R₂ R₃)).ds₃) S₃.base.rounds := by
    rw [hS₃]
    refine fitL_congr _ _ _ (fit₃_of a R₁ R₂ R₃ f₃) ?_ ?_ ?_
    · rw [List.map_map, List.map_map]; exact hE.symm
    · rw [List.map_map, List.map_map]; exact hK.symm
    · rw [List.map_map, List.map_map]; exact hI.symm
  exact
    { read₁ := ⟨sn, bb, ii, jj, ee⟩
      read₂ := rd₂
      read₃ := rd₃
      rounds₁ := hr₁
      sKind := s₁.kind
      sItems := s₁.items
      sPoss := s₁.poss
      sTrits := s₁.trits
      sDrawE := s₁.drawE
      sDrawNZ := s₁.drawNZ
      sWork := s₁.work
      fit₁ := F₁
      fit₂ := F₂
      fit₃ := F₃
      room₁ := room_of_fitL f K _ _ F₁ fun d hd => by
        obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
        exact blocks d' (List.mem_append_left _ hd')
      room₂ := room_of_fitL f K _ _ F₂ fun d hd => by
        obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
        exact blocks d' (List.mem_append_right _ (List.mem_append_left _ hd'))
      room₃ := room_of_fitL f K _ _ F₃ fun d hd => by
        obtain ⟨d', hd', rfl⟩ := List.mem_map.1 hd
        exact blocks d' (List.mem_append_right _ (List.mem_append_right _ hd'))
      seal₂ := sealLast_of a R₁ R₂ R₃ f₂ r₂.1 (by rw [List.getLast?_map, e₂]; rfl)
        s₂.fit
      some₁ := ne₁
      some₃ := ne₃
      wire₁ := hw₁ C K chal (WholeD.of a (Three.Whole.of R₁ R₂ R₃)) tF tJ t3 silent run
      wire₂ := hw₂ C K chal (WholeD.of a (Three.Whole.of R₁ R₂ R₃)) tF tJ t3 silent run
      wire₃ := hw₃ C K chal (WholeD.of a (Three.Whole.of R₁ R₂ R₃)) tF tJ t3 silent run
      joinSh := joinKind TJ tJ
      joinJ := wireSilent_depthJ (K + 1) TJ tJ _
      join0 := wireSilent_depth0 (K + 1) TJ tJ _
      front := rfl
      front2 := Nat.zero_le _
      seam := rfl
      seam2 := Nat.zero_le _
      roots := by
        rw [toBPrfW_roots C (WholeD.of a (Three.Whole.of R₁ R₂ R₃)) tF tJ t3 silent run pF pJ p3
          tabs ext salt path r π hπ,
          rootsT_take _ S₁ sn bb ii _ jj ee _ r₁.1 hr₁ s₁.items]
        simp only [List.nil_append, List.append_nil]
        rfl
      plains₁ := by
        rw [pls₁_A _ π _ _ _ hp, htk, ← plainsT_line]
        exact h1
      plains₂ := by
        rw [pls₂_A _ π _ _ _ hp, ← plainsT_line]
        exact h2
      plains₃ := by
        rw [pls₃_A _ π _ _ _ hp, ← plainsT_line]
        exact h3
      row₁ := Gr.row₁
      row₂ := Gr.row₂
      row₃ := Gr.row₃
      s0 := Gr.s0
      sG := Gr.sG
      s4 := Gr.s4
      s3 := Gr.s3
      late₁ := Gr.late₁
      late₃ := Gr.late₃ }

end

/-! ## From the program's reading -/

section
open OnBytes.Proof (TailPublic FirstEnd SharedEnd TailRead)
variable {p : TailPublic} {block1 : Blk FirstEnd} {start1 : Start} {file : ByteArray} {i : ℕ}
  {R₁ : Rounds} {dry : FirstEnd} {S₁ : Fmt.SpecX} {r : TailRead} {seal1 seal2 : ByteArray}
  {R₂ : Rounds} {dry2 : SharedEnd} {S₂ : Fmt.SpecX} {R₃' : Rounds} {S₃ : Fmt.SpecX}
  {g₁ : Params.Given} {l₁ : ℕ} {x₁ : ByteArray} {n₁ : Fmt.Rand} {R₃ : Rounds}

/-- The third list of rounds of which the data are made has the stored tables, entries, kinds and
items of the rounds under which the third chain was read. -/
theorem dry3_alike
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁)
    (hR : Three.dry3 p r.key (R₁, dry) = some (R₁, R₂, R₃)) :
    StoredAlike R₃' R₃ ∧ R₃'.map (·.1.entry) = R₃.map (·.1.entry) ∧
      R₃'.map (·.1.kind) = R₃.map (·.1.kind) ∧ R₃'.map (·.1.items) = R₃.map (·.1.items) := by
  have hr : r.first.roots.length = Three.rootsIn R₁ :=
    readChain_roots hS₁ [] file i r.first T.first_read
  obtain ⟨R, h3, hA, hE, hK, hI, -⟩ := secondRounds_tags_some p dry dry2 r.first r.shared
    (Three.rootsIn R₂) R₃' T.second_rounds
  rw [hr] at h3
  unfold Three.dry3 at hR
  rw [T.shared_dry] at hR
  have hR' : (((Proof.secondBlock p.lin dry.lin
      (dry2.goesOn (Three.tagChain 2 (Three.rootsIn R₂)))).rounds
      (Proof.secondStart p dry (Three.tagChain 1 (Three.rootsIn R₁)))).bind fun R₃ =>
        some (R₁, R₂, R₃)) = some (R₁, R₂, R₃) := hR
  rw [h3] at hR'
  obtain rfl : R = R₃ := congrArg (fun z => z.2.2) (Option.some.inj hR')
  exact ⟨hA, hE, hK, hI⟩

/-- The description under which the third chain was read has a round, where the tests under which
the data are laid pass. -/
theorem ne₃_of_ok {a : ℕ}
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁)
    (hR : Three.dry3 p r.key (R₁, dry) = some (R₁, R₂, R₃))
    (hok : okAt a (some (R₁, R₂, R₃)) = true) : S₃.base.rounds ≠ [] := by
  intro e
  rw [(describeWith_facts T.second_spec).1] at e
  have e' : R₃' = [] := List.map_eq_nil_iff.1 e
  have hE := (dry3_alike T hS₁ hR).2.1
  rw [e'] at hE
  have e3 : R₃ = [] := List.map_eq_nil_iff.1 hE.symm
  exact ((someFit_iff (R₁, R₂, R₃)).1 (okAt_parts hok).rounds).2 (by rw [e3]; rfl)

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {t : Tag} (C : CK) (K : ℕ)
  (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (a : ℕ)
  {TF TJ T3 Xi : Type} (tF : TF) (tJ : TJ) (t3 : T3) (silent : Xi → TF → TJ → T3 → Bool)
  (run : Xi → View → View → View → Bool)

/-- **`ReadL` at the format's realised oracle, from the program's own reading of a file, tests, and
the nine fields on g.** r₁ is fixed by the equation: the last of the first chain's rounds. -/
theorem readL_of_read (W : Three.Whole) (hW : W = Three.Whole.of R₁ R₂ R₃)
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁)
    (hR : Three.dry3 p r.key (R₁, dry) = some (R₁, R₂, R₃)) (hs : SmallThree S₁ S₂ S₃ file)
    (hok : okAt a (some (R₁, R₂, R₃)) = true) (f : Fmt.Fld)
    (blocks : ∀ d ∈ (WholeD.of a W).ds₁ ++ ((WholeD.of a W).ds₂ ++ (WholeD.of a W).ds₃),
      (bsRound f d.entry d.kind).b ≤ K)
    (embP : PlainPart (chainsOf C (WholeD.of a W) tF tJ t3).sh (chainsOf C (WholeD.of a W) tF tJ t3).ann →
      PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t)) (xin : Xi → Option X) (cms : List (Dig 256))
    (x : Xi) (π : OneProtocolProof 256 (wholeDesc C (WholeD.of a W) tF tJ t3 silent run).batch)
    (g : Fam (typedOracleFamily 256 (K + 1) L)) (sb : ℕ) (cfg : ByteArray) (pF : TF) (pJ : TJ) (p3 : T3)
    (salt : ByteArray) (path : List ByteArray)
    (hπ : typeFile C a W tF tJ t3 silent run sb cfg pF pJ p3 salt path r = some π)
    (Gr : GRows (L := L) (t := t) (C := C) (K := K) (rF := plainRS TF tF) (rJ := plainRS TJ tJ)
      (r3 := plainRS T3 t3) (aJ := RAnn.ofShared .sh _) (ds₁ := toRDs (WholeD.of a W).ds₁)
      (ds₂ := toRDs (WholeD.of a W).ds₂) (ds₃ := toRDs (WholeD.of a W).ds₃)
      (D := wholeDesc C (WholeD.of a W) tF tJ t3 silent run) embP xin cms x π g Fmt.oracle [] [] S₁
      S₂ S₃ r.first.out r.shared.out r.second.out (R₁.map (·.1)).dropLast) :
    ∃ r₁, R₁.getLast? = some r₁ ∧ ReadL (L := L) (t := t) (C := C) (K := K) (rF := plainRS TF tF)
      (rJ := plainRS TJ tJ) (r3 := plainRS T3 t3) (aJ := RAnn.ofShared .sh _)
      (ds₁ := toRDs (WholeD.of a W).ds₁) (ds₂ := toRDs (WholeD.of a W).ds₂)
      (ds₃ := toRDs (WholeD.of a W).ds₃) (D := wholeDesc C (WholeD.of a W) tF tJ t3 silent run)
      (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run) embP xin cms x π g Fmt.oracle chal
      (wireSilent (K + 1) TF tF _) (wireSilent (K + 1) TJ tJ _) (wireSilent (K + 1) T3 t3 _) [] []
      [] S₁ S₂ S₃ r.first.out r.shared.out r.second.out (R₁.map (·.1)).dropLast r₁.1 := by
  subst hW
  have hfit : Three.Whole.fits R₁ R₂ R₃ 2 = true := (okAt_parts hok).fits
  obtain ⟨⟨r₁, w₁, -⟩, r₂, w₂, -⟩ := seals_of_fits R₁ R₂ R₃ hfit
  obtain ⟨-, hE, hK, hI⟩ := dry3_alike T hS₁ hR
  obtain ⟨q₁, q₂, q₃⟩ := three_atOracle T hs
  obtain ⟨tabs, ext, -, -, hπ'⟩ := typeFile_some C a (Three.Whole.of R₁ R₂ R₃) tF tJ t3 silent run
    sb cfg pF pJ p3 salt path r π hπ
  exact ⟨r₁, w₁, readL_of C K chal a R₁ R₂ R₃ tF tJ t3 silent run _ rfl embP xin cms x π g
    Fmt.oracle S₁
    S₂ S₃ r R₃' r₁ r₂ hfit w₁ w₂ (describeWith_facts hS₁).1 (describeWith_facts T.shared_spec).1
    (describeWith_facts T.second_spec).1 hE hK hI ⟨_, _, _, _, q₁⟩ ⟨_, _, _, _, q₂⟩
    ⟨_, _, _, _, q₃⟩ f blocks (ne₁_of_ok hok) (ne₃_of_ok T hS₁ hR hok) pF pJ p3 tabs ext salt path
      hπ'
    Gr⟩

/-- **The draws, at whatever values the three chains have under g.** -/
theorem draws_of_read (W : Three.Whole) (hW : W = Three.Whole.of R₁ R₂ R₃)
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁)
    (hR : Three.dry3 p r.key (R₁, dry) = some (R₁, R₂, R₃)) (hs : SmallThree S₁ S₂ S₃ file)
    (hok : okAt a (some (R₁, R₂, R₃)) = true) (f : Fmt.Fld)
    (blocks : ∀ d ∈ (WholeD.of a W).ds₁ ++ ((WholeD.of a W).ds₂ ++ (WholeD.of a W).ds₃),
      (bsRound f d.entry d.kind).b ≤ K)
    (embP : PlainPart (chainsOf C (WholeD.of a W) tF tJ t3).sh (chainsOf C (WholeD.of a W) tF tJ t3).ann →
      PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t)) (xin : Xi → Option X) (cms : List (Dig 256))
    (x : Xi) (π : OneProtocolProof 256 (wholeDesc C (WholeD.of a W) tF tJ t3 silent run).batch)
    (g : Fam (typedOracleFamily 256 (K + 1) L)) (sb : ℕ) (cfg : ByteArray) (pF : TF) (pJ : TJ) (p3 : T3)
    (salt : ByteArray) (path : List ByteArray)
    (hπ : typeFile C a W tF tJ t3 silent run sb cfg pF pJ p3 salt path r = some π)
    (Gr : GRows (L := L) (t := t) (C := C) (K := K) (rF := plainRS TF tF) (rJ := plainRS TJ tJ)
      (r3 := plainRS T3 t3) (aJ := RAnn.ofShared .sh _) (ds₁ := toRDs (WholeD.of a W).ds₁)
      (ds₂ := toRDs (WholeD.of a W).ds₂) (ds₃ := toRDs (WholeD.of a W).ds₃)
      (D := wholeDesc C (WholeD.of a W) tF tJ t3 silent run) embP xin cms x π g Fmt.oracle [] [] S₁
      S₂ S₃ r.first.out r.shared.out r.second.out (R₁.map (·.1)).dropLast)
    (hkit₁ : TypedOracleCompiler.Run.PQ.KitFits S₁.base.plan.field C K chal)
    (hkit₂ : TypedOracleCompiler.Run.PQ.KitFits S₂.base.plan.field C K chal)
    (hkit₃ : TypedOracleCompiler.Run.PQ.KitFits S₃.base.plan.field C K chal)
    (A : Out 256 (chainsOf C (WholeD.of a W) tF tJ t3).c₁)
    (B : Out 256 (chainsOf C (WholeD.of a W) tF tJ t3).c₂)
    (E : Out 256 (chainsOf C (WholeD.of a W) tF tJ t3).c₃)
    (h₁ : (run₁ t (wholeDesc C (WholeD.of a W) tF tJ t3 silent run) (wqWhole C K chal (WholeD.of a
      W) tF tJ t3 silent run) embP xin cms x π).det g = some A)
    (h₂ : (run₂ t (wholeDesc C (WholeD.of a W) tF tJ t3 silent run) (wqWhole C K chal (WholeD.of a
      W) tF tJ t3 silent run) embP xin cms x π A).det g = some B)
    (h₃ : (run₃ t (wholeDesc C (WholeD.of a W) tF tJ t3 silent run) (wqWhole C K chal (WholeD.of a
      W) tF tJ t3 silent run) embP xin cms x π A B).det g = some E) :
    DrawsHeldA C (WholeD.of a W) tF tJ t3 r (glue A B E).1 := by
  subst hW
  obtain ⟨r₁, -, H⟩ := readL_of_read C K chal a tF tJ t3 silent run _ rfl T hS₁ hR hs hok f blocks
    embP xin cms x π g sb cfg pF pJ p3 salt path hπ Gr
  exact draws_of_readL C K chal _ tF tJ t3 silent run embP xin cms x π g Fmt.oracle [] S₁ S₂ S₃ r _
    _ oracle_32 hkit₁ hkit₂ hkit₃ H A B E h₁ h₂ h₃

/-- **g answers the query that holds the chaining value in which the first chain ends with that
chain's seal as read.** -/
theorem sealAt_of_read (W : Three.Whole) (hW : W = Three.Whole.of R₁ R₂ R₃)
    (T : ThreeRead p block1 start1 file i R₁ dry S₁ r seal1 seal2 R₂ dry2 S₂ R₃' S₃)
    (hS₁ : Params.describeWith g₁ l₁ x₁ n₁ R₁ 0 = some S₁)
    (hR : Three.dry3 p r.key (R₁, dry) = some (R₁, R₂, R₃)) (hs : SmallThree S₁ S₂ S₃ file)
    (hok : okAt a (some (R₁, R₂, R₃)) = true) (f : Fmt.Fld)
    (blocks : ∀ d ∈ (WholeD.of a W).ds₁ ++ ((WholeD.of a W).ds₂ ++ (WholeD.of a W).ds₃),
      (bsRound f d.entry d.kind).b ≤ K)
    (embP : PlainPart (chainsOf C (WholeD.of a W) tF tJ t3).sh (chainsOf C (WholeD.of a W) tF tJ t3).ann →
      PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t)) (xin : Xi → Option X) (cms : List (Dig 256))
    (x : Xi) (π : OneProtocolProof 256 (wholeDesc C (WholeD.of a W) tF tJ t3 silent run).batch)
    (g : Fam (typedOracleFamily 256 (K + 1) L)) (sb : ℕ) (cfg : ByteArray) (pF : TF) (pJ : TJ) (p3 : T3)
    (salt : ByteArray) (path : List ByteArray)
    (hπ : typeFile C a W tF tJ t3 silent run sb cfg pF pJ p3 salt path r = some π)
    (Gr : GRows (L := L) (t := t) (C := C) (K := K) (rF := plainRS TF tF) (rJ := plainRS TJ tJ)
      (r3 := plainRS T3 t3) (aJ := RAnn.ofShared .sh _) (ds₁ := toRDs (WholeD.of a W).ds₁)
      (ds₂ := toRDs (WholeD.of a W).ds₂) (ds₃ := toRDs (WholeD.of a W).ds₃)
      (D := wholeDesc C (WholeD.of a W) tF tJ t3 silent run) embP xin cms x π g Fmt.oracle [] [] S₁
      S₂ S₃ r.first.out r.shared.out r.second.out (R₁.map (·.1)).dropLast)
    (hkit₁ : TypedOracleCompiler.Run.PQ.KitFits S₁.base.plan.field C K chal)
    (hkit₂ : TypedOracleCompiler.Run.PQ.KitFits S₂.base.plan.field C K chal)
    (hkit₃ : TypedOracleCompiler.Run.PQ.KitFits S₃.base.plan.field C K chal)
    (A : Out 256 (chainsOf C (WholeD.of a W) tF tJ t3).c₁)
    (B : Out 256 (chainsOf C (WholeD.of a W) tF tJ t3).c₂)
    (E : Out 256 (chainsOf C (WholeD.of a W) tF tJ t3).c₃)
    (h₁ : (run₁ t (wholeDesc C (WholeD.of a W) tF tJ t3 silent run) (wqWhole C K chal (WholeD.of a
      W) tF tJ t3 silent run) embP xin cms x π).det g = some A)
    (h₂ : (run₂ t (wholeDesc C (WholeD.of a W) tF tJ t3 silent run) (wqWhole C K chal (WholeD.of a
      W) tF tJ t3 silent run) embP xin cms x π A).det g = some B)
    (h₃ : (run₃ t (wholeDesc C (WholeD.of a W) tF tJ t3 silent run) (wqWhole C K chal (WholeD.of a
      W) tF tJ t3 silent run) embP xin cms x π A B).det g = some E) :
    ∀ ρ₁, A.2.2 = .loc ρ₁ → g (OracleName.g t)
      (qSeal₁ t (wholeDesc C (WholeD.of a W) tF tJ t3 silent run) embP π ρ₁ (rtJ (wholeDesc C
        (WholeD.of a W) tF tJ t3 silent run) (wqWhole C K chal (WholeD.of a W) tF tJ t3 silent run)
        π A)) = bytesToDig seal1 := by
  subst hW
  obtain ⟨r₁, -, H⟩ := readL_of_read C K chal a tF tJ t3 silent run _ rfl T hS₁ hR hs hok f blocks
    embP xin cms x π g sb cfg pF pJ p3 salt path hπ Gr
  exact sealAt_of_readL C K chal _ tF tJ t3 silent run embP xin cms x π g Fmt.oracle [] S₁ S₂ S₃ r
    _ _ oracle_32 hkit₁ hkit₂ hkit₃ H A B E h₁ h₂ h₃ seal1 T.first_seal

end

end OnBytes.Maker.Page
