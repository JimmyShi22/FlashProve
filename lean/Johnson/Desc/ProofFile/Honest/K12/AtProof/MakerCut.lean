-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/AtProof/MakerCut.lean

What it proves. A law on the text of the maker of the book of random values (Honest/BookOf.lean, its
first section): the cut that the maker lays at a sub-protocol of the kind K12 whose declared rounds
are those that a place's numbers give is the pair's own: [firstLen, restLen]: the first part's and
the second part's numbers of rounds. General in the numbers (two stages or more), in the chain and
in the sub-protocol's state: so at every plan and at all places of the kind. It reads no label and
no list of sendings.

Names.
  laterNames          the names of a test's rounds behind "BAT".
  later_names, rounds_names   the declared rounds bear these names.
  laterNames_length, rounds_count   how many they are.
  headRun_rep, unitLen_test   the first unit of a test: "BAT" with the first fold.
  cut_names, cut_k12, cut_at_k12   the cut: at the names; at a sub-protocol; at the kind's own
  block.

By what. The texts of unitLen, unitsOf, cutOfNames, partsCut (Honest/BookOf.lean),
Fmt.M1.laterRounds (Fmt/M1Plan.lean), H2U.roundsOfNums (Johnson/Desc/K12/TestEntries.lean),
firstLen, roundOf (Parts.lean in the folder above), restLen (HalfSteps.lean); the library's
k12_rounds (Johnson/Desc/K12/FrameLaws.lean), laterRounds_length and roundsOfNums_length
(Johnson/Desc/K12/CountLaws.lean), lay_names (Johnson/Desc/K12/Law/SitsBats.lean: laying the lists
of trees keeps the rounds' names); of the writers of the hash build's side: unitsOf_fits (the
maker's units add up to the list, at any names) and foldl_add_shift (Honest/BookCutsLaw.lean).

Limits.
- The cut alone: nothing on a part's counts, on what it spends or carries, on owners or starts.
- That a book which the maker returns has this cut at the place is another law (on bookWhole's field
  cuts): not here.
- A test of one stage is left out: a place's numbers give no rounds there.
- The maker cuts by the rounds' names: a round under another name is cut otherwise; here the names
  are those of the library's own text.
- It moves no count. Nothing on completeness, soundness or hiding.

Terms: RunBySpec.lean in the folder above.
-/
import Johnson.Desc.ProofFile.Honest.BookCutsLaw
import Johnson.Desc.ProofFile.Honest.K12.HalfSteps
import Johnson.Desc.K12.FrameLaws
import Johnson.Desc.K12.CountLaws
import Johnson.Desc.K12.Law.SitsBats

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K12 (P12 proximityTestKind k12_rounds)

/-- The names of a proximity test's rounds behind "BAT", from a stage on: for each stage but the
last its fold ("FOLD epsilon", k times "FOLD round") and its switch ("SEND seed", "CS"); then the
base case. -/
def laterNames : Fmt.M1.Stage → List Fmt.M1.Stage → List String
  | _, [] => ["BASE lambda", "BASE"]
  | old, new :: rest =>
    "FOLD epsilon" ::
      (List.replicate old.k "FOLD round" ++ "SEND seed" :: "CS" :: laterNames new rest)

/-- The format's model rounds bear these names. -/
theorem later_names (work : ℕ) : ∀ (rest : List Fmt.M1.Stage) (tree W : ℕ) (old : Fmt.M1.Stage),
    (Fmt.M1.laterRounds work tree W old rest).map (·.entry.name) = laterNames old rest
  | [], _, _, _ => rfl
  | new :: rest, tree, W, old => by
    show ([Fmt.M1.rEps "FOLD epsilon"] ++ List.replicate old.k (Fmt.M1.rTwo "FOLD round") ++
      [Fmt.M1.rSeed new, Fmt.M1.rCs work old tree W] ++
      Fmt.M1.laterRounds work (tree + 1) (Fmt.M1.wMid new) new rest).map (·.entry.name) = _
    rw [List.map_append, List.map_append, List.map_append, List.map_replicate,
      later_names work rest (tree + 1) (Fmt.M1.wMid new) new, List.append_assoc, List.append_assoc]
    rfl

/-- **The names of a proximity test's declared rounds, from the numbers of its place.** -/
theorem rounds_names (N : H2U.TestNums) (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : N.stages = s :: next :: rest) (ds : List Fmt.DeclaredRound)
    (h : H2U.roundsOfNums N = some ds) :
    ds.map (·.entry.name) = "BAT" :: laterNames s (next :: rest) := by
  unfold H2U.roundsOfNums at h
  rw [hst] at h
  have e := H2K.JointK.lay_names _ _ _ _ ds h
  rw [e, List.map_cons, later_names]
  rfl

/-- How many they are. -/
theorem laterNames_length : ∀ (rest : List Fmt.M1.Stage) (old : Fmt.M1.Stage),
    (laterNames old rest).length = ((old :: rest).dropLast.map (·.k + 3)).sum + 2
  | rest, old => by
    rw [← later_names 0 rest 0 0 old, List.length_map]
    exact VerifiableInference.Desc.K12.laterRounds_length 0 rest 0 0 old

/-- The run of a name at the head of so many copies of it, behind which another name stands. -/
theorem headRun_rep (s t : String) (hts : (t == s) = false) (tl : List String) :
    ∀ k : ℕ, headRun s (List.replicate k s ++ t :: tl) = k
  | 0 => by
    show ((t :: tl).takeWhile (· == s)).length = 0
    rw [List.takeWhile_cons, hts]
    rfl
  | k + 1 => by
    have ih := headRun_rep s t hts tl k
    unfold headRun at ih ⊢
    rw [List.replicate_succ, List.cons_append, List.takeWhile_cons, beq_self_eq_true]
    show (List.takeWhile (· == s) (List.replicate k s ++ t :: tl)).length + 1 = k + 1
    rw [ih]

/-- The first unit of a test of two stages or more: "BAT" with the first fold. -/
theorem unitLen_test (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) :
    unitLen ("BAT" :: laterNames s (next :: rest)) = 2 + s.k := by
  show unitLen ("BAT" :: "FOLD epsilon" :: (List.replicate s.k "FOLD round" ++
    "SEND seed" :: "CS" :: laterNames next rest)) = _
  simp only [unitLen, List.head?_cons, List.tail_cons]
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos (by decide),
    headRun_rep "FOLD round" "SEND seed" (by decide)]

/-- **The maker's cut at the names of a proximity test of two stages or more is the pair's own**:
the first part's and the second part's numbers of rounds (firstLen, Parts.lean; restLen,
HalfSteps.lean). -/
theorem cut_names (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) :
    cutOfNames .K12 ("BAT" :: laterNames s (next :: rest)) =
      [firstLen (s :: next :: rest), restLen (s :: next :: rest)] := by
  have hu := unitLen_test s next rest
  have hlen := laterNames_length (next :: rest) s
  have hsum := (unitsOf_fits (laterNames s (next :: rest)).length.succ
    ("BAT" :: laterNames s (next :: rest)) (Nat.le_refl _)).1
  have hdrop : ("BAT" :: laterNames s (next :: rest)).drop (2 + s.k) =
      "SEND seed" :: "CS" :: laterNames next rest := by
    show ("BAT" :: "FOLD epsilon" :: (List.replicate s.k "FOLD round" ++
      "SEND seed" :: "CS" :: laterNames next rest)).drop (2 + s.k) = _
    rw [Nat.add_comm, List.drop_succ_cons, List.drop_succ_cons, List.drop_left']
    exact List.length_replicate
  have hcons : unitsOf (laterNames s (next :: rest)).length.succ
      ("BAT" :: laterNames s (next :: rest)) =
      (2 + s.k) :: unitsOf (laterNames s (next :: rest)).length
        ("SEND seed" :: "CS" :: laterNames next rest) := by
    show unitLen ("BAT" :: laterNames s (next :: rest)) :: unitsOf _
      (("BAT" :: laterNames s (next :: rest)).drop
        (unitLen ("BAT" :: laterNames s (next :: rest)))) = _
    rw [hu, hdrop]
  obtain ⟨m, hm⟩ : ∃ m, (laterNames s (next :: rest)).length = m + 1 := ⟨_, hlen.trans rfl⟩
  have hne : (unitsOf (laterNames s (next :: rest)).length
      ("SEND seed" :: "CS" :: laterNames next rest)).isEmpty = false := by
    rw [hm]
    rfl
  rw [hcons, List.foldl_cons, foldl_add_shift] at hsum
  unfold cutOfNames
  rw [show ("BAT" :: laterNames s (next :: rest)).length =
    (laterNames s (next :: rest)).length.succ from rfl, hcons]
  show (if (VerifiableInference.Desc.KindName.K12 == .K12) = true then
    (if (unitsOf (laterNames s (next :: rest)).length
      ("SEND seed" :: "CS" :: laterNames next rest)).isEmpty = true then [2 + s.k]
     else [2 + s.k, (unitsOf (laterNames s (next :: rest)).length
      ("SEND seed" :: "CS" :: laterNames next rest)).foldl (· + ·) 0]) else _) = _
  rw [if_pos (by decide), hne, if_neg (by decide)]
  have hr : restLen (s :: next :: rest) =
      1 + (((s :: next :: rest).take ((s :: next :: rest).length - 1)).map (·.k + 3)).sum + 2 -
        (2 + s.k) := rfl
  rw [hr, ← List.dropLast_eq_take]
  have hl2 : ("BAT" :: laterNames s (next :: rest)).length =
      (laterNames s (next :: rest)).length + 1 := rfl
  rw [hl2] at hsum
  show [2 + s.k, _] = [2 + s.k, _]
  congr 2
  omega

/-- **The maker's cut at a sub-protocol of the kind K12 whose declared rounds are those that a
place's numbers give**: general in the numbers, in the chain and in the sub-protocol's state. -/
theorem cut_k12 {S Cl : Type} (b : Block S Cl) (hk : b.place.kind = .K12) (N : H2U.TestNums)
    (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hst : N.stages = s :: next :: rest)
    (hr : H2U.roundsOfNums N = some b.rounds) :
    partsCut b = [firstLen N.stages, restLen N.stages] := by
  unfold partsCut
  rw [hk, rounds_names N s next rest hst b.rounds hr, hst]
  exact cut_names s next rest

/-- So at the kind's own block, where it passes its test on the plan and stands at a place of the
kind. -/
theorem cut_at_k12 {T Cl : Type} (X : VerifiableInference.Desc.K12.Parts T) (p : P12)
    (hp : (proximityTestKind X p : Block T Cl).planOk = true) (hk : (proximityTestKind X p : Block T Cl).place.kind = .K12)
    (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hst : p.nums.stages = s :: next :: rest) :
    partsCut (proximityTestKind X p : Block T Cl) = [firstLen p.nums.stages, restLen p.nums.stages] :=
  cut_k12 _ hk p.nums s next rest hst (k12_rounds X p hp)

/-- And the test's rounds are as many as the pair's two numbers, at every place of two stages or
more: the library's count (roundsOfNums_length: roundsIn) in the pair's letters. -/
theorem rounds_count (N : H2U.TestNums) (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : N.stages = s :: next :: rest) (ds : List Fmt.DeclaredRound)
    (h : H2U.roundsOfNums N = some ds) : ds.length = firstLen N.stages + restLen N.stages := by
  rw [VerifiableInference.Desc.K12.roundsOfNums_length N ds h, hst]
  have hr : restLen (s :: next :: rest) =
      1 + (((s :: next :: rest).take ((s :: next :: rest).length - 1)).map (·.k + 3)).sum + 2 -
        (2 + s.k) := rfl
  rw [hr, ← List.dropLast_eq_take]
  show 1 + ((s :: next :: rest).dropLast.map (·.k + 3)).sum + 2 = 2 + s.k + _
  have hs : ((s :: next :: rest).dropLast.map (·.k + 3)).sum =
      s.k + 3 + ((next :: rest).dropLast.map (·.k + 3)).sum := by
    show ((s :: (next :: rest).dropLast).map (·.k + 3)).sum = _
    rw [List.map_cons, List.sum_cons]
  omega

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.laterNames
#print axioms ProofFile.Honest.K12.AtProof.later_names
#print axioms ProofFile.Honest.K12.AtProof.rounds_names
#print axioms ProofFile.Honest.K12.AtProof.laterNames_length
#print axioms ProofFile.Honest.K12.AtProof.headRun_rep
#print axioms ProofFile.Honest.K12.AtProof.unitLen_test
#print axioms ProofFile.Honest.K12.AtProof.cut_names
#print axioms ProofFile.Honest.K12.AtProof.cut_k12
#print axioms ProofFile.Honest.K12.AtProof.cut_at_k12
#print axioms ProofFile.Honest.K12.AtProof.rounds_count
