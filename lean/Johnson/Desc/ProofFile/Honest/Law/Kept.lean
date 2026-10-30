-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Kept.lean: the part of a description's acceptance that no
sub-protocol decides. Theorems on the general functions of Johnson/Desc/Block.lean. They hold of
every description and of all views: no particular prover, kind, file or plan is named. The two main
lemmas are `foldBlocks_ok_iff` and `run_iff_fits`.

Why. Johnson/Desc/RunLaws.lean says what a description's acceptance consists of. For each
sub-protocol, `foldBlocks` tests three things besides the sub-protocol's own decision: that the
rounds fit, that the next columns are those that are read, and, at the end, that nothing is left
over. Whoever wants to prove that some views are accepted would have to prove these three at every
sub-protocol. Here they are gathered into one executable test on a whole chain, so that they can be
proved once.

  1  `decides`   the sub-protocols' decisions alone, along the division that `foldBlocks` makes;
     `kept`: a whole chain's book-keeping as one executable test; `fitsAll`: the six tests of a
     file's acceptance that read neither the instance nor a verifier's state; `Decided`: what is
     left: the sub-protocols' decisions, the second chain's start, the last test
  2  `kept_iff`, `cols_split`, `decides_cons`, `flat_isEmpty`   these definitions unfolded
  3  `foldBlocks_ok_iff`   `foldBlocks` over a chain ends with nothing left over if and only if
     `kept` passes at the chain's declared rounds, concatenated, and `decides` returns;
     `run_iff_fits`: a description accepts if and only if the tests on the plan, the test on
     the instance and `fitsAll` pass, and `Decided` holds

Limits.
  * Both lemmas are equivalences: they say what an acceptance consists of, not that any views are
    accepted.
  * `Decided` is a name for one part of the right-hand side of `run_iff_fits`; nothing is proved
    about it.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.RunLaws
import Johnson.Top.H0.StepLaws.StepLaws
import Johnson.Desc.ProofFile.Views

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Cl Xi : Type}

/-! ## 1 The definitions -/

/-- The sub-protocols' decisions alone, along the division that `foldBlocks` makes: each
sub-protocol gets its own number of rounds, and as many columns as its rounds read at their
challenges. -/
def decides (ft : Nat) : List (Block S Cl) → S → List Fmt.RoundView → List OpenedColumn → Except String S
  | [], s, _, _ => .ok s
  | b :: l, s, rs, cols =>
    let mine := rs.take b.rounds.length
    let groups := groupsOf ft b.rounds (mine.map (·.drawn))
    let k := (groups.flatMap id).length
    (b.decide s (mine.map noDigest) (regroup (groups.map (·.length)) (cols.take k))).bind fun s' =>
      decides ft l s' (rs.drop b.rounds.length) (cols.drop k)

/-- A whole chain's book-keeping as one executable test: `roundsFit` at the chain's declared rounds,
concatenated; and the view's columns are, in key, position and width, exactly those that these
rounds read, and no more. -/
def kept (ft : Nat) (ds : List Fmt.DeclaredRound) (v : Fmt.View) : Bool :=
  roundsFit ds v.rounds &&
    (v.opened.map fun c => (c.1, c.2.1, c.2.2.length)) ==
      (groupsOf ft ds (v.rounds.map (·.drawn))).flatMap id

/-- The six tests of a file's acceptance that read neither the instance nor a verifier's state. -/
def fitsAll (F : FileDescription Xi) (U : Views) : Bool :=
  viewWordsBelowPrime U.1 && viewWordsBelowPrime U.2.1 && viewWordsBelowPrime U.2.2 && kept 0 F.roundsDeclaredByBlocks.1 (withEmptySealRound U.1) &&
    kept 0 F.roundsDeclaredByBlocks.2.1 U.2.1 && kept F.lastChainFirstTreeNumber F.roundsDeclaredByBlocks.2.2 U.2.2

/-- What is left of a file's acceptance: the sub-protocols' decisions, the second chain's start, the
last test. It is a definition: a name for one part of the right-hand side of `run_iff_fits`. Nothing
is claimed of it, and it is none of the library's goals. -/
def Decided (F : FileDescription Xi) (x : Xi) (U : Views) : Prop :=
  ∃ (e₁ : F.S₁) (e₂ : F.S₂) (s₃ e₃ : F.S₃),
    decides 0 F.first.blocksInOrder (F.start₁ (F.pub x)) (withEmptySealRound U.1).rounds U.1.opened = .ok e₁ ∧
    decides 0 F.shared.blocksInOrder (F.start₂ (F.pub x)) U.2.1.rounds U.2.1.opened = .ok e₂ ∧
    F.start₃ (F.pub x) e₁ e₂ = .ok s₃ ∧
    decides F.lastChainFirstTreeNumber F.second.blocksInOrder s₃ U.2.2.rounds U.2.2.opened = .ok e₃ ∧
    F.fin x e₁ e₂ e₃ = true

/-! ## 2 The definitions unfolded -/

/-- The test `kept`, as two propositions. -/
theorem kept_iff (ft : Nat) (ds : List Fmt.DeclaredRound) (rs : List Fmt.RoundView) (cols : List OpenedColumn) :
    kept ft ds ⟨rs, cols⟩ = true ↔
      roundsFit ds rs = true ∧
        (cols.map fun c => (c.1, c.2.1, c.2.2.length)) =
          (groupsOf ft ds (rs.map (·.drawn))).flatMap id := by
  simp only [kept, Bool.and_eq_true, beq_iff_eq]

/-- Columns show two lists, one after the other, if and only if the first so many show the first
list and the others the second. -/
theorem cols_split (W1 W2 : List (Nat × Nat × Nat)) (cols : List OpenedColumn) :
    (cols.map fun c => (c.1, c.2.1, c.2.2.length)) = W1 ++ W2 ↔
      ((cols.take W1.length).map fun c => (c.1, c.2.1, c.2.2.length)) = W1 ∧
        ((cols.drop W1.length).map fun c => (c.1, c.2.1, c.2.2.length)) = W2 := by
  constructor
  · intro h
    constructor
    · rw [List.map_take, h]
      exact List.take_left' rfl
    · rw [List.map_drop, h]
      exact List.drop_left' rfl
  · rintro ⟨h1, h2⟩
    have h := congrArg (List.map fun c : OpenedColumn => (c.1, c.2.1, c.2.2.length))
      (List.take_append_drop W1.length cols)
    rw [List.map_append, h1, h2] at h
    exact h.symm

/-- `decides` at a first sub-protocol, in the terms of Johnson/Top/H0/StepLaws/StepLaws.lean. -/
theorem decides_cons (ft : Nat) (b : Block S Cl) (l : List (Block S Cl)) (s : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) :
    decides ft (b :: l) s rs cols =
      (b.decide s ((rs.take b.rounds.length).map noDigest)
        (b.shown ft (rs.take b.rounds.length) cols)).bind fun s' =>
          decides ft l s' (rs.drop b.rounds.length)
            (cols.drop (b.want ft (rs.take b.rounds.length)).length) := rfl

/-- A chain's flat list has a sub-protocol. -/
theorem flat_isEmpty (c : Chain S Cl) : c.blocksInOrder.isEmpty = false := by
  simp [Chain.blocksInOrder]

/-! ## 3 The two lemmas -/

/- The statement of `foldBlocks_ok_iff`, with its binders under a universal quantifier. -/
theorem foldBlocks_ok_iff_aux (ft : Nat) : ∀ (bs : List (Block S Cl)) (s e : S)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn),
    foldBlocks ft bs s rs cols = .ok (e, [], []) ↔
      kept ft (bs.flatMap (·.rounds)) ⟨rs, cols⟩ = true ∧ decides ft bs s rs cols = .ok e
  | [], s, e, rs, cols => by
    rw [kept_iff]
    cases rs with
    | nil =>
      cases cols with
      | nil => simp [foldBlocks, decides, roundsFit, groupsOf]
      | cons c cs => simp [foldBlocks, decides, roundsFit, groupsOf]
    | cons r rs => simp [foldBlocks, decides, roundsFit]
  | b :: l, s, e, rs, cols => by
    have cut : (groupsOf ft ((b :: l).flatMap (·.rounds)) (rs.map (·.drawn))).flatMap id =
        b.want ft (rs.take b.rounds.length) ++
          (groupsOf ft (l.flatMap (·.rounds)) ((rs.drop b.rounds.length).map (·.drawn))).flatMap
            id := by
      rw [List.flatMap_cons, groupsOf_app, List.flatMap_append, ← List.map_take, ← List.map_drop]
      rfl
    rw [foldBlocks_cons_ok, kept_iff, cut, cols_split, List.flatMap_cons, roundsFit_append,
      decides_cons]
    constructor
    · rintro ⟨_, s', k, hs, hf⟩
      obtain ⟨⟨h1, h2⟩, h3, hk⟩ := (step_iff ft b s s' (rs.take b.rounds.length) cols k).1 hs
      subst hk
      obtain ⟨k2, d2⟩ := (foldBlocks_ok_iff_aux ft l s' e _ _).1 hf
      obtain ⟨r2, c2⟩ := (kept_iff ft _ _ _).1 k2
      refine ⟨⟨⟨h1, r2⟩, beq_iff_eq.1 h2, c2⟩, ?_⟩
      rw [h3]
      exact d2
    · rintro ⟨⟨⟨h1, r2⟩, c1, c2⟩, hd⟩
      cases h3 : b.decide s ((rs.take b.rounds.length).map noDigest)
          (b.shown ft (rs.take b.rounds.length) cols) with
      | error w =>
        rw [h3] at hd
        exact (error_ne_ok hd).elim
      | ok s' =>
        rw [h3] at hd
        exact ⟨roundsFit_length _ _ h1, s', _,
          (step_iff ft b s s' (rs.take b.rounds.length) cols _).2
            ⟨⟨h1, beq_iff_eq.2 c1⟩, h3, rfl⟩,
          (foldBlocks_ok_iff_aux ft l s' e _ _).2 ⟨(kept_iff ft _ _ _).2 ⟨r2, c2⟩, hd⟩⟩

/-- **`foldBlocks` over a chain ends with nothing left over** if and only if the whole chain's
book-keeping holds and the sub-protocols' decisions return along the division. -/
theorem foldBlocks_ok_iff (ft : Nat) (bs : List (Block S Cl)) (s e : S) (rs : List Fmt.RoundView)
    (cols : List OpenedColumn) :
    foldBlocks ft bs s rs cols = .ok (e, [], []) ↔
      kept ft (bs.flatMap (·.rounds)) ⟨rs, cols⟩ = true ∧ decides ft bs s rs cols = .ok e :=
  foldBlocks_ok_iff_aux ft bs s e rs cols

/-- **What a description's acceptance consists of, by who can prove it**: the tests on the plan; the
test on the instance; the six tests that read neither the instance nor a verifier's state; and what
the sub-protocols, the second chain's start and the last test decide. -/
theorem run_iff_fits (F : FileDescription Xi) (x : Xi) (U : Views) :
    F.run x U.1 U.2.1 U.2.2 = true ↔
      F.planOk = true ∧ F.okStart x = true ∧ fitsAll F U = true ∧ Decided F x U := by
  rw [FileDescription.run_ok]
  unfold Decided fitsAll
  simp only [Bool.and_eq_true]
  constructor
  · rintro ⟨e₁, e₂, e₃, hp, ho, w1, w2, w3, c1, c2, ⟨s₃, hs, c3⟩, hf⟩
    obtain ⟨k1, d1⟩ := (foldBlocks_ok_iff 0 _ _ _ _ _).1 (chainAt_ok.1 c1).2
    obtain ⟨k2, d2⟩ := (foldBlocks_ok_iff 0 _ _ _ _ _).1 (chainAt_ok.1 c2).2
    obtain ⟨k3, d3⟩ := (foldBlocks_ok_iff _ _ _ _ _ _).1 (chainAt_ok.1 c3).2
    exact ⟨hp, ho, ⟨⟨⟨⟨⟨w1, w2⟩, w3⟩, k1⟩, k2⟩, k3⟩, e₁, e₂, s₃, e₃, d1, d2, hs, d3, hf⟩
  · rintro ⟨hp, ho, ⟨⟨⟨⟨⟨w1, w2⟩, w3⟩, k1⟩, k2⟩, k3⟩, e₁, e₂, s₃, e₃, d1, d2, hs, d3, hf⟩
    exact ⟨e₁, e₂, e₃, hp, ho, w1, w2, w3,
      chainAt_ok.2 ⟨flat_isEmpty _, (foldBlocks_ok_iff 0 _ _ _ _ _).2 ⟨k1, d1⟩⟩,
      chainAt_ok.2 ⟨flat_isEmpty _, (foldBlocks_ok_iff 0 _ _ _ _ _).2 ⟨k2, d2⟩⟩,
      ⟨s₃, hs, chainAt_ok.2 ⟨flat_isEmpty _, (foldBlocks_ok_iff _ _ _ _ _ _).2 ⟨k3, d3⟩⟩⟩, hf⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.kept_iff
#print axioms ProofFile.Honest.cols_split
#print axioms ProofFile.Honest.decides_cons
#print axioms ProofFile.Honest.flat_isEmpty
#print axioms ProofFile.Honest.foldBlocks_ok_iff_aux
#print axioms ProofFile.Honest.foldBlocks_ok_iff
#print axioms ProofFile.Honest.run_iff_fits
