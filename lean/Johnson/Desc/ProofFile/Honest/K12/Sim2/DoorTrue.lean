-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the state on entry, from what a view holds.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/DoorTrue.lean: the simulators' state on entry of a proximity
test on the first chain, with its true targets, as a function of the public part and of a Before
alone: the description's own fold over the blocks in front, at the columns that the Before lists,
then the way in. And the one equation that ties it to a run: at the front of a called part, cut back
to the rounds in front of the test, the Before lists just the columns of the run's own fold.

What it is for. Three conditions on a simulator that makes
targets: (1) the state is a function of the view and of public data alone: by its type, and by
stateFromView_reads; (2) one function on both sides: the real run's state is that same function at the
real run's Before: stateFromView_at_stand (DoorStand.lean); (3) this is the simulators' letter at every Before: no patch at
a stand stands here.

  columnsOfView      the columns that a Before lists for the reads of rounds in front
  doorFromView, stateFromView   the state, with a refusal; its value or a fall-back
  stateFromView_reads   equal public starts, rounds and columns read give one state
  treeCols_first  what a Before in closed form lists of a tree of the first chain
  reads_of_prefix  reads at a cut of the declared rounds and challenges are reads of the whole
  columnsOfView_at    where the reads are filled at a run, the cut front lists those columns

The equation itself, stateFromView_at_stand, stands in DoorStand.lean.

Limits. The fold and the way in are letters' texts here; that they return is a premise of
stateFromView_at_stand (door_moves_at_L gives it at the first chain's last test). It is a statement on
functions and on a run's closed form: no law, no coin. No property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.FrameAtFirst
import Johnson.Desc.ProofFile.Honest.Law.Rule.Reads
import Johnson.Desc.ProofFile.Honest.K12.Sim.Sims

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block OpenedColumn FileDescription foldBlocks Place)
open VerifiableInference.Desc.K12 (T12)
open ProofFile.Honest ProofFile.Honest.K12

variable {S Cl Pb Xi : Type}

/-- The columns that f lists for the reads that the declared rounds make at the challenges that f
shows. -/
def columnsOfView (decls : List Fmt.DeclaredRound) (f : Before) : Option (List OpenedColumn) :=
  colsOff f (readsOf 0 0 (fun _ _ => none) (fun _ => none) decls (f.seen.map (·.drawn)))

/-- The description's own fold over the blocks in front, at the rounds that f shows and the columns
that it lists, then the way in. -/
def doorFromView (pre : List (Block S Cl)) (start : Pb → S) (enter : S → Except String T12) (pb : Pb)
    (f : Before) : Except String T12 :=
  match columnsOfView (pre.flatMap (·.rounds)) f with
  | some cs => (foldBlocks 0 pre (start pb) f.seen cs).bind fun r => enter r.1
  | none => .error "a column that the rounds in front read is not listed"

/-- **The simulators' state on entry.** Of the public part and of a Before alone. -/
def stateFromView (pre : List (Block S Cl)) (start : Pb → S) (enter : S → Except String T12) (fall : T12)
    (pb : Pb) (f : Before) : T12 :=
  (doorFromView pre start enter pb f).toOption.getD fall

/-- **It reads nothing else**: one start, one list of rounds shown and one list of columns give one
state. -/
theorem stateFromView_reads (pre : List (Block S Cl)) (start : Pb → S) (enter : S → Except String T12)
    (fall : T12) (pb pb' : Pb) (f f' : Before) (hs : start pb = start pb') (hr : f.seen = f'.seen)
    (hc : columnsOfView (pre.flatMap (·.rounds)) f = columnsOfView (pre.flatMap (·.rounds)) f') :
    stateFromView pre start enter fall pb f = stateFromView pre start enter fall pb' f' := by
  unfold stateFromView doorFromView
  rw [hc, hs, hr]

/-- What a Before in closed form lists of a tree of the first chain. -/
theorem treeCols_first (tree : ℕ → List ℕ) (l : List Played)
    (st : List (ℕ × ℕ × List UInt64)) (j : ℕ) :
    (⟨shownBy 0 tree l 0, st⟩ : Before).treeCols 0 j =
      ((allTabs l)[j]?).map fun T => colsOfT T (tree j) := by
  show (((shownBy 0 tree l 0).filter fun r => r.1 == 0).flatMap fun r => r.2.1.cols)[j]? = _
  rw [filter_same]
  have h := cols_at 0 tree l 0 j
  rw [Nat.zero_add] at h
  exact h

/-- Reads at a cut of the declared rounds and challenges are reads of the whole. -/
theorem reads_of_prefix (ch ft : ℕ) (stored : ℕ → ℕ → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) :
    ∀ (n : ℕ) (ds : List Fmt.DeclaredRound) (Rs : List Fmt.Drawn) (q : Read),
      q ∈ readsOf ch ft stored tree (ds.take n) (Rs.take n) → q ∈ readsOf ch ft stored tree ds Rs
  | 0, ds, Rs, q, h => by simp [readsOf] at h
  | n + 1, [], Rs, q, h => by simp [readsOf] at h
  | n + 1, _ :: _, [], q, h => by simp [readsOf] at h
  | n + 1, d :: ds, R :: Rs, q, h => by
    simp only [List.take_succ_cons, readsOf, List.mem_append] at h ⊢
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (reads_of_prefix ch ft stored tree n ds Rs q h)

/-- **Where the reads of the rounds in front are filled at a run, a front in closed form lists just
these columns.** l: the rounds played in front. N: how many. hdecl, hdraw: they are the first N of
the first chain's. hq: the reads, made at l's tables, have words; at a stored table these are those
that st lists. -/
theorem columnsOfView_at {F : FileDescription Xi} {ρ : Draws} {stored : ℕ → ℕ → Option (List UInt64)}
    (l : List Played) (N : ℕ) (decls : List Fmt.DeclaredRound) (hdecl : decls = F.roundsDeclaredByBlocks.1.take N)
    (drawn : List Fmt.Drawn) (hdraw : drawn = ρ.first.take N) (cs : List OpenedColumn)
    (hfill : fillCols (readsOf 0 0 stored (treeOwn l) decls drawn) [] = .ok cs)
    (f : Before) (hf : f = ⟨shownBy 0 (treeAsks F ρ 0) l 0,
      storedShown stored (storedAsks F ρ)⟩) (hseen : f.seen.map (·.drawn) = drawn) :
    columnsOfView decls f = some cs := by
  have hb := colsOff_fill f _ cs hfill fun q hq w hw => ?_
  · unfold columnsOfView
    rw [hseen, ← readsOf_bare 0 0 stored (treeOwn l)]
    exact hb
  have hall : q.bare ∈ allBare F ρ := by
    have h1 : q ∈ readsOf 0 0 stored (treeOwn l) F.roundsDeclaredByBlocks.1 ρ.first := by
      rw [hdecl, hdraw] at hq
      exact reads_of_prefix 0 0 stored (treeOwn l) N _ _ q hq
    have h2 : q.bare ∈ readsOf 0 0 (fun _ _ => none) (fun _ => none) F.roundsDeclaredByBlocks.1 ρ.first := by
      rw [← readsOf_bare 0 0 stored (treeOwn l)]
      exact List.mem_map.2 ⟨q, h1, rfl⟩
    unfold allBare bareReads
    exact List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl h2)))
  rcases readsOf_form 0 0 stored (treeOwn l) decls drawn q hq with ⟨i, h1, -, h3⟩ | ⟨o, h1, h2, h3⟩
  · have hi : q.bare.item = some i := h1
    unfold Before.wordsAt
    rw [hi, hf]
    show (((storedShown stored (storedAsks F ρ)).find? fun c =>
      c.1 == i && c.2.1 == q.pos).map (·.2.2)) = some w
    exact find_stored stored i q.pos w (h3.symm.trans hw) _ (mem_storedAsks F ρ q.bare hall i hi)
  · have hi : q.bare.item = none := h1
    rw [hw] at h3
    cases o with
    | taken a b => simp [treeOwn] at h3
    | own n =>
      have hs : q.bare.src = some (0, n) := h2
      cases hto : treeOwn l (.own n) with
      | none =>
        rw [hto] at h3
        cases h3
      | some pT =>
        rw [hto] at h3
        have hwT : w = pT.2.col q.pos := Option.some.inj h3
        have htab : ((allTabs l)[n]?).join = some pT.2 := by
          have e := tables_tabs l n
          have e2 : (((tablesOf l)[n]?).bind id) = some pT := hto
          rw [e2] at e
          exact e.symm
        have hget : (allTabs l)[n]? = some (some pT.2) := by
          cases hg : (allTabs l)[n]? with
          | none =>
            rw [hg] at htab
            cases htab
          | some t =>
            rw [hg] at htab
            exact congrArg some htab
        have hcols := treeCols_first (treeAsks F ρ 0) l (storedShown stored (storedAsks F ρ)) n
        rw [hget] at hcols
        unfold Before.wordsAt
        rw [hi, hs, hf]
        show ((((⟨shownBy 0 (treeAsks F ρ 0) l 0, storedShown stored (storedAsks F ρ)⟩ :
          Before)).treeCols 0 n).bind fun cols => (cols.find? fun c => c.1 == q.pos).map (·.2)) =
          some w
        rw [hcols, hwT]
        exact find_col pT.2 q.pos _ (mem_treeAsks F ρ q.bare hall _ _ hs)

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.columnsOfView
#print axioms ProofFile.Honest.K12.Sim2.doorFromView
#print axioms ProofFile.Honest.K12.Sim2.stateFromView
#print axioms ProofFile.Honest.K12.Sim2.stateFromView_reads
#print axioms ProofFile.Honest.K12.Sim2.treeCols_first
#print axioms ProofFile.Honest.K12.Sim2.reads_of_prefix
#print axioms ProofFile.Honest.K12.Sim2.columnsOfView_at
