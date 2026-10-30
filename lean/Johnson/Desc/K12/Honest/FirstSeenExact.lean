-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/FirstSeenExact.lean: what an acceptance of a proximity test's fold returns
and leaves, as a term of the rounds. The library has a theorem of this kind at rounds that are made
from a protocol's transcript (`foldD_sem`, Johnson/Desc/K12/Law/FoldLaw.lean). A prover's side has
rounds as a view shows them: a plain list. Here, at every list of rounds (`List Fmt.RoundView`,
Fmt/View.lean), the single rows that the fold returns (`SingleRows`, OnBytes/Iop/Fold.lean) are
`foldOutAt` of these rounds (Johnson/Prover/Link/FormFold.lean), the output of which `fold_holds`
(Johnson/Prover/Link/FoldHolds.lean) speaks; and three fields of the state that the fold's decision
returns are written out. Both arms of the first fold (the fresh table came earlier; the fold's own
first message brings it). `fold_exact` is general in the stage's number j; FirstReads.lean,
FirstValues.lean and Shape/ReadFirst.lean of this folder call it at j = 0. Theorems only. It depends
on no file of the frame for an honest side (Johnson/Desc/ProofFile/Honest/Frame.lean and the files
next to it).

In this file's name and in `rounds_exact`, `foldD_exact` and `fold_exact`, "exact" means "as a term
of the rounds": equations of values, no statement on distributions, and not the field `exact` of
`Good` (Johnson/Desc/ProofFile/Honest/Side.lean).

In the list: a round r has the items `r.vals` and the drawn values `r.drawn`. `sentOf r` is the list
of the items of the sort `.e` in `r.vals`, in order, as elements of `E`; `drawnOf r` is the first of
`r.drawn.elems`, as an element of `E`; `claimOf rs claim` is the running claim after the rounds rs,
begun at claim; `spent S id` is the statement S with the oracle message number id marked
`spentAsMask` (all four: FormFold.lean, whose docstrings say what each is where an item or a message
is missing). d, d' and d1 are carried states (`Desc.Plain.DState`,
Johnson/Desc/First/Base/DescState.lean); t and t₁ are states inside a proximity test (`T12`,
Johnson/Desc/K12/Join.lean). Both kinds have a statement `st` (`Statement`, OnBytes/Iop/Ground.lean:
codes, oracle messages, groups), a book `book` (`TreeBook`, same file: the trees sent so far and
each oracle message's place in them; it is not the `ProverCoinCounts` of the frame for an honest side) and the
number `roots` of roots received. `T12` also has `g`, the number of the group under test, `pass`,
what passes from a part to the next, and `mask`, the fresh table's number if it has come. The fresh
table is the oracle message that the fold marks as spent as a mask; id is its number. A part
(`Part`, Johnson/Desc/K12/Frame.lean) is a test on the plan and a decision `decide`, which takes a
state, the part's rounds and its groups of columns and returns the next state or a refusal; an
acceptance is a return of `.ok`. p (`P12`, same file) has the numbers of the place of a proximity
test; `p.idx` lists for each stage the numbers of its two codes. F is the fold's shape
(`FoldShape`), row the row to fold (`GroupRow`).

  `foldD_exact`: an acceptance of the plain fold returns `foldOutAt` at the state behind the fresh
    table's entering. In full: if `foldD firstTree d F row mask es rs`
    (Johnson/Desc/First/Close/Closing.lean) returns `(out, d')`, there are id and d1 with: mask is
    `some id` and d1 = d, or mask is `none` and `Ground.recvP firstTree d #[foldMaskNotice F]`
    returns d1 with an array of numbers whose first is id; `Ground.spendAsMaskP d1 id = some d'`;
    `out = foldOutAt d1.st F row id rs`; and `Own.foldRowFits d'.st F row` passes
  `fold_exact`: the same at the test's own part: the library's `MaskCase` · the state behind: its
    statement (the table spent, the next stage's group pushed), its book, what it passes, the new
    group's number and two codes. In full: under the hypotheses below, with F :=
    `ioppFoldShape cu L`, there are id, st, book and a pair n with: `MaskCase p t F id st book`;
    `p.idx[j + 1]? = some n`; `t₁.st = Ground.withGroup (spent st id) n.1 n.2`; `t₁.book = book`;
    `t₁.pass` is `.single` of `foldOutAt st F row id rs` and `st.groups.size`; and
    `Own.foldRowFits (spent st id) F row` passes. `MaskCase` (Johnson/Desc/K12/Law/JointK.lean)
    says: `t.mask` is `some id`, and st and book are those of t; or `t.mask` is `none`, and st and
    book are those of the state that `Ground.recvP` returns at the `st`, `book` and `roots` of t,
    some list of opened columns and `#[foldMaskNotice F]`, with id the first number returned
  `rounds_exact`: if `rounds es rs claim` (Closing.lean) returns `(gs, cl)`, then gs is
    `rs.map drawnOf` and cl is `claimOf rs claim`
  `heard_out`: if `heard name items e r roots` (Closing.lean) returns `(xs, x)`, then xs is
    `sentOf r` and x is `drawnOf r`
  `spent_of`, `shapes_spent`: the state behind the spending of a fresh table is `spent`; it keeps
    the oracle messages' shapes, and so does the pushing of a group. In full: `spent_of`: if
    `Ground.spendAsMaskP d o = some d'`, then `d'.st = spent d.st o`, and d' has the book and the
    roots of d. `shapes_spent`: `ShapesKeep S (Ground.withGroup (spent S id) x y)`
    (OnBytes/Slice/BlkSeat.lean) at every S, id, x and y: each oracle message of S is there under
    its number, with its shape
  `mapM_filterMap`: for a function f into `Option`: if `l.mapM f = some xs`, then
    `l.filterMap f = xs`

By what. `fold_exact` takes off the guard on drawn positions by `ranged_ok`
(Johnson/Desc/K12/Law/BaseGives.lean), comes to `foldD` by `foldJ_ok`
(Johnson/Desc/K12/Law/FoldKeeps.lean), and calls `foldD_exact` and `spent_of`. `foldD_exact` unfolds
`foldD` test by test with `bind_ok`, `need_ok` and `got_ok` (FoldLaw.lean) and calls `heard_out`,
`rounds_exact` and `spent_of`. `rounds_exact` goes by recursion on the rounds and calls `heard_out`,
which calls `heard_ok` (FoldLaw.lean) and `mapM_filterMap`. `spent_of` unfolds
`Ground.spendAsMaskP`; `shapes_spent` unfolds `Ground.withGroup` (both:
Johnson/Desc/First/Base/Ground.lean), `spent` and `ShapesKeep`.

Hypotheses of `fold_exact`. hp: what t passes is one claim with its layout: `t.pass = .claim row L`.
hc: `stageAt p j cur = some cu`: `p.idx` has an element number j; cu has its two numbers as `code`
and `maskCode`, and the `k` and `h` of cur. hn: rs has 1 + `cu.k` rounds. h: the decision of
`guardedProximityTestParts.fold p j cur cut` (Johnson/Desc/K12/JoinGuarded.lean) at t, the rounds rs and no group of
columns (`[]`) returns t₁.

Limits. Nothing says that a fold accepts. The states d and t, the rounds and the plan's numbers are
free parameters: nothing says that a run of a verifier or of a prover reaches them. `fold_exact` is
stated at the empty list of groups of columns only. Of t₁ it states `st`, `book` and `pass`: nothing
on `roots`, `g` and `mask`. Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Law.BaseGives
import Johnson.Desc.K12.Law.JointK
import Johnson.Desc.K12.JoinGuarded
import Johnson.Prover.Link.FormFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.First.Close
open H2K.FoldLaw (bind_ok need_ok got_ok heard_ok)
open H2K.JointK (MaskCase)
open Johnson.Prover.Link (sentOf drawnOf claimOf claimStep foldOutAt spent)

theorem mapM_filterMap {α β : Type} (f : α → Option β) : ∀ (l : List α) (xs : List β),
    l.mapM f = some xs → l.filterMap f = xs
  | [], xs, h => by
    simp only [List.mapM_nil] at h
    cases h
    rfl
  | v :: vs, xs, h => by
    rw [List.mapM_cons] at h
    cases hv : f v with
    | none => simp [hv] at h
    | some y =>
      cases hm : vs.mapM f with
      | none => simp [hv, hm] at h
      | some ys =>
        simp [hv, hm] at h
        subst h
        rw [List.filterMap_cons, hv, mapM_filterMap f vs ys hm]

/-- What was heard is what the round shows. What `heard` returns is `sentOf r` and `drawnOf r`. -/
theorem heard_out (name : String) (items : ℕ) (e : Fmt.Entry) (r : Fmt.RoundView) (roots : ℕ)
    (xs : List E) (x : E) (h : heard name items e r roots = .ok (xs, x)) :
    xs = sentOf r ∧ x = drawnOf r := by
  obtain ⟨h1, t, h2, rfl⟩ := heard_ok _ _ _ _ _ _ _ h
  refine ⟨(mapM_filterMap _ _ _ h1).symm, ?_⟩
  unfold drawnOf
  rw [h2]
  rfl

/-- The fold's rounds return the sampled elements and the running claim. -/
theorem rounds_exact : ∀ (es : List Fmt.Entry) (rs : List Fmt.RoundView) (claim : E) (gs : List E)
    (cl : E), rounds es rs claim = .ok (gs, cl) → gs = rs.map drawnOf ∧ cl = claimOf rs claim
  | [], [], _, gs, cl, h => by
    have h' : (Except.ok ([], _) : Except String (List E × E)) = .ok (gs, cl) := h
    cases h'
    exact ⟨rfl, rfl⟩
  | [], _ :: _, _, _, _, h => by cases h
  | _ :: _, [], _, _, _, h => by cases h
  | e :: es, r :: rs, claim, gs, cl, h => by
    rw [rounds] at h
    obtain ⟨⟨xs, g⟩, h1, h⟩ := bind_ok h
    obtain ⟨hx, rfl⟩ := heard_out _ _ _ _ _ _ _ h1
    split at h
    · rename_i c0 c2 g' heq
      cases heq
      obtain ⟨⟨gs', cl'⟩, h2, h⟩ := bind_ok h
      cases h
      obtain ⟨rfl, rfl⟩ := rounds_exact es rs _ gs' cl' h2
      refine ⟨rfl, ?_⟩
      have e : claimOf (r :: rs) claim = claimOf rs (claimStep claim r) := List.foldl_cons ..
      rw [e]
      unfold claimStep
      rw [← hx]
      simp only [List.getD_cons_zero, List.getD_cons_succ]
    · cases h

theorem spent_of {L : Type} (d d' : _root_.Desc.Plain.DState L) (o : ℕ)
    (h : Ground.spendAsMaskP d o = some d') :
    d'.st = spent d.st o ∧ d'.book = d.book ∧ d'.roots = d.roots := by
  unfold Ground.spendAsMaskP at h
  split at h
  · cases h
    exact ⟨rfl, rfl, rfl⟩
  · cases h

/-- Spending a fresh table and pushing a group keep the oracle messages' shapes. -/
theorem shapes_spent (S : Statement) (id x y : ℕ) :
    ShapesKeep S (Ground.withGroup (spent S id) x y) := by
  intro o z hz
  show ∃ x', (S.oracles.modify id fun x => { x with spentAsMask := true })[o]? = some x' ∧ _
  rw [Array.getElem?_modify, hz]
  by_cases e : id = o
  · exact ⟨{ z with spentAsMask := true }, by simp [e], rfl⟩
  · exact ⟨z, by simp [e], rfl⟩

/-- **What an acceptance of the plain fold returns, as a term of the rounds.** In both arms: `mask`
is `some id`, or it is `none`. -/
theorem foldD_exact {L : Type} (firstTree : ℕ) (d d' : _root_.Desc.Plain.DState L) (F : FoldShape)
    (row : GroupRow) (mask : Option ℕ) (es : List Fmt.Entry) (rs : List Fmt.RoundView) (out : SingleRows)
    (h : foldD firstTree d F row mask es rs = .ok (out, d')) :
    ∃ (id : ℕ) (d1 : _root_.Desc.Plain.DState L),
      ((mask = some id ∧ d1 = d) ∨ (mask = none ∧ ∃ ids,
        Ground.recvP firstTree d #[foldMaskNotice F] = some (ids, d1) ∧ ids[0]? = some id)) ∧
      Ground.spendAsMaskP d1 id = some d' ∧ out = foldOutAt d1.st F row id rs ∧
      Own.foldRowFits d'.st F row = true := by
  cases es with
  | nil => cases h
  | cons eE eR =>
    cases rs with
    | nil => cases h
    | cons rE rR =>
      rw [foldD] at h
      obtain ⟨_, _, h⟩ := bind_ok h
      obtain ⟨_, _, h⟩ := bind_ok h
      obtain ⟨_, _, h⟩ := bind_ok h
      have h1 : ∃ (id : ℕ) (d1 : _root_.Desc.Plain.DState L),
          ((mask = some id ∧ d1 = d) ∨ (mask = none ∧ ∃ ids,
            Ground.recvP firstTree d #[foldMaskNotice F] = some (ids, d1) ∧ ids[0]? = some id)) ∧
          (do
            First.Close.need "K10.maskfits" (Own.foldMaskFits d1.st F id)
            First.Close.named (Ground.spendAsMaskL d1.st id)
            let d2 ← got "K10.maskfits" (Ground.spendAsMaskP d1 id)
            match ← heard "FOLD epsilon" 1 eE rE (d1.roots - d.roots) with
            | ([sum], eps) =>
              First.Close.need "K10.rowfits" (Own.foldRowFits d2.st F row)
              let (gamma, claim) ← rounds eR rR (maddE sum eps row.target)
              pure (foldOutput d2.st F row id eps gamma claim, d2)
            | _ => .error "K10.items") = Except.ok (out, d') := by
        cases mask with
        | some o => exact ⟨o, d, .inl ⟨rfl, rfl⟩, h⟩
        | none =>
          obtain ⟨_, _, h⟩ := bind_ok h
          obtain ⟨⟨ids, dd⟩, hr, h⟩ := bind_ok h
          obtain ⟨i0, hi, h⟩ := bind_ok h
          exact ⟨i0, dd, .inr ⟨rfl, ids, got_ok hr, got_ok hi⟩, h⟩
      obtain ⟨id, d1, hcase, h⟩ := h1
      obtain ⟨_, _, h⟩ := bind_ok h
      obtain ⟨_, _, h⟩ := bind_ok h
      obtain ⟨d2, hsp, h⟩ := bind_ok h
      obtain ⟨⟨xs, eps⟩, hh, h⟩ := bind_ok h
      obtain ⟨hx, rfl⟩ := heard_out _ _ _ _ _ _ _ hh
      split at h
      · rename_i sum eps' heq
        cases heq
        obtain ⟨_, hrow, h⟩ := bind_ok h
        obtain ⟨⟨gamma, claim⟩, hr, h⟩ := bind_ok h
        cases h
        obtain ⟨rfl, rfl⟩ := rounds_exact _ _ _ _ _ hr
        refine ⟨id, d1, hcase, got_ok hsp, ?_, need_ok hrow⟩
        show foldOutput d'.st F row id _ _ _ = foldOutput (spent d1.st id) F row id _ _ _
        rw [(spent_of d1 d' id (got_ok hsp)).1, ← hx]
        rfl
      · cases h

/-- **What an acceptance of the test's fold leaves.** Of `t₁` the fields `st`, `book` and `pass` are
stated. The list of groups of columns is `[]`. -/
theorem fold_exact (p : P12) (j : ℕ) (cur : Fmt.M1.Stage) (cut : List Fmt.DeclaredRound) (t t₁ : T12)
    (rs : List Fmt.RoundView) (row : GroupRow) (L : GroupLayout) (cu : IoppStage)
    (hp : t.pass = .claim row L) (hc : stageAt p j cur = some cu) (hn : rs.length = 1 + cu.k)
    (h : (guardedProximityTestParts.fold p j cur cut).decide t rs [] = .ok t₁) :
    ∃ (id : ℕ) (st : Statement) (book : TreeBook) (n : ℕ × ℕ),
      MaskCase p t (ioppFoldShape cu L) id st book ∧ p.idx[j + 1]? = some n ∧
      t₁.st = Ground.withGroup (spent st id) n.1 n.2 ∧ t₁.book = book ∧
      t₁.pass = .single (foldOutAt st (ioppFoldShape cu L) row id rs) st.groups.size ∧
      Own.foldRowFits (spent st id) (ioppFoldShape cu L) row = true := by
  obtain ⟨n, rows, d', es, hn1, hf, rfl⟩ :=
    H2K.JointK.foldJ_ok p j cur cut t t₁ rs [] row L cu hp hc hn
      (H2K.JointK.ranged_ok _ _ _ _ _ _ h).1
  obtain ⟨id, d1, hcase, hsp, rfl, hrow⟩ := foldD_exact _ _ _ _ _ _ _ _ _ hf
  obtain ⟨e1, e2, -⟩ := spent_of d1 d' id hsp
  refine ⟨id, d1.st, d1.book, n, ?_, hn1, by rw [← e1], e2, by rw [e1]; rfl,
    by rw [← e1]; exact hrow⟩
  rcases hcase with ⟨hm, rfl⟩ | ⟨hm, ids, hr, hi⟩
  · exact .inl ⟨hm, rfl, rfl⟩
  · exact .inr ⟨hm, _, ids, d1, hr, hi, rfl, rfl⟩

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.mapM_filterMap
#print axioms ProofFile.Honest.K12.heard_out
#print axioms ProofFile.Honest.K12.rounds_exact
#print axioms ProofFile.Honest.K12.spent_of
#print axioms ProofFile.Honest.K12.shapes_spent
#print axioms ProofFile.Honest.K12.foldD_exact
#print axioms ProofFile.Honest.K12.fold_exact
