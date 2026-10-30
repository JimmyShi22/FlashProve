-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/GroupReads.lean: what the first code switch of a proximity test reads of a
group of several members in several trees is the long symbol of the three folded code words. That is
`hy_group`. It does at a first stage of any layout what `hy_stage`
(Johnson/Prover/Link/HyStage.lean) does at a stage that a switch has made, and `hy_first`
(Johnson/Prover/Link/FrontHy.lean) at the link's group. Its conclusion is that of `hy_stage` word
for word, with `layJ G m` and `layQ G r` as the stage's message and tails: the hypothesis `hy` of
`claim_behind` (Johnson/Prover/Link/SwitchHolds.lean). General in the stage, the group, the group's
public data and the layout. One definition and two theorems with their proofs. It depends on no
frame for an honest side.

In the list: a stage s (`Sg`, OnBytes/Slice/Stage.lean) has a main code `s.C`, a mask code `s.Z` and
the number `s.t` of positions that are sampled. A group G (`Gp s`, OnBytes/Slice/KeyGroup.lean) is
finitely many members; a member is the format of a sent message (`G.mb j`) with a seat
(`G.seat j`): the rows of the stage's tables that the message's rows take. P (`GpData G`,
OnBytes/Slice/BlkProxGp.lean) is what is public of the group. The book (`TreeBook`) lists the trees
sent so far; a tree's place is its index in that list. For the member j, `P.tp j` is the place of
its tree, `P.d j` the data of the round that sent the tree, and `P.lay j` the member's cut: the
words of a column at which its main symbols and its mask symbols begin. The parameter `cut` is
something else: the declared rounds of the switch. The fresh table is the first fold's fresh mask
rows: its tree is at the place `P.ft`, has the depth `P.aF` and was sent by the round with the data
`P.dF`; its symbols begin at word `P.oF` of a column. `P.ts` lists the places of the trees that the
switch opens. `dAt t` is the data of the round that sent the tree at the place t, and `c t` is that
tree's column function: from a position to a column, which is a list of words. gs are the groups
that the switch is dealt, one for each tree of `P.ts`; a dealt column is a position with a list of
words. m and r are the members' messages and tails, φ and ψ the fresh table's; the four are free
parameters. The old rows (`old`) are the three folded rows that the switch reads. A long symbol is
a symbol under the code of the three folded rows (`s.cMid`).

  `hy_group`: under the hypotheses listed below: at each sampled position the code word of
    (`foldMsg`, `foldTl`), at the members' messages and tails laid at their seats (`layJ`, `layQ`,
    Johnson/Desc/K12/Honest/Group.lean), shows what was read. In Lean: for every i and α, `s.cMid.T`
    of that code word at `Qs i` and α is `symS s old out.positions D.y (Qs i).val α`, where `D.y`
    holds the symbols read of the old rows
  `groups_of`: the second half of `GroupsAre` (Johnson/Desc/K12/Law/FirstRead.lean) at `colsOf`.
    If, group by group, each dealt column's position lies in the tree, the column function's column
    there has the tree's width and the dealt column is that column, then `colsOf dAt c` at the tree
    and the position returns the dealt column
  `colsOf dAt c t x`: a definition: the written columns of the trees, by a tree's place in the book,
    as `firstReads_keyed` takes them: at every position the column (`colW`,
    OnBytes/Slice/Stage.lean; empty outside the tree) of the oracle that the column function makes
    (`orcOf`, Johnson/Prover/Link/HyStage.lean)

By what. `firstReads_keyed` (Johnson/Desc/K12/Law/FirstRead.lean) gives `ReadTie`
(Johnson/Desc/K12/Law/JointK.lean) at the oracles that the column functions make; its hypothesis
`GroupsAre` comes from `hpos` and `groups_of` by `groupsAre_of`
(Johnson/Desc/K12/Law/StepGroups.lean). `read_of_tie` (Johnson/Prover/Link/HyStage.lean) makes of
`ReadTie` and `Did` the equation at the three folded words. `ofOrc_enc` and `frOf_enc`
(Johnson/Desc/K12/Honest/Written.lean), `word_enc` (Johnson/Desc/K12/Honest/Group.lean) and
`foldWords_enc` (Johnson/Prover/Link/FoldEnc.lean) rewrite these words as the code word of
(`foldMsg`, `foldTl`). `groups_of` is proved by `colW_orcOf` (Johnson/Prover/Link/HyStage.lean).

Hypotheses of `hy_group`.
- `hs`: the stage's sizes are in order (`Sg.Sized`, OnBytes/Slice/Numbers.lean).
- `h`: a switch has run (`Did`, Johnson/Desc/K12/Law/SwDid.lean) on the dealt groups with the keys
  that the description's `keyed` (Johnson/Desc/K12/Join.lean) puts on them.
- `hk`, `hh`, `hP`, `hL`, `hparts`, `hkeys`: the public hypotheses of the library's reading theorem
  at a group (`firstReads_keyed`), word for word.
- `hdM`, `hdF`: `P.d j` is `dAt (P.tp j)`, and `P.dF` is `dAt P.ft`.
- `hlenM`, `hlenF`: each tree's columns have the tree's width.
- `hpos`: group by group, the dealt positions are the tree's own list (`ownAt`,
  OnBytes/Slice/BlkProxMany.lean) under the sampled positions.
- `hcols`: each dealt column is the column function's at its own position. It has two more clauses:
  the position lies in the tree; the column has the tree's width. These two follow from the other
  hypotheses, though no lemma states that; they are hypotheses all the same.
- `hZa`: the mask code is not longer than the fresh table's tree.
- `hMain`, `hMask`, `hF`: each member's rows' symbols, and the fresh mask rows', stand in the
  columns at the member's cut (the premises of `ofOrc_enc` and `frOf_enc`,
  Johnson/Desc/K12/Honest/Written.lean). For the fresh mask rows the place in a column is word
  `P.oF`, in the columns of the tree at the place `P.ft`.
- `hold`: the old rows are the first fold's output. `hkept`: the row that was folded has no form on
  a kept member. `hγ`: the fold's point has `s.h + s.g` coordinates.
- `hlog`: the old rows' code has the stage's depth.
- `hQ`: `Qs i` is sampled position number i. `ht`: as many positions were sampled as the stage
  states.

Limits. No hypothesis is proved here; that they hold together, at a run, at any value, is not shown
in this file. At a stage that samples no position `hy_group` is vacuous. Members that share a tree,
and a fresh table that stands in a member's tree, share one round's data and one column function:
that is what the letter `dAt` says. At a group without a member the law speaks of the fresh table
alone. Nothing on a decision, on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.Group
import Johnson.Desc.K12.Honest.Written
import Johnson.Desc.K12.Law.FirstRead
import Johnson.Desc.K12.Law.StepGroups
import Johnson.Prover.Link.FoldEnc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun Cb _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw H2K.JointK
open Johnson.Prover.Link (symG orcOf colW_orcOf ext0 foldMsg foldTl foldWords_enc read_of_tie)

/-- The trees' written columns, by a tree's place in the book. `dAt t`: the data of the round that
sent the tree at the place t. `c t`: that tree's column function, from a position to a column. -/
def colsOf (dAt : ℕ → PQ.RD) (c : ℕ → ℕ → List UInt64) (t x : ℕ) : Option (List UInt64) :=
  some (colW (dAt t) (orcOf (dAt t) (c t)) x)

/-- The second half of `GroupsAre` (Johnson/Desc/K12/Law/FirstRead.lean) at `colsOf`, from dealt
columns that are the column functions'. -/
theorem groups_of (dAt : ℕ → PQ.RD) (c : ℕ → ℕ → List UInt64) :
    ∀ (ts : List ℕ) (gs : List (List (ℕ × List UInt64))),
    List.Forall₂ (fun t (grp : List (ℕ × List UInt64)) => ∀ x ∈ grp,
      x.1 < PQ.posN (dAt t).tree ∧ (c t x.1).length = PQ.colW (dAt t).tree ∧ x.2 = c t x.1) ts gs →
    List.Forall₂ (fun t (grp : List (ℕ × List UInt64)) => ∀ x ∈ grp,
      colsOf dAt c t x.1 = some x.2) ts gs
  | [], [], _ => List.Forall₂.nil
  | t :: ts, _ :: gs, h => by
    obtain ⟨h1, h2⟩ := List.forall₂_cons.1 h
    refine List.Forall₂.cons (fun x hx => ?_) (groups_of dAt c ts gs h2)
    obtain ⟨a1, a2, a3⟩ := h1 x hx
    unfold colsOf
    rw [colW_orcOf (dAt t) (c t) x.1 a1 a2, a3]

variable {old : SingleRows} {T : SwitchTarget} {gp : ℕ} {others : Array OracleNotice}
  {St St' : Statement} {Bk Bk' : TreeBook} {roots : ℕ} {out : Switched} {row : GroupRow}
  {lay : GroupLayout} {theta : E} {D : Taken}

/-- **The hypothesis `hy` of `claim_behind` at a group of several members in several trees.**
`claim_behind` is in Johnson/Prover/Link/SwitchHolds.lean. The file's head lists the hypotheses. -/
theorem hy_group (p : P12) (cut : List Fmt.DeclaredRound) (gs : List (List (ℕ × List UInt64))) (s : Sg)
    (hs : s.Sized) (G : Gp s) (P : GpData G) (cu : IoppStage) (L : GroupLayout) (id : ℕ)
    (h : Did p.nums.firstTree (keyed p cut gs) old T gp others St Bk roots St' Bk' out row lay theta
      D)
    (hk : cu.k = s.h + s.g) (hh : cu.h = s.h) (hP : P.Pub p.nums.firstTree) (hL : P.LayG L)
    (hparts : PartsP P St Bk id)
    (hkeys : (cut.flatMap fun r => r.opens.map fun o => o.1.tree - p.nums.firstTree) =
      P.ts.map P.key)
    (dAt : ℕ → PQ.RD) (hdM : ∀ j, P.d j = dAt (P.tp j)) (hdF : P.dF = dAt P.ft)
    (c : ℕ → ℕ → List UInt64)
    (hlenM : ∀ j x, x < 2 ^ (G.mb j).a → (c (P.tp j) x).length = PQ.colW (P.d j).tree)
    (hlenF : ∀ x, x < 2 ^ P.aF → (c P.ft x).length = PQ.colW P.dF.tree)
    (hpos : List.Forall₂ (fun t (grp : List (ℕ × List UInt64)) => grp.map (·.1) =
      (ownAt (P.log t) (Positions.ofDraws s.C.a D.rC.drawn.poss)).toList) P.ts gs)
    (hcols : List.Forall₂ (fun t (grp : List (ℕ × List UInt64)) => ∀ x ∈ grp,
      x.1 < PQ.posN (dAt t).tree ∧ (c t x.1).length = PQ.colW (dAt t).tree ∧ x.2 = c t x.1) P.ts gs)
    (hZa : s.Z.a ≤ P.aF)
    (m : G.Msgs) (r : Tails G) (φ : s.cFr.J → GE) (ψ : s.cFr.Q → GE)
    (hMain : ∀ j x, x < 2 ^ (G.mb j).a → ∀ i : Fin (G.mb j).nM,
      (if (P.lay j).base then read1 (c (P.tp j) x) ((P.lay j).oM + i.val)
        else read3 (c (P.tp j) x) ((P.lay j).oM + 3 * i.val)) =
        symG (G.mb j).C x (ext0 fun a => m j (.inl (i, a))) (ext0 fun q => r j (.inl (i, q))))
    (hMask : ∀ j x, x < 2 ^ (G.mb j).a → ∀ i : Fin (G.mb j).nZ,
      read3 (c (P.tp j) x) ((P.lay j).oZ + 3 * i.val) =
        symG (G.mb j).Z (x % 2 ^ (G.mb j).Z.a) (ext0 fun a => m j (.inr (i, a)))
          (ext0 fun q => r j (.inr (i, q))))
    (hF : ∀ x, x < 2 ^ P.aF → ∀ b : Fin s.h → Bool, read3 (c P.ft x) (P.oF + 3 * Sz.rowNo b) =
        symG s.Z (x % 2 ^ s.Z.a) (ext0 fun a => φ (b, a)) (ext0 fun q => ψ (b, q)))
    (S₀ : Statement) (row₀ : GroupRow) (eps claim : E) (gamma : List E)
    (hold : old = foldOutput S₀ (ioppFoldShape cu L) row₀ id eps gamma claim)
    (hkept : row₀.kept = #[]) (hγ : gamma.length = s.h + s.g) (hlog : D.code.logN = s.C.a)
    (Qs : Fin s.t → s.Ps) (hQ : ∀ i, (Qs i).val = D.rC.drawn.poss.getD i.val 0)
    (ht : D.rC.drawn.poss.length = s.t) :
    ∀ i α, s.cMid.T (s.cMid.enc (foldMsg s (layJ G m) φ (readP (s.h + s.g) gamma))
        (foldTl s (layQ G r) ψ (readP (s.h + s.g) gamma))) (Qs i) α =
      symS s old out.positions D.y (Qs i).val α := by
  intro i α
  have hRd := firstReads_keyed p cut gs s G P cu L St Bk id
    (fun j => orcOf (P.d j) (c (P.tp j))) (orcOf P.dF (c P.ft)) (colsOf dAt c) D.rC.drawn.poss hk hh
    hP hL hparts (fun j x => by unfold colsOf; rw [← hdM j]) (fun x => by unfold colsOf; rw [← hdF])
    hkeys (groupsAre_of _ _ _ _ _ hpos (groups_of dAt c _ _ hcols))
  have hx : (Qs i).val ∈ D.rC.drawn.poss := by
    rw [hQ i, List.getD_eq_getElem _ _ (by rw [ht]; exact i.isLt)]
    exact List.getElem_mem _
  have e := read_of_tie s _ _ (ioppFoldShape cu L) id h hRd S₀ row₀ eps claim gamma hold hkept hγ
    hlog (Qs i) hx α
  have eM : (fun j => (G.mb j).ofOrc (P.lay j) (P.d j) (orcOf (P.d j) (c (P.tp j)))) =
      fun j => (G.mb j).cd.enc (m j) (r j) := funext fun j =>
    ofOrc_enc (G.mb j) (P.lay j) (P.d j) (c (P.tp j)) (hP.posN j) (hlenM j)
      (fun h0 =>
        (congrArg Fmt.M1.Code.a ((G.seat j).hC ⟨0, h0⟩)).trans ((G.seat j).hM ⟨0, h0⟩).symm)
      (m j) (r j) (hMain j) (hMask j)
  rw [eM, word_enc G m r, frOf_enc s P.aF P.oF P.dF (c P.ft) hP.fPosN hlenF hZa φ ψ hF,
    foldWords_enc s hs] at e
  exact e

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.groups_of
#print axioms ProofFile.Honest.K12.hy_group
#print axioms ProofFile.Honest.K12.colsOf
