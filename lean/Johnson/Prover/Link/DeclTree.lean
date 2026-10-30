-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/DeclTree.lean: THE COPY's FILE's PROXIMITY TEST: THE TREE THAT THE PLAN's ROUND
"CS" DECLARES IS THE BOOK's, in number, length and width; and the written column has that width: the
two clauses decl and width, to the letter, of the loop's invariant (FormInv, FormInv.lean).
Statements and proofs.

  tree_of_seats     the tree that rides for the reading (ReadSeat,
                    Johnson/Prover/Link/ReadSeat.lean) IS the tree of the library's SeatP
                    (Johnson/Desc/K12/Law/SwDid.lean): so it has that number, that length and
                    these two lists of symbols
  width_of_symbols  a tree's width from the shapes of its parts
  width_stage       at the two parts of a tree that a switch to a stage but the last sends: the
                    format's width wMid
  decl_later        the clause on the declared tree, at stage number j + 1 that is not the last
  width_later       the clause on the column, at the column that a switch has written (stageColW)
  decl_first        the clause on the declared tree at stage 0 of the link's test: from the numbers
                    that the link's own maker lays (numsOf, Johnson/Desc/Link/LinkDesc.lean)

By: cs_opens, listsOf_first, listsOf_later (DeclPlan.lean); length_stageColW (HyStage.lean).

Limits. ReadSeat, SeatP AT THE NUMBER firstTree + (free + j), Dealt and the stages' list are
premises: the library's seatP_of_sent (Johnson/Desc/K12/Law/SwTies.lean) gives SeatP at firstTree +
the roots in front of the sending. At the last stage nothing is said here but base_opens
(DeclPlan.lean).
Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.DeclPlan
import Johnson.Prover.Link.ReadSeat
import Johnson.Prover.Link.HyStage
import Johnson.Desc.K12.Law.SwDid
import Johnson.Desc.K12.Law.ChainOf
import Johnson.Desc.Link.LinkDesc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw (SeatP)
open H2K.Pub (sgOf)

/-- **The tree of ReadSeat is the tree of SeatP.** -/
theorem tree_of_seats (st : Statement) (book : TreeBook) (ms : List ℕ) (id tN : ℕ) (tr : Tree)
    (k logN : ℕ) (shapes : List OracleShape) (R : ReadSeat st book ms id tN tr)
    (Q : SeatP st book (ms ++ [id]) k logN shapes) :
    tr.number = k ∧ tr.shape.logN = logN ∧
      tr.shape.mainSymbols = (shapes.map fun s => s.mainRows * s.mainDeg).toArray ∧
      tr.shape.maskSymbols = (shapes.map fun s => s.maskRows * 3).toArray := by
  obtain ⟨t, tree, hb, hn, hl, hm, hk, hp⟩ := Q.tree
  have h0 : 0 < (ms ++ [id]).length := by simp
  have p0 := hp 0 h0
  have p1 := R.place 0 h0
  rw [List.getD_eq_getElem _ _ h0, p1] at p0
  obtain rfl : tN = t := congrArg Prod.fst (Option.some.inj p0)
  obtain rfl : tr = tree := Option.some.inj (R.inBook.symm.trans hb)
  exact ⟨hn, hl, hm, hk⟩

/-- A tree's width from the shapes of its parts. -/
theorem width_of_symbols (T : TreeShape) (shapes : List OracleShape)
    (h1 : T.mainSymbols = (shapes.map fun s => s.mainRows * s.mainDeg).toArray)
    (h2 : T.maskSymbols = (shapes.map fun s => s.maskRows * 3).toArray) :
    T.mainWidth + T.maskWidth =
      (shapes.map fun s => s.mainRows * s.mainDeg).sum +
        (shapes.map fun s => s.maskRows * 3).sum := by
  unfold TreeShape.mainWidth TreeShape.maskWidth
  rw [h1, h2, List.foldl_toArray, List.foldl_toArray, List.sum_eq_foldl, List.sum_eq_foldl]

/-- The format's width. -/
theorem width_stage (cur : Fmt.M1.Stage) (c : IoppStage) (hk : cur.h ≤ cur.k) (hc : c.h = cur.h) :
    ((stageShapes (sgOf cur) c).map fun s => s.mainRows * s.mainDeg).sum +
      ((stageShapes (sgOf cur) c).map fun s => s.maskRows * 3).sum = Fmt.M1.wMid cur := by
  have e : cur.h + (cur.k - cur.h) = cur.k := Nat.add_sub_cancel' hk
  simp only [stageShapes, switchTargetStage, foldMaskNotice, ioppFoldShape, sgOf, Fmt.M1.wMid,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hc, e]
  omega

/-- **The clause on the declared tree, behind a switch.** -/
theorem decl_later (N : H2U.TestNums) (j : ℕ) (cur next : Fmt.M1.Stage)
    (rest : List Fmt.M1.Stage) (l : Laid) (st : Statement) (book : TreeBook) (o id tN : ℕ)
    (tr : Tree) (c : IoppStage) (hm : N.ownMask = false)
    (hs : N.stages.drop (j + 1) = cur :: next :: rest)
    (hD : Dealt cur (next :: rest) ((listsOf N).drop (j + 1)) l) (hk : cur.h ≤ cur.k)
    (hc : c.h = cur.h) (R : ReadSeat st book [o] id tN tr)
    (Q : SeatP st book [o, id] (N.firstTree + (N.free + j)) cur.C.a (stageShapes (sgOf cur) c))
    (dS dC : Fmt.DeclaredRound) (hcut : ((l.drop (1 + cur.k)).take 2).map (·.1) = [dS, dC]) :
    ∃ o', dC.opens = [o'] ∧ o'.1.tree = tr.number ∧ o'.1.a = cur.C.a ∧
      o'.1.W = tr.shape.mainWidth + tr.shape.maskWidth := by
  obtain ⟨hn, -, h1, h2⟩ := tree_of_seats st book [o] id tN tr _ _ _ R Q
  have hlen : j + 3 ≤ N.stages.length := by
    have := congrArg List.length hs
    rw [List.length_drop] at this
    simp only [List.length_cons] at this
    omega
  have hcur : N.stages[j + 1]? = some cur := by
    have := congrArg (·[0]?) hs
    simpa [List.getElem?_drop] using this
  have hx := listsOf_later N j cur hm hcur
  have hne : (j + 2 == N.stages.length) = false := by
    rw [beq_eq_false_iff_ne]
    omega
  rw [hne] at hx
  obtain ⟨hj, hxe⟩ := List.getElem?_eq_some_iff.1 hx
  rw [List.drop_eq_getElem_cons hj, hxe] at hD
  refine ⟨_, (cs_opens cur next rest _ _ l hD dS dC hcut).2, hn.symm, rfl, ?_⟩
  rw [width_of_symbols _ _ h1 h2, width_stage cur c hk hc]
  rfl

/-- **The clause on the column, behind a switch.** -/
theorem width_later (cur : Fmt.M1.Stage) (c : IoppStage) (st : Statement) (book : TreeBook)
    (o id tN k : ℕ) (tr : Tree) (tabM tabZ : ℕ → GE) (tM tZ fM fT : ℕ → ℕ → GE)
    (hk : cur.h ≤ cur.k) (hc : c.h = cur.h) (R : ReadSeat st book [o] id tN tr)
    (Q : SeatP st book [o, id] k cur.C.a (stageShapes (sgOf cur) c)) (x : ℕ) :
    (stageColW (sgOf cur) tabM tabZ tM tZ fM fT x).length =
      tr.shape.mainWidth + tr.shape.maskWidth := by
  obtain ⟨-, -, h1, h2⟩ := tree_of_seats st book [o] id tN tr _ _ _ R Q
  rw [width_of_symbols _ _ h1 h2, width_stage cur c hk hc, length_stageColW]
  have e : cur.h + (cur.k - cur.h) = cur.k := Nat.add_sub_cancel' hk
  simp only [sgOf, Fmt.M1.wMid, e]
  omega

/-- **The clause on the declared tree, at stage 0 of the link's test.** -/
theorem decl_first (P : Desc.K15.P15) (Z : H2U.PlaceNums) (lay : TreeLay)
    (cur next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (l : Laid) (tr : Tree)
    (hZ : Desc.K15.numsOf P = some Z) (hm : P.S.masksAhead = true)
    (hL : layTrees P.codes (Desc.K15.sent P) = some lay) (hT : lay.shapes[0]? = some tr.shape)
    (hn : tr.number = 0) (hl : tr.shape.logN = cur.C.a)
    (hD : Dealt cur (next :: rest) (listsOf Z.nums) l)
    (dS dC : Fmt.DeclaredRound) (hcut : ((l.drop (1 + cur.k)).take 2).map (·.1) = [dS, dC]) :
    ∃ o', dC.opens = [o'] ∧ o'.1.tree = tr.number ∧ o'.1.a = cur.C.a ∧
      o'.1.W = tr.shape.mainWidth + tr.shape.maskWidth := by
  have hN : Z.nums.ownMask = false ∧ Z.nums.first =
      [(⟨tr.shape.logN, tr.shape.mainWidth + tr.shape.maskWidth, false, 0⟩, .own 0)] := by
    unfold Desc.K15.numsOf at hZ
    simp only [hL, hT, Option.bind_eq_bind, Option.bind_some, Option.pure_def] at hZ
    by_cases hg : (lay.shapes.size == 1) = true
    · simp only [hg, guard, if_true, Option.bind_some, Option.pure_def, Option.some.injEq] at hZ
      subst hZ
      exact ⟨by simp [hm], rfl⟩
    · simp [hg, guard] at hZ
  have hx := listsOf_first Z.nums hN.1
  obtain ⟨hj, hxe⟩ := List.getElem?_eq_some_iff.1 hx
  have hd : listsOf Z.nums = Z.nums.first :: (listsOf Z.nums).drop 1 := by
    have := List.drop_eq_getElem_cons hj
    rw [List.drop_zero, hxe] at this
    exact this
  rw [hd, hN.2] at hD
  exact ⟨_, (cs_opens cur next rest _ _ l hD dS dC hcut).2, hn.symm, hl, rfl⟩

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.tree_of_seats
#print axioms Johnson.Prover.Link.width_of_symbols
#print axioms Johnson.Prover.Link.width_stage
#print axioms Johnson.Prover.Link.decl_later
#print axioms Johnson.Prover.Link.width_later
#print axioms Johnson.Prover.Link.decl_first
