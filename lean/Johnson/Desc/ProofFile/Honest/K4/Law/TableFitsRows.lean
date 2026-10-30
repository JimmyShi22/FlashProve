-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/TableFitsRows.lean: The two clauses: NO HYPOTHESIS;
`tableFits_three`: CONDITIONAL. Two definitions, and sixteen statements with their proofs.

What is here. THE LAST TWO OF THE ELEVEN CLAUSES OF `k4TableFits` (Honest/K4/Part.lean: the first of
the four public tests on the parts of the feed-forward layers' own rounds, the sub-protocol K4) ARE
TRUE AT EVERY PUBLIC DATA, WITH NO HYPOTHESIS: each part of the row has as many moves as the cut of
the verifier's table of rounds gives it rounds (`moves_cut`); each part spends as many coins
(entries of the two mask messages) as the table has the prover send elements in these rounds
(`spends_cut`). With the six of Law/TableFitsFree.lean EIGHT OF THE ELEVEN HOLD EVERYWHERE;
`tableFits_three`: the test from the three others, each in the test's own text. How. The table is
the row's nineteen (seventeen) stretches laid end to end (`k4Rows`, `k4Rows_flatten`,
Law/ExactFresh/AtSide.lean). Each stretch is one round that neither opens nor closes a masked
sumcheck, or one masked sumcheck: so the cut is the stretches' lengths (`cut_rows`). Part number i
is of the sort that `k4KindsAll` lists at i (`k4_kind_all`, Law/ExactFresh/Whole.lean); a sort's
part has as many moves as the sort sends in rounds (`rowIn_moves`, Law/ExactFresh/AtSideGood.lean)
and spends as many coins as it sends scalars (`Of_spends`; for a masked sumcheck of any shape:
`run_of_call`).

  `cutStep`, `RowOk`, `cut_inner`, `cut_masked`, `cut_rows`, `rows_ok`, `cut_eq`   the cut
  `moves_cut`   **the tenth clause**
  `add_from`, `slots_from`, `run_of_call`, `Of_spends`, `sided_spends`, `rowIn_spends`   the spends
  `kinds_sent`, `sumsBy_rows`   the table's sums
  `spends_cut`   **the eleventh clause**
  `tableFits_three`   the test, from the three others

Not shown here. THE THREE OTHERS: that K4 covers the plan (`covers`); that the group stands in the
list of tails; that each matrix which an earlier sub-proof has committed names an owner in front
(`tableFits_head`, in a file of this folder, has the whole test at the head's own public data, under
the library's hypothesis on the public files). COUNTS ALONE: nothing on what a part sends. Of the
files under Law/ExactFresh/ that it imports it calls lemmas on the row's stretches, sorts, counts
and lengths alone. Nothing on soundness, on completeness or on any other property.

Kin. `add_from` IS THE SAME SENTENCE AS the library's `ProofFile.Honest.foldl_add_shift`
(Honest/BookCutsLaw.lean, which this file's imports do not reach), with one binder in another seat;
`OnBytes.foldl_add` (OnBytes/Chain/Lists.lean) and `SumLaw.foldl_sum` (Honest/SumLaw/SumCut.lean)
say it with `List.sum`. `slots_from` is `MaskedSum.foldl_own`
(Johnson/Desc/Part/MaskedSumLedger.lean) with a fold for `List.sum`. `run_of_call` SAYS THE COUNT OF
the library's `SumLaw.run_count` (Honest/SumLaw/SumCut.lean: `ownRun k + endsN k = runOf k`, at
every shape), in the form in which the test's eleventh clause adds up a part's `spends`. These last
three files are reached by this file's imports; none of these laws is called: each is typed again
here. Sought: by statement, to the letter and up to the bound letters, among the theorems of the
library and of files that are no part of it yet, as they lay with the writer: no hit (that search
sees neither a binder in another seat nor a law behind another definition's name); by short name:
`rows_ok` stands in four further files of the library, `cut_eq` in three, `slots_from` in one: all
eight read: other matters; the nearest, `cut_eq` of Johnson/Desc/K5/Honest/Law/HeardIs.lean, has the
parts' numbers of rounds for another sub-protocol's row.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.ExactFresh.AtSideGood
import Johnson.Desc.ProofFile.Honest.K4.Law.TableFitsFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes.Desc.First.K4 (Rd rounds masked pointRd batchRd)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc.Part.MaskedSum (Call Var ownSlots)
open ProofFile.Honest.K4.ExactFresh

/-! ## 1 The cut -/

/-- The step of `cutOf` (Johnson/Desc/K4/Honest/Front.lean), by a name. -/
def cutStep (s : List Nat × Nat) (d : Rd) : List Nat × Nat :=
  if d.name == .pscEpsilon then (s.1, 1)
  else if d.name == .pscValues then (s.1 ++ [s.2 + 1], 0)
  else if s.2 != 0 then (s.1, s.2 + 1)
  else (s.1 ++ [1], 0)

/-- A stretch of the table: one round that neither opens nor closes a masked sumcheck, or one masked
sumcheck. This defines a hypothesis; the definition claims nothing. -/
def RowOk (L : List Rd) : Prop :=
  (∃ d, L = [d] ∧ (d.name == .pscEpsilon) = false ∧ (d.name == .pscValues) = false) ∨
    ∃ k a b c, L = masked k a b c

theorem cut_inner : ∀ (k n : Nat) (acc : List Nat),
    (List.replicate k ({ name := .pscRound, sent := 2 } : Rd)).foldl cutStep (acc, n + 1) =
      (acc, n + 1 + k)
  | 0, _, _ => rfl
  | k + 1, n, acc => by
    rw [List.replicate_succ, List.foldl_cons]
    have e : cutStep (acc, n + 1) ({ name := .pscRound, sent := 2 } : Rd) = (acc, n + 1 + 1) := by
      simp [cutStep]
    rw [e, cut_inner k (n + 1) acc]
    congr 1
    omega

theorem cut_masked (k a b c : Nat) (acc : List Nat) :
    (masked k a b c).foldl cutStep (acc, 0) = (acc ++ [k + 3], 0) := by
  unfold masked
  rw [List.foldl_append, List.foldl_append]
  have e1 : [({ name := .pscEpsilon, sent := a } : Rd)].foldl cutStep (acc, 0) = (acc, 0 + 1) := rfl
  rw [e1, cut_inner]
  simp [cutStep]
  omega

/-- **The cut of stretches laid end to end is their lengths.** -/
theorem cut_rows : ∀ (Ls : List (List Rd)) (acc : List Nat), (∀ L ∈ Ls, RowOk L) →
    Ls.flatten.foldl cutStep (acc, 0) = (acc ++ Ls.map (·.length), 0)
  | [], acc, _ => by simp
  | L :: Ls, acc, h => by
    rw [List.flatten_cons, List.foldl_append]
    have e : L.foldl cutStep (acc, 0) = (acc ++ [L.length], 0) := by
      rcases h L (List.mem_cons_self ..) with ⟨d, rfl, h1, h2⟩ | ⟨k, a, b, c, rfl⟩
      · simp [cutStep, h1, h2]
      · rw [cut_masked, masked_len]
    rw [e, cut_rows Ls _ fun M hM => h M (List.mem_cons_of_mem _ hM)]
    simp

theorem rows_ok (Q : K4Pub) : ∀ L ∈ k4Rows Q, RowOk L := by
  intro L hL
  unfold k4Rows at hL
  by_cases hg : (Q.g == 0) = true
  · simp only [hg, if_true, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
      or_false] at hL
    rcases hL with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl <;>
      first
        | exact Or.inr ⟨_, _, _, _, rfl⟩
        | exact Or.inl ⟨_, rfl, rfl, rfl⟩
  · simp only [hg, Bool.false_eq_true, if_false, List.cons_append, List.nil_append, List.append_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hL
    rcases hL with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;>
      first
        | exact Or.inr ⟨_, _, _, _, rfl⟩
        | exact Or.inl ⟨_, rfl, rfl, rfl⟩

/-- **The cut of K4's row is the stretches' lengths.** -/
theorem cut_eq (Q : K4Pub) : cutOf Q = (k4Rows Q).map (·.length) := by
  show ((rounds Q.P Q.hp Q.g).foldl cutStep ([], 0)).1 = _
  rw [← k4Rows_flatten, cut_rows _ _ (rows_ok Q)]
  rfl

/-- **THE TENTH CLAUSE.** -/
theorem moves_cut (Q : K4Pub) : ((k4RowIn Q).map (·.moves.length) == cutOf Q) = true := by
  rw [rowIn_moves, ← lens_of_ok (k4Rows_ok Q), cut_eq]
  exact beq_self_eq_true _

/-! ## 2 What a part spends -/

theorem add_from : ∀ (l : List Nat) (a : Nat), l.foldl (· + ·) a = a + l.foldl (· + ·) 0
  | [], a => rfl
  | x :: l, a => by
    rw [List.foldl_cons, List.foldl_cons, add_from l (a + x), add_from l (0 + x)]
    omega

theorem slots_from : ∀ (vs : List Var) (a : Nat),
    vs.foldl (fun n v => n + (v.d - 1)) a = a + (vs.map fun v => v.d - 1).foldl (· + ·) 0
  | [], a => rfl
  | v :: vs, a => by
    rw [List.foldl_cons, List.map_cons, List.foldl_cons, slots_from vs (a + (v.d - 1)),
      add_from _ (0 + (v.d - 1))]
    omega

/-- **A masked sumcheck's part spends as many mask entries as its call sends scalars**, at every
shape. -/
theorem run_of_call (name endName : String) (k : Call) :
    (((name, (⟨0, ownRun k⟩ : Due)) :: endRuns endName k.ends).map (·.2.e)).foldl (· + ·) 0 =
      (scalarsOf k).foldl (· + ·) 0 := by
  obtain ⟨lead, vs, ends⟩ := k
  cases ends with
  | none =>
    have h1 : ownSlots vs = 1 + (vs.map fun v : Var => v.d - 1).foldl (· + ·) 0 := slots_from vs 1
    have h2 : ([lead + 1] ++ vs.map (fun v : Var => v.d - 1) ++ []).foldl (· + ·) 0 =
        0 + (lead + 1) + (vs.map fun v : Var => v.d - 1).foldl (· + ·) 0 := by
      rw [List.append_nil, List.singleton_append, List.foldl_cons]
      exact add_from _ _
    show (0 + (lead + ownSlots vs)) =
      ([lead + 1] ++ vs.map (fun v : Var => v.d - 1) ++ []).foldl (· + ·) 0
    rw [h1, h2]
    omega
  | some e =>
    have h1 : ownSlots (vs ++ [.point OnBytes.zeroE (e.dY + 1)]) =
        1 + (vs.map fun v : Var => v.d - 1).foldl (· + ·) 0 + (e.dY + 1 - 1) := by
      unfold ownSlots
      rw [List.foldl_append, slots_from vs 1]
      rfl
    have h2 : ([lead + 1] ++ vs.map (fun v : Var => v.d - 1) ++ [e.dY, e.n]).foldl (· + ·) 0 =
        0 + (lead + 1) + (vs.map fun v : Var => v.d - 1).foldl (· + ·) 0 + e.dY + e.n := by
      have h3 : ((lead + 1) :: vs.map fun v : Var => v.d - 1).foldl (· + ·) 0 =
          0 + (lead + 1) + (vs.map fun v : Var => v.d - 1).foldl (· + ·) 0 := by
        rw [List.foldl_cons]
        exact add_from _ _
      rw [List.foldl_append, List.singleton_append, h3]
      rfl
    show (0 + (lead + ownSlots (vs ++ [.point OnBytes.zeroE (e.dY + 1)])) + e.n) =
      ([lead + 1] ++ vs.map (fun v : Var => v.d - 1) ++ [e.dY, e.n]).foldl (· + ·) 0
    rw [h1, h2]
    omega

section
variable {W₀ Rc Xi Tr X : Type} (Q : K4Pub) (cells : Tr → Cells) (weights : W₀ → Weights)
  (tokens : Xi → Array Nat) (look : List Fmt.Drawn → OnBytes.Model.Forest.Heard)

/-- A part of a sort spends as many mask entries as the sort sends scalars. -/
theorem Of_spends {x : K4Kind} {i : Nat}
    {y : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X × Sim Xi}
    (h : x.Of Q cells weights tokens look i y) :
    (y.1.spends.map (·.2.e)).foldl (· + ·) 0 = x.sent.foldl (· + ·) 0 := by
  cases x with
  | quiet =>
    obtain rfl : y = _ := h
    rfl
  | lone n =>
    obtain ⟨f, rfl⟩ : ∃ f, y = _ := h
    rfl
  | ms k =>
    obtain ⟨J, rfl, name, endName, rfl⟩ : ∃ J : SumJob K4In Unit, J.shape = k ∧ ∃ name endName,
      y = _ := h
    exact run_of_call name endName J.shape

theorem sided_spends :
    (k4Sided (Rc := Rc) (X := X) Q cells weights tokens look).map
        (fun y => (y.1.spends.map (·.2.e)).foldl (· + ·) 0) =
      (k4KindsAll Q).map fun x => x.sent.foldl (· + ·) 0 := by
  refine List.ext_getElem? fun i => ?_
  rw [List.getElem?_map, List.getElem?_map]
  cases hx : (k4KindsAll Q)[i]? with
  | none =>
    have hn : (k4Sided (Rc := Rc) (X := X) Q cells weights tokens look)[i]? = none := by
      rw [List.getElem?_eq_none_iff] at hx ⊢
      rw [k4Sided_length]
      exact hx
    rw [hn]
    rfl
  | some x =>
    obtain ⟨y, hy, hof⟩ := k4_kind_all (Rc := Rc) (X := X) Q cells weights tokens look hx
    rw [hy]
    exact congrArg some (Of_spends Q cells weights tokens look hof)

end

/-- The row at the small input spends the same: seating a part keeps what it spends. -/
theorem rowIn_spends (Q : K4Pub) :
    (k4RowIn Q).map (fun p => (p.spends.map (·.2.e)).foldl (· + ·) 0) =
      (k4KindsAll Q).map fun x => x.sent.foldl (· + ·) 0 := by
  have e := sided_spends (W₀ := Weights) (Rc := Unit) (Xi := Array Nat) (Tr := Cells) (X := Unit) Q
    id id id fun _ => default
  have hlen : (k4Row (W₀ := Weights) (Rc := Unit) (Xi := Array Nat) (Tr := Cells) (X := Unit) Q
      id id id fun _ => default).length = (k4Sims (Xi := Array Nat) Q).length := by
    have e' := congrArg List.length (k4Sorts_parts Q Unit (Array Nat))
    rw [List.length_map, List.length_map] at e'
    unfold k4Row k4RowIn k4Sims
    rw [List.length_map, List.length_map, List.length_zipIdx, List.length_map,
      List.length_zipIdx, e']
  have e3 : (k4Sided (W₀ := Weights) (Rc := Unit) (Xi := Array Nat) (Tr := Cells) (X := Unit) Q
      id id id fun _ => default).map (fun y => (y.1.spends.map (·.2.e)).foldl (· + ·) 0) =
      ((k4Sided (W₀ := Weights) (Rc := Unit) (Xi := Array Nat) (Tr := Cells) (X := Unit) Q
        id id id fun _ => default).map (·.1)).map
          (fun p => (p.spends.map (·.2.e)).foldl (· + ·) 0) := by
    rw [List.map_map]
    rfl
  rw [← e, e3]
  unfold k4Sided
  rw [map_fst_zip_same _ _ hlen]
  unfold k4Row
  rw [List.map_map]
  exact List.map_congr_left fun p _ => rfl

/-! ## 3 What the table has the prover send -/

/-- Sort by sort: what it sends in each round is what the table's stretch says. -/
theorem kinds_sent (Q : K4Pub) :
    (k4KindsAll Q).map (·.sent) = (k4Rows Q).map fun L => L.map (·.sent) := by
  unfold k4KindsAll k4Kinds k4Rows
  by_cases hg : (Q.g == 0) = true <;>
    simp [hg, K4Kind.sent, sent_level, sent_token, sent_plain, pointRd, batchRd]

theorem sumsBy_rows (f : Rd → Nat) : ∀ Ls : List (List Rd),
    k4SumsBy (Ls.flatten.map f) (Ls.map (·.length)) =
      Ls.map fun L => (L.map f).foldl (· + ·) 0
  | [] => rfl
  | L :: Ls => by
    rw [List.flatten_cons, List.map_append, List.map_cons, List.map_cons]
    show ((L.map f ++ Ls.flatten.map f).take L.length).foldl (· + ·) 0 ::
      k4SumsBy ((L.map f ++ Ls.flatten.map f).drop L.length) (Ls.map (·.length)) = _
    rw [List.take_left' (by simp), List.drop_left' (by simp), sumsBy_rows f Ls]

/-- **THE ELEVENTH CLAUSE.** -/
theorem spends_cut (Q : K4Pub) :
    ((k4RowIn Q).map (fun p => (p.spends.map (·.2.e)).foldl (· + ·) 0) ==
      k4SumsBy ((rounds Q.P Q.hp Q.g).map (·.sent)) (cutOf Q)) = true := by
  have e : (k4KindsAll Q).map (fun x => x.sent.foldl (· + ·) 0) =
      (k4Rows Q).map fun L => (L.map (·.sent)).foldl (· + ·) 0 := by
    have h := congrArg (List.map fun l : List Nat => l.foldl (· + ·) 0) (kinds_sent Q)
    rw [List.map_map, List.map_map] at h
    exact h
  rw [rowIn_spends, e, cut_eq, ← k4Rows_flatten, sumsBy_rows]
  exact beq_self_eq_true _

/-- CONDITIONAL on the three clauses named. **THE TEST ON THE TABLE IS TRUE WHERE ITS THREE OTHER
CLAUSES ARE.** -/
theorem tableFits_three {Q : K4Pub} (h1 : OnBytes.Desc.First.K4.covers Q.P = true)
    (h7 : decide (Q.g < Q.P.tails.size) = true)
    (h8 : ((Q.P.tails.getD Q.g {}).mats.all fun M =>
      M.kind != 1 || (decide (256 ≤ M.aId) && decide (M.aId / 256 - 1 < Q.g) &&
        decide (M.aId % 256 < (Q.P.tails.getD (M.aId / 256 - 1) {}).mats.size))) = true) :
    k4TableFits Q = true :=
  tableFits_of h1 h7 h8 (moves_cut Q) (spends_cut Q)

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.cutStep
#print axioms ProofFile.Honest.K4.RowOk
#print axioms ProofFile.Honest.K4.cut_inner
#print axioms ProofFile.Honest.K4.cut_masked
#print axioms ProofFile.Honest.K4.cut_rows
#print axioms ProofFile.Honest.K4.rows_ok
#print axioms ProofFile.Honest.K4.cut_eq
#print axioms ProofFile.Honest.K4.moves_cut
#print axioms ProofFile.Honest.K4.add_from
#print axioms ProofFile.Honest.K4.slots_from
#print axioms ProofFile.Honest.K4.run_of_call
#print axioms ProofFile.Honest.K4.Of_spends
#print axioms ProofFile.Honest.K4.sided_spends
#print axioms ProofFile.Honest.K4.rowIn_spends
#print axioms ProofFile.Honest.K4.kinds_sent
#print axioms ProofFile.Honest.K4.sumsBy_rows
#print axioms ProofFile.Honest.K4.spends_cut
#print axioms ProofFile.Honest.K4.tableFits_three
