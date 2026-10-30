-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/Shown.lean: under four public premises (not the four of rowsExact), what the
honest sender discloses in its two rounds (shownR) is one function, the same for all data and coins,
of what the instance of the general model discloses.
Terms: Johnson/SendSim/At/Sim.lean; sender, readC, dataOf and the instance's answers:
Johnson/SendSim/At/Bridge.lean. Limits of the folder: Johnson/SendSim/Defs.lean.

What this file proves, for each value of data and coins; no distribution is named. The first three
have the four premises of Spec.shownTie: the job fits its place (sendFits); RidesZero (a table that
is sent along has entries 0 in its 2 ^ h rows if its coins are all 0); the challenge consists of
exactly the seeds (seedsFit); no seed's factor is 0.
  shownTie      Spec.shownTie, stated in Johnson/SendSim/At/Bridge.lean: there is one function back
                such that, for all data and coins c, shownR is back applied to what the instance
                discloses at dataOf data and readC c.
  shown_congr   If the instance discloses the same at (data, c) and at (data', c'), so does the
                sender.
  yAt_inj       If the instance's answers are the same at two such pairs, so are the sender's
                answers yAt. The instance's three answers are the coordinates of y / β, where y is
                the sender's answer and β its seed's factor, and they determine y.
  cols_congr    The disclosed columns are the same for two families of rows whose symbols symOf are
                the same at every queried position of each row's tree. No premise.
  answers_congr   The disclosed answers are the same where all yAt are the same. No premise.

Limits. The function back is obtained by choice; it is not given as an explicit term. RidesZero is a
premise here; it holds for every ride (ridesZero, Johnson/SendSim/At/RideLay.lean).

How it fits. shown_paid (Johnson/SendSim/At/Paid.lean) is shownTie without RidesZero;
Johnson/SendSim/At/JoinRows.lean uses it for rowsExact (Johnson/SendSim/At/RowsExact.lean),
rowsFresh (Johnson/SendSim/At/RowsFresh.lean) and, through fresh_leg, rowsFreshAny
(Johnson/SendSim/At/FreshWideProofs.lean). Since back is one fixed function and readC maps uniform
coins to uniform coins (readUnif), an equation between distributions of what the instance discloses
carries over to shownR. The proofs rest on symOf_eq and col_congr (Johnson/SendSim/At/Symbols.lean,
which defines symOf), ans_tie (Johnson/SendSim/At/Answers.lean, which defines yAt) and
treeTables_get (Johnson/SendSim/At/Stat.lean).

The other names.
  mem_asksOf    a position queried of a tree is in asksOf, as a point, for each row in that tree.
  tabOf, tabOf_col, treeTables_tab, shown_at   a table made from a function from positions to
                columns; the sender's tables are such tables; the disclosed columns of one tree.
-/
import Johnson.SendSim.At.Answers

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt held answers col)

variable (P : K1.Par) (ride : Nat → Option Ride)

/-- If the oracle message of the row ρ is in the tree τ and p is a position queried of τ, then the
pair of ρ and the evaluation point of p in the row's code is in the list asksOf P asks. -/
theorem mem_asksOf (asks : List (List (List Nat))) (ρ : RowN P) (τ p : ℕ)
    (hτ : treeOf P ρ.1 = some τ) (hp : p ∈ asked asks τ) :
    (ρ, ptF (codeAt P ρ).a p) ∈ asksOf P asks := by
  unfold asksOf
  refine List.mem_flatMap.2 ⟨ρ, Finset.mem_toList.2 (Finset.mem_univ ρ), ?_⟩
  rw [hτ]
  exact List.mem_map.2 ⟨p, hp, rfl⟩

/-- A table (Table) with the length and width of the tree shape T. Its symbol at a position holds
the words of the column cl pos, read in the base field, and 0 beyond that column's length. -/
def tabOf (T : TreeShape) (cl : ℕ → List UInt64) : Table where
  logLength := T.logN
  words := T.mainWidth + T.maskWidth
  sym := fun pos i => toF ((cl pos).getD i.val 0)

/-- The column of tabOf T cl at a position p depends only on cl p. -/
theorem tabOf_col (T : TreeShape) (cl cl' : ℕ → List UInt64) (p : ℕ) (h : cl p = cl' p) :
    (tabOf T cl).col p = (tabOf T cl').col p := by
  show (List.ofFn fun i : Fin (T.mainWidth + T.maskWidth) =>
      OnBytes.Slice.ofF (toF ((cl p).getD i.val 0))) =
    List.ofFn fun i : Fin (T.mainWidth + T.maskWidth) =>
      OnBytes.Slice.ofF (toF ((cl' p).getD i.val 0))
  rw [h]

/-- The sender's table number τ is tabOf at the shape of tree number τ and at the column function
col (Johnson/Prover/Send/Core.lean). -/
theorem treeTables_tab (V : ℕ → Rows) (τ : ℕ) :
    (treeTables P V)[τ]? = (P.trees[τ]?).map fun T => tabOf T (col P V τ) :=
  treeTables_get P V τ

/-- The columns that are disclosed of tree number τ: each position queried of τ, with the column of
the sender's table at that position. -/
theorem shown_at (asks : List (List (List Nat))) (V : ℕ → Rows) (τ : ℕ) :
    ((treeTables P V).zipIdx.map fun t => (asked asks t.2).map fun p => (p, t.1.col p))[τ]? =
      (P.trees[τ]?).map fun T =>
        (asked asks τ).map fun p => (p, (tabOf T (col P V τ)).col p) := by
  rw [List.getElem?_map, List.getElem?_zipIdx, treeTables_tab, Option.map_map, Option.map_map,
    Nat.zero_add]
  rfl

/-- The disclosed columns are the same for two families of rows V and V' whose symbols symOf are the
same at every row and every position queried of the tree of the row's oracle message. -/
theorem cols_congr (asks : List (List (List Nat))) (V V' : ℕ → Rows)
    (h : ∀ (ρ : RowN P) (τ p : ℕ), treeOf P ρ.1 = some τ → p ∈ asked asks τ →
      symOf P V ρ p = symOf P V' ρ p) :
    ((treeTables P V).zipIdx.map fun t => (asked asks t.2).map fun p => (p, t.1.col p)) =
      (treeTables P V').zipIdx.map fun t => (asked asks t.2).map fun p => (p, t.1.col p) := by
  refine List.ext_getElem? fun τ => ?_
  rw [shown_at, shown_at]
  refine congrArg (fun F => Option.map F P.trees[τ]?) (funext fun T => ?_)
  refine List.map_congr_left fun p hp => congrArg (Prod.mk p) ?_
  exact tabOf_col T _ _ p (col_congr P V V' τ p fun ρ hρ => h ρ τ p hρ hp)

variable (ds : List Fmt.Drawn)

/-- The sender's lists of answers at (data, c) and at (data', c') are the same if yAt is the same at
every oracle message k and every answer i of it. -/
theorem answers_congr (first : ℕ) (data data' : Nat → Nat → Nat → Option (GF ⊕ GE))
    (c c' : Cs (dueR P ride))
    (h : ∀ k i, k < P.sent.size → i < (shapeAt P k).answers →
      yAt P ride ds data c first k i = yAt P ride ds data' c' first k i) :
    answers P (stAt P first) first (held (fun _ _ _ => 0) first P (rowsR P ride data c))
        (seedsAt P ds) =
      answers P (stAt P first) first (held (fun _ _ _ => 0) first P (rowsR P ride data' c'))
        (seedsAt P ds) := by
  unfold answers
  refine congrArg List.flatten (List.map_congr_left fun k hk => ?_)
  refine List.map_congr_left fun i hi => ?_
  exact congrArg ofE (h k i (List.mem_range.1 (List.mem_filter.1 hk).1) (List.mem_range.1 hi))

/-- If the job fits its place (sendFits), RidesZero holds, the challenge consists of exactly the
seeds (seedsFit) and no seed's factor is 0: where the instance's answers are the same at (data, c)
and at (data', c'), so is each answer yAt of the sender. -/
theorem yAt_inj (hf : sendFits P ride = true) (hR : RidesZero ride) (hs : seedsFit P ds = true)
    (hβ : ∀ s ∈ seedsAt P ds, readE s.2 ≠ 0) (first : ℕ)
    (data data' : Nat → Nat → Nat → Option (GF ⊕ GE)) (c c' : Cs (dueR P ride))
    (h : (sender P ride).ansAt (wOf P ds) (dataOf P ride data) (readC P ride c) =
      (sender P ride).ansAt (wOf P ds) (dataOf P ride data') (readC P ride c'))
    (k i : ℕ) (hk : k < P.sent.size) (hi : i < (shapeAt P k).answers) :
    yAt P ride ds data c first k i = yAt P ride ds data' c' first k i := by
  have hb : bInv P ds i ≠ 0 := inv_ne_zero (hβ _ (seedAt_mem P ds k i hk hi))
  refine mul_left_cancel₀ hb (ext_crd fun s => ?_)
  have e := congrFun h (⟨⟨k, hk⟩, (⟨i, hi⟩, s)⟩ : AnsN P)
  rw [ans_tie P ride ds data c hf hR hs first ⟨k, hk⟩ ⟨i, hi⟩ s,
    ans_tie P ride ds data' c' hf hR hs first ⟨k, hk⟩ ⟨i, hi⟩ s] at e
  exact e

/-- Under the four premises of Spec.shownTie (Johnson/SendSim/At/Bridge.lean): where the instance
discloses the same at (data, c) and at (data', c'), the sender discloses the same in its two rounds
(shownR). -/
theorem shown_congr (hf : sendFits P ride = true) (hR : RidesZero ride)
    (hs : seedsFit P ds = true) (hβ : ∀ s ∈ seedsAt P ds, readE s.2 ≠ 0) (first : ℕ)
    (asks : List (List (List Nat))) (data data' : Nat → Nat → Nat → Option (GF ⊕ GE))
    (c c' : Cs (dueR P ride))
    (h : (sender P ride).shown (wOf P ds) (asksOf P asks) (dataOf P ride data) (readC P ride c) =
      (sender P ride).shown (wOf P ds) (asksOf P asks) (dataOf P ride data') (readC P ride c')) :
    shownR P first ride data ds asks c = shownR P first ride data' ds asks c' := by
  have h1 := List.map_inj_left.1 (congrArg Prod.fst h)
  have h2 := congrArg Prod.snd h
  unfold shownR
  rw [cols_congr P asks (rowsR P ride data c) (rowsR P ride data' c') fun ρ τ p hτ hp => by
      rw [symOf_eq P ride data c hf hR, symOf_eq P ride data' c' hf hR]
      exact h1 _ (mem_asksOf P asks ρ τ p hτ hp),
    answers_congr P ride ds first data data' c c'
      (yAt_inj P ride ds hf hR hs hβ first data data' c c' h2)]

/-- Proof of Spec.shownTie. By shown_congr, shownR factors through what the instance discloses; the
function back is obtained from that by choice. -/
theorem shownTie : Spec.shownTie := by
  intro P first ride ds asks hf hR hs hβ
  have hF : Function.FactorsThrough
      (fun x : (Nat → Nat → Nat → Option (GF ⊕ GE)) × Cs (dueR P ride) =>
        shownR P first ride x.1 ds asks x.2)
      (fun x : (Nat → Nat → Nat → Option (GF ⊕ GE)) × Cs (dueR P ride) =>
        (sender P ride).shown (wOf P ds) (asksOf P asks) (dataOf P ride x.1)
          (readC P ride x.2)) :=
    fun x x' h => shown_congr P ride ds hf hR hs hβ first asks x.1 x'.1 x.2 x'.2 h
  obtain ⟨back, hb⟩ := (Function.factorsThrough_iff _).1 hF
  exact ⟨back, fun data c => congrFun hb (data, c)⟩

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.shown_congr
#print axioms OnBytes.SendSim.At.shownTie
