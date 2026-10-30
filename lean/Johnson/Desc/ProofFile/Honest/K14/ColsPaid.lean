-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/ColsPaid.lean: kind K14: ONE OF THE FOUR PREMISES ON WHAT A
MEMBER's OWN PLAY SHOWS FOLLOWS FROM ANOTHER PREMISE: ShowsCols (Honest/K14/Exchange2.lean: the
columns that "LOC" is handed hold the rows' own symbols) from hTab, under Plan2. Statements with
their proofs.

"LOC" has a round, and its half says nothing (quietPart, Honest/K14/Parts.lean: halves): the prover
sends nothing there; the theorems here are general in the thread's halves. The columns that its step
is handed are read off the table at hand by the frame's own functions (readsOf, fillCols:
Honest/Frame.lean), and the thread ties that table to the letter stored. So what they hold follows
from the premise on the committed table's every column, which «Exchange» at "LIN point" asks
already.

Main names:
  mem_of_lookup, fillCols_words   small ones; with no run to fall back on, every column is its
                      read's own words
  reads_loc           what "LOC"'s one round reads: the committed table's column at a location below
                      2 ^ logN
  showsCols_of_tab    **ShowsCols**, from hTab
  exchange4_of_tab    so «Exchange» at "LOC" with no premise on what is shown, under Plan2, hN, hTab

What is assumed, as premises: Plan2 (Debts2.lean). In exchange4_of_tab also hN: no two messages have
one tenant. hTab: the committed table's column at every location holds the rows' own symbols (where
the table has no column at a location, or one that is too short, 0 is read): SHOWN IN NO FILE: no
theorem ties it to a committer written in Lean; the library has one that runs,
Johnson/Bind/Twin.lean, and one as mathematics, Johnson/Top/ToldCommitPlain.lean.

What is not claimed. The other three premises on what is shown. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.Exchange2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes OnBytes.Params
open OnBytes.Slice (rdE)
open VerifiableInference.Desc (OpenedColumn)
open Desc.K14 (P14 readsAtLoc)
open Desc.K14.Honest
open Desc.K14.Law (genK entryAt)

variable {Bk : ProverCoinCounts} {W₀ Rc X₀ P₁ Wt : Type} {Q : P14} {sentU : Array OracleNotice}

/-- What a look-up returns lies in the list. Kin: the frame's lemma of the same short name
(Honest/Law/Rule/FileOkOf.lean) says the same with a Place for the key. -/
theorem mem_of_lookup {β : Type} : ∀ (l : List (Nat × β)) (a : Nat) (b : β),
    l.lookup a = some b → (a, b) ∈ l
  | [], _, _, h => by cases h
  | (a', b') :: l, a, b, h => by
    by_cases e : a = a'
    · subst e
      rw [List.lookup_cons_self] at h
      obtain rfl := Option.some.inj h
      exact List.mem_cons_self
    · rw [List.lookup_cons, show (a == a') = false from by simpa using e] at h
      exact List.mem_cons_of_mem _ (mem_of_lookup l a b h)

/-- **With no run to fall back on, every column is its read's own words**, where fillCols returns.
The frame has a theorem of the same short name with another statement (Honest/Law/Cols.lean); inside
this namespace the short name means this one. -/
theorem fillCols_words : ∀ (q : List Read) (c : List OpenedColumn), fillCols q [] = .ok c →
    ∀ x ∈ c, ∃ r ∈ q, r.words = some x.2.2 ∧ r.pos = x.2.1
  | [], c, h, x, hx => by
    simp only [fillCols] at h
    cases h
    cases hx
  | r :: rs, c, h, x, hx => by
    cases hw : r.words with
    | none => simp [fillCols, hw] at h
    | some w =>
      simp only [fillCols, hw] at h
      split at h
      · cases h
      cases hrec : fillCols rs ([] : List OpenedColumn) with
      | error e =>
        simp only [List.tail_nil, hrec, Except.map] at h
        cases h
      | ok l =>
        simp only [List.tail_nil, hrec, Except.map] at h
        cases h
        rcases List.mem_cons.1 hx with rfl | hx'
        · exact ⟨r, List.mem_cons_self, hw, rfl⟩
        · obtain ⟨r', hr', a, b⟩ := fillCols_words rs l hrec x hx'
          exact ⟨r', List.mem_cons_of_mem _ hr', a, b⟩

/-- **What "LOC"'s one round reads**: the committed table's column at a location below 2 ^ logN, as
the table at hand holds it. -/
theorem reads_loc (Q : P14) (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (VerifiableInference.Desc.Place × Table)) (R : Fmt.Drawn) :
    ∀ r ∈ readsOf chain ft stored tree
      [{ entry := entryAt Q 1, stored := [readsAtLoc Q.S.fold Q.item] }] [R],
      r.words = stored Q.item r.pos ∧ r.pos < 2 ^ Q.S.fold.index.code.logN := by
  intro r hr
  simp only [readsOf, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_map] at hr
  obtain ⟨x, hx, rfl⟩ := hr
  refine ⟨rfl, ?_⟩
  obtain ⟨z, _, hz⟩ := List.mem_map.1 ((Fmt.listOf_mem _ _).1 hx)
  show x < 2 ^ Q.S.fold.index.code.logN
  rw [← hz]
  exact Nat.mod_lt _ (Nat.pos_of_ne_zero (by simp))

/-- **ShowsCols, from the premise on the committed table's every column**: the columns that "LOC" is
handed are read off the table at hand, which the thread ties to the letter stored. -/
theorem showsCols_of_tab {layO : TreeLay} (hQ : Plan2 Q sentU layO) (O : Others Bk W₀ Rc X₀ P₁ Wt)
    (Cl : Type)
    (hTab : ∀ k w, O.valid w → ∀ x < 2 ^ Q.par.S.fold.index.code.logN,
      ∀ r < Q.par.S.fold.index.rows,
        rdE.val (ofF (((O.stored w Q.item x).getD []).toArray.getD r 0)) =
          genK rdE Q.par.S.fold x ((O.holds k w).Rw r)) :
    ShowsCols Q sentU O Cl := by
  obtain ⟨B⟩ := hQ.eight
  have hU := hQ.facts.goes
  intro blk k s m E ds y cols hblk hd hA hMv x col hcol q hq
  obtain ⟨hH, -, -, -, -, -, hV⟩ := hA
  have F := flatOf_carried (Cl := Cl) O.c Q B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 O.tests O.last
    B.made
  have hl := F.at4 hblk
  obtain ⟨_, _, _, e4, _⟩ := blocks_rounds Q sentU B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 B.made hU
  have hr := hl.rounds.trans e4
  have hc := hMv.2
  rw [hr] at hc hd
  have hlen := drawsFit_length _ _ hd
  obtain ⟨R, rfl⟩ : ∃ R, ds = [R] := by
    match ds, hlen with
    | [R], _ => exact ⟨R, rfl⟩
  obtain ⟨c, hcm, hce⟩ := List.mem_map.1 (mem_of_lookup _ _ _ hcol)
  obtain ⟨e1, e2⟩ := Prod.mk.inj hce
  obtain ⟨r, hrm, hw, hp⟩ := fillCols_words _ _ hc c hcm
  obtain ⟨w1, w2⟩ := reads_loc Q _ _ _ _ R r hrm
  have hs : O.stored m.st.input Q.item x = some col := by
    have h1 : E.stored Q.item r.pos = some c.2.2 := w1.symm.trans hw
    rw [hH.1, hp, e1, e2] at h1
    exact h1
  have ht := hTab k _ hV x (by rw [← e1, ← hp]; exact w2) q hq
  rw [hs] at ht
  exact ht

/-- **«Exchange» at "LOC", with no premise on what is shown**: under Plan2, hN (no two messages have
one tenant) and hTab. -/
theorem exchange4_of_tab {layO : TreeLay} (hQ : Plan2 Q sentU layO) (O : Others Bk W₀ Rc X₀ P₁ Wt)
    (Cl : Type) (hN : Function.Injective O.N.tenant)
    (hTab : ∀ k w, O.valid w → ∀ x < 2 ^ Q.par.S.fold.index.code.logN,
      ∀ r < Q.par.S.fold.index.rows,
        rdE.val (ofF (((O.stored w Q.item x).getD []).toArray.getD r 0)) =
          genK rdE Q.par.S.fold x ((O.holds k w).Rw r)) :
    Exchange (letters2 Q sentU O Cl).thread 4 :=
  exchange4 hQ O Cl hN (showsCols_of_tab hQ O Cl hTab)

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.mem_of_lookup
#print axioms ProofFile.Honest.K14.fillCols_words
#print axioms ProofFile.Honest.K14.reads_loc
#print axioms ProofFile.Honest.K14.showsCols_of_tab
#print axioms ProofFile.Honest.K14.exchange4_of_tab
