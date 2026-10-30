-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the thread's state at a border is the run's.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/RecordOfThread.lean: where a thread's invariant stands at a
border of a chain with no rounds ahead of it, at the available tables of a run's rounds, its state is
the state of the fold over these rounds at the columns that the run reads. So a fact on the thread's
state is a fact on the state that the run's own fold reaches.

  tree_of_add      the tables available at the border are the rounds' in front of it
  state_of_thread  the statement

No property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Thr
import Johnson.Desc.ProofFile.Honest.Law.Along
import Johnson.Desc.ProofFile.Honest.Law.Cut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block OpenedColumn foldBlocks)
open ProofFile.Honest

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-- **The tables available at the border.** -/
theorem tree_of_add {E₀ : Env} {Q P₁ P₂ : List Played} {stored : Nat → Nat → Option (List UInt64)}
    (ha : E₀.add Q = envOf stored (fun _ _ => none) (P₁ ++ P₂))
    (hs : E₀.sent = (tablesOf P₁).length) (ht : E₀.Tight) : E₀.tree = treeOwn P₁ := by
  funext d
  have e := congrArg Env.tree ha
  cases d with
  | own n =>
    have e' := congrFun e (.own n)
    by_cases hn : n < E₀.sent
    · have l : (E₀.add Q).tree (.own n) = E₀.tree (.own n) := by
        show (if n < E₀.sent then E₀.tree (.own n) else _) = _
        rw [if_pos hn]
      rw [l] at e'
      refine e'.trans ?_
      show ((tablesOf (P₁ ++ P₂))[n]?).bind id = ((tablesOf P₁)[n]?).bind id
      rw [tablesOf_append, List.getElem?_append_left (hs ▸ hn)]
    · have hn' : E₀.sent ≤ n := Nat.le_of_not_lt hn
      rw [ht n hn']
      show none = ((tablesOf P₁)[n]?).bind id
      rw [List.getElem?_eq_none (hs ▸ hn')]
      rfl
  | taken c k =>
    have e' := congrFun e (.taken c k)
    exact e'

/-- **The thread's state is the fold's.** -/
theorem state_of_thread (T : Thread Bk S Cl V W X Pb) {pre : List (Block S Cl)}
    {blk : Block S Cl} {t : List (Block S Cl)} (hcut : T.bs = pre ++ blk :: t) (hft : T.ft = 0)
    (hfr : T.front = 0) (hch : T.chain = 0) {k : Coins Bk} {s : S} {m₀ : Mid W X} {E₀ : Env}
    (hM : T.Made pre.length k s m₀ E₀) {Q P₁ P₂ : List Played}
    {stored : Nat → Nat → Option (List UInt64)}
    (ha : E₀.add Q = envOf stored (fun _ _ => none) (P₁ ++ P₂))
    (hs : (tablesOf P₁).length = treesTo T.bs pre.length)
    {s₀ s' : S} (hb : ∀ x, T.begun k m₀.st.input (m₀.st.heard.take T.front) x → x = s₀)
    {cs : List OpenedColumn}
    (hfold : foldBlocks 0 pre s₀ m₀.seen cs = .ok (s', [], []))
    (hfill : fillCols (readsOf 0 0 stored (treeOwn P₁) (pre.flatMap (·.rounds))
      (m₀.seen.map (·.drawn))) [] = .ok cs) : s = s' := by
  obtain ⟨e1, -, e3, e4, x₀, cols, hbeg, hcols, hf⟩ := hM
  obtain rfl := hb _ hbeg
  have hstored : E₀.stored = stored := congrArg Env.stored ha
  have htree : E₀.tree = treeOwn P₁ := tree_of_add ha (e3.trans hs.symm) e4
  have hd : declsTo T.bs pre.length = pre.flatMap (·.rounds) := by
    unfold declsTo
    rw [hcut, List.take_left' rfl]
  unfold Thread.colsTo at hcols
  rw [hch, hft, hfr, List.drop_zero, hstored, htree, hd, ← e1, hfill] at hcols
  obtain rfl : cs = cols := Except.ok.inj hcols
  rw [hft, hfr, List.drop_zero] at hf
  have hf' : foldBlocks 0 (T.bs.take pre.length) x₀ m₀.seen cs = .ok (s, [], []) := hf
  rw [hcut, List.take_left' rfl] at hf'
  have := Except.ok.inj (hfold.symm.trans hf')
  exact (Prod.mk.inj this).1.symm

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.tree_of_add
#print axioms ProofFile.Honest.K12.Sim2.state_of_thread
