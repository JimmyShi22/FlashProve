-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/MadeLaw.lean: the generic step of the invariant `Thr`
(Honest/Thread/Thr.lean): its clauses (F) and (X) after a sub-protocol, from the two before it and
the sub-protocol's own step. That is, `MadeNext` (Honest/Thread/Pays.lean) holds at every
sub-protocol of a list, if the tests on the parameters pass (`Thread.fits`) and all sub-protocols of
the list pass `planOk` and `shaped`. No parameter of a table of joints, no item and no definition of
a prover's side is in it. A lemma on this folder's own functions and definitions.

  1  `take_succ_some`, `declsTo_succ`, `treesTo_succ`, `flatMap_id_map`, `steps_oracles`,
     `Env.add_keeps`   small lemmas
  2  `made_next`   the step; `reach_of_made`   what (X) gives the library's lemmas along the
     verifier's run

How it is proved. (F): `drawsFit_append`. What was heard and shown, and what the stops may read:
`play_mid`, `play_heard`, `yields_drawn`. The count of trees: `tables_count`
(Honest/Law/Causal.lean) over `steps_shaped`. No tree above those sent: `Env.add_tight`. The
columns: `readsOf_append`, `fillCols_append`, `fillCols_mono`. The verifier's state: the library's
own `fold_more` and `fold_snoc` (Johnson/Top/H0/Walk/Reach.lean).

Limits.
  * It is none of the library's goals.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.PaysLaw
import Johnson.Desc.ProofFile.Honest.Law.Causal
import Johnson.Top.H0.Walk.Reach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc
open Johnson.Desc.First.Walk.Tied (Reach fold_more fold_snoc reach_of_fold)

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-! ## 1 Small lemmas -/

theorem take_succ_some {α : Type} {l : List α} {b : Nat} {a : α} (h : l[b]? = some a) :
    l.take (b + 1) = l.take b ++ [a] := by
  rw [List.take_add_one, h]
  rfl

theorem declsTo_succ {bs : List (Block S Cl)} {b : Nat} {blk : Block S Cl}
    (h : bs[b]? = some blk) : declsTo bs (b + 1) = declsTo bs b ++ blk.rounds := by
  unfold declsTo
  rw [take_succ_some h, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]

theorem treesTo_succ {bs : List (Block S Cl)} {b : Nat} {blk : Block S Cl}
    (h : bs[b]? = some blk) :
    treesTo bs (b + 1) = treesTo bs b + (blk.oracles.flatMap id).length := by
  unfold treesTo
  rw [take_succ_some h, List.flatMap_append, List.length_append, List.flatMap_cons,
    List.flatMap_nil, List.append_nil]

theorem flatMap_id_map {α β : Type} (f : α → List β) :
    ∀ l : List α, (l.map f).flatMap id = l.flatMap f
  | [] => rfl
  | a :: t => congrArg (f a ++ ·) (flatMap_id_map f t)

/-- The `Step`s that `chainSteps` prepares for one sub-protocol declare the sub-protocol's oracle
messages. -/
theorem steps_oracles {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {v : Option V} {blk : Block S Cl} {hs : List (Placed V W X)} {l : List (Step W X)}
    (h : chainSteps B rows look v [blk] hs = .ok l) :
    l.flatMap (·.oracles) = blk.oracles.flatMap id := by
  obtain ⟨h1, h2⟩ := chainSteps_rows [blk] hs l h
  have ho := h1 blk List.mem_cons_self
  have e := congrArg (List.map fun z => z.2.1) h2
  rw [List.map_map, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_map] at e
  have e1 : l.map (·.oracles) = (blk.rounds.zip blk.oracles).map Prod.snd := e
  have e2 : (blk.rounds.zip blk.oracles).map Prod.snd = blk.oracles :=
    List.map_snd_zip (Nat.le_of_eq ho)
  rw [← e2, ← e1]
  exact (flatMap_id_map _ l).symm

/-- A table that is available stays available after further rounds, if the available tables are
tight (`Env.Tight`). -/
theorem Env.add_keeps {E : Env} (hE : E.Tight) (ps : List Played) {z : Fmt.TreeSource}
    {pt : Place × Table} (h : E.tree z = some pt) : (E.add ps).tree z = some pt :=
  Env.add_prefix E [] ps z pt (by rw [Env.add_nil E hE]; exact h)

/-! ## 2 The step -/

/-- **The clauses (F) and (X) after a sub-protocol.** A lemma on this folder's own functions and
definitions. It is none of the library's goals. -/
theorem made_next (T : Thread Bk S Cl V W X Pb) {n : Nat} (hfit : T.fits n = true)
    (hsh : ∀ x ∈ T.bs, x.planOk = true ∧ x.shaped = true) (b : Nat) : MadeNext T b := by
  intro blk hblk k s m E ds y cols s' hF hM hd hS
  unfold Thread.Stepped Thread.Moved at hS
  obtain ⟨⟨⟨l, hl, hy⟩, hc⟩, hstep⟩ := hS
  unfold Thread.Made at hM
  obtain ⟨hseen, hloc, hsent, hTi, s₀, c₀, hbeg, hc₀, hdec₀⟩ := hM
  obtain ⟨ei, eloc, eseen⟩ := play_mid _ _ _ _ _ hy
  have eh := play_heard _ _ _ _ _ hy
  have Y := play_yields _ _ _ _ _ hy
  have hlen := T.heard_length hF
  obtain ⟨-, hnear⟩ := T.fits_parts hfit
  have hfr : T.front ≤ m.st.heard.length := by
    rw [hlen]
    exact Nat.le_add_right _ _
  have hsl : m.seen.length = m.st.heard.length := by
    have e := congrArg List.length hseen
    rw [List.length_map] at e
    exact e
  have hfs : T.front ≤ m.seen.length := by
    rw [hsl]
    exact hfr
  have hmem : blk ∈ T.bs := List.mem_of_getElem? hblk
  have hn : l.length = blk.rounds.length := by
    have e := congrArg List.length (steps_decl hl)
    rw [List.length_map, List.flatMap_cons, List.flatMap_nil, List.append_nil] at e
    exact e
  have hdr : (roundsOf y.1).map (·.drawn) = ds := yields_drawn _ _ _ _ Y
  have hrb : (declsTo T.bs b).length = (m.st.heard.drop T.front).length := by
    rw [List.length_drop, hlen]
    unfold roundsTo
    omega
  refine ⟨?_, ?_⟩
  · -- (F)
    have hL : m.st.heard.length = (T.ahead ++ declsTo T.bs b).length := drawsFit_length _ _ hF
    unfold Thread.Fit
    rw [declsTo_succ hblk, ← List.append_assoc, eh, drawsFit_append, List.take_left' hL,
      List.drop_left' hL, Bool.and_eq_true]
    exact ⟨hF, hd⟩
  · -- (X)
    unfold Thread.Made
    refine ⟨?_, ?_, ?_, Env.add_tight hTi y.1, s₀, c₀ ++ cols, ?_, ?_, ?_⟩
    · rw [eseen, List.map_append, hseen, hdr, eh]
    · rw [eloc, hloc, eh]
      unfold Thread.locOf
      rw [List.take_append_of_le_length (Nat.le_trans hnear hfr),
        List.drop_append_of_le_length hfr, List.append_assoc]
    · show E.sent + (tablesOf y.1).length = treesTo T.bs (b + 1)
      rw [hsent, treesTo_succ hblk,
        tables_count _ _ _ _ Y (steps_shaped hl fun x hx => by
          rw [List.mem_singleton.1 hx]
          exact hsh blk hmem),
        steps_oracles hl]
    · rw [ei, eh, List.take_append_of_le_length hfr]
      exact hbeg
    · unfold Thread.colsTo at hc₀ ⊢
      have f₁ : fillCols (readsOf T.chain T.ft (E.add y.1).stored (E.add y.1).tree
          (declsTo T.bs b) (m.st.heard.drop T.front)) [] = .ok c₀ :=
        fillCols_mono (fun z pt hz => Env.add_keeps hTi y.1 hz) _ _ _ hc₀
      rw [declsTo_succ hblk, eh, List.drop_append_of_le_length hfr,
        readsOf_append _ _ _ _ _ _ _ _ hrb, fillCols_append, f₁]
      show (fillCols _ (([] : List OpenedColumn).drop _)).map _ = _
      rw [List.drop_nil, hc]
      rfl
    · have hr₂ : (roundsOf y.1).length = blk.rounds.length := by
        unfold roundsOf
        rw [List.length_map, yields_length _ _ _ _ Y, hn]
      have h1 := fold_more T.ft (roundsOf y.1) cols (T.bs.take b) s₀ s (m.seen.drop T.front) []
        c₀ [] hdec₀
      have h2 : foldBlocks T.ft (T.bs.take b) s₀ (m.seen.drop T.front ++ roundsOf y.1)
          (c₀ ++ cols) = .ok (s, roundsOf y.1, cols) := h1
      rw [take_succ_some hblk, eseen, List.drop_append_of_le_length hfs]
      exact fold_snoc (T.bs.take b) s₀ s _ _ h2 hr₂ hstep

/-- **What clause (X) gives the library's lemmas along the verifier's run**: if `start z` is the
only first state that `begun` allows (z is meant to be the public part; the statement does not
require that), the verifier's state at a border is reached in the library's own sense (`Reach`,
Johnson/Top/H0/Walk/Reach.lean), over the sub-protocols of `T.bs` as they are, not over the
library's wrapped ones (`below`). -/
theorem reach_of_made (T : Thread Bk S Cl V W X Pb) {P : Type} (start : P → S) (z : P) {b : Nat}
    {k : Coins Bk} {s : S} {m : Mid W X} {E : Env} (hb : b ≤ T.bs.length)
    (h0 : ∀ s₀, T.begun k m.st.input (m.st.heard.take T.front) s₀ → s₀ = start z)
    (hM : T.Made b k s m E) : Reach T.ft T.bs start b (z, s) := by
  unfold Thread.Made at hM
  obtain ⟨-, -, -, -, s₀, c₀, hbeg, -, hf⟩ := hM
  rw [h0 s₀ hbeg] at hf
  exact reach_of_fold b hb s _ _ _ _ hf

end ProofFile.Honest

#print axioms ProofFile.Honest.take_succ_some
#print axioms ProofFile.Honest.declsTo_succ
#print axioms ProofFile.Honest.treesTo_succ
#print axioms ProofFile.Honest.flatMap_id_map
#print axioms ProofFile.Honest.steps_oracles
#print axioms ProofFile.Honest.Env.add_keeps
#print axioms ProofFile.Honest.made_next
#print axioms ProofFile.Honest.reach_of_made
