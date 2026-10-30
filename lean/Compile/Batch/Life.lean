-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/Life.lean: the whole lifetime of the encodings, with batches and coalitions. Proofs on
the definitions of Compile/Batch/SpecLife.lean (words of this library: lean/GLOSSARY.md).

 Part 1  one session for a coalition J, and its simulator
 Part 2  game 1: theorem `lifetime`, by `lifetime_abstract`, `rows_law`, `Play.within_plug` of
         Compile/Life.lean
 Part 3  two lemmas; the theorem on game 2, `lifePlaced`, is not in this library.
 Part 4  companions: the placement of game 2 is a uniform injection. Not in this library: the
         statement for any adversary (the probability of an overrun is added), the one from the
         properties of the record of protocols, and, for this file's game, the bound
         n_T z_T + n_L z_L + n_req z_on (for the first encoding and its copies: `nice_pre` and
         `life_star`, Compile/Batch/LifeStar.lean)

Notation: in Compile/Batch/SpecLife.lean: `Call ι X N`: the calls; ι is the set of names of the
encodings, N the number of slots; `test e`: a session of Test on encoding e; `link e e'`: a session
of Link on the encodings e (parent) and e' (child); `bat e J xs rest`: a session of Batch on
encoding e: the adversary owns the slots J, with the requests xs; rest is what the other slots hold;
`idx`: an `ι → I`: encoding e is an encoding of the index idx e; `i₀`: an `I`; `t`: an
`Adversary L ι α`, a `Play` (Compile/Life.lean): an adversary that makes calls, as a decision tree;
`err zT zL zO`: the error of the session that a call starts: a coalition J costs |J| zO;
`load qT qpar qch qon c a`: the query complexity of the session that a call starts to encoding a;
`t.Fits w b ld` (Compile/Life.lean): a call c puts the load w c e on row e; if the rows carry the
loads ld already, then at the end no row carries more than b, whatever the answers and the coins
are; `t.cost z` (Compile/Life.lean): the sum of the costs z c of the calls on the most expensive
path, whatever the answers and the coins are; `b`, `qT`, `qpar`, `qch`, `qon`: natural numbers, the
arguments of `BatchProtocol.Reads` (Iop/Batch.lean); `real`, `ideal`, `Sims`; game 1, game 2, coalition,
placement: the head and the docstrings of Compile/Batch/SpecLife.lean.
-/
import Compile.Batch.SpecLife
import Mathlib.Logic.Equiv.Fintype

noncomputable section

namespace Compile.BatchLife

open Prob Iop Compile.Lifetime
open scoped ENNReal

/-! ## Part 1. One session -/

section Session
variable {X : Type} {E : ExtSpec} {Wt : Type} {Q : BatchInteractiveOracleProof X E} {N : ℕ}

/-- For a coalition, under `h` (the simulator's error is at most z): a session and its simulated
counterpart are within z. -/
theorem tv_bsess_le (H : BatchHonestProver Q Wt) (Sim : BSimOf Q N) (w : Wt) (x : Fin N → Option X)
    (J : Finset (Fin N)) (xs : J → X) {z : ℝ≥0∞}
    (h : prBRho {ρ | H.output w x ρ J ≠
          Sim J xs (fun j => ρ.slot j.1) (Q.extAnsJ J xs (fun j => ρ.slot j.1) (H.ext w))} ≤ z) :
    tv (bsess H w x J) (simBsess Q Sim J xs (H.ext w)) ≤ z := by
  refine (tv_bind_right_le_pr_ne _ _ _).trans (le_trans (pr_mono _ ?_) h)
  intro ρ hρ hEq
  exact hρ (congrArg
      (fun d : PMF (J → Option (DView Q.loc)) => d.map fun o => ((fun j : J => ρ.slot j.1), o)) hEq)

open Classical in
/-- The positions that the verifiers of J read. -/
def readsJ (Q : BatchInteractiveOracleProof X E) (J : Finset (Fin N)) (xs : J → X) (ρs : J → Rho Q.loc.shape) :
    Finset E.Pos :=
  Finset.univ.biUnion fun j : J => Q.loc.extReads (xs j) (ρs j)

theorem mem_readsJ {J : Finset (Fin N)} {xs : J → X} {ρs : J → Rho Q.loc.shape} {q : E.Pos} :
    q ∈ readsJ Q J xs ρs ↔ ∃ j, q ∈ Q.loc.extReads (xs j) (ρs j) := by
  simp [readsJ]

/-- Under `h` (`ReadsAtMost N q`) there are at most q positions in `readsJ`: they are among the
positions that are read in the execution in which the slots outside J are empty. -/
theorem card_readsJ_le {q : ℕ} (h : Q.ReadsAtMost N q) (J : Finset (Fin N))
    (xs : J → X) (ρ : BRho N Q.loc.shape Q.ann) :
    (readsJ Q J xs fun j => ρ.slot j.1).card ≤ q := by
  classical
  refine (Finset.card_le_card fun p hp => ?_).trans (h (vec J xs fun _ => none) ρ)
  obtain ⟨j, hj⟩ := mem_readsJ.1 hp
  unfold BatchInteractiveOracleProof.allReads
  refine Finset.mem_biUnion.2 ⟨j.1, Finset.mem_univ _, ?_⟩
  have e : vec J xs (fun _ => none) j.1 = some (xs j) := by
    unfold vec
    rw [dif_pos j.2]
  rw [e]
  exact hj

variable {P : Type}

/-- The simulated session as an algorithm that reads a table: position q of the external string is
the entry loc q. -/
def bsessR (Q : BatchInteractiveOracleProof X E) (Sim : BSimOf Q N) (J : Finset (Fin N))
    (xs : J → X) (loc : E.Pos → P) :
    Reader P (fun _ => E.Sym) (BSess Q J) :=
  .draw (BRho N Q.loc.shape Q.ann) (unif (BRho N Q.loc.shape Q.ann)) fun ρ =>
    readK loc (readsJ Q J xs fun j => ρ.slot j.1).toList (fun _ => none) fun ans =>
      .draw (J → Option (DView Q.loc)) (Sim J xs (fun j => ρ.slot j.1) ans) fun o =>
        .done (fun j => ρ.slot j.1, o)

open Classical in
theorem run_bsessR (Sim : BSimOf Q N) (J : Finset (Fin N)) (xs : J → X) (loc : E.Pos → P)
    (f : P → E.Sym) (str : E.Str) (h : ∀ q, E.rd str q = f (loc q)) :
    (bsessR Q Sim J xs loc).run f = simBsess Q Sim J xs str := by
  unfold bsessR simBsess
  rw [Reader.run_draw]
  congr 1
  funext ρ
  rw [run_readK, Reader.run_draw]
  have h1 : (fun q =>
        if q ∈ (readsJ Q J xs fun j => ρ.slot j.1).toList then some (f (loc q)) else none) =
      Q.extAnsJ J xs (fun j => ρ.slot j.1) str := by
    funext q
    unfold BatchInteractiveOracleProof.extAnsJ
    by_cases hq : ∃ j : J, q ∈ Q.loc.extReads (xs j) (ρ.slot j.1)
    · rw [if_pos (Finset.mem_toList.2 (mem_readsJ.2 hq)), if_pos hq, h]
    · rw [if_neg (fun hh => hq (mem_readsJ.1 (Finset.mem_toList.1 hh))), if_neg hq]
  rw [h1]
  rfl

/-- The simulated session reads the entries for the positions of the verifiers of J and no
others. -/
theorem within_bsessR [DecidableEq P] (Sim : BSimOf Q N) (J : Finset (Fin N)) (xs : J → X)
    (loc : E.Pos → P) {good : Finset P → Prop} (S : Finset P)
    (h : ∀ ρ : BRho N Q.loc.shape Q.ann, good (S ∪ (readsJ Q J xs fun j => ρ.slot j.1).image loc)) :
    (bsessR Q Sim J xs loc).Within good S := by
  intro ρ
  refine within_readK loc _ _ _ S fun acc' o => ?_
  have h1 : ((readsJ Q J xs fun j => ρ.slot j.1).toList.map loc).toFinset =
      (readsJ Q J xs fun j => ρ.slot j.1).image loc := by
    ext p
    simp
  show good _
  rw [h1]
  exact h ρ

end Session

/-! ### What the slots outside J hold does not reach the output for J -/

theorem vec_apply_mem {N : ℕ} {X : Type} (J : Finset (Fin N)) (xs : J → X)
    (rest : {j : Fin N // j ∉ J} → Option X) (j : J) :
    vec J xs rest j.1 = some (xs j) := by
  unfold vec
  rw [dif_pos j.2]

section Hidden
variable {X : Type} {E : ExtSpec} {Wt : Type} {Q : BatchInteractiveOracleProof X E} {N : ℕ}

open Classical in
/-- The output for J, written out: for each slot j of J, `none` if the challenges of its transcript
are in the withheld set of its request, and else the disclosed view of its transcript, which is made
from the shared coins, the coins of slot j, the request of slot j and the challenges of slot j.
`rest`, what the other slots hold, does not occur on the right. -/
theorem output_vec (H : BatchHonestProver Q Wt) (w : Wt) (J : Finset (Fin N)) (xs : J → X)
    (rest : {j : Fin N // j ∉ J} → Option X) (ρ : BRho N Q.loc.shape Q.ann) :
    H.output w (vec J xs rest) ρ J = (unif (H.Coin0 × (Fin N → H.Coin))).map fun c => fun j : J =>
      if ρ.slot j.1 ∈ H.one.withheld w (xs j) then none
      else
          some (Q.loc.dview (xs j) (H.ext w)
                ((H.one.strat w (xs j) (c.1, c.2 j)).run (ρ.slot j.1)).1) := by
  unfold BatchHonestProver.output
  refine congrArg (fun f => (unif (H.Coin0 × (Fin N → H.Coin))).map f)
    (funext fun c => funext fun j => ?_)
  rw [vec_apply_mem]

/-- A slot outside J can change nothing in the output for J: neither a disclosed view, nor whether a
slot of J is withheld. -/
theorem output_vec_congr (H : BatchHonestProver Q Wt) (w : Wt) (J : Finset (Fin N)) (xs : J → X)
    (rest rest' : {j : Fin N // j ∉ J} → Option X) (ρ : BRho N Q.loc.shape Q.ann) :
    H.output w (vec J xs rest) ρ J = H.output w (vec J xs rest') ρ J := by
  rw [output_vec, output_vec]

/-- The session, as the owner of J sees it, does not depend on what the other slots hold. So the
experiment may run every batch with the other slots empty. -/
theorem bsess_vec_congr (H : BatchHonestProver Q Wt) (w : Wt) (J : Finset (Fin N)) (xs : J → X)
    (rest rest' : {j : Fin N // j ∉ J} → Option X) :
    bsess H w (vec J xs rest) J = bsess H w (vec J xs rest') J := by
  unfold bsess
  exact congrArg _ (funext fun ρ => by rw [output_vec_congr H w J xs rest rest' ρ])

end Hidden

/-! ## Part 2. Game 1 -/

section Game
variable {I X ι : Type}

/-- The hiding properties of the record of protocols say that there are good simulators. -/
theorem exists_sims {L : BatchProtocol I X} {Ryes : I → X → Prop}
    {zT zL zO : ℝ≥0∞} (h : L.Hiding Ryes zT zL zO) :
    ∃ Sm : Sims L, Sm.Good Ryes zT zL zO := by
  obtain ⟨sT, hT⟩ := h.hidT
  obtain ⟨sL, hL⟩ := h.hidL
  obtain ⟨sB, hB⟩ := h.hidB
  exact ⟨⟨sT, sL, sB⟩, fun w x => hT w x trivial, fun w x => hL w x trivial, hB⟩

/-- Simulated sessions as algorithms that read the table whose row e is the string number e. -/
def simR (L : BatchProtocol I X) (Sm : Sims L) :
    ∀ c : Call ι X L.maxBatchSize, Reader (ι × Fin L.wordLength) (fun _ => L.Symbol) (Ans L c)
  | .test e => sessR L.offline Sm.T () fun p => (e, p)
  | .link e e' => sessR L.link Sm.Lk () (Sum.elim (fun p => (e, p)) fun p => (e', p))
  | .bat e J xs _ => bsessR L.onlineBatch Sm.B J xs fun p => (e, p)

theorem run_simR (L : BatchProtocol I X) (Sm : Sims L) (Ps : ι → Fin L.wordLength → L.Symbol) (c : Call ι X L.maxBatchSize) :
    (simR L Sm c).run (fun p => Ps p.1 p.2) = simO L Sm Ps c := by
  cases c with
  | test e => exact run_sessR L.offline Sm.T () _ _ (Ps e) fun _ => rfl
  | link e e' => exact run_sessR L.link Sm.Lk () _ _ (Ps e, Ps e') fun q => by cases q <;> rfl
  | bat e J xs rest => exact run_bsessR Sm.B J xs _ _ (Ps e) fun _ => rfl

variable [DecidableEq ι]

theorem card_filter_const_le {Qp : Type} (T : Finset Qp) (e a : ι) {q : ℕ} (h : T.card ≤ q) :
    (T.filter fun _ => e = a).card ≤ if a = e then q else 0 := by
  by_cases hae : a = e
  · rw [if_pos hae]
    exact (Finset.card_filter_le _ _).trans h
  · rw [if_neg hae, Finset.filter_false_of_mem fun _ _ hh => hae hh.symm]
    simp

/-- Under `L.Reads`, each simulated session keeps to its load. -/
theorem adds_simR {L : BatchProtocol I X} {b qT qpar qch qon : ℕ} (hR : L.Reads b qT qpar qch qon)
    (Sm : Sims L) (c : Call ι X L.maxBatchSize) :
    Adds (simR L Sm c) (load qT qpar qch qon c) := by
  intro S
  cases c with
  | test e =>
    exact within_sessR L.offline Sm.T () _ S fun ρ a => (rowCard_union_image_le S _ _ a).trans
      (Nat.add_le_add_left (card_filter_const_le _ e a (hR.cntT () ρ)) _)
  | bat e J xs rest =>
    exact within_bsessR Sm.B J xs _ S fun ρ a => (rowCard_union_image_le S _ _ a).trans
      (Nat.add_le_add_left (card_filter_const_le _ e a (card_readsJ_le hR.cntB J xs ρ)) _)
  | link e e' =>
    refine within_sessR L.link Sm.Lk () _ S fun ρ a => (rowCard_union_image_le S _ _ a).trans
      (Nat.add_le_add_left ?_ _)
    have hsub : ((L.link.extReads () ρ).filter fun q =>
          ((Sum.elim (fun p => (e, p)) fun p => (e', p) : Fin L.wordLength ⊕ Fin L.wordLength → ι × Fin L.wordLength) q).1 = a)
        ⊆ (((L.link.extReads () ρ).filter fun p => p.isLeft).filter fun _ => e = a)
          ∪ (((L.link.extReads () ρ).filter fun p => p.isRight).filter fun _ => e' = a) := by
      intro q hq
      obtain ⟨hq1, hq2⟩ := Finset.mem_filter.1 hq
      cases q with
      | inl p =>
        exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hq1, rfl⟩, hq2⟩)
      | inr p =>
        exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hq1, rfl⟩, hq2⟩)
    exact (Finset.card_le_card hsub).trans
      ((Finset.card_union_le _ _).trans
        (Nat.add_le_add (card_filter_const_le _ e a (hR.cntLp () ρ))
          (card_filter_const_le _ e' a (hR.cntLc () ρ))))

theorem vec_of_mem {N : ℕ} (J : Finset (Fin N)) (xs : J → X)
    (rest : {j : Fin N // j ∉ J} → Option X) (j : J) :
    vec J xs rest j.1 = some (xs j) := by
  unfold vec
  rw [dif_pos j.2]

theorem valid_vec {N : ℕ} {ok : X → Prop} (J : Finset (Fin N))
    (xs : J → X) (rest : {j : Fin N // j ∉ J} → Option X)
    (h1 : ∀ j, ok (xs j)) (h2 : ∀ j x, rest j = some x → ok x) :
    ∀ j xj, vec J xs rest j = some xj → ok xj := by
  intro j xj h
  unfold vec at h
  by_cases hj : j ∈ J
  · rw [dif_pos hj] at h
    exact Option.some.inj h ▸ h1 ⟨j, hj⟩
  · rw [dif_neg hj] at h
    exact h2 ⟨j, hj⟩ xj h

variable [Fintype ι]

/-- The whole lifetime of the encodings, with batches and coalitions, for an adversary within the
budget (`Fits`) whose calls are allowed (`Allowed`); further hypotheses below.
(the conclusion: `tv (real L idx t) (ideal L Sm i₀ t) ≤ t.cost (err zT zL zO)`) -/
theorem lifetime {L : BatchProtocol I X} {Ryes : I → X → Prop} {b qT qpar qch qon : ℕ} {zT zL zO : ℝ≥0∞}
    (hW : L.Wired) (hR : L.Reads b qT qpar qch qon) {Sm : Sims L} (hS : Sm.Good Ryes zT zL zO)
    (idx : ι → I) (i₀ : I) {α : Type} (t : Adversary L ι α) (hok : t.Calls (Allowed Ryes idx))
    (hfit : t.Fits (load qT qpar qch qon) b fun _ => 0) :
    tv (real L idx t) (ideal L Sm i₀ t) ≤ t.cost (err zT zL zO) := by
  have h := lifetime_abstract (unif (ι → L.EncodingRandomness))
    (fun r => fun p : ι × Fin L.wordLength => L.encodeIndex (idx p.1) (r p.1) p.2)
    ((unif (ι → L.EncodingRandomness)).map fun r => fun p : ι × Fin L.wordLength => L.encodeIndex i₀ (r p.1) p.2) (realO L idx)
    (simR L Sm) (Allowed Ryes idx) (err zT zL zO) (fun T => ∀ e, rowCard T e ≤ b) ?_ ?_ t hok ?_
  · rw [PMF.bind_map] at h
    have e1 : ∀ r : ι → L.EncodingRandomness,
        (t.run fun c => (simR L Sm c).run fun p : ι × Fin L.wordLength => L.encodeIndex i₀ (r p.1) p.2) =
          t.run (simO L Sm fun e => L.encodeIndex i₀ (r e)) := fun r =>
      congrArg t.run (funext fun c => run_simR L Sm (fun e => L.encodeIndex i₀ (r e)) c)
    unfold real ideal
    simp only [← e1]
    exact h
  · intro r c hc
    rw [run_simR L Sm (fun e => L.encodeIndex (idx e) (r e)) c]
    cases c with
    | test e =>
      have h1 := tv_sess_le L.honestOfflineProver Sm.T (idx e, r e) () (hS.goodT (idx e, r e) ())
      rwa [hW.extT] at h1
    | link e e' =>
      have h1 := tv_sess_le L.honestLinkProver Sm.Lk (idx e, r e, r e') () (hS.goodL (idx e, r e, r e') ())
      have hc' : idx e = idx e' := hc
      rw [hW.extL] at h1
      show tv _ (simSess L.link Sm.Lk () (L.encodeIndex (idx e) (r e), L.encodeIndex (idx e') (r e'))) ≤ _
      rw [← hc']
      exact h1
    | bat e J xs rest =>
      have h1 := tv_bsess_le L.honestOnlineBatchProver Sm.B (idx e, r e) (vec J xs rest) J xs
        (hS.goodB (idx e, r e) (vec J xs rest) (valid_vec J xs rest hc.1 hc.2)
          J xs (vec_of_mem J xs rest))
      rwa [hW.extB] at h1
  · exact fun S hSb =>
      rows_law (fun e r => L.encodeIndex (idx e) r) (fun _ r => L.encodeIndex i₀ r) b
        (fun e T hT => hR.hidE T hT (idx e) i₀) S hSb
  · exact Play.within_plug (adds_simR hR Sm) t (fun _ => 0) ∅ (fun e => by rw [rowCard_empty]) hfit

end Game

/-! ## Part 3. Two lemmas for game 2 -/

section Placed
variable {I X Pr ι : Type} (L : BatchProtocol I X) (ans : I → Pr → Option X) (idx : ι → I)

variable {α : Type}

theorem filterMap_id_map (f : Pr → Option X) (l : List Pr) :
    (l.map f).filterMap id = l.filterMap f := by
  rw [List.filterMap_map]
  rfl


theorem card_slotsOf_le {N : ℕ} (σ : Equiv.Perm (Fin N)) (k : ℕ) : (slotsOf σ k).card ≤ k := by
  have h := Finset.card_le_card_of_injOn (s := slotsOf σ k) (t := Finset.range k)
    (fun j => (σ.symm j).val)
    (fun j hj => Finset.mem_coe.2 (Finset.mem_range.2 (Finset.mem_filter.1 hj).2))
    (fun a _ b _ hab => σ.symm.injective (Fin.ext hab))
  rwa [Finset.card_range] at h

variable {L ans idx}


end Placed

/-! ## Part 4. Companions -/

/-! ### The placement of game 2 is a uniform injection -/

/-- Any injection of k places into the N slots can be carried to any other by a permutation of the
slots. -/
theorem exists_perm_comp {N k : ℕ} (f g : Fin k → Fin N)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    ∃ τ : Equiv.Perm (Fin N), ∀ a, τ (f a) = g a := by
  classical
  let e : {x // x ∈ Set.range f} ≃ {x // x ∈ Set.range g} :=
    (Equiv.ofInjective f hf).symm.trans (Equiv.ofInjective g hg)
  refine ⟨e.extendSubtype, fun a => ?_⟩
  rw [Equiv.extendSubtype_apply_of_mem e (f a) ⟨a, rfl⟩]
  show ((Equiv.ofInjective g hg) ((Equiv.ofInjective f hf).symm ⟨f a, a, rfl⟩)).1 = g a
  rw [Equiv.ofInjective_symm_apply]
  rfl

/-- The restriction of a uniform permutation of the slots to the first k places is a uniform
injection: all injections have the same probability. -/
theorem pr_placement_eq {N k : ℕ} (hk : k ≤ N) (f g : Fin k → Fin N)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    pr (unif (Equiv.Perm (Fin N))) {σ | ∀ a : Fin k, σ (Fin.castLE hk a) = f a} =
      pr (unif (Equiv.Perm (Fin N))) {σ | ∀ a : Fin k, σ (Fin.castLE hk a) = g a} := by
  obtain ⟨τ, hτ⟩ := exists_perm_comp f g hf hg
  have h1 : {σ : Equiv.Perm (Fin N) | ∀ a : Fin k, σ (Fin.castLE hk a) = f a}
      = (Equiv.mulLeft τ) ⁻¹' {σ | ∀ a : Fin k, σ (Fin.castLE hk a) = g a} := by
    ext σ
    constructor
    · intro h a
      show τ (σ (Fin.castLE hk a)) = g a
      rw [h a, hτ]
    · intro h a
      have h2 : τ (σ (Fin.castLE hk a)) = g a := h a
      rw [← hτ a] at h2
      exact τ.injective h2
  rw [h1, ← pr_map, map_unif_equiv]

end Compile.BatchLife
