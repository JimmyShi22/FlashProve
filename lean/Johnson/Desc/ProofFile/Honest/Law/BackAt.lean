-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/BackAt.lean: `BackAt` (Honest/Law/Rule/OneSim.lean) holds at a
file whose plan passes its tests and whose data fit the description (`backAt_of`). `BackAt` says: at
a pair at which `Tied` holds, at a verifier's message that passes `Draws.due` and is not in
`withheld`, at a run of `runC` that has returned, the library's disclosed view of the transcript
that the two strategies of `honestBatchProverOfFile` (Honest/StratC.lean) write is the function `back`
(Honest/Law/Rule/Back.lean) of the value of `pubJ`, what the run has produced, the instance, the
message and the external answers. The proof goes by the three hypotheses of `back_eq` on that
transcript: its challenges are the verifier's message; its plain parts are those of the transcript
computed from what was produced; and so are its symbols at the protocol's own reads.

What this is. A conditional lemma about this folder's own strategies: an equation between two values
of the library's type of disclosed views, pointwise. Its conclusion is a definition of ours, meant
as a hypothesis of other lemmas. It is none of the library's goals.

  1  `want_src`   a `Want` of a tree at a verifier's message: the chain that sent the tree, the
     tree's number there, a read
  2  `allTabs_len`, `src_bound`   a tree that a run reads is one that was sent
  3  `backAt_of`   the main lemma

Limits.
  * Where `runC` does not return, at a pair at which `Tied` does not hold, at a message that does
    not pass `Draws.due`, and inside `withheld`, nothing is said.
  * Nothing is said of a position that the protocol does not read.
  * Hypotheses that the prose above does not name: `Draws.due` (the challenges are such as the
    description's rounds can draw; the first chain's last challenge is the empty one): `want_src`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.BackFile

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc
open OnBytes.Maker (RDT WholeD Want uLT chainsOf drawnT posAtST ownPosOf wants₁ wants₂ wants₃
  wantsOf)
open _root_.Run.PQ (CK SgX)

variable {Xi W₀ Rc Ky Tr X₀ X Sd TF TJ T3 R2 R3 : Type}

/-! ## 1 A `Want` of a tree -/

section
variable (C : CK) (D : WholeD) (tF : TF) (tJ : TJ) (t3 : T3) (F : FileDescription Xi)

/-- A `Want` of a tree's leaf, at a verifier's message: the chain c that sent the tree, its number n
there, and a read of the declared rounds at that tree and that position. -/
theorem want_src (hD : DataFits F D) (ρ : Iop.Rho (chainsOf C D tF tJ t3).sh)
    (hdue : (drawsAt C D tF tJ t3 ρ).due F = true) (j k : Nat)
    (h : Want.tree j k ∈ wants₁ C D tF tJ t3 ρ ++
      (wants₂ C D tF tJ t3 ρ ++ wants₃ C D tF tJ t3 ρ)) :
    ∃ c n, ∃ q ∈ allBare F (drawsAt C D tF tJ t3 ρ), q.src = some (c, n) ∧ q.pos = k ∧
      j = (if c = 0 then 0 else if c = 1 then F.t₁ else F.t₁ + F.t₂) + n := by
  unfold allBare bareReads
  rcases List.mem_append.1 h with g | g
  · have g' : Want.tree j k ∈ wantsOf D.a D.depth D.ds₁
        (drawnT C D.ds₁ ((chainsOf C D tF tJ t3).rho₁ ρ)) := g
    rw [hD.wants.1] at g'
    obtain ⟨rd, -, o, -, ej, q, hq, e1, e2⟩ := want_tree (numAt F.t₁ F.t₂ 0) 0 0
      (fun _ _ => none) (fun _ => none) _ _ j k g'
    exact ⟨(srcOf 0 o.2).1, (srcOf 0 o.2).2, q, List.mem_append_left _ (List.mem_append_left _ (by
      rw [(first_reads C D tF tJ t3 F ρ hdue _ _).1]
      exact hq)), e1,
      e2, by rw [ej, numAt_src]⟩
  · rcases List.mem_append.1 g with g | g
    · have g' : Want.tree j k ∈ wantsOf D.a D.depth D.ds₂
          (drawnT C D.ds₂ ((chainsOf C D tF tJ t3).rho₂ ρ)) := g
      rw [hD.wants.2.1] at g'
      obtain ⟨rd, -, o, -, ej, q, hq, e1, e2⟩ := want_tree (numAt F.t₁ F.t₂ 1) 1 0
        (fun _ _ => none) (fun _ => none) _ _ j k g'
      exact ⟨(srcOf 1 o.2).1, (srcOf 1 o.2).2, q,
        List.mem_append_left _ (List.mem_append_right _ hq), e1,
        e2, by rw [ej, numAt_src]⟩
    · have g' : Want.tree j k ∈ wantsOf D.a D.depth D.ds₃
          (drawnT C D.ds₃ ((chainsOf C D tF tJ t3).rho₃ ρ)) := g
      rw [hD.wants.2.2] at g'
      obtain ⟨rd, -, o, -, ej, q, hq, e1, e2⟩ := want_tree (numAt F.t₁ F.t₂ 2) 2 F.lastChainFirstTreeNumber
        (fun _ _ => none) (fun _ => none) _ _ j k g'
      exact ⟨(srcOf 2 o.2).1, (srcOf 2 o.2).2, q, List.mem_append_right _ hq, e1,
        e2, by rw [ej, numAt_src]⟩

end

/-! ## 2 A tree that a run reads is one that was sent -/

theorem allTabs_len (l : List Played) : (allTabs l).length = (l.map (·.tables.length)).sum := by
  unfold allTabs
  rw [List.length_flatMap]

/-- A read of the declared rounds at a tree: at a run for which `RunOk` holds, that tree is among
the tables that its chain has produced. -/
theorem src_bound {F : FileDescription Xi} {δ : Draws} {stored : Nat → Nat → Option (List UInt64)}
    {l₀ l₁ l₂ : List Played} {q₀ q₁ q₂ : List Read} (h : RunOk F δ stored l₀ l₁ l₂ q₀ q₁ q₂)
    {q : Read} (hq : q ∈ allBare F δ) {c n : Nat} (hs : q.src = some (c, n)) :
    c ≤ 2 ∧ n < (allTabs (pick3 l₀ l₁ l₂ c)).length := by
  rw [← h.bare] at hq
  obtain ⟨q', hq', rfl⟩ := List.mem_map.1 hq
  have hs' : q'.src = some (c, n) := hs
  obtain ⟨-, hw⟩ := h.words q' hq'
  rcases hw with ⟨i, -, e, -⟩ | ⟨c', j', T, -, e, hc, ht, -⟩
  · rw [hs'] at e
    cases e
  · rw [hs'] at e
    cases e
    refine ⟨hc, ?_⟩
    cases hg : (allTabs (pick3 l₀ l₁ l₂ c))[n]? with
    | none =>
      rw [hg] at ht
      cases ht
    | some _ => exact (List.getElem?_eq_some_iff.1 hg).1

/-! ## 3 The main lemma -/

section
variable {C : CK} {D : WholeD} {tF : TF} {tJ : TJ} {t3 : T3} {F : FileDescription Xi}
  {silent : Xi → TF → TJ → T3 → Bool} {Bk : ProverCoinCounts} [Fintype R2] [Nonempty R2] [Fintype R3]
  [Inhabited R3] {H : Prover W₀ Rc Xi Ky Tr X₀ X} {G : Sides F Bk W₀ Rc Ky Tr X₀ X}
  {J : R2 → R3 → KeyAndJoiningRoundMessages W₀ Rc Sd Xi Ky TF TJ T3} {sh : Ky → F.S₂}
  {ext : W₀ × Rc × Sd → (Iop.oneExternalString (2 ^ D.a) SgX).Str} {pubJ : R2 → R3 → Xi → TF × TJ × T3}
  {Rel : W₀ → Rc → Xi → Prop}

/-- **`BackAt` holds**, if the plan passes its tests and the data fit the description. -/
theorem backAt_of (hp : F.planOk = true) (hD : DataFits F D) :
    BackAt C D tF tJ t3 F silent Bk H G J sh ext pubJ Rel := by
  intro w x hv ρ hdue _ c r hr
  obtain ⟨mF, mJ, m3, p1, p2, p3, ⟨n1, n2, n3⟩, ⟨z1, z2, z3⟩, e1, e2, s1, s2⟩ :=
    laid_at_stratC C D tF tJ t3 F Bk (G.prover H) (J c.1.2 default) (J c.1.2 c.2.2) sh w c.1.1 x
      c.2.1 ρ hr hp hD (hv.key _ _) (hv.key _ _) hv.start.symm
  have hRO := (runOk_of hr).1
  have hL := laid_is r.run hRO
  have hse := hv.seam c.1.2 c.2.2
  have hτ : (((honestBatchProverOfFile C D tF tJ t3 F silent Bk (G.prover H) J sh ext).one.strat w x c).run ρ).1 =
      trAtC C D tF tJ t3 F Bk (G.prover H) (J c.1.2 default) (J c.1.2 c.2.2) sh w c.1.1 x c.2.1
        ρ := rfl
  rw [hτ, hL]
  refine back_eq C D tF tJ t3 F silent _ _ x ρ (ext w) _ (Iop.Strat.rho_run _ ρ) ?_ ?_
  · refine plains_of_parts (chainsOf C D tF tJ t3) _ _ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [mF, whole_F, ← hse]
    · rw [p1, whole_1]
      exact laid_plains C 0 _ D.ds₁ _ 0 _ n1
    · rw [mJ, whole_J, ← hse]
    · rw [p2, whole_2]
      exact laid_plains C 1 _ D.ds₂ _ 0 _ n2
    · rw [m3, whole_3', ← hse]
    · rw [p3, whole_3]
      exact laid_plains C 2 _ D.ds₃ _ 0 _ n3
  · refine fun (p : Iop.OPos (chainsOf C D tF tJ t3).sh) hp' => ?_
    have hp'' : p ∈ ((wants₁ C D tF tJ t3 ρ ++ (wants₂ C D tF tJ t3 ρ ++
        wants₃ C D tF tJ t3 ρ)).filterMap (ownPosOf C D tF tJ t3)).toFinset := hp'
    obtain ⟨wt, hw, hpos⟩ := List.mem_filterMap.1 (List.mem_toFinset.1 hp'')
    cases wt with
    | table i k => cases hpos
    | tree j k =>
      obtain ⟨cc, n, q, hq, hs, hk, hj⟩ := want_src C D tF tJ t3 F hD ρ hdue j k hw
      obtain ⟨hc, hb⟩ := src_bound hRO hq hs
      have hin := mem_treeAsks F _ q hq cc n hs
      rw [hk] at hin
      rw [allTabs_len] at hb
      obtain rfl | rfl | rfl : cc = 0 ∨ cc = 1 ∨ cc = 2 := by omega
      · have hj' : j = 0 + n := hj
        have hb' : n < (r.run.played.1.map (·.tables.length)).sum := hb
        rw [hj', Nat.zero_add, own_pos₁ C D tF tJ t3 n k (by rw [← s1]; exact hb')] at hpos
        obtain ⟨q₀, hq₀, rfl⟩ := Option.map_eq_some_iff.1 hpos
        rw [OnBytes.Maker.read_i₁, p1, whole_1]
        exact laid_read C 0 _ D.ds₁ _ 0 _ n1 z1 n k q₀ hq₀ (by rw [Nat.zero_add]; exact hin)
      · have hj' : j = F.t₁ + n := hj
        have hb' : n < (r.run.played.2.1.map (·.tables.length)).sum := hb
        rw [hj', e1, own_pos₂ C D tF tJ t3 n k (by rw [← s2]; exact hb')] at hpos
        obtain ⟨q₀, hq₀, rfl⟩ := Option.map_eq_some_iff.1 hpos
        rw [OnBytes.Maker.read_i₂, p2, whole_2]
        exact laid_read C 1 _ D.ds₂ _ 0 _ n2 z2 n k q₀ hq₀ (by rw [Nat.zero_add]; exact hin)
      · have hj' : j = F.t₁ + F.t₂ + n := hj
        rw [hj', e1, e2, own_pos₃ C D tF tJ t3 n k] at hpos
        obtain ⟨q₀, hq₀, rfl⟩ := Option.map_eq_some_iff.1 hpos
        rw [OnBytes.Maker.read_i₃, p3, whole_3]
        exact laid_read C 2 _ D.ds₃ _ 0 _ n3 z3 n k q₀ hq₀ (by rw [Nat.zero_add]; exact hin)

end

end ProofFile.Honest

#print axioms ProofFile.Honest.want_src
#print axioms ProofFile.Honest.allTabs_len
#print axioms ProofFile.Honest.src_bound
#print axioms ProofFile.Honest.backAt_of
