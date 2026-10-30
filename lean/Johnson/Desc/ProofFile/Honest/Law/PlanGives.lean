-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/PlanGives.lean: what the plan declares, from the description's own
tests. `PlanServes` (Honest/Law/RunsFile.lean), the structure of hypotheses of `runC_returns` on the
rounds that `ready` has prepared, follows from the tests on the plan (`FileDescription.planOk`), one
executable test on the prover's sides (`rootedAll`: a prover's side is defined at every sub-protocol
that sends a root) and one condition on its stored columns. This is the lemma `planServes`.

  1  `mem_zipIdx_of`, `root_lt`, `sum_take_le`, `orcs_length`   on lists; on `BookPlan.roundOfRoot`
  2  `rooted`, `rootedAll`, `steps_noRoot`   a round without a move declares no root
  3  `inTime_plan`, `chain_inTime`, `no_taken`   no tree is opened before it is sent
     (`BookPlan.inTime`, Johnson/Desc/BookPlan.lean), and each is opened with the width with which
     it is declared (`opened_fits`, Honest/Law/StratCols.lean)
  4  `planServes`   the lemma

Limits.
  * The condition on the stored columns (`hst`: at every position below the depth a column is
    available, with the declared width) is a hypothesis: whoever fills `Prover.stored` has to prove
    it (see Honest/Committer.lean).
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.RunsFile
import Johnson.Desc.ProofFile.Honest.Law.RunMid
import Johnson.Desc.ProofFile.Honest.Law.StratRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {S Cl Xi V W Y W₀ Rc Ky Tr X₀ X : Type}

/-! ## 1 On lists -/

theorem mem_zipIdx_of {α : Type} : ∀ (l : List α) (k r : Nat) (a : α), l[r]? = some a →
    (a, k + r) ∈ l.zipIdx k
  | [], _, _, _, h => by simp at h
  | x :: l, k, 0, a, h => by
    have e : x = a := by simpa using h
    rw [List.zipIdx_cons, e]
    exact List.mem_cons_self
  | x :: l, k, r + 1, a, h => by
    rw [List.zipIdx_cons]
    have h' : l[r]? = some a := by simpa using h
    have ih := mem_zipIdx_of l (k + 1) r a h'
    have e : k + 1 + r = k + (r + 1) := by omega
    rw [e] at ih
    exact List.mem_cons_of_mem _ ih

/-- The root number `n` is among those that the rounds up to and including its sending round count.
-/
theorem root_lt : ∀ (zs : List Fmt.DeclaredRound) (n i : Nat), BookPlan.roundOfRoot zs n = some i →
    n < ((zs.take (i + 1)).map (·.entry.roots)).sum
  | [], _, _, h => by simp [BookPlan.roundOfRoot] at h
  | d :: zs, n, i, h => by
    unfold BookPlan.roundOfRoot at h
    by_cases hlt : n < d.entry.roots
    · rw [if_pos hlt] at h
      cases h
      rw [List.take_succ_cons, List.map_cons, List.sum_cons]
      omega
    · rw [if_neg hlt] at h
      obtain ⟨i', hi', rfl⟩ := Option.map_eq_some_iff.1 h
      have ih := root_lt zs _ i' hi'
      rw [List.take_succ_cons, List.map_cons, List.sum_cons]
      omega

theorem sum_take_le : ∀ (l : List Nat) (a b : Nat), a ≤ b → (l.take a).sum ≤ (l.take b).sum
  | [], _, _, _ => by simp
  | _ :: _, 0, _, _ => Nat.zero_le _
  | _ :: _, _ + 1, 0, h => absurd h (Nat.not_succ_le_zero _)
  | x :: l, a + 1, b + 1, h => by
    rw [List.take_succ_cons, List.take_succ_cons, List.sum_cons, List.sum_cons]
    exact Nat.add_le_add_left (sum_take_le l a b (Nat.le_of_succ_le_succ h)) _

theorem orcs_length : ∀ l : List (Step W Y), (∀ s ∈ l, s.oracles.length = s.decl.entry.roots) →
    (l.flatMap (·.oracles)).length = ((l.map (·.decl)).map (·.entry.roots)).sum
  | [], _ => rfl
  | s :: l, h => by
    rw [List.flatMap_cons, List.length_append, List.map_cons, List.map_cons, List.sum_cons,
      h s List.mem_cons_self, orcs_length l fun s' hs' => h s' (List.mem_cons_of_mem _ hs')]

/-! ## 2 A round without a move declares no root -/

/-- A prover's side is defined at every sub-protocol one of whose rounds sends a root: an executable
test. -/
def rooted (bs : List (Block S Cl)) (hs : List (Placed V W Y)) : Bool :=
  bs.all fun b => (hs.any fun h => h.place == b.place) || b.rounds.all fun d => d.entry.roots == 0

def rootedAll (F : FileDescription Xi) (H : Prover W₀ Rc Xi Ky Tr X₀ X) : Bool :=
  rooted F.first.blocksInOrder H.first && rooted F.shared.blocksInOrder H.shared && rooted F.second.blocksInOrder H.second

theorem steps_noRoot {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
    {v : Option V} {bs : List (Block S Cl)} {hs : List (Placed V W Y)} {ss : List (Step W Y)}
    (h : chainSteps B rows look v bs hs = .ok ss) (h4 : rooted bs hs = true) :
    ∀ s ∈ ss, s.move.isSome = false → s.decl.entry.roots = 0 := by
  intro s hs' hm
  obtain ⟨-, h2⟩ := chainSteps_rows bs hs ss h
  have h1 : (s.decl, s.oracles, s.addr.place, s.move.isSome) ∈
      ss.map (fun s => (s.decl, s.oracles, s.addr.place, s.move.isSome)) :=
    List.mem_map.2 ⟨s, hs', rfl⟩
  rw [h2] at h1
  obtain ⟨b, hb, hz⟩ := List.mem_flatMap.1 h1
  obtain ⟨z, hz', e⟩ := List.mem_map.1 hz
  have e1 : z.1 = s.decl := congrArg (·.1) e
  have e2 : (hs.any fun h => h.place == b.place) = s.move.isSome := congrArg (·.2.2.2) e
  have hb4 := List.all_eq_true.1 h4 b hb
  rcases Bool.or_eq_true_iff.1 hb4 with h5 | h5
  · rw [h5, hm] at e2
    cases e2
  · rw [← e1]
    exact beq_iff_eq.1 (List.all_eq_true.1 h5 z.1 (List.of_mem_zip (a := z.1) (b := z.2) hz').1)

/-! ## 3 In time, and with the declared width -/

theorem inTime_plan {F : FileDescription Xi} (hp : F.planOk = true) :
    BookPlan.inTime F.roundsDeclaredByBlocks F.roots = true := by
  have hb := ((F.planOk_ok).1 hp).book
  unfold FileDescription.treeSharingOk BookPlan.allClausesHold at hb
  exact List.all_eq_true.1 hb ("inTime", BookPlan.inTime F.roundsDeclaredByBlocks F.roots)
    (by simp [BookPlan.clauses])

section
variable {F : FileDescription Xi} {B : ProverCoinCounts} {rows : List (Addr × Due)} {look : Addr → (d : Due) × Cs d}
  {v : Option V} {bs : List (Block S Cl)} {hs : List (Placed V W Y)} {ss : List (Step W Y)}

/-- One chain. `i`: its number, from 0. -/
theorem chain_inTime (hp : F.planOk = true) (h : chainSteps B rows look v bs hs = .ok ss) {i : Nat}
    (hi : (bs.flatMap (·.rounds), i) ∈ [(F.roundsDeclaredByBlocks.1, 0), (F.roundsDeclaredByBlocks.2.1, 1), (F.roundsDeclaredByBlocks.2.2, 2)])
    (hj : (sentOf bs, i) ∈
      [(sentOf F.first.blocksInOrder, 0), (sentOf F.shared.blocksInOrder, 1), (sentOf F.second.blocksInOrder, 2)])
    (hsh : ∀ s ∈ ss, s.oracles.length = s.decl.entry.roots) : InTime ss := by
  intro r s hr o ho n hn
  have hd := steps_decl h
  have hT := inTime_plan hp
  unfold BookPlan.inTime at hT
  have h1 := List.all_eq_true.1 hT (bs.flatMap (·.rounds), i) hi
  have hr' : (bs.flatMap (·.rounds))[r]? = some s.decl := by
    rw [← hd, List.getElem?_map, hr]
    rfl
  have h2 := List.all_eq_true.1 h1 (s.decl, r) (by
    have e := mem_zipIdx_of _ 0 r s.decl hr'
    rw [Nat.zero_add] at e
    exact e)
  have h3 := List.all_eq_true.1 h2 o ho
  rw [hn] at h3
  have h3' : ((BookPlan.roundOfRoot (bs.flatMap (·.rounds)) n).any fun j =>
      decide (j + (if BookPlan.holdsSampled F.roots i n then 1 else 0) ≤ r)) = true := h3
  cases hj1 : BookPlan.roundOfRoot (bs.flatMap (·.rounds)) n with
  | none =>
    rw [hj1] at h3'
    cases h3'
  | some j =>
  rw [hj1] at h3'
  have hj2 : j + (if BookPlan.holdsSampled F.roots i n then 1 else 0) ≤ r := of_decide_eq_true h3'
  have hjr : j ≤ r := Nat.le_trans (Nat.le_add_right _ _) hj2
  have hlt := root_lt _ n j hj1
  have hle := sum_take_le ((bs.flatMap (·.rounds)).map (·.entry.roots)) (j + 1) (r + 1)
    (Nat.succ_le_succ hjr)
  rw [← List.map_take, ← List.map_take] at hle
  have hcount : ((ss.take (r + 1)).flatMap (·.oracles)).length =
      (((bs.flatMap (·.rounds)).take (r + 1)).map (·.entry.roots)).sum := by
    rw [orcs_length _ fun s' hs' => hsh s' (List.mem_of_mem_take hs'), List.map_take, hd]
  have hn' : n < ((ss.take (r + 1)).flatMap (·.oracles)).length := by
    rw [hcount]
    omega
  refine ⟨((ss.take (r + 1)).flatMap (·.oracles))[n], List.getElem?_eq_getElem hn', ?_⟩
  have hall : (ss.flatMap (·.oracles))[n]? = some ((ss.take (r + 1)).flatMap (·.oracles))[n] := by
    have e : ss = ss.take (r + 1) ++ ss.drop (r + 1) := (List.take_append_drop _ _).symm
    conv_lhs => rw [e]
    rw [List.flatMap_append, List.getElem?_append_left hn']
    exact List.getElem?_eq_getElem hn'
  have hsent := steps_sent h
  have hf := opened_fits hp hi (List.mem_of_getElem? hr') ho hj (by rw [hn]; rfl)
  rw [hn] at hf
  have hf' : (sentOf bs)[n]? = some (o.1.a, o.1.W) := hf
  rw [← hsent, List.getElem?_map, hall] at hf'
  exact (Prod.mk.inj (Option.some.inj hf')).2

/-- The first two chains take over nothing. -/
theorem no_taken (hp : F.planOk = true) (h : chainSteps B rows look v bs hs = .ok ss) {i : Nat}
    (hi : (bs.flatMap (·.rounds), i) ∈ [(F.roundsDeclaredByBlocks.1, 0), (F.roundsDeclaredByBlocks.2.1, 1), (F.roundsDeclaredByBlocks.2.2, 2)])
    (h2 : i ≠ 2) : ∀ u ∈ ss, ∀ o ∈ u.decl.opens, ∀ ch j, o.2 ≠ .taken ch j := by
  intro u hu o ho ch j e
  have hd := steps_decl h
  have hT := inTime_plan hp
  unfold BookPlan.inTime at hT
  have h1 := List.all_eq_true.1 hT (bs.flatMap (·.rounds), i) hi
  obtain ⟨r, hr⟩ := List.mem_iff_getElem?.1 hu
  have hr' : (bs.flatMap (·.rounds))[r]? = some u.decl := by
    rw [← hd, List.getElem?_map, hr]
    rfl
  have h3 := List.all_eq_true.1 (List.all_eq_true.1 h1 (u.decl, r) (by
    have e' := mem_zipIdx_of _ 0 r u.decl hr'
    rw [Nat.zero_add] at e'
    exact e')) o ho
  rw [e] at h3
  have h4 : (i == 2 && decide (ch < 2) && (BookPlan.roundOfRoot
      (([F.roundsDeclaredByBlocks.1, F.roundsDeclaredByBlocks.2.1, F.roundsDeclaredByBlocks.2.2][ch]?).getD []) j).isSome) = true := h3
  rw [Bool.and_eq_true, Bool.and_eq_true] at h4
  exact h2 (beq_iff_eq.1 h4.1.1)

end

/-! ## 4 The lemma -/

/-- **What the plan declares, from the description's own tests.** -/
theorem planServes {F : FileDescription Xi} {B : ProverCoinCounts} {H : Prover W₀ Rc Xi Ky Tr X₀ X} {w₀ : W₀} {rc : Rc}
    {x : Xi} {c : Coins B} {R : Ready W₀ Rc Xi Ky Tr X₀ X}
    (hR : ready F B H w₀ rc x c = .ok R) (hp : F.planOk = true) (hr : rootedAll F H = true)
    (hst : ∀ d ∈ F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2, ∀ t ∈ d.stored, ∀ y, y < 2 ^ t.sh.a →
      ∃ u, H.storedWords w₀ rc t.item y = some u ∧ u.length = t.sh.W) :
    PlanServes H w₀ rc R := by
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  have P := (F.planOk_ok).1 hp
  simp only [rootedAll, Bool.and_eq_true] at hr
  obtain ⟨⟨r1, r2⟩, r3⟩ := hr
  have o1 := steps_shaped s1 P.blocks₁
  have o2 := steps_shaped s2 P.blocks₂
  have o3 := steps_shaped s3 P.blocks₃
  have m1 : ∀ u ∈ R.first, u.decl ∈ F.roundsDeclaredByBlocks.1 := fun u hu => by
    show u.decl ∈ F.first.blocksInOrder.flatMap (·.rounds)
    rw [← steps_decl s1]
    exact List.mem_map.2 ⟨u, hu, rfl⟩
  have m2 : ∀ u ∈ R.shared, u.decl ∈ F.roundsDeclaredByBlocks.2.1 := fun u hu => by
    show u.decl ∈ F.shared.blocksInOrder.flatMap (·.rounds)
    rw [← steps_decl s2]
    exact List.mem_map.2 ⟨u, hu, rfl⟩
  have m3 : ∀ u ∈ R.second, u.decl ∈ F.roundsDeclaredByBlocks.2.2 := fun u hu => by
    show u.decl ∈ F.second.blocksInOrder.flatMap (·.rounds)
    rw [← steps_decl s3]
    exact List.mem_map.2 ⟨u, hu, rfl⟩
  refine ⟨⟨o1, steps_noRoot s1 r1, steps_part0 _ _ s1,
      chain_inTime hp s1 (i := 0) (by simp [FileDescription.roundsDeclaredByBlocks]) (by simp) o1,
      fun u hu => hst _ (List.mem_append_left _ (List.mem_append_left _ (m1 u hu)))⟩,
    ⟨o2, steps_noRoot s2 r2, steps_part0 _ _ s2,
      chain_inTime hp s2 (i := 1) (by simp [FileDescription.roundsDeclaredByBlocks]) (by simp) o2,
      fun u hu => hst _ (List.mem_append_left _ (List.mem_append_right _ (m2 u hu)))⟩,
    ⟨o3, steps_noRoot s3 r3, steps_part0 _ _ s3,
      chain_inTime hp s3 (i := 2) (by simp [FileDescription.roundsDeclaredByBlocks]) (by simp) o3,
      fun u hu => hst _ (List.mem_append_right _ (m3 u hu))⟩,
    no_taken hp s1 (i := 0) (by simp [FileDescription.roundsDeclaredByBlocks]) (by decide),
    no_taken hp s2 (i := 1) (by simp [FileDescription.roundsDeclaredByBlocks]) (by decide), ?_⟩
  intro u hu o ho ch j e
  have hT := inTime_plan hp
  unfold BookPlan.inTime at hT
  have h1 := List.all_eq_true.1 hT (F.roundsDeclaredByBlocks.2.2, 2) (by simp [List.zipIdx])
  obtain ⟨r, hr'⟩ := List.mem_iff_getElem?.1 (m3 u hu)
  have h3 := List.all_eq_true.1 (List.all_eq_true.1 h1 (u.decl, r) (by
    have e' := mem_zipIdx_of _ 0 r u.decl hr'
    rw [Nat.zero_add] at e'
    exact e')) o ho
  rw [e] at h3
  have h4 : ((2 : Nat) == 2 && decide (ch < 2) && (BookPlan.roundOfRoot
      (([F.roundsDeclaredByBlocks.1, F.roundsDeclaredByBlocks.2.1, F.roundsDeclaredByBlocks.2.2][ch]?).getD []) j).isSome) = true := h3
  rw [Bool.and_eq_true, Bool.and_eq_true] at h4
  have hch : ch < 2 := of_decide_eq_true h4.1.2
  have hcases : ch = 0 ∨ ch = 1 := by omega
  rcases hcases with rfl | rfl
  · left
    refine ⟨rfl, ?_⟩
    have hf := opened_fits hp (i := 2) (l := F.roundsDeclaredByBlocks.2.2) (by simp) (m3 u hu) ho (j := 0)
      (L := sentOf F.first.blocksInOrder) (by simp) (by rw [e]; rfl)
    rw [e] at hf
    have hf' : (sentOf F.first.blocksInOrder)[j]? = some (o.1.a, o.1.W) := hf
    rw [← steps_sent s1, List.getElem?_map] at hf'
    obtain ⟨orc, g1, g2⟩ := Option.map_eq_some_iff.1 hf'
    exact ⟨orc, g1, (Prod.mk.inj g2).2⟩
  · right
    refine ⟨rfl, ?_⟩
    have hf := opened_fits hp (i := 2) (l := F.roundsDeclaredByBlocks.2.2) (by simp) (m3 u hu) ho (j := 1)
      (L := sentOf F.shared.blocksInOrder) (by simp) (by rw [e]; rfl)
    rw [e] at hf
    have hf' : (sentOf F.shared.blocksInOrder)[j]? = some (o.1.a, o.1.W) := hf
    rw [← steps_sent s2, List.getElem?_map] at hf'
    obtain ⟨orc, g1, g2⟩ := Option.map_eq_some_iff.1 hf'
    exact ⟨orc, g1, (Prod.mk.inj g2).2⟩

end ProofFile.Honest

#print axioms ProofFile.Honest.mem_zipIdx_of
#print axioms ProofFile.Honest.root_lt
#print axioms ProofFile.Honest.sum_take_le
#print axioms ProofFile.Honest.orcs_length
#print axioms ProofFile.Honest.steps_noRoot
#print axioms ProofFile.Honest.inTime_plan
#print axioms ProofFile.Honest.chain_inTime
#print axioms ProofFile.Honest.no_taken
#print axioms ProofFile.Honest.planServes
