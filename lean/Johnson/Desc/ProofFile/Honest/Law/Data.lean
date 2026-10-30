-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Data.lean: the data that `FileDescription.data`
(Johnson/Desc/BlockSlot.lean) computes from a description that passes its tests on the plan satisfy
`DataFits` (Honest/Law/StratWords.lean). That is: depth, wants and keys; and, round by round, the
declared round's items and, for each tree that the round sends, the length and width that the
sub-protocol declares for its oracle message. The main lemma is `dataFits_of_data`.

  1  `zip_items`   a declared round and its data: the items; as many trees as the entry counts roots
  2  `rows_fst`, `rows_len`, `rows_sent`, `rows_cons`, `shaped_parts`, `zip_snd_flat`, `flat_len`,
     `to_rows`   a chain's declared rounds with their declared oracle messages
  3  `fits_of_flat`   from "tree number n of the chain" to "round by round"
  4  `dataFits_of_data`   the main lemma

It uses `ofData`, `data_ok`, `writtenOf_ok`, `round_ok`, `fits_roots`
(Johnson/Desc/BlockSlotProofs.lean) and `toldShape` (Johnson/Desc/Sound/OraclesAre.lean).

Limits.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.Sound.OraclesAre
import Johnson.Desc.ProofFile.Honest.Law.DataKinds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference
open VerifiableInference.Desc
open OnBytes OnBytes.Maker
open OnBytes.Three (rdOf rdsFromL)

variable {Xi S Cl : Type}

/-! ## 1 A declared round and its data -/

theorem zip_items (all : List (ℕ × Fmt.Shape × ℕ × ℕ)) (t₁ t₂ here base first : ℕ)
    {e : List (List ByteArray × ByteArray)} {l : List Fmt.DeclaredRound} {R : Params.Rounds}
    (hw : List.Forall₂ (Written e) l R) :
    (∀ x ∈ R, x.1.items.countP (· == .root) = x.1.entry.roots) →
    ∀ L : List ℕ, L.length = R.length →
    List.Forall₂ (fun (d : RDT) (r : Fmt.DeclaredRound) =>
        d.items = r.items ∧ d.trees.length = r.entry.roots)
      ((List.zipWith (rdOf all t₁ t₂ here base first) R L).map rdtOf) l := by
  induction hw with
  | nil =>
    intro _ L _
    rw [List.zipWith_nil_left]
    exact .nil
  | @cons r x l R hd _ ih =>
    intro hf L hL
    cases L with
    | nil => cases hL
    | cons n L =>
      rw [List.zipWith_cons_cons, List.map_cons]
      have hx := hf x List.mem_cons_self
      obtain ⟨y, hy, rfl⟩ := hd
      obtain ⟨e1, e2, -⟩ := round_ok hy
      refine .cons ⟨e2, ?_⟩ (ih (fun x' hx' => hf x' (List.mem_cons_of_mem _ hx')) L
        (Nat.succ.inj hL))
      show ((List.range (y.items.countP (· == .root))).map _).length = r.entry.roots
      rw [List.length_map, List.length_range, ← e1]
      exact hx

/-! ## 2 A chain's declared rounds with their declared oracle messages -/

theorem rows_cons (b : Block S Cl) (bs : List (Block S Cl)) :
    rowsOfChain (b :: bs) = b.rounds.zip b.oracles ++ rowsOfChain bs := by
  unfold rowsOfChain
  rw [List.flatMap_cons]

theorem shaped_parts {b : Block S Cl} (h : b.shaped = true) :
    b.oracles.length = b.rounds.length ∧
      ∀ z ∈ b.rounds.zip b.oracles, z.2.length = z.1.entry.roots := by
  unfold Block.shaped at h
  rw [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  refine ⟨h.1, fun z hz => ?_⟩
  have h3 := h.2 z hz
  rw [Bool.and_eq_true, beq_iff_eq] at h3
  exact h3.1

theorem rows_fst : ∀ bs : List (Block S Cl), (∀ b ∈ bs, b.shaped = true) →
    (rowsOfChain bs).map (·.1) = bs.flatMap (·.rounds)
  | [], _ => rfl
  | b :: bs, h => by
    rw [rows_cons, List.map_append, List.flatMap_cons,
      rows_fst bs fun b' hb' => h b' (List.mem_cons_of_mem _ hb')]
    exact congrArg (· ++ _) ((map_zip_fst (fun (d : Fmt.DeclaredRound) => d) b.rounds b.oracles
      (Nat.le_of_eq (shaped_parts (h b List.mem_cons_self)).1.symm)).trans (List.map_id' _))

theorem rows_len : ∀ bs : List (Block S Cl), (∀ b ∈ bs, b.shaped = true) →
    ∀ z ∈ rowsOfChain bs, z.2.length = z.1.entry.roots := by
  intro bs h z hz
  obtain ⟨b, hb, hz'⟩ := List.mem_flatMap.1 hz
  exact (shaped_parts (h b hb)).2 z hz'

theorem zip_snd_flat {α β γ : Type} (g : β → γ) : ∀ (l : List α) (m : List (List β)),
    m.length ≤ l.length →
    ((l.zip m).flatMap (·.2)).map g = m.flatMap fun x => x.map g
  | _, [], _ => by simp
  | [], _ :: _, h => by simp at h
  | _ :: l, x :: m, h => by
    rw [List.zip_cons_cons, List.flatMap_cons, List.flatMap_cons, List.map_append,
      zip_snd_flat g l m (Nat.le_of_succ_le_succ h)]

theorem rows_sent : ∀ bs : List (Block S Cl), (∀ b ∈ bs, b.shaped = true) →
    ((rowsOfChain bs).flatMap (·.2)).map (fun o : Desc.Oracle => (o.logLength, o.words)) = sentOf bs
  | [], _ => rfl
  | b :: bs, h => by
    have e2 : sentOf (b :: bs) = (b.oracles.flatMap fun l' => l'.map fun o =>
        (o.logLength, o.words)) ++ sentOf bs := by
      unfold sentOf
      rw [List.flatMap_cons]
    rw [rows_cons, List.flatMap_append, List.map_append, e2,
      rows_sent bs fun b' hb' => h b' (List.mem_cons_of_mem _ hb'),
      zip_snd_flat _ b.rounds b.oracles (Nat.le_of_eq (shaped_parts (h b List.mem_cons_self)).1)]

/-! ## 3 From "tree number n" to "round by round" -/

theorem fits_of_flat : ∀ (ds : List RDT) (zs : List (Fmt.DeclaredRound × List Desc.Oracle)),
    List.Forall₂ (fun (d : RDT) (z : Fmt.DeclaredRound × List Desc.Oracle) =>
      d.items = z.1.items ∧ d.trees.length = z.2.length) ds zs →
    (∀ (n : ℕ) (p : ℕ × ℕ),
      ((zs.flatMap (·.2)).map fun o : Desc.Oracle => (o.logLength, o.words))[n]? = some p →
      ∃ sh, treeShT ds n = some sh ∧ sh.a = p.1 ∧ sh.W = p.2) →
    List.Forall₂ RoundFits ds zs
  | [], [], _, _ => .nil
  | [], _ :: _, h, _ => by cases h
  | _ :: _, [], h, _ => by cases h
  | d :: ds, z :: zs, h, hf => by
    obtain ⟨⟨h1, h2⟩, ht⟩ := List.forall₂_cons.1 h
    refine .cons ⟨h1, ?_⟩ (fits_of_flat ds zs ht fun n p hn => ?_)
    · apply List.ext_getElem?
      intro i
      by_cases hi : i < z.2.length
      · have hz : (z.2.map fun o : Desc.Oracle => (o.logLength, o.words))[i]? =
            some ((z.2[i]'hi).logLength, (z.2[i]'hi).words) := by
          rw [List.getElem?_map, List.getElem?_eq_getElem hi]
          rfl
        obtain ⟨sh, g1, g2, g3⟩ := hf i _ (by
          rw [List.flatMap_cons, List.map_append,
            List.getElem?_append_left (by rw [List.length_map]; exact hi)]
          exact hz)
        rw [treeShT_cons, if_pos (by rw [h2]; exact hi)] at g1
        rw [hz, List.getElem?_map, g1]
        show some (sh.a, sh.W) = _
        rw [g2, g3]
      · have hi' := Nat.le_of_not_lt hi
        rw [List.getElem?_eq_none (by rw [List.length_map, h2]; exact hi'),
          List.getElem?_eq_none (by rw [List.length_map]; exact hi')]
    · obtain ⟨sh, g1, g2, g3⟩ := hf (z.2.length + n) p (by
        rw [List.flatMap_cons, List.map_append,
          List.getElem?_append_right (by rw [List.length_map]; exact Nat.le_add_right _ _),
          List.length_map, Nat.add_sub_cancel_left]
        exact hn)
      rw [treeShT_cons, if_neg (by rw [h2]; omega), h2, Nat.add_sub_cancel_left] at g1
      exact ⟨sh, g1, g2, g3⟩

theorem flat_len : ∀ (ds : List RDT) (zs : List (Fmt.DeclaredRound × List Desc.Oracle)),
    List.Forall₂ (fun (d : RDT) (z : Fmt.DeclaredRound × List Desc.Oracle) =>
      d.items = z.1.items ∧ d.trees.length = z.2.length) ds zs →
    (zs.flatMap (·.2)).length = (ds.map (·.trees.length)).sum
  | [], [], _ => rfl
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | d :: ds, z :: zs, h => by
    obtain ⟨⟨-, h2⟩, ht⟩ := List.forall₂_cons.1 h
    rw [List.flatMap_cons, List.length_append, List.map_cons, List.sum_cons, flat_len ds zs ht, h2]

/-- From the declared rounds to `rowsOfChain`: each round with its declared oracle messages. -/
theorem to_rows {ds : List RDT} {bs : List (Block S Cl)} (hb : ∀ b ∈ bs, b.shaped = true)
    (h : List.Forall₂ (fun (d : RDT) (r : Fmt.DeclaredRound) =>
      d.items = r.items ∧ d.trees.length = r.entry.roots) ds (bs.flatMap (·.rounds))) :
    List.Forall₂ (fun (d : RDT) (z : Fmt.DeclaredRound × List Desc.Oracle) =>
      d.items = z.1.items ∧ d.trees.length = z.2.length) ds (rowsOfChain bs) := by
  rw [← rows_fst bs hb, List.forall₂_map_right_iff] at h
  have hl := rows_len bs hb
  generalize rowsOfChain bs = rows at h hl
  revert hl
  induction h with
  | nil => intro _; exact .nil
  | @cons d z ds zs h1 _ ih =>
    intro hl
    exact .cons ⟨h1.1, h1.2.trans (hl z List.mem_cons_self).symm⟩
      (ih fun z' hz' => hl z' (List.mem_cons_of_mem _ hz'))

/-! ## 4 The main lemma -/

theorem dataFits_of_data {F : FileDescription Xi} {file : String} {D : WholeD}
    (h : F.data file = .ok D) (hp : F.planOk = true) : DataFits F D := by
  obtain ⟨hwants, hkeys, -⟩ := ofData Xi F file D h
  have told := Sound.toldShape Xi F file D h (Sound.sentFit_of_planOk F hp)
  have P := (F.planOk_ok).1 hp
  have b₁ : ∀ b ∈ F.first.blocksInOrder, b.shaped = true := fun b hb => (P.blocks₁ b hb).2
  have b₂ : ∀ b ∈ F.shared.blocksInOrder, b.shaped = true := fun b hb => (P.blocks₂ b hb).2
  have b₃ : ∀ b ∈ F.second.blocksInOrder, b.shaped = true := fun b hb => (P.blocks₃ b hb).2
  obtain ⟨⟨R₁, R₂, R₃⟩, hR, hk, rfl⟩ := data_ok h
  obtain ⟨w₁, w₂, w₃⟩ := writtenOf_ok hR
  have hf : Three.Whole.fits R₁ R₂ R₃ 2 = true := (okAt_parts hk).fits
  have i₁ := to_rows b₁ (zip_items _ _ _ _ _ _ w₁ (fits_roots hf (0, R₁) (by simp)) _
    (sentBefore_length R₁) : List.Forall₂ _ ((Three.Whole.of R₁ R₂ R₃).ds₁.map rdtOf) F.roundsDeclaredByBlocks.1)
  have i₂ := to_rows b₂ (zip_items _ _ _ _ _ _ w₂ (fits_roots hf (1, R₂) (by simp)) _
    (sentBefore_length R₂) : List.Forall₂ _ ((Three.Whole.of R₁ R₂ R₃).ds₂.map rdtOf) F.roundsDeclaredByBlocks.2.1)
  have i₃ := to_rows b₃ (zip_items _ _ _ _ _ _ w₃ (fits_roots hf (2, R₃) (by simp)) _
    (sentBefore_length R₃) : List.Forall₂ _ ((Three.Whole.of R₁ R₂ R₃).ds₃.map rdtOf) F.roundsDeclaredByBlocks.2.2)
  have j₁ := forall₂_dropLast i₁
  rw [← List.map_dropLast] at j₁
  generalize hD : WholeD.of F.tableDepth (wholeAt (some (R₁, R₂, R₃))) = D at *
  have d₁ : D.ds₁ = (Three.Whole.of R₁ R₂ R₃).ds₁.dropLast.map rdtOf := by rw [← hD]; rfl
  have d₂ : D.ds₂ = (Three.Whole.of R₁ R₂ R₃).ds₂.map rdtOf := by rw [← hD]; rfl
  have d₃ : D.ds₃ = (Three.Whole.of R₁ R₂ R₃).ds₃.map rdtOf := by rw [← hD]; rfl
  replace j₁ : List.Forall₂ (fun (d : RDT) (z : Fmt.DeclaredRound × List Desc.Oracle) =>
      d.items = z.1.items ∧ d.trees.length = z.2.length) D.ds₁
      (rowsOfChain F.first.blocksInOrder).dropLast := by
    rw [d₁]
    exact j₁
  replace i₂ : List.Forall₂ (fun (d : RDT) (z : Fmt.DeclaredRound × List Desc.Oracle) =>
      d.items = z.1.items ∧ d.trees.length = z.2.length) D.ds₂
      (rowsOfChain F.shared.blocksInOrder) := by
    rw [d₂]
    exact i₂
  replace i₃ : List.Forall₂ (fun (d : RDT) (z : Fmt.DeclaredRound × List Desc.Oracle) =>
      d.items = z.1.items ∧ d.trees.length = z.2.length) D.ds₃
      (rowsOfChain F.second.blocksInOrder) := by
    rw [d₃]
    exact i₃
  have n₁ : ((rowsOfChain F.first.blocksInOrder).dropLast.flatMap (·.2)).length = D.t₁ := flat_len _ _ j₁
  have n₂ : ((rowsOfChain F.shared.blocksInOrder).flatMap (·.2)).length = D.t₂ := flat_len _ _ i₂
  refine ⟨by rw [← hD]; rfl, hwants, hkeys, fits_of_flat _ _ j₁ ?_, fits_of_flat _ _ i₂ ?_,
    fits_of_flat _ _ i₃ ?_⟩
  · intro n p hn
    have hlt : n < D.t₁ := by
      rw [← n₁, ← List.length_map (f := fun o : Desc.Oracle => (o.logLength, o.words))]
      exact (List.getElem?_eq_some_iff.1 hn).1
    have hpre : (Sound.sentAt F 0)[n]? = some p := by
      show (sentOf F.first.blocksInOrder)[n]? = some p
      rw [← rows_sent _ b₁]
      have e : rowsOfChain F.first.blocksInOrder = (rowsOfChain F.first.blocksInOrder).dropLast ++
          (rowsOfChain F.first.blocksInOrder).drop ((rowsOfChain F.first.blocksInOrder).length - 1) := by
        rw [List.dropLast_eq_take, List.take_append_drop]
      rw [e, List.flatMap_append, List.map_append, List.getElem?_append_left (by
        rw [List.length_map, n₁]
        exact hlt)]
      exact hn
    obtain ⟨sh, g1, g2, g3⟩ := told 0 n p hpre
    refine ⟨sh, ?_, g2, g3⟩
    have g1' : D.shape (0 + n) = some sh := g1
    unfold WholeD.shape at g1'
    rw [Nat.zero_add, if_pos hlt] at g1'
    exact g1'
  · intro n p hn
    have hlt : n < D.t₂ := by
      rw [← n₂, ← List.length_map (f := fun o : Desc.Oracle => (o.logLength, o.words))]
      exact (List.getElem?_eq_some_iff.1 hn).1
    have hpre : (Sound.sentAt F 1)[n]? = some p := by
      show (sentOf F.shared.blocksInOrder)[n]? = some p
      rw [← rows_sent _ b₂]
      exact hn
    obtain ⟨sh, g1, g2, g3⟩ := told 1 n p hpre
    refine ⟨sh, ?_, g2, g3⟩
    have g1' : D.shape (D.t₁ + n) = some sh := g1
    unfold WholeD.shape at g1'
    rw [if_neg (by omega), Nat.add_sub_cancel_left, if_pos hlt] at g1'
    exact g1'
  · intro n p hn
    have hpre : (Sound.sentAt F 2)[n]? = some p := by
      show (sentOf F.second.blocksInOrder)[n]? = some p
      rw [← rows_sent _ b₃]
      exact hn
    obtain ⟨sh, g1, g2, g3⟩ := told 2 n p hpre
    refine ⟨sh, ?_, g2, g3⟩
    have g1' : D.shape (D.t₁ + D.t₂ + n) = some sh := g1
    unfold WholeD.shape at g1'
    have e : D.t₁ + D.t₂ + n - D.t₁ - D.t₂ = n := by omega
    rw [if_neg (by omega), if_neg (by omega), e] at g1'
    exact g1'

end ProofFile.Honest

#print axioms ProofFile.Honest.zip_items
#print axioms ProofFile.Honest.rows_cons
#print axioms ProofFile.Honest.shaped_parts
#print axioms ProofFile.Honest.rows_fst
#print axioms ProofFile.Honest.rows_len
#print axioms ProofFile.Honest.zip_snd_flat
#print axioms ProofFile.Honest.rows_sent
#print axioms ProofFile.Honest.fits_of_flat
#print axioms ProofFile.Honest.flat_len
#print axioms ProofFile.Honest.to_rows
#print axioms ProofFile.Honest.dataFits_of_data
