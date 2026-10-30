-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/FrontRoad/ThinProver.lean: the proofs of the seven statements of
Johnson/FrontRoad/ThinProverSpec.lean. A CONTROL: NOT THE HONEST PROVER: at a written book, written
rows and a prover that has the twenty-five pinned halves of the smallness test and no other half,
all premises of Spec.sessionStops_of_cellsOwn, at mats := matsOf Zp.p.X, hold together, under the
four public premises and ReadsAs.
Terms of this folder: Johnson/FrontRoad/Spec.lean.

What this file has (namespace OnBytes.FrontRoad).
  On the halves   k8PlaceAt_inj, mem_thinFirst, find_in, thin_find: the twenty-five places are
      pairwise distinct; what a member of thinFirst is; the first half of thinFirst at k8PlaceAt l
      is the one made at l.
  On lists   filter_key_len, one_of_nodup: in a list of pairs whose keys are pairwise distinct, each
      key stands once. due_mono, due_mem: a sum of counts is at least each of them. lookup_one: a
      look-up in a list of pairs made of members. not_not_true: a small fact on Bool.
  On the description   planOk_laid, len_of_shaped, no_mask_of_round, k8_member_at, k8_in_front,
      k8_rounds: under LaidAt (the last three under scope and the reading of the files too) the
      plan's tests pass, so the places are in order and every member is shaped; at each of the
      twenty-five places a member of the first chain stands, it has one round, and it declares no
      mask word.
  On the book and on ready   masks_ok, thinBook_word_of: the book's own tests pass at thinBook.
      lookup_key, chain_ok, lend_quiet: when chainSteps and lendRow return. twice_of_nodup,
      nodup_in, nodup_thin, tests_ok, ready_ok_of: when readyTests and ready return. thinP_first,
      thinP_shared, thinP_second: provG's halves at the thin rows.
  The seven proofs   thin_halves, thin_no_frame, thin_meets_four, thinBook_word, thin_ready,
      premises_met_together, sessionStops_at_thin.

Whose text is whose. Beside what the docstrings of filter_key_len, twice_of_nodup, len_of_shaped,
chain_ok and ready_ok_of say: the four lemmas on when readyTests, lendRow, chainSteps and ready
return (tests_ok, lend_quiet, chain_ok, ready_ok_of) walk the same definitions as cut_some,
chainSteps_any and ready_any (Johnson/Desc/ProofFile/Honest/Law/ReadyAny.lean), and their proofs go
much as those do: chain_ok's as the goal's side of chainSteps_any. find_in and thin_find have the
form and the plan of find_stored (Johnson/Desc/ProofFile/Honest/Law/Rule/Faith.lean); lookup_key and
lookup_one those of lookup_cols (Johnson/Desc/ProofFile/Honest/Law/BackChain.lean). Fainter
likenesses to that folder's lemmas are not listed.

All limits: the head of Johnson/FrontRoad/ThinProverSpec.lean. Not one of the release's goal
statements.
-/
import Johnson.FrontRoad.ThinProverSpec
import Johnson.FrontRoad.CarryThrough
import Johnson.Desc.ProofFile.Honest.Law.Rule.Tests

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped ENNReal

namespace OnBytes.FrontRoad
open AtPublicFiles.AtFiles AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed
open OnBytes (TableKey)
open OnBytes.Flat (RecFull)
open OnBytes.Params (Lines missedInTheChecks clog2)
open OnBytes.Maker (WholeD)
open OnBytes.Model.Verify (publicOf)
open OnBytes.HonestTrace (Tr cellsC matsOf cellsSmall_cellOf ServesAt theTrace meetsAll_theTrace
  servesAt_iff_in_scope TraceHinge)
open Inst.Model (Instance ppref)
open VerifiableInference.Desc (Block Place KindName)
open VerifiableInference.Desc.First.K8 (Par)
open ProofFile.Honest (Prover ProverCoinCounts Sides Ready Coins ready Placed Local Common Cells Addr Due Cs)
open ProofFile.Honest.K8 (smallStop windowShare)
open ProofFile.Honest.K9 (quietStop)
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles readFiles)
open FlashProve (protocolDataWellFormed)
open P5J

/- The library's default table of scales (Inst.Model.Scl.ref) is switched off within this namespace,
so that no statement uses it silently. A statement that reads such a table names it. -/
attribute [-instance] Inst.Model.Scl.ref

/- Among all that this file imports, the search for this instance runs out of its budget. It is a
proposition, so whichever proof is found, the statements below are the same. -/
local instance (priority := high) nonemptyPadZ_thinProver : Nonempty PadZ :=
  pads_nonempty OnBytes.Slice.frS 402653181

/- The same of this one. -/
local instance (priority := high) nonemptyOfInhabited_thinProver {α : Type} [Inhabited α] :
    Nonempty α := ⟨default⟩

/-! ## On the halves -/

theorem k8PlaceAt_inj {l l' : ℕ} (h : k8PlaceAt l = k8PlaceAt l') : l = l' :=
  Option.some.inj (congrArg (fun a : Place => a.link) h)

section
variable {W₀ Rc Xi Tr' X : Type} (Zp : ProofFile.Pub) (cells : Tr' → Cells)

/-- What a member of thinFirst is. -/
theorem mem_thinFirst {g : Placed (Local W₀ Rc Xi Tr') (Local W₀ Rc Xi Tr') X}
    (hg : g ∈ thinFirst Zp cells) :
    ∃ l P, l < 25 ∧ parOwn Zp (matsOf Zp.p.X) (k8PlaceAt l) = some P ∧
      g = ⟨k8PlaceAt l, [quietStop (smallStop cells P) (windowShare P.1)]⟩ := by
  unfold thinFirst at hg
  obtain ⟨l, hl, e⟩ := List.mem_filterMap.1 hg
  obtain ⟨P, hP, rfl⟩ := Option.map_eq_some_iff.1 e
  exact ⟨l, P, List.mem_range.1 hl, hP, rfl⟩

/-- Among halves made number by number, each at the written place of its number, the first half at
the place of l is the one made at l. -/
theorem find_in (f : ℕ → Option (Placed (Local W₀ Rc Xi Tr') (Local W₀ Rc Xi Tr') X))
    (hf : ∀ l g, f l = some g → g.place = k8PlaceAt l) (l : ℕ)
    (g : Placed (Local W₀ Rc Xi Tr') (Local W₀ Rc Xi Tr') X) (hg : f l = some g) :
    ∀ ls : List ℕ, l ∈ ls →
    ((ls.filterMap f).find? fun h => h.place == k8PlaceAt l) = some g
  | [], h => by cases h
  | l' :: ls, h => by
    by_cases e : l' = l
    · subst e
      rw [List.filterMap_cons_some hg, List.find?_cons_of_pos]
      rw [hf _ _ hg]
      exact beq_self_eq_true _
    · have hl : l ∈ ls := (List.mem_cons.1 h).resolve_left (Ne.symm e)
      cases hc : f l' with
      | none =>
        rw [List.filterMap_cons_none hc]
        exact find_in f hf l g hg ls hl
      | some g' =>
        rw [List.filterMap_cons_some hc, List.find?_cons_of_neg]
        · exact find_in f hf l g hg ls hl
        · rw [hf _ _ hc]
          intro hh
          exact e (k8PlaceAt_inj (by simpa using hh))

/-- The first half of thinFirst at k8PlaceAt l is the one made at l. -/
theorem thin_find {l : ℕ} (hl : l < 25) {P : Par × List (ℕ × String × ℕ)}
    (hP : parOwn Zp (matsOf Zp.p.X) (k8PlaceAt l) = some P) :
    ((thinFirst Zp cells : List (Placed (Local W₀ Rc Xi Tr') (Local W₀ Rc Xi Tr') X)).find?
        fun h => h.place == k8PlaceAt l) =
      some ⟨k8PlaceAt l, [quietStop (smallStop cells P) (windowShare P.1)]⟩ := by
  unfold thinFirst
  refine find_in _ (fun l' g h => ?_) l _ (by rw [hP]; rfl) _ (List.mem_range.2 hl)
  obtain ⟨P', -, rfl⟩ := Option.map_eq_some_iff.1 h
  rfl

end

theorem thin_no_frame : Spec.thin_no_frame := by
  intro W₀ Rc Xi Tr' X Zp cells g hg
  obtain ⟨l, P, -, -, rfl⟩ := mem_thinFirst Zp cells hg
  rfl

theorem thin_halves : Spec.thin_halves := by
  intro Z Zp Np cF scope pp hr D r L W₀ Rc Xi Tr' X cells
  refine (halves_first_iff Z Zp Np cF scope hr L cells _).2 ⟨fun l hl => ?_, ?_⟩
  · obtain ⟨G₀, Xl, -, -, hP, -⟩ := matsOf_fits Z Zp Np cF scope hr L l hl
    exact ⟨_, _, hP, thin_find Zp cells hl hP, rfl⟩
  · intro b hb g hg
    have hk : (b.place.kind != KindName.K8) = true := (List.mem_filter.1 hb).2
    have hp : g.place = b.place := by simpa using List.find?_some hg
    have hK := thin_no_frame Zp cells g (List.mem_of_find?_eq_some hg)
    rw [hp] at hK
    rw [hK] at hk
    cases hk

theorem thin_meets_four : Spec.thin_meets_four := by
  intro Z Zp Np cF scope pp hr D r L Rc' Tr' X₀ Xh H₀ cells' e hE H'
  refine ⟨fun g hg => ?_, thin_halves Z Zp Np cF scope hr L cells', fun b _ g hg => ?_,
    model_traceCells Zp.p.X cells' e hE⟩
  · rw [thin_no_frame Zp cells' g hg]
    decide
  · cases hg

/-! ## On lists -/

section
variable {α β : Type} [DecidableEq α]

/-- How often a key stands in a list of pairs. The statement is that of count_place
(Johnson/Desc/ProofFile/Honest/Law/Rule/FileOkOf.lean) at a pair's first part, its two sides
exchanged, and the proof goes as that of count_place there, line by line. -/
theorem filter_key_len : ∀ (l : List (α × β)) (a : α),
    (l.filter fun q => q.1 == a).length = (l.map (·.1)).count a
  | [], _ => rfl
  | q :: l, a => by
    rw [List.map_cons, List.count_cons, ← filter_key_len l a]
    by_cases e : (q.1 == a) = true
    · rw [List.filter_cons_of_pos (p := fun q : α × β => q.1 == a) e, if_pos e]
      rfl
    · rw [List.filter_cons_of_neg (p := fun q : α × β => q.1 == a) e, if_neg e]
      rfl

/-- Where the keys are pairwise distinct, each stands once. -/
theorem one_of_nodup {l : List (α × β)} (hn : (l.map (·.1)).Nodup) {r : α × β} (hr : r ∈ l) :
    (l.filter fun q => q.1 == r.1).length = 1 := by
  rw [filter_key_len]
  exact List.count_eq_one_of_mem hn (List.mem_map_of_mem hr)

end

/-- A sum of counts does not fall. -/
theorem due_mono : ∀ (l : List (Addr × Due)) (acc : Due),
    acc.f ≤ (l.foldl (fun n r => Due.plus n r.2) acc).f
  | [], _ => le_rfl
  | r :: l, acc => by
    rw [List.foldl_cons]
    exact le_trans (Nat.le_add_right _ _) (due_mono l (Due.plus acc r.2))

/-- It is at least each of the counts. -/
theorem due_mem : ∀ (l : List (Addr × Due)) (acc : Due) (r : Addr × Due), r ∈ l →
    r.2.f ≤ (l.foldl (fun n r => Due.plus n r.2) acc).f
  | q :: l, acc, r, h => by
    rw [List.foldl_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact le_trans (Nat.le_add_left _ _) (due_mono l (Due.plus acc r.2))
    · exact due_mem l _ r h

section
variable {S Cl : Type}

/-- A look-up among pairs made of members: where a member stands at the place and every member there
yields v, the look-up yields v. -/
theorem lookup_one {γ : Type} (f : Block S Cl → γ) (a : Place) (v : γ) : ∀ bs : List (Block S Cl),
    (∃ b ∈ bs, b.place = a) → (∀ b ∈ bs, b.place = a → f b = v) →
    (bs.map fun b => (b.place, f b)).lookup a = some v
  | [], h, _ => by
    obtain ⟨b, hb, -⟩ := h
    cases hb
  | b :: bs, h, hv => by
    rw [List.map_cons, List.lookup_cons]
    by_cases e : b.place = a
    · rw [e, beq_self_eq_true]
      exact congrArg some (hv b List.mem_cons_self e)
    · have e' : (a == b.place) = false := by
        rw [beq_eq_false_iff_ne]
        exact fun h => e h.symm
      rw [e']
      refine lookup_one f a v bs ?_ fun b' hb' => hv b' (List.mem_cons_of_mem _ hb')
      obtain ⟨b', hb', he⟩ := h
      rcases List.mem_cons.1 hb' with rfl | hb'
      · exact absurd he e
      · exact ⟨b', hb', he⟩

/-- A shaped member's lists of oracle messages and of rounds have one length. It is the first
conjunct of shaped_parts (Johnson/Desc/ProofFile/Honest/Law/Data.lean), with that lemma's binders;
the three lines of the proof go as those of shape_of
(Johnson/Desc/ProofFile/Honest/Law/Rule/FileOkOf.lean). -/
theorem len_of_shaped {b : Block S Cl} (h : b.shaped = true) :
    b.oracles.length = b.rounds.length := by
  unfold VerifiableInference.Desc.Block.shaped at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

/-- A shaped member whose one round is the smallness test's declares no mask word. -/
theorem no_mask_of_round {b : Block S Cl} (h : b.shaped = true) {P : Par}
    (hr : b.rounds = [VerifiableInference.Desc.First.K8.round P]) : ProofFile.Honest.maskWords b = 0 := by
  obtain ⟨o, ho⟩ : ∃ o, b.oracles = [o] :=
    List.length_eq_one_iff.1 (by rw [len_of_shaped h, hr]; rfl)
  unfold VerifiableInference.Desc.Block.shaped at h
  rw [hr, ho] at h
  simp only [List.zip_cons_cons, List.zip_nil_right, List.all_cons, List.all_nil, Bool.and_true,
    Bool.and_eq_true, beq_iff_eq] at h
  have ho' : o = [] := List.length_eq_zero_iff.1 (h.2.1.trans rfl)
  unfold ProofFile.Honest.maskWords
  rw [ho, ho']
  rfl

/-- The book's rows for a chain have at each member's place at least the member's mask words. -/
theorem masks_ok (bs : List (Block S Cl)) :
    ProofFile.Honest.masksOk bs
      (bs.map fun b => ((⟨b.place, 0⟩ : Addr), (⟨ProofFile.Honest.maskWords b, 0⟩ : Due))) = true := by
  unfold ProofFile.Honest.masksOk
  rw [List.all_eq_true]
  intro b hb
  rw [decide_eq_true_eq]
  refine le_trans ?_ (Nat.le_add_right _ _)
  unfold ProofFile.Honest.placeDue
  exact due_mem _ _ ((⟨b.place, 0⟩ : Addr), (⟨ProofFile.Honest.maskWords b, 0⟩ : Due))
    (List.mem_filter.2 ⟨List.mem_map_of_mem hb, beq_self_eq_true _⟩)

end

theorem not_not_true {s : String} {e : Bool} (h : e = true) : ¬ (!(s, e).2) = true := by
  simp [h]

/-- **The book's own tests pass at thinBook**, at a description whose places are in order, at
pairwise distinct places of ks at each of which a member of the first chain stands, with one round.
-/
theorem thinBook_word_of {Xi : Type} (F : VerifiableInference.Desc.FileDescription Xi) (ks : List Place)
    (hp : F.placesOk = true) (hn : ks.Nodup) (hk : ∀ a ∈ ks, ∃ b ∈ F.first.blocksInOrder, b.place = a)
    (h1 : ∀ b ∈ F.first.blocksInOrder, b.place ∈ ks → b.rounds.length = 1) :
    (thinBook F ks).word F = none := by
  have hO := ProofFile.Honest.orderOf_nodup hp
  have hrows : (((thinBook F ks).first ++ (thinBook F ks).shared ++ (thinBook F ks).second).map
      (·.1)).Nodup := by
    have e : ((thinBook F ks).first ++ (thinBook F ks).shared ++ (thinBook F ks).second).map (·.1) =
        (ProofFile.Honest.orderOf F).map fun a => (⟨a, 0⟩ : Addr) := by
      simp [thinBook, ProofFile.Honest.orderOf, List.map_append, List.map_map, Function.comp_def]
    rw [e]
    exact hO.map fun a a' h => congrArg (fun x : Addr => x.place) h
  have hcuts : ((thinBook F ks).cuts.map (·.1)).Nodup := by
    have e : (thinBook F ks).cuts.map (·.1) = ks := by
      simp [thinBook, List.map_map, Function.comp_def]
    rw [e]
    exact hn
  unfold ProofFile.Honest.ProverCoinCounts.word
  rw [Option.map_eq_none_iff, List.find?_eq_none]
  intro x hx
  simp only [ProofFile.Honest.ProverCoinCounts.clauses, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · refine not_not_true ?_
    simp only [Bool.and_eq_true, List.all_eq_true]
    refine ⟨⟨fun r hr => ?_, fun r hr => ?_⟩, fun r hr => ?_⟩ <;>
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hr
      exact List.elem_eq_true_of_mem (List.mem_map_of_mem hb)
  · refine not_not_true ?_
    rw [List.all_eq_true]
    intro r hr
    rw [beq_iff_eq]
    exact one_of_nodup hrows hr
  · refine not_not_true ?_
    simp only [Bool.and_eq_true]
    exact ⟨⟨masks_ok _, masks_ok _⟩, masks_ok _⟩
  · exact not_not_true rfl
  · exact not_not_true rfl
  · exact not_not_true rfl
  · exact not_not_true rfl
  · exact not_not_true rfl
  · exact not_not_true rfl
  · refine not_not_true ?_
    rw [List.all_eq_true]
    intro c hc
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hc
    simp only [Bool.and_eq_true, beq_iff_eq]
    refine ⟨⟨?_, rfl⟩, one_of_nodup hcuts hc⟩
    rw [List.append_assoc, List.lookup_append,
      lookup_one (fun b => b.rounds.length) a 1 F.first.blocksInOrder (hk a ha)
        fun b hb e => h1 b hb (e ▸ ha)]
    rfl
  · exact not_not_true rfl

/-! ## On chainSteps and lendRow -/

section
variable {κ γ δ : Type} [DecidableEq κ]

/-- A look-up among pairs made of the members of a list: where a member has the key and every member
with the key yields v, the look-up yields v. -/
theorem lookup_key (key : δ → κ) (f : δ → γ) (a : κ) (v : γ) : ∀ bs : List δ,
    (∃ b ∈ bs, key b = a) → (∀ b ∈ bs, key b = a → f b = v) →
    (bs.map fun b => (key b, f b)).lookup a = some v
  | [], h, _ => by
    obtain ⟨b, hb, -⟩ := h
    cases hb
  | b :: bs, h, hv => by
    rw [List.map_cons, List.lookup_cons]
    by_cases e : key b = a
    · rw [e, beq_self_eq_true]
      exact congrArg some (hv b List.mem_cons_self e)
    · have e' : (a == key b) = false := by
        rw [beq_eq_false_iff_ne]
        exact fun h => e h.symm
      rw [e']
      refine lookup_key key f a v bs ?_ fun b' hb' => hv b' (List.mem_cons_of_mem _ hb')
      obtain ⟨b', hb', he⟩ := h
      rcases List.mem_cons.1 hb' with rfl | hb'
      · exact absurd he e
      · exact ⟨b', hb', he⟩

end

section
variable {S Cl V W X : Type}

/-- **chainSteps returns** where every member's lists of oracle messages and of rounds have one
length and, at each member at whose place a half stands, the five tests on that half pass. A
converse, over the whole list, of chainSteps_cons_ok
(Johnson/Desc/ProofFile/Honest/Law/Rule/Member.lean), which tells at one member what a return of
chainSteps gives; of our five tests that lemma tells three. -/
theorem chain_ok (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (v : Option V) (hs : List (Placed V W X)) : ∀ bs : List (Block S Cl),
    (∀ b ∈ bs, b.oracles.length = b.rounds.length ∧
      ∀ h, (hs.find? fun h => h.place == b.place) = some h →
        h.rounds = b.rounds.length ∧
        B.cuts.lookup b.place = some (h.parts.map (·.moves.length)) ∧
        (rows.any fun r => r.1.place == b.place && decide (h.parts.length ≤ r.1.part)) = false ∧
        (B.ahead.any fun e =>
          e.spender.place == b.place && decide (h.parts.length ≤ e.spender.part)) = false ∧
        ∃ c, ProofFile.Honest.lendRow B rows look b.place h.parts 0 = .ok c) →
    ∃ l, ProofFile.Honest.chainSteps B rows look v bs hs = .ok l
  | [], _ => ⟨[], rfl⟩
  | b :: bs, H => by
    obtain ⟨l, hl⟩ := chain_ok B rows look v hs bs fun b' hb' => H b' (List.mem_cons_of_mem _ hb')
    obtain ⟨h0, hh⟩ := H b List.mem_cons_self
    rw [ProofFile.Honest.chainSteps, if_neg (by simp [h0])]
    cases hf : hs.find? fun h => h.place == b.place with
    | none =>
      simp only [hl]
      exact ⟨_, rfl⟩
    | some h =>
      obtain ⟨a1, a2, a3, a4, c, hc⟩ := hh h hf
      simp only
      rw [if_neg (by simp [a1]), if_neg (by simp [a2]), if_neg (by simp [a3]),
        if_neg (by simp [a4]), hc, hl]
      exact ⟨_, rfl⟩

/-- lendRow returns at the one quiet part with a private abort test, where the book has no entry and
no coin for it. -/
theorem lend_quiet (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (a : Place) (h : V → List Fmt.Drawn → List Fmt.Drawn → Option String) (sh : ProofFile.Honest.Odds)
    (hA : B.ahead = []) (hd : ProofFile.Honest.dueAt rows ⟨a, 0⟩ = ⟨0, 0⟩) :
    ∃ c, ProofFile.Honest.lendRow B rows look a [(quietStop h sh : ProofFile.Honest.Part V W X)] 0 = .ok c := by
  have hcut : ∃ o, (look ⟨a, 0⟩).2.cut ⟨0, 0⟩ ⟨0, 0⟩ = some o := by
    unfold ProofFile.Honest.Cs.cut
    rw [dif_pos ⟨Nat.zero_le _, Nat.zero_le _⟩]
    exact ⟨_, rfl⟩
  obtain ⟨o, ho⟩ := hcut
  have hp : ∃ c, ProofFile.Honest.lendPart B rows look ⟨a, 0⟩ (quietStop h sh : ProofFile.Honest.Part V W X) =
      .ok c := by
    unfold ProofFile.Honest.lendPart
    split
    · rename_i h1
      have h2 : ((⟨0, 0⟩ : Due) != ProofFile.Honest.dueAt rows ⟨a, 0⟩) = true := h1
      rw [hd] at h2
      cases h2
    · split
      · rename_i h3
        have h4 : (look ⟨a, 0⟩).2.cut ⟨0, 0⟩ ⟨0, 0⟩ = none := h3
        rw [ho] at h4
        cases h4
      · rw [hA]
        exact ⟨_, rfl⟩
  obtain ⟨c, hc⟩ := hp
  rw [ProofFile.Honest.lendRow, hc]
  exact ⟨_, rfl⟩

end

/-- **ready returns** where readyTests does, the trace function answers, and chainSteps returns at
each of the three chains. A converse of ready_ok (Johnson/Desc/ProofFile/Honest/Law/Run.lean): its
five premises are that lemma's conjuncts on readyTests, on the trace and on the three chains, each
chain's list under an «∃». The proof's last lines go as the end of that of ready_any
(Johnson/Desc/ProofFile/Honest/Law/ReadyAny.lean). -/
theorem ready_ok_of {W₀ Rc Xi Ky Tr' X₀ X : Type} (F : VerifiableInference.Desc.FileDescription Xi)
    (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr' X₀ X) (w : W₀) (rc : Rc) (x : Xi) (c : Coins B)
    (hT : ProofFile.Honest.readyTests F B H w = .ok ()) {tr : Tr'} (htr : H.trace w x = some tr)
    (c1 : ∃ l, ProofFile.Honest.chainSteps B (B.rowsOf 0) (c.look 0)
      (ProofFile.Honest.Face.own.sees (⟨w, rc, x, tr⟩ : Local W₀ Rc Xi Tr')) F.first.blocksInOrder H.first = .ok l)
    (c2 : ∃ l, ProofFile.Honest.chainSteps B (B.rowsOf 1) (ProofFile.Honest.sharedLook B c.shared)
      (ProofFile.Honest.Face.shared.sees (⟨w, rc, H.key x⟩ : Common W₀ Rc Ky)) F.shared.blocksInOrder H.shared =
        .ok l)
    (c3 : ∃ l, ProofFile.Honest.chainSteps B (B.rowsOf 2) (c.look 2)
      (ProofFile.Honest.Face.own.sees (⟨w, rc, x, tr⟩ : Local W₀ Rc Xi Tr')) F.second.blocksInOrder H.second =
        .ok l) :
    ∃ R, ready F B H w rc x c = .ok R := by
  obtain ⟨l1, h1⟩ := c1
  obtain ⟨l2, h2⟩ := c2
  obtain ⟨l3, h3⟩ := c3
  refine ⟨⟨⟨w, rc, x, tr⟩, ⟨w, rc, H.key x⟩, l1, l2, l3⟩, ?_⟩
  unfold ProofFile.Honest.ready ProofFile.Honest.sharedSteps
  rw [hT, htr]
  simp only [h1, h2, h3]
  rfl

/-! ## On the description -/

section
variable (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
  (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl)

/-- Under LaidAt the tests on the plan pass at the description. -/
theorem planOk_laid {D : WholeD} {r : LPFD.Full.RunPF}
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) : (descZ Zp Np cF).PlanOk :=
  (VerifiableInference.Desc.FileDescription.planOk_ok _).1 L.planOk

variable (scope : InScope Z = true) {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp) {D : WholeD}
  {r : LPFD.Full.RunPF} (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF)
include scope hr L

/-- At each of the twenty-five places a member of the first chain without its last stands. -/
theorem k8_member_at {l : ℕ} (hl : l < 25) :
    ∃ b ∈ (descZ Zp Np cF).first.blocksInOrder.dropLast, b.place = k8PlaceAt l := by
  have h := (k8_places_front Z Zp Np cF scope hr L).1
  have hm : k8PlaceAt l ∈ (List.range 25).map k8PlaceAt :=
    List.mem_map_of_mem (List.mem_range.2 hl)
  rw [← h] at hm
  obtain ⟨b, hb, e⟩ := List.mem_map.1 (List.mem_filter.1 hm).1
  exact ⟨b, hb, e⟩

/-- A member of the first chain of the kind K8 is not the last. -/
theorem k8_in_front {b : Block TS ProofFile.Cl} (hb : b ∈ (descZ Zp Np cF).first.blocksInOrder)
    (hk : b.place.kind = KindName.K8) : b ∈ (descZ Zp Np cF).first.blocksInOrder.dropLast := by
  have hl := (k8_places_front Z Zp Np cF scope hr L).2
  obtain ⟨bl, hbl, hkl⟩ := Option.map_eq_some_iff.1 hl
  have hfl : (descZ Zp Np cF).first.blocksInOrder.dropLast ++ [bl] = (descZ Zp Np cF).first.blocksInOrder :=
    List.dropLast_append_getLast? bl hbl
  rw [← hfl] at hb
  rcases List.mem_append.1 hb with hb | hb
  · exact hb
  · obtain rfl := List.mem_singleton.1 hb
    rw [hk] at hkl
    cases hkl

/-- It has the one round of the smallness test. -/
theorem k8_rounds {b : Block TS ProofFile.Cl} (hb : b ∈ (descZ Zp Np cF).first.blocksInOrder)
    (hk : b.place.kind = KindName.K8) :
    ∃ P : Par, b.rounds = [VerifiableInference.Desc.First.K8.round P] := by
  obtain ⟨P, -, h⟩ := pin_first_public Z Zp Np cF scope hr L (matsOf Zp.p.X) b
    (k8_in_front Z Zp Np cF scope hr L hb hk) hk
  exact ⟨P.1, h⟩

end

theorem thinBook_word : Spec.thinBook_word := by
  intro Z Zp Np cF scope pp hr D r L
  refine thinBook_word_of _ _ (planOk_laid Z Zp Np cF L).places
    ((List.nodup_range).map fun a a' h => k8PlaceAt_inj h) (fun a ha => ?_) fun b hb ha => ?_
  · obtain ⟨l, hl, rfl⟩ := List.mem_map.1 ha
    obtain ⟨b, hb, e⟩ := k8_member_at Z Zp Np cF scope hr L (List.mem_range.1 hl)
    exact ⟨b, List.mem_of_mem_dropLast hb, e⟩
  · obtain ⟨l, -, e⟩ := List.mem_map.1 ha
    obtain ⟨P, h⟩ := k8_rounds Z Zp Np cF scope hr L hb (by rw [← e]; rfl)
    rw [h]
    rfl

/-! ## On readyTests and ready -/

section
variable {V W X : Type}

/-- Where the halves' places are pairwise distinct, no two halves stand at one place. The converse
of nodup_of_twice (Johnson/Desc/ProofFile/Honest/Law/Rule/FileOkOf.lean); the line «have hf» is
written as in that lemma's proof, and count_place of that file is called. -/
theorem twice_of_nodup {hs : List (Placed V W X)} (hn : (hs.map (·.place)).Nodup) :
    ProofFile.Honest.twice hs = [] := by
  unfold ProofFile.Honest.twice
  have hf : ((hs.map (·.place)).filter fun a =>
      decide (1 < (hs.filter fun h => h.place == a).length)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro a _
    rw [← ProofFile.Honest.count_place, decide_eq_true_eq]
    exact Nat.not_lt.2 (List.nodup_iff_count_le_one.1 hn a)
  rw [hf]
  rfl

end

section
variable {W₀ Rc Xi Tr' X : Type}

/-- Halves made number by number, each at the written place of its number, of pairwise distinct
numbers, stand at pairwise distinct places. -/
theorem nodup_in (f : ℕ → Option (Placed (Local W₀ Rc Xi Tr') (Local W₀ Rc Xi Tr') X))
    (hf : ∀ l g, f l = some g → g.place = k8PlaceAt l) : ∀ ls : List ℕ, ls.Nodup →
    ((ls.filterMap f).map (·.place)).Nodup
  | [], _ => List.nodup_nil
  | l :: ls, hn => by
    have hn' := List.nodup_cons.1 hn
    cases hc : f l with
    | none =>
      rw [List.filterMap_cons_none hc]
      exact nodup_in f hf ls hn'.2
    | some g =>
      rw [List.filterMap_cons_some hc, List.map_cons]
      refine List.nodup_cons.2 ⟨fun hm => ?_, nodup_in f hf ls hn'.2⟩
      obtain ⟨g2, hg2, e⟩ := List.mem_map.1 hm
      obtain ⟨l2, hl2, e2⟩ := List.mem_filterMap.1 hg2
      rw [hf _ _ e2, hf _ _ hc] at e
      exact hn'.1 (k8PlaceAt_inj e ▸ hl2)

theorem nodup_thin (Zp : ProofFile.Pub) (cells : Tr' → Cells) :
    ((thinFirst Zp cells :
      List (Placed (Local W₀ Rc Xi Tr') (Local W₀ Rc Xi Tr') X)).map (·.place)).Nodup := by
  unfold thinFirst
  refine nodup_in _ (fun l g h => ?_) _ List.nodup_range
  obtain ⟨P, -, rfl⟩ := Option.map_eq_some_iff.1 h
  rfl

end

/-- readyTests returns where each of its tests passes. -/
theorem tests_ok {W₀ Rc Xi Ky Tr' X₀ X : Type} (F : VerifiableInference.Desc.FileDescription Xi) (B : ProverCoinCounts)
    (H : Prover W₀ Rc Xi Ky Tr' X₀ X) (w : W₀)
    (s1 : ProofFile.Honest.strays F.first.blocksInOrder H.first = [])
    (s2 : ProofFile.Honest.strays F.shared.blocksInOrder H.shared = [])
    (s3 : ProofFile.Honest.strays F.second.blocksInOrder H.second = [])
    (t1 : ProofFile.Honest.twice H.first = []) (t2 : ProofFile.Honest.twice H.shared = [])
    (t3 : ProofFile.Honest.twice H.second = []) (hp : F.placesOk = true)
    (hd : H.inRange H.dummy = true) (hw : H.inRange w = true) (hb : B.word F = none) :
    ProofFile.Honest.readyTests F B H w = .ok () := by
  unfold ProofFile.Honest.readyTests
  rw [s1, s2, s3, t1, t2, t3, hp, hd, hw, hb]
  rfl

section
variable (Z : PublicFiles) (Zp : ProofFile.Pub) (Np : H2U.Places4)
  (cF : VerifiableInference.Desc.Chain TS ProofFile.Cl) {Tr' X₀ Xh : Type}
  (cells' : Tr' → Cells) (e : Tr → Tr') (H₀ : Prover FullSizeMatrix (protocolAtFiles Z).EncodingRandomness ProofFile.Inst TableKey Tr' X₀ Xh)

theorem thinP_first : (thinP Z Zp Np cF cells' e H₀).first = thinFirst Zp cells' :=
  forget_bareRows _

theorem thinP_shared : (thinP Z Zp Np cF cells' e H₀).shared = [] := rfl

theorem thinP_second : (thinP Z Zp Np cF cells' e H₀).second = [] := rfl

end

theorem thin_ready : Spec.thin_ready := by
  intro Z Zp Np cF Tr' X₀ Xh H₀ scope pp hr live D r L cells' e
  obtain ⟨i, x', T⟩ := servedTyped_exists Z Zp Np cF scope hr live L
  obtain ⟨rc⟩ := (inferInstance : Nonempty (protocolAtFiles Z).EncodingRandomness)
  obtain ⟨s⟩ := (inferInstance : Nonempty (protocolAtFiles Z).OutOfDomainSeed)
  have PO := planOk_laid Z Zp Np cF L
  have e1 := thinP_first Z Zp Np cF cells' e H₀
  have e2 := thinP_shared Z Zp Np cF cells' e H₀
  have e3 := thinP_second Z Zp Np cF cells' e H₀
  have htr : (thinP Z Zp Np cF cells' e H₀).trace (VerifiableInference.OnPublicFiles.Flat.matrixOf i)
      (LPFD.Full.instanceAsPlainRecord (x', (protocolAtFiles Z).recOf (VerifiableInference.OnPublicFiles.Flat.matrixOf i) rc s)) =
      some (e (theTrace Zp.p.X i x'.val)) := by
    show (viaIndex (modelTrace Zp.p.X) (VerifiableInference.OnPublicFiles.Flat.matrixOf i) _).map e = _
    rw [viaIndex_matrixOf, modelTrace_served Zp.p.X i (x', _) T]
    rfl
  have hs1 : ProofFile.Honest.strays (descZ Zp Np cF).first.blocksInOrder
      (thinP Z Zp Np cF cells' e H₀).first = [] := by
    rw [e1]
    unfold ProofFile.Honest.strays
    rw [List.map_eq_nil_iff, List.filter_eq_nil_iff]
    intro g hg
    obtain ⟨l, P, hl, -, rfl⟩ := mem_thinFirst Zp cells' hg
    obtain ⟨b, hb, eb⟩ := k8_member_at Z Zp Np cF scope hr L hl
    have ha : ((descZ Zp Np cF).first.blocksInOrder.any fun b => b.place == k8PlaceAt l) = true :=
      List.any_eq_true.2 ⟨b, List.mem_of_mem_dropLast hb, by rw [eb]; exact beq_self_eq_true _⟩
    show ¬ (!((descZ Zp Np cF).first.blocksInOrder.any fun b => b.place == k8PlaceAt l)) = true
    rw [ha]
    decide
  have hT : ProofFile.Honest.readyTests (descZ Zp Np cF) (thinB Zp Np cF)
      (thinP Z Zp Np cF cells' e H₀) (VerifiableInference.OnPublicFiles.Flat.matrixOf i) = .ok () :=
    tests_ok _ _ _ _ hs1 (by rw [e2]; rfl) (by rw [e3]; rfl)
      (by rw [e1]; exact twice_of_nodup (nodup_thin Zp cells')) (by rw [e2]; rfl)
      (by rw [e3]; rfl) PO.places rfl rfl (thinBook_word Z Zp Np cF scope hr L)
  have c1 : ∀ v k, ∃ l, ProofFile.Honest.chainSteps (thinB Zp Np cF) ((thinB Zp Np cF).rowsOf 0)
      (ProofFile.Honest.Coins.look (B := thinB Zp Np cF) k 0) v (descZ Zp Np cF).first.blocksInOrder
      (thinP Z Zp Np cF cells' e H₀).first = .ok l := by
    intro v k
    rw [e1]
    refine chain_ok _ _ _ _ _ _ fun b hb => ⟨len_of_shaped (PO.blocks₁ b hb).2, fun h hh => ?_⟩
    obtain ⟨l, P, hl, -, rfl⟩ := mem_thinFirst Zp cells' (List.mem_of_find?_eq_some hh)
    have hp : k8PlaceAt l = b.place := by simpa using List.find?_some hh
    have hk : b.place.kind = KindName.K8 := by rw [← hp]; rfl
    obtain ⟨Q, hQ⟩ := k8_rounds Z Zp Np cF scope hr L hb hk
    refine ⟨by rw [hQ]; rfl, ?_, ?_, rfl, ?_⟩
    · rw [← hp]
      exact lookup_key id (fun _ => [1]) (k8PlaceAt l) [1] _
        ⟨_, List.mem_map_of_mem (List.mem_range.2 hl), rfl⟩ fun _ _ _ => rfl
    · rw [List.any_eq_false]
      intro q hq
      obtain ⟨b', -, rfl⟩ := List.mem_map.1 hq
      simp
    · refine lend_quiet _ _ _ _ _ _ rfl ?_
      have hlk := lookup_key (fun b : Block TS ProofFile.Cl => (⟨b.place, 0⟩ : Addr))
        (fun b => (⟨ProofFile.Honest.maskWords b, 0⟩ : Due)) ⟨b.place, 0⟩ ⟨0, 0⟩
        (descZ Zp Np cF).first.blocksInOrder ⟨b, hb, rfl⟩ fun b' hb' e' => by
          have ep : b'.place = b.place := congrArg (fun a : Addr => a.place) e'
          obtain ⟨Q', hQ'⟩ := k8_rounds Z Zp Np cF scope hr L hb' (by rw [ep]; exact hk)
          exact congrArg (fun n : ℕ => (⟨n, 0⟩ : Due))
            (no_mask_of_round (PO.blocks₁ b' hb').2 hQ')
      exact congrArg (fun o : Option Due => o.getD ⟨0, 0⟩) hlk
  have c2 : ∀ v c₀, ∃ l, ProofFile.Honest.chainSteps (thinB Zp Np cF) ((thinB Zp Np cF).rowsOf 1)
      (ProofFile.Honest.sharedLook (thinB Zp Np cF) c₀) v (descZ Zp Np cF).shared.blocksInOrder
      (thinP Z Zp Np cF cells' e H₀).shared = .ok l := by
    intro v c₀
    rw [e2]
    exact chain_ok _ _ _ _ _ _ fun b hb =>
      ⟨len_of_shaped (PO.blocks₂ b hb).2, fun h hh => by cases hh⟩
  have c3 : ∀ v k, ∃ l, ProofFile.Honest.chainSteps (thinB Zp Np cF) ((thinB Zp Np cF).rowsOf 2)
      (ProofFile.Honest.Coins.look (B := thinB Zp Np cF) k 2) v (descZ Zp Np cF).second.blocksInOrder
      (thinP Z Zp Np cF cells' e H₀).second = .ok l := by
    intro v k
    rw [e3]
    exact chain_ok _ _ _ _ _ _ fun b hb =>
      ⟨len_of_shaped (PO.blocks₃ b hb).2, fun h hh => by cases hh⟩
  exact ⟨_, rc, _, default, ready_ok_of _ _ _ _ rc _ default hT htr (c1 _ _) (c2 _ _) (c3 _ _)⟩

theorem premises_met_together : Spec.premises_met_together := by
  intro Z Zp Np cF R₂ R₃ _ _ _ _ run₂ run₃ Tr' X₀ Xh H₀ scope pp hr live D r L cells' e hE
  have e1 := thinP_first Z Zp Np cF cells' e H₀
  refine ⟨thin_ready Z Zp Np cF H₀ scope hr live L cells' e, fun L' hL' => ?_, ?_, ?_,
    fun Yes => ?_⟩
  · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hL'
    show g.place.kind ≠ KindName.frame
    rw [thin_no_frame Zp cells' g hg]
    decide
  · rw [e1]
    exact (pin_first_iff Z Zp Np cF scope hr L cells' _).2
      (thin_halves Z Zp Np cF scope hr L cells')
  · rw [thinP_second]
    exact (pin_iff _ cells' _ _).2 ⟨public_second Zp Np cF, fun b _ g hg => by cases hg⟩
  · exact cellsOwn_speaks Z Zp Np cF run₂ run₃ _ _ _ Yes cells' e hE

theorem sessionStops_at_thin : Spec.sessionStops_at_thin := by
  intro Z Zp Np cF R₂ R₃ _ _ _ _ run₂ run₃ Tr' X₀ Xh H₀ scope pp hr live D r L cells' e hE Yes ok Gs
  obtain ⟨⟨w₀, rc, x₀, k₀, R, hR⟩, hn, h₁, h₃, hO⟩ :=
    premises_met_together Z Zp Np cF run₂ run₃ H₀ scope hr live L cells' e hE
  exact sessionStops_of_cellsOwn Z Zp Np cF run₂ run₃ _ _ _ scope hr live L hR hn Yes
    (matsOf Zp.p.X) cells' h₁ h₃ (hO Yes) ok Gs

end OnBytes.FrontRoad

#print axioms OnBytes.FrontRoad.nonemptyPadZ_thinProver
#print axioms OnBytes.FrontRoad.nonemptyOfInhabited_thinProver
#print axioms OnBytes.FrontRoad.k8PlaceAt_inj
#print axioms OnBytes.FrontRoad.mem_thinFirst
#print axioms OnBytes.FrontRoad.find_in
#print axioms OnBytes.FrontRoad.thin_find
#print axioms OnBytes.FrontRoad.thin_no_frame
#print axioms OnBytes.FrontRoad.thin_halves
#print axioms OnBytes.FrontRoad.thin_meets_four
#print axioms OnBytes.FrontRoad.filter_key_len
#print axioms OnBytes.FrontRoad.one_of_nodup
#print axioms OnBytes.FrontRoad.due_mono
#print axioms OnBytes.FrontRoad.due_mem
#print axioms OnBytes.FrontRoad.lookup_one
#print axioms OnBytes.FrontRoad.len_of_shaped
#print axioms OnBytes.FrontRoad.no_mask_of_round
#print axioms OnBytes.FrontRoad.masks_ok
#print axioms OnBytes.FrontRoad.not_not_true
#print axioms OnBytes.FrontRoad.thinBook_word_of
#print axioms OnBytes.FrontRoad.lookup_key
#print axioms OnBytes.FrontRoad.chain_ok
#print axioms OnBytes.FrontRoad.lend_quiet
#print axioms OnBytes.FrontRoad.planOk_laid
#print axioms OnBytes.FrontRoad.k8_member_at
#print axioms OnBytes.FrontRoad.k8_in_front
#print axioms OnBytes.FrontRoad.k8_rounds
#print axioms OnBytes.FrontRoad.thinBook_word
#print axioms OnBytes.FrontRoad.twice_of_nodup
#print axioms OnBytes.FrontRoad.nodup_in
#print axioms OnBytes.FrontRoad.nodup_thin
#print axioms OnBytes.FrontRoad.tests_ok
#print axioms OnBytes.FrontRoad.thinP_first
#print axioms OnBytes.FrontRoad.thinP_shared
#print axioms OnBytes.FrontRoad.thinP_second
#print axioms OnBytes.FrontRoad.thin_ready
#print axioms OnBytes.FrontRoad.premises_met_together
#print axioms OnBytes.FrontRoad.sessionStops_at_thin
#print axioms OnBytes.FrontRoad.ready_ok_of
