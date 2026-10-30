-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/CallsC.lean: K01_law: THE FIVE BINDERS ON THE PLAN's NUMBERS (hinj · trees · msgs · hP · hbase of k01_later_tied, Johnson/Desc/K1/Law/LaterOne.lean), EACH TO ITS LETTER, FROM A YES OF TESTS WITH CODE ON THE NUMBERS N AND ON WHAT THE CHAIN's BLOCKS TELL
(told), by five proofs (NumbersFreeProofs.lean · SentAtProofs.lean, this folder) and fenceFit_at.
  PlanK1 N told Z G₀ L     **what is asked of the plan's side, in one structure**: four tests' yes and two sentences:
     rows    First.eachOnce ((List.range 26).map fun m => (N.groupAt m, 0)) = true   (one conjunct of First.rowsAtFit N 25, the table's own test; no conjunct of planSideOk)
     book    First.bookFit N ps told = true                    (Johnson/Desc/First/BookFit.lean; it has run true at both sizes)
     fence   First.fenceFit N linksFull ps = true              (Johnson/Desc/First/FenceFit.lean; it has run true at both sizes)
     sent    sentAtB N told (noL l d) l (momL d) = true        (K1's files', SentAt.lean in this folder: it has run at no plan)
     tells   block number noL l d tells a list that is the place's layout (K1.Declares)      (row N6: in scope, from the description's own block; owed)
     base    the piece's base at (l, d) is N.treesAt at the place                             (row N8: with the piece's letters; owed)
  tenant_sampled   row N7: every message of the fifty has an out-of-domain (OOD) sample, in tenantOf's form [kernel: later_sampled_full]
  hinj_of · trees_of · msgs_of · hP_of · hbase_of
Nothing on soundness.
-/
import Johnson.Desc.K1.Law.LaterOne
import Johnson.Desc.K1.Law.NumbersUser
import Johnson.Desc.K1.Law.NumbersFreeProofs
import Johnson.Desc.K1.Law.SentAtProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S Numbers flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull)
open VerifiableInference.Desc.K13.Law (openAt)
open VerifiableInference.Desc.ReqLit (shapeFull)
open IM (k1Ix)

/-- **What K01_law asks of the plan's side.** told: for each block of the first chain, in order, the oracles beneath the roots that it sends. B: the pieces' bases. -/
structure PlanK1 (N : Numbers) (told : List (List Oracle)) (Z : ProofFile.Pub) (G₀ : ProofFile.Ground)
    (B : ℕ → Bool → ℕ) : Prop where
  /-- THE ONE CONJUNCT OF First.rowsAtFit N 25 THAT K01_law SPENDS: no two of the segments 0 … 25 have one group.
  At groupAt := id: by the kernel (groupsOnce_id). -/
  rows : First.eachOnce ((List.range 26).map fun m => (N.groupAt m, 0)) = true
  book : First.bookFit N (flatPlacesOf linksFull true) told = true
  fence : First.fenceFit N linksFull (flatPlacesOf linksFull true) = true
  sent : ∀ l, l < 25 → ∀ d : Bool, sentAtB N told (noL l d) l (momL d) = true
  tells : ∀ l, l < 25 → ∀ d : Bool, ∃ decl, told[noL l d]? = some decl ∧
    Declares decl (layOf (parL Z G₀ l d)) (parL Z G₀ l d).sent.size (tenantOf (parL Z G₀ l d))
  base : ∀ l, l < 25 → ∀ d : Bool, B l d = N.treesAt (flatPlacesOf linksFull true)[noL l d]?

/-- ROW N7. -/
theorem tenant_sampled (q : Params.First) (gp : GPar) (hs : q.shape = shapeFull) (l piece m : Nat)
    (hl : l < 25) (hm : m = 1 ∨ m = 2) (i : Nat) (hi : i < (parLater q gp l piece m).sent.size) :
    (tenantOf (parLater q gp l piece m) i).sampled = true := by
  have h := List.all_eq_true.1 (List.all_eq_true.1 later_sampled_full l (List.mem_range.2 hl)) m
    (by rcases hm with rfl | rfl <;> simp)
  have h2 := List.all_eq_true.1 ((Bool.and_eq_true_iff.1 h).2)
  have e : (parLater q gp l piece m).sent.toList[i]? =
      some ((parLater q gp l piece m).sent.getD i default) := by
    rw [Array.getElem?_toList, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
    rfl
  have hmem : (parLater q gp l piece m).sent.getD i default ∈ laterSent shapeFull l m := by
    rw [← hs, ← parLater_sent q gp l piece m]
    exact List.mem_of_getElem? e
  exact h2 _ hmem

theorem tenant_sampledL (Z : ProofFile.Pub) (G₀ : ProofFile.Ground) (hs : G₀.first.shape = shapeFull) (l : ℕ)
    (hl : l < 25) (d : Bool) (i : Nat) (hi : i < (parL Z G₀ l d).sent.size) :
    (tenantOf (parL Z G₀ l d) i).sampled = true := by
  cases d with
  | true => exact tenant_sampled _ _ hs l _ 2 hl (Or.inr rfl) i hi
  | false => exact tenant_sampled _ _ hs l _ 1 hl (Or.inl rfl) i hi

/-- From the one conjunct. -/
theorem groups_inj (N : Numbers)
    (h : First.eachOnce ((List.range 26).map fun m => (N.groupAt m, 0)) = true) (m m' : ℕ)
    (hm : m ≤ 25) (hm' : m' ≤ 25) (e : N.groupAt m' = N.groupAt m) : m' = m :=
  eq_of_nodup_map (fun m => (N.groupAt m, 0)) _ (eachOnce_nodup _ h) m'
    (List.mem_range.2 (Nat.lt_succ_of_le hm')) m (List.mem_range.2 (Nat.lt_succ_of_le hm))
    (by show (N.groupAt m', 0) = (N.groupAt m, 0); rw [e])

/-- It is met where the groups' numbers are the segments' own (the structure's default). -/
theorem groupsOnce_id : First.eachOnce ((List.range 26).map fun m => ((id m : ℕ), 0)) = true := by
  decide

/-- It can fail: two segments with one group. -/
theorem groupsOnce_no : First.eachOnce ((List.range 26).map fun _ => ((0 : ℕ), 0)) = false := by
  decide

/-- hinj_fifty (NumbersUser.lean) from «no two segments have one group» alone. -/
theorem hinj_fifty' (N : Numbers)
    (h : ∀ m m' : ℕ, m ≤ 25 → m' ≤ 25 → N.groupAt m' = N.groupAt m → m' = m) (l : ℕ) (hl : l < 25)
    (d : Bool) :
    ∀ m' ∈ First.rowSegs (openAt linksFull (flatPlacesOf linksFull true)
      (14 * l + k1Ix l d + 2 + 1)), N.groupAt m' = N.groupAt l → m' = l := by
  intro m' hm' e
  have a := of_decide_eq_true (List.all_eq_true.1 (List.all_eq_true.1
    (List.all_eq_true.1 rowSegs_full l (List.mem_range.2 hl)) d (by cases d <;> simp)) m' hm')
  exact h l m' (by omega) (by omega) e

section
variable {N : Numbers} {told : List (List Oracle)} {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {B : ℕ → Bool → ℕ}

theorem hinj_of (h : PlanK1 N told Z G₀ B) (l : ℕ) (hl : l < 25) (d : Bool) :
    ∀ m' ∈ First.rowSegs (openAt linksFull (flatPlacesOf linksFull true) (noL l d + 1)),
      N.groupAt m' = N.groupAt l → m' = l :=
  hinj_fifty' N (groups_inj N h.rows) l hl d

theorem trees_of (h : PlanK1 N told Z G₀ B) (l : ℕ) (hl : l < 25) (d : Bool) :
    N.treesAt (flatPlacesOf linksFull true)[noL l d + 1]? =
      N.treesAt (flatPlacesOf linksFull true)[noL l d]? + (layOf (parL Z G₀ l d)).shapes.size := by
  obtain ⟨decl, ht, hD⟩ := h.tells l hl d
  exact (book_fifty bookFitSucc declaredCounts N told h.book l hl d _ decl ht hD).1

theorem msgs_of (h : PlanK1 N told Z G₀ B) (l : ℕ) (hl : l < 25) (d : Bool) :
    N.msgsAt (flatPlacesOf linksFull true)[noL l d + 1]? =
      N.msgsAt (flatPlacesOf linksFull true)[noL l d]? + (parL Z G₀ l d).sent.size := by
  obtain ⟨decl, ht, hD⟩ := h.tells l hl d
  exact (book_fifty bookFitSucc declaredCounts N told h.book l hl d _ decl ht hD).2

theorem hP_of (h : PlanK1 N told Z G₀ B) (hs : G₀.first.shape = shapeFull) (l : ℕ) (hl : l < 25)
    (d : Bool) :
    laterSeatsB N (parL Z G₀ l d) l (momL d)
      (N.treesAt (flatPlacesOf linksFull true)[noL l d]?) = true := by
  obtain ⟨decl, ht, hD⟩ := h.tells l hl d
  exact laterSeatsOfTold N _ told (noL l d) l (momL d) _ decl h.book
    (Nat.le_of_lt (lt_places l hl d)) ht hD (tenant_sampledL Z G₀ hs l hl d) (h.sent l hl d)

theorem hbase_of (h : PlanK1 N told Z G₀ B) (l : ℕ) (hl : l < 25) (d : Bool) :
    ∀ u ∈ First.sampledIn N (openAt linksFull (flatPlacesOf linksFull true) (noL l d)),
      u.1 < B l d := by
  rw [h.base l hl d]
  exact hbase_fifty N h.fence l hl d

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.tenant_sampled
#print axioms VerifiableInference.Desc.K1.hinj_of
#print axioms VerifiableInference.Desc.K1.trees_of
#print axioms VerifiableInference.Desc.K1.msgs_of
#print axioms VerifiableInference.Desc.K1.hP_of
#print axioms VerifiableInference.Desc.K1.hbase_of
