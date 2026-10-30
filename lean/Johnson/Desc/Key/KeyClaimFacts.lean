-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/KeyClaimFacts.lean: THE KEY FILE's ROW 1.16: THE TWO FACTS ON THE CLAIM THAT THE BATCHING MAKES (border 17's two new clauses of the book-keeping). No oracle, no witness.
  listOf_zeros     the set of a list of zeros that is not empty is [0]
  seat_fit         the seat's yes holds the front's own test on the laid pile (memberRowsFit)
  batt_masks       the row that the batching hands on names the ledger's entries alone (rowOf_onLedger) AND NAMES ONE (the fresh entries: run_fields · G4.hidingWalk_length)
  claim_masks0     so, at the ledger 0: listOfT ‹the claim's masks' messages› = [0]
  claim_parts      every mask entry of the claim that the batching makes stands at the part «mask» (memberClaim's own text)
  PubPile one      PUBLIC, ON THE PLAN ALONE: the matrix's rows are spelled by at most 63 bits · every run of every part of every lookup lies inside the part
  pile_ok          under PubPile every vector of every row of the laid pile is Tensor.ok (by KeyPend.pendingAt_ok and its mapM_get, Johnson/RunOne/KeyPend.lean, called)
  claim_ok         so every vector of the claim's row weights is Tensor.ok (batt_row_ok)
Nothing on soundness.
-/
import Johnson.Desc.Key.KeyPileSays
import Johnson.Desc.Key.KeyBattRow
import Johnson.Desc.Key.KeyTensorOk
import Johnson.Desc.K13.Law.Good2
import OnBytes.G4.RunLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key
open OnBytes OnBytes.Params
open VerifiableInference.Desc.K13 (batt St)
open Johnson.Desc.First.ForkGround (RowsOwed)
open VerifiableInference.Desc.K13.Law (batt_ok ebind_ok frontB_fit OnLedger rowOf_onLedger onLedger_of_fit run_fields walkOf wsOf)

theorem listOf_zeros : ∀ l : List Nat, l ≠ [] → (∀ x ∈ l, x = 0) → Fmt.listOf l = [0]
  | [], h, _ => absurd rfl h
  | x :: t, _, h0 => by
    obtain rfl : x = 0 := h0 x List.mem_cons_self
    cases t with
    | nil => rfl
    | cons y t' =>
      have ih := listOf_zeros (y :: t') (by simp) fun z hz => h0 z (List.mem_cons_of_mem _ hz)
      show Fmt.insertIntoIncreasingList 0 (Fmt.listOf (y :: t')) = [0]
      rw [ih]
      rfl

variable {β Cl : Type}

theorem seat_fit (keysOf : β → List (List Lkp.Keys)) (one : OneTime) (N : Pieces) (sent : Nat) (s s' : ChainState β) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (batchTableRows (Cl := Cl) keysOf one N sent).decide s rs gs = .ok s') (rows : List TensorRow)
    (hlay : layPile keysOf one s = .ok { s with pile := rows }) : memberRowsFit s.d.st (batchWhere one N sent).lin s.idx rows = true := by
  unfold batchTableRows at h
  dsimp only at h
  rw [decide_andThen] at h
  obtain ⟨t₃, h3, _⟩ := ebind_ok.1 h
  rw [decide_andThen] at h3
  obtain ⟨t₂, h2, _⟩ := ebind_ok.1 h3
  rw [decide_andThen] at h2
  obtain ⟨t₁, h1, hf⟩ := ebind_ok.1 h2
  have h1' : layPile keysOf one s = .ok t₁ := h1
  obtain rfl : ({ s with pile := rows } : ChainState β) = t₁ := Except.ok.inj (hlay.symm.trans h1')
  obtain ⟨p, he, hp, hfit⟩ := frontB_fit batchLens _ hf
  obtain ⟨_, rfl⟩ := (lens_enter _ _).1 he
  obtain ⟨_, rfl⟩ := (lens_get _ _).1 hp
  exact hfit

section
variable {owed : RowsOwed} {k n : Nat} {pile : List TensorRow} {ledger : Nat} {d : St} {rs : List Fmt.RoundView} {out : TensorRow × St}

theorem fits_pos (h : Batt.fits k pile = true) : 1 ≤ k := by
  unfold Batt.fits at h
  cases pile with
  | nil => exact nomatch h
  | cons r₀ l =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1

theorem batt_masks (h : batt owed k n pile ledger d rs = .ok out) (hp : ∀ r ∈ pile, OnLedger ledger r) : out.1.masks ≠ [] ∧ OnLedger ledger out.1 := by
  obtain ⟨_, _, x, t, hd, o, _, _, hf, _, _, _, _, ho, _, rfl⟩ := batt_ok h
  refine ⟨?_, rowOf_onLedger hf hp ho⟩
  obtain ⟨hr, _, hfr, _, hmk, _, _⟩ := run_fields hf ho
  show o.rowMasks ≠ []
  rw [hmk]
  have hk := fits_pos hf
  have hz : ((wsOf k).zip (hd.rounds.map (·.2))) ≠ [] := by
    intro e
    have := congrArg List.length e
    simp only [List.length_zip, List.length_replicate, List.length_map, hr, Nat.min_self, List.length_nil] at this
    omega
  have hw := OnBytes.G4.hidingWalk_length _ hz (fun p hp' => by
    have h1 := (List.of_mem_zip hp').1
    rw [List.eq_of_mem_replicate h1]
    decide)
  intro e
  have hl := congrArg List.length e
  simp only [List.length_append, List.length_zip, List.length_nil] at hl
  have hw' : 1 ≤ (walkOf k hd).1.length := by
    show 1 ≤ (Psc.hidingWalk ((wsOf k).zip (hd.rounds.map (·.2)))).1.length
    rw [hw]
    omega
  omega

theorem claim_masks0 (h : batt owed k n pile 0 d rs = .ok out) (hp : ∀ r ∈ pile, OnLedger 0 r) :
    listOfT ((memberClaim out.1).masks.toList.map (·.oracle)) = [0] := by
  obtain ⟨hne, hon⟩ := batt_masks h hp
  rw [listOfT_eq]
  have e : (memberClaim out.1).masks.toList.map (·.oracle) = out.1.masks.map (·.1.oracle) := by
    simp [memberClaim, List.map_map, Function.comp_def]
  rw [e]
  refine listOf_zeros _ (by simpa using hne) fun x hx => ?_
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
  exact hon t ht

theorem claim_ok (h : batt owed k n pile ledger d rs = .ok out) (hp : ∀ r ∈ pile, ∀ t ∈ r.g, t.ok = true) : (memberClaim out.1).g.all (·.ok) = true :=
  List.all_eq_true.2 fun t ht => batt_row_ok h hp t ht

end

/-- **Every mask entry of the claim that the batching makes stands at the part «mask»**: by memberClaim's own text. (A clause that, by reading, is fenced nowhere in the tables' promise from border 17 on: THE BATCHING CAN EARN IT.) -/
theorem claim_parts (r : TensorRow) : (memberClaim r).masks.all (·.part == .mask) = true := by
  simp [memberClaim]

/-- **PUBLIC, on the plan alone.** -/
structure PubPile (one : OneTime) : Prop where
  kRow : (Wf.matrixOf one.lin).kRow ≤ 63
  runs : ∀ L ∈ one.ranges.lookups, ∀ p ∈ L.parts, ∀ r ∈ p.runs, r.firstPlace + r.places ≤ 2 ^ p.logPlaces

theorem pile_ok (keysOf : β → List (List Lkp.Keys)) (one : OneTime) (H : PubPile one) (s : ChainState β) (rows : List TensorRow)
    (hlay : layPile keysOf one s = .ok { s with pile := rows }) : ∀ r ∈ rows, ∀ t ∈ r.g, t.ok = true := by
  obtain ⟨rowss, _, hm, e⟩ := layPile_whole _ _ _ _ hlay
  have er : rows = rowss.flatten := congrArg (·.pile) e
  intro r hr
  rw [er] at hr
  obtain ⟨rl, hrl, hr'⟩ := List.mem_flatten.1 hr
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hrl
  obtain ⟨⟨L, cs⟩, hz, hf⟩ := (Johnson.RunOne.KeyRows1.mapM_get _ _ _ hm).2 i rl hi
  exact Johnson.RunOne.KeyRows1.pendingAt_ok _ L cs rl H.kRow (H.runs L (List.of_mem_zip (List.mem_of_getElem? hz)).1) hf r hr'

end VerifiableInference.Desc.Key

#print axioms VerifiableInference.Desc.Key.seat_fit
#print axioms VerifiableInference.Desc.Key.claim_masks0
#print axioms VerifiableInference.Desc.Key.claim_ok
#print axioms VerifiableInference.Desc.Key.claim_parts
#print axioms VerifiableInference.Desc.Key.pile_ok
