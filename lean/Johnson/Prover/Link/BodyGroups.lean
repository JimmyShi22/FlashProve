-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/BodyGroups.lean: THE COPY's FILE's PROXIMITY TEST: THE GROUPS THAT Block.step
DEALS THE STAGES ARE THE GROUPS AT WHICH THE STAGES' LAWS SPEAK: what the declared rounds behind
"BAT" read of what the written rounds drew (groupsOf, Johnson/Desc/Block.lean), each group read by
key (readG, Johnson/Desc/Plain/OneYes.lean), IS bodyAll's own list of groups
(Johnson/Prover/Link/BodyAll.lean). Two definitions, statements and proofs.

  Looked        along bodyAll's own recursion: at each stage the first of the plan's lists that are
                left names ONE tree, of the stage's depth, and under that tree's key the look-up
                finds, at every position of the tree, the written column that holds the stage's rows
  groups_two    two declared rounds of which the first reads nothing and the second one tree
  groups_body   under Dealt (Johnson/Desc/K12/OpenLaws.lean), h ≤ k at each stage, and Looked
  Seats         its letters: a look-up L, a list TR of columns, stages and the plan's lists: under
                each LATER stage's declared tree's key the look-up finds the column that stands, in
                a list of the rounds' columns, at the round "SEND seed" of the switch into that
                stage
  tr_seed, tr_later   where bodyAll's own list of the rounds' columns holds a switch's column, and
                the later stages'
  looked_of_tr  Looked from: the list agrees with bodyAll's from a place b on; the first stage's
                clause; Seats

By: groupsOf_append (Johnson/Desc/BlockSlot.lean), groupsOf_none (Johnson/Desc/K15/FoldInv.lean),
Dealt.cons, open_step (OpenLaws.lean), readG_groupAt (LinkLook.lean), length_sRF (BodyCausal.lean).

Limits. Looked, or Seats with the first stage's clause, is a premise: NO MEMBER OF EITHER IS SHOWN
HERE, and none can be shown by evaluation (bodyAll has no code). Nothing on what a stage decides.
Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.LinkLook
import Johnson.Prover.Link.DeclPlan
import Johnson.Desc.K15.FoldInv
import Johnson.Desc.BlockSlot

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.Plain.One (readG)
open H2K.Pub (sgOf)

/-- **Under each stage's declared tree's key the look-up finds the stage's written column.** -/
def Looked (L : ℕ → ℕ → Option (List UInt64)) (p : P12) (K : BCoins) (D : ℕ → Fmt.Drawn) :
    List Fmt.M1.Stage → ℕ → Fmt.M1.Stage → Laid → ℕ → T12 → PS → (ℕ → List UInt64) →
      List (List Told) → Prop
  | [], _, cur, _, _, _, _, col, Ls =>
    ∃ o' Ls', Ls = [o'] :: Ls' ∧ o'.1.a = cur.C.a ∧
      ∀ x, x < 2 ^ cur.C.a → L (o'.1.tree - 0) x = some (col x)
  | next :: rest, j, cur, l, o, t, P, col, Ls =>
    ∃ o' Ls', Ls = [o'] :: Ls' ∧ o'.1.a = cur.C.a ∧
      (∀ x, x < 2 ^ cur.C.a → L (o'.1.tree - 0) x = some (col x)) ∧
      Looked L p K D rest (j + 1) next (l.drop (cur.k + 3))
        (o + ((sgOf cur).h + (sgOf cur).g) + 3)
        (sT3 p K rest.isEmpty j cur next l o t P col (rowOf t) D)
        (sNext K rest.isEmpty j cur next o P (rowOf t) D)
        (sCol K rest.isEmpty j cur next o P (rowOf t) D) Ls'

/-- Two declared rounds of which the first reads nothing and the second one tree. -/
theorem groups_two (L : ℕ → ℕ → Option (List UInt64)) (d₁ d₂ : Fmt.DeclaredRound) (x₁ x₂ : Fmt.Drawn)
    (o' : Told) (a : ℕ) (col : ℕ → List UInt64) (s1 : d₁.stored = []) (s2 : d₂.stored = [])
    (h1 : d₁.opens = []) (h2 : d₂.opens = [o']) (ha : o'.1.a = a)
    (hL : ∀ x, x < 2 ^ a → L (o'.1.tree - 0) x = some (col x)) :
    (groupsOf 0 [d₁, d₂] [x₁, x₂]).map (readG L) = [groupAt a x₂.poss col] := by
  simp only [groupsOf, s1, s2, h1, h2, List.map_nil, List.map_cons, List.nil_append,
    List.append_nil, List.cons_append]
  rw [ha, readG_groupAt L _ a _ _ col hL]

/-- **The groups that the stages are dealt.** -/
theorem groups_body (L : ℕ → ℕ → Option (List UInt64)) (p : P12) (K : BCoins)
    (D : ℕ → Fmt.Drawn) :
    ∀ (rest : List Fmt.M1.Stage) (j : ℕ) (cur : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P : PS)
      (col : ℕ → List UInt64) (Ls : List (List Told)), Dealt cur rest Ls l →
      (∀ s ∈ cur :: rest, s.h ≤ s.k) → Looked L p K D rest j cur l o t P col Ls →
      (groupsOf 0 (l.map (·.1)) ((bodyAll p K rest j cur l o t P col D).rs.map (·.drawn))).map
        (readG L) = (bodyAll p K rest j cur l o t P col D).gs
  | [], j, cur, l, o, t, P, col, Ls, hD, _, hK => by
    obtain ⟨o', Ls', rfl, ha, hL⟩ := hK
    have hl : l.map (·.1.opens) = [[], [o']] := by
      rw [hD.opens]
      rfl
    obtain ⟨y₁, y₂, rfl⟩ : ∃ y₁ y₂, l = [y₁, y₂] := by
      have h2l : l.length = 2 := by
        have := congrArg List.length hl
        simpa using this
      match l, h2l with
      | [y₁, y₂], _ => exact ⟨y₁, y₂, rfl⟩
    have e := List.cons.inj hl
    exact groups_two L y₁.1 y₂.1 _ _ o' _ col (hD.stored y₁ (by simp)) (hD.stored y₂ (by simp))
      e.1 (List.cons.inj e.2).1 ha hL
  | next :: rest, j, cur, l, o, t, P, col, Ls, hD, hk, hK => by
    obtain ⟨o', Ls', rfl, ha, hL, hK'⟩ := hK
    have hc := hD.cons
    have hD' := (open_step (Cl := Unit) guardedProximityTestParts p j cur next rest _ _ l hD).2.2
    have ek : (sgOf cur).h + (sgOf cur).g = cur.k :=
      Nat.add_sub_cancel' (hk cur List.mem_cons_self)
    have ih := groups_body L p K D rest (j + 1) next (l.drop (cur.k + 3))
      (o + ((sgOf cur).h + (sgOf cur).g) + 3)
      (sT3 p K rest.isEmpty j cur next l o t P col (rowOf t) D)
      (sNext K rest.isEmpty j cur next o P (rowOf t) D)
      (sCol K rest.isEmpty j cur next o P (rowOf t) D) Ls' hD'
      (fun s hs => hk s (List.mem_cons_of_mem _ hs)) hK'
    have hlen : cur.k + 3 ≤ l.length := by
      have := congrArg List.length hc
      simp only [List.length_map, List.length_append, List.length_replicate,
        List.length_cons] at this
      omega
    -- the rounds, cut in three
    have hl3 : l = l.take (1 + cur.k) ++ ((l.drop (1 + cur.k)).take 2 ++ l.drop (cur.k + 3)) := by
      have e3 : l.drop (cur.k + 3) = (l.drop (1 + cur.k)).drop 2 := by
        rw [List.drop_drop]
        congr 1
        omega
      rw [e3, List.take_append_drop, List.take_append_drop]
    obtain ⟨y₁, y₂, h2⟩ : ∃ y₁ y₂, (l.drop (1 + cur.k)).take 2 = [y₁, y₂] := by
      have h2l : ((l.drop (1 + cur.k)).take 2).length = 2 := by
        rw [List.length_take, List.length_drop]
        omega
      match (l.drop (1 + cur.k)).take 2, h2l with
      | [y₁, y₂], _ => exact ⟨y₁, y₂, rfl⟩
    obtain ⟨q1, q2⟩ := cs_opens cur next rest _ _ l hD y₁.1 y₂.1 (by rw [h2]; rfl)
    have m1 : y₁ ∈ l := List.mem_of_mem_drop (List.mem_of_mem_take (h2 ▸ List.mem_cons_self))
    have m2 : y₂ ∈ l := List.mem_of_mem_drop (List.mem_of_mem_take
      (h2 ▸ List.mem_cons_of_mem _ List.mem_cons_self))
    have hquiet : ∀ d ∈ (l.take (1 + cur.k)).map (·.1), d.stored = [] ∧ d.opens = [] := by
      intro d hd
      obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hd
      refine ⟨hD.stored y (List.mem_of_mem_take hy), ?_⟩
      have h1 : (l.take (1 + cur.k)).map (·.1.opens) = List.replicate (1 + cur.k) [] := by
        rw [List.map_take, hc, List.take_left' (by simp)]
      have : y.1.opens ∈ List.replicate (1 + cur.k) ([] : List Told) := by
        rw [← h1]
        exact List.mem_map.2 ⟨y, hy, rfl⟩
      exact (List.mem_replicate.1 this).2
    show (groupsOf 0 (l.map (·.1)) ((sRF K j cur o P (rowOf t) D ++
      sRS p K j cur next l o t P (rowOf t) D ++ (bodyAll p K rest _ _ _ _ _ _ _ D).rs).map
        (·.drawn))).map (readG L) = sGS cur o col D ++ (bodyAll p K rest _ _ _ _ _ _ _ D).gs
    have hA : ((l.take (1 + cur.k)).map (·.1)).length =
        ((sRF K j cur o P (rowOf t) D).map (·.drawn)).length := by
      rw [List.length_map, List.length_map, length_sRF, ek, List.length_take]
      omega
    have hm : l.map (·.1) = (l.take (1 + cur.k)).map (·.1) ++
        ([y₁.1, y₂.1] ++ (l.drop (cur.k + 3)).map (·.1)) := by
      conv_lhs => rw [hl3]
      rw [h2, List.map_append, List.map_append]
      rfl
    rw [hm, List.append_assoc, List.map_append, List.map_append,
      groupsOf_append 0 _ _ _ _ hA, groupsOf_none 0 _ _ hquiet, List.nil_append,
      groupsOf_append 0 _ _ _ _ rfl, List.map_append, ih]
    congr 1
    exact groups_two L y₁.1 y₂.1 _ _ o' _ col (hD.stored y₁ m1) (hD.stored y₂ m2) q1 q2 ha hL

/-! ## Looked, from the trees' columns by round -/

/-- **Under each later stage's declared tree's key the look-up finds the column that stands, in a
list of the rounds' columns, at the round "SEND seed" of the switch into that stage.** Its letters:
a look-up L and a list TR of the rounds' columns; stages and the plan's lists. b: the place in the
list of the first round of the stage cur. -/
def Seats (L : ℕ → ℕ → Option (List UInt64)) (TR : List (ℕ → List UInt64)) :
    ℕ → Fmt.M1.Stage → List Fmt.M1.Stage → List (List Told) → Prop
  | _, _, [], _ => True
  | b, cur, next :: rest, Ls =>
    ∃ o' Ls', Ls = [o'] :: Ls' ∧ o'.1.a = next.C.a ∧
      (∀ x, x < 2 ^ next.C.a → L (o'.1.tree - 0) x =
        some ((TR[b + (1 + ((sgOf cur).h + (sgOf cur).g))]?).getD (fun _ => []) x)) ∧
      Seats L TR (b + (((sgOf cur).h + (sgOf cur).g) + 3)) next rest Ls'

section
variable (p : P12) (K : BCoins) (D : ℕ → Fmt.Drawn) (next : Fmt.M1.Stage)
  (rest : List Fmt.M1.Stage) (j : ℕ) (cur : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P : PS)
  (col : ℕ → List UInt64)

/-- The column of the tree that the switch sends stands at its round "SEND seed". -/
theorem tr_seed : (bodyAll p K (next :: rest) j cur l o t P col D).tr[1 +
    ((sgOf cur).h + (sgOf cur).g)]? = some (sCol K rest.isEmpty j cur next o P (rowOf t) D) := by
  show ((sRF K j cur o P (rowOf t) D).map (fun (_ : Fmt.RoundView) (_ : ℕ) => ([] : List UInt64)) ++
    [sCol K rest.isEmpty j cur next o P (rowOf t) D, fun _ => []] ++
    (bodyAll p K rest _ _ _ _ _ _ _ D).tr)[1 + ((sgOf cur).h + (sgOf cur).g)]? = _
  rw [List.append_assoc, List.getElem?_append_right (by rw [List.length_map, length_sRF]),
    List.length_map, length_sRF, Nat.sub_self]
  rfl

/-- Behind the stage's rounds stand the later stages'. -/
theorem tr_later (i : ℕ) : (bodyAll p K (next :: rest) j cur l o t P col D).tr[
    ((sgOf cur).h + (sgOf cur).g) + 3 + i]? =
    (bodyAll p K rest (j + 1) next (l.drop (cur.k + 3)) (o + ((sgOf cur).h + (sgOf cur).g) + 3)
      (sT3 p K rest.isEmpty j cur next l o t P col (rowOf t) D)
      (sNext K rest.isEmpty j cur next o P (rowOf t) D)
      (sCol K rest.isEmpty j cur next o P (rowOf t) D) D).tr[i]? := by
  show ((sRF K j cur o P (rowOf t) D).map (fun (_ : Fmt.RoundView) (_ : ℕ) => ([] : List UInt64)) ++
    [sCol K rest.isEmpty j cur next o P (rowOf t) D, fun _ => []] ++
    (bodyAll p K rest _ _ _ _ _ _ _ D).tr)[((sgOf cur).h + (sgOf cur).g) + 3 + i]? = _
  have hl : ((sRF K j cur o P (rowOf t) D).map (fun (_ : Fmt.RoundView) (_ : ℕ) => ([] : List UInt64)) ++
      [sCol K rest.isEmpty j cur next o P (rowOf t) D, fun _ => []]).length =
      ((sgOf cur).h + (sgOf cur).g) + 3 := by
    rw [List.length_append, List.length_map, length_sRF]
    show 1 + _ + 2 = _
    omega
  rw [List.getElem?_append_right (by rw [hl]; omega), hl, Nat.add_sub_cancel_left]

end

/-- **Looked, from the trees' columns by round.** -/
theorem looked_of_tr (L : ℕ → ℕ → Option (List UInt64)) (p : P12) (K : BCoins)
    (D : ℕ → Fmt.Drawn) (TR : List (ℕ → List UInt64)) :
    ∀ (rest : List Fmt.M1.Stage) (j : ℕ) (cur : Fmt.M1.Stage) (l : Laid) (o : ℕ) (t : T12) (P : PS)
      (col : ℕ → List UInt64) (b : ℕ) (o' : Told) (Ls' : List (List Told)),
      (∀ i, TR[b + i]? = (bodyAll p K rest j cur l o t P col D).tr[i]?) → o'.1.a = cur.C.a →
      (∀ x, x < 2 ^ cur.C.a → L (o'.1.tree - 0) x = some (col x)) → Seats L TR b cur rest Ls' →
      Looked L p K D rest j cur l o t P col ([o'] :: Ls')
  | [], _, _, _, _, _, _, _, _, o', Ls', _, ha, hL, _ => ⟨o', Ls', rfl, ha, hL⟩
  | next :: rest, j, cur, l, o, t, P, col, b, o', Ls', hT, ha, hL, hS => by
    obtain ⟨o'', Ls'', rfl, ha', hL', hS'⟩ := hS
    refine ⟨o', _, rfl, ha, hL, looked_of_tr L p K D TR rest _ _ _ _ _ _ _
      (b + (((sgOf cur).h + (sgOf cur).g) + 3)) o'' Ls'' (fun i => ?_) ha' (fun x hx => ?_) hS'⟩
    · rw [Nat.add_assoc, hT, tr_later]
    · rw [hL' x hx, hT, tr_seed]
      rfl

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.groups_two
#print axioms Johnson.Prover.Link.groups_body
#print axioms Johnson.Prover.Link.tr_seed
#print axioms Johnson.Prover.Link.tr_later
#print axioms Johnson.Prover.Link.looked_of_tr
