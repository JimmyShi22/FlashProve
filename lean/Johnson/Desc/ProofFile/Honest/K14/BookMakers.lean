-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/BookMakers.lean: WHAT THE FRAME's MAKERS OF A BOOK's ENTRIES
YIELD, WHERE THEY YIELD, READ OFF THEIR TEXT (addrOfRound, addrIn, foldBehind, foldK:
Honest/BookFolds.lean, Honest/BookRows.lean; behindFold, carryPair, groupCarries:
Honest/BookCarry.lean; splitEntry: Honest/BookAll.lean); and that a later round's part is not in
front of an earlier round's. One definition with code, one form; statements with their proofs. NO
KIND's PART IS NAMED: the files on the books at "send o_u" and at "send o_omega" both call these.

  addrIn_planOf, planOf_rounds, addrOfRound_skip   the two texts by which a round's part is found
                  agree; a plan has the list's rounds; a member whose rounds are all earlier is
                  passed over
  mapM_agree      two functions that agree on a list's members yield the same under mapM
  carryPair_form, carryPair_spender, groupCarries_form   an entry that carries: of which message; to
                  which of the fold's two parts
  idx_of_drop, find_of_dropWhile, zipIdx_entries   three small steps on lists
  foldBehind_name, foldBehind_foldK, foldK_entries, foldK_congr   the round that foldBehind finds is
                  named "FOLD epsilon"; the makers' two ways to a fold's number of rounds agree;
                  that number reads the rounds' entries alone
  behindFold_fold, behindFold_rounds, foldSeedAt, behindFold_seeds   **which rounds' parts a fold's
                  two parts are**: that of the first round named "FOLD epsilon" behind the given
                  one, and that of the first round named "SEND seed" behind that; with code, of the
                  rounds' entries alone
  split_spender   who spends the split's coin: the part of the first round named "SPLIT"
  StandsBehind ord s k   the form: s stands in front of k; k does not stand in front of s; they
                  are two
  partNo_mono, addr_not_before   **a later round's part is not in front of an earlier round's**, in
                  an order without a repeat that holds the list's places in the list's order

Kin. The frame's addrOfRound_place, addrIn_place, planOf_places (Honest/BookSharedKit.lean) ·
cutRow_order, chainActs_order, theActs_order (Honest/Law/Rule/Order.lean): the addresses of a
chain's acts stand in the order Addr.before, in the same setting (an order without a repeat, pre ++
the list's places ++ post): near kin of addr_not_before, which speaks of the makers' addrOfRound.
Called of the frame's: Addr.not_before (Honest/Law/Rule/Lent.lean).
What is not claimed. That any maker yields at any list. That two rounds lie in two parts. No
property.
-/
import Johnson.Desc.ProofFile.Honest.BookSharedLaw
import Johnson.Desc.ProofFile.Honest.Law.Rule.Lent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block Place)
open ProofFile.Honest.BookShared

variable {S Cl : Type}

/-! ## 1 A round's part -/

/-- The maker's two ways to an address agree. -/
theorem addrIn_planOf : ∀ (bs : List (Block S Cl)) (i : Nat),
    addrIn (planOf bs) i = addrOfRound bs i
  | [], _ => rfl
  | b :: bs, i => by
    show addrIn (⟨b.place, partsCut b, b.rounds⟩ :: planOf bs) i = _
    rw [addrIn, addrOfRound]
    split
    · rfl
    · exact addrIn_planOf bs _

/-- And its two ways to the rounds. -/
theorem planOf_rounds (bs : List (Block S Cl)) :
    (planOf bs).flatMap (·.rounds) = bs.flatMap (·.rounds) := by
  unfold planOf
  rw [List.flatMap_map]

/-- A sub-protocol whose rounds all lie in front of the round is passed. -/
theorem addrOfRound_skip (b : Block S Cl) (bs : List (Block S Cl)) (i : Nat)
    (h : b.rounds.length ≤ i) : addrOfRound (b :: bs) i = addrOfRound bs (i - b.rounds.length) := by
  rw [addrOfRound, if_neg (by omega)]

/-! ## 2 Small steps on lists -/

/-- Two functions that agree on a list's members yield the same there, one by one. -/
theorem mapM_agree {α β : Type} {f g : α → Option β} :
    ∀ l : List α, (∀ x ∈ l, f x = g x) → l.mapM f = l.mapM g
  | [], _ => rfl
  | a :: l, h => by
    rw [List.mapM_cons, List.mapM_cons, h a (List.Mem.head _),
      mapM_agree l fun x hx => h x (List.Mem.tail _ hx)]

/-- A member of a numbered list behind its first n members has a number from n on. -/
theorem idx_of_drop {α : Type} {L : List α} {n : Nat} {x : α × Nat}
    (h : x ∈ L.zipIdx.drop n) : n ≤ x.2 := by
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 h
  rw [List.getElem?_drop, List.getElem?_zipIdx] at hk
  obtain ⟨a, -, rfl⟩ := Option.map_eq_some_iff.1 hk
  simp

/-- What stands first behind the members that fail a test is the first member that passes it. -/
theorem find_of_dropWhile {α : Type} (p : α → Bool) : ∀ (l : List α) (x : α) (u : List α),
    l.dropWhile (fun a => !p a) = x :: u → l.find? p = some x
  | [], _, _, h => by cases h
  | a :: l, x, u, h => by
    rw [List.dropWhile_cons] at h
    rw [List.find?_cons]
    cases hp : p a with
    | true =>
      rw [hp] at h
      exact congrArg some (List.cons.inj h).1
    | false =>
      rw [hp] at h
      exact find_of_dropWhile p l x u h

/-- The numbered entries are the numbered rounds' entries. -/
theorem zipIdx_entries (R : List Fmt.DeclaredRound) (n : Nat) :
    ((R.map (·.entry)).zipIdx.drop n) =
      (R.zipIdx.drop n).map fun y => (y.1.entry, y.2) := by
  rw [List.zipIdx_map, List.map_drop]
  rfl

/-! ## 3 An entry that carries -/

/-- A carrying entry is a message's whole run, carried. (Kin: the frame's carryPair_owner,
Honest/BookSharedKit.lean, has the owner.) -/
theorem carryPair_form {p q : Addr} {reach : List SentMsg} {own : Option SentMsg} :
    ∀ e ∈ carryPair p q reach own, ∃ m, (m ∈ reach ∨ own = some m) ∧ e.owner = m.sender ∧
      e.start = m.start ∧ e.count = m.count ∧ e.once = false := by
  intro e he
  unfold carryPair at he
  rcases List.mem_append.1 he with h | h
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 h
    exact ⟨m, Or.inl hm, rfl, rfl, rfl, rfl⟩
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.1 h
    rcases List.mem_append.1 hm with h1 | h1
    · exact ⟨m, Or.inl h1, rfl, rfl, rfl, rfl⟩
    · refine ⟨m, Or.inr ?_, rfl, rfl, rfl, rfl⟩
      cases own with
      | none => cases h1
      | some x => rw [mem_one h1]

/-- A carrying entry is handed to one of the fold's two parts. -/
theorem carryPair_spender {p q : Addr} {reach : List SentMsg} {own : Option SentMsg} :
    ∀ e ∈ carryPair p q reach own, e.spender = p ∨ e.spender = q := by
  intro e he
  unfold carryPair at he
  rcases List.mem_append.1 he with h | h
  · obtain ⟨m, -, rfl⟩ := List.mem_map.1 h
    exact Or.inl rfl
  · obtain ⟨m, -, rfl⟩ := List.mem_map.1 h
    exact Or.inr rfl

/-- The same of a fold whose group the caller lays. -/
theorem groupCarries_form {l : List PlanB} {i : Nat} {group : List SentMsg}
    {own : Option SentMsg} {r : List Ahead} (h : groupCarries l i group own = .ok r) :
    ∀ e ∈ r, ∃ m, (m ∈ group ∨ own = some m) ∧ e.owner = m.sender ∧ e.start = m.start ∧
      e.count = m.count ∧ e.once = false := by
  unfold groupCarries at h
  split at h
  · rw [← Except.ok.inj h]
    exact carryPair_form
  · cases h

/-! ## 4 A fold, and the sending behind it -/

/-- The round that foldBehind finds is named "FOLD epsilon". -/
theorem foldBehind_name {l : List PlanB} {i e : Nat} {b : Bool} {k : Nat}
    (h : foldBehind l i = some (e, b, k)) :
    ∃ r, (l.flatMap (·.rounds))[e]? = some r ∧ r.entry.name = "FOLD epsilon" := by
  unfold foldBehind at h
  dsimp only at h
  split at h
  · cases h
  · rename_i x u hx
    have e1 : x.2 = e := congrArg Prod.fst (Option.some.inj h)
    have hm : x ∈ ((l.flatMap (·.rounds)).zipIdx.drop (i + 1)).dropWhile
        fun r => r.1.entry.name != "FOLD epsilon" := by
      rw [hx]
      exact List.Mem.head _
    have hn : (x.1.entry.name != "FOLD epsilon") = false := by
      have := List.head?_dropWhile_not (fun r : Fmt.DeclaredRound × Nat =>
        r.1.entry.name != "FOLD epsilon") ((l.flatMap (·.rounds)).zipIdx.drop (i + 1))
      rw [hx] at this
      simpa using this
    have hz : x ∈ (l.flatMap (·.rounds)).zipIdx :=
      List.mem_of_mem_drop ((List.dropWhile_sublist _).mem hm)
    refine ⟨x.1, ?_, by simpa using hn⟩
    rw [← e1]
    exact List.mem_zipIdx_iff_getElem?.1 hz

/-- **The maker's two ways to a fold's number of rounds agree.** -/
theorem foldBehind_foldK {l : List PlanB} {i e : Nat} {b : Bool} {k : Nat}
    (h : foldBehind l i = some (e, b, k)) :
    foldK ((l.flatMap (·.rounds)).drop (i + 1)) = some k := by
  have hZ : ((l.flatMap (·.rounds)).zipIdx.drop (i + 1)).map Prod.fst =
      (l.flatMap (·.rounds)).drop (i + 1) := by
    rw [List.map_drop, List.zipIdx_map_fst]
  unfold foldBehind at h
  dsimp only at h
  split at h
  · cases h
  · rename_i x u hx
    have hx' : ((l.flatMap (·.rounds)).zipIdx.drop (i + 1)).dropWhile
        ((fun r : Fmt.DeclaredRound => r.entry.name != "FOLD epsilon") ∘ Prod.fst) = x :: u := hx
    have e3 : (u.takeWhile
        ((fun r : Fmt.DeclaredRound => r.entry.name == "FOLD round") ∘ Prod.fst)).length = k :=
      congrArg (fun y => y.2.2) (Option.some.inj h)
    unfold foldK
    rw [← hZ, List.dropWhile_map, hx']
    show some ((u.map Prod.fst).takeWhile fun r => r.entry.name == "FOLD round").length = _
    rw [List.takeWhile_map, List.length_map, e3]

/-- The maker's count of a fold's rounds, of the rounds' entries. -/
theorem foldK_entries (rs : List Fmt.DeclaredRound) :
    foldK rs =
      match (rs.map (·.entry)).dropWhile fun e => e.name != "FOLD epsilon" with
      | [] => none
      | _ :: u => some (u.takeWhile fun e => e.name == "FOLD round").length := by
  rw [List.dropWhile_map]
  unfold foldK
  have e : ((fun e : Fmt.Entry => e.name != "FOLD epsilon") ∘ fun r : Fmt.DeclaredRound => r.entry) =
      fun r : Fmt.DeclaredRound => r.entry.name != "FOLD epsilon" := rfl
  rw [e]
  cases rs.dropWhile fun r : Fmt.DeclaredRound => r.entry.name != "FOLD epsilon" with
  | nil => rfl
  | cons x u =>
    show some _ = some ((u.map (·.entry)).takeWhile fun e => e.name == "FOLD round").length
    rw [List.takeWhile_map, List.length_map]
    rfl

/-- **It reads the rounds' entries alone.** -/
theorem foldK_congr {rs rs' : List Fmt.DeclaredRound} (h : rs.map (·.entry) = rs'.map (·.entry)) :
    foldK rs = foldK rs' := by
  rw [foldK_entries, foldK_entries, h]

/-- The fold's part, in the maker's two texts. -/
theorem behindFold_fold {l : List PlanB} {i : Nat} {p q : Addr}
    (h : behindFold l i = some (p, q)) :
    ∃ f, foldBehind l i = some f ∧ addrIn l f.1 = some p := by
  unfold behindFold at h
  obtain ⟨f, hf, h⟩ := opt_bind h
  dsimp only at h
  obtain ⟨q', -, h⟩ := opt_bind h
  obtain ⟨p', hp, h⟩ := opt_map h
  obtain ⟨rfl, -⟩ := Prod.mk.inj h
  exact ⟨f, hf, hp⟩

/-- **Which rounds' parts a fold's two parts are**: that of a round named "FOLD epsilon", and that
of a later round. -/
theorem behindFold_rounds {l : List PlanB} {i : Nat} {p q : Addr}
    (h : behindFold l i = some (p, q)) :
    ∃ e s ρ, (l.flatMap (·.rounds))[e]? = some ρ ∧ ρ.entry.name = "FOLD epsilon" ∧ e < s ∧
      addrIn l e = some p ∧ addrIn l s = some q := by
  unfold behindFold at h
  obtain ⟨⟨e, b, k⟩, hf, h⟩ := opt_bind h
  dsimp only at h
  obtain ⟨q', hq, h⟩ := opt_bind h
  obtain ⟨p', hp, h⟩ := opt_map h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
  obtain ⟨s, hs, hq⟩ := opt_bind hq
  obtain ⟨ρ, hρ, hn⟩ := foldBehind_name hf
  exact ⟨e, s.2, ρ, hρ, hn, idx_of_drop (List.mem_of_find?_eq_some hs), hp, hq⟩

/-- With code, of the rounds' entries alone: the number of the first round "FOLD epsilon" behind the
round i, and of the first round "SEND seed" behind that. -/
def foldSeedAt (es : List Fmt.Entry) (i : Nat) : Option (Nat × Nat) :=
  ((es.zipIdx.drop (i + 1)).find? fun r => r.1.name == "FOLD epsilon").bind fun x =>
    ((es.zipIdx.drop (x.2 + 1)).find? fun r => r.1.name == "SEND seed").map fun y => (x.2, y.2)

/-- **The maker's behindFold finds the parts of these two rounds.** -/
theorem behindFold_seeds {l : List PlanB} {i : Nat} {p q : Addr}
    (h : behindFold l i = some (p, q)) :
    ∃ e s, foldSeedAt ((l.flatMap (·.rounds)).map (·.entry)) i = some (e, s) ∧
      addrIn l e = some p ∧ addrIn l s = some q := by
  unfold behindFold at h
  obtain ⟨f, hf, h⟩ := opt_bind h
  dsimp only at h
  obtain ⟨q', hq, h⟩ := opt_bind h
  obtain ⟨p', hp, h⟩ := opt_map h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
  obtain ⟨s, hs, hq⟩ := opt_bind hq
  unfold foldBehind at hf
  dsimp only at hf
  split at hf
  · cases hf
  · rename_i x u hx
    have ef : f.1 = x.2 := by rw [← Option.some.inj hf]
    rw [ef] at hp hs
    have h1 : ((l.flatMap (·.rounds)).zipIdx.drop (i + 1)).find?
        (fun r => r.1.entry.name == "FOLD epsilon") = some x :=
      find_of_dropWhile (fun r : Fmt.DeclaredRound × Nat => r.1.entry.name == "FOLD epsilon") _ x u hx
    refine ⟨x.2, s.2, ?_, hp, hq⟩
    unfold foldSeedAt
    rw [zipIdx_entries, List.find?_map]
    have h1' : ((l.flatMap (·.rounds)).zipIdx.drop (i + 1)).find?
        ((fun r : Fmt.Entry × Nat => r.1.name == "FOLD epsilon") ∘
          fun y : Fmt.DeclaredRound × Nat => (y.1.entry, y.2)) = some x := h1
    rw [h1']
    show (((((l.flatMap (·.rounds)).map (·.entry)).zipIdx.drop (x.2 + 1)).find?
      fun r => r.1.name == "SEND seed").map fun y => (x.2, y.2)) = _
    rw [zipIdx_entries, List.find?_map]
    have h2' : ((l.flatMap (·.rounds)).zipIdx.drop (x.2 + 1)).find?
        ((fun r : Fmt.Entry × Nat => r.1.name == "SEND seed") ∘
          fun y : Fmt.DeclaredRound × Nat => (y.1.entry, y.2)) = some s := hs
    rw [h2']
    rfl

/-! ## 5 The split's coin -/

/-- Who spends the split's coin: the part of the first round named "SPLIT". -/
theorem split_spender {S Cl : Type} {xs : List (Block S Cl)} {p1 : Johnson.G.ChainSends}
    {e : Ahead} (h : splitEntry xs p1 = some e) :
    addrOfRound xs ((xs.flatMap (·.rounds)).findIdx fun r => r.entry.name == "SPLIT") =
      some e.spender := by
  unfold splitEntry at h
  dsimp only at h
  obtain ⟨p, hp, h⟩ := opt_bind h
  obtain ⟨m, -, h⟩ := opt_map h
  rw [hp, ← h]
  rfl

/-! ## 6 The order of rounds' parts -/

/-- What is shown of a part k beside the part s: s stands in front of k in the order; k does not
stand in front of s; the two are not one. -/
def StandsBehind (ord : List Place) (s k : Addr) : Prop :=
  s.before ord k = true ∧ k.before ord s = false ∧ k ≠ s

/-- The number of the part that holds a round, among a sub-protocol's parts: it does not fall as the
round's number grows. -/
theorem partNo_mono (starts : List Nat) {i j : Nat} (h : i ≤ j) :
    (starts.filter (· ≤ i)).length - 1 ≤ (starts.filter (· ≤ j)).length - 1 := by
  have : (starts.filter (· ≤ i)).length ≤ (starts.filter (· ≤ j)).length := by
    induction starts with
    | nil => exact Nat.le_refl _
    | cons x t ih =>
      simp only [List.filter_cons]
      by_cases h1 : x ≤ i
      · have h2 : x ≤ j := Nat.le_trans h1 h
        simp only [h1, h2, decide_true, if_true, List.length_cons]
        omega
      · by_cases h2 : x ≤ j
        · simp only [h1, h2, decide_true, decide_false, if_true, List.length_cons]
          simp
          omega
        · simp only [h1, h2, decide_false]
          simpa using ih
  omega

/-- **A later round's part is not in front of an earlier round's**, in an order of places without a
repeat that holds the list's places, in the list's order, between two stretches. -/
theorem addr_not_before : ∀ (bs : List (Block S Cl)) (pre post : List Place) (i j : Nat)
    (a b : Addr), (pre ++ bs.map (·.place) ++ post).Nodup → i ≤ j → addrOfRound bs i = some a →
    addrOfRound bs j = some b → b.before (pre ++ bs.map (·.place) ++ post) a = false
  | [], _, _, _, _, _, _, _, _, ha, _ => by
    rw [addrOfRound] at ha
    cases ha
  | x :: bs, pre, post, i, j, a, b, hN, hij, ha, hb => by
    rw [addrOfRound] at ha hb
    by_cases hi : i < x.rounds.length
    · rw [if_pos hi] at ha
      by_cases hj : j < x.rounds.length
      · rw [if_pos hj] at hb
        rw [← Option.some.inj ha, ← Option.some.inj hb]
        unfold Addr.before
        simp only [Nat.lt_irrefl, decide_false, Bool.false_or, beq_self_eq_true, Bool.true_and,
          decide_eq_false_iff_not, Nat.not_lt]
        exact partNo_mono _ hij
      · rw [if_neg hj] at hb
        have hbp := addrOfRound_place _ _ _ hb
        have e : pre ++ (x :: bs).map (·.place) ++ post =
            (pre ++ [x.place]) ++ (bs.map (·.place) ++ post) := by simp
        rw [e] at hN ⊢
        refine Addr.not_before (by rw [← Option.some.inj ha]; simp) fun hmem => ?_
        exact (List.nodup_append.1 hN).2.2 _ hmem _ (List.mem_append_left _ hbp) rfl
    · rw [if_neg hi] at ha
      rw [if_neg (by omega)] at hb
      have e : pre ++ (x :: bs).map (·.place) ++ post =
          (pre ++ [x.place]) ++ bs.map (·.place) ++ post := by simp
      rw [e] at hN ⊢
      exact addr_not_before bs (pre ++ [x.place]) post _ _ a b hN (by omega) ha hb

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.addrIn_planOf
#print axioms ProofFile.Honest.K14.planOf_rounds
#print axioms ProofFile.Honest.K14.addrOfRound_skip
#print axioms ProofFile.Honest.K14.mapM_agree
#print axioms ProofFile.Honest.K14.idx_of_drop
#print axioms ProofFile.Honest.K14.find_of_dropWhile
#print axioms ProofFile.Honest.K14.zipIdx_entries
#print axioms ProofFile.Honest.K14.carryPair_form
#print axioms ProofFile.Honest.K14.carryPair_spender
#print axioms ProofFile.Honest.K14.groupCarries_form
#print axioms ProofFile.Honest.K14.foldBehind_name
#print axioms ProofFile.Honest.K14.foldBehind_foldK
#print axioms ProofFile.Honest.K14.foldK_entries
#print axioms ProofFile.Honest.K14.foldK_congr
#print axioms ProofFile.Honest.K14.behindFold_fold
#print axioms ProofFile.Honest.K14.behindFold_rounds
#print axioms ProofFile.Honest.K14.behindFold_seeds
#print axioms ProofFile.Honest.K14.split_spender
#print axioms ProofFile.Honest.K14.partNo_mono
#print axioms ProofFile.Honest.K14.addr_not_before
