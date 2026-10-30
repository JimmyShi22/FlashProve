-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/CutProof.lean: cutAll at a book's known entries, and, under three public
premises, at the entries by which an address spends, is a function of the instance's coins in knownN
and knownT, or in spentN: the names of the known and of the spent coins. The proofs of Spec.knownTie
and Spec.spentTie.
Terms: Johnson/SendSim/At/Sim.lean; for the book, Johnson/SendSim/At/Fresh.lean; sender, readC,
slot, name, number: Johnson/SendSim/At/Bridge.lean. Limits of the folder: Johnson/SendSim/Defs.lean.

What this file proves, for each value of the coins; no distribution is named.
  knownTie, spentTie   Spec.knownTie, which has no premise, and Spec.spentTie, which has three:
               sendFits; WithinAt; MaskSpender or FoldSpender. Both are written out in
               Johnson/SendSim/At/CutTie.lean.
  cutAll_congr   For every number of coins and every list of entries: cutAll is the same at two
               values of the coins that agree at the entries' numbers. cut_congr says it of one run.
  cutAll_some  If every entry is within the number of coins, cutAll returns the runs, not none.

Limits. The two functions are obtained by choice; they are not given as explicit terms. The
conditions on the book are public. What is proved of them with a coin spent:
Johnson/SendSim/At/Fresh.lean, Limits.

How it fits. Johnson/SendSim/At/JoinRows.lean uses knownTie and spentTie for rowsFresh
(Johnson/SendSim/At/RowsFresh.lean). Johnson/SendSim/At/Runs.lean, Johnson/SendSim/At/WriteAll.lean
and Johnson/SendSim/At/FoldAnyRoad.lean use cutAll_congr and cutAll_some. The three sets are defined
in Johnson/SendSim/At/ClearOf.lean. The proofs rest chiefly on seat_onto
(Johnson/Desc/ProofFile/Honest/K1/SeatOnto.lean: every number below the sender's number of coins is
a slot's), exists_name (Johnson/SendSim/At/Names.lean) and free_lt
(Johnson/Desc/ProofFile/Honest/K1/Fence.lean).

The other names.
  exists_tail  a slot in a tail, within the sizes, with a coordinate that its field has, is the slot
               and coordinate of a name in TailN.
  coinAt_names, ce_names, cf_names   let c and c' be read alike by readC at all names in namesOf NE
               NF and tailsOf NE NF. Then coinAt agrees at every slot within the sizes whose number
               is in the pair, and c and c' have the same coin at every number in NE and in NF.
  mem_eAll, mem_fAll   a number of an entry of a list is a number of the list.
  spent_inMsg  under MaskSpender or FoldSpender, a slot within the sizes whose number is spent is
               not in a tail.
-/
import Johnson.Desc.ProofFile.Honest.K1.SeatOnto
import Johnson.SendSim.At.CutTie
import Johnson.SendSim.At.ClearOfFold

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open Johnson.Prover.Send (shapeAt)

variable {P : K1.Par} {ride : Nat → Option Ride}

/-- A slot y of oracle message k that is within the sizes and in a tail, with a coordinate t < 3
that is 0 if the slot's coin is in the base field, is the slot and coordinate of some name in TailN.
-/
theorem exists_tail (k : Fin P.sent.size) (y : Seat) (t : ℕ)
    (hy : y.ok P.codes (shapeAt P k) (ride k)) (hm : inMsg y = false) (ht : t < 3)
    (h0 : y.inE (shapeAt P k) = false → t = 0) :
    ∃ x : TailN P, x.1.1 = k ∧ seatT P x.1 x.2.val = (y, t) := by
  cases y with
  | word r j => cases hm
  | pad i => cases hm
  | mask i => cases hm
  | tail r q =>
    exact ⟨⟨⟨k, .inl (⟨r, hy.1⟩, ⟨t, lt_dg P k _ t ht rfl h0⟩)⟩, ⟨q, hy.2⟩⟩, rfl, rfl⟩
  | maskTail r q => exact ⟨⟨⟨k, .inr (⟨r, hy.1⟩, ⟨t, ht⟩)⟩, ⟨q, hy.2⟩⟩, rfl, rfl⟩

variable (NE NF : Finset ℕ) (c c' : Cs (dueR P ride))
  (h1 : ∀ n ∈ namesOf P ride NE NF, (readC P ride c).1 n = (readC P ride c').1 n)
  (h2 : ∀ x ∈ tailsOf P ride NE NF, (readC P ride c).2 x.1 x.2 = (readC P ride c').2 x.1 x.2)

include h1 h2 in
/-- If readC reads c and c' alike at all names in namesOf NE NF and tailsOf NE NF, then coinAt
agrees on c and c' at every slot within the sizes whose coin, by field and number, is in the pair
NE, NF, at each coordinate t < 3 that the slot's field has (t = 0 in the base field). -/
theorem coinAt_names (k : Fin P.sent.size) (y : Seat) (t : ℕ)
    (hy : y.ok P.codes (shapeAt P k) (ride k)) (ht : t < 3)
    (h0 : y.inE (shapeAt P k) = false → t = 0)
    (hin : inNos NE NF (y.inE (shapeAt P k)) (y.no P ride k)) :
    coinAt P ride c k (y, t) = coinAt P ride c' k (y, t) := by
  cases hm : inMsg y
  · obtain ⟨x, hk, hs⟩ := exists_tail k y t hy hm ht h0
    have h := h2 x ((mem_tailsOf _ _ x).2 (by rw [hs, hk]; exact hin))
    have e : ∀ d : Cs (dueR P ride), (readC P ride d).2 x.1 x.2 = coinAt P ride d k (y, t) :=
      fun d => by
        show coinAt P ride d x.1.1 (seatT P x.1 x.2.val) = _
        rw [hs, hk]
    rwa [e, e] at h
  · obtain ⟨n, hk, hs⟩ := exists_name P ride k y t hy hm ht h0
    have h := h1 n ((mem_namesOf _ _ n).2 (by rw [hs, hk]; exact hin))
    have e : ∀ d : Cs (dueR P ride), (readC P ride d).1 n = coinAt P ride d k (y, t) :=
      fun d => by
        show coinAt P ride d n.1 (seatC P ride n) = _
        rw [hs, hk]
    rwa [e, e] at h

include h1 h2 in
/-- Under the same premise, c and c' have the same coin of the extension field at every number in
NE. -/
theorem ce_names (N : ℕ) (hN : N ∈ NE) : ce c N = ce c' N := by
  by_cases hlt : N < (dueR P ride).e
  · obtain ⟨k, y, hk, hy, hE, hno⟩ := seat_onto P ride true N hlt
    refine ext_crd fun t => ?_
    have h := coinAt_names NE NF c c' h1 h2 ⟨k, hk⟩ y t.val hy t.isLt
      (fun e => by rw [hE] at e; cases e) (by
        show inNos NE NF (y.inE (shapeAt P k)) (y.no P ride k)
        rw [hE, hno]
        exact hN)
    unfold coinAt at h
    simp only [hE, if_true, co_fin, hno] at h
    exact h
  · unfold ce
    rw [dif_neg hlt, dif_neg hlt]

include h1 h2 in
/-- Under the same premise, c and c' have the same coin of the base field at every number in NF. -/
theorem cf_names (N : ℕ) (hN : N ∈ NF) : cf c N = cf c' N := by
  by_cases hlt : N < (dueR P ride).f
  · obtain ⟨k, y, hk, hy, hE, hno⟩ := seat_onto P ride false N hlt
    have h := coinAt_names NE NF c c' h1 h2 ⟨k, hk⟩ y 0 hy (by norm_num) (fun _ => rfl) (by
      show inNos NE NF (y.inE (shapeAt P k)) (y.no P ride k)
      rw [hE, hno]
      exact hN)
    unfold coinAt at h
    simp only [hE, Bool.false_eq_true, if_false, hno] at h
    exact h
  · unfold cf
    rw [dif_neg hlt, dif_neg hlt]

omit h1 h2 in
theorem mem_eAll (es : List Ahead) (e : Ahead) (he : e ∈ es) (i : ℕ) (hi : i ∈ eOf e) :
    i ∈ eAll es := by
  induction es with
  | nil => cases he
  | cons a l ih =>
    show i ∈ eOf a ∪ eAll l
    rcases List.mem_cons.1 he with rfl | h
    · exact Finset.mem_union_left _ hi
    · exact Finset.mem_union_right _ (ih h)

omit h1 h2 in
theorem mem_fAll (es : List Ahead) (e : Ahead) (he : e ∈ es) (i : ℕ) (hi : i ∈ fOf e) :
    i ∈ fAll es := by
  induction es with
  | nil => cases he
  | cons a l ih =>
    show i ∈ fOf a ∪ fAll l
    rcases List.mem_cons.1 he with rfl | h
    · exact Finset.mem_union_left _ hi
    · exact Finset.mem_union_right _ (ih h)

omit h1 h2 in
/-- Cs.cut at a run is the same at two values of the coins that agree at the run's numbers. -/
theorem cut_congr {d : Due} (c c' : Cs d) (a n : Due)
    (hf : ∀ i, a.f ≤ i → i < a.f + n.f → cf c i = cf c' i)
    (he : ∀ i, a.e ≤ i → i < a.e + n.e → ce c i = ce c' i) : c.cut a n = c'.cut a n := by
  unfold Cs.cut
  by_cases h : a.f + n.f ≤ d.f ∧ a.e + n.e ≤ d.e
  · rw [dif_pos h, dif_pos h]
    refine congrArg some (cs_ext _ _ (funext fun i => ?_) (funext fun i => ?_))
    · have := hf (a.f + i.1) (Nat.le_add_right _ _) (Nat.add_lt_add_left i.2 _)
      unfold cf at this
      have hlt : a.f + i.1 < d.f := by have := h.1; have := i.2; omega
      rwa [dif_pos hlt, dif_pos hlt] at this
    · have := he (a.e + i.1) (Nat.le_add_right _ _) (Nat.add_lt_add_left i.2 _)
      unfold ce at this
      have hlt : a.e + i.1 < d.e := by have := h.2; have := i.2; omega
      rwa [dif_pos hlt, dif_pos hlt] at this
  · rw [dif_neg h, dif_neg h]

omit h1 h2 in
/-- cutAll at a list of entries is the same at two values of the coins that agree at the entries'
numbers, in both fields. -/
theorem cutAll_congr {d : Due} (c c' : Cs d) : ∀ es : List Ahead,
    (∀ i ∈ fAll es, cf c i = cf c' i) → (∀ i ∈ eAll es, ce c i = ce c' i) →
    cutAll c es = cutAll c' es
  | [], _, _ => rfl
  | e :: es, hf, he => by
    show (c.cut e.start e.count).bind _ = (c'.cut e.start e.count).bind _
    rw [cut_congr c c' e.start e.count
      (fun i h1 h2 => hf i (Finset.mem_union_left _ (Finset.mem_Ico.2 ⟨h1, h2⟩)))
      (fun i h1 h2 => he i (Finset.mem_union_left _ (Finset.mem_Ico.2 ⟨h1, h2⟩))),
      cutAll_congr c c' es (fun i h => hf i (Finset.mem_union_right _ h))
        fun i h => he i (Finset.mem_union_right _ h)]

/-- Proof of Spec.knownTie. The function is obtained by choice. -/
theorem knownTie : Spec.knownTie := by
  intro P ride Bk ord o p
  have hF : Function.FactorsThrough
      (fun c : Cs (dueR P ride) => cutAll c (Bk.knownBy ord o p))
      (fun c : Cs (dueR P ride) =>
        ((sender P ride).cut (knownN P ride Bk ord o p) (readC P ride c),
          (sender P ride).cutT (knownT P ride Bk ord o p) (readC P ride c))) := by
    intro c c' h
    have h1 : ∀ n ∈ namesOf P ride (eAll (Bk.knownBy ord o p)) (fAll (Bk.knownBy ord o p)),
        (readC P ride c).1 n = (readC P ride c').1 n :=
      fun n hn => congrFun (congrArg Prod.fst h) ⟨n, hn⟩
    have h2 : ∀ x ∈ tailsOf P ride (eAll (Bk.knownBy ord o p)) (fAll (Bk.knownBy ord o p)),
        (readC P ride c).2 x.1 x.2 = (readC P ride c').2 x.1 x.2 :=
      fun x hx => congrFun (congrArg Prod.snd h) ⟨x, hx⟩
    exact cutAll_congr c c' _ (fun i hi => cf_names _ _ c c' h1 h2 i hi)
      fun i hi => ce_names _ _ c c' h1 h2 i hi
  obtain ⟨back, hb⟩ := (Function.factorsThrough_iff _).1 hF
  exact ⟨back, fun c => congrFun hb c⟩

/-- If every entry of es is within the number of coins d, cutAll c es is some family of runs. -/
theorem cutAll_some {d : Due} (c : Cs d) : ∀ es : List Ahead,
    (∀ e ∈ es, e.start.f + e.count.f ≤ d.f ∧ e.start.e + e.count.e ≤ d.e) →
    ∃ v, cutAll c es = some v
  | [], _ => ⟨(), rfl⟩
  | e :: es, h => by
    obtain ⟨v, hv⟩ := cutAll_some c es fun e' he' => h e' (List.mem_cons_of_mem _ he')
    show ∃ v, (c.cut e.start e.count).bind _ = some v
    unfold Cs.cut
    rw [dif_pos (h e List.mem_cons_self), hv]
    exact ⟨_, rfl⟩

/-- Under MaskSpender or FoldSpender at o and p, a slot within the sizes whose coin, by field and
number, is among the coins that p spends is not in a tail. -/
theorem spent_inMsg {Bk : ProverCoinCounts} {ord : List Place} {o p : Addr}
    (h : MaskSpender P ride Bk ord o p ∨ FoldSpender P ride Bk ord o p) (k : ℕ) (y : Seat)
    (hy : y.ok P.codes (shapeAt P k) (ride k))
    (hin : inNos (eAll (Bk.spentBy o p)) (fAll (Bk.spentBy o p)) (y.inE (shapeAt P k))
      (y.no P ride k)) : inMsg y = true := by
  unfold inNos at hin
  rcases h with M | F
  · cases hE : y.inE (shapeAt P k)
    · rw [hE, M.noF] at hin
      simp at hin
    · rw [hE, if_pos rfl] at hin
      obtain ⟨k', _, hr, ha, hfree⟩ := M.free _ hin
      unfold freeNo at hfree
      obtain ⟨j, hj, e⟩ := Finset.mem_image.1 hfree
      have hy' : (Seat.mask j).ok P.codes (shapeAt P k') (ride k') := by
        show j < (stepsOf P.codes (shapeAt P k') (ride k')).mask
        have := free_lt _ _ _ j (Nat.pos_of_ne_zero ha) (Finset.mem_range.1 hj)
        simpa [stepsOf, hr] using this
      rw [(seat_inj P ride k k' y (.mask j) hy hy' hE (by rw [no_mask]; exact e.symm)).2]
      rfl
  · obtain ⟨k', R, e, _, hr, _, hsp, hc, hst, _⟩ := F.one
    cases hE : y.inE (shapeAt P k)
    · rw [hE, hsp] at hin
      simp [fAll, fOf, hc] at hin
    · rw [hE, if_pos rfl, hsp] at hin
      simp only [eAll, List.foldr_cons, List.foldr_nil, Finset.union_empty, eOf, hc, hst,
        Finset.mem_Ico] at hin
      obtain ⟨i, hi⟩ : ∃ i, y.no P ride k = maskStart P ride k' + i :=
        ⟨_, (Nat.add_sub_cancel' hin.1).symm⟩
      have hy' : (Seat.mask i).ok P.codes (shapeAt P k') (ride k') := by
        show i < (stepsOf P.codes (shapeAt P k') (ride k')).mask
        have : i < R.count := by omega
        simpa [stepsOf, hr] using this
      rw [(seat_inj P ride k k' y (.mask i) hy hy' hE (by rw [no_mask]; exact hi)).2]
      rfl

/-- Proof of Spec.spentTie. The function is obtained by choice. -/
theorem spentTie : Spec.spentTie := by
  intro P ride Bk ord o p _ hW h
  have hF : Function.FactorsThrough
      (fun c : Cs (dueR P ride) => cutAll c (Bk.spentBy o p))
      (fun c : Cs (dueR P ride) =>
        (sender P ride).cut (spentN P ride Bk o p) (readC P ride c)) := by
    intro c c' e
    have h1 : ∀ n ∈ namesOf P ride (eAll (Bk.spentBy o p)) (fAll (Bk.spentBy o p)),
        (readC P ride c).1 n = (readC P ride c').1 n := fun n hn => congrFun e ⟨n, hn⟩
    have h2 : ∀ x ∈ tailsOf P ride (eAll (Bk.spentBy o p)) (fAll (Bk.spentBy o p)),
        (readC P ride c).2 x.1 x.2 = (readC P ride c').2 x.1 x.2 := fun x hx => by
      exfalso
      have hm := spent_inMsg h x.1.1 (seatT P x.1 x.2.val).1 (seatT_ok P ride x.1 x.2)
        ((mem_tailsOf _ _ x).1 hx)
      obtain ⟨⟨k, v⟩, q⟩ := x
      rcases v with v | v <;> cases hm
    exact cutAll_congr c c' _ (fun i hi => cf_names _ _ c c' h1 h2 i hi)
      fun i hi => ce_names _ _ c c' h1 h2 i hi
  obtain ⟨back, hb⟩ := (Function.factorsThrough_iff _).1 hF
  refine ⟨fun v => (back v).getD default, fun c => ?_⟩
  obtain ⟨v, hv⟩ := cutAll_some c (Bk.spentBy o p) fun e he => hW e (.inl he)
  have e := congrFun hb c
  simp only [Function.comp] at e
  show cutAll c (Bk.spentBy o p) =
    some ((back ((sender P ride).cut (spentN P ride Bk o p) (readC P ride c))).getD default)
  rw [← e, hv]
  rfl

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.spentTie
#print axioms OnBytes.SendSim.At.cutAll_congr
#print axioms OnBytes.SendSim.At.knownTie
