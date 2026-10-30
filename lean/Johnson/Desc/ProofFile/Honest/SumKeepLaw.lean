-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/SumKeepLaw.lean: the masked sumcheck's part with a kept state
(`keepPart`, Honest/SumKeep.lean) sends the messages of `sumPart` (Honest/Sum.lean) at the earlier
job, and leaves the state as it found it. Lemmas with their proofs, and the definitions that they
need.

How it relates to its neighbours. The lemmas are stated with `alone` and `stateFrom`
(Honest/SumLaw/Terms.lean, Honest/SumLaw/Plays.lean): the rounds of a part whose moves are played
alone, and the state after them. The lemmas of Honest/SumLaw/ about `sumPart` have
`alone (sumPart …) … = some …` as a hypothesis, so `alone_keep` carries them over by rewriting.
`alone_lift` (Honest/SumLaw/Lift.lean) is general in the part, so it covers a lifted `keepPart`.
What the part is handed before its rounds (`Seen`, Honest/Frame.lean: the rounds shown and the
columns opened) is a bound letter in every lemma that names it, the same value on both sides.

  0  `KeepJob.FaithfulOn`, `KeepJob.Faithful.on`   the hypothesis, asked only where a condition on
     the state before the part holds; `KeepJob.Faithful` is a case of it
  1  `take_app`, `drawnE_snoc`, `drawnE_length`, `varsAt`, `drop_length`, `varsAt_short`,
     `varsAt_snoc`, `varsAt_full`   the variables' challenges among a part's own challenges
  2  `Kept`, `keptAt_of`, `pass_fst`, `pass_last`, `pass_kept`   the invariant: the kept state is
     absent or is the one computed from the start; `KeepJob.pass` preserves it
  3  `AgreeAt`, `Agree`, `Agree.cons`, `Agree.head`, `Agree.tail`, `aloneFrom_agree`   moves that
     say the same at every state that satisfies the invariant, played alone
  4  `agree_first`, `agree_var`, `agree_Y`, `agree_ends`, `agree_vars`, `agree_all`   the moves of
     the two parts agree
  5  `keepPart_moves`, `alone_keep_on`, `alone_keep`   the messages are the same
  6  `stateFrom_pass`, `sumGs_rounds`, `state_keep`   the state after the part

Limits.
  * `alone_keep_on` and `alone_keep` start at a state without a kept state. At a state that holds
    some other value as its kept state nothing is proved.
  * The hypothesis `KeepJob.FaithfulOn` or `KeepJob.Faithful` has to be proved by whoever supplies
    the job. It is asked at every `Front`, so at every `Front.seen`, rounds and columns: it cannot
    hold of a job whose `round`, `inY` or `ends` depends on them where `Ok` holds. That `Ok` still
    holds before a later part, after more challenges, is not proved here.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.SumKeep
import Johnson.Desc.ProofFile.Honest.SumLaw.Said

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open OnBytes (E)

variable {W X K : Type}

/-- **The kept state gives what the earlier job computes, where `Ok` holds.** A definition, meant as
a hypothesis: `KeepJob.Faithful` (Honest/SumKeep.lean) with each of its three clauses asked only at
an input, challenges before the part and a passed-on value that satisfy `Ok`. It is for a job whose
`start` trusts something in what was passed on, for example tables that an earlier part has
computed. -/
structure KeepJob.FaithfulOn (J : KeepJob W X K) (Ok : W → List Fmt.Drawn → X → Prop) : Prop where
  round : ∀ (w : W) (f : Front X) (rs : List E), Ok w f.heard f.own →
    rs.length < J.base.shape.vs.length →
    J.round (J.madeAt w f.heard f.own rs) = J.base.round w f rs
  inY : ∀ (w : W) (f : Front X) (rs m : List E), Ok w f.heard f.own →
    rs.length = J.base.shape.vs.length →
    J.inY (J.madeAt w f.heard f.own rs) m = J.base.inY w f rs m
  ends : ∀ (w : W) (f : Front X) (rs : List E), Ok w f.heard f.own →
    rs.length = J.base.shape.vs.length →
    J.ends (J.madeAt w f.heard f.own rs) = J.base.ends w f rs

/-- `KeepJob.Faithful` is the case in which `Ok` always holds. -/
theorem KeepJob.Faithful.on {J : KeepJob W X K} (h : J.Faithful) :
    J.FaithfulOn fun _ _ _ => True :=
  ⟨fun w f rs _ hl => h.round w f rs hl, fun w f rs m _ hl => h.inY w f rs m hl,
    fun w f rs _ hl => h.ends w f rs hl⟩

end ProofFile.Honest

namespace ProofFile.Honest.Keep
open OnBytes (E zeroE)
open VerifiableInference.Desc.Part.MaskedSum (Var Ends)
open ProofFile.Honest.SumLaw

variable {V W X K : Type}

/-! ## 1 The variables' challenges -/

/-- The first entries of a list with something appended, where the list is long enough. -/
theorem take_app {α : Type} :
    ∀ (n : Nat) (a b : List α), n ≤ a.length → (a ++ b).take n = a.take n
  | 0, _, _, _ => rfl
  | n + 1, [], _, h => absurd h (Nat.not_succ_le_zero n)
  | n + 1, x :: a, b, h => congrArg (x :: ·) (take_app n a b (Nat.le_of_succ_le_succ h))

theorem drawnE_snoc (l : List Fmt.Drawn) (d : Fmt.Drawn) :
    drawnE (l ++ [d]) = drawnE l ++ [elemOf d] := by
  show (l ++ [d]).map elemOf = l.map elemOf ++ [elemOf d]
  exact List.map_append

theorem drawnE_length (l : List Fmt.Drawn) : (drawnE l).length = l.length := by
  rw [drawnE_eq, List.length_map]

/-- The variables' challenges among a part's own challenges `own`: the first, eps, is dropped, and
at most as many are taken as there are variables. -/
def varsAt (J : KeepJob W X K) (own : List Fmt.Drawn) : List E :=
  ((drawnE own).drop 1).take J.base.shape.vs.length

theorem drop_length (own : List Fmt.Drawn) : ((drawnE own).drop 1).length = own.length - 1 := by
  rw [List.length_drop, drawnE_length]

/-- Up to the round "PSC Y" nothing is cut. -/
theorem varsAt_short (J : KeepJob W X K) (own : List Fmt.Drawn)
    (h : own.length ≤ J.base.shape.vs.length + 1) : varsAt J own = (drawnE own).drop 1 := by
  have e : ((drawnE own).drop 1).length ≤ J.base.shape.vs.length := by
    rw [drop_length]
    omega
  exact List.take_of_length_le e

/-- One variable's challenge more. -/
theorem varsAt_snoc (J : KeepJob W X K) (own : List Fmt.Drawn) (d : Fmt.Drawn)
    (h0 : 0 < own.length) (h : own.length ≤ J.base.shape.vs.length) :
    varsAt J (own ++ [d]) = varsAt J own ++ [elemOf d] := by
  have e : (own ++ [d]).length ≤ J.base.shape.vs.length + 1 := by
    rw [List.length_append]
    exact Nat.succ_le_succ h
  rw [varsAt_short J (own ++ [d]) e, varsAt_short J own (Nat.le_succ_of_le h), drawnE_snoc]
  cases own with
  | nil => exact absurd h0 (Nat.lt_irrefl 0)
  | cons a l => rfl

/-- After all variables' challenges a further challenge changes nothing. -/
theorem varsAt_full (J : KeepJob W X K) (own : List Fmt.Drawn) (d : Fmt.Drawn)
    (h : J.base.shape.vs.length < own.length) : varsAt J (own ++ [d]) = varsAt J own := by
  unfold varsAt
  rw [drawnE_snoc]
  cases own with
  | nil => exact absurd h (Nat.not_lt_zero _)
  | cons a l =>
    have e : J.base.shape.vs.length ≤ (drawnE l).length := by
      rw [drawnE_length]
      exact Nat.le_of_lt_succ h
    show (drawnE l ++ [elemOf d]).take J.base.shape.vs.length =
      (drawnE l).take J.base.shape.vs.length
    exact take_app _ _ _ e

/-! ## 2 The invariant -/

/-- **The invariant.** `H`: the challenges before the part. `own`: the part's own challenges so far.
The kept state is absent, or it is the one computed from the start. -/
def Kept (J : KeepJob W X K) (w : W) (H : List Fmt.Drawn) (x : X) (own : List Fmt.Drawn)
    (k : Option K) : Prop :=
  k = none ∨ k = some (J.madeAt w H x (varsAt J own))

/-- Under the invariant a round reads the kept state computed from the start. -/
theorem keptAt_of (J : KeepJob W X K) (w : W) (H : List Fmt.Drawn) (x : X) (S : Seen)
    (own : List Fmt.Drawn) (k : Option K) (rs : List E) (hk : Kept J w H x own k)
    (hr : varsAt J own = rs) : J.keptAt w ⟨H, (x, k), S⟩ rs = J.madeAt w H x rs := by
  subst hr
  rcases hk with h | h
  · subst h
    rfl
  · subst h
    rfl

/-- No move changes the first component of the state. -/
theorem pass_fst (J : KeepJob W X K) (n : Nat) (t : State W (X × Option K)) :
    (J.pass n t).1 = t.own.1 := by
  by_cases h1 : (n + 1 == (scalarsOf J.base.shape).length) = true
  · have e : J.pass n t = (t.own.1, none) := if_pos h1
    exact (congrArg Prod.fst e).trans rfl
  · by_cases h2 : J.base.shape.vs.length < n
    · exact congrArg Prod.fst ((if_neg h1).trans (if_pos h2))
    · have e : J.pass n t = (t.own.1, _) := (if_neg h1).trans (if_neg h2)
      exact (congrArg Prod.fst e).trans rfl

/-- After the part's last round no kept state is passed on. -/
theorem pass_last (J : KeepJob W X K) (n : Nat) (t : State W (X × Option K))
    (h : n + 1 = (scalarsOf J.base.shape).length) : J.pass n t = (t.own.1, none) :=
  if_pos (beq_iff_eq.2 h)

/-- **`KeepJob.pass` preserves the invariant.** -/
theorem pass_kept (J : KeepJob W X K) (w : W) (H : List Fmt.Drawn) (x : X) (n : Nat)
    (own : List Fmt.Drawn) (d : Fmt.Drawn) (k : Option K) (ho : own.length = n)
    (hk : Kept J w H x own k) :
    ∃ k', J.pass n ⟨w, (H ++ own) ++ [d], (x, k)⟩ = (x, k') ∧ Kept J w H x (own ++ [d]) k' := by
  by_cases h1 : (n + 1 == (scalarsOf J.base.shape).length) = true
  · exact ⟨none, if_pos h1, Or.inl rfl⟩
  · by_cases h2 : J.base.shape.vs.length < n
    · refine ⟨k, (if_neg h1).trans (if_pos h2), ?_⟩
      rcases hk with h | h
      · exact Or.inl h
      · have e : J.base.shape.vs.length < own.length := by
          rw [ho]
          exact h2
        refine Or.inr ?_
        rw [h, varsAt_full J own d e]
    · have hn : n ≤ J.base.shape.vs.length := Nat.le_of_not_lt h2
      have e1 : ((H ++ own) ++ [d]).take (((H ++ own) ++ [d]).length - (n + 1)) = H := by
        rw [List.append_assoc, List.length_append, List.length_append, ho]
        show (H ++ (own ++ [d])).take (H.length + (n + 1) - (n + 1)) = H
        rw [Nat.add_sub_cancel, List.take_left']
        rfl
      have e2 : ∀ k₀ : Option K,
          State.lately (⟨w, (H ++ own) ++ [d], (x, k₀)⟩ : State W (X × Option K)) (n + 1) =
            own ++ [d] := by
        intro k₀
        show ((H ++ own) ++ [d]).drop (((H ++ own) ++ [d]).length - (n + 1)) = own ++ [d]
        rw [List.append_assoc, List.length_append, List.length_append, ho]
        show (H ++ (own ++ [d])).drop (H.length + (n + 1) - (n + 1)) = own ++ [d]
        rw [Nat.add_sub_cancel, List.drop_left']
        rfl
      have e3 : ∀ k₀ : Option K,
          State.lately (⟨w, (H ++ own) ++ [d], (x, k₀)⟩ : State W (X × Option K)) 1 = [d] := by
        intro k₀
        show ((H ++ own) ++ [d]).drop (((H ++ own) ++ [d]).length - 1) = [d]
        rw [List.length_append]
        show ((H ++ own) ++ [d]).drop ((H ++ own).length + 1 - 1) = [d]
        rw [Nat.add_sub_cancel, List.drop_left']
        rfl
      have e4 : (own ++ [d]).length ≤ J.base.shape.vs.length + 1 := by
        rw [List.length_append, ho]
        exact Nat.succ_le_succ hn
      have fresh : J.madeAt w H x ((drawnE (own ++ [d])).drop 1) =
          J.madeAt w H x (varsAt J (own ++ [d])) := by
        rw [varsAt_short J (own ++ [d]) e4]
      refine ⟨some (J.madeAt w H x (varsAt J (own ++ [d]))),
        ((if_neg h1).trans (if_neg h2)).trans ?_, Or.inr rfl⟩
      cases n with
      | zero =>
        show (x, some (J.madeAt w
          (((H ++ own) ++ [d]).take (((H ++ own) ++ [d]).length - (0 + 1))) x
          ((drawnE (State.lately (⟨w, (H ++ own) ++ [d], (x, k)⟩ : State W (X × Option K))
            (0 + 1))).drop 1))) = _
        rw [e1, e2 k, fresh]
      | succ m =>
        rcases hk with h | h
        · subst h
          show (x, some (J.madeAt w
            (((H ++ own) ++ [d]).take (((H ++ own) ++ [d]).length - (m + 1 + 1))) x
            ((drawnE (State.lately (⟨w, (H ++ own) ++ [d], (x, none)⟩ : State W (X × Option K))
              (m + 1 + 1))).drop 1))) = _
          rw [e1, e2 none, fresh]
        · subst h
          have p0 : 0 < own.length := by
            rw [ho]
            exact Nat.succ_pos m
          have p1 : own.length ≤ J.base.shape.vs.length := by
            rw [ho]
            exact hn
          show (x, some (J.bind (J.madeAt w H x (varsAt J own))
            ((drawnE (State.lately (⟨w, (H ++ own) ++ [d],
              (x, some (J.madeAt w H x (varsAt J own)))⟩ : State W (X × Option K)) 1)).headD
                zeroE))) = _
          rw [e3, varsAt_snoc J own d p0 p1]
          unfold KeepJob.madeAt
          rw [List.foldl_append]
          rfl

/-! ## 3 Moves that say the same under the invariant -/

/-- At every state that satisfies the invariant after `n` rounds of the part, `a` and `b` say the
same. `S`: what a part is handed before the part: the rounds shown and the columns opened (`Seen`,
Honest/Frame.lean). -/
def AgreeAt (J : KeepJob W X K) {name endName : String} (c : SumCoins name endName J.base) (w : W)
    (H : List Fmt.Drawn) (x : X) (S : Seen) (n : Nat)
    (a : SumCoins name endName J.job → Seen → State W (X × Option K) → List E)
    (b : SumCoins name endName J.base → Seen → State W X → List E) : Prop :=
  ∀ (own : List Fmt.Drawn) (shown : List Fmt.RoundView) (k : Option K), own.length = n →
    shown.length = n → Kept J w H x own k →
    a c (S.plus shown) ⟨w, H ++ own, (x, k)⟩ = b c (S.plus shown) ⟨w, H ++ own, x⟩

/-- Two lists agree position by position, the first position being round number `n`. -/
def Agree (J : KeepJob W X K) {name endName : String} (c : SumCoins name endName J.base) (w : W)
    (H : List Fmt.Drawn) (x : X) (S : Seen) : Nat →
    List (SumCoins name endName J.job → Seen → State W (X × Option K) → List E) →
    List (SumCoins name endName J.base → Seen → State W X → List E) → Prop
  | _, [], [] => True
  | n, a :: l₁, b :: l₂ => AgreeAt J c w H x S n a b ∧ Agree J c w H x S (n + 1) l₁ l₂
  | _, _, _ => False

section
variable {J : KeepJob W X K} {name endName : String} {c : SumCoins name endName J.base} {w : W}
  {H : List Fmt.Drawn} {x : X} {S : Seen} {n : Nat}
  {a : SumCoins name endName J.job → Seen → State W (X × Option K) → List E}
  {b : SumCoins name endName J.base → Seen → State W X → List E}
  {l₁ : List (SumCoins name endName J.job → Seen → State W (X × Option K) → List E)}
  {l₂ : List (SumCoins name endName J.base → Seen → State W X → List E)}

theorem Agree.cons (h₁ : AgreeAt J c w H x S n a b) (h₂ : Agree J c w H x S (n + 1) l₁ l₂) :
    Agree J c w H x S n (a :: l₁) (b :: l₂) :=
  And.intro h₁ h₂

theorem Agree.head (h : Agree J c w H x S n (a :: l₁) (b :: l₂)) : AgreeAt J c w H x S n a b :=
  And.left (b := Agree J c w H x S (n + 1) l₁ l₂) h

theorem Agree.tail (h : Agree J c w H x S n (a :: l₁) (b :: l₂)) :
    Agree J c w H x S (n + 1) l₁ l₂ :=
  And.right (a := AgreeAt J c w H x S n a b) h

end

/-- **Lists that agree, played alone, show the same rounds.** -/
theorem aloneFrom_agree (J : KeepJob W X K) {name endName : String}
    (c : SumCoins name endName J.base) (w : W) (H : List Fmt.Drawn) (x : X) (S : Seen) :
    ∀ (l₁ : List (SumCoins name endName J.job → Seen → State W (X × Option K) → List E))
      (l₂ : List (SumCoins name endName J.base → Seen → State W X → List E)) (n : Nat)
      (own : List Fmt.Drawn) (shown : List Fmt.RoundView) (k : Option K) (ds : List Fmt.Drawn),
      Agree J c w H x S n l₁ l₂ → own.length = n → shown.length = n → Kept J w H x own k →
      aloneFrom (C := SumCoins name endName J.base) c (withPass J.pass n (l₁.map mvOf))
          ⟨w, H ++ own, (x, k)⟩ (S.plus shown) ds =
        aloneFrom c (l₂.map mvOf) ⟨w, H ++ own, x⟩ (S.plus shown) ds
  | [], [], _, _, _, _, [], _, _, _, _ => rfl
  | [], [], _, _, _, _, _ :: _, _, _, _, _ => rfl
  | _ :: _, _ :: _, _, _, _, _, [], _, _, _, _ => rfl
  | a :: l₁, b :: l₂, n, own, shown, k, d :: ds, hA, ho, hs, hk => by
    obtain ⟨k', hp, hk'⟩ := pass_kept J w H x n own d k ho hk
    have e := hA.head own shown k ho hs hk
    have o' : (own ++ [d]).length = n + 1 := by
      rw [List.length_append, ho]
      rfl
    have s' : (shown ++ [rvSaid (b c (S.plus shown) ⟨w, H ++ own, x⟩) d]).length = n + 1 := by
      rw [List.length_append, hs]
      rfl
    show (aloneFrom (C := SumCoins name endName J.base) c (withPass J.pass (n + 1) (l₁.map mvOf))
        ⟨w, (H ++ own) ++ [d], J.pass n ⟨w, (H ++ own) ++ [d], (x, k)⟩⟩
        ((S.plus shown).plus [rvSaid (a c (S.plus shown) ⟨w, H ++ own, (x, k)⟩) d]) ds).map
          (rvSaid (a c (S.plus shown) ⟨w, H ++ own, (x, k)⟩) d :: ·) =
      (aloneFrom c (l₂.map mvOf) ⟨w, (H ++ own) ++ [d], x⟩
        ((S.plus shown).plus [rvSaid (b c (S.plus shown) ⟨w, H ++ own, x⟩) d]) ds).map
          (rvSaid (b c (S.plus shown) ⟨w, H ++ own, x⟩) d :: ·)
    rw [hp, e, List.append_assoc H, Seen.plus_plus S,
      aloneFrom_agree J c w H x S l₁ l₂ (n + 1) (own ++ [d])
        (shown ++ [rvSaid (b c (S.plus shown) ⟨w, H ++ own, x⟩) d]) k' ds hA.tail o' s' hk']
  | [], _ :: _, _, _, _, _, _, hA, _, _, _ => False.elim hA
  | _ :: _, [], _, _, _, _, _, hA, _, _, _ => False.elim hA

/-! ## 4 The two parts' moves agree -/

theorem agree_first (J : KeepJob W X K) {name endName : String} (c : SumCoins name endName J.base)
    (w : W) (H : List Fmt.Drawn) (x : X) (S : Seen) :
    AgreeAt J c w H x S 0 (askG name endName J.job (saidFirst J.job) 0)
      (askG name endName J.base (saidFirst J.base) 0) := by
  intro _ _ _ _ _ _
  rfl

theorem agree_var (J : KeepJob W X K) {Ok : W → List Fmt.Drawn → X → Prop} (hJ : J.FaithfulOn Ok)
    {name endName : String} (c : SumCoins name endName J.base) (w : W) (H : List Fmt.Drawn) (x : X)
    (hOk : Ok w H x) (S : Seen) (i : Nat) (hi : i < J.base.shape.vs.length) :
    AgreeAt J c w H x S (i + 1) (askG name endName J.job (saidVar J.job i) (i + 1))
      (askG name endName J.base (saidVar J.base i) (i + 1)) := by
  intro own shown k ho hs hk
  have q1 : own.length ≤ J.base.shape.vs.length + 1 := by
    rw [ho]
    omega
  have q2 : ((drawnE own).drop 1).length < J.base.shape.vs.length := by
    rw [drop_length, ho]
    omega
  have e : J.round (J.keptAt w ⟨H, (x, k), S⟩ ((drawnE own).drop 1)) =
      J.base.round w ⟨H, x, S⟩ ((drawnE own).drop 1) := by
    rw [keptAt_of J w H x S own k ((drawnE own).drop 1) hk (varsAt_short J own q1)]
    exact hJ.round w ⟨H, x, S⟩ _ hOk q2
  refine (askG_at name endName J.job (saidVar J.job i) (i + 1) c w H own (x, k) S shown ho hs).trans
    (Eq.trans ?_
      (askG_at name endName J.base (saidVar J.base i) (i + 1) c w H own x S shown ho hs).symm)
  exact congrArg (fun z =>
    sentOfL ((J.base.callAt w ⟨H, x, S⟩).all.getD i (.plain 0))
      (addL (hAt (sharesOf J.base.shape.lead (J.base.callAt w ⟨H, x, S⟩).all (firstRun c))
        ((drawnE own).drop 1) zeroE) (scaleL ((drawnE own).headD zeroE) z))) e

theorem agree_Y (J : KeepJob W X K) {Ok : W → List Fmt.Drawn → X → Prop} (hJ : J.FaithfulOn Ok)
    {name endName : String} (c : SumCoins name endName J.base) (w : W) (H : List Fmt.Drawn) (x : X)
    (hOk : Ok w H x) (S : Seen) (en : Ends) :
    AgreeAt J c w H x S (J.base.shape.vs.length + 1)
      (askG name endName J.job (saidY J.job en) (J.base.shape.vs.length + 1))
      (askG name endName J.base (saidY J.base en) (J.base.shape.vs.length + 1)) := by
  intro own shown k ho hs hk
  have q2 : ((drawnE own).drop 1).length = J.base.shape.vs.length := by
    rw [drop_length, ho, Nat.add_sub_cancel]
  have e : J.inY (J.keptAt w ⟨H, (x, k), S⟩ ((drawnE own).drop 1)) (endRun c) =
      J.base.inY w ⟨H, x, S⟩ ((drawnE own).drop 1) (endRun c) := by
    rw [keptAt_of J w H x S own k ((drawnE own).drop 1) hk
      (varsAt_short J own (Nat.le_of_eq ho))]
    exact hJ.inY w ⟨H, x, S⟩ _ _ hOk q2
  refine (askG_at name endName J.job (saidY J.job en) (J.base.shape.vs.length + 1) c w H own (x, k)
    S shown ho hs).trans (Eq.trans ?_
      (askG_at name endName J.base (saidY J.base en) (J.base.shape.vs.length + 1) c w H own x S
        shown ho hs).symm)
  exact congrArg (fun z =>
    sentOfL (.point zeroE (en.dY + 1))
      (addL (hAt (sharesOf J.base.shape.lead (J.base.callAt w ⟨H, x, S⟩).all (firstRun c))
        ((drawnE own).drop 1) zeroE) (scaleL ((drawnE own).headD zeroE) z))) e

theorem agree_ends (J : KeepJob W X K) {Ok : W → List Fmt.Drawn → X → Prop}
    (hJ : J.FaithfulOn Ok) {name endName : String} (c : SumCoins name endName J.base) (w : W)
    (H : List Fmt.Drawn) (x : X) (hOk : Ok w H x) (S : Seen) (en : Ends) :
    AgreeAt J c w H x S (J.base.shape.vs.length + 2)
      (askG name endName J.job (saidEnds J.job en) (J.base.shape.vs.length + 2))
      (askG name endName J.base (saidEnds J.base en) (J.base.shape.vs.length + 2)) := by
  intro own shown k ho hs hk
  have q2 : (varsAt J own).length = J.base.shape.vs.length := by
    unfold varsAt
    rw [List.length_take, drop_length, ho]
    exact Nat.min_eq_left (by omega)
  have e : J.ends (J.keptAt w ⟨H, (x, k), S⟩ (varsAt J own)) =
      J.base.ends w ⟨H, x, S⟩ (varsAt J own) := by
    rw [keptAt_of J w H x S own k (varsAt J own) hk rfl]
    exact hJ.ends w ⟨H, x, S⟩ _ hOk q2
  refine (askG_at name endName J.job (saidEnds J.job en) (J.base.shape.vs.length + 2) c w H own
    (x, k) S shown ho hs).trans (Eq.trans ?_
      (askG_at name endName J.base (saidEnds J.base en) (J.base.shape.vs.length + 2) c w H own x S
        shown ho hs).symm)
  exact congrArg (fun z =>
    addL (padTo en.n z) (scaleL ((drawnE own).getLastD zeroE) (padTo en.n (endRun c)))) e

/-- The variables' moves, followed by lists that agree. -/
theorem agree_vars (J : KeepJob W X K) {name endName : String} (c : SumCoins name endName J.base)
    (w : W) (H : List Fmt.Drawn) (x : X) (S : Seen) (nv : Nat)
    (F₁ : Nat → SumCoins name endName J.job → Seen → State W (X × Option K) → List E)
    (F₂ : Nat → SumCoins name endName J.base → Seen → State W X → List E)
    (hF : ∀ i, i < nv → AgreeAt J c w H x S (i + 1) (F₁ i) (F₂ i))
    (t₁ : List (SumCoins name endName J.job → Seen → State W (X × Option K) → List E))
    (t₂ : List (SumCoins name endName J.base → Seen → State W X → List E))
    (ht : Agree J c w H x S (nv + 1) t₁ t₂) :
    ∀ (m s : Nat), s + m = nv →
      Agree J c w H x S (s + 1) ((List.range' s m).map F₁ ++ t₁) ((List.range' s m).map F₂ ++ t₂)
  | 0, s, h => by
    have e : s = nv := h
    rw [e]
    exact ht
  | m + 1, s, h => by
    have r := agree_vars J c w H x S nv F₁ F₂ hF t₁ t₂ ht m (s + 1) (by omega)
    exact Agree.cons (hF s (by omega)) r

/-- **The moves of the two parts agree.** -/
theorem agree_all (J : KeepJob W X K) {Ok : W → List Fmt.Drawn → X → Prop} (hJ : J.FaithfulOn Ok)
    {name endName : String} (c : SumCoins name endName J.base) (w : W) (H : List Fmt.Drawn) (x : X)
    (hOk : Ok w H x) (S : Seen) :
    Agree J c w H x S 0 (sumGs name endName J.job) (sumGs name endName J.base) := by
  have ht : Agree J c w H x S (J.base.shape.vs.length + 1)
      ((J.base.shape.ends.map fun e =>
        [askG name endName J.job (saidY J.job e) (J.base.shape.vs.length + 1),
          askG name endName J.job (saidEnds J.job e) (J.base.shape.vs.length + 2)]).getD [])
      ((J.base.shape.ends.map fun e =>
        [askG name endName J.base (saidY J.base e) (J.base.shape.vs.length + 1),
          askG name endName J.base (saidEnds J.base e) (J.base.shape.vs.length + 2)]).getD []) := by
    cases J.base.shape.ends with
    | none => exact True.intro
    | some en =>
      exact Agree.cons (agree_Y J hJ c w H x hOk S en)
        (Agree.cons (l₁ := []) (l₂ := []) (agree_ends J hJ c w H x hOk S en) True.intro)
  have hv := agree_vars J c w H x S J.base.shape.vs.length
    (fun i => askG name endName J.job (saidVar J.job i) (i + 1))
    (fun i => askG name endName J.base (saidVar J.base i) (i + 1))
    (fun i hi => agree_var J hJ c w H x hOk S i hi) _ _ ht J.base.shape.vs.length 0 (Nat.zero_add _)
  rw [← List.range_eq_range'] at hv
  exact Agree.cons (agree_first J c w H x S) hv

/-! ## 5 The messages are the same -/

/-- The part's moves: what `sumPart` at `KeepJob.job` says, with `KeepJob.pass`. -/
theorem keepPart_moves (name endName : String) (J : KeepJob W X K) :
    (keepPart (V := V) name endName J).moves =
      withPass J.pass 0 ((sumGs name endName J.job).map mvOf) := by
  show withPass J.pass 0 (sumPart (V := V) name endName J.job).moves = _
  rw [sumPart_moves]
  rfl

/-- **The part with a kept state shows the rounds of `sumPart` at the earlier job**, at a state
before the part that satisfies `Ok`. -/
theorem alone_keep_on (name endName : String) (J : KeepJob W X K)
    (Ok : W → List Fmt.Drawn → X → Prop) (hJ : J.FaithfulOn Ok) (c : SumCoins name endName J.base)
    (w : W) (h : List Fmt.Drawn) (x : X) (hOk : Ok w h x) (seen : Seen)
    (ds : List Fmt.Drawn) :
    alone (keepPart (V := V) name endName J) c ⟨w, h, (x, none)⟩ seen ds =
      alone (sumPart (V := V) name endName J.base) c ⟨w, h, x⟩ seen ds := by
  have e := aloneFrom_agree J c w h x seen (sumGs name endName J.job) (sumGs name endName J.base) 0
    [] [] none ds (agree_all J hJ c w h x hOk seen) rfl rfl (Or.inl rfl)
  rw [List.append_nil, Seen.plus_nil] at e
  show aloneFrom (C := SumCoins name endName J.base) c (keepPart (V := V) name endName J).moves
      ⟨w, h, (x, none)⟩ seen ds =
    aloneFrom (C := SumCoins name endName J.base) c (sumPart (V := V) name endName J.base).moves
      ⟨w, h, x⟩ seen ds
  rw [keepPart_moves, sumPart_moves]
  exact e

/-- **The same under `KeepJob.Faithful`**, at every state before the part. -/
theorem alone_keep (name endName : String) (J : KeepJob W X K) (hJ : J.Faithful)
    (c : SumCoins name endName J.base) (w : W) (h : List Fmt.Drawn) (x : X) (seen : Seen)
    (ds : List Fmt.Drawn) :
    alone (keepPart (V := V) name endName J) c ⟨w, h, (x, none)⟩ seen ds =
      alone (sumPart (V := V) name endName J.base) c ⟨w, h, x⟩ seen ds :=
  alone_keep_on name endName J (fun _ _ _ => True) hJ.on c w h x True.intro seen ds

/-! ## 6 The state after the part -/

/-- Moves with `KeepJob.pass`, the last of which is the part's last: after them the first component
is unchanged and no kept state is left. -/
theorem stateFrom_pass (J : KeepJob W X K) {C : Type} :
    ∀ (l : List (Move C W (X × Option K))) (n : Nat) (t : State W (X × Option K))
      (ds : List Fmt.Drawn), l.length = ds.length →
      n + l.length = (scalarsOf J.base.shape).length → (l = [] → t.own.2 = none) →
      stateFrom (withPass J.pass n l) t ds = ⟨t.input, t.heard ++ ds, (t.own.1, none)⟩
  | [], _, ⟨i, hd, (p, q)⟩, [], _, _, h0 => by
    have e : q = none := h0 rfl
    subst e
    show (⟨i, hd, (p, none)⟩ : State W (X × Option K)) = ⟨i, hd ++ [], (p, none)⟩
    rw [List.append_nil]
  | mv :: l, n, t, d :: ds, hl, hn, _ => by
    have a1 : l.length = ds.length := by
      simp only [List.length_cons] at hl
      omega
    have a2 : n + 1 + l.length = (scalarsOf J.base.shape).length := by
      simp only [List.length_cons] at hn
      omega
    have a3 : l = [] → (J.pass n ⟨t.input, t.heard ++ [d], t.own⟩).2 = none := by
      intro e
      subst e
      rw [pass_last J n _ hn]
    show stateFrom (withPass J.pass (n + 1) l)
      ⟨t.input, t.heard ++ [d], J.pass n ⟨t.input, t.heard ++ [d], t.own⟩⟩ ds = _
    rw [stateFrom_pass J l (n + 1)
      ⟨t.input, t.heard ++ [d], J.pass n ⟨t.input, t.heard ++ [d], t.own⟩⟩ ds a1 a2 a3]
    show (⟨t.input, (t.heard ++ [d]) ++ ds,
      ((J.pass n ⟨t.input, t.heard ++ [d], t.own⟩).1, none)⟩ : State W (X × Option K)) = _
    rw [pass_fst, List.append_assoc]
    rfl
  | [], _, _, _ :: _, hl, _, _ => by
    simp only [List.length_cons, List.length_nil] at hl
    omega
  | _ :: _, _, _, [], hl, _, _ => by
    simp only [List.length_cons, List.length_nil] at hl
    omega

/-- The part has as many moves as its call has rounds. -/
theorem sumGs_rounds (name endName : String) (J : SumJob W X) :
    (sumGs name endName J).length = (scalarsOf J.shape).length := by
  unfold sumGs scalarsOf
  cases J.shape.ends with
  | none =>
    simp only [List.length_append, List.length_map, List.length_range]
    rfl
  | some e =>
    simp only [List.length_append, List.length_map, List.length_range]
    rfl

/-- **The part leaves the state as it found it**, with its own challenges heard. -/
theorem state_keep (name endName : String) (J : KeepJob W X K) (w : W) (h : List Fmt.Drawn) (x : X)
    (ds : List Fmt.Drawn) (hl : ds.length = (scalarsOf J.base.shape).length) :
    stateFrom (keepPart (V := V) name endName J).moves ⟨w, h, (x, none)⟩ ds =
      ⟨w, h ++ ds, (x, none)⟩ := by
  have hg : ((sumGs name endName J.job).map mvOf).length = (scalarsOf J.base.shape).length := by
    rw [List.length_map]
    exact sumGs_rounds name endName J.job
  rw [keepPart_moves]
  exact stateFrom_pass J ((sumGs name endName J.job).map mvOf) 0 ⟨w, h, (x, none)⟩ ds
    (hg.trans hl.symm) ((Nat.zero_add _).trans hg) (fun _ => rfl)

end ProofFile.Honest.Keep

#print axioms ProofFile.Honest.KeepJob.Faithful.on
#print axioms ProofFile.Honest.Keep.take_app
#print axioms ProofFile.Honest.Keep.drawnE_snoc
#print axioms ProofFile.Honest.Keep.drawnE_length
#print axioms ProofFile.Honest.Keep.drop_length
#print axioms ProofFile.Honest.Keep.varsAt_short
#print axioms ProofFile.Honest.Keep.varsAt_snoc
#print axioms ProofFile.Honest.Keep.varsAt_full
#print axioms ProofFile.Honest.Keep.keptAt_of
#print axioms ProofFile.Honest.Keep.pass_fst
#print axioms ProofFile.Honest.Keep.pass_last
#print axioms ProofFile.Honest.Keep.pass_kept
#print axioms ProofFile.Honest.Keep.Agree.cons
#print axioms ProofFile.Honest.Keep.Agree.head
#print axioms ProofFile.Honest.Keep.Agree.tail
#print axioms ProofFile.Honest.Keep.aloneFrom_agree
#print axioms ProofFile.Honest.Keep.agree_first
#print axioms ProofFile.Honest.Keep.agree_var
#print axioms ProofFile.Honest.Keep.agree_Y
#print axioms ProofFile.Honest.Keep.agree_ends
#print axioms ProofFile.Honest.Keep.agree_vars
#print axioms ProofFile.Honest.Keep.agree_all
#print axioms ProofFile.Honest.Keep.keepPart_moves
#print axioms ProofFile.Honest.Keep.alone_keep_on
#print axioms ProofFile.Honest.Keep.alone_keep
#print axioms ProofFile.Honest.Keep.stateFrom_pass
#print axioms ProofFile.Honest.Keep.sumGs_rounds
#print axioms ProofFile.Honest.Keep.state_keep
#print axioms ProofFile.Honest.KeepJob.FaithfulOn
#print axioms ProofFile.Honest.Keep.varsAt
#print axioms ProofFile.Honest.Keep.Kept
#print axioms ProofFile.Honest.Keep.AgreeAt
#print axioms ProofFile.Honest.Keep.Agree
