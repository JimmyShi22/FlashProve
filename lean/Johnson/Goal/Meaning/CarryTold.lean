-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/CarryTold.lean: THE THIRD INSTANCE of Johnson/Goal/Meaning/CarryDriver.lean's
Carried: a count of the verifier's state that a yes of a block raises by JUST WHAT THE BLOCK TELLS
in its own field "oracles" (the tenants under the roots that it declares), UNDER AN INVARIANT A OF
THE STATE, which is kept. General in the state's type, the count and A.

Why an invariant. A code switch's decision does not read what its block tells; what it sends is read
off the verifier's state. So "a yes adds what the block tells" is at that kind no sentence on the
block alone: it wants a premise on the state in front, and that premise must hold again at the next
block.
  toldMsgs b: ((b.oracles.flatten).map fun o => o.tenants.length).sum.
  StepOn A cnt b: (b's test on the plan · A s · a yes from s to s' ⇒ cnt s' = cnt s + toldMsgs b) ∧
      (A s · a yes ⇒ A s').
  KeptOn A cnt s t: cnt t = cnt s ∧ (A s → A t): for what a link runs and does not decide.
  toldMsgs_andThen. carried_told: **Carried (StepOn A cnt) (KeptOn A cnt).** It spends UnderP's
      clause on "oracles" and quiet's premise "tells no oracle message".
  foldBlocks_told: along a fold: every block has StepOn · every block passes its test on the plan ·
      A s · the fold's return r ⇒ cnt r.1 = cnt s + (bs.map toldMsgs).sum ∧ A r.1.
WITH BLOCKS SET APART. Marked P b: one of b's declared rounds has the mark P. StepAll cnt: StepOn at
no invariant. carried_or: **THE FOURTH INSTANCE: Carried (fun b => Marked P b ∨ StepAll cnt b)
(KeptOn (fun _ => True) cnt)**: the mark goes along every wrapper (they keep the declared rounds)
and into two blocks as one. told_at_take: at every cut k of a list all of whose blocks bear the mark
or have StepAll: OF THE MARKED BLOCKS AMONG THE FIRST k IT IS ASKED, AT THE FOLD's OWN TWO STATES
(the returns at the cuts j and j + 1), that the step adds what the block tells ⇒ cnt r.1 = cnt s +
((l.take k).map toldMsgs).sum.
FELLOW. foldBlocks_roots (Johnson/Desc/K12/Law/RootsFold.lean) is the like for the roots that the
rounds declare, without an invariant. A search of the theorems named foldBlocks_… or fold_… in this
file's cone finds no other that carries a weight a block; foldSteps and foldAt
(FoldStepsProofs.lean) take a relation on states alone.
OBJECT: any list of blocks. USER: Johnson/IMR/MsgsSeat.lean. LETTERS: T, Cl, A, cnt: free.


Compiled with the whole library.
Limits. Book-keeping. Nothing on soundness.
-/
import Johnson.Goal.Meaning.CarryDriver
import Johnson.Desc.ChainEndFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Carry

open VerifiableInference.Desc
open VerifiableInference.Desc.Keeps (Decides Fn FnCl)

variable {T Cl : Type}

/-- The oracle messages (tenants) that a block tells in its own field "oracles". -/
def toldMsgs (b : Block T Cl) : Nat := (b.oracles.flatten.map fun o => o.tenants.length).sum

/-- **Under an invariant A of the verifier's state: a yes of the block adds to the count just what
the block tells; and A is kept.** -/
def StepOn (A : T → Prop) (cnt : T → Nat) (b : Block T Cl) : Prop :=
  (b.planOk = true → ∀ (s s' : T) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
    A s → b.decide s rs gs = .ok s' → cnt s' = cnt s + toldMsgs b) ∧
  ∀ (s s' : T) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
    A s → b.decide s rs gs = .ok s' → A s'

/-- The count stays, and A is kept. -/
def KeptOn (A : T → Prop) (cnt : T → Nat) : T → T → Prop := fun s t => cnt t = cnt s ∧ (A s → A t)

theorem toldMsgs_andThen (n : String) (p q : Block T Cl) :
    toldMsgs (p.andThen n q) = toldMsgs p + toldMsgs q := by
  show ((p.oracles ++ q.oracles).flatten.map fun o => o.tenants.length).sum = _
  rw [List.flatten_append, List.map_append, List.sum_append]
  rfl

/-- **The third instance.** -/
theorem carried_told (A : T → Prop) (cnt : T → Nat) :
    Carried (Cl := Cl) (StepOn A cnt) (KeptOn A cnt) where
  refl _ := ⟨rfl, id⟩
  trans _ _ _ h₁ h₂ := ⟨h₂.1.trans h₁.1, fun ha => h₂.2 (h₁.2 ha)⟩
  under {c b} u W :=
    ⟨fun hp s s' rs gs ha h => by
      have e : toldMsgs c = toldMsgs b := by unfold toldMsgs; rw [u.2.2]
      rw [e]
      exact W.1 (u.2.1 hp) s s' rs gs ha (u.1.2 s rs gs s' h),
    fun s s' rs gs ha h => W.2 s s' rs gs ha (u.1.2 s rs gs s' h)⟩
  quiet {b} _ ho W :=
    ⟨fun _ s s' rs gs _ h => by
      have e : toldMsgs b = 0 := by unfold toldMsgs; rw [ho]; rfl
      rw [e, Nat.add_zero]
      exact (W s rs gs s' h).1,
    fun s s' rs gs ha h => (W s rs gs s' h).2 ha⟩
  andThen {n p q} W₁ W₂ :=
    ⟨fun hp s s' rs gs ha h => by
      have hp' : (p.planOk && q.planOk) = true := hp
      rw [Bool.and_eq_true] at hp'
      obtain ⟨m, h1, h2⟩ := Keeps.ebind_ok h
      rw [toldMsgs_andThen, W₂.1 hp'.2 _ _ _ _ (W₁.2 _ _ _ _ ha h1) h2, W₁.1 hp'.1 _ _ _ _ ha h1,
        Nat.add_assoc],
    fun s s' rs gs ha h => by
      obtain ⟨m, h1, h2⟩ := Keeps.ebind_ok h
      exact W₂.2 _ _ _ _ (W₁.2 _ _ _ _ ha h1) h2⟩

/-- **Along a fold.** (foldBlocks_roots is the like for the roots that the rounds declare.) -/
theorem foldBlocks_told (A : T → Prop) (cnt : T → Nat) (ft : Nat) : ∀ (bs : List (Block T Cl)),
    (∀ b ∈ bs, StepOn A cnt b) → (∀ b ∈ bs, b.planOk = true) →
    ∀ (s : T) (rs : List Fmt.RoundView) (cols : List OpenedColumn) (r : T × List Fmt.RoundView × List OpenedColumn), A s →
      foldBlocks ft bs s rs cols = .ok r → cnt r.1 = cnt s + (bs.map toldMsgs).sum ∧ A r.1 := by
  intro bs
  induction bs with
  | nil =>
    intro _ _ s rs cols r ha h
    simp only [foldBlocks, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, ha⟩
  | cons b l ih =>
    intro hb hp s rs cols r ha h
    simp only [foldBlocks] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i s' k hs
        obtain ⟨rs', gs', hd⟩ := ChainEnd.step_decide ft b s s' _ cols k hs
        have W := hb b List.mem_cons_self
        have e1 := W.1 (hp b List.mem_cons_self) _ _ _ _ ha hd
        obtain ⟨e2, a2⟩ := ih (fun x hx => hb x (List.mem_cons_of_mem _ hx))
          (fun x hx => hp x (List.mem_cons_of_mem _ hx)) _ _ _ _ (W.2 _ _ _ _ ha hd) h
        refine ⟨?_, a2⟩
        rw [e2, e1, List.map_cons, List.sum_cons, Nat.add_assoc]

/-! ## With blocks set apart by a mark on their declared rounds -/

/-- One of the block's declared rounds has the mark. -/
def Marked (P : Fmt.DeclaredRound → Prop) (b : Block T Cl) : Prop := ∃ r ∈ b.rounds, P r

/-- No invariant. -/
abbrev StepAll (cnt : T → Nat) (b : Block T Cl) : Prop := StepOn (fun _ => True) cnt b

/-- **The fourth instance: the block bears the mark, or a yes adds to the count what it tells.** The
mark goes along every wrapper (they keep the declared rounds) and into two blocks as one. -/
theorem carried_or (P : Fmt.DeclaredRound → Prop) (cnt : T → Nat) :
    Carried (Cl := Cl) (fun b => Marked P b ∨ StepAll cnt b) (KeptOn (fun _ => True) cnt) where
  refl := (carried_told (Cl := Cl) (fun _ => True) cnt).refl
  trans := (carried_told (Cl := Cl) (fun _ => True) cnt).trans
  under {c b} u W := W.elim (fun ⟨r, hr, h⟩ => Or.inl ⟨r, u.1.1 ▸ hr, h⟩)
    fun W => Or.inr ((carried_told (fun _ => True) cnt).under u W)
  quiet h0 ho W := Or.inr ((carried_told (fun _ => True) cnt).quiet h0 ho W)
  andThen {n p q} W₁ W₂ := by
    rcases W₁ with ⟨r, hr, h⟩ | W₁
    · exact Or.inl ⟨r, List.mem_append_left _ hr, h⟩
    · rcases W₂ with ⟨r, hr, h⟩ | W₂
      · exact Or.inl ⟨r, List.mem_append_right _ hr, h⟩
      · exact Or.inr ((carried_told (fun _ => True) cnt).andThen W₁ W₂)

/-- **At every cut of a list**: of the marked blocks it is asked, at the fold's own two states, that
the step adds what the block tells; of the others it is known. -/
theorem told_at_take (P : Fmt.DeclaredRound → Prop) (cnt : T → Nat) (ft : Nat) (l : List (Block T Cl))
    (hl : ∀ b ∈ l, Marked P b ∨ StepAll cnt b) (s : T) (rs : List Fmt.RoundView) (cols : List OpenedColumn) :
    ∀ (k : Nat), (∀ b ∈ l.take k, b.planOk = true) →
      (∀ (j : Nat) (b : Block T Cl), j < k → l[j]? = some b → Marked P b →
        ∀ r₀ r₁ : T × List Fmt.RoundView × List OpenedColumn, foldBlocks ft (l.take j) s rs cols = .ok r₀ →
          foldBlocks ft (l.take (j + 1)) s rs cols = .ok r₁ → cnt r₁.1 = cnt r₀.1 + toldMsgs b) →
      ∀ r : T × List Fmt.RoundView × List OpenedColumn, foldBlocks ft (l.take k) s rs cols = .ok r →
        cnt r.1 = cnt s + ((l.take k).map toldMsgs).sum
  | 0, _, _, r, h => by
    rw [List.take_zero] at h ⊢
    simp only [foldBlocks, Except.ok.injEq] at h
    subst h
    rfl
  | k + 1, hp, hM, r, h => by
    cases hb : l[k]? with
    | none =>
      have e : l.take (k + 1) = l.take k := by
        rw [List.take_add_one, hb]
        simp
      rw [e] at h hp ⊢
      exact told_at_take P cnt ft l hl s rs cols k hp
        (fun j b hj => hM j b (Nat.lt_succ_of_lt hj)) r h
    | some b =>
      have e : l.take (k + 1) = l.take k ++ [b] := by
        rw [List.take_add_one, hb]
        rfl
      have h' := h
      rw [e] at h'
      obtain ⟨u, r₁, c₁, g0, g1⟩ := Keeps.foldBlocks_split ft [b] _ _ _ _ _ h'
      have ih := told_at_take P cnt ft l hl s rs cols k
        (fun x hx => hp x (by rw [e]; exact List.mem_append_left _ hx))
        (fun j x hj => hM j x (Nat.lt_succ_of_lt hj)) _ g0
      have step : cnt r.1 = cnt u + toldMsgs b := by
        rcases hl b (List.mem_of_getElem? hb) with hm | W
        · exact hM k b (Nat.lt_succ_self k) hb hm _ _ g0 h
        · exact (foldBlocks_told (fun _ => True) cnt ft [b]
            (fun x hx => by rw [List.mem_singleton.1 hx]; exact W)
            (fun x hx => hp x (by rw [e]; exact List.mem_append_right _ hx)) u r₁ c₁ r trivial
            g1).1.trans (by simp)
      rw [e, List.map_append, List.sum_append, step, ih, Nat.add_assoc]
      simp

#print axioms carried_or
#print axioms told_at_take
#print axioms carried_told
#print axioms foldBlocks_told

end Meaning.Carry
