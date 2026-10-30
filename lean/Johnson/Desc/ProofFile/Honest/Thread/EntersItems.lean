-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/EntersItems.lean: THE ITEMS THAT ARE OPEN AT THE FIRST CHAIN's
START, ONE BY ONE. `enters_head` (Honest/Thread/EntersHead.lean) leaves one heavy premise: every
item that is open at border 0 holds of the thread's witness, at every continuation. Here that
premise is cut: the open set at border 0 IS the library's `start` at the written links (by
unfolding): no mark, the stored table's pin, the (empty) pile, and for each link its relaxed
relation in four parts. "No mark" comes of the state; the stored table's pin holds at the thread's
own witness (`head_pinW`, Honest/Thread/HeadPinW.lean); the pile and the hundred parts stay
premises, EACH AT THE ONE ITEM, in `Thread.Items`' own form: the form in which the integer-model
thread hands in its `items_constr_at_thread`. General in the thread: items that hold one by one
hold together.

  `items_of_each`     general in the thread: one by one gives together
  `mem_start`         what lies in the library's `start`
  `head_opened_zero`  the open set at border 0 is `start` at the written links: by unfolding
  `head_items_start`  `enters_head`'s premise from: no mark; the pile; the parts one by one

Limits. Nothing shows that a part's sentence holds at any run. None is one of the library's goals.
This file proves nothing about soundness, completeness, hiding or any other property of the
protocol. The item `pinW` among the items that are open at the start is proved here through
`head_pinW` (Honest/Thread/HeadPinW.lean), which holds by `rfl`: at these parameters the decoder of
the stored table is a constant, so the item says nothing about the stored table, nor about the
committed weights: it is no step toward correctness of extraction.
-/
import Johnson.Desc.ProofFile.Honest.Thread.HeadPinW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

/-- **ITEMS THAT HOLD ONE BY ONE HOLD TOGETHER.** -/
theorem items_of_each {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb)
    {O : List T.ι} {k : Coins Bk} {s : S} {m : Mid W X} {E : Env}
    (h : ∀ i ∈ O, T.Items [i] k s m E) : T.Items O k s m E :=
  fun ds i hi => h i hi ds i (List.mem_singleton.2 rfl)

namespace FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.First (Item Part ModelPart start)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)

/-- What lies in the library's `start`. -/
theorem mem_start {links : List ModelPart} {i : Item} (hi : i ∈ start links) :
    i = .unmarked ∨ i = .pinW ∨ i = .pile ∨
      ∃ m sub p, links[m]? = some sub ∧ p ∈ [Part.idn, Part.lookCalls, Part.rider, Part.small] ∧
        i = .constr m p := by
  unfold start at hi
  rcases List.mem_append.1 hi with h3 | hf
  · simp at h3
    rcases h3 with e | e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
    · exact Or.inr (Or.inr (Or.inl e))
  · obtain ⟨x, hx, hix⟩ := List.mem_flatMap.1 hf
    have hx' : links[x.2]? = some x.1 := List.mem_zipIdx_iff_getElem?.1 hx
    refine Or.inr (Or.inr (Or.inr ?_))
    simp at hix
    rcases hix with e | e | e | e
    · exact ⟨x.2, x.1, .idn, hx', by simp, e⟩
    · exact ⟨x.2, x.1, .lookCalls, hx', by simp, e⟩
    · exact ⟨x.2, x.1, .rider, hx', by simp, e⟩
    · exact ⟨x.2, x.1, .small, hx', by simp, e⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- The open set at border 0 is the library's `start` at the written links. -/
theorem head_opened_zero :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened 0 =
      start P5J.At.links := rfl

/-- **THE ITEMS OPEN AT THE START, FROM: NO MARK; THE PILE; THE PARTS ONE BY ONE.** -/
theorem head_items_start {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hmark : s.failed = none)
    (hpile : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Items [Item.pile] k s
      m E)
    (hparts : ∀ l sub, P5J.At.links[l]? = some sub →
      ∀ p ∈ [Part.idn, Part.lookCalls, Part.rider, Part.small],
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Items [Item.constr l p] k s
          m E) :
    (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.Items
      ((lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.opened 0) k s m E := by
  refine items_of_each _ fun i hi => ?_
  rw [head_opened_zero] at hi
  rcases mem_start hi with e | e | e | ⟨l, sub, p, hl, hp, e⟩
  · subst e
    intro ds j hj
    obtain rfl := List.mem_singleton.1 hj
    exact hmark
  · subst e
    intro ds j hj
    obtain rfl := List.mem_singleton.1 hj
    exact head_pinW h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w _ _ _ k _
  · subst e
    exact hpile
  · subst e
    exact hparts l sub hl p hp

end FirstThread

end ProofFile.Honest

#print axioms ProofFile.Honest.items_of_each
#print axioms ProofFile.Honest.FirstThread.mem_start
#print axioms ProofFile.Honest.FirstThread.head_opened_zero
#print axioms ProofFile.Honest.FirstThread.head_items_start
