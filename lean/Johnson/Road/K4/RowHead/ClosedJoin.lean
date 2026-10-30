-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/RowHead/ClosedJoin.lean: FROM A TEST AT CLOSED VALUES TO THE SAME TEST AT
withPlans, AT ALL LETTERS.

What is here. plans_closed: a test f holds at withPlans v pub sc rope
(Johnson/Road/K4/RowHead/Twins.lean) if it holds at afterN (ClosedAt.lean) at all letters.
after_letters: it holds at afterN at all letters if it holds there at closed values and is blind to
the letters. front_blind: the test "the listing front returns at the plan's value", at one group, is
blind to them. Lemmas on variables: cases on what a maker returns, and calls. What they call: that
the first, the fifth and the sixth maker store the letters and read none
(Johnson/Road/K4/C/TwinLetters.lean); the second and the third are passed in after_letters by
unfolding: of the layout they get its calls and the numbers lidb and lmb; no statement says it of
them; that the listing front returns at the letters just where it returns without them
(C/FrontLetters.lean); that the scan has the numerals (ClosedTies.lean); closedSizes and weightsAt
(ClosedAt.lean).

  `onOk_dep`, `onOk_in`, `onOk_two`, `num_two`   tests at returned values.
  `all_two`   a test at 0 and 1.
  `after_letters`, `front_blind`   from closed values to all letters; front's test is blind.
  `sizes_letters`   two sizes and a switch of the first maker's return, at all three constants.
  `lk_same`, `ws_ref`, `at_weights`   the fourth maker.
  **`plans_closed`**   from afterN at all three constants and all layouts of the weights to
      withPlans, for any test. The title's sentence is after_letters and plans_closed together, for
      a test that is blind to the letters; the caller joins them.

Limits. Only for the parameter files whose scan is Pv v at some eight free numbers v (the full-size
model). That a test holds at closed values is not shown here.
No property is claimed.
-/
import Johnson.Road.K4.RowHead.ClosedTies
import Johnson.Road.K4.C.FrontLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.Closed
open OnBytes OnBytes.Model OnBytes.Model.Layer
open OnBytes.Road.K4 (onOk Pv clOf withPlans)
open OnBytes.Road.K4.C (setP onOk_inv onOk_go base_letters pub_letters plans_letters
  frontB_letters)
open OnBytes.Desc.First.K4.Total (frontB)

/-- A test behind a maker, from a family of tests and one more test at what it returns. -/
theorem onOk_dep {ε α β : Type} {x : Except ε α} {P : β → α → Bool} {S T : α → Bool}
    (A : ∀ b, onOk x (P b) = true) (B : onOk x S = true)
    (H : ∀ a, (∀ b, P b a = true) → S a = true → T a = true) : onOk x T = true := by
  cases x with
  | error e => exact B
  | ok a => exact H a A B

/-- The same from the family alone. -/
theorem onOk_in {ε α β : Type} {x : Except ε α} {P : β → α → Bool} {T : α → Bool}
    (A : ∀ b, onOk x (P b) = true) (b0 : β)
    (H : ∀ a, (∀ b, P b a = true) → T a = true) : onOk x T = true := by
  cases x with
  | error e => exact A b0
  | ok a => exact H a A

/-- A test at a returned value holds of a test that two others give, if it holds of each. -/
theorem onOk_two {ε α : Type} {x : Except ε α} {f1 f2 h : α → Bool}
    (H : ∀ a, f1 a = true → f2 a = true → h a = true) (h1 : onOk x f1 = true)
    (h2 : onOk x f2 = true) : onOk x h = true := by
  cases x with
  | error e => exact h1
  | ok a => exact H a h1 h2

/-- onOk_two, carried through afterN's five makers. -/
theorem num_two {e1 e2 eF : Nat} {pub : Array Nat} {sc : Layer.Scales} {rope : Array Nat}
    {W : WsLay} {f1 f2 h : Pub → Array HPlan2 → Bool}
    (H : ∀ L G, f1 L G = true → f2 L G = true → h L G = true)
    (h1 : afterN e1 e2 eF pub sc rope W f1 = true)
    (h2 : afterN e1 e2 eF pub sc rope W f2 = true) : afterN e1 e2 eF pub sc rope W h = true :=
  onOk_two (fun _ => onOk_two fun _ => onOk_two fun _ => onOk_two fun L =>
    onOk_two fun G => H L G) h1 h2

/-- A test at the numbers below 2. -/
theorem all_two {p : Nat → Bool} (h0 : p 0 = true) (h1 : p 1 = true) :
    (List.range 2).all p = true := by
  show (p 0 && (p 1 && true)) = true
  rw [h0, h1]
  rfl

/-- **From closed values to all letters.** hf: the test is blind to the letters. -/
theorem after_letters {f : Pub → Array HPlan2 → Bool} (e1 e2 eF : Nat) (pub pub0 : Array Nat)
    (sc sc0 : Scales) (rope rope0 : Array Nat) (W W0 : WsLay)
    (hf : ∀ L G, f (setP L e1 e2 eF pub sc rope W) G = f L G)
    (h : afterN 0 0 0 pub0 sc0 rope0 W0 f = true) : afterN e1 e2 eF pub sc rope W f = true := by
  unfold afterN at h ⊢
  obtain ⟨y0, hb, h⟩ := onOk_inv h
  obtain ⟨fo, hfo, h⟩ := onOk_inv h
  obtain ⟨kbm, hk, h⟩ := onOk_inv h
  obtain ⟨L, hL, h⟩ := onOk_inv h
  obtain ⟨G, hG, h⟩ := onOk_inv h
  exact onOk_go (base_letters hb e1 e2 eF) (onOk_go (a := fo) hfo (onOk_go (a := kbm) hk
    (onOk_go (pub_letters hL e1 e2 eF pub sc rope W)
      (onOk_go ((plans_letters L e1 e2 eF pub sc rope W).trans hG) ((hf L G).trans h)))))

/-- The test of front_free_at (FrontFreeK.lean), at one group, is blind to the letters. -/
theorem front_blind (g : Nat) (e1 e2 eF : Nat) (pub : Array Nat) (sc : Scales) (rope : Array Nat)
    (W : WsLay) (L : Pub) (G : Array HPlan2) :
    ((G[g]?).any fun hp => frontB false (setP L e1 e2 eF pub sc rope W) hp g
      (setP L e1 e2 eF pub sc rope W).y.fo) =
      (G[g]?).any fun hp => frontB false L hp g L.y.fo := by
  simp only [frontB_letters]

/-- Two sizes and a switch of the first maker's return, at all three constants: from the closed fact
and the law that the maker stores the constants and reads none. -/
theorem sizes_letters (e1 e2 eF : Nat) :
    onOk (baseNoStops (shapeL e1 e2 eF) VerifierAndGoals.Lines.callsRef) (fun y0 =>
      y0.dkv == 1024 && y0.dq == 5120 && y0.h.p3) = true := by
  obtain ⟨y0, hb, h⟩ := onOk_inv closedSizes
  exact onOk_go (base_letters hb e1 e2 eF) h

/-- A layout with its own number of column bits laid in anew is itself. -/
theorem lk_same {W : WsLay} {k : Nat} (h : W.lk = k) : ({ W with lk := k } : WsLay) = W := by
  subst h
  rfl

/-- The shape of the weights with the layout's two numbers laid in is shapeRef. -/
theorem ws_ref {a b : Nat} (ha : a = 1024) (hb : b = 5120) :
    ({ D := 2048, L := 48, d := 5120, dh := 128, dkv := a, dq := b, f := 16384, fe := 8192,
       NE := 128, V := 202048 } : WsShape) = shapeRef := by
  subst ha hb
  rfl

/-- **The fourth maker**: a test behind it holds if it holds at every layout with the asked number
of column bits and the maker is called at shapeRef, true and 18. -/
theorem at_weights {s : WsShape} {p3 : Bool} {lkW : Nat} {R : WsLay → Bool}
    (A : ∀ W : WsLay, R { W with lk := lkW } = true) (hs : s = shapeRef) (hp : p3 = true)
    (hk : lkW = 18) : onOk (wsLayOf s p3 lkW) R = true := by
  subst hs hp hk
  obtain ⟨lay, hw, hl⟩ := onOk_inv weightsAt
  have a := A lay
  rw [lk_same (eq_of_beq hl)] at a
  exact onOk_go hw a

/-- **At withPlans' own text, for any test f**: from the test at numerals, at all letters. -/
theorem plans_closed {v : VerifierAndGoals.FreeLines} {pub : Array Nat} {sc : Scales}
    {rope : Array Nat} {f : Pub → Array HPlan2 → Bool}
    (A : ∀ (e1 e2 eF : Nat) (W : WsLay), afterN e1 e2 eF pub sc rope W f = true) :
    withPlans v pub sc rope f = true := by
  unfold withPlans
  rw [shapeIs v, vocabIs v, colsIs v, setIs v]
  refine onOk_dep (A _ _ _) (sizes_letters _ _ _) fun y0 a1 b1 => onOk_in a1 default fun fo a2 =>
    onOk_in a2 default fun kbm a3 => at_weights a3 ?_ ?_ rfl
  · rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at b1
    exact (weightsIs v _).trans (ws_ref b1.1.1 b1.1.2)
  · rw [Bool.and_eq_true] at b1
    exact b1.2

end OnBytes.Road.K4.Closed

#print axioms OnBytes.Road.K4.Closed.onOk_dep
#print axioms OnBytes.Road.K4.Closed.onOk_in
#print axioms OnBytes.Road.K4.Closed.onOk_two
#print axioms OnBytes.Road.K4.Closed.num_two
#print axioms OnBytes.Road.K4.Closed.all_two
#print axioms OnBytes.Road.K4.Closed.after_letters
#print axioms OnBytes.Road.K4.Closed.front_blind
#print axioms OnBytes.Road.K4.Closed.sizes_letters
#print axioms OnBytes.Road.K4.Closed.lk_same
#print axioms OnBytes.Road.K4.Closed.ws_ref
#print axioms OnBytes.Road.K4.Closed.at_weights
#print axioms OnBytes.Road.K4.Closed.plans_closed
