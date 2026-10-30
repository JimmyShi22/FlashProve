-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/PinMove.lean: A PIN IS A FACT ON A SEAT, NOT ON THE LIST IN WHICH A MEMBER
STANDS.
Definitions and theorems, proved.

Why. A member (`Mem`, World.lean) is a place in a list of shapes with radii (`Sending`). One law
speaks of a message as a member of its own prover's message's list; another (a code switch's) as a
member of the list of a whole group. As values these are two members. What is said of them
(`ShownAt`, `PinAt`, `CfAt`, MsgSig.lean; `decAt`, World.lean) reads the list through the member's
own entry alone: the shape, the radius; and the seat; and the sample.
  `Alike x x₂`: two members have one entry (shape and radius) and one seat.
  `SmpBySeat smp`: a condition on the letter smp: at two members that are alike the record holds one
    sample.
  `shown1`, `dec1`, `cf1`: three of the notions at the list of one entry; `shownAt_eq1`,
    `decAt_eq1`, `cfAt_eq1` (proved, by unfolding): each notion at a member is that.
  `dec_of_alike` (proved): a member decodes as a member that is alike does, at that one's own
    sample: smp is read at the first alone.
  `shown_move`, `dec_move`, `pin_move`, `cf_move` (proved): **what is said of a member is said of
    every member that is alike**, where the two samples are one.
Limits. `SmpBySeat` is a premise wherever it is spent: whoever fills smp shows it. Nothing on
soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.World

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Fo.Peel Cb Johnson.Pack OnBytes.Slice

/-- Two members have one entry (shape and radius) and one seat. -/
def Alike (x x₂ : Mem) : Prop :=
  x.1.l.get x.2 = x₂.1.l.get x₂.2 ∧ x.1.seat x.2 = x₂.1.seat x₂.2

section
variable (cs : OnBytes.Codes) {Xi : Type} (G : FileDescription Xi) {A Cells Tok : Type} (arr : ℕ → ℕ → ℕ)

/-- The one place of a list of one entry. -/
abbrev at0 (p : OnBytes.OracleShape × ℕ) : Fin [p].length := ⟨0, Nat.zero_lt_one⟩

/-- A sample of a message with the entry p. -/
abbrev Smp1 (p : OnBytes.OracleShape × ℕ) : Type := ((sigOf cs [p]).om (at0 p)).Smp

def shown1 (p : OnBytes.OracleShape × ℕ) (q : ℕ × ℕ) (y : Strs) : Prop :=
  ShownAt G cs [p] (fun _ => q) y (at0 p)

open Classical in
def dec1 (p : OnBytes.OracleShape × ℕ) (q : ℕ × ℕ) (z : Option (Smp1 cs p)) (y : Strs) :
    Option MsgT :=
  z.bind fun z =>
    if ShownAt G cs [p] (fun _ => q) y (at0 p) then
      (((sigOf cs [p]).om (at0 p)).dec (wordsOf G cs [p] (fun _ => q) y (at0 p)) z).map
        (toMsgT cs [p] (at0 p))
    else none

def cf1 (p : OnBytes.OracleShape × ℕ) (q : ℕ × ℕ) (z : Option (Smp1 cs p)) (y : Strs) : Prop :=
  ∃ z', z = some z' ∧ ShownAt G cs [p] (fun _ => q) y (at0 p) ∧
    ¬ ((sigOf cs [p]).om (at0 p)).Clash (wordsOf G cs [p] (fun _ => q) y (at0 p)) z'.1

variable (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)

theorem shownAt_eq1 (x : Mem) (y : Strs) :
    ShownAt G cs x.1.l x.1.seat y x.2 = shown1 cs G (x.1.l.get x.2) (x.1.seat x.2) y := rfl

theorem decAt_eq1 (x : Mem) (a : A) (y : Strs) :
    decAt cs G smp x.1 x.2 a y = dec1 cs G (x.1.l.get x.2) (x.1.seat x.2) (smp a x.1 x.2) y := rfl

theorem cfAt_eq1 (x : Mem) (a : A) (y : Strs) :
    CfAt G cs x.1.l x.1.seat (fun z => smp z x.1) x.2 a y =
      cf1 cs G (x.1.l.get x.2) (x.1.seat x.2) (smp a x.1 x.2) y := rfl

/-- The samples hang on the entry and the seat, not on the list in which a member stands. -/
def SmpBySeat : Prop :=
  ∀ (a : A) (x x₂ : Mem), Alike x x₂ → HEq (smp a x.1 x.2) (smp a x₂.1 x₂.2)

theorem dec1_congr (p p₂ : OnBytes.OracleShape × ℕ) (q q₂ : ℕ × ℕ) (z : Option (Smp1 cs p))
    (z₂ : Option (Smp1 cs p₂)) (hp : p = p₂) (hq : q = q₂) (hz : HEq z z₂) (y : Strs) :
    dec1 cs G p q z y = dec1 cs G p₂ q₂ z₂ y := by
  subst hp
  subst hq
  rw [eq_of_heq hz]

theorem cf1_congr (p p₂ : OnBytes.OracleShape × ℕ) (q q₂ : ℕ × ℕ) (z : Option (Smp1 cs p))
    (z₂ : Option (Smp1 cs p₂)) (hp : p = p₂) (hq : q = q₂) (hz : HEq z z₂) (y : Strs) :
    cf1 cs G p q z y = cf1 cs G p₂ q₂ z₂ y := by
  subst hp
  subst hq
  rw [eq_of_heq hz]

/-- Every leaf is shown: of a member, so of every member that is alike. -/
theorem shown_move (x x₂ : Mem) (h : Alike x x₂) (y : Strs) :
    ShownAt G cs x.1.l x.1.seat y x.2 ↔ ShownAt G cs x₂.1.l x₂.1.seat y x₂.2 := by
  rw [shownAt_eq1, shownAt_eq1, h.1, h.2]

/-- **What a member decodes to, every member that is alike decodes to.** -/
theorem dec_move (x x₂ : Mem) (h : Alike x x₂) (a : A)
    (hz : HEq (smp a x.1 x.2) (smp a x₂.1 x₂.2)) (y : Strs) :
    decAt cs G smp x.1 x.2 a y = decAt cs G smp x₂.1 x₂.2 a y := by
  rw [decAt_eq1, decAt_eq1]
  exact dec1_congr cs G _ _ _ _ _ _ h.1 h.2 hz y

/-- **A member decodes as a member that is alike does, at that one's own sample**: smp is read at x
alone. -/
theorem dec_of_alike (x : Mem) (s : Sending) (i : Fin s.l.length) (h : Alike x ⟨s, i⟩) (a : A)
    (y : Strs) (z : ((sigOf cs s.l).om i).Smp) (hz : HEq (smp a x.1 x.2) (some z))
    (hs : ShownAt G cs s.l s.seat y i) (u : ((sigOf cs s.l).om i).Msg)
    (hd : ((sigOf cs s.l).om i).dec (wordsOf G cs s.l s.seat y i) z = some u) :
    decAt cs G smp x.1 x.2 a y = some (toMsgT cs s.l i u) := by
  rw [decAt_eq1, dec1_congr cs G _ (s.l.get i) _ (s.seat i) _ (some z) h.1 h.2 hz y]
  have hs' : ShownAt G cs [s.l.get i] (fun _ => s.seat i) y (at0 (s.l.get i)) := hs
  have hd' : ((sigOf cs [s.l.get i]).om (at0 (s.l.get i))).dec
      (wordsOf G cs [s.l.get i] (fun _ => s.seat i) y (at0 (s.l.get i))) z = some u := hd
  unfold dec1
  rw [Option.bind_some, if_pos hs', hd']
  rfl

theorem pin_move_mp (x x₂ : Mem) (h : Alike x x₂) (a : A)
    (hz : HEq (smp a x.1 x.2) (smp a x₂.1 x₂.2)) (y : Strs) (w : Wit Cells Tok MsgT)
    (p : PinAt G cs x.1.l x.1.seat (fun z => smp z x.1) arr x.2 a y w) :
    PinAt G cs x₂.1.l x₂.1.seat (fun z => smp z x₂.1) arr x₂.2 a y w := by
  have D := dec_of_pin cs G arr smp x.1 x.2 a y w p
  have T := tab_of_pin cs G arr smp x.1 x.2 a y w _ D p
  rw [dec_move cs G smp x x₂ h a hz y] at D
  refine pin_of_dec cs G arr smp x₂.1 x₂.2 a y w _ D ?_
  intro mask row place hin
  have e1 : (x₂.1.l.get x₂.2).1 = (x.1.l.get x.2).1 := (congrArg Prod.fst h.1).symm
  have e2 : x₂.1.seat x₂.2 = x.1.seat x.2 := h.2.symm
  rw [e1] at hin
  rw [e1, e2]
  exact T mask row place hin

/-- **A pin of a member is the pin of every member that is alike.** -/
theorem pin_move (x x₂ : Mem) (h : Alike x x₂) (a : A)
    (hz : HEq (smp a x.1 x.2) (smp a x₂.1 x₂.2)) (y : Strs) (w : Wit Cells Tok MsgT) :
    PinAt G cs x.1.l x.1.seat (fun z => smp z x.1) arr x.2 a y w ↔
      PinAt G cs x₂.1.l x₂.1.seat (fun z => smp z x₂.1) arr x₂.2 a y w :=
  ⟨pin_move_mp cs G arr smp x x₂ h a hz y w,
    pin_move_mp cs G arr smp x₂ x ⟨h.1.symm, h.2.symm⟩ a hz.symm y w⟩

/-- And the promise beside it. -/
theorem cf_move (x x₂ : Mem) (h : Alike x x₂) (a : A)
    (hz : HEq (smp a x.1 x.2) (smp a x₂.1 x₂.2)) (y : Strs) :
    CfAt G cs x.1.l x.1.seat (fun z => smp z x.1) x.2 a y ↔
      CfAt G cs x₂.1.l x₂.1.seat (fun z => smp z x₂.1) x₂.2 a y := by
  rw [cfAt_eq1, cfAt_eq1, cf1_congr cs G _ _ _ _ _ _ h.1 h.2 hz y]

end

end VerifiableInference.Desc.Sound
