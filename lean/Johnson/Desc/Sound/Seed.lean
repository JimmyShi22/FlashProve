-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/Seed.lean: THE SAMPLE's SEED UNDER ITS OWN "THERE IS", TIED TO THE RECORD BY THE
ROWS. Definitions, the library's notions' congruences in the seed, and the two forms of the pin and
of the promise, proved equal.

Why. `PinAt` and `CfAt` (MsgSig.lean) ask that the record hold a member's sample: the library's:
SEED and answers. The chain's record keeps the sample ROWS (their coefficients are made of the seed;
their targets are the answers), not the seed. But the library's notions read a seed through its rows
alone. So:
  forms a s i: A LETTER: the member's sample rows, as the record a holds them, read as linear forms
  on the member's message (one for each answer); ans a s i: A LETTER: their targets.
  `SeedIs forms a s i ρ`: THE RECORD's ROWS ARE THE LIBRARY's ROWS AT THE SEED ρ (`Sample.mat ρ`;
    `OMsg.row`, Cb/Ld/LdSig.lean).
  `val_congr`, `dec_congr`, `clash_congr`, `cand_congr` (proved): two seeds with one matrix have one
    `Sample.val`, and then the library's `OMsg.dec`, `OMsg.Clash`, `OMsg.Cand` say the same at both.
    NO INJECTIVITY OF THE ROWS IN THE SEED IS WANTED.
  `smpOf forms ans`: the second reading (`smp`) made of the two letters: some seed whose rows are
    the record's, by choice, with the targets.
  `pinAt_iff` (proved): at that reading `PinAt` says: THERE IS A SEED ρ WITH `SeedIs` and answers v
    that the record holds, every leaf is shown, and `dec word (ρ, v)` is the witness's message.
  `cfAt_iff` (proved): at that reading `CfAt` says: there is such a seed; the record holds the
    answers; every leaf is shown; and AT EVERY SEED ρ WITH `SeedIs` there is no collision.
Limits. forms and ans are letters: the reading of the program's plain rows (sparse units, runs and
tensors over oracle, part and index) as linear forms on the library's typed message is the law of
the sending's kind; it bears every pin. SILLY MEMBER: a record whose rows are all 0: if some seed
has the matrix 0, `SeedIs` holds of it and a collision is certain wherever the list has two members:
the promise is then false, rightly. That the sample rows of an oracle message whose pin is open stay
in the record is each later block's duty. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.World

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Cb Cb.Ood Johnson.Pack OnBytes.Slice

/-! ## 1 The library's notions read a seed through its rows -/

theorem val_congr {E J : Type} [Field E] [Fintype J] (Z : Sample E J) (ρ ρ' : Z.D)
    (h : Z.mat ρ = Z.mat ρ') : Z.val ρ = Z.val ρ' := by
  funext u s
  unfold Sample.val
  rw [h]

theorem decMin_congr {T U D Y : Type} (dist rank : T → ℕ) (view : T → U) (ev : D → U → Y) (e : ℕ)
    (ρ ρ' : D) (y : Y) (h : ev ρ = ev ρ') :
    decMin dist rank view ev e ρ y = decMin dist rank view ev e ρ' y := by
  have hP : (fun t => First dist rank view ev ρ y t ∧ dist t ≤ e) =
      fun t => First dist rank view ev ρ' y t ∧ dist t ≤ e := by
    funext t
    unfold First
    rw [h]
  have key : ∀ P Q : T → Prop, P = Q →
      (open Classical in if g : ∃ t, P t then some (view g.choose) else none) =
        (open Classical in if g : ∃ t, Q t then some (view g.choose) else none) := by
    intro P Q e
    subst e
    rfl
  exact key _ _ hP

variable {E : Type} [Field E] (o : OMsg E)

theorem dec_congr (f : o.Str) (ρ ρ' : o.Z.D) (v : o.Z.S → E) (h : o.Z.val ρ = o.Z.val ρ') :
    o.dec f (ρ, v) = o.dec f (ρ', v) :=
  decMin_congr _ _ _ _ _ ρ ρ' v h

theorem clash_congr (f : o.Str) (ρ ρ' : o.Z.D) (h : o.Z.val ρ = o.Z.val ρ') :
    o.Clash f ρ ↔ o.Clash f ρ' := by
  unfold OMsg.Clash Ood.Clash
  rw [h]

theorem cand_congr (f : o.Str) (ρ ρ' : o.Z.D) (v : o.Z.S → E) (m : o.Msg)
    (h : o.Z.val ρ = o.Z.val ρ') : o.Cand f (ρ, v) m ↔ o.Cand f (ρ', v) m := by
  unfold OMsg.Cand Ood.Cand
  show _ ∧ o.Z.val ρ m = v ↔ _ ∧ o.Z.val ρ' m = v
  rw [h]

/-! ## 2 The seed, tied to the record by the rows -/

section
variable (cs : OnBytes.Codes) {A : Type}
  (forms : A → (s : Sending) → (i : Fin s.l.length) →
    Option (((sigOf cs s.l).om i).Z.S → ((sigOf cs s.l).om i).C.J → GE))
  (ans : A → (s : Sending) → (i : Fin s.l.length) → Option (((sigOf cs s.l).om i).Z.S → GE))

/-- **The record's rows are the library's rows at the seed ρ.** -/
def SeedIs (a : A) (s : Sending) (i : Fin s.l.length) (ρ : ((sigOf cs s.l).om i).Z.D) : Prop :=
  forms a s i = some (((sigOf cs s.l).om i).Z.mat ρ)

theorem seedIs_val (a : A) (s : Sending) (i : Fin s.l.length) (ρ ρ' : ((sigOf cs s.l).om i).Z.D)
    (h : SeedIs cs forms a s i ρ) (h' : SeedIs cs forms a s i ρ') :
    ((sigOf cs s.l).om i).Z.val ρ = ((sigOf cs s.l).om i).Z.val ρ' :=
  val_congr _ ρ ρ' (Option.some.inj (h.symm.trans h'))

open Classical in
/-- **The second reading, of the two letters**: some seed whose rows are the record's, with the
targets. -/
def smpOf (a : A) (s : Sending) (i : Fin s.l.length) : Option ((sigOf cs s.l).om i).Smp :=
  if h : ∃ ρ, SeedIs cs forms a s i ρ then (ans a s i).map fun v => (h.choose, v) else none

theorem smpOf_some (a : A) (s : Sending) (i : Fin s.l.length) (z : ((sigOf cs s.l).om i).Smp)
    (h : smpOf cs forms ans a s i = some z) :
    SeedIs cs forms a s i z.1 ∧ ans a s i = some z.2 := by
  unfold smpOf at h
  by_cases g : ∃ ρ, SeedIs cs forms a s i ρ
  · rw [dif_pos g] at h
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨g.choose_spec, hv⟩
  · rw [dif_neg g] at h
    cases h

theorem smpOf_of (a : A) (s : Sending) (i : Fin s.l.length) (ρ : ((sigOf cs s.l).om i).Z.D)
    (v : ((sigOf cs s.l).om i).Z.S → GE) (h : SeedIs cs forms a s i ρ) (hv : ans a s i = some v) :
    ∃ ρ', smpOf cs forms ans a s i = some (ρ', v) ∧ SeedIs cs forms a s i ρ' := by
  have g : ∃ ρ, SeedIs cs forms a s i ρ := ⟨ρ, h⟩
  refine ⟨g.choose, ?_, g.choose_spec⟩
  unfold smpOf
  rw [dif_pos g, hv]
  rfl

variable {Xi : Type} (G : FileDescription Xi) {Cells Tok : Type} (arr : ℕ → ℕ → ℕ)

/-- **The pin, with the seed under its own "there is".** -/
theorem pinAt_iff (s : Sending) (i : Fin s.l.length) (a : A) (y : Strs) (w : Wit Cells Tok MsgT) :
    PinAt G cs s.l s.seat (fun z => smpOf cs forms ans z s) arr i a y w ↔
      ∃ ρ v, SeedIs cs forms a s i ρ ∧ ans a s i = some v ∧ ShownAt G cs s.l s.seat y i ∧
        ((sigOf cs s.l).om i).dec (wordsOf G cs s.l s.seat y i) (ρ, v) =
          some (msgsOf cs s.l s.seat arr w i) := by
  constructor
  · rintro ⟨z, hz, hs, hd⟩
    obtain ⟨h1, h2⟩ := smpOf_some cs forms ans a s i z hz
    exact ⟨z.1, z.2, h1, h2, hs, hd⟩
  · rintro ⟨ρ, v, h1, h2, hs, hd⟩
    obtain ⟨ρ', e, h'⟩ := smpOf_of cs forms ans a s i ρ v h1 h2
    exact ⟨(ρ', v), e, hs, by
      rw [dec_congr _ _ ρ' ρ v (seedIs_val cs forms a s i ρ' ρ h' h1)]
      exact hd⟩

/-- **The promise, at every seed whose rows are the record's.** -/
theorem cfAt_iff (s : Sending) (i : Fin s.l.length) (a : A) (y : Strs) :
    CfAt G cs s.l s.seat (fun z => smpOf cs forms ans z s) i a y ↔
      (∃ ρ, SeedIs cs forms a s i ρ) ∧ (ans a s i).isSome = true ∧ ShownAt G cs s.l s.seat y i ∧
        ∀ ρ, SeedIs cs forms a s i ρ →
          ¬ ((sigOf cs s.l).om i).Clash (wordsOf G cs s.l s.seat y i) ρ := by
  constructor
  · rintro ⟨z, hz, hs, hn⟩
    obtain ⟨h1, h2⟩ := smpOf_some cs forms ans a s i z hz
    refine ⟨⟨z.1, h1⟩, by rw [h2]; rfl, hs, fun ρ hρ hc => hn ?_⟩
    exact (clash_congr _ _ ρ z.1 (seedIs_val cs forms a s i ρ z.1 hρ h1)).1 hc
  · rintro ⟨⟨ρ, h1⟩, h2, hs, hn⟩
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 h2
    obtain ⟨ρ', e, h'⟩ := smpOf_of cs forms ans a s i ρ v h1 hv
    exact ⟨(ρ', v), e, hs, hn ρ' h'⟩

end

end VerifiableInference.Desc.Sound
