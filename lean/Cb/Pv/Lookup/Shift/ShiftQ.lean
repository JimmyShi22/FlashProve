-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lookup/Shift/ShiftQ.lean.
The round that draws a shift, for calls of unequal size.

Several calls share one lookup: their key vectors are laid into one joint vector key X, X < 2^v, and
their tables into one joint table tab Y, Y < 2^d. Two maps say to which call an index belongs: fK X,
the call of the key X; fT Y, the call whose table the row Y is a row of.
tag c is the field element of call c. This file restates Cb/Ld/LdLkpShift.lean, with the proofs,
over such maps; that file has calls of one size.
  In-claim, AllInQ: each key X equals a row Y of its own call (fT Y = fK X).
  The block: one draw of θ, uniform in E; no prover's message.
  Out-claim: the library's InTable v d of the vectors key X + tag (fK X) θ and tab Y + tag (fT Y) θ.
  Premise, TagsQ: a row whose tag equals the key's tag has its value among the rows of the key's
    call. It follows from "equal tags, the same call" (tagsQ_of_eq), and so from "both maps land
    below nc, and tag is injective below nc" (tagsQ_of_lt).
  The number of bad θ: at most 2^d.
Main statements: shiftQ_fwd, shiftQ_cnt, shiftQ_goodAt, shiftQ_goodB; shiftQ_ofP (the library's
ShiftP is a case of ShiftQ, and its TagInj gives TagsQ); shiftQ_one (with one call the two claims
are the same at every θ: no draw is needed).
Limits: the keys are functions of the tuple of messages, and the count is for a fixed tuple; 2^d at
or above |E| says nothing; see also the limits in the head of Cb/Ld/LdLkpShift.lean.
Classical reasoning stands in proofs alone. No definition here is noncomputable.

-/
import Cb.Ld.LdLkpShiftProofs

set_option autoImplicit false

namespace Cb.LdLkp
open Finset Cb.Lkp Iop IOR

section
variable {E : Type} [Field E]

/-- each key is a row of its own call's table -/
def AllInQ (v d : ℕ) (fK fT : ℕ → ℕ) (key tab : ℕ → E) : Prop :=
  ∀ X < 2 ^ v, ∃ Y < 2 ^ d, fT Y = fK X ∧ key X = tab Y

/-- The joint keys and the joint table at θ. -/
def shKeyQ (fK : ℕ → ℕ) (key : ℕ → E) (tag : ℕ → E) (θ : E) : ℕ → E :=
  fun X => key X + tag (fK X) * θ
def shTabQ (fT : ℕ → ℕ) (tab : ℕ → E) (tag : ℕ → E) (θ : E) : ℕ → E :=
  fun Y => tab Y + tag (fT Y) * θ

/-- In place of TagInj: a row with the key's tag holds a value that a row of the key's call holds.
-/
def TagsQ (v d : ℕ) (fK fT : ℕ → ℕ) (tab : ℕ → E) (tag : ℕ → E) : Prop :=
  ∀ X < 2 ^ v, ∀ Y < 2 ^ d, tag (fK X) = tag (fT Y) → ∃ Y' < 2 ^ d, fT Y' = fK X ∧ tab Y' = tab Y

end

/-- The data of the block. -/
structure ShiftQ (E St M : Type) where
  v : ℕ
  d : ℕ
  fK : ℕ → ℕ
  fT : ℕ → ℕ
  key : St → M → ℕ → E
  tab : St → ℕ → E
  tag : ℕ → E

namespace ShiftQ
variable {E St M : Type} [Field E] (P : ShiftQ E St M)

/-- The claim before; the claim after. -/
def inC : St → M → Prop := fun st m => AllInQ P.v P.d P.fK P.fT (P.key st m) (P.tab st)
def outC : St × E → M → Prop := fun x m =>
  InTable P.v P.d (shKeyQ P.fK (P.key x.1 m) P.tag x.2) (shTabQ P.fT (P.tab x.1) P.tag x.2)

/-- What is asked of the tags, at every state. -/
def Tags : Prop := ∀ st, TagsQ P.v P.d P.fK P.fT (P.tab st) P.tag

variable {Kc Wp : Type} {Ex : ExtSpec}

/-- The two joints: R0 rides along. (The library's jIn, jOut, word for word.) -/
def jIn (R0 : Rels Kc St Ex (M × Wp)) : Rels Kc St Ex (M × Wp) :=
  ⟨fun x y w => R0.rel x y w ∧ P.inC x w.1, fun a w => R0.relR a w ∧ P.inC a.1 w.1, R0.on, R0.core⟩
def jOut (R0 : Rels Kc St Ex (M × Wp)) : Rels Kc (St × E) Ex (M × Wp) :=
  ⟨fun x y w => R0.rel x.1 y w ∧ P.outC x w.1,
    fun a w => R0.relR (a.1.1, a.2) w ∧ P.outC a.1 w.1,
    fun a => R0.on (a.1.1, a.2),
    R0.core⟩

end ShiftQ

/-- The library's data as a value: the function's number in the high bits, on both sides. -/
def ShiftP.toQ {E St M : Type} (P : ShiftP E St M) : ShiftQ E St M where
  v := P.g + P.v
  d := P.g + P.d
  fK := fun X => X / 2 ^ P.v
  fT := fun Y => Y / 2 ^ P.d
  key := fun st m X => P.key st m (X / 2 ^ P.v) (X % 2 ^ P.v)
  tab := fun st Y => P.tab st (Y / 2 ^ P.d) (Y % 2 ^ P.d)
  tag := P.tag

end Cb.LdLkp

namespace Cb.Spec
open Finset Prob Cb.Lkp Cb.LdLkp Iop IOR

/-- Complete at every θ. Nothing is asked of the tags. -/
def shiftQ_fwd : Prop :=
  ∀ (E : Type) [Field E] (v d : ℕ) (fK fT : ℕ → ℕ) (key tab : ℕ → E) (tag : ℕ → E) (θ : E),
    AllInQ v d fK fT key tab → InTable v d (shKeyQ fK key tag θ) (shTabQ fT tab tag θ)

/-- For fixed keys, under TagsQ, if some key is outside its own call's rows: at most as many bad θ
as the joint table has entries. -/
def shiftQ_cnt : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (v d : ℕ) (fK fT : ℕ → ℕ) (key tab : ℕ → E) (tag : ℕ → E),
    TagsQ v d fK fT tab tag → ¬ AllInQ v d fK fT key tab →
    cnt (fun θ : E => InTable v d (shKeyQ fK key tag θ) (shTabQ fT tab tag θ)) ≤ 2 ^ d

/-- «equal tags ⇒ the same call» gives TagsQ, at any table. -/
def tagsQ_of_eq : Prop :=
  ∀ (E : Type) [Field E] (v d : ℕ) (fK fT : ℕ → ℕ) (tab : ℕ → E) (tag : ℕ → E),
    (∀ X < 2 ^ v, ∀ Y < 2 ^ d, tag (fK X) = tag (fT Y) → fT Y = fK X) → TagsQ v d fK fT tab tag

/-- Both maps land below nc, and the tags of the calls below nc differ. -/
def tagsQ_of_lt : Prop :=
  ∀ (E : Type) [Field E] (v d nc : ℕ) (fK fT : ℕ → ℕ) (tab : ℕ → E) (tag : ℕ → E),
    (∀ X < 2 ^ v, fK X < nc) → (∀ Y < 2 ^ d, fT Y < nc) →
    (∀ c < nc, ∀ c' < nc, tag c = tag c' → c = c') → TagsQ v d fK fT tab tag

/-- The tag of call c is the field element c: different below the characteristic. -/
def natTag_inj : Prop :=
  ∀ (E : Type) [Field E] (p : ℕ) [CharP E p] (nc : ℕ), nc ≤ p →
    ∀ c < nc, ∀ c' < nc, ((c : ℕ) : E) = ((c' : ℕ) : E) → c = c'

/-- The block at the base. -/
def shiftQ_goodAt : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (St M Wp Kc : Type) (Ex : ExtSpec)
      (P : ShiftQ E St M) (R0 : Rels Kc St Ex (M × Wp)),
    P.Tags →
    GoodAt (IOR.draw E (Prod.mk : St → E → St × E) Ex) (Honest.draw E Prod.mk Ex (M × Wp))
      (P.jIn R0) (P.jOut R0) (fun _ _ _ wp => wp) (Nums.draw Kc E Prod.mk Ex (2 ^ P.d))

/-- Over a signature. -/
def shiftQ_goodB : Prop :=
  ∀ (E : Type) [Field E] [Fintype E] (S : Sig E) (St Wp Kc : Type) (E₀ : ExtSpec)
      (P : ShiftQ E St S.Msg) (R0 : Rels Kc St E₀ (S.Msg × Wp)),
    P.Tags →
    GoodB ((IOR.draw E (Prod.mk : St → E → St × E) E₀).keep S.Smp S.ext)
      (S.liftH (Honest.draw E Prod.mk E₀ (S.Msg × Wp))) (S.over (P.jIn R0)) (S.over (P.jOut R0))
      (fun _ _ w => w) ((Nums.draw Kc E Prod.mk E₀ (2 ^ P.d)).keep S.Smp S.ext)

/-- `ShiftP` (Cb/Ld/LdLkpShift.lean) is a case of `ShiftQ`. The out-claim is the same term. The
in-claim is the same proposition up to the numbering (an iff). TagInj gives Tags. The count 2 ^ d is
2 ^ (g + d). -/
def shiftQ_ofP : Prop :=
  ∀ (E : Type) [Field E] (St M : Type) (P : ShiftP E St M),
    P.toQ.outC = P.outC ∧ (∀ st m, P.toQ.inC st m ↔ P.inC st m) ∧ (TagInj P.g P.tag → P.toQ.Tags) ∧
    2 ^ P.toQ.d = 2 ^ (P.g + P.d)

/-- One call (all indices are of one call): at every θ the out-claim says what the in-claim says. So
no draw is needed: any fixed θ serves (the Lean verifier under OnBytes/ takes 0). Nothing is asked
of the tags. -/
def shiftQ_one : Prop :=
  ∀ (E : Type) [Field E] (St M : Type) (P : ShiftQ E St M),
    (∀ X < 2 ^ P.v, ∀ Y < 2 ^ P.d, P.fT Y = P.fK X) →
    ∀ st m θ, P.outC (st, θ) m ↔ P.inC st m

end Cb.Spec

namespace Cb
open Finset Prob Cb.Lkp Cb.LdLkp Iop IOR

theorem shiftQ_fwd : Spec.shiftQ_fwd := by
  intro E _ v d fK fT key tab tag θ h X hX
  obtain ⟨Y, hY, hf, he⟩ := h X hX
  refine ⟨Y, hY, ?_⟩
  unfold shKeyQ shTabQ
  rw [hf, he]

theorem shiftQ_cnt : Spec.shiftQ_cnt := by
  classical
  intro E _ _ v d fK fT key tab tag hT hn
  have hex : ∃ X, X < 2 ^ v ∧ ∀ Y < 2 ^ d, fT Y = fK X → key X ≠ tab Y := by
    by_contra hc
    refine hn fun X hX => ?_
    by_contra hc'
    exact hc ⟨X, hX, fun Y hY hf he => hc' ⟨Y, hY, hf, he⟩⟩
  obtain ⟨X, hX, hout⟩ := hex
  let Pd : ℕ → E → Prop := fun Y θ =>
    tag (fK X) ≠ tag (fT Y) ∧ key X + tag (fK X) * θ = tab Y + tag (fT Y) * θ
  have hsub : cnt (fun θ : E => InTable v d (shKeyQ fK key tag θ) (shTabQ fT tab tag θ)) ≤
      cnt (fun θ : E => ∃ Y ∈ range (2 ^ d), Pd Y θ) := by
    refine cnt_mono fun θ hθ => ?_
    obtain ⟨Y, hY, he⟩ := hθ X hX
    unfold shKeyQ shTabQ at he
    refine ⟨Y, mem_range.2 hY, fun hj => ?_, he⟩
    rw [hj] at he
    obtain ⟨Y', hY', hf', he'⟩ := hT X hX Y hY hj
    exact hout Y' hY' hf' ((add_right_cancel he).trans he'.symm)
  refine hsub.trans ((cnt_exists_mem_le _ _).trans ?_)
  have hone : ∀ Y ∈ range (2 ^ d), cnt (Pd Y) ≤ 1 := by
    intro Y _
    refine cnt_le_one fun θ θ' h h' => ?_
    have hne : tag (fK X) - tag (fT Y) ≠ 0 := fun h0 => h.1 (sub_eq_zero.1 h0)
    have e : (tag (fK X) - tag (fT Y)) * (θ - θ') = 0 := by linear_combination h.2 - h'.2
    exact sub_eq_zero.1 ((mul_eq_zero.1 e).resolve_left hne)
  calc ∑ Y ∈ range (2 ^ d), cnt (Pd Y) ≤ ∑ _Y ∈ range (2 ^ d), 1 := sum_le_sum hone
    _ = 2 ^ d := by simp

theorem tagsQ_of_eq : Spec.tagsQ_of_eq := fun _ _ _ _ _ _ _ _ h X hX Y hY ht =>
  ⟨Y, hY, h X hX Y hY ht, rfl⟩

theorem tagsQ_of_lt : Spec.tagsQ_of_lt := fun E _ v d _ fK fT tab tag hK hT hi =>
  tagsQ_of_eq E v d fK fT tab tag fun X hX Y hY ht => (hi _ (hK X hX) _ (hT Y hY) ht).symm

theorem natTag_inj : Spec.natTag_inj := by
  intro E _ p _ nc hp c hc c' hc' h
  have h1 := (CharP.natCast_eq_natCast E p).1 h
  have h2 : c % p = c' % p := h1
  rwa [Nat.mod_eq_of_lt (lt_of_lt_of_le hc hp), Nat.mod_eq_of_lt (lt_of_lt_of_le hc' hp)] at h2

theorem shiftQ_goodAt : Spec.shiftQ_goodAt := by
  intro E _ _ St M Wp Kc Ex P R0 hT
  refine goodAt_draw Kc M St (St × E) Ex Wp E Prod.mk (P.jIn R0) (P.jOut R0) (2 ^ P.d) ?_
    (fun _ _ _ h => h) (fun _ => rfl) ?_
  · intro x y w θ h
    exact ⟨h.1, shiftQ_fwd E P.v P.d P.fK P.fT _ _ P.tag θ h.2⟩
  · intro x y m _
    by_cases hin : P.inC x m
    · refine le_trans (le_of_eq (cnt_false ?_)) (Nat.zero_le _)
      rintro θ ⟨wp, h, hn⟩
      exact hn ⟨h.1, hin⟩
    · refine (cnt_mono ?_).trans (shiftQ_cnt E P.v P.d P.fK P.fT (P.key x m) (P.tab x) P.tag (hT x)
        hin)
      rintro θ ⟨wp, h, _⟩
      exact h.2

theorem shiftQ_goodB : Spec.shiftQ_goodB := fun E _ _ S St Wp Kc E₀ P R0 hT =>
  sigLift_goodB E S Kc _ _ Wp Wp E₀ E₀ _ _ _ _ _ _ (shiftQ_goodAt E St S.Msg Wp Kc E₀ P R0 hT)

theorem shiftQ_ofP : Spec.shiftQ_ofP := by
  intro E _ St M P
  refine ⟨rfl, fun st m => ⟨fun h f hf b hb => ?_, fun h X hX => ?_⟩, fun hT st => ?_, rfl⟩
  · obtain ⟨h1, h2, h3⟩ := ldLkpShift_num P.g P.v f b hf hb
    obtain ⟨Y, hY, hfY, he⟩ := h _ h1
    have hfY' : Y / 2 ^ P.d = (b + 2 ^ P.v * f) / 2 ^ P.v := hfY
    have he' : P.key st m ((b + 2 ^ P.v * f) / 2 ^ P.v) ((b + 2 ^ P.v * f) % 2 ^ P.v) =
        P.tab st (Y / 2 ^ P.d) (Y % 2 ^ P.d) := he
    rw [hfY', h2, h3] at he'
    exact ⟨Y % 2 ^ P.d, (ldLkpShift_split P.g P.d Y hY).2, he'⟩
  · obtain ⟨hf, hb⟩ := ldLkpShift_split P.g P.v X hX
    obtain ⟨u, hu, he⟩ := h _ hf _ hb
    obtain ⟨h1, h2, h3⟩ := ldLkpShift_num P.g P.d (X / 2 ^ P.v) u hf hu
    refine ⟨u + 2 ^ P.d * (X / 2 ^ P.v), h1, h2, ?_⟩
    show P.key st m (X / 2 ^ P.v) (X % 2 ^ P.v) = P.tab st _ _
    rw [h2, h3, he]
  · exact tagsQ_of_eq E _ _ _ _ _ _ fun X hX Y hY ht =>
      (hT _ (ldLkpShift_split P.g P.v X hX).1 _ (ldLkpShift_split P.g P.d Y hY).1 ht).symm

theorem shiftQ_one : Spec.shiftQ_one := by
  intro E _ St M P h1 st m θ
  refine ⟨fun h X hX => ?_, fun h => shiftQ_fwd E P.v P.d P.fK P.fT _ _ P.tag θ h⟩
  obtain ⟨Y, hY, he⟩ := h X hX
  have he' : P.key st m X + P.tag (P.fK X) * θ = P.tab st Y + P.tag (P.fT Y) * θ := he
  rw [h1 X hX Y hY] at he'
  exact ⟨Y, hY, h1 X hX Y hY, add_right_cancel he'⟩

end Cb
