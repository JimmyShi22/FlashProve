-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/Defer2Safe.lean: for the hypothesis `AdvAlw` of the lemma on deferred programming of the
random oracle (`Spec.defer2`, CompileK/SpecDefer2.lean): the rules of the token language in local
form (the library's discipline: `SafeO`, `TidyO`) with what a joint charge asks more: `SafeO2` :=
`SafeO` (Compile/Batch/SpecDiscipline.lean) and, at the oracles named by Jo: at a marked evaluation
the point is jointly injective in (the charged token, one further token b), b is unshown, stands in
no earlier point of that oracle, and the two lengths together reach ℓ2; at a reveal: with a further
token of such an evaluation its charged token is shown too (`UpClosed`: the converse of `ClosedO`'s
clause "others"). Under the hypotheses of the two statements it gives that hypothesis with Jo as the
joint classes.

Definitions, statements (`Compile.Batch.Disc.Spec.alw_of_safeO2`,
`Compile.Batch.Disc.Spec.advAlw_of_safeO2`) and proofs. Generic in the family of oracles and in the
challenger. Nothing assumed beyond the hypotheses of the statements and whatever the arguments hold
as proofs. Programs, states and the two modes: Rom/Defer.lean. A joint charge: in classes named for
it a point is charged to two tokens jointly (CompileK/SpecDefer2.lean, refinement (2)).

Main names:
  `Tidy2 Jo ℓ2 d`: the state's side: every evaluation at an oracle of Jo has one further token b;
    the lengths; b shown ⇒ the charged token shown (with `TidyO`'s "charged shown ⇒ released":
    unreleased ⇒ b unshown).
  `Spec.alw_of_safeO2`: marked points lie at oracles of ks; `TidyO`, `Tidy2`,
    `SafeO2 Rl Jo ℓ2 c d Q` ⇒ c.Alw (clO S) Jo (Ok2 .. (bits2 ..) ks) d (the end: Q, `TidyO`,
    `Tidy2`).
  `Spec.advAlw_of_safeO2`: the same for a challenger, an adversary and a property P of (adversary,
    the challenger's state, the experiment's state), under the hypotheses of its statement; they are
    those of `advAlw_of_safeO` (CompileK/Defer2Bridge.lean) with `Tidy2` beside `TidyO` and `SafeO2`
    for `SafeO`.

Limits: this file does not say that any program is `SafeO2` (for token trees:
CompileK/Defer2Tree.lean). P is a letter.
-/
import CompileK.Defer2Bridge

set_option autoImplicit false

namespace Compile.Batch.Disc
open Iop Rom Rom.DeferTail Rom.DeferTail2
open Compile.Disc
  (Rules markBad markDue afterPlain afterFresh afterMark afterReveal nEv val_of_prefix markDue_o
    markDue_charged markDue_others mem_evs_afterMark)

variable {S : OSpec} {sp : Split S} {α β : Type}

/-- The condition at a marked evaluation at an oracle with joint charges; the head's first paragraph
tells its clauses. -/
structure JMark (ℓ2 : S.ι → ℕ) (d : DSt S) (o : S.ι) (t : Tok)
    (us : List Tok) (pt : Bits → List Bits → S.Dom o) : Prop where
  inj2 : ∀ v v' x x', pt v [x] = pt v' [x'] → v = v' ∧ x = x'
  snd : ∃ b,
    us = [b] ∧ b ∉ d.shown ∧
    (∀ e ∈ d.evs, e.o = o → b ≠ e.charged ∧ b ∉ e.others) ∧
    ℓ2 o ≤ (d.val t).length + (d.val b).length

/-- with a further token of an evaluation at an oracle of Jo its charged token is shown too -/
def UpClosed (Jo : S.ι → Bool) (d : DSt S) (ts : List Tok) : Prop :=
  ∀ e ∈ d.evs, Jo e.o = true → ∀ b ∈ e.others, b ∈ ts → e.charged ∈ ts ∨ e.charged ∈ d.shown

/-- SafeO with what a joint charge asks more -/
def SafeO2 (Rl : Rules S) (Jo : S.ι → Bool) (ℓ2 : S.ι → ℕ) :
    Step S sp α → DSt S → (α → DSt S → Prop) → Prop
  | .pure a, d, Q => Q a d
  | .sample _ k, d, Q => ∀ r, SafeO2 Rl Jo ℓ2 (k r) d Q
  | .plain o q k, d, Q => Rl.Pl o q ∧ ∀ r T, SafeO2 Rl Jo ℓ2 (k r) (afterPlain d o T) Q
  | .fresh ℓ k, d, Q => ∀ u : Fin ℓ → Bool, SafeO2 Rl Jo ℓ2 (k d.vals.length) (afterFresh d (List.ofFn u)) Q
  | .marked o t us pt _ k, d, Q =>
      (∀ u ∈ us, u < d.vals.length) ∧ t ∉ us ∧ FreeAt d o t ∧
      Rl.bits o ≤ (d.val t).length ∧ Rl.Mk o (pt (d.val t) (us.map d.val)) ∧
      (Jo o = true → JMark ℓ2 d o t us pt) ∧
      ∀ r T, SafeO2 Rl Jo ℓ2 (k (sp.split o r).1 d.vals.length)
        (afterMark sp d o t us (pt (d.val t) (us.map d.val)) r T) Q
  | .reveal ts k, d, Q =>
    ClosedO d ts ∧ UpClosed Jo d ts ∧ ∀ T, SafeO2 Rl Jo ℓ2 (k (ts.map d.val)) (afterReveal d ts T) Q

/-- The state's side: the invariant on states that goes, beside `TidyO`, with `SafeO2`; the head's
row tells its clauses. -/
def Tidy2 (Jo : S.ι → Bool) (ℓ2 : S.ι → ℕ) (d : DSt S) : Prop :=
  ∀ e ∈ d.evs, Jo e.o = true →
    ∃ b,
      e.others = [b] ∧
      ℓ2 e.o ≤ (d.val e.charged).length + (d.val b).length ∧
      (b ∈ d.shown → e.charged ∈ d.shown)

def bits2 (Rl : Rules S) (Jo : S.ι → Bool) (ℓ2 : S.ι → ℕ) : S.ι → ℕ := fun o =>
  if Jo o = true then ℓ2 o else Rl.bits o

namespace Spec

def alw_of_safeO2 : Prop :=
  ∀ (S : OSpec) (sp : Split S) (α : Type) (Rl : Rules S) (Jo : S.ι → Bool)
      (ℓ2 : S.ι → ℕ) (ks : Finset S.ι),
    (∀ o q, Rl.Mk o q → o ∈ ks) →
    ∀ (c : Step S sp α) (d : DSt S) (Q : α → DSt S → Prop), TidyO Rl d →
      Tidy2 Jo ℓ2 d → SafeO2 Rl Jo ℓ2 c d Q →
      c.Alw (clO S) Jo (DSt.Ok2 (clO S) Jo (bits2 Rl Jo ℓ2) ks) d fun y =>
        Q y.1 y.2 ∧ TidyO Rl y.2 ∧ Tidy2 Jo ℓ2 y.2

def advAlw_of_safeO2 : Prop :=
  ∀ (S : OSpec) (sp : Split S) (Out In α : Type) (Rl : Rules S) (Jo : S.ι → Bool) (ℓ2 : S.ι → ℕ)
      (ks : Finset S.ι) (C : Chall S sp Out In) (e M : S.ι → ℕ)
      (P : Adv S Out In α → C.τ → DSt S → Prop),
    (∀ o q, Rl.Mk o q → o ∈ ks) → (∀ A s d, P A s d → TidyO Rl d ∧ Tidy2 Jo ℓ2 d) →
    (∀ a s d, P (.halt a) s d → (∀ o, d.nPlain o ≤ e o) ∧ ∀ o, nEv d o ≤ M o) →
    (∀ n k s d, P (.sample n k) s d → ∀ r, P (k r) s d) →
    (∀ o q k s d, P (.query o q k) s d → ∀ r T, P (k r) s { d with table := T }) →
    (∀ m k s d, P (.call m k) s d → SafeO2 Rl Jo ℓ2 (C.step s m) d fun y d' => P (k y.1) y.2 d') →
    ∀ A s d, P A s d →
      AdvAlw C (clO S) Jo (DSt.Ok2 (clO S) Jo (bits2 Rl Jo ℓ2) ks) (DSt.CntK2 (clO S) e M) A (s, d)

end Spec

variable {Rl : Rules S} {Jo : S.ι → Bool} {ℓ2 : S.ι → ℕ}

theorem SafeO2.mono {Q Q' : α → DSt S → Prop} (h : ∀ a d', Q a d' → Q' a d') (c : Step S sp α) :
    ∀ d, SafeO2 Rl Jo ℓ2 c d Q → SafeO2 Rl Jo ℓ2 c d Q' := by
  induction c with
  | pure a => exact fun d hd => h a d hd
  | sample n k ih => exact fun d hd r => ih r d (hd r)
  | plain o q k ih => exact fun d hd => ⟨hd.1, fun r T => ih r _ (hd.2 r T)⟩
  | fresh L k ih => exact fun d hd u => ih _ _ (hd u)
  | marked o t us pt inj k ih =>
    exact fun d ⟨h1, h2, h3, h4, h5, h6, h7⟩ =>
      ⟨h1, h2, h3, h4, h5, h6, fun r T => ih _ _ _ (h7 r T)⟩
  | reveal ts k ih => exact fun d ⟨h1, h2, h3⟩ => ⟨h1, h2, fun T => ih _ _ (h3 T)⟩

theorem SafeO2.bind {Q : β → DSt S → Prop} (c : Step S sp α) (g : α → Step S sp β) :
    ∀ d, SafeO2 Rl Jo ℓ2 c d (fun a d' => SafeO2 Rl Jo ℓ2 (g a) d' Q) →
      SafeO2 Rl Jo ℓ2 (c.bind g) d Q := by
  induction c with
  | pure a => exact fun d hd => hd
  | sample n k ih => exact fun d hd r => ih r d (hd r)
  | plain o q k ih => exact fun d hd => ⟨hd.1, fun r T => ih r _ (hd.2 r T)⟩
  | fresh L k ih => exact fun d hd u => ih _ _ (hd u)
  | marked o t us pt inj k ih =>
    exact fun d ⟨h1, h2, h3, h4, h5, h6, h7⟩ =>
      ⟨h1, h2, h3, h4, h5, h6, fun r T => ih _ _ _ (h7 r T)⟩
  | reveal ts k ih => exact fun d ⟨h1, h2, h3⟩ => ⟨h1, h2, fun T => ih _ _ (h3 T)⟩

theorem SafeO2.toSafeO {Q : α → DSt S → Prop} (c : Step S sp α) :
    ∀ d, SafeO2 Rl Jo ℓ2 c d Q → SafeO Rl c d Q := by
  induction c with
  | pure a => exact fun d hd => hd
  | sample n k ih => exact fun d hd r => ih r d (hd r)
  | plain o q k ih => exact fun d hd => ⟨hd.1, fun r T => ih r _ (hd.2 r T)⟩
  | fresh L k ih => exact fun d hd u => ih _ _ (hd u)
  | marked o t us pt inj k ih =>
    exact fun d ⟨h1, h2, h3, h4, h5, _, h7⟩ => ⟨h1, h2, h3, h4, h5, fun r T => ih _ _ _ (h7 r T)⟩
  | reveal ts k ih => exact fun d ⟨h1, _, h3⟩ => ⟨h1, fun T => ih _ _ (h3 T)⟩

/-! ### Lemmas: each of the four kinds of action keeps Tidy2, under its hypotheses -/

theorem Tidy2.plain {d : DSt S} (h : Tidy2 Jo ℓ2 d) (o : S.ι) (T : Table S) :
    Tidy2 Jo ℓ2 (afterPlain d o T) := h

theorem Tidy2.table {d : DSt S} (h : Tidy2 Jo ℓ2 d) (T : Table S) :
    Tidy2 Jo ℓ2 { d with table := T } := h

theorem Tidy2.ext {d d' : DSt S} (ht : TidyO Rl d) (h : Tidy2 Jo ℓ2 d)
    (hv : d.vals <+: d'.vals) (hs : d'.shown = d.shown) :
    ∀ e ∈ d.evs, Jo e.o = true →
      ∃ b,
        e.others = [b] ∧
        ℓ2 e.o ≤ (d'.val e.charged).length + (d'.val b).length ∧
        (b ∈ d'.shown → e.charged ∈ d'.shown) := by
  intro e he hJ
  obtain ⟨b, hb, hl, hsn⟩ := h e he hJ
  refine ⟨b, hb, ?_, by rw [hs]; exact hsn⟩
  rw [val_of_prefix hv (ht.charged_lt e he),
    val_of_prefix hv (ht.others_lt e he b (by rw [hb]; exact List.mem_singleton.2 rfl))]
  exact hl

theorem Tidy2.fresh {d : DSt S} (ht : TidyO Rl d) (h : Tidy2 Jo ℓ2 d) (v : Bits) :
    Tidy2 Jo ℓ2 (afterFresh d v) :=
  Tidy2.ext (d := d) (d' := afterFresh d v) ht h (List.prefix_append _ _) rfl

theorem Tidy2.mark {d : DSt S} (ht : TidyO Rl d) (h : Tidy2 Jo ℓ2 d) {o : S.ι} {t : Tok}
    {us : List Tok} {pt : Bits → List Bits → S.Dom o} (hus : ∀ u ∈ us, u < d.vals.length)
    (hfree : FreeAt d o t) (hJ : Jo o = true → JMark ℓ2 d o t us pt) (P : S.Dom o)
    (r : S.Rng o) (T : Table S) :
    Tidy2 Jo ℓ2 (afterMark sp d o t us P r T) := by
  intro e he hJe
  rcases List.mem_append.1 (show e ∈ d.evs ++ [_] from he) with he | he
  · exact Tidy2.ext (d := d) (d' := afterMark sp d o t us P r T) ht h
      (List.prefix_append _ _) rfl e he hJe
  · obtain rfl := List.mem_singleton.1 he
    obtain ⟨b, hb, hbs, _, hl⟩ := (hJ hJe).snd
    refine ⟨b, hb, ?_, fun hs => absurd hs hbs⟩
    show ℓ2 o ≤
      ((afterMark sp d o t us P r T).val t).length + ((afterMark sp d o t us P r T).val b).length
    rw [val_of_prefix (d := d) (List.prefix_append _ _) hfree.lt,
      val_of_prefix (d := d) (List.prefix_append _ _)
        (hus b (by rw [hb]; exact List.mem_singleton.2 rfl))]
    exact hl

theorem Tidy2.reveal {d : DSt S} (h : Tidy2 Jo ℓ2 d) {ts : List Tok}
    (hu : UpClosed Jo d ts) (T : Table S) :
    Tidy2 Jo ℓ2 (afterReveal d ts T) := by
  intro e' he' hJ
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 (show e' ∈ d.evs.map (markDue (d.shown ++ ts)) from he')
  rw [markDue_o] at hJ
  obtain ⟨b, hb, hl, hsn⟩ := h e he hJ
  rw [markDue_o, markDue_charged, markDue_others]
  refine ⟨b, hb, hl, fun hs => ?_⟩
  rcases List.mem_append.1 (show b ∈ d.shown ++ ts from hs) with hs | hs
  · exact List.mem_append_left _ (hsn hs)
  · rcases hu e he hJ b (by rw [hb]; exact List.mem_singleton.2 rfl) hs with h1 | h1
    · exact List.mem_append_right _ h1
    · exact List.mem_append_left _ h1

/-! ### The bridge: `alw_of_safeO2`, `advAlw_of_safeO2` -/

theorem ok2_of_tidy2 {ks : Finset S.ι} (hks : ∀ o q, Rl.Mk o q → o ∈ ks) {d : DSt S}
    (h : TidyO Rl d) (h2 : Tidy2 Jo ℓ2 d) :
    d.Ok2 (clO S) Jo (bits2 Rl Jo ℓ2) ks := by
  refine ⟨h.viol, fun v hv => ⟨hks _ _ (h.point v hv), fun hJ => ?_, fun hJ => ?_⟩⟩
  · have hJ' : Jo v.o = false := hJ
    show bits2 Rl Jo ℓ2 v.o ≤ _
    rw [bits2, if_neg (by simp [hJ'])]
    exact h.bits v hv
  · have hJ' : Jo v.o = true := hJ
    obtain ⟨b, hb, hl, hsn⟩ := h2 v hv hJ'
    refine ⟨b, hb, ?_, fun hr hs => ?_⟩
    · show bits2 Rl Jo ℓ2 v.o ≤ _
      rw [bits2, if_pos hJ']
      exact hl
    · have := h.released v hv (hsn hs)
      rw [hr] at this
      simp at this

theorem alw_of_safeO2 : Spec.alw_of_safeO2 := by
  intro S sp α Rl Jo ℓ2 ks hks c
  induction c with
  | pure a => exact fun d Q hd h2 h => ⟨h, hd, h2⟩
  | sample n k ih => exact fun d Q hd h2 h r => ih r d Q hd h2 (h r)
  | plain o q k ih => exact fun d Q hd h2 h y _ => ih y.1 _ Q (hd.plain o y.2) (h2.plain o y.2) (h.2 y.1 y.2)
  | fresh L k ih => exact fun d Q hd h2 h u => ih _ _ Q (hd.fresh _) (Tidy2.fresh hd h2 _) (h u)
  | marked o t us pt inj k ih =>
    intro d Q hd h2 h
    obtain ⟨hus, htu, hfree, hbit, hmk, hJ, hk⟩ := h
    refine ⟨⟨fun _ _ _ _ => rfl, fun hJo => (hJ hJo).inj2⟩, fun hJo => ?_, fun r => ?_⟩
    · obtain ⟨b, hb, hbs, hbe, _⟩ := (hJ hJo).snd
      exact ⟨b, hb, hbs, hbe⟩
    · have hd' := hd.mark (sp := sp) hus htu hfree _ hbit hmk r d.table
      have h2' := Tidy2.mark (sp := sp) hd h2 hus hfree hJ (pt (d.val t) (us.map d.val)) r d.table
      exact ⟨ok2_of_tidy2 hks hd' h2', ih _ _ _ Q hd' h2' (hk r d.table)⟩
  | reveal ts k ih =>
    intro d Q hd h2 h
    obtain ⟨hc, hu, hk⟩ := h
    have hd' := hd.reveal hc (releaseAll true (d.shown ++ ts) d.evs d.table).2
    have h2' := Tidy2.reveal h2 hu (releaseAll true (d.shown ++ ts) d.evs d.table).2
    show DSt.Ok2 _ _ _ _ (postReveal true d ts) ∧
      Step.Alw _ _ _ (k (ts.map d.val)) (postReveal true d ts) _
    rw [postReveal_eq]
    exact ⟨ok2_of_tidy2 hks hd' h2', ih _ _ Q hd' h2' (hk _)⟩

theorem advAlw_of_safeO2 : Spec.advAlw_of_safeO2 := by
  intro S sp Out In α Rl Jo ℓ2 ks C e M P hks htidy hhalt hsample hquery hcall A s d h
  refine advAlw_of_inv C _ (fun A s => P A s.1 s.2) (fun a s hs => hhalt a s.1 s.2 hs)
    (fun n k s hs r => hsample n k s.1 s.2 hs r) (fun o q k s hs r T => hquery o q k s.1 s.2 hs r T)
    (fun m k s hs => ?_) A (s, d) h
  exact alw_mono (fun y hy => hy.1) _ _
    (alw_of_safeO2 S sp _ Rl Jo ℓ2 ks hks (C.step s.1 m) s.2 _ (htidy _ _ _ hs).1
      (htidy _ _ _ hs).2 (hcall m k s.1 s.2 hs))

end Compile.Batch.Disc
