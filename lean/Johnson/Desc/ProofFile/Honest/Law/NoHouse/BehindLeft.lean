-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/NoHouse/BehindLeft.lean: «LINK m: BEHIND THE BATCHING» LEAVES WHAT
THE MERGE LEFT. The hash build asks of the 25 members behind the batchings: that their decision
leaves, at a layers' link, what the link's own rounds returned (`S.own?`), and at the head's link
what the merge laid (the field wo of the head's own part). The library's `rest9`
(Johnson/Desc/First/Link/Law/Rest9.lean) blanks, of the open segment's part, the link's context, the
ledger and the approximate range proof's state alone: so both are read off «`rest9` alike». NO
PREMISE ON THE MARK IS TAKEN.

WHAT THIS IS. Lemmas on the library's definitions; calls. In 3: THE FULL SIZE ALONE, and the
format's second hash function alone. None of the library's goals.

  1  `rest9_own`, `rest9_head`, `rest9_wo`   from «`rest9` alike»
  2  `keepsBehind_own`, `keepsBehind_wo`, `after_left`   from the clause; from a yes of the runs
  3  `behind_left_head`   AT EVERY LINK OF THE LIBRARY's HEAD

Limits. `rest9_head`'s proof is `keepsBehind_head`'s own (Honest/Law/NoHouse/BehindKeeps.lean),
which took the whole clause where the middle conjunct serves. This file proves nothing about
soundness, completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.NoHouse.BehindShare

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Link Claim)
open VerifiableInference.Desc.First (S HeadOwn Here)
open VerifiableInference.Desc.LinkJoin (rest9 here9 RunRests AtAfter SegAt)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

/-! ## 1 From «`rest9` alike» -/

/-- What a layers' link's own rounds returned is as it was. -/
theorem rest9_own {L₀ : OnBytes.Model.LinkCtx} {F₀ : OnBytes.Model.Fork}
    {t₀ : OnBytes.Model.HTailF2} {s s' : S} (e : rest9 L₀ F₀ t₀ s' = rest9 L₀ F₀ t₀ s) :
    s'.own? = s.own? := by
  have r : ∀ u : S, (rest9 L₀ F₀ t₀ u).own? = u.own? := fun u => by
    unfold S.own? rest9
    cases u.here <;> rfl
  rw [← r s', ← r s, e]

/-- In the head's link: the same part but for the three that are blanked. -/
theorem rest9_head {s s' : S} (h : ∀ L₀ F₀ t₀, rest9 L₀ F₀ t₀ s' = rest9 L₀ F₀ t₀ s) (a : HeadOwn)
    (ha : s.here = .head a) :
    ∃ L F tl, s'.here = .head { a with L := L, F := F, tl := tl } := by
  have e := h a.L a.F a.tl
  have e' : (rest9 a.L a.F a.tl s').here = (rest9 a.L a.F a.tl s).here :=
    congrArg (fun z : S => z.here) e
  have e'' : here9 a.L a.F a.tl s'.here =
      here9 a.L a.F a.tl s.here := e'
  rw [ha] at e''
  cases hs : s'.here with
  | head a' =>
    rw [hs] at e''
    have e3 : ({ a' with L := a.L, F := a.F, tl := a.tl } : HeadOwn) =
        { a with L := a.L, F := a.F, tl := a.tl } :=
      Here.head.inj e''
    refine ⟨a'.L, a'.F, a'.tl, ?_⟩
    cases a
    cases a'
    simp only [HeadOwn.mk.injEq] at e3
    obtain ⟨g1, g2, g3, -, -, g4, g5, -, g6, g7, g8, g9, g10, g11, g12⟩ := e3
    subst g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12
    rfl
  | between => rw [hs] at e''; cases e''
  | lay _ => rw [hs] at e''; cases e''
  | att _ => rw [hs] at e''; cases e''
  | fin _ => rw [hs] at e''; cases e''
  | mem _ => rw [hs] at e''; cases e''

/-- **What the merge laid is as it was.** -/
theorem rest9_wo {s s' : S} (h : ∀ L₀ F₀ t₀, rest9 L₀ F₀ t₀ s' = rest9 L₀ F₀ t₀ s) (a : HeadOwn)
    (ha : s.here = .head a) : ∃ a', s'.here = .head a' ∧ a'.wo = a.wo := by
  obtain ⟨L, F, tl, e⟩ := rest9_head h a ha
  exact ⟨_, e, rfl⟩

/-! ## 2 From the clause; from a yes of the runs -/

theorem keepsBehind_own {s s' : S} (h : keepsBehind s s') : s'.own? = s.own? :=
  rest9_own (h.2.1 { check := s.check } {} {})

theorem keepsBehind_wo {s s' : S} (h : keepsBehind s s') (a : HeadOwn) (ha : s.here = .head a) :
    ∃ a', s'.here = .head a' ∧ a'.wo = a.wo :=
  rest9_wo h.2.1 a ha

/-- **From a yes of the runs behind the batching**, marked or not. -/
theorem after_left (Lk : Link S Claim)
    (A : ∀ B : S → S → Prop, RunRests B → ∀ o ∈ Lk.orderAfter, ∀ run, AtAfter Lk o run →
      ∀ e e₁, run e = .ok e₁ → B e e₁) (s s' : S)
    (h : Lk.runBehind s = .ok s') : s'.own? = s.own? ∧
      ∀ a, s.here = .head a → ∃ a', s'.here = .head a' ∧ a'.wo = a.wo := by
  have r := (after_state Lk A s s' h).2.1
  exact ⟨rest9_own (r { check := s.check } {} {}), fun a ha => rest9_wo r a ha⟩

/-! ## 3 At the library's head -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **AT EVERY LINK OF THE HEAD.** -/
theorem behind_left_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {m : Nat} (hm : m < 25)
    {Lk : Link S Claim} (hlk : h.𝔇.lk m = some Lk) (hseg : SegAt m (IM.subAt m) Lk) (s s' : S)
    (hy : Lk.runBehind s = .ok s') : s'.own? = s.own? ∧
      ∀ a, s.here = .head a → ∃ a', s'.here = .head a' ∧ a'.wo = a.wo :=
  after_left Lk (after_share_head h hm hlk hseg) s s' hy

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.rest9_own
#print axioms ProofFile.Honest.FirstThread.rest9_head
#print axioms ProofFile.Honest.FirstThread.rest9_wo
#print axioms ProofFile.Honest.FirstThread.keepsBehind_own
#print axioms ProofFile.Honest.FirstThread.keepsBehind_wo
#print axioms ProofFile.Honest.FirstThread.after_left
#print axioms ProofFile.Honest.FirstThread.behind_left_head
