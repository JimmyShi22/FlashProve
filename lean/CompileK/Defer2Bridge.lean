-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/Defer2Bridge.lean: the local form in which the library proves that its token programs obey
the rules (Compile/Batch/SpecDiscipline.lean: `SafeO`, `TidyO`) implies the hypothesis `AdvAlw` of
the lemma on deferred programming of the random oracle (`Spec.defer2`, CompileK/SpecDefer2.lean) at
classes := the oracles' names, no joint class; under the hypotheses of the two statements.

A definition, statements (`Compile.Batch.Disc.Spec.alw_of_safeO`,
`Compile.Batch.Disc.Spec.advAlw_of_safeO`) and proofs. Generic in the family of oracles and in the
challenger. Nothing assumed beyond the hypotheses of the statements and whatever the arguments hold
as proofs. Programs, states and the two modes: Rom/Defer.lean. `SafeO Rl c d Q` says that the
program c obeys the rules Rl from the state d and ends in Q, whatever the coins, the answers and the
tables are; `TidyO Rl d` is the invariant on states that goes with it.

Main names:
  `Spec.advAlw_of_safeO`: marked points lie at oracles of ks; a challenger, a property P of
    (adversary, the challenger's state, the experiment's state) that implies `TidyO`, gives the
    counts at a halt, is kept by samples and by queries whatever the table, and at a call gives
    `SafeO` of the step with the end P ⇒ `AdvAlw` for every (A, s, d) with P.

Why the proofs are short: `SafeO Rl c d Q` is, like `Step.Alw`, a recursion along the program, for
all coins, answers and tables; `TidyO` is kept by the four kinds of action where `SafeO` allows them
(Compile/Batch/Discipline.lean); `DSt.Ok2` at no joint class is three clauses of `TidyO` (viol,
bits, point; the last with "marked points lie at oracles of ks").

Limits: this file does not say "nothing is lost". For that, every challenger to which
`Rom.Spec.defer` or `Rom.Spec.deferTotal` is applied in the library would have to be brought under
`advAlw_of_safeO`: none is in this file. And `Rom.Spec.defer`'s and `Rom.Spec.deferTotal`'s own
hypothesis (final states) is not shown to imply `AdvAlw`. P is a letter: at P := never the statement
says nothing. This file says nothing on any sharper bound: at this setting `Rom.Spec.defer2`'s bound
is `Rom.Spec.deferTotal`'s. It does not say that a particular challenger of the library has such a
P. The library's proofs have one in another form: an invariant with counts, by runs
(Compile/Batch/DisciplineWorld.lean).
-/
import Compile.Batch.Discipline
import CompileK.Defer2Adv

set_option autoImplicit false

namespace Compile.Batch.Disc
open Iop Rom Rom.DeferTail Rom.DeferTail2
open Compile.Disc (Rules markBad markDue afterPlain afterFresh afterMark afterReveal nEv)

variable {S : OSpec} {sp : Split S}

/-- the class of a point is its oracle -/
def clO (S : OSpec) : PtCls S S.ι :=
  { of := fun k => k.1, orc := fun o => o, orc_of := fun _ => rfl }

namespace Spec

def alw_of_safeO : Prop :=
  ∀ (S : OSpec) (sp : Split S) (α : Type) (Rl : Rules S) (ks : Finset S.ι),
    (∀ o q, Rl.Mk o q → o ∈ ks) →
    ∀ (c : Step S sp α) (d : DSt S) (Q : α → DSt S → Prop), TidyO Rl d → SafeO Rl c d Q →
      c.Alw (clO S) (fun _ => false) (DSt.Ok2 (clO S) (fun _ => false) Rl.bits ks)
        d fun y => Q y.1 y.2 ∧ TidyO Rl y.2

def advAlw_of_safeO : Prop :=
  ∀ (S : OSpec) (sp : Split S) (Out In α : Type) (Rl : Rules S) (ks : Finset S.ι)
      (C : Chall S sp Out In) (e M : S.ι → ℕ) (P : Adv S Out In α → C.τ → DSt S → Prop),
    (∀ o q, Rl.Mk o q → o ∈ ks) → (∀ A s d, P A s d → TidyO Rl d) →
    (∀ a s d, P (.halt a) s d → (∀ o, d.nPlain o ≤ e o) ∧ ∀ o, nEv d o ≤ M o) →
    (∀ n k s d, P (.sample n k) s d → ∀ r, P (k r) s d) →
    (∀ o q k s d, P (.query o q k) s d → ∀ r T, P (k r) s { d with table := T }) →
    (∀ m k s d, P (.call m k) s d → SafeO Rl (C.step s m) d fun y d' => P (k y.1) y.2 d') →
    ∀ A s d, P A s d →
      AdvAlw C (clO S) (fun _ => false) (DSt.Ok2 (clO S) (fun _ => false) Rl.bits ks)
        (DSt.CntK2 (clO S) e M) A (s, d)

end Spec

theorem ok2_of_tidyO {Rl : Rules S} {ks : Finset S.ι} (hks : ∀ o q, Rl.Mk o q → o ∈ ks)
    {d : DSt S} (h : TidyO Rl d) :
    d.Ok2 (clO S) (fun _ => false) Rl.bits ks :=
  ⟨h.viol, fun v hv => ⟨hks _ _ (h.point v hv), fun _ => h.bits v hv, fun hJ => by simp at hJ⟩⟩

theorem postReveal_eq (d : DSt S) (ts : List Tok) :
    postReveal true d ts = afterReveal d ts (releaseAll true (d.shown ++ ts) d.evs d.table).2 := by
  unfold postReveal afterReveal
  rw [Rom.DeferTail.releaseAll_fst]
  rfl

theorem alw_of_safeO : Spec.alw_of_safeO := by
  intro S sp α Rl ks hks c
  induction c with
  | pure a => exact fun d Q hd h => ⟨h, hd⟩
  | sample n k ih => exact fun d Q hd h r => ih r d Q hd (h r)
  | plain o q k ih => exact fun d Q hd h y _ => ih y.1 _ Q (hd.plain o y.2) (h.2 y.1 y.2)
  | fresh L k ih => exact fun d Q hd h u => ih _ _ Q (hd.fresh _) (h u)
  | marked o t us pt inj k ih =>
    intro d Q hd h
    obtain ⟨hus, htu, hfree, hbit, hmk, hk⟩ := h
    refine ⟨⟨fun _ _ _ _ => rfl, fun hJ => by simp at hJ⟩, fun hJ => by simp at hJ, fun r => ?_⟩
    have hd' := hd.mark (sp := sp) hus htu hfree _ hbit hmk r d.table
    exact ⟨ok2_of_tidyO hks hd', ih _ _ _ Q hd' (hk r d.table)⟩
  | reveal ts k ih =>
    intro d Q hd h
    obtain ⟨hc, hk⟩ := h
    have hd' := hd.reveal hc (releaseAll true (d.shown ++ ts) d.evs d.table).2
    show DSt.Ok2 _ _ _ _ (postReveal true d ts) ∧
      Step.Alw _ _ _ (k (ts.map d.val)) (postReveal true d ts) _
    rw [postReveal_eq]
    exact ⟨ok2_of_tidyO hks hd', ih _ _ Q hd' (hk _)⟩

theorem advAlw_of_safeO : Spec.advAlw_of_safeO := by
  intro S sp Out In α Rl ks C e M P hks htidy hhalt hsample hquery hcall A s d h
  refine advAlw_of_inv C _ (fun A s => P A s.1 s.2) (fun a s hs => hhalt a s.1 s.2 hs)
    (fun n k s hs r => hsample n k s.1 s.2 hs r) (fun o q k s hs r T => hquery o q k s.1 s.2 hs r T)
    (fun m k s hs => ?_) A (s, d) h
  exact alw_mono (fun y hy => hy.1) _ _
    (alw_of_safeO S sp _ Rl ks hks (C.step s.1 m) s.2 _ (htidy _ _ _ hs) (hcall m k s.1 s.2 hs))

end Compile.Batch.Disc
