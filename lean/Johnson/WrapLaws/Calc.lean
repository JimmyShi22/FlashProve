-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/WrapLaws/Calc.lean: two small calculi for programs of an adversary (Rom.Adv), by which a
reduction around the game of Hiop/Seeded/Game.lean is shown to be admissible and consistent.
Definitions, lemmas and proofs. No scheme occurs here. This file states no goal of the release.
Devices of a proof: Tame and KeepsBy stand in no statement on the scheme.

Part 1 (namespace Hiop.Seeded). Tame ok A n: every session that A calls for is allowed (A.CallsOK
  (okCall ok)), and on every path A makes at most n calls for a session (SessLe,
  Hiop/Seeded/Total.lean): the two premises on an adversary in Spec.lifeSeededN and in
  Spec.lifeSeededAt (Hiop/Seeded/AtIndex.lean). Rules: a program that makes neither a query nor a
  call is tame at every n; a sequence adds the numbers; a call for a session costs 1, every other
  call nothing.
Part 2 (namespace Rom). KeepsBy π T P: against every challenger, from every state of it, the table
  that π reads off P's output holds every entry of T. Rules: a sequence; a call; and the runs of an
  oracle algorithm as programs (runLazyA, runDeferA, runReplayA, Rom/Handle/Adv.lean) keep the table
  that they are handed. interp_rel: a relation on states that every move of a rule keeps is kept by
  the run of an algorithm under that rule.
KeepsBy and its rules halt, call and bind follow KeepsBP, keepsBP_halt, keepsBP_call and
keepsBP_toAdv_bind (Compile/Batch/PubWr.lean) closely: the same definition and proofs, with the
place of the table in the output and the scheme's types made letters.
Terms: lean/GLOSSARY.md.

-/
import Hiop.Seeded.Total
import Rom.Handle.Adv

set_option autoImplicit false

noncomputable section

/-! ## Part 1. Allowed calls, and at most n sessions -/

namespace Hiop.Seeded
open Prob Iop Rom

variable {I X : Type} {L : HolographicProtocol I X} {F : Form X} {S : OSpec} {α β : Type}

theorem SessLe.succ (A : Adv S (GOut L F) (GIn L F) α) : ∀ n, SessLe A n → SessLe A (n + 1) := by
  induction A with
  | halt a => intro _ _; exact trivial
  | sample m k ih => intro n h r; exact ih r n (h r)
  | query o q k ih => intro n h r; exact ih r n (h r)
  | call c k ih =>
    intro n h
    cases c with
    | table s => exact fun a => ih a n (h a)
    | test e => exact fun a => ih a n (h a)
    | link e => exact fun a => ih a n (h a)
    | read e p => exact fun a => ih a n (h a)
    | sess e q hq =>
      cases n with
      | zero => exact h.elim
      | succ j => exact fun a => ih a j (h a)

theorem SessLe.le {A : Adv S (GOut L F) (GIn L F) α} {n m : ℕ} (h : SessLe A n) (hnm : n ≤ m) :
    SessLe A m := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact SessLe.succ A _ ih

/-- Every session that A calls for is allowed, and on every path there are at most n such calls. -/
def Tame (ok : X → Prop) (A : Adv S (GOut L F) (GIn L F) α) (n : ℕ) : Prop :=
  A.CallsOK (okCall ok) ∧ SessLe A n

namespace Tame
variable {ok : X → Prop}

theorem le {A : Adv S (GOut L F) (GIn L F) α} {n m : ℕ} (h : Tame ok A n) (hnm : n ≤ m) :
    Tame ok A m := ⟨h.1, h.2.le hnm⟩

theorem halt (a : α) (n : ℕ) : Tame ok (.halt a : Adv S (GOut L F) (GIn L F) α) n :=
  ⟨trivial, trivial⟩

theorem of_quiet {A : Adv S (GOut L F) (GIn L F) α} (h : A.Quiet) (n : ℕ) : Tame ok A n := by
  induction A with
  | halt a => exact halt a n
  | sample m k ih => exact ⟨fun r => (ih r (h r)).1, fun r => (ih r (h r)).2⟩
  | query o q k _ => exact h.elim
  | call c k _ => exact h.elim

theorem table (s : L.OutOfDomainSeed) {k : GIn L F → Adv S (GOut L F) (GIn L F) α} {n : ℕ}
    (h : ∀ a, Tame ok (k a) n) : Tame ok (.call (.table s) k) n :=
  ⟨⟨trivial, fun a => (h a).1⟩, fun a => (h a).2⟩

theorem test (e : ℕ) {k : GIn L F → Adv S (GOut L F) (GIn L F) α} {n : ℕ}
    (h : ∀ a, Tame ok (k a) n) : Tame ok (.call (.test e) k) n :=
  ⟨⟨trivial, fun a => (h a).1⟩, fun a => (h a).2⟩

theorem link (e : ℕ) {k : GIn L F → Adv S (GOut L F) (GIn L F) α} {n : ℕ}
    (h : ∀ a, Tame ok (k a) n) : Tame ok (.call (.link e) k) n :=
  ⟨⟨trivial, fun a => (h a).1⟩, fun a => (h a).2⟩

theorem sess (e : ℕ) {q : F.QB} {hq : F.HB q} (ho : F.okB ok q hq)
    {k : GIn L F → Adv S (GOut L F) (GIn L F) α} {n : ℕ} (h : ∀ a, Tame ok (k a) n) :
    Tame ok (.call (.sess e q hq) k) (n + 1) :=
  ⟨⟨ho, fun a => (h a).1⟩, fun a => (h a).2⟩

/-- A sequence adds the numbers. -/
theorem bind {A : Adv S (GOut L F) (GIn L F) α} {f : α → Adv S (GOut L F) (GIn L F) β} {n : ℕ}
    (hf : ∀ a, Tame ok (f a) n) : ∀ {m : ℕ}, Tame ok A m → Tame ok (A.bind f) (m + n) := by
  induction A with
  | halt a => intro m _; exact (hf a).le (Nat.le_add_left n m)
  | sample j k ih =>
    intro m hA
    exact ⟨fun r => (ih r ⟨hA.1 r, hA.2 r⟩).1, fun r => (ih r ⟨hA.1 r, hA.2 r⟩).2⟩
  | query o q k ih =>
    intro m hA
    exact ⟨fun r => (ih r ⟨hA.1 r, hA.2 r⟩).1, fun r => (ih r ⟨hA.1 r, hA.2 r⟩).2⟩
  | call c k ih =>
    intro m hA
    cases c with
    | table s =>
      exact ⟨⟨trivial, fun a => (ih a ⟨hA.1.2 a, hA.2 a⟩).1⟩, fun a => (ih a ⟨hA.1.2 a, hA.2 a⟩).2⟩
    | test e =>
      exact ⟨⟨trivial, fun a => (ih a ⟨hA.1.2 a, hA.2 a⟩).1⟩, fun a => (ih a ⟨hA.1.2 a, hA.2 a⟩).2⟩
    | link e =>
      exact ⟨⟨trivial, fun a => (ih a ⟨hA.1.2 a, hA.2 a⟩).1⟩, fun a => (ih a ⟨hA.1.2 a, hA.2 a⟩).2⟩
    | read e p =>
      exact ⟨⟨trivial, fun a => (ih a ⟨hA.1.2 a, hA.2 a⟩).1⟩, fun a => (ih a ⟨hA.1.2 a, hA.2 a⟩).2⟩
    | sess e q hq =>
      cases m with
      | zero => exact hA.2.elim
      | succ j =>
        have e1 : j + 1 + n = j + n + 1 := by omega
        rw [e1]
        exact ⟨⟨hA.1.1, fun a => (ih a ⟨hA.1.2 a, hA.2 a⟩).1⟩,
          fun a => (ih a ⟨hA.1.2 a, hA.2 a⟩).2⟩

/-- A sequence whose first part calls for no session. -/
theorem bind0 {A : Adv S (GOut L F) (GIn L F) α} {f : α → Adv S (GOut L F) (GIn L F) β} {n : ℕ}
    (hA : Tame ok A 0) (hf : ∀ a, Tame ok (f a) n) : Tame ok (A.bind f) n := by
  have h := bind hf hA
  rw [Nat.zero_add] at h
  exact h

end Tame
end Hiop.Seeded

/-! ## Part 2. The table is kept -/

namespace Rom
open Prob

variable {S : OSpec} {Out In σ α β γ : Type}

/-- A relation on states that is reflexive and transitive and that every move of the rule h keeps is
kept by the run of an algorithm under h. -/
theorem interp_rel {h : Handler S σ} {Rel : σ → σ → Prop} (hr : ∀ s, Rel s s)
    (ht : ∀ s s' s'', Rel s s' → Rel s' s'' → Rel s s'')
    (hh : ∀ s o q, ∀ p ∈ (h s o q).support, Rel s p.2) (c : OComp S α) :
    ∀ s, ∀ x ∈ (c.interp h s).support, Rel s x.2 := by
  induction c with
  | pure a =>
    intro s x hx
    rw [(PMF.mem_support_pure_iff _ _).1 hx]
    exact hr s
  | query o q k ih =>
    intro s x hx
    obtain ⟨p, hp, hx⟩ := (PMF.mem_support_bind_iff _ _ _).1 hx
    exact ht _ _ _ (hh s o q p hp) (ih p.1 p.2 x hx)
  | sample n k ih =>
    intro s x hx
    obtain ⟨r, -, hx⟩ := (PMF.mem_support_bind_iff _ _ _).1 hx
    exact ih r s x hx

theorem lazyAnswer_sub (T : Table S) (o : S.ι) (q : S.Dom o) :
    ∀ p ∈ (lazyAnswer T o q).support, T.Sub p.2 := by
  intro p hp
  cases hT : T o q with
  | some r =>
    rw [lazyAnswer_of_some hT] at hp
    rw [(PMF.mem_support_pure_iff _ _).1 hp]
    exact Table.Sub.refl T
  | none =>
    rw [lazyAnswer_of_none hT] at hp
    obtain ⟨r, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hp
    exact Table.sub_set hT r

theorem defer_sub (mk : Mark S) (s : Table S × Trace S) (o : S.ι) (q : S.Dom o) :
    ∀ p ∈ (Handler.defer mk Handler.lazy s o q).support, s.1.Sub p.2.1 := by
  intro p hp
  cases hm : mk o q with
  | true =>
    have e : Handler.defer mk Handler.lazy s o q =
        (unif (S.Rng o)).map fun r => (r, (s.1, s.2 ++ [⟨o, q, r⟩])) := if_pos hm
    rw [e] at hp
    obtain ⟨r, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hp
    exact Table.Sub.refl _
  | false =>
    have e : Handler.defer mk Handler.lazy s o q =
        (lazyAnswer s.1 o q).map fun p => (p.1, (p.2, s.2)) :=
      if_neg (by rw [hm]; exact Bool.false_ne_true)
    rw [e] at hp
    obtain ⟨y, hy, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hp
    exact lazyAnswer_sub _ o q y hy

theorem replay_sub (mk : Mark S) (s : RSt S (Table S)) (o : S.ι) (q : S.Dom o) :
    ∀ p ∈ (Handler.replay mk Handler.lazy s o q).support, s.base.Sub p.2.base := by
  intro p hp
  cases hm : mk o q with
  | true =>
    have e : Handler.replay mk Handler.lazy s o q = (Record.next o s.left).map fun p =>
        (p.1, { s with log := s.log ++ [⟨o, q, p.1⟩], left := p.2.1,
                       miss := s.miss || p.2.2 }) := if_pos hm
    rw [e] at hp
    obtain ⟨y, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hp
    exact Table.Sub.refl _
  | false =>
    have e : Handler.replay mk Handler.lazy s o q =
        (lazyAnswer s.base o q).map fun p => (p.1, { s with base := p.2 }) :=
      if_neg (by rw [hm]; exact Bool.false_ne_true)
    rw [e] at hp
    obtain ⟨y, hy, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hp
    exact lazyAnswer_sub _ o q y hy

/-- Writing a log keeps every entry that stands. -/
theorem Table.sub_lay (T : Table S) (l : Trace S) : T.Sub (T.lay l) :=
  fun _ _ _ h => Table.lay_of_some l h

/-- Against every challenger, from every state of it, the table that π reads off P's output holds
every entry of T. -/
def KeepsBy (π : β → Table S) (T : Table S) (P : Adv S Out In β) : Prop :=
  ∀ (G : World S Out In) (g : G.σ), ∀ z ∈ (interact G P g).support, T.Sub (π z.1)

namespace KeepsBy

theorem halt {π : β → Table S} {T : Table S} {a : β} (h : T.Sub (π a)) :
    KeepsBy π T (.halt a : Adv S Out In β) := by
  intro G g z hz
  simp only [interact, PMF.support_pure, Set.mem_singleton_iff] at hz
  rw [hz]
  exact h

theorem call {π : β → Table S} {T : Table S} (m : Out) {k : In → Adv S Out In β}
    (h : ∀ a, KeepsBy π T (k a)) : KeepsBy π T (.call m k) := by
  intro G g z hz
  simp only [interact, PMF.mem_support_bind_iff] at hz
  obtain ⟨y, -, hz⟩ := hz
  exact h y.1 G y.2 z hz

theorem bind {π₁ : β → Table S} {π₂ : γ → Table S} {T : Table S} {A : Adv S Out In β}
    {f : β → Adv S Out In γ} (hA : KeepsBy π₁ T A) (hf : ∀ a, KeepsBy π₂ (π₁ a) (f a)) :
    KeepsBy π₂ T (A.bind f) := by
  intro G g z hz
  rw [interact_bind] at hz
  obtain ⟨y, hy, hz⟩ := (PMF.mem_support_bind_iff _ _ _).1 hz
  exact (hA G g y hy).trans (hf y.1 G y.2 z hz)

theorem runLazyA (c : OComp S α) (T : Table S) :
    KeepsBy Prod.snd T (c.runLazyA (Out := Out) (In := In) T) := by
  intro G g z hz
  rw [interact_runLazyA, ← OComp.interp_lazy] at hz
  obtain ⟨y, hy, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hz
  exact interp_rel (Rel := Table.Sub) Table.Sub.refl (fun _ _ _ => Table.Sub.trans)
    (fun s o q => lazyAnswer_sub s o q) c T y hy

theorem runDeferA (mk : Mark S) (c : OComp S α) (T : Table S) (lg : Trace S) :
    KeepsBy (fun x : α × Table S × Trace S => x.2.1) T
      (c.runDeferA (Out := Out) (In := In) mk T lg) := by
  intro G g z hz
  rw [interact_runDeferA] at hz
  obtain ⟨y, hy, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hz
  exact interp_rel (Rel := fun s s' : Table S × Trace S => s.1.Sub s'.1)
    (fun s => Table.Sub.refl s.1) (fun _ _ _ => Table.Sub.trans) (defer_sub mk) c (T, lg) y hy

theorem runReplayA (mk : Mark S) (c : OComp S α) (T : Table S) (lg : Trace S) (R : Record S) :
    KeepsBy (fun x : α × RSt S (Table S) => x.2.base) T
      (c.runReplayA (Out := Out) (In := In) mk T lg R) := by
  intro G g z hz
  rw [interact_runReplayA] at hz
  obtain ⟨y, hy, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hz
  exact interp_rel (Rel := fun s s' : RSt S (Table S) => s.base.Sub s'.base)
    (fun s => Table.Sub.refl s.base) (fun _ _ _ => Table.Sub.trans) (replay_sub mk) c
    ⟨T, lg, R, false⟩ y hy

end KeepsBy
end Rom

#print axioms Hiop.Seeded.Tame.bind
#print axioms Rom.KeepsBy.runReplayA
