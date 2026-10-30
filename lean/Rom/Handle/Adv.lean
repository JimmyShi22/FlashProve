-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/Handle/Adv.lean: the run of an oracle algorithm under a rule for answering its queries
(Rom/Handle/Defs.lean), WRITTEN AS A PROGRAM OF AN ADVERSARY. Definitions, and the lemmas that tie
them to the laws of Rom/Handle/Defs.lean. General in the family of oracles.

General lemmas. This file states no goal of the release.

Why. A reduction (Wrap, Compile/Step1_defc_Gen.lean) is made of programs of the type Adv
(Rom/World.lean): trees of draws, queries and calls. A law (PMF) cannot stand inside such a tree.
The rules of Rom/Handle/Defs.lean draw from finite types alone, so each of them can be written as a
tree of draws. Here that is done once.

  HandlerA S Out In σ   a rule whose moves are programs of an adversary.
  OComp.interpA hA      the run of an algorithm under such a rule, as a program of an adversary.
  HandlerA.lazy         lazy sampling from a table that is PART OF THE STATE. No query is passed on
                        to the challenger. A fresh entry is one draw, through the library's
                        enumeration of a finite type (finEnum, Rom/LateAdv.lean).
  HandlerA.fixed, .idle, .defer mk hA, .replay mk hA   the twins of the rules of that name.
  Realises hA h         against every challenger and from every state of it, each move of hA has the
                        law of h's move, and the challenger's state is left alone.
  interact_interpA      **the tie**: if hA realises h, the program c.interpA hA s, run against any
                        challenger, has the law c.interp h s, and the challenger's state is left
                        alone.
  realises_lazy, realises_fixed, realises_idle, Realises.defer, Realises.replay
  OComp.runLazyA, .runDeferA, .runReplayA, .recordA   the twins of OComp.runLazy, .runDefer,
                        .runReplay and .record, each with its tie (interact_runLazyA …).
  QuietA, quiet_interpA, …   these programs make neither a query nor a call (Adv.Quiet,
                        Rom/LateAdv.lean).
Follows the pattern of LStep.toAdv and interact_toAdv (Rom/LateAdv.lean).

-/
import Rom.Handle.Laws
import Rom.LateAdv
import Compile.Step1_defc_Gen

set_option autoImplicit false

noncomputable section

namespace Rom
open Prob
variable {S : OSpec} {Out In σ α β : Type}

/-- A rule for answering queries whose moves are programs of an adversary. -/
abbrev HandlerA (S : OSpec) (Out In σ : Type) : Type :=
  σ → (o : S.ι) → S.Dom o → Adv S Out In (S.Rng o × σ)

/-- One uniform draw from a finite type, then k. -/
def Adv.draw (β : Type) [Fintype β] [Nonempty β] (k : β → Adv S Out In α) : Adv S Out In α :=
  .sample (Fintype.card β - 1) fun r => k (finEnum β r)

theorem interact_draw (G : World S Out In) (β : Type) [Fintype β] [Nonempty β]
    (k : β → Adv S Out In α) (g : G.σ) :
    interact G (Adv.draw β k) g = (unif β).bind fun b => interact G (k b) g :=
  unif_enum_bind β fun b => interact G (k b) g

/-- **The run of an algorithm under a rule hA, as a program of an adversary.** -/
def OComp.interpA (hA : HandlerA S Out In σ) : OComp S α → σ → Adv S Out In (α × σ)
  | .pure a, s => .halt (a, s)
  | .query o q k, s => (hA s o q).bind fun p => (k p.1).interpA hA p.2
  | .sample n k, s => .sample n fun r => (k r).interpA hA s

/-- The next of the recorded answers for the oracle o, as a program (Record.next). -/
def Record.nextA (o : S.ι) : Record S → Adv S Out In (S.Rng o × Record S × Bool)
  | [] => Adv.draw (S.Rng o) fun r => .halt (r, [], true)
  | a :: R =>
      if e : a.1 = o then .halt (e ▸ a.2, R, false)
      else Adv.draw (S.Rng o) fun r => .halt (r, R, true)

namespace HandlerA

/-- Lazy sampling from a table that is the state. -/
def lazy : HandlerA S Out In (Table S) := fun T o q =>
  match T o q with
  | some r => .halt (r, T)
  | none => Adv.draw (S.Rng o) fun r => .halt (r, T.set o q r)

/-- Every query answered by a function. -/
def fixed (f : Fam S) : HandlerA S Out In Unit := fun _ o q => .halt (f o q, ())

/-- Every query answered by an arbitrary fixed value. -/
def idle : HandlerA S Out In Unit := fixed fun _ _ => Classical.arbitrary _

/-- Deferred queries get fresh answers, which are logged; the others go to hA. -/
def defer (mk : Mark S) (hA : HandlerA S Out In σ) : HandlerA S Out In (σ × Trace S) :=
  fun s o q =>
    if mk o q then Adv.draw (S.Rng o) fun r => .halt (r, (s.1, s.2 ++ [⟨o, q, r⟩]))
    else (hA s.1 o q).bind fun p => .halt (p.1, (p.2, s.2))

/-- Deferred queries get the recorded answers, in their order, and are logged; the others go to hA.
-/
def replay (mk : Mark S) (hA : HandlerA S Out In σ) : HandlerA S Out In (RSt S σ) :=
  fun s o q =>
    if mk o q then (Record.nextA o s.left).bind fun p =>
      .halt (p.1, { s with log := s.log ++ [⟨o, q, p.1⟩], left := p.2.1, miss := s.miss || p.2.2 })
    else (hA s.base o q).bind fun p => .halt (p.1, { s with base := p.2 })

end HandlerA

/-- Against every challenger, each move of hA has the law of h's move and leaves the challenger's
state alone. -/
def Realises (hA : HandlerA S Out In σ) (h : Handler S σ) : Prop :=
  ∀ (G : World S Out In) (g : G.σ) (s : σ) (o : S.ι) (q : S.Dom o),
    interact G (hA s o q) g = (h s o q).map fun p => (p, g)

/-- **The tie.** If hA realises h, the program c.interpA hA s has, against any challenger, the law
c.interp h s, and leaves the challenger's state alone. -/
theorem interact_interpA {hA : HandlerA S Out In σ} {h : Handler S σ} (hr : Realises hA h)
    (G : World S Out In) (c : OComp S α) : ∀ (s : σ) (g : G.σ),
    interact G (c.interpA hA s) g = (c.interp h s).map fun y => (y, g) := by
  induction c with
  | pure a =>
    intro s g
    simp only [OComp.interpA, interact, OComp.interp, PMF.pure_map]
  | query o q k ih =>
    intro s g
    simp only [OComp.interpA, interact_bind, hr G g s o q, PMF.bind_map, Function.comp_def, ih,
      OComp.interp, PMF.map_bind]
  | sample n k ih =>
    intro s g
    simp only [OComp.interpA, interact, ih, OComp.interp, PMF.map_bind]

theorem interact_nextA (G : World S Out In) (g : G.σ) (o : S.ι) (R : Record S) :
    interact G (Record.nextA o R) g = (Record.next o R).map fun p => (p, g) := by
  cases R with
  | nil =>
    simp only [Record.nextA, Record.next, interact_draw, interact, PMF.map_comp]
    rfl
  | cons a R =>
    by_cases e : a.1 = o
    · simp only [Record.nextA, Record.next, dif_pos e, interact, PMF.pure_map]
    · simp only [Record.nextA, Record.next, dif_neg e, interact_draw, interact, PMF.map_comp]
      rfl

theorem realises_lazy : Realises (HandlerA.lazy (S := S) (Out := Out) (In := In)) Handler.lazy := by
  intro G g T o q
  cases hT : T o q with
  | some r =>
    simp only [HandlerA.lazy, Handler.lazy, lazyAnswer, hT, interact, PMF.pure_map]
  | none =>
    simp only [HandlerA.lazy, Handler.lazy, lazyAnswer, hT, interact_draw, interact, PMF.map_comp]
    rfl

theorem realises_fixed (f : Fam S) :
    Realises (HandlerA.fixed (Out := Out) (In := In) f) (Handler.fixed f) := by
  intro G g s o q
  simp only [HandlerA.fixed, Handler.fixed, interact, PMF.pure_map]

theorem realises_idle : Realises (HandlerA.idle (S := S) (Out := Out) (In := In)) Handler.idle :=
  realises_fixed _

theorem Realises.defer {hA : HandlerA S Out In σ} {h : Handler S σ} (hr : Realises hA h)
    (mk : Mark S) : Realises (HandlerA.defer mk hA) (Handler.defer mk h) := by
  rintro G g ⟨b, l⟩ o q
  cases hm : mk o q with
  | false =>
    rw [Handler.defer_of_not h hm]
    have e : HandlerA.defer mk hA (b, l) o q = (hA b o q).bind fun p => .halt (p.1, (p.2, l)) :=
      if_neg (by rw [hm]; exact Bool.false_ne_true)
    rw [e, interact_bind, hr G g b o q, PMF.bind_map, PMF.map_comp]
    rfl
  | true =>
    rw [Handler.defer_of_mark h hm]
    have e : HandlerA.defer mk hA (b, l) o q =
        Adv.draw (S.Rng o) fun r => .halt (r, (b, l ++ [⟨o, q, r⟩])) := if_pos hm
    rw [e, interact_draw, PMF.map_comp]
    rfl

theorem Realises.replay {hA : HandlerA S Out In σ} {h : Handler S σ} (hr : Realises hA h)
    (mk : Mark S) : Realises (HandlerA.replay mk hA) (Handler.replay mk h) := by
  rintro G g ⟨b, l, R, m⟩ o q
  cases hm : mk o q with
  | false =>
    rw [Handler.replay_of_not h hm]
    have e : HandlerA.replay mk hA ⟨b, l, R, m⟩ o q =
        (hA b o q).bind fun p => .halt (p.1, ⟨p.2, l, R, m⟩) :=
      if_neg (by rw [hm]; exact Bool.false_ne_true)
    rw [e, interact_bind, hr G g b o q, PMF.bind_map, PMF.map_comp]
    rfl
  | true =>
    rw [Handler.replay_of_mark h hm]
    have e : HandlerA.replay mk hA ⟨b, l, R, m⟩ o q =
        (Record.nextA o R).bind fun p =>
          .halt (p.1, ⟨b, l ++ [⟨o, q, p.1⟩], p.2.1, m || p.2.2⟩) := if_pos hm
    rw [e, interact_bind, interact_nextA, PMF.bind_map, PMF.map_comp]
    rfl

/-! ## The four runs as programs -/

namespace OComp

/-- runLazy as a program: the table is an argument and comes back with the output. -/
def runLazyA (c : OComp S α) (T : Table S) : Adv S Out In (α × Table S) :=
  c.interpA HandlerA.lazy T

/-- runDefer as a program. -/
def runDeferA (mk : Mark S) (c : OComp S α) (T : Table S) (lg : Trace S) :
    Adv S Out In (α × Table S × Trace S) :=
  c.interpA (HandlerA.defer mk HandlerA.lazy) (T, lg)

/-- runReplay as a program. -/
def runReplayA (mk : Mark S) (c : OComp S α) (T : Table S) (lg : Trace S) (R : Record S) :
    Adv S Out In (α × RSt S (Table S)) :=
  c.interpA (HandlerA.replay mk HandlerA.lazy) ⟨T, lg, R, false⟩

/-- OComp.record as a program. -/
def recordA (mk : Mark S) (c : OComp S α) : Adv S Out In (α × Record S) :=
  (c.interpA (HandlerA.defer mk HandlerA.idle) ((), [])).bind fun x =>
    .halt (x.1, x.2.2.answers)

end OComp

theorem interact_runLazyA (G : World S Out In) (c : OComp S α) (T : Table S) (g : G.σ) :
    interact G (c.runLazyA T) g = (c.runLazy T).map fun y => (y, g) := by
  rw [← OComp.interp_lazy]
  exact interact_interpA realises_lazy G c T g

theorem interact_runDeferA (G : World S Out In) (mk : Mark S) (c : OComp S α) (T : Table S)
    (lg : Trace S) (g : G.σ) :
    interact G (c.runDeferA mk T lg) g = (c.runDefer mk T lg).map fun y => (y, g) :=
  interact_interpA (realises_lazy.defer mk) G c (T, lg) g

theorem interact_runReplayA (G : World S Out In) (mk : Mark S) (c : OComp S α) (T : Table S)
    (lg : Trace S) (R : Record S) (g : G.σ) :
    interact G (c.runReplayA mk T lg R) g = (c.runReplay mk T lg R).map fun y => (y, g) :=
  interact_interpA (realises_lazy.replay mk) G c ⟨T, lg, R, false⟩ g

theorem interact_recordA (G : World S Out In) (mk : Mark S) (c : OComp S α) (g : G.σ) :
    interact G (c.recordA mk) g = (c.record mk).map fun y => (y, g) := by
  rw [OComp.recordA, interact_bind, interact_interpA (realises_idle.defer mk) G c ((), []) g,
    PMF.bind_map, OComp.record, PMF.map_comp]
  rfl

/-! ## Neither a query nor a call -/

theorem Adv.Quiet.bind {A : Adv S Out In α} {f : α → Adv S Out In β} (hA : A.Quiet)
    (hf : ∀ a, (f a).Quiet) : (A.bind f).Quiet := by
  induction A with
  | halt a => exact hf a
  | sample n k ih => exact fun r => ih r (hA r)
  | query o q k _ => exact hA.elim
  | call m k _ => exact hA.elim

/-- Every move of the rule makes neither a query nor a call. -/
def QuietA (hA : HandlerA S Out In σ) : Prop := ∀ s o q, (hA s o q).Quiet

theorem quiet_interpA {hA : HandlerA S Out In σ} (hq : QuietA hA) (c : OComp S α) :
    ∀ s, (c.interpA hA s).Quiet := by
  induction c with
  | pure a => exact fun _ => trivial
  | query o q k ih => exact fun s => (hq s o q).bind fun p => ih p.1 p.2
  | sample n k ih => exact fun s r => ih r s

theorem quiet_nextA (o : S.ι) (R : Record S) :
    (Record.nextA (Out := Out) (In := In) o R).Quiet := by
  cases R with
  | nil => exact fun _ => trivial
  | cons a R =>
    by_cases e : a.1 = o
    · simp only [Record.nextA, dif_pos e]
      trivial
    · simp only [Record.nextA, dif_neg e]
      exact fun _ => trivial

theorem quietA_lazy : QuietA (HandlerA.lazy (S := S) (Out := Out) (In := In)) := by
  intro T o q
  cases hT : T o q with
  | some r =>
    simp only [HandlerA.lazy, hT]
    trivial
  | none =>
    simp only [HandlerA.lazy, hT]
    exact fun _ => trivial

theorem quietA_idle : QuietA (HandlerA.idle (S := S) (Out := Out) (In := In)) :=
  fun _ _ _ => trivial

theorem QuietA.defer {hA : HandlerA S Out In σ} (hq : QuietA hA) (mk : Mark S) :
    QuietA (HandlerA.defer mk hA) := by
  intro s o q
  cases hm : mk o q with
  | false =>
    have e : HandlerA.defer mk hA s o q = (hA s.1 o q).bind fun p => .halt (p.1, (p.2, s.2)) :=
      if_neg (by rw [hm]; exact Bool.false_ne_true)
    rw [e]
    exact (hq s.1 o q).bind fun _ => trivial
  | true =>
    have e : HandlerA.defer mk hA s o q =
        Adv.draw (S.Rng o) fun r => .halt (r, (s.1, s.2 ++ [⟨o, q, r⟩])) := if_pos hm
    rw [e]
    exact fun _ => trivial

theorem QuietA.replay {hA : HandlerA S Out In σ} (hq : QuietA hA) (mk : Mark S) :
    QuietA (HandlerA.replay mk hA) := by
  intro s o q
  cases hm : mk o q with
  | false =>
    have e : HandlerA.replay mk hA s o q =
        (hA s.base o q).bind fun p => .halt (p.1, { s with base := p.2 }) :=
      if_neg (by rw [hm]; exact Bool.false_ne_true)
    rw [e]
    exact (hq s.base o q).bind fun _ => trivial
  | true =>
    have e : HandlerA.replay mk hA s o q = (Record.nextA o s.left).bind fun p =>
        .halt (p.1, { s with log := s.log ++ [⟨o, q, p.1⟩], left := p.2.1,
                             miss := s.miss || p.2.2 }) := if_pos hm
    rw [e]
    exact (quiet_nextA o s.left).bind fun _ => trivial

theorem quiet_runLazyA (c : OComp S α) (T : Table S) :
    (c.runLazyA (Out := Out) (In := In) T).Quiet := quiet_interpA quietA_lazy c T

theorem quiet_runDeferA (mk : Mark S) (c : OComp S α) (T : Table S) (lg : Trace S) :
    (c.runDeferA (Out := Out) (In := In) mk T lg).Quiet :=
  quiet_interpA (quietA_lazy.defer mk) c (T, lg)

theorem quiet_runReplayA (mk : Mark S) (c : OComp S α) (T : Table S) (lg : Trace S)
    (R : Record S) : (c.runReplayA (Out := Out) (In := In) mk T lg R).Quiet :=
  quiet_interpA (quietA_lazy.replay mk) c _

end Rom

#print axioms Rom.interact_interpA
#print axioms Rom.interact_runDeferA
#print axioms Rom.interact_runReplayA
#print axioms Rom.interact_recordA
