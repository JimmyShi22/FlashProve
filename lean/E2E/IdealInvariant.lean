-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/IdealInvariant.lean: what the programs of the scheme's simulator do to the state of the
simulated game: if every OOD seed is in Gs the setup is never refused, and a request raises each
count of sessions by at most one.

Summary. E2E/IdealOneCall.lean bounds one request from a good state of the reduction
(Johnson/WholeKey/Wrap.lean) and of the simulated game (Hiop/Seeded/Game.lean). This file proves
that the good states are kept: after the setup, after a request and after an oracle query. The
arguments are on supports: no probability occurs.

Main results.
  `keeps_setupA`: if every OOD seed is in Gs, then after the setup the reduction holds all M + 1
    copies, the game has made M + 1 further tables, and no session is counted.
  `keeps_proveStepA`: a request leaves what the reduction holds and the number of tables; each count
    of sessions grows by at most one. `keeps_ans`: an oracle query leaves all of these.

Terms: E2E/HidingTerms.lean.

Limits. About counts alone: nothing about what is given out. Whether the game refuses the call for
the first table's proof or for a link is not examined: neither changes these counts. No security
property is stated.

Definitions and helper lemmas.
  `GAt H c k gs`: the game has made c further tables, and at most k sessions have been run on each.
  `Keeps H B Gs A Pre Post`: from a state of the game with Pre, whatever the program A returns comes
    with a state with Post.
  `WAt W h w`: the reduction holds all M + 1 copies. Two local signs: 𝔉 is the simulated game's host
    (`hostOf W r₀ h Sm i₀`), 𝓛 the bounds on its counts (`boundsW h s1`).
  `reply_first`, `reply_table`, `reply_test`, `reply_link`, `reply_sess_at`: the game's state after
    each call, for an arbitrary host.
  `keeps_halt`, `keeps_bind`, `keeps_call`, `keeps_quiet`, `keeps_quiet_supp`, `keeps_weaken`: the
    rules for `Keeps`.
  `keeps_pass2A`, `keeps_tableA_first`, `keeps_tableA`, `keeps_tablesA`, `keeps_linksA`: the parts
    of the setup.


-/
import E2E.IdealOneCall

set_option autoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace AtPublicFiles.Shown
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover OnBytes.WholeKey OnBytes.Dry
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open Hiop.Seeded (gameSim gameW gameReply HostF GSt GOut GIn)
open scoped ENNReal

/-! ## 1. The game's state after a call, for an arbitrary host -/

section Game
variable {I X : Type} {L : HolographicProtocol I X} {F : Hiop.Seeded.Form X} (H : HostF L F) (B : Hiop.BoundsR)
  (Gs : L.OutOfDomainSeed → Prop)

/-- The number of further tables is c, and at most k sessions have been run on each. -/
def GAt (c k : ℕ) (gs : GSt H) : Prop := ∃ u st, gs = some (c, u, st) ∧ ∀ e, u.sess e ≤ k

theorem reply_first (hGs : ∀ s, Gs s) (s : L.OutOfDomainSeed) :
    ∀ p ∈ (gameReply H B Gs none (.table s)).support, (∃ rc, p.1 = .ood rc) ∧ GAt H 0 0 p.2 := by
  intro p hp
  simp only [gameReply] at hp
  rw [if_pos (hGs s)] at hp
  obtain ⟨q, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hp
  exact ⟨⟨_, rfl⟩, _, _, rfl, fun _ => Nat.le_refl _⟩

theorem reply_table (hGs : ∀ s, Gs s) (s : L.OutOfDomainSeed) {c k : ℕ} {gs : GSt H} (hg : GAt H c k gs)
    (hc : c < B.nenc) :
    ∀ p ∈ (gameReply H B Gs gs (.table s)).support,
      (∃ rc, p.1 = .ood rc) ∧ GAt H (c + 1) k p.2 := by
  obtain ⟨u, st, rfl, hu⟩ := hg
  intro p hp
  simp only [gameReply] at hp
  rw [if_pos ⟨hGs s, hc⟩] at hp
  obtain ⟨q, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hp
  exact ⟨⟨_, rfl⟩, _, _, rfl, hu⟩

theorem reply_test (e : ℕ) {c k : ℕ} {gs : GSt H} (hg : GAt H c k gs) :
    ∀ p ∈ (gameReply H B Gs gs (.test e)).support, GAt H c k p.2 := by
  obtain ⟨u, st, rfl, hu⟩ := hg
  intro p hp
  simp only [gameReply] at hp
  split at hp
  · obtain ⟨q, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hp
    exact ⟨_, _, rfl, hu⟩
  · obtain rfl := (PMF.mem_support_pure_iff _ _).1 hp
    exact ⟨_, _, rfl, hu⟩

theorem reply_link (e : ℕ) {c k : ℕ} {gs : GSt H} (hg : GAt H c k gs) :
    ∀ p ∈ (gameReply H B Gs gs (.link e)).support, GAt H c k p.2 := by
  obtain ⟨u, st, rfl, hu⟩ := hg
  intro p hp
  simp only [gameReply] at hp
  split at hp
  · obtain ⟨q, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hp
    exact ⟨_, _, rfl, hu⟩
  · obtain rfl := (PMF.mem_support_pure_iff _ _).1 hp
    exact ⟨_, _, rfl, hu⟩

theorem reply_sess_at (e : ℕ) (q : F.QB) (hq : F.HB q) {c k : ℕ} {gs : GSt H}
    (hg : GAt H c k gs) :
    ∀ p ∈ (gameReply H B Gs gs (.sess e q hq)).support, GAt H c (k + 1) p.2 := by
  obtain ⟨u, st, rfl, hu⟩ := hg
  intro p hp
  simp only [gameReply] at hp
  split at hp
  · obtain ⟨y, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hp
    refine ⟨_, _, rfl, fun e' => ?_⟩
    show Hiop.bump u.sess e e' ≤ k + 1
    unfold Hiop.bump
    by_cases he : e' = e
    · subst he
      rw [Function.update_self]
      exact Nat.succ_le_succ (hu _)
    · rw [Function.update_of_ne he]
      exact (hu _).trans (Nat.le_succ _)
  · obtain rfl := (PMF.mem_support_pure_iff _ _).1 hp
    exact ⟨_, _, rfl, fun e' => (hu _).trans (Nat.le_succ _)⟩

/-! ## 2. Programs against the game: what they do to its state -/

variable {S' : OSpec} {α β : Type}

/-- From a state of the game with Pre, whatever the program returns comes with a state with Post. -/
def Keeps (A : Adv S' (GOut L F) (GIn L F) α) (Pre : GSt H → Prop) (Post : α → GSt H → Prop) :
    Prop :=
  ∀ gs T, Pre gs → ∀ y ∈ (interact (gameW H B Gs S') A (gs, T)).support, Post y.1 y.2.1

theorem keeps_halt (a : α) (Pre : GSt H → Prop) :
    Keeps H B Gs (.halt a : Adv S' (GOut L F) (GIn L F) α) Pre fun b gs => b = a ∧ Pre gs := by
  intro gs T hp y hy
  obtain rfl : y = (a, (gs, T)) := (PMF.mem_support_pure_iff _ _).1 hy
  exact ⟨rfl, hp⟩

theorem keeps_bind {A : Adv S' (GOut L F) (GIn L F) α} {f : α → Adv S' (GOut L F) (GIn L F) β}
    {Pre : GSt H → Prop} {Mid : α → GSt H → Prop} {Post : β → GSt H → Prop}
    (hA : Keeps H B Gs A Pre Mid) (hf : ∀ a, Keeps H B Gs (f a) (Mid a) Post) :
    Keeps H B Gs (A.bind f) Pre Post := by
  intro gs T hp y hy
  rw [interact_bind] at hy
  obtain ⟨z, hz, hy⟩ := (PMF.mem_support_bind_iff _ _ _).1 hy
  exact hf z.1 z.2.1 z.2.2 (hA gs T hp z hz) y hy

theorem keeps_call (m : GOut L F) {k : GIn L F → Adv S' (GOut L F) (GIn L F) α}
    {Pre : GSt H → Prop} {Mid : GIn L F → GSt H → Prop} {Post : α → GSt H → Prop}
    (hm : ∀ gs, Pre gs → ∀ p ∈ (gameReply H B Gs gs m).support, Mid p.1 p.2)
    (hk : ∀ r, Keeps H B Gs (k r) (Mid r) Post) : Keeps H B Gs (.call m k) Pre Post := by
  intro gs T hp y hy
  have hy' : y ∈ (((gameReply H B Gs gs m).map fun p => (p.1, (p.2, T))).bind fun p =>
      interact (gameW H B Gs S') (k p.1) p.2).support := hy
  obtain ⟨z, hz, hy''⟩ := (PMF.mem_support_bind_iff _ _ _).1 hy'
  obtain ⟨p, hp', rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hz
  exact hk p.1 p.2 T (hm gs hp p hp') y hy''

/-- A program that neither asks nor calls the game leaves its state. -/
theorem keeps_quiet {A : Adv S' (GOut L F) (GIn L F) α} {D : PMF α}
    (hA : ∀ g, interact (gameW H B Gs S') A g = D.map fun y => (y, g)) (Pre : GSt H → Prop) :
    Keeps H B Gs A Pre fun _ gs => Pre gs := by
  intro gs T hp y hy
  rw [hA] at hy
  obtain ⟨z, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hy
  exact hp

/-- The same, with what it can return. -/
theorem keeps_quiet_supp {A : Adv S' (GOut L F) (GIn L F) α} {D : PMF α}
    (hA : ∀ g, interact (gameW H B Gs S') A g = D.map fun y => (y, g)) (Pre : GSt H → Prop) :
    Keeps H B Gs A Pre fun a gs => a ∈ D.support ∧ Pre gs := by
  intro gs T hp y hy
  rw [hA] at hy
  obtain ⟨z, hz, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hy
  exact ⟨hz, hp⟩

theorem keeps_weaken {A : Adv S' (GOut L F) (GIn L F) α} {Pre : GSt H → Prop}
    {Post Post' : α → GSt H → Prop} (hA : Keeps H B Gs A Pre Post)
    (h : ∀ a gs, Post a gs → Post' a gs) : Keeps H B Gs A Pre Post' :=
  fun gs T hp y hy => h _ _ (hA gs T hp y hy)

end Game

/-! ## 3. The reduction's programs -/

section Red
variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (h : HonestSide lam L Bd aT aL) (Sm : Sims L) (i₀ : I)
  (s1 : ℕ) (Gs : L.OutOfDomainSeed → Prop)

local notation "𝔉" => hostOf W r₀ h Sm i₀
local notation "𝓛" => boundsW h s1

/-- The second pass leaves the game's state. -/
theorem keeps_pass2A (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout lam W.K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body (typedOracleCarrier L Bd aT aL))
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) t)
      (annOf (typedOracleCarrier L Bd aT aL) t)) (xin : Y → Option L.XC) (cms : List (Dig lam)) (x : Y)
    (xt : ℕ → TreeK lam (typedOracleCarrier L Bd aT aL)) (cap : ℕ → ℕ)
    (embE : E.Sym → Body (typedOracleCarrier L Bd aT aL)) (v : Option (DView Q.loc))
    (co : Coins lam (typedOracleCarrier L Bd aT aL)) (Rc : Record (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)))
    (T : Tb W) (Pre : GSt 𝔉 → Prop) :
    Keeps 𝔉 𝓛 Gs (pass2A t Q wq embS embP xin cms x xt cap embE v co Rc T) Pre
      fun _ gs => Pre gs :=
  keeps_bind 𝔉 𝓛 Gs (keeps_quiet 𝔉 𝓛 Gs (fun g => interact_runReplayA _ _ _ _ _ _ g) Pre)
    fun _ => keeps_weaken 𝔉 𝓛 Gs (keeps_halt 𝔉 𝓛 Gs _ Pre) fun _ _ hh => hh.2

/-- The first table is made. -/
theorem keeps_tableA_first (hGs : ∀ s, Gs s) (s : ℕ → Bits) (T : Tb W) :
    Keeps 𝔉 𝓛 Gs (tableA W S r₀ h s T) (fun gs => gs = none)
      fun y gs => y.1.isSome = true ∧ GAt 𝔉 0 0 gs := by
  refine keeps_bind 𝔉 𝓛 Gs (keeps_quiet 𝔉 𝓛 Gs (fun g => interact_runDeferA _ _ _ _ _ g) _)
    fun o => keeps_call 𝔉 𝓛 Gs _ (Mid := fun r gs => (∃ rc, r = .ood rc) ∧ GAt 𝔉 0 0 gs)
      (fun gs hgs p hp => ?_) fun r => ?_
  · subst hgs
    exact reply_first 𝔉 𝓛 Gs hGs _ p hp
  · intro gs T' hm y hy
    obtain ⟨⟨rc, rfl⟩, hg⟩ := hm
    obtain rfl := (PMF.mem_support_pure_iff _ _).1 hy
    exact ⟨rfl, hg⟩

/-- A further table is made, while there is room. -/
theorem keeps_tableA (hGs : ∀ s, Gs s) (s : ℕ → Bits) (T : Tb W) (c k : ℕ) (hc : c < h.M + 1) :
    Keeps 𝔉 𝓛 Gs (tableA W S r₀ h s T) (GAt 𝔉 c k)
      fun y gs => y.1.isSome = true ∧ GAt 𝔉 (c + 1) k gs := by
  refine keeps_bind 𝔉 𝓛 Gs (keeps_quiet 𝔉 𝓛 Gs (fun g => interact_runDeferA _ _ _ _ _ g) _)
    fun o => keeps_call 𝔉 𝓛 Gs _ (Mid := fun r gs => (∃ rc, r = .ood rc) ∧ GAt 𝔉 (c + 1) k gs)
      (fun gs hgs p hp => reply_table 𝔉 𝓛 Gs hGs _ hgs hc p hp) fun r => ?_
  intro gs T' hm y hy
  obtain ⟨⟨rc, rfl⟩, hg⟩ := hm
  obtain rfl := (PMF.mem_support_pure_iff _ _).1 hy
  exact ⟨rfl, hg⟩

/-- So are several. -/
theorem keeps_tablesA (hGs : ∀ s, Gs s) (k : ℕ) : ∀ (ss : List (ℕ → Bits)) (T : Tb W) (c : ℕ),
    c + ss.length ≤ h.M + 1 →
    Keeps 𝔉 𝓛 Gs (tablesA W S r₀ h ss T) (GAt 𝔉 c k)
      fun y gs => (∃ ts, y.1 = some ts ∧ ts.length = ss.length) ∧ GAt 𝔉 (c + ss.length) k gs
  | [], T, c, _ => keeps_weaken 𝔉 𝓛 Gs (keeps_halt 𝔉 𝓛 Gs _ _) fun a gs hh => by
      obtain ⟨rfl, hg⟩ := hh
      exact ⟨⟨[], rfl, rfl⟩, hg⟩
  | s :: ss, T, c, hc => by
    have hc' : c + (ss.length + 1) ≤ h.M + 1 := hc
    refine keeps_bind 𝔉 𝓛 Gs (keeps_tableA W S r₀ h Sm i₀ s1 Gs hGs s T c k (by omega))
      fun o => ?_
    intro gs T' hm y hy
    obtain ⟨ho, hg⟩ := hm
    have hrec := keeps_bind 𝔉 𝓛 Gs (keeps_tablesA hGs k ss o.2 (c + 1) (by omega))
      (f := fun o' => .halt (o.1.bind fun t => o'.1.map fun ts => t :: ts, o'.2))
      (Post := fun y gs => (∃ ts, y.1 = some ts ∧ ts.length = ss.length + 1) ∧
        GAt 𝔉 (c + 1 + ss.length) k gs) (fun o' => by
        intro gs' T'' hm' y' hy'
        obtain ⟨⟨ts, e, hl⟩, hg'⟩ := hm'
        obtain rfl := (PMF.mem_support_pure_iff _ _).1 hy'
        obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 ho
        exact ⟨⟨t :: ts, by rw [ht, e]; rfl, by rw [List.length_cons, hl]⟩, hg'⟩)
    have := hrec gs T' hg y hy
    rw [show c + 1 + ss.length = c + (ss.length + 1) by omega] at this
    exact this

/-- The links leave the number of tables and the sessions' counts. -/
theorem keeps_linksA (t₁ : TabW lam L Bd aT aL) (c k : ℕ) :
    ∀ (l : List (DrawCopy lam L Bd aT aL h.KL × TabW lam L Bd aT aL)) (e : ℕ) (T : Tb W),
    Keeps 𝔉 𝓛 Gs (linksA W cA r₀ h t₁ e l T) (GAt 𝔉 c k) fun _ gs => GAt 𝔉 c k gs
  | [], e, T => keeps_weaken 𝔉 𝓛 Gs (keeps_halt 𝔉 𝓛 Gs _ _) fun _ _ hh => hh.2
  | a :: l, e, T => by
    refine keeps_call 𝔉 𝓛 Gs _ (Mid := fun _ gs => GAt 𝔉 c k gs)
      (fun gs hgs p hp => reply_link 𝔉 𝓛 Gs e hgs p hp) fun rp => ?_
    refine keeps_bind 𝔉 𝓛 Gs (Mid := fun _ gs => GAt 𝔉 c k gs) ?_ fun o =>
      keeps_bind 𝔉 𝓛 Gs (keeps_linksA t₁ c k l (e + 1) o.2) fun _ =>
        keeps_weaken 𝔉 𝓛 Gs (keeps_halt 𝔉 𝓛 Gs _ _) fun _ _ hh => hh.2
    cases rp with
    | link u => exact keeps_pass2A W r₀ h Sm i₀ s1 Gs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    | ood _ => exact keeps_weaken 𝔉 𝓛 Gs (keeps_halt 𝔉 𝓛 Gs _ _) fun _ _ hh => hh.2
    | test _ => exact keeps_weaken 𝔉 𝓛 Gs (keeps_halt 𝔉 𝓛 Gs _ _) fun _ _ hh => hh.2
    | sess _ _ => exact keeps_weaken 𝔉 𝓛 Gs (keeps_halt 𝔉 𝓛 Gs _ _) fun _ _ hh => hh.2
    | sym _ => exact keeps_weaken 𝔉 𝓛 Gs (keeps_halt 𝔉 𝓛 Gs _ _) fun _ _ hh => hh.2
    | none => exact keeps_weaken 𝔉 𝓛 Gs (keeps_halt 𝔉 𝓛 Gs _ _) fun _ _ hh => hh.2

/-- The reduction holds all copies. -/
def WAt (w : StG W) : Prop := ∃ ts, w.2 = some ts ∧ ts.length = h.M + 1

/-- **A request leaves what the reduction holds and the number of tables; the sessions' counts grow
by one at most.** -/
theorem keeps_proveStepA (w : StG W) (xs : List X) (c k : ℕ) :
    Keeps 𝔉 𝓛 Gs (proveStepA W cA r₀ h w xs) (GAt 𝔉 c k)
      fun y gs => y.2.2 = w.2 ∧ GAt 𝔉 c (k + 1) gs := by
  have up : ∀ gs, GAt 𝔉 c k gs → GAt 𝔉 c (k + 1) gs := fun gs hg => by
    obtain ⟨u, st, rfl, hu⟩ := hg
    exact ⟨u, st, rfl, fun e => (hu e).trans (Nat.le_succ _)⟩
  match xs with
  | [] =>
    exact keeps_weaken 𝔉 𝓛 Gs (keeps_halt 𝔉 𝓛 Gs _ _) fun a gs hh => by
      obtain ⟨rfl, hg⟩ := hh
      exact ⟨rfl, up _ hg⟩
  | u :: v :: l =>
    exact keeps_weaken 𝔉 𝓛 Gs (keeps_halt 𝔉 𝓛 Gs _ _) fun a gs hh => by
      obtain ⟨rfl, hg⟩ := hh
      exact ⟨rfl, up _ hg⟩
  | [x] =>
    unfold proveStepA
    refine keeps_bind 𝔉 𝓛 Gs (keeps_quiet 𝔉 𝓛 Gs (fun g => interact_runLazyA _ _ _ g) _)
      fun o => ?_
    cases hm : (w.2.bind fun ts => ts[o.1.j]?) with
    | none =>
      exact keeps_weaken 𝔉 𝓛 Gs (keeps_halt 𝔉 𝓛 Gs _ _) fun a gs hh => by
        obtain ⟨rfl, hg⟩ := hh
        exact ⟨rfl, up _ hg⟩
    | some t =>
      refine keeps_call 𝔉 𝓛 Gs _ (Mid := fun _ gs => GAt 𝔉 c (k + 1) gs)
        (fun gs hgs p hp => reply_sess_at 𝔉 𝓛 Gs _ _ _ hgs p hp) fun rp => ?_
      refine keeps_bind 𝔉 𝓛 Gs (Mid := fun _ gs => GAt 𝔉 c (k + 1) gs) ?_ fun o' =>
        keeps_weaken 𝔉 𝓛 Gs (keeps_halt 𝔉 𝓛 Gs _ _) fun a gs hh => by
          obtain ⟨rfl, hg⟩ := hh
          exact ⟨rfl, hg⟩
      cases rp with
      | sess _ u => exact keeps_pass2A W r₀ h Sm i₀ s1 Gs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      | ood _ => exact keeps_weaken 𝔉 𝓛 Gs (keeps_halt 𝔉 𝓛 Gs _ _) fun _ _ hh => hh.2
      | test _ => exact keeps_weaken 𝔉 𝓛 Gs (keeps_halt 𝔉 𝓛 Gs _ _) fun _ _ hh => hh.2
      | link _ => exact keeps_weaken 𝔉 𝓛 Gs (keeps_halt 𝔉 𝓛 Gs _ _) fun _ _ hh => hh.2
      | sym _ => exact keeps_weaken 𝔉 𝓛 Gs (keeps_halt 𝔉 𝓛 Gs _ _) fun _ _ hh => hh.2
      | none => exact keeps_weaken 𝔉 𝓛 Gs (keeps_halt 𝔉 𝓛 Gs _ _) fun _ _ hh => hh.2

/-- **If every OOD seed is in Gs, the setup is never refused**: after it the reduction holds all
M + 1 copies, the game has made as many further tables, and no session has been run. -/
theorem keeps_setupA (hGs : ∀ s, Gs s) (T : Tb W) :
    Keeps 𝔉 𝓛 Gs (setupA W S cA r₀ h T) (fun gs => gs = none)
      fun y gs => WAt W h y.2 ∧ GAt 𝔉 (h.M + 1) 0 gs := by
  unfold setupA
  refine keeps_bind 𝔉 𝓛 Gs (keeps_quiet_supp 𝔉 𝓛 Gs (fun g => interact_runLazyA _ _ _ g) _)
    fun o₀ => ?_
  intro gs T' hm y hy
  obtain ⟨ho₀, rfl⟩ := hm
  have hlen : o₀.1.copies.length = h.M + 1 :=
    (onlyCoins_support T _ (onlyCoins_coinsC W h) o₀ ho₀).1.2.2.1
  refine keeps_bind 𝔉 𝓛 Gs (Post := fun y gs => WAt W h y.2 ∧ GAt 𝔉 (h.M + 1) 0 gs)
    (keeps_tableA_first W S r₀ h Sm i₀ s1 Gs hGs _ _) (fun o₁ => ?_) none T' rfl y hy
  intro gs₁ T₁ hm₁ y₁ hy₁
  obtain ⟨h₁, hg₁⟩ := hm₁
  refine keeps_bind 𝔉 𝓛 Gs (Post := fun y gs => WAt W h y.2 ∧ GAt 𝔉 (h.M + 1) 0 gs)
    (keeps_tablesA W S r₀ h Sm i₀ s1 Gs hGs 0 _ _ 0
      (by rw [List.length_map, hlen, Nat.zero_add])) (fun o₂ => ?_) gs₁ T₁ hg₁ y₁ hy₁
  intro gs₂ T₂ hm₂ y₂ hy₂
  obtain ⟨⟨ts, e₂, hl₂⟩, hg₂⟩ := hm₂
  rw [List.length_map, hlen, Nat.zero_add] at hg₂
  rw [List.length_map, hlen] at hl₂
  obtain ⟨t₁, e₁⟩ := Option.isSome_iff_exists.1 h₁
  rw [e₁, e₂] at hy₂
  refine keeps_call 𝔉 𝓛 Gs _ (Mid := fun _ gs => GAt 𝔉 (h.M + 1) 0 gs)
    (Post := fun y gs => WAt W h y.2 ∧ GAt 𝔉 (h.M + 1) 0 gs)
    (fun gs hgs p hp => reply_test 𝔉 𝓛 Gs 0 hgs p hp) (fun rp => ?_) gs₂ T₂ hg₂ y₂ hy₂
  refine keeps_bind 𝔉 𝓛 Gs (Mid := fun _ gs => GAt 𝔉 (h.M + 1) 0 gs) ?_ fun o₃ =>
    keeps_bind 𝔉 𝓛 Gs (keeps_linksA W cA r₀ h Sm i₀ s1 Gs t₁ (h.M + 1) 0 _ 1 o₃.2) fun o₄ =>
      keeps_weaken 𝔉 𝓛 Gs (keeps_halt 𝔉 𝓛 Gs _ _) fun a gs hh => by
        obtain ⟨rfl, hg⟩ := hh
        exact ⟨⟨ts, rfl, hl₂⟩, hg⟩
  cases rp with
  | test u => exact keeps_pass2A W r₀ h Sm i₀ s1 Gs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  | ood _ => exact keeps_weaken 𝔉 𝓛 Gs (keeps_halt 𝔉 𝓛 Gs _ _) fun _ _ hh => hh.2
  | link _ => exact keeps_weaken 𝔉 𝓛 Gs (keeps_halt 𝔉 𝓛 Gs _ _) fun _ _ hh => hh.2
  | sess _ _ => exact keeps_weaken 𝔉 𝓛 Gs (keeps_halt 𝔉 𝓛 Gs _ _) fun _ _ hh => hh.2
  | sym _ => exact keeps_weaken 𝔉 𝓛 Gs (keeps_halt 𝔉 𝓛 Gs _ _) fun _ _ hh => hh.2
  | none => exact keeps_weaken 𝔉 𝓛 Gs (keeps_halt 𝔉 𝓛 Gs _ _) fun _ _ hh => hh.2

/-- An oracle query to the reduction leaves what it holds and the game's state. -/
theorem keeps_ans (w : StG W) (o : (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)).ι)
    (q : (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)).Dom o) (Pre : GSt 𝔉 → Prop) :
    Keeps 𝔉 𝓛 Gs ((wrapW W S cA r₀ h).ans w o q) Pre fun y gs => y.2.2 = w.2 ∧ Pre gs :=
  keeps_bind 𝔉 𝓛 Gs (keeps_quiet 𝔉 𝓛 Gs (fun g => realises_lazy _ g w.1 o q) Pre) fun _ =>
    keeps_weaken 𝔉 𝓛 Gs (keeps_halt 𝔉 𝓛 Gs _ Pre) fun a gs hh => by
      obtain ⟨rfl, hg⟩ := hh
      exact ⟨rfl, hg⟩

end Red

end AtPublicFiles.Shown

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.Shown.keeps_quiet_supp
#print axioms AtPublicFiles.Shown.keeps_setupA
#print axioms AtPublicFiles.Shown.keeps_ans
#print axioms AtPublicFiles.Shown.keeps_linksA
#print axioms AtPublicFiles.Shown.keeps_proveStepA
#print axioms AtPublicFiles.Shown.keeps_pass2A
#print axioms AtPublicFiles.Shown.keeps_tableA_first
#print axioms AtPublicFiles.Shown.keeps_tableA
#print axioms AtPublicFiles.Shown.keeps_tablesA
#print axioms AtPublicFiles.Shown.keeps_halt
#print axioms AtPublicFiles.Shown.keeps_bind
#print axioms AtPublicFiles.Shown.keeps_call
#print axioms AtPublicFiles.Shown.keeps_quiet
#print axioms AtPublicFiles.Shown.keeps_weaken
#print axioms AtPublicFiles.Shown.reply_first
#print axioms AtPublicFiles.Shown.reply_table
#print axioms AtPublicFiles.Shown.reply_test
#print axioms AtPublicFiles.Shown.reply_link
#print axioms AtPublicFiles.Shown.reply_sess_at
