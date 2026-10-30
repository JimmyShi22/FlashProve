-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/PubOverrun.lean: stopping before a copy serves more than s1 batches, for the
challengers that publish a function of the key at the setup: `chalLBP` against `chalLSBP`
(Compile/Batch/PubChall.lean) (words of this library: lean/GLOSSARY.md).

The two challengers are the two challengers of a `LeafGame` (Compile/Batch/OverrunGen.lean, which is
generic in the reply to the setup: its field `cIn`), and the bound is `LeafGame.overrun`: leaves ·
Pr[Bin(n, 1 / leaves) > s1], the same term as without publishing (leaves: `p.leaves`, the number of
copies; n: the batches of the admissible adversary, at most). Each batch with an own request still
samples its copy uniformly and independently of all that came before, the published value included.
-/
import Compile.Batch.PubChall
import Compile.Batch.OverrunGen

noncomputable section

namespace Compile.Batch
open Iop Rom Prob ZKCP
open Compile.GlueB (GCall GAdm)
open Compile.DefC (virtL)
open Compile.OverrunGen (Kind LeafGame)
open scoped ENNReal

variable {I X V : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
  (pw : IVK lam L → WKey lam L → V) (i : I)

/-- what the two challengers for batches are made of -/
def gameBP : LeafGame (spec lam W.K L) (split lam W.K L) (GCall X Unit) (BInP V lam L) where
  κ := IskH lam L
  Req := Gen.Batch X Unit
  CRes := IVK lam L × IskH lam L
  Res := List (Prf lam L)
  kind := fun c => match c with
    | .setup => .setup
    | .batch b => if hasOwn b then .draw b else .idle
  M := p.M
  s1 := p.s1
  no := .inr []
  cp := CpL W WP p i
  cIn := fun o => .inl (pw o.1 (keyOf o.2))
  cKey := fun o => o.2
  sess := fun k N₀ t₀ b j => virtL N₀ (t₀ + 1 - N₀) (PpLJ W WP p k (ownFlag b) (reqs b) j)
  reply := replyOfP V

theorem step_chalLBP (s : Option (IskH lam L × ℕ)) (c : GCall X Unit) :
    (chalLBP W WP p pw i).step s c = (gameBP W WP p pw i).chal.step s c := by
  cases c with
  | setup => cases s <;> rfl
  | batch b =>
    cases s with
    | none =>
      show LStep.pure _ =
        (gameBP W WP p pw i).stepK (if hasOwn b then Kind.draw b else Kind.idle) none
      cases hasOwn b <;> rfl
    | some z =>
      obtain ⟨k, N₀⟩ := z
      show (if hasOwn b then _ else _) =
        (gameBP W WP p pw i).stepK (if hasOwn b then Kind.draw b else Kind.idle) (some (k, N₀))
      cases hasOwn b <;> rfl

theorem step_chalLSBP (s : Option (IskH lam L × ℕ × (ℕ → ℕ))) (c : GCall X Unit) :
    (chalLSBP W WP p pw i).step s c = (gameBP W WP p pw i).chalS.step s c := by
  cases c with
  | setup => cases s <;> rfl
  | batch b =>
    cases s with
    | none =>
      show LStep.pure _ =
        (gameBP W WP p pw i).stepKS (if hasOwn b then Kind.draw b else Kind.idle) none
      cases hasOwn b <;> rfl
    | some z =>
      obtain ⟨k, N₀, c⟩ := z
      show (if hasOwn b then _ else _) =
        (gameBP W WP p pw i).stepKS (if hasOwn b then Kind.draw b else Kind.idle) (some (k, N₀, c))
      cases hasOwn b <;> rfl

theorem chalLBP_eq : chalLBP W WP p pw i = (gameBP W WP p pw i).chal :=
  congrArg (LChall.mk _) (funext fun s => funext fun c => step_chalLBP W WP p pw i s c)

theorem chalLSBP_eq : chalLSBP W WP p pw i = (gameBP W WP p pw i).chalS :=
  congrArg (LChall.mk _) (funext fun s => funext fun c => step_chalLSBP W WP p pw i s c)

/-- an admissible adversary with at most n batches makes at most n calls that sample a copy -/
theorem callBound_of_gAdmP (ok : Gen.Batch X Unit → Prop) {α : Type}
    (A : Adv (spec lam W.K L) (GCall X Unit) (BInP V lam L) α) :
    ∀ (b : Bool) (n : ℕ),
      GAdm ok A b n → A.CallBound (fun m => ∃ x, (gameBP W WP p pw i).kind m = .draw x) n := by
  induction A with
  | halt a => exact fun _ _ _ => trivial
  | sample m k ih => exact fun b n h r => ih r b n (h r)
  | query o q k ih => exact fun b n h r => ih r b n (h r)
  | call m k ih =>
    intro b n h
    cases m with
    | setup =>
      refine ⟨fun ⟨x, hx⟩ => ?_, fun _ a => ih a true n (h.2 a)⟩
      cases hx
    | batch c =>
      cases n with
      | zero => exact h.elim
      | succ n =>
        have h' : ∀ a, GAdm ok (k a) b n := h.2.2
        refine ⟨fun _ => ⟨n, rfl, fun a => ih a b n (h' a)⟩, fun _ a => ?_⟩
        exact callBound_succ _ _ n (ih a b n (h' a))
where
  callBound_succ {α : Type} (P : GCall X Unit → Prop)
      (A : Adv (spec lam W.K L) (GCall X Unit) (BInP V lam L) α) :
      ∀ n, A.CallBound P n → A.CallBound P (n + 1) := by
    induction A with
    | halt a => exact fun _ _ => trivial
    | sample m k ih => exact fun n h r => ih r n (h r)
    | query o q k ih => exact fun n h r => ih r n (h r)
    | call m k ih =>
      intro n h
      refine ⟨fun hP => ?_, fun hP a => ih a n (h.2 hP a)⟩
      obtain ⟨n', rfl, hk⟩ := h.1 hP
      exact ⟨n' + 1, rfl, fun a => ih a n' (hk a)⟩

/-- For an admissible adversary with at most n batches: stopping before a copy serves more than s1
batches changes the view by at most leaves · Pr[Bin(n, 1 / leaves) > s1]. -/
theorem overrunBP (ok : Gen.Batch X Unit → Prop) {α : Type}
    (A : Adv (spec lam W.K L) (GCall X Unit) (BInP V lam L) α) (n : ℕ) (hA : GAdm ok A false n) :
    tv ((interact (chalLBP W WP p pw i).world A (none, LSt.init _)).map Prod.fst)
        ((interact (chalLSBP W WP p pw i).world A (none, LSt.init _)).map Prod.fst) ≤
      p.leaves * binTail n p.leaves p.s1 := by
  have h : tv ((interact (LChall.world ⟨Option (IskH lam L × ℕ), (gameBP W WP p pw i).chal.step⟩)
          A (none, LSt.init _)).map Prod.fst)
        ((interact
            (LChall.world ⟨Option (IskH lam L × ℕ × (ℕ → ℕ)), (gameBP W WP p pw i).chalS.step⟩)
            A (none, LSt.init _)).map Prod.fst) ≤
      p.leaves * binTail n p.leaves p.s1 :=
    (gameBP W WP p pw i).overrun A n (callBound_of_gAdmP W WP p pw i ok A false n hA)
  have e1 : (gameBP W WP p pw i).chal.step = (chalLBP W WP p pw i).step :=
    funext fun s => funext fun c => (step_chalLBP W WP p pw i s c).symm
  have e2 : (gameBP W WP p pw i).chalS.step = (chalLSBP W WP p pw i).step :=
    funext fun s => funext fun c => (step_chalLSBP W WP p pw i s c).symm
  rw [e1, e2] at h
  exact h

end Compile.Batch
