-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
  Compile/Batch/OverrunGen.lean: stopping before a leaf is used too often, for challengers written
  in `LStep` (Rom/DeferLate.lean), generic in the scheme (words of this library: lean/GLOSSARY.md).

  A `LeafGame` consists of a setup program, a kind for each call (setup; a call that samples a leaf;
  a call that does nothing), and the program of a call once its leaf is sampled (a leaf: one of
  M + 1 values, of which a sampling call samples one uniformly).
    `G.chal`     setup: the setup program, then a token of no bits (to learn the number N₀ of
                 tokens); a second setup is rejected; a sampling call: a token of no bits, a uniform
                 leaf j, the program of the call on j;
    `G.chalS`    the same with a counter for each leaf: a call that samples a leaf which has served
                 s1 calls replies "nothing" and does nothing more.
  `overrun`: for an adversary with at most n sampling calls the two views differ by at most leaves ·
  Pr[Bin(n, 1 / leaves) > s1].
  The proof checks the conditions of Rom/Overrun.lean, where the induction on the adversary is made
  once for all challengers.
  Notation:
    `G`: a `LeafGame S sp Out In`: what the two challengers are made of; `G.M`, `G.s1`: M + 1
      leaves; at most s1 calls on a leaf
    `N₀`, `t₀`: number N₀ of tokens of the setup, number t₀ of tokens so far (the field `sess`);
      token: the head of Rom/Defer.lean
    in the scheme a leaf is a copy: `gameBP`, Compile/Batch/PubOverrun.lean
-/
import Rom.Overrun
import Compile.Step1_defc_L
import Compile.Spec

noncomputable section

open Rom Prob
open scoped ENNReal

namespace Compile.OverrunGen

open Compile.DefC (run_bind)

/-- the three kinds of calls -/
inductive Kind (Req : Type) : Type
  | setup : Kind Req
  | draw (x : Req) : Kind Req
  | idle : Kind Req

/-- What the two challengers are made of. -/
structure LeafGame (S : OSpec) (sp : Split S) (Out In : Type) where
  /-- the key; what a sampling call asks for; the results of the setup program and of a call's
  program -/
  κ : Type
  Req : Type
  CRes : Type
  Res : Type
  kind : Out → Kind Req
  /-- M + 1 leaves; at most s1 calls on a leaf -/
  M : ℕ
  s1 : ℕ
  /-- the reply of a call that does nothing -/
  no : In
  cp : LStep S sp CRes
  cIn : CRes → In
  cKey : CRes → κ
  /-- the program of a call: key, number N₀ of tokens of the setup, number t₀ of tokens so far, the
  request, the leaf -/
  sess : κ → ℕ → ℕ → Req → Fin (M + 1) → LStep S sp Res
  reply : Req → Res → In

variable {S : OSpec} {sp : Split S} {Out In : Type} (G : LeafGame S sp Out In)

namespace LeafGame

/-- a step of the challenger without counters, by the kind of the call -/
def stepK : Kind G.Req → Option (G.κ × ℕ) → LStep S sp (In × Option (G.κ × ℕ))
  | .setup, none => G.cp.bind fun o => LStep.fresh 0 fun t => LStep.pure (G.cIn o, some (G.cKey o, t))
  | .setup, some k => LStep.pure (G.no, some k)
  | .draw _, none => LStep.pure (G.no, none)
  | .idle, s => LStep.pure (G.no, s)
  | .draw x, some (k, N₀) => LStep.fresh 0 fun t₀ => LStep.sample G.M fun j =>
      (G.sess k N₀ t₀ x j).bind fun r => LStep.pure (G.reply x r, some (k, N₀))

/-- a step of the challenger with counters -/
def stepKS : Kind G.Req → Option (G.κ × ℕ × (ℕ → ℕ)) → LStep S sp (In × Option (G.κ × ℕ × (ℕ → ℕ)))
  | .setup, none => G.cp.bind fun o => LStep.fresh 0 fun t => LStep.pure (G.cIn o, some (G.cKey o, t, fun _ => 0))
  | .setup, some k => LStep.pure (G.no, some k)
  | .draw _, none => LStep.pure (G.no, none)
  | .idle, s => LStep.pure (G.no, s)
  | .draw x, some (k, N₀, c) => LStep.fresh 0 fun t₀ => LStep.sample G.M fun j =>
      if c j.val < G.s1 then
        (G.sess k N₀ t₀ x j).bind fun r =>
          LStep.pure (G.reply x r, some (k, N₀, Function.update c j.val (c j.val + 1)))
      else LStep.pure (G.no, some (k, N₀, c))

/-- The challenger. -/
def chal : LChall S sp Out In where
  τ := Option (G.κ × ℕ)
  step s c := G.stepK (G.kind c) s

/-- The challenger that stops before a leaf serves more than s1 calls. -/
def chalS : LChall S sp Out In where
  τ := Option (G.κ × ℕ × (ℕ → ℕ))
  step s c := G.stepKS (G.kind c) s

/-- forget the counters; read the counters (before the setup all are 0) -/
def fgτ (s : Option (G.κ × ℕ × (ℕ → ℕ))) : Option (G.κ × ℕ) := s.map fun z => (z.1, z.2.1)
def ctrτ (s : Option (G.κ × ℕ × (ℕ → ℕ))) : Fin (G.M + 1) → ℕ :=
  match s with
  | none => fun _ => 0
  | some z => fun j => z.2.2 j.val

def pair : Overrun.Pair G.chal.world G.chalS.world G.M where
  fg := fun s => (G.fgτ s.1, s.2)
  ctr := fun s => G.ctrτ s.1

theorem ctrτ_update (k : G.κ) (N₀ : ℕ) (c : ℕ → ℕ) (j : Fin (G.M + 1)) (v : ℕ) :
    G.ctrτ (some (k, N₀, Function.update c j.val v)) =
      Function.update (G.ctrτ (some (k, N₀, c))) j v := by
  funext a
  by_cases h : a = j
  · subst h; simp [ctrτ]
  · have h' : a.val ≠ j.val := fun e => h (Fin.ext e)
    simp [ctrτ, Function.update_of_ne h, Function.update_of_ne h']

/-- a step that replies "nothing" and keeps the state is quiet -/
theorem quiet_of_pure (st : Option (G.κ × ℕ × (ℕ → ℕ))) (w : LSt S) (m : Out)
    (h1 : G.stepK (G.kind m) (G.fgτ st) = LStep.pure (G.no, G.fgτ st))
    (h2 : G.stepKS (G.kind m) st = LStep.pure (G.no, st)) :
    Overrun.Quiet G.pair (st, w) m := by
  constructor
  · show ((G.stepK (G.kind m) (G.fgτ st)).run w).map _ =
      (((G.stepKS (G.kind m) st).run w).map _).map _
    rw [h1, h2]
    simp only [LStep.run, PMF.pure_map]
    rfl
  · intro x hx j
    have hx' : x ∈ (((G.stepKS (G.kind m) st).run w).map fun p => (p.1.1, (p.1.2, p.2))).support :=
      hx
    rw [h2] at hx'
    have e : ((LStep.pure (G.no, st) : LStep S sp _).run w).map (fun p => (p.1.1, (p.1.2, p.2))) =
        PMF.pure (G.no, (st, w)) :=
      PMF.pure_map _ _
    have hx2 : x ∈ (PMF.pure (G.no, (st, w))).support := by rw [← e]; exact hx'
    rw [(PMF.mem_support_pure_iff _ _).1 hx2]
    exact le_rfl

/-- The two challengers satisfy the conditions of Rom/Overrun.lean. -/
theorem laws : Overrun.Laws G.pair G.s1 (fun m => ∃ x, G.kind m = .draw x) where
  answer := fun s o q => by
    show (lazyAnswer s.2.table o q).map _ = ((lazyAnswer s.2.table o q).map _).map _
    rw [PMF.map_comp]
    rfl
  answer_ctr := fun s o q x hx => by
    obtain ⟨y, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hx
    rfl
  reply := fun s m => by
    obtain ⟨st, w⟩ := s
    cases hk : G.kind m with
    | idle => exact Or.inl (G.quiet_of_pure st w m (by rw [hk]; rfl) (by rw [hk]; rfl))
    | setup =>
      cases st with
      | some z => exact Or.inl (G.quiet_of_pure (some z) w m (by rw [hk]; rfl) (by rw [hk]; rfl))
      | none =>
        refine Or.inl ⟨?_, ?_⟩
        · show ((G.stepK (G.kind m) none).run w).map _ =
            (((G.stepKS (G.kind m) none).run w).map _).map _
          rw [hk]
          simp only [stepK, stepKS, run_bind, LStep.run, PMF.map_bind, PMF.pure_map]
          rfl
        · intro x hx j
          have hx' : x ∈
              (((G.stepKS (G.kind m) none).run w).map fun p => (p.1.1, (p.1.2, p.2))).support := hx
          rw [hk] at hx'
          have e : ((G.stepKS .setup none).run w).map (fun p => (p.1.1, (p.1.2, p.2)))
              = (G.cp.run w).bind fun a => (PMF.uniformOfFintype (Fin 0 → Bool)).bind fun u =>
                  PMF.pure (G.cIn a.1,
                    ((some (G.cKey a.1, a.2.vals.length, fun _ => 0) : Option (G.κ × ℕ × (ℕ → ℕ))),
                      { a.2 with vals := a.2.vals ++ [List.ofFn u] })) := by
            simp only [stepKS, run_bind, LStep.run, PMF.map_bind, PMF.pure_map]
          have hx2 : x ∈
              ((G.cp.run w).bind fun a =>
                (PMF.uniformOfFintype (Fin 0 → Bool)).bind fun u =>
                    PMF.pure (G.cIn a.1,
                          ((some (G.cKey a.1, a.2.vals.length,
                                fun _ => 0) : Option (G.κ × ℕ × (ℕ → ℕ))),
                            { a.2 with vals := a.2.vals ++ [List.ofFn u] }))).support := by
            rw [← e]; exact hx'
          obtain ⟨y, -, hx3⟩ := (PMF.mem_support_bind_iff _ _ _).1 hx2
          obtain ⟨u, -, hx4⟩ := (PMF.mem_support_bind_iff _ _ _).1 hx3
          rw [(PMF.mem_support_pure_iff _ _).1 hx4]
          exact le_rfl
    | draw x =>
      cases st with
      | none => exact Or.inl (G.quiet_of_pure none w m (by rw [hk]; rfl) (by rw [hk]; rfl))
      | some z =>
        obtain ⟨k, N₀, c⟩ := z
        refine Or.inr
          ⟨⟨x, rfl⟩, Fin 0 → Bool,
            PMF.uniformOfFintype _,
            (fun u j =>
              (((G.sess k N₀ w.vals.length x j).bind fun r =>
                    LStep.pure (G.reply x r, some (k, N₀))).run
                  { w with vals := w.vals ++ [List.ofFn u] }).map
                fun p => (p.1.1, (p.1.2, p.2))),
            (fun u j =>
              ((if c j.val < G.s1 then
                    (G.sess k N₀ w.vals.length x j).bind fun r =>
                      LStep.pure (G.reply x r, some (k, N₀, Function.update c j.val (c j.val + 1)))
                      else LStep.pure (G.no, some (k, N₀, c))).run
                  { w with vals := w.vals ++ [List.ofFn u] }).map
                fun p => (p.1.1, (p.1.2, p.2))),
            ?_, ?_, ?_⟩
        · show ((G.stepK (G.kind m) (some (k, N₀))).run w).map _ = _
          rw [hk]
          simp only [stepK, LStep.run, PMF.map_bind]
          rfl
        · show ((G.stepKS (G.kind m) (some (k, N₀, c))).run w).map _ = _
          rw [hk]
          simp only [stepKS, LStep.run, PMF.map_bind]
          rfl
        · intro u j hj
          have hj' : c j.val < G.s1 := hj
          refine ⟨?_, ?_⟩
          · simp only [if_pos hj', run_bind, LStep.run, PMF.map_bind, PMF.pure_map]
            rfl
          · intro y hy
            have e : ((if c j.val < G.s1 then
                      (G.sess k N₀ w.vals.length x j).bind fun r =>
                        LStep.pure
                          (G.reply x r, some (k, N₀, Function.update c j.val (c j.val + 1)))
                        else LStep.pure (G.no, some (k, N₀, c))).run
                    { w with vals := w.vals ++ [List.ofFn u] }).map
                  (fun p => (p.1.1, (p.1.2, p.2))) =
                ((G.sess k N₀ w.vals.length x j).run
                  { w with vals := w.vals ++ [List.ofFn u] }).bind fun a =>
                    PMF.pure (G.reply x a.1,
                      ((some (k, N₀,
                            Function.update c j.val (c j.val + 1)) : Option (G.κ × ℕ × (ℕ → ℕ))),
                        a.2)) := by
              simp only [if_pos hj', run_bind, LStep.run, PMF.map_bind, PMF.pure_map]
            have hy2 : y ∈
                (((G.sess k N₀ w.vals.length x j).run
                  { w with vals := w.vals ++ [List.ofFn u] }).bind fun a =>
                    PMF.pure (G.reply x a.1,
                          ((some (k, N₀,
                                Function.update c j.val
                                  (c j.val + 1)) : Option (G.κ × ℕ × (ℕ → ℕ))),
                            a.2))).support := by
              rw [← e]; exact hy
            obtain ⟨r, -, hy3⟩ := (PMF.mem_support_bind_iff _ _ _).1 hy2
            rw [(PMF.mem_support_pure_iff _ _).1 hy3]
            exact G.ctrτ_update k N₀ c j _

/-- Stopping before a leaf serves more than s1 calls changes the view of an adversary with at most n
sampling calls by at most leaves · Pr[Bin(n, 1 / leaves) > s1]. -/
theorem overrun {α : Type} (A : Adv S Out In α) (n : ℕ)
    (hA : A.CallBound (fun m => ∃ x, G.kind m = .draw x) n) :
    tv ((interact G.chal.world A (none, LSt.init S)).map Prod.fst)
        ((interact G.chalS.world A (none, LSt.init S)).map Prod.fst) ≤
      ((G.M + 1 : ℕ) : ℝ≥0∞) * Compile.binTail n (G.M + 1) G.s1 := by
  have h := Overrun.tv_le_pOver G.laws A n ((none, LSt.init S) : G.chalS.world.σ) rfl hA
  rw [pOver, Prob.binTail_eq_sum_Icc] at h
  exact h

end LeafGame
end Compile.OverrunGen
