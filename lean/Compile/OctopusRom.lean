-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/OctopusRom.lean: joint verification of Merkle openings from pruned paths (`octC`,
Hash/Octopus.lean) as an oracle algorithm: soundness within a trace, evaluation, number of queries.
Generic in the family of oracles and in the node program.

  `octSound`        Sound within a trace. If `octC` from the nodes js with as many digests v runs
                    within a trace tr and ends in the digests out, then every node j of js has a
                    full path of d digests whose verification (`climbM`, Compile/MerkleM.lean) runs
                    within the same trace, and ends in the digest of an entry of out whose number is
                    j / 2^d, the node's ancestor. (On a list that is not strictly ascending several
                    entries may have that number; whoever calls `octC` compares every entry with its
                    root.) Whatever the list s is, and whatever the order of js. So a verifier that
                    uses `octC` accepts only what a verifier that verifies every path accepts for
                    some paths, with no further query.
  `Evaluates.octC`  If the node program evaluates to a function, `octC` evaluates to `octF`, in the
                    sense of `Evaluates` (Compile/MerkleList.lean).
  `Counts`, `Counts.octC`
                    For every bound P on algorithms that adds up along bind (no coin and at most t
                    queries; weights of queries), if a node costs 1, `octC` costs at most js.length
                    * d node queries: no more than the verification of js.length full paths.

Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Notation: `js`: a list of natural numbers; "a list js of node numbers" (the head of
Hash/Octopus.lean); `v`: a list over D; "beside it, the list of their digests" (there); `s`: a list
over D; "the message (the list of digests that is sent)" (there); `d`: a natural number; "d levels
up" (`octC`, there); `nd` (the node program): a function D → D → OComp S D, in the place of `hN`, "a
function `hN` that hashes two children" (there).
-/
import Hash.OctopusFacts
import Compile.MerkleRom

noncomputable section

namespace Compile
open Rom Octopus

section Sound
variable {S : OSpec} {D : Type} [Inhabited D] {tr : Trace S} (nd : D → D → OComp S D)

omit [Inhabited D] in
theorem climbM_cons (s : D) (ss : List D) (j : ℕ) (c : D) :
    climbM nd (s :: ss) j c = (lone nd j c s).bind fun u => climbM nd ss (j / 2) u := by
  simp only [climbM, lone]
  split_ifs <;> rfl

theorem runsIn_stepC :
    ∀ (js : List ℕ) (v s out : List D), v.length = js.length → RunsIn tr (stepC nd js v s) out →
      out.length = (up js).length ∧
      ∀ e ∈ js.zip v,
        ∃ sb, ∃ m ∈ (up js).zip out, m.1 = e.1 / 2 ∧ RunsIn tr (lone nd e.1 e.2 sb) m.2
  | [], v, s, out, _, h => by
      obtain rfl : [] = out := runsIn_pure_iff.1 h
      exact ⟨rfl, fun e he => by simp at he⟩
  | [i], v, s, out, hl, h => by
      match v, hl with
      | [a], _ =>
        have h' : RunsIn tr ((lone nd i a (s.headD default)).bind fun u => OComp.pure [u]) out := h
        obtain ⟨u, hu, h2⟩ := (runsIn_bind_iff _ _ _).1 h'
        obtain rfl := runsIn_pure_iff.1 h2
        refine ⟨rfl, fun e he => ?_⟩
        obtain rfl : e = (i, a) := by simpa using he
        exact ⟨s.headD default, (i / 2, u), by simp [up], rfl, hu⟩
  | i :: j :: l, v, s, out, hl, h => by
      match v, hl with
      | a :: b :: v', hl =>
        have hl' : v'.length = l.length := by simpa using hl
        by_cases hs : sib i j
        · have h' : RunsIn tr
              ((nd a b).bind fun u => (stepC nd l v' s).bind fun r => OComp.pure (u :: r)) out := by
            have e : stepC nd (i :: j :: l) (a :: b :: v') s =
                (nd a b).bind fun u => (stepC nd l v' s).bind fun r => OComp.pure (u :: r) := by
              simp only [stepC, if_pos hs]; rfl
            rwa [e] at h
          obtain ⟨u, hu, h2⟩ := (runsIn_bind_iff _ _ _).1 h'
          obtain ⟨r, hr, h3⟩ := (runsIn_bind_iff _ _ _).1 h2
          obtain rfl := runsIn_pure_iff.1 h3
          obtain ⟨ih1, ih2⟩ := runsIn_stepC l v' s r hl' hr
          have hup : up (i :: j :: l) = i / 2 :: up l := by simp only [up, if_pos hs]
          rw [hup]
          refine ⟨by simp [ih1], fun e he => ?_⟩
          simp only [List.zip_cons_cons, List.mem_cons] at he
          obtain ⟨hi, rfl⟩ := hs
          rcases he with rfl | rfl | he
          · exact ⟨b, (i / 2, u), by simp, rfl, by unfold lone; rw [if_pos hi]; exact hu⟩
          · refine ⟨a, (i / 2, u), by simp, by show i / 2 = (i + 1) / 2; omega, ?_⟩
            unfold lone
            rw [if_neg (by show ¬ (i + 1) % 2 = 0; omega)]
            exact hu
          · obtain ⟨sb, m, hm, h4, h5⟩ := ih2 e he
            exact ⟨sb, m,
              by simp only [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hm, h4, h5⟩
        · have h' : RunsIn tr
              ((lone nd i a (s.headD default)).bind fun u =>
                (stepC nd (j :: l) (b :: v') s.tail).bind fun r => OComp.pure (u :: r)) out := by
            have e : stepC nd (i :: j :: l) (a :: b :: v') s =
                (lone nd i a (s.headD default)).bind fun u =>
                  (stepC nd (j :: l) (b :: v') s.tail).bind fun r => OComp.pure (u :: r) := by
              simp only [stepC, if_neg hs]; rfl
            rwa [e] at h
          obtain ⟨u, hu, h2⟩ := (runsIn_bind_iff _ _ _).1 h'
          obtain ⟨r, hr, h3⟩ := (runsIn_bind_iff _ _ _).1 h2
          obtain rfl := runsIn_pure_iff.1 h3
          obtain ⟨ih1, ih2⟩ := runsIn_stepC (j :: l) (b :: v') s.tail r (by simpa using hl') hr
          have hup : up (i :: j :: l) = i / 2 :: up (j :: l) := by simp only [up, if_neg hs]
          rw [hup]
          refine ⟨by simp [ih1], fun e he => ?_⟩
          rw [List.zip_cons_cons] at he
          rcases List.mem_cons.1 he with rfl | he
          · exact ⟨s.headD default, (i / 2, u), by simp, rfl, hu⟩
          · obtain ⟨sb, m, hm, h4, h5⟩ := ih2 e he
            exact ⟨sb, m,
              by simp only [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hm, h4, h5⟩

end Sound

def Spec.octSound : Prop :=
  ∀ (S : OSpec) (D : Type) [Inhabited D] (tr : Trace S) (nd : D → D → OComp S D) (d : ℕ)
      (js : List ℕ) (v s out : List D),
    v.length = js.length → RunsIn tr (octC nd d js v s) out →
    out.length = (upN d js).length ∧
    ∀ e ∈ js.zip v, ∃ path : List D,
      path.length = d ∧
      ∃ m ∈ (upN d js).zip out, m.1 = e.1 / 2 ^ d ∧ RunsIn tr (climbM nd path e.1 e.2) m.2

/-- `octC` is sound within a trace: if it runs within a trace, from as many digests as nodes, every
node has a full path whose verification runs within the same trace and ends where `octC` ends. -/
theorem octSound : Spec.octSound := by
  intro S D _ tr nd d
  induction d with
  | zero =>
    intro js v s out hl h
    obtain rfl : v = out := runsIn_pure_iff.1 h
    exact ⟨hl, fun e he => ⟨[], rfl, e, he, by simp, RunsIn.pure _⟩⟩
  | succ d ih =>
    intro js v s out hl h
    have h' : RunsIn tr
        ((stepC nd js v s).bind fun v' => octC nd d (up js) v' (s.drop (need1 js))) out := h
    obtain ⟨v', hv, h2⟩ := (runsIn_bind_iff _ _ _).1 h'
    obtain ⟨s1, s2⟩ := runsIn_stepC nd js v s v' hl hv
    obtain ⟨i1, i2⟩ := ih (up js) v' _ out s1 h2
    refine ⟨i1, fun e he => ?_⟩
    obtain ⟨sb, m, hm, hm1, hm2⟩ := s2 e he
    obtain ⟨path, hp, m', hm', h3, h4⟩ := i2 m hm
    refine ⟨sb :: path, by simp [hp], m', hm', ?_, ?_⟩
    · rw [h3, hm1, Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm]
    · rw [climbM_cons]
      exact (runsIn_bind_iff _ _ _).2 ⟨m.2, hm2, by rw [← hm1]; exact h4⟩

/-! ## Evaluation -/

section Evaluates
variable {D : Type} [Inhabited D] {M : Type → Type} [Monad M] {R : {α : Type} → M α → α → Prop}
  (hR : Evaluates M R) {qN : D → D → M D} {hN : D → D → D} (hq : ∀ a b, R (qN a b) (hN a b))
include hR hq

omit [Inhabited D] [Monad M] hR in
theorem Evaluates.lone (i : ℕ) (a s : D) : R (lone qN i a s) (loneF hN i a s) := by
  unfold Octopus.lone loneF
  split_ifs
  · exact hq a s
  · exact hq s a

theorem Evaluates.stepC : ∀ (js : List ℕ) (v s : List D), R (stepC qN js v s) (stepF hN js v s)
  | [], _, _ => hR.pure _
  | [i], v, s => hR.bind (Evaluates.lone hq i _ _) (hR.pure _)
  | i :: j :: l, v, s => by
      by_cases hs : sib i j
      · have e1 : Octopus.stepC qN (i :: j :: l) v s =
            (qN (v.headD default) (v.tail.headD default) >>=
              fun u => Octopus.stepC qN l v.tail.tail s >>= fun r => Pure.pure (u :: r)) := by
          simp only [Octopus.stepC, if_pos hs]
        have e2 : stepF hN (i :: j :: l) v s =
            hN (v.headD default) (v.tail.headD default) :: stepF hN l v.tail.tail s := by
          simp only [stepF, Octopus.stepC, if_pos hs]; rfl
        rw [e1, e2]
        exact hR.bind (hq _ _) (hR.bind (Evaluates.stepC l _ _) (hR.pure _))
      · have e1 : Octopus.stepC qN (i :: j :: l) v s =
            (Octopus.lone qN i (v.headD default) (s.headD default) >>=
              fun u =>
                Octopus.stepC qN (j :: l) v.tail s.tail >>= fun r => Pure.pure (u :: r)) := by
          simp only [Octopus.stepC, if_neg hs]
        have e2 : stepF hN (i :: j :: l) v s =
            loneF hN i (v.headD default) (s.headD default) :: stepF hN (j :: l) v.tail s.tail := by
          simp only [stepF, Octopus.stepC, if_neg hs]; rfl
        rw [e1, e2]
        exact hR.bind (Evaluates.lone hq i _ _) (hR.bind (Evaluates.stepC (j :: l) _ _) (hR.pure _))

/-- If the node program evaluates to hN, `octC` evaluates to `octF`, in the sense of `Evaluates`
(hR; Compile/MerkleList.lean). -/
theorem Evaluates.octC :
    ∀ (d : ℕ) (js : List ℕ) (v s : List D), R (octC qN d js v s) (octF hN d js v s)
  | 0, _, _, _ => hR.pure _
  | d + 1, js, v, s => hR.bind (hR.stepC hq js v s) (Evaluates.octC d _ _ _)

end Evaluates

/-! ## The number of queries, and every other property that pure and bind preserve -/

/-- A bound on oracle algorithms that adds up along bind. Examples: DetBound of
Compile/GlueBinding.lean (no coin, at most t queries); OComp.CostBound w (the weights of the queries
add up to at most t). A property without a number (all queries avoid an oracle; the algorithm
factors through a part of its answers) is the case where P does not look at t. -/
structure Counts (S : OSpec) (P : {α : Type} → OComp S α → ℕ → Prop) : Prop where
  pure : ∀ {α : Type} (a : α) (t : ℕ), P (OComp.pure a) t
  bind : ∀ {α β : Type} {c : OComp S α} {g : α → OComp S β} {s t : ℕ},
    P c s → (∀ a, P (g a) t) → P (c.bind g) (s + t)
  mono : ∀ {α : Type} {c : OComp S α} {s t : ℕ}, P c s → s ≤ t → P c t

section Bound
variable {S : OSpec} {P : {α : Type} → OComp S α → ℕ → Prop} (hP : Counts S P) {D : Type}
  [Inhabited D] {nd : D → D → OComp S D} (hn : ∀ a b, P (nd a b) 1)
include hP hn

omit [Inhabited D] hP in
theorem Counts.lone (i : ℕ) (a s : D) : P (lone nd i a s) 1 := by
  unfold Octopus.lone
  split_ifs
  · exact hn a s
  · exact hn s a

theorem Counts.stepC : ∀ (js : List ℕ) (v s : List D), P (stepC nd js v s) (up js).length
  | [], _, _ => hP.pure _ _
  | [i], v, s => hP.bind (t := 0) (Counts.lone hn i _ _) fun _ => hP.pure _ _
  | i :: j :: l, v, s => by
      by_cases hs : sib i j
      · have e1 : Octopus.stepC nd (i :: j :: l) v s =
            (nd (v.headD default) (v.tail.headD default)).bind fun u =>
              (Octopus.stepC nd l v.tail.tail s).bind fun r => OComp.pure (u :: r) := by
          simp only [Octopus.stepC, if_pos hs]; rfl
        rw [e1]
        refine hP.mono
          (hP.bind (t := (up l).length + 0) (hn _ _) fun u =>
            hP.bind (t := 0) (Counts.stepC l _ _) fun _ => hP.pure _ _) ?_
        simp only [up, if_pos hs, List.length_cons]; omega
      · have e1 : Octopus.stepC nd (i :: j :: l) v s =
            (Octopus.lone nd i (v.headD default) (s.headD default)).bind fun u =>
                (Octopus.stepC nd (j :: l) v.tail s.tail).bind fun r => OComp.pure (u :: r) := by
          simp only [Octopus.stepC, if_neg hs]; rfl
        rw [e1]
        refine hP.mono
          (hP.bind (t := (up (j :: l)).length + 0) (Counts.lone hn i _ _) fun u =>
            hP.bind (t := 0) (Counts.stepC (j :: l) _ _) fun _ => hP.pure _ _) ?_
        simp only [up, if_neg hs, List.length_cons]; omega

/-- For a bound P with `Counts S P` (hP): if a node costs 1, `octC` costs at most js.length * d: no
more than the verification of js.length full paths. -/
theorem Counts.octC : ∀ (d : ℕ) (js : List ℕ) (v s : List D), P (octC nd d js v s) (js.length * d)
  | 0, _, _, _ => hP.pure _ _
  | d + 1, js, v, s => by
      refine hP.mono (hP.bind (hP.mono (hP.stepC hn js v s) (length_up_le js)) fun v' =>
        hP.mono (Counts.octC d (up js) v' _) (Nat.mul_le_mul_right d (length_up_le js))) ?_
      rw [Nat.mul_succ]; omega

end Bound

end Compile
