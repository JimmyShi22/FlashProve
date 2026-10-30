-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/GenWitProofs.lean: the proofs of CompileK/GenWit.lean. Generic in the scheme.

Main names:
  `withW_completeness`: under the hypotheses of its statement, a scheme whose prover is handed pairs
    (x, ()), read in the syntax with witnesses, keeps its completeness error.
  `withW_privacy`: under the hypotheses of its statement, it keeps index privacy, with the same
    simulator and the same bound.
  `binding_congr_V`: index binding reads a scheme only through its verifier. Two schemes with the
    same V (their proving keys may be of different types) have it together, with the same extractor
    and the same bound.

Why: all three follow from equalities of programs. The completeness experiment of `withW W A` on a
batch b is that of A on b with the witnesses forgotten (`completenessExp_withW`). An environment Z
for the relation with witnesses gives the environment `forgetEnv Z` for the relation without: the
same slots, the same marks, the witnesses forgotten. With `hpp` for the ideal one, the real and the
ideal experiment with Z are those with `forgetEnv Z` (`realExp_withW`, `idealExp_forget`): what a
batch releases and the instances of the adversary's own slots do not depend on the witnesses
(`released_forgetB`, `ownX_forgetB`).

Limits: this file says nothing on index binding, or on any other form of binding, for `withW W A`:
that needs an extractor for witnesses (CompileK/KnowExt.lean). It says nothing on a construction.
-/
import CompileK.GenWit
import Rom.Bridge

set_option autoImplicit false

open scoped ENNReal

namespace ZKCP.Gen
open Rom (OSpec)

variable {S : OSpec} {I X W PP IVK ISK ISK' Pf : Type}

/-! ## Batches with the witnesses forgotten -/

/-- A batch as the environment names it, the witnesses forgotten; slots and marks stay. -/
def forgetB (b : Batch X W) : Batch X Unit := b.map fun s => (s.1, (), s.2.2)

/-- The environment for the relation without witnesses. -/
def forgetEnv (Z : ViewEnv S IVK X W Pf) : ViewEnv S IVK X Unit Pf := fun v => (Z v).map forgetB

theorem pairs_forgetB (b : Batch X W) : (forgetB b).pairs = forgetW b.pairs := by
  simp only [forgetB, forgetW, Batch.pairs, List.map_map]
  rfl

theorem ownX_forgetB (b : Batch X W) : (forgetB b).ownX = b.ownX := by
  simp only [forgetB, Batch.ownX, List.filter_map, List.map_map]
  rfl

theorem released_forgetB (b : Batch X W) (πs : List Pf) :
    (forgetB b).released πs = b.released πs := by
  simp only [forgetB, Batch.released, List.zip_map_left, List.filter_map, List.map_map]
  rfl

theorem fst_forgetW (b : List (X × W)) : (forgetW b).map Prod.fst = b.map Prod.fst := by
  simp only [forgetW, List.map_map]
  rfl

theorem validBatch_forgetW {R : RelPair I X W PP} {R₀ : RelPair I X Unit PP}
    (h : ∀ i x w, R.yes i x w → R₀.yes i x ()) {B : ℕ} {i : I}
    {b : List (X × W)} (hb : ValidBatch R B i b) :
    ValidBatch R₀ B i (forgetW b) := by
  refine ⟨by rw [forgetW, List.length_map]; exact hb.1, fun xu hxu => ?_⟩
  obtain ⟨xw, hxw, rfl⟩ := List.mem_map.1 hxu
  exact h i xw.1 xw.2 (hb.2 xw hxw)

/-- A program that reads the prover's output only as a list does not see which of two equal batches
was named. -/
theorem P_bind_congr {γ : Type} (A : Arg S I X W IVK ISK Pf) (k : ISK) {b b' : List (X × W)}
    (h : b = b') (F : List Pf → Rom.OComp S γ) :
    ((A.P k b).bind fun l => F l.val) = (A.P k b').bind fun l => F l.val := by
  subst h
  rfl

/-- The prover of `withW W A`, followed by a program that reads its output as a list. -/
theorem withW_P_bind {γ : Type} (A : Arg S I X Unit IVK ISK Pf) (k : ISK)
    (b : List (X × W)) (F : List Pf → Rom.OComp S γ) :
    (((withW W A).P k b).bind fun l => F l.val) = (A.P k (forgetW b)).bind fun l => F l.val := by
  show ((A.P k (forgetW b)).bind fun l =>
        Rom.OComp.pure (⟨l.val, l.property.trans (List.length_map _)⟩ : Slots Pf b)).bind
      (fun l => F l.val) = _
  rw [Rom.OComp.bind_assoc]
  rfl

/-! ## Completeness -/

theorem verifyAll_withW (A : Arg S I X Unit IVK ISK Pf) (v : IVK) :
    ∀ l : List (X × Pf), verifyAll (withW W A) v l = verifyAll A v l
  | [] => rfl
  | (x, π) :: t => by
      show (A.V v x π).bind (fun c => (verifyAll (withW W A) v t).bind fun cs => .pure (c && cs)) =
        (A.V v x π).bind fun c => (verifyAll A v t).bind fun cs => .pure (c && cs)
      rw [verifyAll_withW A v t]

theorem sessionExp_withW (A : Arg S I X Unit IVK ISK Pf) (v : IVK) (k : ISK) (b : List (X × W)) :
    sessionExp (withW W A) v k b = sessionExp A v k (forgetW b) := by
  show ((withW W A).P k b).bind (fun πs => verifyAll (withW W A) v ((b.map Prod.fst).zip πs.val)) =
    (A.P k (forgetW b)).bind fun πs => verifyAll A v (((forgetW b).map Prod.fst).zip πs.val)
  rw [withW_P_bind A k b fun l => verifyAll (withW W A) v ((b.map Prod.fst).zip l), fst_forgetW]
  simp only [verifyAll_withW]

/-- The completeness experiment of `withW W A` is that of A on the batch with the witnesses
forgotten. -/
theorem completenessExp_withW (A : Arg S I X Unit IVK ISK Pf) (i : I) (b : List (X × W)) :
    completenessExp (withW W A) i b = completenessExp A i (forgetW b) := by
  show (A.C i).bind (fun o => sessionExp (withW W A) o.1 o.2 b) =
    (A.C i).bind fun o => sessionExp A o.1 o.2 (forgetW b)
  simp only [sessionExp_withW]

theorem withW_completeness : Spec.withW_completeness :=
  fun _ _ _ _ _ _ _ _ _ _ A _ _ h hc i b hb => by
    rw [completenessExp_withW]
    exact hc i (forgetW b) (validBatch_forgetW h hb)

/-! ## Index privacy -/

theorem forgetEnv_isValid {R : RelPair I X W PP} {R₀ : RelPair I X Unit PP}
    (h : ∀ i x w, R.yes i x w → R₀.yes i x ()) {B : ℕ} {i : I}
    {Z : ViewEnv S IVK X W Pf} (hZ : Z.IsValid R B i) :
    (forgetEnv Z).IsValid R₀ B i := by
  intro v b₀ hb₀
  obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hb₀
  rw [pairs_forgetB]
  exact validBatch_forgetW h (hZ v b hb)

theorem realLoop_withW (A : Arg S I X Unit IVK ISK Pf) (Z : ViewEnv S IVK X W Pf)
    (k : ISK) (V : AdvVerifier S X Pf) :
    ∀ (n : ℕ) (v : View S IVK X Pf),
      realLoop (withW W A) Z k V n v = realLoop A (forgetEnv Z) k V n v := by
  induction V with
  | halt => exact fun _ _ => rfl
  | query o q K ih =>
    intro n v
    simp only [realLoop]
    exact congrArg _ (funext fun r => ih r n _)
  | sample m K ih =>
    intro n v
    simp only [realLoop]
    exact congrArg _ (funext fun r => ih r n _)
  | request K ih =>
    intro n v
    cases n with
    | zero => rfl
    | succ n =>
      simp only [realLoop, forgetEnv]
      cases hz : Z v with
      | none => rfl
      | some b =>
        show ((withW W A).P k b.pairs).bind (fun πs =>
            realLoop (withW W A) Z k (K (b.released πs.val)) n
              { v with sessions := v.sessions ++ [b.released πs.val] }) =
          (A.P k (forgetB b).pairs).bind fun πs =>
            realLoop A (forgetEnv Z) k (K ((forgetB b).released πs.val)) n
              { v with sessions := v.sessions ++ [(forgetB b).released πs.val] }
        rw [withW_P_bind A k b.pairs fun l =>
              realLoop (withW W A) Z k (K (b.released l)) n
                { v with sessions := v.sessions ++ [b.released l] },
          P_bind_congr A k (pairs_forgetB b) fun l =>
            realLoop A (forgetEnv Z) k (K ((forgetB b).released l)) n
              { v with sessions := v.sessions ++ [(forgetB b).released l] }]
        refine congrArg _ (funext fun l => ?_)
        rw [released_forgetB]
        exact ih _ n _

/-- The real experiment of `withW W A` with Z is that of A with `forgetEnv Z`: one program. -/
theorem realExp_withW (A : Arg S I X Unit IVK ISK Pf) (Vt : IVK → AdvVerifier S X Pf)
    (Z : ViewEnv S IVK X W Pf) (i : I) (N : ℕ) :
    realExp (withW W A) Vt Z i N = realExp A Vt (forgetEnv Z) i N := by
  show (A.C i).bind (fun o => realLoop (withW W A) Z o.2 (Vt o.1) N ⟨o.1, [], [], []⟩) =
    (A.C i).bind fun o => realLoop A (forgetEnv Z) o.2 (Vt o.1) N ⟨o.1, [], [], []⟩
  simp only [realLoop_withW]

/-- The simulator's answer to a batch, followed by a map that reads the proofs as a list, does not
see which of two equal lists of instances was named. -/
theorem prove_bind_congr {γ : Type} (Sim : Simulator S PP IVK X Pf) (s : Sim.St) {xs xs' : List X}
    (h : xs = xs') (F : List Pf → Sim.St → PMF γ) :
    ((Sim.prove s xs).bind fun out => F out.1.val out.2) =
      (Sim.prove s xs').bind fun out => F out.1.val out.2 := by
  subst h
  rfl

theorem idealLoop_forget (Sim : Simulator S PP IVK X Pf)
    (Z : ViewEnv S IVK X W Pf) (V : AdvVerifier S X Pf) :
    ∀ (n : ℕ) (v : View S IVK X Pf) (s : Sim.St),
      idealLoop Sim Z V n v s = idealLoop Sim (forgetEnv Z) V n v s := by
  induction V with
  | halt => exact fun _ _ _ => rfl
  | query o q K ih =>
    intro n v s
    simp only [idealLoop]
    exact congrArg _ (funext fun out => ih out.1 n _ out.2)
  | sample m K ih =>
    intro n v s
    simp only [idealLoop]
    exact congrArg _ (funext fun r => ih r n _ s)
  | request K ih =>
    intro n v s
    cases n with
    | zero => rfl
    | succ n =>
      simp only [idealLoop, forgetEnv]
      cases hz : Z v with
      | none => rfl
      | some b =>
        show (Sim.prove s b.ownX).bind (fun out =>
            idealLoop Sim Z (K (b.ownX.zip out.1.val)) n
              { v with sessions := v.sessions ++ [b.ownX.zip out.1.val] } out.2) =
          (Sim.prove s (forgetB b).ownX).bind fun out =>
            idealLoop Sim (forgetEnv Z) (K ((forgetB b).ownX.zip out.1.val)) n
              { v with sessions := v.sessions ++ [(forgetB b).ownX.zip out.1.val] } out.2
        rw [prove_bind_congr Sim s (ownX_forgetB b) fun l t =>
            idealLoop Sim (forgetEnv Z) (K ((forgetB b).ownX.zip l)) n
              { v with sessions := v.sessions ++ [(forgetB b).ownX.zip l] } t]
        refine congrArg _ (funext fun out => ?_)
        rw [ownX_forgetB]
        exact ih _ n _ out.2

/-- The ideal experiment with Z is that with `forgetEnv Z`, if the two relations have the same
public parameters. -/
theorem idealExp_forget {R : RelPair I X W PP} {R₀ : RelPair I X Unit PP}
    (hpp : R.pp = R₀.pp) (Sim : Simulator S PP IVK X Pf) (Vt : IVK → AdvVerifier S X Pf)
    (Z : ViewEnv S IVK X W Pf) (i : I) (N : ℕ) :
    idealExp R Sim Vt Z i N = idealExp R₀ Sim Vt (forgetEnv Z) i N := by
  unfold idealExp
  rw [hpp]
  simp only [idealLoop_forget Sim Z]

theorem withW_privacy : Spec.withW_privacy :=
  fun _ _ _ _ _ _ _ _ _ _ A _ Sim _ h hpp hp i Z hZ tV Vt N hV => by
    rw [realExp_withW, idealExp_forget hpp]
    exact hp i (forgetEnv Z) (forgetEnv_isValid h hZ) tV Vt N hV

/-! ## Index binding reads only V -/

/-- The experiment of index binding reads a scheme only through its verifier. -/
theorem bindingExp_congr_V {A : Arg S I X W IVK ISK Pf} {A' : Arg S I X W IVK ISK' Pf}
    (h : ∀ v x π, A.V v x π = A'.V v x π) {St : Type} (E : Extractor S I X W IVK Pf)
    (Ct : Rom.OComp S (IVK × St)) (Pt : St → Rom.OComp S (X × Pf)) :
    bindingExp A E Ct Pt = bindingExp A' E Ct Pt := by
  have hV : A.V = A'.V := funext fun v => funext fun x => funext fun π => h v x π
  unfold bindingExp
  rw [hV]

/-- Index binding reads only V. -/
theorem binding_congr_V (R : RelPair I X W PP) {A : Arg S I X W IVK ISK Pf}
    {A' : Arg S I X W IVK ISK' Pf} (h : ∀ v x π, A.V v x π = A'.V v x π)
    {E : Extractor S I X W IVK Pf} {ε : ℕ → ℕ → ℝ≥0∞} (hb : HasIndexBindingWith R A E ε) :
    HasIndexBindingWith R A' E ε :=
  fun tC tP St Ct Pt hC hP => by
    rw [← bindingExp_congr_V h]
    exact hb tC tP St Ct Pt hC hP

end ZKCP.Gen
