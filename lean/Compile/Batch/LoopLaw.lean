-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/LoopLaw.lean: the distribution of the search over nonces. It proves `Spec.ok_share`,
`Spec.ok_indep` and `Spec.fbG_fibre` (Compile/Batch/SpecLoop.lean) (words of this library:
lean/GLOSSARY.md).

 1  The answers, sorted. Under `w.OKG` and `g.OK`: the challenge of a uniform answer is uniform
    (`chalU`), and so are its proof-of-work bits (`tstU`). `ansB_someG`, `ansT_eq`: the sets of
    answers are fibres. `ans_split`, `ansT_fibre`: a uniform answer, and one uniform among those
    with given bits, each sampled in two steps.
 2  `ok_share`, `ok_indep` (the last section of the file)
 3  one attempt (`try_last`, `try_step`)
 4  the search, by recursion on the number of attempts that are left (`fbWL_fibre`), and
    `fbG_fibre`. Why it is true: on every path the given challenge c is used in exactly one attempt,
    the final one; the other attempts sample from all answers with their proof-of-work bits.

Notation: `w`: a `WireRB lam K r a` (Iop/BatchWire.lean), the wire record of one round; `w.OKG`: the
laws of the wire of a round that may have a test; `g`: a `GrW C P` (the same file); `g.b`: the
number of test bits; `g.tst`: the test bits of a verifier message; `g.set`: the verifier message
with other test bits; `g.ok`: the test: all test bits are 0; `g.more`: the honest prover tries the
nonces 0, .., more; `g.OK`: tst and set are a lens, and the nonces that the honest prover tries are
read back (`get_put`); in Compile/Batch/Mirror.lean: `ansB w h`: the answers from which the answer
of a round is sampled: all, or those that yield the given challenge (all, if none does);
`ansT w g z`: the answers whose challenge has the proof-of-work bits z (all, if none has);
`zBits b r`: b bits from a number below 2^b; `qFail ok` (Prob/Retry.lean): the probability that one
uniform sample fails the test.
-/
import Compile.Batch.SpecLoop
import Compile.Step1_defc_Prob
import Prob.LensLaw

noncomputable section

namespace Compile.Batch.LoopLaw
open Iop Rom Prob
open Compile.DefC (virtL fibre fibre_nonempty unif_eq_bind_fibre unif_prod_map_fst)
open scoped ENNReal

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X}

/-- the answers of a Fiat-Shamir query -/
abbrev Ans (lam K : ℕ) : Type := (Fin K → Dig lam) × Dig lam

section Sorted
variable {r : Round} {a : RAnn r} (w : WireRB lam K r a) {P : Type} (g : GrW r.Chal P)

theorem lens (hg : g.OK) : Prob.Lens.OK g.tst g.set := ⟨hg.tst_set, hg.set_tst, hg.set_set⟩

/-- For `w.OKG`: the challenge of a uniform answer is uniform. -/
theorem chalU (hw : w.OKG) : (unif (Ans lam K)).map (fun x => w.chal x.1) = unif r.Chal := by
  have h1 : (unif (Ans lam K)).map Prod.fst = unif (Fin K → Dig lam) := unif_prod_map_fst
  calc
    (unif (Ans lam K)).map (fun x => w.chal x.1) = ((unif (Ans lam K)).map Prod.fst).map w.chal :=
      (PMF.map_comp _ _ _).symm
    _ = (unif (Fin K → Dig lam)).map w.chal := by rw [h1]
    _ = unif r.Chal := hw.chal_unif

/-- For `w.OKG`, `g.OK`: the proof-of-work bits of the challenge of a uniform answer are uniform. -/
theorem tstU (hw : w.OKG) (hg : g.OK) :
    (unif (Ans lam K)).map (fun x => g.tst (w.chal x.1)) = unif (Fin g.b → Bool) := by
  have e : (fun x : Ans lam K => g.tst (w.chal x.1)) = g.tst ∘ fun x => w.chal x.1 := rfl
  rw [e, ← PMF.map_comp, chalU w hw, Prob.Lens.map_tst (lens g hg)]

open Classical in
theorem ansB_someG (hw : w.OKG) (c : r.Chal) :
    ansB w (some c) =
      ⟨fibre (fun x : Ans lam K => w.chal x.1) c, fibre_nonempty _ (chalU w hw) c⟩ := by
  have h : (Finset.univ.filter fun x : Ans lam K => w.chal x.1 = c).Nonempty :=
    fibre_nonempty (fun x : Ans lam K => w.chal x.1) (chalU w hw) c
  show (if h : (Finset.univ.filter fun x : Ans lam K => w.chal x.1 = c).Nonempty then
        (⟨_, h⟩ : ASet lam K)
      else ⟨Finset.univ, Finset.univ_nonempty⟩) = _
  rw [dif_pos h]
  rfl

theorem ansT_eq (hw : w.OKG) (hg : g.OK) (z : Fin g.b → Bool) :
    ansT w g z =
      ⟨fibre (fun x : Ans lam K => g.tst (w.chal x.1)) z, fibre_nonempty _ (tstU w g hw hg) z⟩ := by
  have h : (Finset.univ.filter fun x : Ans lam K => g.tst (w.chal x.1) = z).Nonempty :=
    fibre_nonempty (fun x : Ans lam K => g.tst (w.chal x.1)) (tstU w g hw hg) z
  show (if h : (Finset.univ.filter fun x : Ans lam K => g.tst (w.chal x.1) = z).Nonempty then
        (⟨_, h⟩ : ASet lam K)
      else ⟨Finset.univ, Finset.univ_nonempty⟩) = _
  rw [dif_pos h]
  rfl

/-- the uniform distribution on a set of answers -/
abbrev U (A : ASet lam K) : PMF (Ans lam K) := PMF.uniformOfFinset A.1 A.2

theorem chal_of_memB (hw : w.OKG) (c : r.Chal) (x : Ans lam K)
    (hx : x ∈ (U (ansB w (some c))).support) : w.chal x.1 = c := by
  classical
  rw [ansB_someG w hw c, PMF.mem_support_uniformOfFinset_iff] at hx
  simpa [fibre] using hx

theorem tst_of_memT (hw : w.OKG) (hg : g.OK) (z : Fin g.b → Bool)
    (x : Ans lam K) (hx : x ∈ (U (ansT w g z)).support) : g.tst (w.chal x.1) = z := by
  rw [ansT_eq w g hw hg z, PMF.mem_support_uniformOfFinset_iff] at hx
  simpa [fibre] using hx

/-- For `w.OKG`: a uniform answer is a uniform challenge, then a uniform answer from its fibre. -/
theorem ans_unifG (hw : w.OKG) :
    unif (Ans lam K) = (unif r.Chal).bind fun c => U (ansB w (some c)) := by
  classical
  refine (unif_eq_bind_fibre (fun x : Ans lam K => w.chal x.1) (chalU w hw)).trans
    (congrArg _ (funext fun c => ?_))
  rw [ansB_someG w hw c]

/-- For `w.OKG`, `g.OK`, a uniform answer is: uniform proof-of-work bits, then a uniform answer with
these bits. -/
theorem ans_tst (hw : w.OKG) (hg : g.OK) :
    unif (Ans lam K) = (unif (Fin g.b → Bool)).bind fun z => U (ansT w g z) := by
  refine (unif_eq_bind_fibre (fun x : Ans lam K => g.tst (w.chal x.1)) (tstU w g hw hg)).trans
    (congrArg _ (funext fun z => ?_))
  rw [ansT_eq w g hw hg z]

/-- For `w.OKG`, `g.OK`, a uniform answer is: proof-of-work bits from a uniform number, then a
uniform answer with these bits. -/
theorem ans_split (hw : w.OKG) (hg : g.OK) :
    unif (Ans lam K) = (unif (Fin (2 ^ g.b - 1 + 1))).bind fun x => U (ansT w g (zBits g.b x)) := by
  have e : unif (Fin g.b → Bool) = (unif (Fin (2 ^ g.b - 1 + 1))).map (zBits g.b) :=
    (Prob.map_bitsOf g.b).symm
  rw [ans_tst w g hw hg, e, PMF.bind_map]
  rfl

/-- For `w.OKG`, `g.OK`, a uniform answer with the bits z is: a uniform challenge c, then a uniform
answer that yields c with the bits z written over its own. -/
theorem ansT_fibre (hw : w.OKG) (hg : g.OK) (z : Fin g.b → Bool) :
    U (ansT w g z) = (unif r.Chal).bind fun c => U (ansB w (some (g.set z c))) := by
  refine Prob.fibres_unique (fun x : Ans lam K => g.tst (w.chal x.1)) (fun z => U (ansT w g z))
    (fun z => (unif r.Chal).bind fun c => U (ansB w (some (g.set z c))))
    (fun z x hx => tst_of_memT w g hw hg z x hx) (fun z x hx => ?_) ?_ z
  · obtain ⟨c, -, hc⟩ := (PMF.mem_support_bind_iff _ _ _).1 hx
    show g.tst (w.chal x.1) = z
    rw [chal_of_memB w hw _ x hc, hg.tst_set]
  · have e1 : (unif r.Chal).bind (fun c => U (ansB w (some c))) =
        (unif ((Fin g.b → Bool) × r.Chal)).bind fun p => U (ansB w (some (g.set p.1 p.2))) := by
      rw [← Prob.Lens.map_set (lens g hg), PMF.bind_map]
      rfl
    have e2 : (unif ((Fin g.b → Bool) × r.Chal)).bind (fun p => U (ansB w (some (g.set p.1 p.2)))) =
        (unif (Fin g.b → Bool)).bind fun z =>
          (unif r.Chal).bind fun c => U (ansB w (some (g.set z c))) := by
      rw [Prob.unif_prod]
      unfold Prob.prod
      rw [PMF.bind_bind]
      refine congrArg _ (funext fun z => ?_)
      rw [PMF.bind_map]
      rfl
    exact (ans_tst w g hw hg).symm.trans ((ans_unifG w hw).trans (e1.trans e2))

theorem ok_of_tst {c : r.Chal} (h : g.tst c = fun _ => false) : g.ok c = true := decide_eq_true h
theorem not_ok_of_tst {c : r.Chal} (h : g.tst c ≠ fun _ => false) : g.ok c = false :=
  decide_eq_false h

/-! ## 3. One attempt, as distributions -/

variable {γ : Type}

/-- The last attempt (`w.OKG`, `g.OK`): it is the final one whatever its proof-of-work bits are. -/
theorem try_last (hw : w.OKG) (hg : g.OK) (F : Ans lam K → PMF γ) :
    (unif (Ans lam K)).bind F = (unif r.Chal).bind fun c => (unif (Fin (2 ^ g.b - 1 + 1))).bind fun y =>
      (U (if true || decide (zBits g.b y = fun _ => false) then
              ansB w (some (g.set (zBits g.b y) c))
            else ansT w g (zBits g.b y))).bind F := by
  rw [PMF.bind_comm, ans_split w g hw hg, PMF.bind_bind]
  refine congrArg _ (funext fun y => ?_)
  rw [ansT_fibre w g hw hg, PMF.bind_bind]
  rfl

/-- An attempt that is not the last (`w.OKG`, `g.OK`). F h x: what follows the answer x. If x
passes, what follows does not depend on h (`hk`); if x fails, what follows has the property that is
to be shown (`ih`). Then the same holds of the attempt with what follows: with h = none it is a
uniform c, then the attempt with h = some c. -/
theorem try_step (hw : w.OKG) (hg : g.OK) (F : Option r.Chal → Ans lam K → PMF γ)
    (hk : ∀ c x, g.ok (w.chal x.1) = true → F (some c) x = F none x)
    (ih : ∀ x, g.ok (w.chal x.1) = false → F none x = (unif r.Chal).bind fun c => F (some c) x) :
    (unif (Ans lam K)).bind (F none) = (unif r.Chal).bind fun c => (unif (Fin (2 ^ g.b - 1 + 1))).bind fun y =>
      (U (if false || decide (zBits g.b y = fun _ => false) then
                ansB w (some (g.set (zBits g.b y) c))
              else ansT w g (zBits g.b y))).bind
          (F (some c)) := by
  rw [PMF.bind_comm, ans_split w g hw hg, PMF.bind_bind]
  refine congrArg _ (funext fun y => ?_)
  by_cases hz : zBits g.b y = fun _ => false
  · have e : ∀ c : r.Chal, (U
        (if false || decide (zBits g.b y = fun _ => false) then
            ansB w (some (g.set (zBits g.b y) c))
          else ansT w g (zBits g.b y))).bind (F (some c))
        = (U (ansB w (some (g.set (zBits g.b y) c)))).bind (F none) := by
      intro c
      rw [if_pos (by rw [Bool.false_or]; exact decide_eq_true hz)]
      refine Prob.bind_congr_on _ fun x hx => hk c x (ok_of_tst g ?_)
      rw [chal_of_memB w hw _ x hx, hg.tst_set, hz]
    simp only [e]
    rw [ansT_fibre w g hw hg, PMF.bind_bind]
  · have e : ∀ c : r.Chal, (U
        (if false || decide (zBits g.b y = fun _ => false) then
            ansB w (some (g.set (zBits g.b y) c))
          else ansT w g (zBits g.b y))).bind (F (some c))
        = (U (ansT w g (zBits g.b y))).bind (F (some c)) := by
      intro c
      rw [if_neg (by rw [Bool.false_or]; exact fun h => hz (of_decide_eq_true h))]
    simp only [e]
    rw [PMF.bind_comm]
    refine Prob.bind_congr_on _ fun x hx => ih x (not_ok_of_tst g ?_)
    rw [tst_of_memT w g hw hg _ x hx]
    exact hz

end Sorted

/-! ## 4. The search -/

section Loop
variable (N₀ δ : ℕ) {r : Round} {a : RAnn r} (w : WireRB lam K r a) {P β : Type} (g : GrW r.Chal P)
  (hw : w.OKG) (hg : g.OK) (t : Tag) (tk : Tok) (us : List Tok)
include hw hg

theorem fbWL_fibre (k : ℕ → List Tok → Blk lam K → Tok → Lp lam K L β) :
    ∀ (n j : ℕ) (dd : List Tok) (st : LSt (spec lam K L)),
      (virtL N₀ δ (fbWL w g (ansB w) t tk us none k n j dd)).run st =
        (unif r.Chal).bind fun c =>
          (virtL N₀ δ (fbWL w g (ansB w) t tk us (some c) k n j dd)).run st
  | 0, j, dd, st => try_last w g hw hg _
  | n + 1, j, dd, st =>
      try_step w g hw hg
        (fun h x =>
          (virtL N₀ δ
            (if g.ok (w.chal x.1) then k (j + 1) dd x.1 (st.vals.length - δ)
              else fbWL w g (ansB w) t tk us h k n (j + 1) ((st.vals.length - δ) :: dd))).run
          { st with vals := st.vals ++ [List.ofFn ((split lam K L).split (OracleName.fbw t j) x).2],
                    evs := st.evs ++
                      [⟨OracleName.fbw t j, x, Life2.up N₀ δ tk, us.map (Life2.up N₀ δ),
                        st.vals.length, false⟩] })
        (fun c x hx => by simp only [if_pos hx])
        (fun x hx => by
          simp only [hx, Bool.false_eq_true, if_false]
          exact fbWL_fibre k n (j + 1) _ _)

theorem fbTGL_fibre (k : ℕ → List Tok → Blk lam K → Tok → Lp lam K L β) (st : LSt (spec lam K L)) :
    (virtL N₀ δ (fbTGL w g (ansB w) t tk us none k)).run st =
      (unif r.Chal).bind fun c => (virtL N₀ δ (fbTGL w g (ansB w) t tk us (some c) k)).run st := by
  unfold fbTGL
  cases g.more with
  | zero => exact try_last w g hw hg _
  | succ n =>
      exact try_step w g hw hg
        (fun h x =>
          (virtL N₀ δ
            (if g.ok (w.chal x.1) then k 0 [] x.1 (st.vals.length - δ)
              else fbWL w g (ansB w) t tk us h k n 0 [st.vals.length - δ])).run
          { st with vals := st.vals ++ [List.ofFn ((split lam K L).split (OracleName.fb t) x).2],
                    evs := st.evs ++
                      [⟨OracleName.fb t, x, Life2.up N₀ δ tk, us.map (Life2.up N₀ δ),
                        st.vals.length, false⟩] })
        (fun c x hx => by simp only [if_pos hx])
        (fun x hx => by
          simp only [hx, Bool.false_eq_true, if_false]
          exact fbWL_fibre N₀ δ w g hw hg t tk us k n 0 _ _)

end Loop

/-! ## 2. The share of the answers that pass; independence -/

section Share
variable {r : Round} {a : RAnn r} (w : WireRB lam K r a) {P : Type} (g : GrW r.Chal P)

/-- For `w.OKG`: the challenge and the chaining value of a uniform answer are uniform. -/
theorem pairU (hw : w.OKG) :
    (unif (Ans lam K)).map (fun x => (w.chal x.1, x.2)) = unif (r.Chal × Dig lam) :=
  Prob.map_unif_prodMap w.chal id hw.chal_unif (PMF.map_id _)

/-- the lens on (challenge, chaining value), for `g.OK` -/
theorem lens2 (hg : g.OK) :
    Prob.Lens.OK (fun p : r.Chal × Dig lam => g.tst p.1) (fun z p => (g.set z p.1, p.2)) :=
  ⟨fun z p => hg.tst_set z p.1,
    fun p => Prod.ext (hg.set_tst p.1) rfl,
    fun z z' p => Prod.ext (hg.set_set z z' p.1) rfl⟩

theorem ok_false_iff (c : r.Chal) :
    g.ok c = false ↔ g.tst c ∈ ({fun _ => false} : Set (Fin g.b → Bool))ᶜ := by
  unfold GrW.ok
  rw [decide_eq_false_iff_not]
  rfl

theorem qFail_eq (hw : w.OKG) :
    qFail (fun x : Ans lam K => g.ok (w.chal x.1)) =
      pr (unif (r.Chal × Dig lam))
        {p | g.tst p.1 ∈ ({fun _ => false} : Set (Fin g.b → Bool))ᶜ} := by
  unfold qFail
  rw [← pairU w hw, pr_map]
  exact congrArg _ (Set.ext fun x => ok_false_iff g (w.chal x.1))

end Share

end Compile.Batch.LoopLaw

namespace Compile.Batch
open Iop Rom Prob LoopLaw
open scoped ENNReal

theorem ok_share : Spec.ok_share := by
  intro lam K r a w P g hw hg
  rw [qFail_eq w g hw]
  have e : pr (unif (r.Chal × Dig lam))
        {p | g.tst p.1 ∈ ({fun _ => false} : Set (Fin g.b → Bool))ᶜ} =
      pr (unif (Fin g.b → Bool)) ({fun _ => false} : Set (Fin g.b → Bool))ᶜ := by
    rw [← Prob.Lens.map_tst (lens2 g hg), pr_map]
    rfl
  rw [e, pr_compl, pr_singleton, PMF.uniformOfFintype_apply]
  congr 2
  simp

theorem ok_indep : Spec.ok_indep := by
  intro lam K r a w P g hw hg b
  rw [qFail_eq w g hw]
  have h := Prob.Lens.pr_indep (lens2 g hg) (fun _ => false)
    ({fun _ => false} : Set (Fin g.b → Bool))ᶜ ({b} : Set (r.Chal × Dig lam))
  have e1 : pr (unif (Ans lam K))
        {x | (g.set (fun _ => false) (w.chal x.1), x.2) = b ∧ g.ok (w.chal x.1) = false} =
      pr (unif (r.Chal × Dig lam))
        {c | (g.set (fun _ => false) c.1, c.2) ∈ ({b} : Set (r.Chal × Dig lam)) ∧
          g.tst c.1 ∈ ({fun _ => false} : Set (Fin g.b → Bool))ᶜ} := by
    rw [← pairU w hw, pr_map]
    exact congrArg _ (Set.ext fun x => and_congr Iff.rfl (ok_false_iff g (w.chal x.1)))
  have e2 : pr (unif (Ans lam K)) {x | (g.set (fun _ => false) (w.chal x.1), x.2) = b} =
      pr (unif (r.Chal × Dig lam))
        {c | (g.set (fun _ => false) c.1, c.2) ∈ ({b} : Set (r.Chal × Dig lam))} := by
    rw [← pairU w hw, pr_map]
    rfl
  rw [e1, e2]
  exact h

theorem fbG_fibre : Spec.fbG_fibre := by
  intro I X lam K L N₀ δ r a w P β gr hw hgr t tk us k st
  cases gr with
  | none =>
    show (unif (Ans lam K)).bind _ = (unif r.Chal).bind fun c => (U (ansB w (some c))).bind _
    rw [ans_unifG w hw, PMF.bind_bind]
  | some g => exact fbTGL_fibre N₀ δ w g hw (hgr g rfl) t tk us (fun m => k (some m)) st

end Compile.Batch
