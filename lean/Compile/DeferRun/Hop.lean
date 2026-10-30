-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/DeferRun/Hop.lean: FROM A REAL EXPERIMENT TO MODE I OF A TOKEN CHALLENGER, for any
challenger whose tokens keep their numbers for the whole experiment, and any exchange of queries.
Definitions and lemmas, general in the family of oracles.

General lemmas. This file states no goal of the release.

A challenger in the language of tokens (Chall, Rom/Defer.lean) has two modes. In mode R one lazily
sampled table serves everybody. This file says, once and for every challenger:

  erasedStep C, erasedW C   the challenger as oracle algorithms: each step erased (erase,
                  Compile/Star.lean), with THE STORE OF ALL STRINGS AS PART OF ITS STATE.
  modeR_erased    mode R of C, and erasedW C: every adversary has the same output.
  gAdm_via        an admissible adversary stays admissible when its queries are exchanged.
  viaErased_modeR   if all steps are written with exchanged queries (φ, a bijection with inverse ψ):
                  the same output as against mode R of C, the adversary's queries exchanged by ψ
                  (World.pre, Rom/SpecVia.lean).
  hop_pre         mode R and mode I of C, both behind ψ, are within the library's bound for one
                  passage to fresh answers (costTotal, Rom/SpecHopCost.lean), if the runs in mode I
                  of the adversary with exchanged queries stay within the counts.
  real_to_modeI   the three together: an experiment that has the output of the erased steps with
                  exchanged queries is within costTotal of mode I of C behind ψ.
Limits. The price of the hop is the library's formula costTotal at letters e, M, ℓ, os; no number is
evaluated. That the runs in mode I stay within these counts is a premise of hop_pre and
real_to_modeI. The one theorem on a probability that is called is Rom.hopCost_total
(Rom/HopCost.lean); all else here is an equality of laws.
Follows the pattern of hopRPG (Compile/Batch/PubProgReal.lean) and closeVia_of
(Compile/Batch/Ghost.lean).

-/
import Compile.Step1_life2_Chall
import Compile.Step1_defc_Gen
import Compile.Batch.SpecGlue
import Rom.HopCost
import Rom.Via

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace Compile
namespace DeferRun
open Rom Prob
open Compile.GlueB (GCall GIn GAdm)

variable {S : OSpec} {sp : Split S} {Out In α : Type}

/-- A step of the challenger as an oracle algorithm. The state: the challenger's own, and the store
of all strings so far. -/
def erasedStep (C : Chall S sp Out In) (s : C.τ × List Bits) (m : Out) :
    OComp S (In × (C.τ × List Bits)) :=
  (erase (C.step s.1 m) s.2).bind fun o => pure (o.1.1, (o.1.2, o.2))

/-- The challenger as oracle algorithms over one lazily sampled table. -/
def erasedW (C : Chall S sp Out In) : World S Out In := World.ofOComp (erasedStep C)

/-- **Mode R of a challenger is the challenger of its erased steps.** -/
theorem modeR_erased (C : Chall S sp Out In) (A : Adv S Out In α) (s : C.τ) (D : DSt S) :
    (interact (C.world false) A (s, D)).map Prod.fst =
      (interact (erasedW C) A ((s, D.vals), D.table)).map Prod.fst := by
  have h := interact_lump (C.world false) (erasedW C)
    (fun x : C.τ × DSt S => ((x.1, x.2.vals), x.2.table)) (fun _ => True)
    (fun x o q _ => by
      show ((lazyAnswer x.2.table o q).map _).map _ = (lazyAnswer x.2.table o q).map _
      rw [PMF.map_comp]
      rfl)
    (fun x m _ => by
      show (((C.step x.1 m).run false x.2).map fun p => (p.1.1, (p.1.2, p.2))).map _ =
        (((erase (C.step x.1 m) x.2.vals).bind fun o =>
          pure (o.1.1, (o.1.2, o.2))).runLazy x.2.table).map fun p => (p.1.1, (p.1.2, p.2))
      rw [Life2.runLazy_bind_pure, ← Life2.run_false_eq_erase, PMF.map_comp, PMF.map_comp,
        PMF.map_comp]
      rfl)
    (fun _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ => trivial) A (s, D) trivial
  rw [← h, PMF.map_comp]
  rfl

/-- An admissible adversary stays admissible when its queries are exchanged. -/
theorem gAdm_via {X Wn IVK Pf : Type} (ok : ZKCP.Gen.Batch X Wn → Prop) (ψ : QMap S)
    (A : Adv S (GCall X Wn) (GIn IVK Pf) α) :
    ∀ (f : Bool) (n : ℕ), GAdm ok A f n → GAdm ok (A.via ψ) f n := by
  induction A with
  | halt a => exact fun _ _ _ => trivial
  | sample m k ih => exact fun f n hA r => ih r f n (hA r)
  | query o q k ih => exact fun f n hA r => ih _ f n (hA _)
  | call c k ih =>
    intro f n hA
    rcases c with _ | b
    · exact ⟨hA.1, fun a => ih a true n (hA.2 a)⟩
    · cases n with
      | zero => exact hA.elim
      | succ n => exact ⟨hA.1, hA.2.1, fun a => ih a f n (hA.2.2 a)⟩

/-- All steps written with exchanged queries: the same output as against mode R, the adversary's
queries exchanged back. -/
theorem viaErased_modeR (C : Chall S sp Out In) {φ ψ : QMap S} (hP : QMap.Perm φ ψ)
    (A : Adv S Out In α) (c₀ : C.τ) :
    (interact (World.ofOComp fun s m => (erasedStep C s m).via φ) A
        ((c₀, []), Table.empty S)).map Prod.fst =
      (interact ((C.world false).pre ψ) A (c₀, DSt.init S)).map Prod.fst := by
  rw [viaWorld S Out In _ α φ ψ hP (erasedStep C) A (c₀, []) (Table.empty S), Table.via_empty,
    viaPre S Out In α ψ (C.world false) A (c₀, DSt.init S)]
  exact (modeR_erased C (A.via ψ) c₀ (DSt.init S)).symm

/-- **The hop**, behind an exchange of queries. -/
theorem hop_pre (C : Chall S sp Out In) (c₀ : C.τ) (ψ : QMap S) (e M ℓ : S.ι → ℕ)
    (os : Finset S.ι) (A : Adv S Out In α) (t N : ℕ) (hT : A.TotalBound t N)
    (hw : ∀ x ∈ (interact (C.world true) (A.via ψ) (c₀, DSt.init S)).support,
      x.2.2.Within e M ℓ os) :
    tv ((interact ((C.world false).pre ψ) A (c₀, DSt.init S)).map Prod.fst)
        ((interact ((C.world true).pre ψ) A (c₀, DSt.init S)).map Prod.fst) ≤
      costTotal e M ℓ os t := by
  rw [viaPre S Out In α ψ (C.world false) A (c₀, DSt.init S),
    viaPre S Out In α ψ (C.world true) A (c₀, DSt.init S)]
  exact hopCost_total e M ℓ os sp Out In α C c₀ (A.via ψ) t N
    ((viaBounds S Out In α ψ A).1 t N hT) hw

/-- **From a real experiment to mode I.** Wr, r₀: any challenger and state against which A has the
output that it has against the erased steps with exchanged queries. -/
theorem real_to_modeI (C : Chall S sp Out In) (c₀ : C.τ) {φ ψ : QMap S} (hP : QMap.Perm φ ψ)
    (e M ℓ : S.ι → ℕ) (os : Finset S.ι) (Wr : World S Out In) (r₀ : Wr.σ) (A : Adv S Out In α)
    (t N : ℕ) (hT : A.TotalBound t N)
    (hr : (interact Wr A r₀).map Prod.fst =
      (interact (World.ofOComp fun s m => (erasedStep C s m).via φ) A
        ((c₀, []), Table.empty S)).map Prod.fst)
    (hw : ∀ x ∈ (interact (C.world true) (A.via ψ) (c₀, DSt.init S)).support,
      x.2.2.Within e M ℓ os) :
    tv ((interact Wr A r₀).map Prod.fst)
        ((interact ((C.world true).pre ψ) A (c₀, DSt.init S)).map Prod.fst) ≤
      costTotal e M ℓ os t := by
  rw [hr, viaErased_modeR C hP A c₀]
  exact hop_pre C c₀ ψ e M ℓ os A t N hT hw

end DeferRun
end Compile

#print axioms Compile.DeferRun.modeR_erased
#print axioms Compile.DeferRun.hop_pre
#print axioms Compile.DeferRun.real_to_modeI
