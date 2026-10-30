-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFE1R/SlotsOfFour.lean: LeftRest's FIELD slots (
Link/Law/LeftOfRest.lean: what is left of K9's hLeft): OF THE FULL STATE t BEHIND K8's RUN: ITS
LEDGER HAS ITS SIZES, AND EVERY SLOT THAT A FORM OF THE RUN's FIRST FOUR CLAIMS NAMES IS FILLED IN
IT: FROM Ok's CLAUSE "four" (OkCore.four: Link/Law/OkOne.lean) ALONE. Statements and
proofs: the road of k8_four (Batch/Law/K8Four.lean), walked for "filled" instead of for
the values.

  slots_of_four     general in φ, π, Ok, Fu and the fixed part q: under hπ (π reads the structure,
                    blanked, and the functions off φ) and hOk4 (k8_four's own hypothesis: the
                    snapshot's ledger has its sizes; every slot that a form of the four names lies
                    in the leaves' window or is filled in the snapshot)
  slots_at_phiAll   the field's text at φ := phiAll u ψ · π := pi8 · the promise fun q => Ok q ∧
                    rowsFit p.rows pi8 q, at every fixed part q (the field's is fixed9 (phiAll u ψ)
                    a.1)
  okFour_of_core    hOk4 from OkCore at every q at which Ok holds

THE FOUR STONES. (a) the run's first four claims are four8 tl g: take_four. (b) the run
lays the leaves' hiding coefficients: take_four's hideRun, and hideRun_ok
(OnBytes/Tie/Pv/Psc/PscFork.lean): every slot of the window is filled behind it. (c) "filled" passes
along "later" (Later.keep): from the run's ledger to the full state's by laterK; from the snapshot's
to the full state's by Fx9 … t. (d) the sizes pass along "later" too.

Limits. AN IMPLICATION: hOk4 (OkCore.four) is the debt. No soundness statement.

-/
import Johnson.Desc.First.Batch.Law.K8Four
import Johnson.Desc.First.Link.Law.OkOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.PscRun (Later Sized Filled paid_later hideRun_ok)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.TailClaims (equations)
open VerifiableInference.Desc.First.TailClaims.Law (blank)
open VerifiableInference.Desc.K4Values (winOf)
open VerifiableInference.Desc.PhiAll

/-- **The first four claims' forms name filled slots of the full state's ledger.** -/
theorem slots_of_four {α : Type} (φ : S → α) (Ok : α × Option Pub9 → Prop) (Fu : S → Prop)
    (u : HTailF2) (π : α → Option HTailF2 × Option (Array HFun))
    (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?))
    (hOk4 : ∀ q v tlb g, Ok q → q.2 = some v → (π q.1).1 = some tlb → tlb.heard = some g →
      Sized v.F ∧ ∀ cl ∈ four8 tlb g, ∀ x ∈ cl.form.slots.toList,
        K4Values.InWin (winOf g.leaves) x.1 ∨ Filled v.F x.1) :
    ∀ q (t e : S) (b : K9.Part) (front : ℕ) (Fe : Fork) (tl tl' : HTailF2) (funs : Array HFun)
      (F1 : Fork) (c : List Claim), atS.get? t = some b → e.fork? = some Fe → e.tl? = some tl →
      equations (Fe.nClaim + front) tl funs Fe = .ok (tl', F1, c) → Fx9 φ Ok q e → Fx9 φ Ok q t →
      laterK atS (O9 (K := GE8) φ Ok Fu) ((e.putTl tl').putFork F1) t →
      Sized b.F ∧ ∀ kc ∈ c.take 4, ∀ s ∈ kc.form.slots.toList, Filled b.F s.1 := by
  intro q t e b front Fe tl tl' funs F1 c hb hFe htl he fxe fxt hlat
  obtain ⟨hok, hφ, v, a0, hv, ha0, gv⟩ := fxe
  obtain ⟨a₁, ha₁, f1, _, _, _, _, hF'⟩ := get_put e a0 ha0 tl' F1
  obtain rfl : Fe = a0.F := Option.some.inj (hFe.symm.trans hF')
  obtain ⟨g, Fa, hg, h4, hrun, hF1⟩ := take_four he
  obtain ⟨b', hb', gb⟩ := hlat.2.1.2 a₁ ha₁
  obtain rfl : b' = b := Option.some.inj (hb'.symm.trans hb)
  have hq1 : (π q.1).1 = some (blank u tl) := by
    rw [← hφ, hπ, htl]
    rfl
  obtain ⟨hsz, hslots⟩ := hOk4 q v (blank u tl) g hok hv hq1 hg
  rw [four8_blank] at hslots
  have hsa : Sized a0.F := gv.1.sized hsz
  have hlb : Later F1 b'.F := by
    have := gb.1
    rwa [show (pubOf a₁).F = F1 from f1] at this
  have hFaB : Later Fa b'.F :=
    (by rw [hF1]; exact paid_later Fa g.owedPlanes : Later Fa F1).trans hlb
  obtain ⟨_, _, hin, _⟩ := hideRun_ok _ Fa g.leaves.first _ _
    ((paid_later a0.F g.owedJoin).sized hsa) hrun
  obtain ⟨_, _, v', b2, hv', hb2, gv'⟩ := fxt
  obtain rfl : v' = v := Option.some.inj (hv'.symm.trans hv)
  obtain rfl : b2 = b' := Option.some.inj (hb2.symm.trans hb)
  refine ⟨gv'.1.sized hsz, fun kc hkc s hs => ?_⟩
  rw [h4] at hkc
  rcases hslots kc hkc s hs with hw | hf
  · obtain ⟨w1, w2⟩ := hw
    have w1' : g.leaves.first ≤ s.1 := w1
    have w2' : s.1 < g.leaves.first + g.leaves.walk.1.length := w2
    have h5 := (hin (s.1 - g.leaves.first) (by simp; omega)).2.2.1
    rw [show g.leaves.first + (s.1 - g.leaves.first) = s.1 by omega] at h5
    exact (hFaB.keep _ h5).1
  · exact (gv'.1.keep _ hf).1

variable {β : Type}

/-- hOk4 from the core of every sort's Ok. -/
theorem okFour_of_core {Ok : Q β → Prop} {nU : Array ℕ} {tlD : HTailF2}
    (hc : ∀ q, Ok q → OkCore nU tlD q) :
    ∀ q v tlb g, Ok q → q.2 = some v → (pi8 q.1).1 = some tlb → tlb.heard = some g →
      Sized v.F ∧ ∀ cl ∈ four8 tlb g, ∀ x ∈ cl.form.slots.toList,
        K4Values.InWin (winOf g.leaves) x.1 ∨ Filled v.F x.1 :=
  fun q v tlb g hq hv ht hg => (hc q hq).four v tlb g hv ht hg

/-- **LeftRest's FIELD slots, at every fixed part.** -/
theorem slots_at_phiAll (u : HTailF2) (ψ : S → β) (Ok : Q β → Prop) (nU : Array ℕ)
    (tlD : HTailF2) (rows : ℕ) (hc : ∀ q, Ok q → OkCore nU tlD q) :
    ∀ q (t e : S) (b : K9.Part) (front : ℕ) (Fe : Fork) (tl tl' : HTailF2) (funs : Array HFun)
      (F1 : Fork) (c : List Claim), atS.get? t = some b → e.fork? = some Fe → e.tl? = some tl →
      equations (Fe.nClaim + front) tl funs Fe = .ok (tl', F1, c) →
      Fx9 (phiAll u ψ) (fun q => Ok q ∧ (rowsFit rows pi8) q) q e →
      Fx9 (phiAll u ψ) (fun q => Ok q ∧ (rowsFit rows pi8) q) q t →
      laterK atS (O9 (K := GE8) (phiAll u ψ) (fun q => Ok q ∧ (rowsFit rows pi8) q) (FullAt nU))
        ((e.putTl tl').putFork F1) t →
      Sized b.F ∧ ∀ kc ∈ c.take 4, ∀ s ∈ kc.form.slots.toList, Filled b.F s.1 :=
  slots_of_four (phiAll u ψ) _ (FullAt nU) u pi8 (fun _ => rfl)
    (okFour_of_core fun q hq => hc q hq.1)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.slots_of_four
#print axioms VerifiableInference.Desc.LinkJoin.okFour_of_core
#print axioms VerifiableInference.Desc.LinkJoin.slots_at_phiAll
