-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/Says.lean: what the merge's claim says, at the head's link. Theorems with
their
proofs.

Main names:
  `decide_inv`: what the decision's yes holds: the tape; what `mergeHear` returned; how the head's
    ledger, its next free slot and the ledger in front are laid.
  `fvp_sized`: the shown end value is the sent one, where the ledger's three arrays on slots have
  its
    number of slots (OnBytes.Model.Road.Sized).
  `claim_says`: where the decision says yes, then at any later record whose head's part keeps what
    the merge left, the form of the claim that the run hands on is worth 0 in a world exactly if
    the typed row claim holds of the typed output.

The library's `Sized` (OnBytes/Tie/Pv/Psc/Run/PscHide.lean) is spent: a statement on a plain record.

Limits. `claim_says` has four premises: `Sized` of the ledger in front; the last challenge reads
other than 0; (D1) and (D2) of Johnson/Top/H0/MergeLaw/Said.lean. None is paid here. That other
blocks' runs keep what the merge left is not said. No typed record has been made here from a plan.
Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Top.H0.MergeLaw.Said
import Johnson.Top.H0.MergeLaw.Run
import Johnson.Top.H0.MergeLaw.Ledger

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open Iop Cb Cb.Pv.Lay
open OnBytes (E addE mulE zeroE)
open OnBytes.K.Kc (Tape flatOf)
open OnBytes.Psc (Weight)
open OnBytes.Model (Reading World Fork wsForkStart)
open OnBytes.Model.Road (Sized)
open OnBytes.Tie.Pv.Lay.Eng (SumSaid sumOut)
open VerifiableInference.Desc (Claim need named)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide headMergeClaim mergeTapeE mergeHear
    mergeEntries)

/-- What the decision's yes holds. -/
theorem decide_inv {P : HeadMergeP} {s s' : S} {rs : List Fmt.RoundView} (h : headMergeDecide P s rs = .ok
           s') :
    ∃ a a' tp F claim x wo, s.here = .head a ∧ s'.here = .head a' ∧ a.claim = some claim ∧ a.x =
        some x ∧
      a'.wo = some wo ∧ mergeTapeE rs (mergeEntries P.lay.lk 1 P.work) = .ok tp ∧
      mergeHear P.lay #[claim] #[x.sV] a.F tp = .ok (wo, F, []) ∧
      a'.F = { F with planClaimsF := P.nLin } ∧ a'.slot = some F.next ∧ a'.Fm = a.F ∧ F.next =
          P.nMsg := by
  cases hh : s.here with
  | head a =>
    by_cases ho : a.opened = true
    · by_cases hw : s.noneWaits = true
      · cases ht : mergeTapeE rs (mergeEntries P.lay.lk 1 P.work) with
        | error e => simp [headMergeDecide, hh, ho, hw, ht, need, bind, Except.bind] at h
        | ok t =>
          cases hcl : a.claim with
          | none => simp [headMergeDecide, hh, ho, hw, ht, hcl, need, named, bind, Except.bind] at h
          | some claim =>
          cases hx : a.x with
          | none => simp [headMergeDecide, hh, ho, hw, ht, hcl, hx, need, named, bind, Except.bind]
                at h
          | some x =>
          cases hm : mergeHear P.lay #[claim] #[x.sV] a.F t with
          | error e => simp [headMergeDecide, hh, ho, hw, ht, hcl, hx, hm, need, named, bind,
                Except.bind] at h
          | ok r =>
            obtain ⟨wo, F, t'⟩ := r
            by_cases he : t'.isEmpty = true
            · by_cases hc : (F.next == P.nMsg) = true
              · simp [headMergeDecide, hh, ho, hw, ht, hcl, hx, hm, he, hc, need, named, bind,
                    Except.bind, pure,
                  Except.pure] at h
                subst h
                have ht' : t' = [] := List.isEmpty_iff.1 he
                subst ht'
                exact ⟨a, _, t, F, claim, x, wo, rfl, rfl, hcl, hx, rfl, rfl, hm, rfl, rfl, rfl, by
                    simpa using hc⟩
              · simp [headMergeDecide, hh, ho, hw, ht, hcl, hx, hm, he, hc, need, named, bind,
                    Except.bind] at h
            · simp [headMergeDecide, hh, ho, hw, ht, hcl, hx, hm, he, need, named, bind,
                  Except.bind] at h
      · simp [headMergeDecide, hh, ho, hw, need, bind, Except.bind] at h
    · simp [headMergeDecide, hh, ho, need, bind, Except.bind] at h
  | _ => simp [headMergeDecide, hh] at h

/-- Where the ledger's three arrays on slots have its number of slots (`Sized`), the shown end value
is the sent one. -/
theorem fvp_sized {F G : Fork} {n j : Nat} {v b w : E} (h4 : ({ F with next := n } : Fork).hideRun j
    #[v] b = some G)
    (h5 : G.shown j = some w) (hz : Sized F) : w = v := by
  have hj : j < F.vp.size := by
    have := (hide_inv (hideRun_one h4)).1
    rw [hz.vp]
    exact this
  have h := shown_hideRun_one h4 hj
  rw [h5] at h
  exact Option.some.inj h

variable {K : Type} [Field K] [Fintype K] (ρ : Reading K)

/-- **What the merge's claim says**: see the head. -/
theorem claim_says (P : HeadMergeP) (L : MergeL K) (hk : L.k = P.lay.lk) {s s' : S} {rs : List
    Fmt.RoundView}
    (h : headMergeDecide P s rs = .ok s') (st : L.St) :
    ∃ (a a' : HeadOwn) (wo : OnBytes.Model.WsForkOut) (mu c beta v : E) (qs : List (Nat × List E ×
        E)),
      s.here = .head a ∧ s'.here = .head a' ∧ a'.wo = some wo ∧ wo.beta = beta ∧
      ∀ (_ : Sized a.F) (hβ : ρ.val beta ≠ 0) (n : Nat) (s₂ s₃ : S) (a₂ : HeadOwn) (cls : List
          Claim),
        s₂.here = .head a₂ → a₂.wo = a'.wo → headMergeClaim n s₂ = .ok (cls, s₃) →
        ∃ form, cls = [{ form := form }] ∧
          ∀ (Ex : ExtSpec) (_ : Ex.Str) (W : World K) (m : L.J → K),
            L.toSum.T.par.W st m = OnBytes.Road.Hd.place W.slot (L.toSum.T.par.vars st) wo.p.first →
            L.toSum.T.par.inc st m = ρ.val wo.p.target - wo.p.start.value ρ W →
            (form.value ρ W = 0 ↔
              L.toSum.T.par.UHolds (sumOut ρ L.toSum (fun st => pick (L.toSum.T.par.vars st)) st
                wo.p.target mu wo.p.eps (qs.map fun q => (q.2.1, q.2.2)) [c] beta hβ fun _ => ρ.val
                    v) m) := by
  obtain ⟨a, a', tp, G, claim, x0, wo, ha, ha', _, _, hwo', _, hm, _⟩ := decide_inv h
  obtain ⟨x, mu, c, beta, v, T, r1, rY, rV, qs, _, _, _, _, hbeta, hhide, hshown, H⟩ := hear_tie ρ L
      hk hm st
  refine ⟨a, a', wo, mu, c, beta, v, qs, ha, ha', hwo', hbeta, ?_⟩
  intro hz hβ n s₂ s₃ a₂ cls h₂ hwo hrun
  obtain ⟨b, wo₂, _, hb, hbwo, _, hcls, _⟩ := claim_inv hrun
  have hab : b = a₂ := by
    rw [h₂] at hb
    exact (Here.head.inj hb).symm
  subst hab
  have hfv : wo.fvp = v := fvp_sized hhide hshown hz
  have hw2 : wo₂ = wo := by
    rw [hwo, hwo'] at hbwo
    exact (Option.some.inj hbwo).symm
  refine ⟨_, hcls, ?_⟩
  rw [hw2, hfv]
  exact (H hβ).2.1

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.claim_says
