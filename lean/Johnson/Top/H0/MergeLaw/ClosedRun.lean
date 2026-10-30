-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/ClosedRun.lean: from the merge's yes and the yes of its run of claims to the
claim on the weights, at the closed caller. Theorems with their proofs.

`ClosedSays` (Johnson/Top/H0/MergeLaw/Closed.lean) asks for a world that fits the entries (p2) in
which the row form at the sent end value is worth 0 (p3). Here both are said of texts that run: the
world is the world of a ledger (`Fork.worldOf`) that is later than the ledger which the kind's own
run of claims, `headMergeClaim`, leaves; the form is the one claim that this run hands on.

Main names:
  `filled_of_public`: where the ledger has a public part of one claim's start form, the slot of that
    claim's value is filled.
  `closed_run`: under `FrontIs`, `ClosedSays` and "the front ledger's three arrays have one entry
  for
    each slot": there are the values heard; and at every later record of the head's link that still
    holds what the merge left, whose ledger is later than the merge's, at which the run says yes,
    and for every ledger Fl later than the run's: the run hands on one claim; and if what rides
    holds, that claim's form is worth 0 in the world of Fl at the entries' mask row, and the row on
    the end value holds, then the claim on the weights holds.

How. The run lays 0 and -1 under the 2 lk + 2 slots of the hiding polynomial's coefficients, the
first of the sumcheck's own 2 lk + 3 (the last, the end value's, the hearing has filled)
(`claim_inv`; `OnBytes.PscRun.hideRun_ok`); what lies under a filled slot stays
(`OnBytes.PscRun.Later`); so `K11Caller.world_at` gives `Fits2`. The shown end value is the sent
one (`fvp_sized`).

WHAT STAYS A PREMISE, ONE BY ONE: (p1) Rd · (p3') the run's claim is worth 0 in that world: the
batching's to pay · (p4) the row on the end value · (p5) `FrontIs` · (p7) one claim; the column bits
·
(p9) the front ledger's arrays have their size · (p10) between the merge and its run the ledger only
grows later (`Later`) and what the merge left stays in the record: the blocks' and runs' between ·
(p11) the last ledger is later than the run's.
BESIDE THESE: `ClosedSays` itself is a premise of `closed_run`, and no theorem here joins
`merge_closed` to `closed_run`; that the run of claims says yes at all is a premise too; Pl and N
are letters, as in Closed.lean.

Limits. Statements on two records, no game: the game is in Closed.lean. It is no soundness of the
protocol. Nothing on hiding.

-/
import Johnson.Top.H0.MergeLaw.Closed
import Johnson.Top.H0.MergeLaw.Keeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open Iop IOR Cb Cb.Pv.Lay Johnson.L5.Layers TWhole
open OnBytes (E zeroE oneE subE)
open OnBytes.Flat OnBytes.Maker OnBytes.Slice
open OnBytes.Model (Reading World Fork wsForkStart)
open OnBytes.PscRun (Later Filled)
open VerifiableInference.Desc (Claim)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeClaim)
open OnBytes.Tie.Pv.Lay.Eng (sumOut)
open K11Caller (MergeIn GS Fits2 maskOf world_at)

theorem getD_replicate_zero (n i : ℕ) : (Array.replicate n zeroE).getD i zeroE = zeroE := by
  by_cases h : i < n <;> simp [Array.getD, h]

/-- Where the ledger has a public part of the start form of one claim, the slot of that claim's
value is filled. -/
theorem filled_of_public {F : Fork} {j : ℕ} {x T : E}
    (h : F.publicPart (wsForkStart #[j] (OnBytes.Model.powers x 1)) = some T) : Filled F j := by
  have h2 : ∃ y, F.shown j = some y := by
    cases hs : F.shown j with
    | some y => exact ⟨y, rfl⟩
    | none =>
      simp [Fork.publicPart, wsForkStart, OnBytes.Model.powers, OnBytes.Model.powersLoop,
          OnBytes.Model.Aff.addMul,
        OnBytes.Model.Aff.slot, hs] at h
  obtain ⟨y, hy⟩ := h2
  exact ((OnBytes.PscRun.shown_iff F j y).1 hy).2.1

variable {Pl : K11Caller.Place} (N : K11Caller.Nums Pl)
  (Rd : MergeIn Pl.n → (Pl.Cell ⊕ (Fin N.ns ⊕ Fin N.ni) → GE) → Prop)

/-- **From the merge's yes and its run's yes to the claim on the weights**: the world is the world
of any ledger later than the run's. -/
theorem closed_run (P : HeadMergeP) (hlk : Pl.lay.lk = P.lay.lk) (h1 : Pl.n = 1)
    (m : Pl.Cell ⊕ (Fin N.ns ⊕ Fin N.ni) → GE) (st : MergeIn Pl.n) {s s' : S}
    (hfr : FrontIs N st s) (hC : ClosedSays N Rd P m st s s')
    (hz : ∀ a, s.here = .head a → OnBytes.PscRun.Sized a.F) :
    ∃ (a' : HeadOwn) (wo : OnBytes.Model.WsForkOut) (x mu cY beta v : E) (qs : List (Nat × List E ×
        E))
      (hβ : Reading.gl.val beta ≠ 0),
      s'.here = .head a' ∧ a'.wo = some wo ∧ wo.beta = beta ∧ wo.rm.toList = qs.map (·.2.2) ∧
      ∀ (n : ℕ) (s₂ s₃ : S) (a₂ a₃ : HeadOwn) (cls : List Claim) (Fl : Fork) (entry : ℕ → ℕ → ℕ →
          GE),
        s₂.here = .head a₂ → a₂.wo = a'.wo → Later a'.F a₂.F → headMergeClaim n s₂ = .ok (cls, s₃) →
        s₃.here = .head a₃ → Later a₃.F Fl →
        ∃ form, cls = [{ form := form }] ∧
          (Rd st m → form.value Reading.gl (Fl.worldOf Reading.gl (maskOf N m) entry) = 0 →
            (GS Reading.gl N Rd).L.f (st, Reading.gl.val x) m ((GS Reading.gl N Rd).L.toSum.Q.outPt
                (GS Reading.gl N Rd).L.toSum.M
                (sumOut Reading.gl (GS Reading.gl N Rd).L.toSum (fun st => pick ((GS Reading.gl N
                    Rd).L.toSum.T.par.vars st)) (st, Reading.gl.val x) wo.p.target mu
                  wo.p.eps (qs.map fun q => (q.2.1, q.2.2)) [cY] beta hβ fun _ => Reading.gl.val v))
                      =
              Reading.gl.val v - m (GS Reading.gl N Rd).L.cAt * Reading.gl.val beta →
            ∀ c, (GS Reading.gl N Rd).Cl st m c) := by
  obtain ⟨a, a', claim, x0, wo, x, mu, cY, beta, v, T, qs, hβ, e1, e2, e3, e4, e5, e6, e7, e8,
      hfirst, hstart, hlen, hrm, hrecs,
    ⟨Gf, hhide, hshown, hF'⟩, himp⟩ := hC
  obtain ⟨fF, _, fsv, ffirst⟩ := hfr a claim x0 e1 e3 e4
  have hza := hz a e1
  refine ⟨a', wo, x, mu, cY, beta, v, qs, hβ, e2, e5, e8, hrm, ?_⟩
  intro n s₂ s₃ a₂ a₃ cls Fl entry h₂ hwo hl12 hrun h₃ hl3
  obtain ⟨b, wo₂, G, hb, hbwo, hs3, hcls, hrunF⟩ := claim_inv hrun
  have hab : b = a₂ := by
    rw [h₂] at hb
    exact (Here.head.inj hb).symm
  subst hab
  have hw2 : wo₂ = wo := by
    rw [hwo, e5] at hbwo
    exact (Option.some.inj hbwo).symm
  subst hw2
  have hG : a₃.F = G := by
    rw [hs3] at h₃
    rw [← Here.head.inj h₃]
  rw [hG] at hl3
  have L01 : Later a.F a'.F := by
    rw [hF']
    have k1 : Later a.F { a.F with next := a.F.next + 1 + 2 * P.lay.lk + 2 } :=
      ⟨by show a.F.next ≤ a.F.next + 1 + 2 * P.lay.lk + 2; omega, rfl, id, fun _ h => ⟨h, rfl, rfl⟩⟩
    exact (k1.trans (OnBytes.PscRun.hideRun_keeps hhide)).trans ⟨Nat.le_refl _, rfl, id, fun _ h =>
        ⟨h, rfl, rfl⟩⟩
  have L02 : Later a.F b.F := L01.trans hl12
  obtain ⟨_, _, r3, _⟩ := OnBytes.PscRun.hideRun_ok b.F G _ _ _ (L02.sized hza) hrunF
  have own : ∀ j, N.first ≤ j → j < N.first + 2 * Pl.lay.lk + 2 →
      Fl.vp.getD j zeroE = zeroE ∧ Fl.mf.getD j zeroE = subE zeroE oneE := by
    intro j j1 j2
    have hi : j - N.first < (Array.replicate wo₂.p.walk.1.length zeroE).size := by
      rw [Array.size_replicate, hlen, ← hlk]
      omega
    obtain ⟨_, _, q3, q4, q5⟩ := r3 (j - N.first) hi
    have ej : wo₂.p.first + (j - N.first) = j := by
      rw [hfirst, ← ffirst]
      omega
    rw [ej] at q3 q4 q5
    obtain ⟨_, k2, k3⟩ := hl3.keep j q3
    exact ⟨by rw [k2, q4, getD_replicate_zero], by rw [k3, q5]⟩
  have hsv : ∀ i : Fin Pl.n, N.sv i = x0.sV := by
    intro i
    have e : N.svA.getD i.val 0 = N.sv i := by simp [K11Caller.Nums.svA, Array.getD, i.isLt]
    have i0 : i.val = 0 := by have := i.isLt; omega
    rw [← e, fsv, i0]
    rfl
  have kept : ∀ i, Fl.vp.getD (N.sv i) zeroE = st.F.vp.getD (N.sv i) zeroE ∧
      Fl.mf.getD (N.sv i) zeroE = st.F.mf.getD (N.sv i) zeroE := by
    intro i
    rw [hsv i, fF]
    obtain ⟨_, k2, k3⟩ := ((L02.trans (OnBytes.PscRun.hideRun_keeps hrunF)).trans hl3).keep x0.sV
        (filled_of_public e6)
    exact ⟨k2, k3⟩
  have hfv : wo₂.fvp = v := fvp_sized hhide hshown ⟨hza.1, hza.2.1, hza.2.2⟩
  refine ⟨_, hcls, ?_⟩
  intro hRd hval hev
  rw [hfv] at hval
  exact himp hRd ⟨_, world_at Reading.gl N st m Fl entry own kept, hval⟩ hev

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.closed_run
