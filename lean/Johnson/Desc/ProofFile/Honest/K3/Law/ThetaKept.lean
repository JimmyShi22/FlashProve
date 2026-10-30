-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/ThetaKept.lean: what the lookup's three runs of claims do to
the open ledger: they mark a debt as paid, and "planes" lays one run of hidden values before that.
So every property of a ledger that passes these two steps is handed on by an accepting call of each
run; among them "the batching element is θ". Then, under the library's hypothesis `P5J.AtMgA`, that
sentence at the nine entries of a link's order that name a run of the lookup's. Theorems.

Terms. Honest/K3/GLOSSARY.md ("ledger", "run (of claims)", "seat", "`P5J.AtMgA`"). In this file: "a
ledger is open and has P" is `HasFork P` (Johnson/Desc/First/Link/Law/SizedRides.lean). To mark a
debt as paid is `Fork.paid`; to lay a run of hidden values is `Fork.hideRun` (both in
OnBytes/Model/Hide.lean).

What is shown.
  `fork_kept_objects`, `fork_kept_join`, `fork_kept_planes`: for every seat (at the first chain's
    state), all keys and readers of the caller, and every property P: `HasFork P` is handed on.
  `theta_kept_objects`, `theta_kept_join`, `theta_kept_planes`: the same at P := the batching
    element is θ. There `hp` and `hh` are shown.
  `theta_at_layers`: at a feed-forward link: (1, "objects"), (6, "objects").
  `theta_at_attention`: at an attention link: (1, "objects"), (2, "join"), (1, "planes"),
    (6, "objects").
  `theta_at_head`: at the head's link: (2, "objects"), (2, "planes"), (7, "objects").
The last three end in one form: for every θ, every entry o of the list and every run that the link
states at o (`LinkJoin.At`), an accepting call hands on `HasFork (fun G => G.theta = θ)`. It is
written out over the library's own names. One of the nine is read off another kind's member:
(2, "join") at an attention link stands at the calling kind's sub-protocol; the run there is the
lookup's own `joinRun` at that kind's keys (`at_join_is`).

Hypotheses that remain.
  In the first three theorems:
  `hA`: the seat reads and writes the state's own ledger (`AtS2`, Johnson/Top/H/Keep/RunsAtS.lean).
  `h`: the run returns.
  `hp`: P passes the mark of a debt.
  `hh`: (at "planes" alone) P passes a run of hidden values laid.
  In the middle three (`theta_kept_objects`, `theta_kept_join`, `theta_kept_planes`): `hA` and `h`,
  as in the first three; `hp` and `hh` are shown there.
  In the last three:
  `h`: the library's hypothesis `P5J.AtMgA`.
  `hg`, `hL`: the link's number, and that L is the chain's link there.

How the proof goes. The proofs call the library's `objects_cut`, `join_heard`, `planes_heard`,
`planes_fills` (Johnson/Top/H/Keep/K3Inv.lean), `joinRun_cut` (Johnson/Top/H/K3RunsLaw.lean),
`paid_core`, `hideRun_core` (Johnson/Desc/First/K4/RunsCore.lean), `at_objects_is`
(Johnson/Desc/First/Link/Law/SortK3Objects.lean), `at_join_is`
(Johnson/Desc/First/Link/Law/SortK3Join.lean), `at_planes_is`
(Johnson/Desc/First/Link/Law/SortK3Planes.lean), `readersAt_att`, `scope_all`
(Johnson/Desc/First/Att/Door/Law/K5RestOpen.lean), `P4.readers_head`, `P4.head_24`
(Johnson/P4SR/PlanesAtSeat.lean), `P4.k6Back_at_seat` (Johnson/P4SR/K6BackAtSeat.lean). The
library's own `k3s_objects`, `k3s_join`, `k3s_planes` (one in each of the three files
SortK3Objects.lean, SortK3Join.lean, SortK3Planes.lean) are their pattern.

Users. Honest/K3/Law/ForkKeptAt.lean imports this file and calls the first three theorems.

Limits. Whether a run returns is not spoken of. Nothing is said on the other fields of the ledger.
The last three hold at the full size alone: that limit comes with `P5J.AtMgA`. No instance of these
hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.First.Link.Law.SortK3Objects
import Johnson.Desc.First.Link.Law.SortK3Join
import Johnson.Desc.First.Link.Law.SortK3Planes
import Johnson.Desc.First.Att.Door.Law.K5RestOpen
import Johnson.Desc.First.K4.RunsCore
import Johnson.P4SR.PlanesAtSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Law
open OnBytes (E)
open OnBytes.Model (Fork Aff)
open OnBytes.Desc.First.K4 (paid_core hideRun_core)
open VerifiableInference.Desc (Chain Link Claim)
open VerifiableInference.Desc.K3 (Seat Readers planesRun joinRun seatCalls)
open VerifiableInference.Desc.LinkJoin (At HasFork at_join_is)
open VerifiableInference.OnPublicFiles (AtS2 objectsRun seatOf objects_cut join_heard planes_heard
        planes_fills joinRun_cut at_objects_is at_planes_is atS2_seatOf k03_atS2_calls objects_entry_low
        objects_entry_head planes_entry_low planes_entry_head)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

local notation "FS" => VerifiableInference.Desc.First.S

/-! ## 1 For every seat and every property -/

section
variable (seat : Seat FS Claim) (hA : AtS2 seat) {P : Fork → Prop}
  (hp : ∀ (F : Fork) (i : Nat), P F → P (F.paid i))
include hA hp

/-- **"objects" hands on "a ledger is open and has P".** -/
theorem fork_kept_objects (n : Nat) (e : FS) (c : List Claim) (e₁ : FS)
    (h : objectsRun seat n e = .ok (c, e₁)) : HasFork P e → HasFork P e₁ := by
  rintro ⟨G₀, hF, hP⟩
  obtain ⟨F, g, e1, _, rfl⟩ := objects_cut seat h
  obtain rfl : G₀ = F := Option.some.inj (hF.symm.trans ((hA.fork e).symm.trans e1))
  rw [hA.mark]
  exact ⟨_, VerifiableInference.Desc.LinkJoin.fork_putFork e G₀ hF _, hp _ _ hP⟩

/-- **"join" hands it on**, at every caller's keys. -/
theorem fork_kept_join (keys : FS → Option (Array Aff)) (n : Nat) (e : FS) (c : List Claim)
    (e₁ : FS) (h : joinRun seat keys n e = .ok (c, e₁)) : HasFork P e → HasFork P e₁ := by
  rintro ⟨G₀, hF, hP⟩
  obtain ⟨F, g, e1, e2⟩ := join_heard seat keys h
  obtain rfl : G₀ = F := Option.some.inj (hF.symm.trans ((hA.fork e).symm.trans e1))
  obtain ⟨_, _, _, _, rfl⟩ := joinRun_cut seat keys e1 e2 h
  rw [hA.mark]
  exact ⟨_, VerifiableInference.Desc.LinkJoin.fork_putFork e G₀ hF _, hp _ _ hP⟩

/-- **"planes" hands it on**, at every caller's readers. -/
theorem fork_kept_planes
    (hh : ∀ (F G : Fork) (first : Nat) (v : Array E) (k : E), F.hideRun first v k = some G →
      P F → P G)
    (lm : Nat) (readers : Readers FS) (n : Nat) (e : FS) (c : List Claim) (e₁ : FS)
    (h : planesRun seat lm readers n e = .ok (c, e₁)) : HasFork P e → HasFork P e₁ := by
  rintro ⟨G₀, hF, hP⟩
  obtain ⟨F, g, e1, e2⟩ := planes_heard seat lm readers h
  obtain rfl : G₀ = F := Option.some.inj (hF.symm.trans ((hA.fork e).symm.trans e1))
  obtain ⟨G, hG, rfl⟩ := planes_fills seat lm readers e1 e2 h
  rw [hA.mark]
  exact ⟨_, VerifiableInference.Desc.LinkJoin.fork_putFork e G₀ hF _,
    hp _ _ (hh _ _ _ _ _ hG hP)⟩

end

/-! ## 2 The batching element -/

section
variable (seat : Seat FS Claim) (hA : AtS2 seat) (θ : E)
include hA

/-- **"objects" hands on "a ledger is open and its batching element is θ".** Conditional on the seat
reading and writing the state's own ledger (`AtS2`) and on the run's return. -/
theorem theta_kept_objects (n : Nat) (e : FS) (c : List Claim) (e₁ : FS)
    (h : objectsRun seat n e = .ok (c, e₁)) :
    HasFork (fun G => G.theta = θ) e → HasFork (fun G => G.theta = θ) e₁ :=
  fork_kept_objects seat hA (fun F i hF => (paid_core F i).theta.trans hF) n e c e₁ h

/-- **"join" hands it on**, at every caller's keys. Conditional on the same. -/
theorem theta_kept_join (keys : FS → Option (Array Aff)) (n : Nat) (e : FS) (c : List Claim)
    (e₁ : FS) (h : joinRun seat keys n e = .ok (c, e₁)) :
    HasFork (fun G => G.theta = θ) e → HasFork (fun G => G.theta = θ) e₁ :=
  fork_kept_join seat hA (fun F i hF => (paid_core F i).theta.trans hF) keys n e c e₁ h

/-- **"planes" hands it on**, at every caller's readers. Conditional on the same. -/
theorem theta_kept_planes (lm : Nat) (readers : Readers FS) (n : Nat) (e : FS) (c : List Claim)
    (e₁ : FS) (h : planesRun seat lm readers n e = .ok (c, e₁)) :
    HasFork (fun G => G.theta = θ) e → HasFork (fun G => G.theta = θ) e₁ :=
  fork_kept_planes seat hA (fun F i hF => (paid_core F i).theta.trans hF)
    (fun _ _ _ _ _ hr hF => (hideRun_core hr).theta.trans hF) lm readers n e c e₁ h

end

/-! ## 3 At the nine entries, under `P5J.AtMgA` -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **At a feed-forward link.** Conditional on `P5J.AtMgA`, g < 12 and the chain's link. No instance
of these hypotheses is exhibited in this file. -/
theorem theta_at_layers (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (g : Nat) (hg : g < 12)
    {L : Link FS Claim} (hL : cF.links[2 * g]? = some L) :
    ∀ θ : E, ∀ o ∈ [((1 : Nat), "objects"), (6, "objects")], ∀ run, At L o run →
      ∀ n e c e₁, run n e = .ok (c, e₁) →
        HasFork (fun G => G.theta = θ) e → HasFork (fun G => G.theta = θ) e₁ := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  intro θ o ho run hr n e c e₁ hy
  obtain ⟨d, rfl⟩ := objects_entry_low (m := 2 * g) (by omega) (by simpa using ho)
  rw [at_objects_is h.scope h.reads O (by omega) d hL hr] at hy
  exact theta_kept_objects _ (atS2_seatOf d) θ n e c e₁ hy

/-- **At an attention link.** Conditional on `P5J.AtMgA`, g < 12 and the chain's link. No instance
of these hypotheses is exhibited in this file. -/
theorem theta_at_attention (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (g : Nat) (hg : g < 12)
    {L : Link FS Claim} (hL : cF.links[2 * g + 1]? = some L) :
    ∀ θ : E, ∀ o ∈ [((1 : Nat), "objects"), (2, "join"), (1, "planes"), (6, "objects")],
      ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c, e₁) →
        HasFork (fun G => G.theta = θ) e → HasFork (fun G => G.theta = θ) e₁ := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨p4, ng, hAll⟩ := H2K5.Door.scope_all h
  obtain ⟨a, ha⟩ := hAll g hg
  have p4' : Bs.G₀.W.p4 = true := by
    rw [O.W]
    exact p4
  have ng' : g < Bs.G₀.W.NGr := by
    rw [O.W]
    have e12 : Zp.p.X.NGr = 12 := ng
    omega
  have ha' : Bs.G₀.W.A[g]? = some a := by
    rw [O.W]
    exact ha
  intro θ o ho run hr n e c e₁ hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl
  · obtain ⟨d, ed⟩ := objects_entry_low (m := 2 * g + 1) (by omega) (Or.inl rfl)
    rw [ed] at hr
    rw [at_objects_is h.scope h.reads O (by omega) d hL hr] at hy
    exact theta_kept_objects _ (atS2_seatOf d) θ n e c e₁ hy
  · rw [at_join_is O p4' ng' ha' hL hr] at hy
    exact theta_kept_join _ k03_atS2_calls θ _ n e c e₁ hy
  · rw [planes_entry_low (m := 2 * g + 1) (by omega)] at hr
    obtain ⟨p, _, rfl⟩ := at_planes_is h.scope h.reads O (by omega) hL
      (H2K5.Door.readersAt_att p4' ha') hr
    exact theta_kept_planes _ k03_atS2_calls θ _ _ n e c e₁ hy
  · obtain ⟨d, ed⟩ := objects_entry_low (m := 2 * g + 1) (by omega) (Or.inr rfl)
    rw [ed] at hr
    rw [at_objects_is h.scope h.reads O (by omega) d hL hr] at hy
    exact theta_kept_objects _ (atS2_seatOf d) θ n e c e₁ hy

/-- **At the head's link.** Conditional on `P5J.AtMgA` and the chain's link. No instance of these
hypotheses is exhibited in this file. -/
theorem theta_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {L : Link FS Claim}
    (hL : cF.links[24]? = some L) :
    ∀ θ : E, ∀ o ∈ [((2 : Nat), "objects"), (2, "planes"), (7, "objects")], ∀ run, At L o run →
      ∀ n e c e₁, run n e = .ok (c, e₁) →
        HasFork (fun G => G.theta = θ) e → HasFork (fun G => G.theta = θ) e₁ := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨_, iU3, _, hU, _, _⟩ := P4.k6Back_at_seat h.scope h.reads O
  intro θ o ho run hr n e c e₁ hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl
  · obtain ⟨d, ed⟩ := objects_entry_head (Or.inl rfl)
    rw [ed] at hr
    rw [at_objects_is h.scope h.reads O (by omega) d hL hr] at hy
    exact theta_kept_objects _ (atS2_seatOf d) θ n e c e₁ hy
  · rw [planes_entry_head] at hr
    obtain ⟨p, _, rfl⟩ := at_planes_is h.scope h.reads O (by omega) hL
      (P4.readers_head (P4.head_24 h.scope h.reads O) hU) hr
    exact theta_kept_planes _ k03_atS2_calls θ _ _ n e c e₁ hy
  · obtain ⟨d, ed⟩ := objects_entry_head (Or.inr rfl)
    rw [ed] at hr
    rw [at_objects_is h.scope h.reads O (by omega) d hL hr] at hy
    exact theta_kept_objects _ (atS2_seatOf d) θ n e c e₁ hy

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.fork_kept_objects
#print axioms ProofFile.Honest.K3.Law.fork_kept_join
#print axioms ProofFile.Honest.K3.Law.fork_kept_planes
#print axioms ProofFile.Honest.K3.Law.theta_kept_objects
#print axioms ProofFile.Honest.K3.Law.theta_kept_join
#print axioms ProofFile.Honest.K3.Law.theta_kept_planes
#print axioms ProofFile.Honest.K3.Law.theta_at_layers
#print axioms ProofFile.Honest.K3.Law.theta_at_attention
#print axioms ProofFile.Honest.K3.Law.theta_at_head
