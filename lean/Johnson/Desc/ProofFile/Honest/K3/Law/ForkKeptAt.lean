-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/ForkKeptAt.lean: under the library's hypothesis `P5J.AtMgA`, at
the nine entries of a link's order that name a run of the lookup's: "a ledger is open and has P"
(`HasFork P`) is handed on by an accepting call, for every property P of a ledger that passes the
mark of a debt (`hp`) and, at the links that state "planes", a run of hidden values laid (`hh`).
Then at P := "later than U". Theorems. The counterpart of Honest/K3/Law/ThetaKept.lean, whose last
three theorems are these at P := "the batching element is θ".

Terms. Honest/K3/GLOSSARY.md ("ledger", "run (of claims)", "`P5J.AtMgA`"); for `HasFork`, the mark
of a debt and a run of hidden values laid, the head of ThetaKept.lean. "Later than U" is
`PscRun.Later U G` (OnBytes/Tie/Pv/Psc/PscLater.lean).

What is shown.
  `fork_at_layers`: at a feed-forward link: (1, "objects"), (6, "objects"); under `hp`.
  `fork_at_attention`: at an attention link: (1, "objects"), (2, "join"), (1, "planes"),
    (6, "objects"); under `hp` and `hh`.
  `fork_at_head`: at the head's link: (2, "objects"), (2, "planes"), (7, "objects"); under `hp` and
    `hh`.
  `later_paid_kept`, `later_hide_kept`: `hp` and `hh` at P := fun G => PscRun.Later U G; the second
    under the hypothesis that U has its sizes.
  `later_at_layers`, `later_at_attention`, `later_at_head`: so the three hold at that P, for every U
    that has its sizes (at a feed-forward link: for every U).
One of the nine is read off another kind's member: (2, "join") at an attention link, as in
ThetaKept.lean.

Hypotheses that remain.
  `h`: the library's hypothesis `P5J.AtMgA`.
  `hg`, `hL`: the link's number, and that L is the chain's link there.
  `hp`, `hh`: P passes the mark of a debt; P passes a run of hidden values laid.
  `hU`: U has its sizes (`Sized`, OnBytes/Tie/Pv/Psc/PscFork.lean).
  `hF`, `hr`: (in `later_paid_kept`, `later_hide_kept`) the ledger in front is later than U; the run
    of hidden values has been laid (`hideRun` returns).

How the proof goes. The proofs call `fork_kept_objects`, `fork_kept_join`, `fork_kept_planes`
(ThetaKept.lean), the theorems of the library that the last three of ThetaKept.lean call, and
`Later.trans`, `paid_later`, `hideRun_later` (PscLater.lean).

Users. "Later than U" stands here because it is the sentence that another file names
`LaterAt` (Honest/K8/LaterRunAt.lean), at that file's own three lists. That file is not imported:
the three
conclusions are written out.

Limits. Whether a run returns is not spoken of. At the full size alone: that limit comes with
`P5J.AtMgA`. No instance of these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.ThetaKept
import OnBytes.Tie.Pv.Psc.PscLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Law
open OnBytes (E)
open OnBytes.Model (Fork)
open OnBytes.PscRun (Sized Later paid_later hideRun_later)
open VerifiableInference.Desc (Chain Link Claim)
open VerifiableInference.Desc.LinkJoin (At HasFork at_join_is)
open VerifiableInference.OnPublicFiles (at_objects_is at_planes_is atS2_seatOf k03_atS2_calls
        objects_entry_low objects_entry_head planes_entry_low planes_entry_head)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

local notation "FS" => VerifiableInference.Desc.First.S

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-! ## 1 For every property -/

/-- **At a feed-forward link.** Conditional on `P5J.AtMgA`, g < 12, the chain's link, `hp`.
No instance of these hypotheses is exhibited in this file. -/
theorem fork_at_layers (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (g : Nat) (hg : g < 12)
    {L : Link FS Claim} (hL : cF.links[2 * g]? = some L) {P : Fork → Prop}
    (hp : ∀ (F : Fork) (i : Nat), P F → P (F.paid i)) :
    ∀ o ∈ [((1 : Nat), "objects"), (6, "objects")], ∀ run, At L o run →
      ∀ n e c e₁, run n e = .ok (c, e₁) → HasFork P e → HasFork P e₁ := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  intro o ho run hr n e c e₁ hy
  obtain ⟨d, rfl⟩ := objects_entry_low (m := 2 * g) (by omega) (by simpa using ho)
  rw [at_objects_is h.scope h.reads O (by omega) d hL hr] at hy
  exact fork_kept_objects _ (atS2_seatOf d) hp n e c e₁ hy

/-- **At an attention link.** Conditional on `P5J.AtMgA`, g < 12, the chain's link, `hp`, `hh`.
No instance of these hypotheses is exhibited in this file. -/
theorem fork_at_attention (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (g : Nat) (hg : g < 12)
    {L : Link FS Claim} (hL : cF.links[2 * g + 1]? = some L) {P : Fork → Prop}
    (hp : ∀ (F : Fork) (i : Nat), P F → P (F.paid i))
    (hh : ∀ (F G : Fork) (first : Nat) (v : Array E) (k : E), F.hideRun first v k = some G →
      P F → P G) :
    ∀ o ∈ [((1 : Nat), "objects"), (2, "join"), (1, "planes"), (6, "objects")],
      ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c, e₁) → HasFork P e → HasFork P e₁ := by
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
  intro o ho run hr n e c e₁ hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl
  · obtain ⟨d, ed⟩ := objects_entry_low (m := 2 * g + 1) (by omega) (Or.inl rfl)
    rw [ed] at hr
    rw [at_objects_is h.scope h.reads O (by omega) d hL hr] at hy
    exact fork_kept_objects _ (atS2_seatOf d) hp n e c e₁ hy
  · rw [at_join_is O p4' ng' ha' hL hr] at hy
    exact fork_kept_join _ k03_atS2_calls hp _ n e c e₁ hy
  · rw [planes_entry_low (m := 2 * g + 1) (by omega)] at hr
    obtain ⟨p, _, rfl⟩ := at_planes_is h.scope h.reads O (by omega) hL
      (H2K5.Door.readersAt_att p4' ha') hr
    exact fork_kept_planes _ k03_atS2_calls hp hh _ _ n e c e₁ hy
  · obtain ⟨d, ed⟩ := objects_entry_low (m := 2 * g + 1) (by omega) (Or.inr rfl)
    rw [ed] at hr
    rw [at_objects_is h.scope h.reads O (by omega) d hL hr] at hy
    exact fork_kept_objects _ (atS2_seatOf d) hp n e c e₁ hy

/-- **At the head's link.** Conditional on `P5J.AtMgA`, the chain's link, `hp`, `hh`. No instance of
these hypotheses is exhibited in this file. -/
theorem fork_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {L : Link FS Claim}
    (hL : cF.links[24]? = some L) {P : Fork → Prop}
    (hp : ∀ (F : Fork) (i : Nat), P F → P (F.paid i))
    (hh : ∀ (F G : Fork) (first : Nat) (v : Array E) (k : E), F.hideRun first v k = some G →
      P F → P G) :
    ∀ o ∈ [((2 : Nat), "objects"), (2, "planes"), (7, "objects")], ∀ run, At L o run →
      ∀ n e c e₁, run n e = .ok (c, e₁) → HasFork P e → HasFork P e₁ := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨_, iU3, _, hU, _, _⟩ := P4.k6Back_at_seat h.scope h.reads O
  intro o ho run hr n e c e₁ hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl
  · obtain ⟨d, ed⟩ := objects_entry_head (Or.inl rfl)
    rw [ed] at hr
    rw [at_objects_is h.scope h.reads O (by omega) d hL hr] at hy
    exact fork_kept_objects _ (atS2_seatOf d) hp n e c e₁ hy
  · rw [planes_entry_head] at hr
    obtain ⟨p, _, rfl⟩ := at_planes_is h.scope h.reads O (by omega) hL
      (P4.readers_head (P4.head_24 h.scope h.reads O) hU) hr
    exact fork_kept_planes _ k03_atS2_calls hp hh _ _ n e c e₁ hy
  · obtain ⟨d, ed⟩ := objects_entry_head (Or.inr rfl)
    rw [ed] at hr
    rw [at_objects_is h.scope h.reads O (by omega) d hL hr] at hy
    exact fork_kept_objects _ (atS2_seatOf d) hp n e c e₁ hy

/-! ## 2 "Later than U" -/

/-- `hp` at "later than U". -/
theorem later_paid_kept (U F : Fork) (i : Nat) (hF : Later U F) : Later U (F.paid i) :=
  hF.trans (paid_later F i)

/-- `hh` at "later than U". Conditional on: U has its sizes. -/
theorem later_hide_kept {U : Fork} (hU : Sized U) (F G : Fork) (first : Nat) (v : Array E) (k : E)
    (hr : F.hideRun first v k = some G) (hF : Later U F) : Later U G :=
  hF.trans (hideRun_later (hF.sized hU) hr)

/-- **At a feed-forward link.** Conditional on `P5J.AtMgA`, g < 12 and the chain's link. No instance
of these hypotheses is exhibited in this file. -/
theorem later_at_layers (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (g : Nat) (hg : g < 12)
    {L : Link FS Claim} (hL : cF.links[2 * g]? = some L) (U : Fork) :
    ∀ o ∈ [((1 : Nat), "objects"), (6, "objects")], ∀ run, At L o run →
      ∀ n e c e₁, run n e = .ok (c, e₁) →
        HasFork (fun G => Later U G) e → HasFork (fun G => Later U G) e₁ :=
  fork_at_layers h g hg hL (later_paid_kept U)

/-- **At an attention link.** Conditional on `P5J.AtMgA`, g < 12, the chain's link, U's sizes.
No instance of these hypotheses is exhibited in this file. -/
theorem later_at_attention (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (g : Nat) (hg : g < 12)
    {L : Link FS Claim} (hL : cF.links[2 * g + 1]? = some L) (U : Fork) (hU : Sized U) :
    ∀ o ∈ [((1 : Nat), "objects"), (2, "join"), (1, "planes"), (6, "objects")],
      ∀ run, At L o run → ∀ n e c e₁, run n e = .ok (c, e₁) →
        HasFork (fun G => Later U G) e → HasFork (fun G => Later U G) e₁ :=
  fork_at_attention h g hg hL (later_paid_kept U) (later_hide_kept hU)

/-- **At the head's link.** Conditional on `P5J.AtMgA`, the chain's link, U's sizes. No instance of
these hypotheses is exhibited in this file. -/
theorem later_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {L : Link FS Claim}
    (hL : cF.links[24]? = some L) (U : Fork) (hU : Sized U) :
    ∀ o ∈ [((2 : Nat), "objects"), (2, "planes"), (7, "objects")], ∀ run, At L o run →
      ∀ n e c e₁, run n e = .ok (c, e₁) →
        HasFork (fun G => Later U G) e → HasFork (fun G => Later U G) e₁ :=
  fork_at_head h hL (later_paid_kept U) (later_hide_kept hU)

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.fork_at_layers
#print axioms ProofFile.Honest.K3.Law.fork_at_attention
#print axioms ProofFile.Honest.K3.Law.fork_at_head
#print axioms ProofFile.Honest.K3.Law.later_paid_kept
#print axioms ProofFile.Honest.K3.Law.later_hide_kept
#print axioms ProofFile.Honest.K3.Law.later_at_layers
#print axioms ProofFile.Honest.K3.Law.later_at_attention
#print axioms ProofFile.Honest.K3.Law.later_at_head
