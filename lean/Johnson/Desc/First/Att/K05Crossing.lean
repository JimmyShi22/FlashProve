-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Crossing.lean: what a yes of the kind K5 does to what the lookup left, at
the seats `seatSO` (Johnson/Desc/First/Att/SeatO.lean) and `K3.seatCalls`
(Johnson/Desc/First/Look/K3Seat.lean). What was heard of the lookup stays; the ledger behind is
later than the ledger in front, in the sense of `Fo.Later`
(OnBytes/Tie/Pv/Lookup/Forest/FoForm.lean), and has its sizes.

Statements and proofs.
Main names:
  `later_of_hear`: where `hear` returns from a ledger with `Room`: `Fo.Later` F G and the three
    sizes of G.
  `lay_keeps_heard`: seatSO.lay turns nothing of what `S.lookHeard?` reads.
  `k5_crosses`: a yes of `decide` seatSO p from a record whose ledger has `Room` gives F and G with
    fork s = some F, fork s' = some G, heard s' = heard s, `Fo.Later` F G and `PscRun.Sized` G,
    where fork and heard are the readers of `K3.seatCalls`.
What it is for: a statement on the lookup's kind that is to stand at a record behind a later piece
asks of that piece that what was heard stays and that the ledger is later and has its sizes. This
file gives these for the piece of K5.
Limits: `Room` at the ledger in front is a premise. No soundness of the protocol is claimed. Nothing
on completeness or hiding.

-/
import Johnson.Desc.First.Att.K05LeftSeats

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Model.Road

/-- **Behind the kind's hearing the ledger is later**, and has its sizes. -/
theorem later_of_hear {x : Params.AttentionRounds} {F G : Fork} {rs rest : List Fmt.RoundView} {lead ns nx k : ℕ} {h : Heard}
    (hh : hear x (F, rs, 0) = some (h, G, rest, lead)) (R : Room F ns nx (slotsOf (script x) + k)) :
    Fo.Later F G ∧ OnBytes.PscRun.Sized G := by
  obtain ⟨_, _, _, _, _, _, st⟩ := hear_said hh R.sized
  have RG := room_behind hh R
  refine ⟨⟨by rw [R.next, RG.next]; exact Nat.le_add_right _ _, RG.ns.trans R.ns.symm, fun j hj => ?_⟩,
    RG.sized.vp, RG.sized.mf, RG.sized.got⟩
  obtain ⟨a, b, d⟩ := st j _ _ ⟨hj, rfl, rfl⟩
  exact ⟨a, b, d⟩

/-- The hearing's seat turns nothing of what was heard of the lookup. -/
theorem lay_keeps_heard {s s' : First.S} {h : Heard} {G : Fork} (e : seatSO.lay s h G = some s') :
    s'.lookHeard? = s.lookHeard? := by
  unfold seatSO at e
  simp only at e
  split at e
  · rename_i a ea
    obtain ⟨g0, _, e2⟩ := Option.bind_eq_some_iff.1 e
    cases hu : First.S.hear5? { s with rowsOwed := none, here := .att { a with F := G } } h with
    | error m =>
      rw [hu] at e2
      have e3 : (none : Option First.S) = some s' := e2
      cases e3
    | ok t =>
      rw [hu] at e2
      have e3 : some t = some s' := e2
      obtain rfl : t = s' := Option.some.inj e3
      obtain ⟨e1, _⟩ := (First.S.unmarked_ok _ _).1 hu
      have ht : ∃ a', t.here = .att a' ∧ a'.lookHeard = a.lookHeard := by
        rw [← e1]
        unfold First.S.hear5
        simp only
        split
        · exact ⟨_, here_mark _ _, rfl⟩
        · exact ⟨_, rfl, rfl⟩
      obtain ⟨a', h1, h2⟩ := ht
      unfold First.S.lookHeard?
      simp only [h1, h2, ea]
  · cases e

/-- **The kind's share of the crossing.** -/
theorem k5_crosses {Cl : Type} (claim : Aff → Cl) (p : Par) {s s' : First.S} {rs : List Fmt.RoundView} {ns nx k : ℕ}
    (hd : decide seatSO p s rs = .ok s')
    (R : ∀ F, seatSO.ledger s = some F → Room F ns nx (slotsOf (script p.own) + k)) :
    ∃ F G : Fork, (VerifiableInference.Desc.K3.seatCalls claim).fork s = some F ∧
      (VerifiableInference.Desc.K3.seatCalls claim).fork s' = some G ∧
      (VerifiableInference.Desc.K3.seatCalls claim).heard s' = (VerifiableInference.Desc.K3.seatCalls claim).heard s ∧
      Fo.Later F G ∧ OnBytes.PscRun.Sized G := by
  obtain ⟨_, F, h, G, l1, hh, l2⟩ := (decide_lays seatSO p _ _ _).1 hd
  obtain ⟨a, b⟩ := later_of_hear hh (R F l1)
  exact ⟨F, G, ledgerO_fork claim l1, ledgerO_fork claim (laysBack_seatSO _ _ _ _ l2), lay_keeps_heard l2, a, b⟩

end VerifiableInference.Desc.First.Att.P
