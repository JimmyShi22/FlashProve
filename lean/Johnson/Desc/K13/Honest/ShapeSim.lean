--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K13/Honest/ShapeSim.lean: kind K13, the members' batching: THE SHAPE OF WHAT STANDS AT
THE CHAIN's END BEHIND THE JOINED SUB-PROTOCOL (`atM3`): a function of the plan, the pile's rows'
shapes and the slots taken. AND: TWO STATES OF THE VERIFIER THAT HAVE ONE SHAPE (`shOf`, Shape.lean
of this folder) STEP ALIKE: the sub-protocol returns at both or at neither, whatever elements its
rounds hold, and the states behind are of one shape, the claim that is laid among it. Both states
are the verifier's: nothing here is a simulator, and nothing is said on zero knowledge. Definitions
with code, and statements with their proofs.
Main names:
  `EndSh`, `endOf`: the shape of what stands at the chain's end: W's message as announced; the
    numbers of the messages sent; four numbers; the claim's row's shape.
  `takeMask_num`, `takeMasksInto_list`, `takeMasks_list`: which mask entries are taken hangs on the
    ledger alone.
  `atM3_return_row`: where the sub-protocol returns: the state behind, with the row as `Batt.rowOf`
    at what the sumcheck's run returns.
  `endOf_behind`: the shape of what stands at the chain's end behind the sub-protocol: a function of
    the plan, the pile's rows' shapes and the slots taken.
  `atM3_sim`: **the statement.** `atM3_sim_iff`: it returns at the one exactly if at the other.

What is not claimed. That two states of a run's course are of one shape. Which relation between
states other kinds' sub-protocols want. Nothing on soundness or on hiding.

-/
import Johnson.Desc.K13.Honest.ShapeStep
import Johnson.Desc.K13.Honest.AcceptsFit
import Johnson.Desc.K13.Honest.ClaimShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes OnBytes.Model OnBytes.Params
open VerifiableInference.Desc (roundsFit noDigest)
open VerifiableInference.Desc.Ground (takeMaskP takeMaskL takeMasksInto takeMasksP ok)
open VerifiableInference.Desc.First (S rowOfClaim)
open VerifiableInference.Desc.K13.Law
open Desc.Plain (DState)

/-- The shape of what stands at the chain's end. -/
structure EndSh where
  msg : Array OracleNotice
  ids : Array Nat
  /-- where a claim is laid: W's number, the split's, the own group's, the first fold's mask's; the
  claim's row's shape -/
  lin : Option (Nat × Nat × Nat × Option Nat × RowSh)

/-- Of a state; none where the chain has not come to its end. -/
def endOf (s : S) : Option EndSh :=
  match s.here with
  | .mem a =>
    some ⟨a.msg, a.ids,
      a.lin.map fun l => (l.w, l.split, l.own, l.mask, rowSh (rowOfClaim l.claim))⟩
  | _ => none

variable {L : Type}

/-- Which entry is handed out, and the ledger behind. -/
theorem takeMask_num {d d' : DState L} {o i : ℕ} (h : takeMaskP d o = some (i, d')) :
    ∃ l, (d.st.oracles[o]?).bind (·.ledger) = some l ∧ i = nextOf l ∧
      (d'.st.oracles[o]?).bind (·.ledger) = some (taken l) := by
  obtain ⟨x, l, hx, hl, -, -, hd⟩ := takeMask_left h
  have hb : (d.st.oracles[o]?).bind (·.ledger) = some l := by
    rw [hx]
    exact hl
  refine ⟨l, hb, ?_, ?_⟩
  · unfold takeMaskP at h
    split at h
    · rw [hb] at h
      exact ((Prod.mk.inj (Option.some.inj h)).1).symm
    · cases h
  · rw [hd, layLedger_at hx (taken l)]
    rfl

/-- Which entries the loop of the taking hands out hangs on the ledger alone. -/
theorem takeMasksInto_list (o o' : ℕ) : ∀ (n : ℕ) (d d₂ : DState L) (acc : Array ℕ)
    (t t₂ : List ℕ × DState L),
    (d.st.oracles[o]?).bind (·.ledger) = (d₂.st.oracles[o']?).bind (·.ledger) →
    takeMasksInto o n d acc = some t → takeMasksInto o' n d₂ acc = some t₂ → t.1 = t₂.1
  | 0, d, d₂, acc, t, t₂, _, h, h₂ => by
    rw [← Option.some.inj h, ← Option.some.inj h₂]
  | n + 1, d, d₂, acc, t, t₂, e, h, h₂ => by
    unfold takeMasksInto at h h₂
    cases hm : takeMaskP d o with
    | none =>
      rw [hm] at h
      cases h
    | some q =>
      cases hm₂ : takeMaskP d₂ o' with
      | none =>
        rw [hm₂] at h₂
        cases h₂
      | some q₂ =>
        rw [hm] at h
        rw [hm₂] at h₂
        obtain ⟨l, a1, a2, a3⟩ := takeMask_num (i := q.1) (d' := q.2) hm
        obtain ⟨l₂, b1, b2, b3⟩ := takeMask_num (i := q₂.1) (d' := q₂.2) hm₂
        obtain rfl : l = l₂ := Option.some.inj (a1.symm.trans (e.trans b1))
        have eq : q.1 = q₂.1 := a2.trans b2.symm
        have h₂' : takeMasksInto o' n q₂.2 (acc.push q.1) = some t₂ := by
          rw [eq]
          exact h₂
        exact takeMasksInto_list o o' n q.2 q₂.2 (acc.push q.1) t t₂ (a3.trans b3.symm) h h₂'

/-- The same, as the text calls it. -/
theorem takeMasks_list {d d₂ : DState L} {o o' n : ℕ} {t t₂ : List ℕ × DState L}
    (e : (d.st.oracles[o]?).bind (·.ledger) = (d₂.st.oracles[o']?).bind (·.ledger))
    (h : takeMasksP d o n = some t) (h₂ : takeMasksP d₂ o' n = some t₂) : t.1 = t₂.1 :=
  takeMasksInto_list o o' n d d₂ #[] t t₂ e h h₂

variable {Cl : Type}

/-- **Where the joined sub-protocol returns**: what the taking returns, W's message, and the row as
`Batt.rowOf` at what the sumcheck's run returns. -/
theorem atM3_return_row {P : Where} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (atM3 (Cl := Cl) P).decide s rs gs = .ok s') :
    ∃ (t : List ℕ × St) (msg : Array OracleNotice) (x : E) (hd : Psc.Heard) (o : Psc.Out),
      takeMasksP (dOf s) s.out.indexMasks (Batt.masksOf P.lin.kCol) = some t ∧
      linMessageW P.lin = some msg ∧ Batt.fits P.lin.kCol s.out.pending = true ∧
      Psc.run (Batt.claimOf s.out.pending x) (Batt.summandOf s.out.pending x)
        (t.1.map fun i => ⟨s.out.indexMasks, i⟩) hd = some o ∧
      s' = withClaim s t.2.st msg (Batt.rowOf s.out.pending o) := by
  have h' : (((frontB (Cl := Cl) atS P).decide s _ _).bind fun s₁ =>
      (claimCombinationBlock (Cl := Cl) atS P).decide s₁ _ _).bind (fun s₂ =>
                      (quietB (Cl := Cl) atS P).decide s₂ _ _) = .ok s' := h
  obtain ⟨s₂, h12, h3⟩ := ebind_ok.1 h'
  obtain ⟨s₁, h1, h2⟩ := ebind_ok.1 h12
  have he := frontB_ok atS P h1
  obtain ⟨p, out, hp, hb, rfl⟩ := battB_ok atS P h2
  have h3' := h3
  simp only [quietB, still, quiet_is, Law.bind_ok, Law.there_ok, Law.need_ok, Law.pure_ok,
    Lens.part] at h3'
  obtain ⟨p', hp', _, _, msg, ⟨_, _, hm⟩, rfl⟩ := h3'
  obtain ⟨f, -, -, hfin, -⟩ := atM3_rec h
  have e1 : atS.enter s = some s.enterMem := by simp only [atS, hfin]
  rw [e1] at he
  have e2 : s₁ = { s with here := .mem { msg := #[], ids := #[], lin := none } } := by
    rw [← Option.some.inj he]
    simp only [S.enterMem, hfin]
  subst e2
  obtain rfl := Option.some.inj hp
  obtain rfl := Option.some.inj hp'
  obtain ⟨_, _, x, t, hd, o, _, _, b2, _, _, b4, _, b6, _, rfl⟩ := batt_ok hb
  exact ⟨t, msg, x, hd, o, b4, hm, b2, b6, rfl⟩

/-- **The shape of what stands at the chain's end behind the sub-protocol.** -/
theorem endOf_behind {k : ℕ} (s : S) (st : Statement) (msg : Array OracleNotice) {x : E}
    {fresh : List Slot} {hd : Psc.Heard} {o : Psc.Out} (hf : Batt.fits k s.out.pending = true)
    (hr : Psc.run (Batt.claimOf s.out.pending x) (Batt.summandOf s.out.pending x) fresh hd =
      some o) :
    endOf (withClaim s st msg (Batt.rowOf s.out.pending o)) =
      some ⟨msg, #[], some (noId, noId, noId, none, claimSh k (shOf s).pile fresh)⟩ := by
  show some (⟨msg, #[], some (noId, noId, noId, none,
    rowSh (rowOfClaim (memberClaim (Batt.rowOf s.out.pending o))))⟩ : EndSh) = _
  rw [rowOfClaim_member, rowSh_rowOf hf hr]
  rfl

/-- **Two states of one shape step alike.** s, u: two states of the verifier, of one shape. Where
the sub-protocol returns at s, on whatever rounds, it returns at u on all rounds that pass the
step's own test on rounds; and the two states behind are of one shape, what stands at the chain's
end among it. -/
theorem atM3_sim {P : Where} {s s' u : S} (e : shOf s = shOf u) {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (atM3 (Cl := Cl) P).decide s rs gs = .ok s')
    (rs₂ : List Fmt.RoundView) (hr₂ : roundsFit (battRounds P) rs₂ = true)
    (gs₂ : List (List (Nat × List UInt64))) :
    ∃ u', (atM3 (Cl := Cl) P).decide u (rs₂.map noDigest) gs₂ = .ok u' ∧ shOf s' = shOf u' ∧
      endOf s' = endOf u' := by
  have hu : readySh P (shOf u) = true := by
    rw [← e]
    exact shape_of_return h
  obtain ⟨f, t₀, msg₀, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := ready_of_shape hu
  obtain ⟨row₀, h₂⟩ := atM3_accepts_fit (Cl := Cl) a1 a2 a3 a4 a5 a6 a7 a8 a9 rs₂ hr₂ gs₂
  refine ⟨_, h₂, ?_, ?_⟩
  · have q1 := shape_step h
    have q2 := shape_step h₂
    rw [e, q2] at q1
    exact (Option.some.inj q1).symm
  · obtain ⟨t, msg, x, hd, o, b1, b2, b3, b4, b5⟩ := atM3_return_row h
    obtain ⟨t', msg', x', hd', o', c1, c2, c3, c4, c5⟩ := atM3_return_row h₂
    rw [b5, c5, endOf_behind s t.2.st msg b3 b4, endOf_behind u t'.2.st msg' c3 c4]
    obtain rfl : msg = msg' := Option.some.inj (b2.symm.trans c2)
    have ei : s.out.indexMasks = u.out.indexMasks := congrArg Sh.index e
    have el : (s.st.oracles[s.out.indexMasks]?).bind (·.ledger) =
        (u.st.oracles[u.out.indexMasks]?).bind (·.ledger) := by
      have q : ((shOf s).msgs[(shOf s).index]?).bind (·.ledger) =
          ((shOf u).msgs[(shOf u).index]?).bind (·.ledger) := by rw [e]
      unfold shOf at q
      simp only [Array.getElem?_map] at q
      cases hs : s.st.oracles[s.out.indexMasks]? <;>
        cases hu' : u.st.oracles[u.out.indexMasks]? <;> rw [hs, hu'] at q <;> exact q
    have et : t.1 = t'.1 := takeMasks_list (d := dOf s) (d₂ := dOf u) el b1 c1
    rw [et, ei, e]

/-- It returns at the one exactly if at the other. -/
theorem atM3_sim_iff {P : Where} {s u : S} (e : shOf s = shOf u) (rs : List Fmt.RoundView)
    (hr : roundsFit (battRounds P) rs = true) (gs gs₂ : List (List (Nat × List UInt64))) :
    (∃ s', (atM3 (Cl := Cl) P).decide s (rs.map noDigest) gs = .ok s') ↔
      ∃ u', (atM3 (Cl := Cl) P).decide u (rs.map noDigest) gs₂ = .ok u' :=
  ⟨fun ⟨_, q⟩ => (atM3_sim e q rs hr gs₂).imp fun _ r => r.1,
    fun ⟨_, q⟩ => (atM3_sim e.symm q rs hr gs).imp fun _ r => r.1⟩

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.takeMask_num
#print axioms VerifiableInference.Desc.K13.Honest.takeMasksInto_list
#print axioms VerifiableInference.Desc.K13.Honest.takeMasks_list
#print axioms VerifiableInference.Desc.K13.Honest.atM3_return_row
#print axioms VerifiableInference.Desc.K13.Honest.endOf_behind
#print axioms VerifiableInference.Desc.K13.Honest.atM3_sim
#print axioms VerifiableInference.Desc.K13.Honest.atM3_sim_iff
