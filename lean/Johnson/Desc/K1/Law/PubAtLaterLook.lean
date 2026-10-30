-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- A copy of a working file of this project that is not in this repository: as copied, it parted
-- from it in its import lines alone.
/-
Johnson/Desc/K1/Law/PubAtLaterLook.lean: a yes of a segment's later moment (`commitAtS`) leaves four
Bools of the lookups' layer (Johnson/Desc/First/Look/K3FillCode.lean): `liveIsC`, `linkFreshC`,
`lookOutC` are the same behind as in front; `lookInC`'s yes in front gives its yes behind.

Main names: `fork_putK`, `lookHeard_put` (what the block's three writes do to two readers of the
state `S`); `commitAtS_heardAt`, `commitAtS_forkSlots`; `liveIs_at_later`, `linkFresh_at_later`,
`lookOut_at_later`, `lookIn_at_later`.

What is not claimed. Nothing on the quiet step that stands behind the sending at a place of the
reads. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.First.Look.K3FillCode
import Johnson.Desc.K1.Law.LinkKeptAtLater
import Johnson.Desc.K1.Law.TlAtRecord
import Johnson.Desc.K1.KeepsSlots

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Look (K3Data liveIsC linkFreshC lookInC lookOutC placeAt)
open VerifiableInference.Desc.K3 (k3OnIn k3OnOut heardAt sizedB freeB)

variable {Cl : Type}

/-- Where a ledger is open, laying a link's context and then a ledger leaves that ledger open. -/
theorem fork_putK (s : S) (w : DState Unit) (L' : LinkCtx) (F F' : Fork) (hF : s.fork? = some F) :
    (((laid s w).putLink L').putFork F').fork? = some F' := by
  cases hs : s.here with
  | lay a => simp [S.putFork, S.putLink, S.fork?, laid, hs]
  | att a => simp [S.putFork, S.putLink, S.fork?, laid, hs]
  | head a =>
    have ho : a.opened = true := by
      by_contra hn
      simp [S.fork?, hs, hn] at hF
    simp [S.putFork, S.putLink, S.fork?, laid, hs, ho]
  | between => simp [S.fork?, hs] at hF
  | fin a => simp [S.fork?, hs] at hF
  | mem a => simp [S.fork?, hs] at hF

/-- The three writes leave what was heard of the lookup on the calls. -/
theorem lookHeard_put (s : S) (w : DState Unit) (L' : LinkCtx) (F' : Fork) :
    (((laid s w).putLink L').putFork F').lookHeard? = s.lookHeard? := by
  cases hs : s.here with
  | lay a => simp [S.putFork, S.putLink, S.lookHeard?, laid, hs]
  | att a => simp [S.putFork, S.putLink, S.lookHeard?, laid, hs]
  | head a =>
    by_cases ho : a.opened = true <;> simp [S.putFork, S.putLink, S.lookHeard?, laid, hs, ho]
  | between => simp [S.putFork, S.putLink, S.lookHeard?, laid, hs]
  | fin a => simp [S.putFork, S.putLink, S.lookHeard?, laid, hs]
  | mem a => simp [S.putFork, S.putLink, S.lookHeard?, laid, hs]

/-- What was heard at either seat is as it was. -/
theorem commitAtS_heardAt (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (s s' : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s rs gs = .ok s') (digits : Bool) :
    heardAt digits s' = heardAt digits s := by
  obtain ⟨_, _, F', w, _, _, e⟩ := commitAtS_rec P link moment arrays s s' rs gs h
  unfold heardAt
  rw [(commitAtS_tl P link moment arrays s s' rs gs h).1, e, lookHeard_put]

/-- The ledger behind has the slots of the ledger in front. -/
theorem commitAtS_forkSlots (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (s s' : S)
    (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s rs gs = .ok s') :
    ∃ F F', s.fork? = some F ∧ s'.fork? = some F' ∧ PscRun.SlotsSame F F' := by
  obtain ⟨_, F, _, y, _, hF, _, rfl, hs⟩ := commitAtS_slots h
  exact ⟨F, y.F, hF, fork_putK s _ _ F _ hF, hs⟩

theorem sizedB_same {F F' : Fork} (h : PscRun.SlotsSame F F') : sizedB F' = sizedB F := by
  unfold sizedB
  rw [h.vp, h.mf, h.gotF, h.ns]

theorem freeB_same {F F' : Fork} (h : PscRun.SlotsSame F F') (a n : Nat) :
    freeB F' a n = freeB F a n := by
  unfold freeB
  rw [h.gotF, h.ns]

/-- **"frame.liveIs".** -/
theorem liveIs_at_later (d : K3Data) (P : Par) (link moment : Nat) (arrays : Option (List Nat))
    (s s' : S) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s [r₁, r₂] gs = .ok s') :
    liveIsC d s' = liveIsC d s := by
  obtain ⟨L, L', a, b, _, _, er, es⟩ := commitAtS_linkKept P link moment arrays s s' r₁ r₂ gs h
  unfold liveIsC S.live
  rw [a, b]
  show (decide (L'.check.frame.shape = d.shape) && decide (L'.check.rows.layout = d.layout)) =
    (decide (L.check.frame.shape = d.shape) && decide (L.check.rows.layout = d.layout))
  rw [er, es]

/-- **linkFresh.** -/
theorem linkFresh_at_later (d : K3Data) (m : Nat) (P : Par) (link moment : Nat)
    (arrays : Option (List Nat)) (s s' : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s [r₁, r₂] gs = .ok s') :
    linkFreshC d m s' = linkFreshC d m s := by
  obtain ⟨L, L', a, b, _, ea, _, _⟩ := commitAtS_linkKept P link moment arrays s s' r₁ r₂ gs h
  unfold linkFreshC
  rw [(commitAtS_tl P link moment arrays s s' _ gs h).1, a, b]
  show (_ && (L'.arrayOf == _)) = (_ && (L.arrayOf == _))
  rw [ea]

/-- The lookup's condition behind its block is as it was. -/
theorem k3OnOut_at_later (p : First.Look.P) (P : Par) (link moment : Nat)
    (arrays : Option (List Nat)) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s rs gs = .ok s') :
    k3OnOut p s' = k3OnOut p s := by
  obtain ⟨F, F', a, b, hs⟩ := commitAtS_forkSlots P link moment arrays s s' rs gs h
  unfold k3OnOut
  rw [commitAtS_heardAt P link moment arrays s s' rs gs h, a, b]
  cases p.shape with
  | none => rfl
  | some hh =>
    cases heardAt p.digits s with
    | none => rfl
    | some g =>
      show (_ && _) = (_ && _)
      simp only [sizedB_same hs, freeB_same hs, hs.next]

/-- **lookOut.** -/
theorem lookOut_at_later (d : K3Data) (m : Nat) (dg : Bool) (P : Par) (link moment : Nat)
    (arrays : Option (List Nat)) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s rs gs = .ok s') :
    lookOutC d m dg s' = lookOutC d m dg s := by
  unfold lookOutC
  congr 1
  funext p
  exact k3OnOut_at_later p P link moment arrays s s' rs gs h

/-- The lookup's condition in front of its block: its yes stays. -/
theorem k3OnIn_at_later (p : First.Look.P) (P : Par) (link moment : Nat)
    (arrays : Option (List Nat)) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s rs gs = .ok s')
    (h0 : k3OnIn p s = true) : k3OnIn p s' = true := by
  obtain ⟨F, F', a, b, hs⟩ := commitAtS_forkSlots P link moment arrays s s' rs gs h
  unfold k3OnIn at h0 ⊢
  rw [commitAtS_heardAt P link moment arrays s s' rs gs h,
    (commitAtS_tl P link moment arrays s s' rs gs h).2, b]
  rw [a] at h0
  cases hp : p.shape with
  | none => rw [hp] at h0; cases h0
  | some hh =>
    rw [hp] at h0
    simp only [Bool.and_eq_true, Option.any_some] at h0 ⊢
    refine ⟨⟨h0.1.1, rfl⟩, ?_⟩
    rw [sizedB_same hs, freeB_same hs, hs.next]
    exact h0.2

/-- **lookIn.** -/
theorem lookIn_at_later (d : K3Data) (m : Nat) (dg : Bool) (P : Par) (link moment : Nat)
    (arrays : Option (List Nat)) (s s' : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s [r₁, r₂] gs = .ok s')
    (h0 : lookInC d m dg s = true) : lookInC d m dg s' = true := by
  obtain ⟨L, L', a, b, el, ea, _, _⟩ := commitAtS_linkKept P link moment arrays s s' r₁ r₂ gs h
  unfold lookInC at h0 ⊢
  cases hp : placeAt d.X m dg with
  | none => rw [hp] at h0; cases h0
  | some p =>
    rw [hp] at h0
    rw [a] at h0
    rw [b]
    simp only [Option.any_some, Bool.and_eq_true] at h0 ⊢
    refine ⟨k3OnIn_at_later p P link moment arrays s s' _ gs h h0.1, ?_⟩
    rw [el, ea]
    exact h0.2

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.liveIs_at_later
#print axioms VerifiableInference.Desc.K1.linkFresh_at_later
#print axioms VerifiableInference.Desc.K1.lookOut_at_later
#print axioms VerifiableInference.Desc.K1.lookIn_at_later
