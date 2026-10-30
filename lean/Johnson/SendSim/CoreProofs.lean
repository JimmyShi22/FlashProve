-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/CoreProofs.lean: the two theorems of the general model, sendExact and sendFresh,
proved for every finite field and every sender of the model, under the premises named below. It
claims no property of the protocol: not hiding, not zero knowledge.
Terms: Johnson/SendSim/Defs.lean, "Terms of the model". Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file proves. The full statements are Spec.sendExact and Spec.sendFresh. Both hold for
every finite field, every sender of the model, and all weights, lists of queries and data.
  sendExact   If the list of queries is within the bound (Within: of each row at most as many
              distinct points as its tail has entries) and Mends holds (for any values of the
              answers there is a family of message coins, at which lay is additive, that contributes
              them), then what is disclosed (shown) has, over uniform coins, the same distribution
              for any two data.
  sendFresh   If the list is within the bound and MendsOff holds for the sets U, Kn and KnT (any
              change of the coins in U extends to a family, at which lay is additive, that changes
              no coin in Kn, no answer, and no message of a row with a tail coin in KnT), then over
              uniform coins the coins in U are uniform, and independent of what is disclosed
              together with the coins in Kn and KnT.

Limits. Those of the two statements (Johnson/SendSim/Defs.lean, "Limits of these two statements").
Whether a sending of the release is an instance of the model, with the premises met, is not said
here. Johnson/SendSim/At/Bridge.lean makes the honest sender (sendPart, a definition in Lean) an
instance; other files of that folder derive the model's premises from public premises on the job,
the seeds, the queried positions and the book.

How it fits. rowsExact (Johnson/SendSim/At/RowsExact.lean) applies sendExact; rowsFresh
(Johnson/SendSim/At/RowsFresh.lean) and rowsFreshAny (Johnson/SendSim/At/FreshWideProofs.lean) apply
sendFresh.

How the proofs go. A family s of message coins at which lay is additive changes each row's message
by lay s. A change of a row's message is compensated, at no more points than the tail has entries,
by a change of the tail (sym_shift, Johnson/LinkSim/Tail.lean). So a change of the data, or of some
coins, is a translation of the coins by a vector that depends on no coin, under which what is
disclosed stays the same (shown_move). The theorems follow by map_eq_of_shift
(Johnson/LinkSim/Shift.lean) and by apart_of_shifts (Johnson/SendSim/Apart.lean).

The other names.
  mem_ptsOf       the point of a query in the list is among the points queried of its row.
  moveBy          the vector: s, and for each row the tail that compensates the change dm.
  shown_move      what is disclosed at data and c is what is disclosed at data' and c + moveBy, if
                  the list is within the bound, lay is additive at s, and each answer's form agrees
                  at data and at data' + lay s.
  tailShift_zero  a change of a message that is 0 at all entries needs no change of the tail.
-/
import Johnson.SendSim.Pads
import Johnson.SendSim.Apart
import Johnson.SendSim.Tie.Sym

set_option autoImplicit false

noncomputable section

namespace OnBytes.SendSim
open Prob OnBytes.LinkSim

variable {K : Type} [Field K] [DecidableEq K]

namespace Sender
variable {S : Sender K}

/-- The point of a query in the list is among the points that the list queries of its row. -/
theorem mem_ptsOf {asks : List (S.Row × K)} {a : S.Row × K} (h : a ∈ asks) :
    a.2 ∈ S.ptsOf asks a.1 := by
  unfold ptsOf
  exact List.mem_toFinset.2 (List.mem_map.2 ⟨a, List.mem_filter.2 ⟨h, by simp⟩, rfl⟩)

/-- The vector by which the coins are translated: s on the message coins, and on each row's tail the
change that compensates the change dm of the row's message at the queried points. -/
def moveBy (asks : List (S.Row × K)) (s : S.Cn → K) (dm : S.Row → ℕ → K) : S.Coins :=
  (s, fun ρ => cutTl (S.r ρ) (tailShift (S.r ρ) (S.l ρ) (S.ptsOf asks ρ) (dm ρ)))

/-- If the list is within the bound, lay is additive at s, and each answer's form takes the same
value at data and at data' + lay s, then what is disclosed at data and c is what is disclosed at
data' and c + moveBy asks s (data - data' - lay s). -/
theorem shown_move (w : S.Ans → S.Row → ℕ → K) {asks : List (S.Row × K)} (hW : S.Within asks)
    (data data' : S.Row → ℕ → K) {s : S.Cn → K} (hs : S.AddsAt s)
    (hw : ∀ i, S.form (w i) data = S.form (w i) data' + S.wt w s i) (c : S.Coins) :
    S.shown w asks data c =
      S.shown w asks data' (c + moveBy asks s fun ρ => data ρ - data' ρ - S.lay s ρ) := by
  refine Prod.ext (List.map_congr_left fun a ha => ?_) (funext fun i => ?_)
  · show sym (S.r a.1) (S.l a.1) a.2 (data a.1 + S.lay c.1 a.1) (tl (c.2 a.1)) =
      sym (S.r a.1) (S.l a.1) a.2 (data' a.1 + S.lay (c.1 + s) a.1)
        (tl (c.2 a.1 + cutTl (S.r a.1) (tailShift (S.r a.1) (S.l a.1) (S.ptsOf asks a.1)
          (data a.1 - data' a.1 - S.lay s a.1))))
    rw [hs c.1]
    have e : data a.1 + S.lay c.1 a.1 =
        (data' a.1 + (S.lay c.1 + S.lay s) a.1) + (data a.1 - data' a.1 - S.lay s a.1) := by
      funext j
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    rw [e, sym_shift _ _ _ (hW a.1) _ _ _ (mem_ptsOf ha)]
    refine sym_congr _ _ _ (fun _ _ => rfl) fun q hq => ?_
    rw [tl_add, Pi.add_apply, Pi.add_apply, tl_cutTl _ _ hq]
  · show S.form (w i) (fun ρ => data ρ + S.lay c.1 ρ) =
      S.form (w i) (fun ρ => data' ρ + S.lay (c.1 + s) ρ)
    rw [hs c.1]
    have e1 : (fun ρ => data ρ + S.lay c.1 ρ) = data + S.lay c.1 := rfl
    have e2 : (fun ρ => data' ρ + (S.lay c.1 + S.lay s) ρ) = data' + (S.lay c.1 + S.lay s) := rfl
    rw [e1, e2, form_add, form_add, form_add, hw i]
    show _ = S.form (w i) data' + (S.form (w i) (S.lay c.1) + S.wt w s i)
    ring

/-- If dm is 0 at all l entries of a message, the compensating change of the tail is 0. -/
theorem tailShift_zero (r l : ℕ) (pts : Finset K) {dm : ℕ → K} (h : ∀ j < l, dm j = 0) :
    tailShift r l pts dm = 0 :=
  tailFor_zero pts fun p _ => by
    unfold msgPart
    exact Finset.sum_eq_zero fun j hj => by rw [h j (Finset.mem_range.1 hj), mul_zero]

end Sender

open Sender

/-- Proof of Spec.sendExact: if the list of queries is within the bound and Mends holds, then what
is disclosed has, over uniform coins, the same distribution for any two data. -/
theorem sendExact : Spec.sendExact := by
  intro K _ _ _ S w asks data data' hW hM
  obtain ⟨s, hs, hw⟩ := hM fun i => S.form (w i) data - S.form (w i) data'
  exact map_eq_of_shift (moveBy asks s fun ρ => data ρ - data' ρ - S.lay s ρ) _ _
    (shown_move w hW data data' hs fun i => by rw [hw]; ring)

/-- Proof of Spec.sendFresh: if the list of queries is within the bound and MendsOff holds, then the
coins in U are uniform, and independent of what is disclosed together with the coins in Kn and KnT.
-/
theorem sendFresh : Spec.sendFresh := by
  intro K _ _ _ S w asks data U Kn KnT hW hM
  choose s hs hU hKn hw hT using hM
  refine apart_of_shifts (S.cut U)
    (fun c => (S.shown w asks data c, S.cut Kn c, S.cutT KnT c))
    (fun δ c => c + moveBy asks (s δ) fun ρ => data ρ - data ρ - S.lay (s δ) ρ)
    (fun δ => (Equiv.addRight _).bijective) (fun δ c => funext fun u => ?_) fun δ c => ?_
  · show c.1 u + s δ u = c.1 u + δ u
    rw [hU δ u]
  · refine Prod.ext ?_ (Prod.ext (funext fun k => ?_) (funext fun x => ?_))
    · exact (shown_move w hW data data (hs δ) (fun i => by rw [hw δ]; simp) c).symm
    · show c.1 k + s δ k = c.1 k
      rw [hKn δ k k.2, add_zero]
    · show c.2 x.1.1 x.1.2 + cutTl _ (tailShift _ _ _ _) x.1.2 = c.2 x.1.1 x.1.2
      rw [tailShift_zero _ _ _ fun j hj => by
        simp [hT δ x.1 x.2 j hj]]
      exact add_zero _

end OnBytes.SendSim

#print axioms OnBytes.SendSim.sendExact
#print axioms OnBytes.SendSim.sendFresh
