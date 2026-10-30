-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/LedgerFwd.lean: what the output head's seat reads back out of the ledger it reads
the same out of every later ledger.

Why. The seat makes "what was heard" anew at each state, out of the program's structure of heard
values and the ledger (`allOf`, Johnson/Stored/HeadSeat.lean): a hidden scalar is named by its slot,
and what is shown of it stands in the ledger. Between the output head's own sub-protocol and the
batching the ledger grows. The library's "later ledger" (`OnBytes.PscRun.Later`,
OnBytes/Tie/Pv/Psc/PscLater.lean) says that a filled slot stays filled with what is shown under it.

What is shown. Each in one direction: where the reader answers at F, it answers the same at a later
G.
  `shown_fwd`: what is shown under a slot.
  `hidAt_fwd`, `mapM_fwd`, `hidsAt_fwd`, `sumOf_fwd`: a hidden scalar; a run of them; a sumcheck.
  `allOf_fwd`: **all that was heard.**

Limits. One direction: a reader that is silent at F may answer at G. Nothing on soundness.


-/
import Johnson.Stored.HeadSeat
import OnBytes.Tie.Pv.Psc.PscLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads.Pass

open OnBytes (E)
open OnBytes.Model (Fork)
open OnBytes.PscRun (Later)
open VerifiableInference.Desc.Kinds.Head (hidAt hidsAt sumOf allOf)

/-- What is shown under a slot. -/
theorem shown_fwd {F G : Fork} (hL : Later F G) {j : Nat} {v : E} (h : F.shown j = some v) :
    G.shown j = some v := by
  unfold Fork.shown at h ⊢
  by_cases hc : (decide (j < F.ns) && F.gotF.getD j false) = true
  · rw [if_pos hc] at h
    obtain ⟨c1, c2⟩ := Eq.mp (Bool.and_eq_true _ _) hc
    obtain ⟨k1, k2, _⟩ := hL.keep j c2
    have k1' : G.gotF.getD j false = true := k1
    rw [hL.ns, c1, k1', k2]
    exact h
  · rw [if_neg hc] at h
    cases h

theorem hidAt_fwd {F G : Fork} (hL : Later F G) {j : Nat} {y : VerifiableInference.Desc.Kinds.Hid}
    (h : hidAt F j = some y) : hidAt G j = some y := by
  unfold hidAt at h ⊢
  cases hs : F.shown j with
  | none =>
    rw [hs] at h
    cases h
  | some v =>
    rw [hs] at h
    rw [shown_fwd hL hs]
    exact h

/-- A list read through two readers, of which the second answers wherever the first does. -/
theorem mapM_fwd {α β : Type} {f g : α → Option β} (hfg : ∀ a b, f a = some b → g a = some b) :
    ∀ (l : List α) (ys : List β), l.mapM f = some ys → l.mapM g = some ys
  | [], ys, h => h
  | a :: l, ys, h => by
    rw [List.mapM_cons] at h ⊢
    cases h1 : f a with
    | none =>
      rw [h1] at h
      cases h
    | some b =>
      rw [h1] at h
      rw [hfg a b h1]
      cases h2 : l.mapM f with
      | none =>
        rw [h2] at h
        cases h
      | some bs =>
        rw [h2] at h
        rw [mapM_fwd hfg l bs h2]
        exact h

theorem hidsAt_fwd {F G : Fork} (hL : Later F G) {j n : Nat}
    {ys : Array VerifiableInference.Desc.Kinds.Hid} (h : hidsAt F j n = some ys) :
    hidsAt G j n = some ys := by
  unfold hidsAt at h ⊢
  cases h1 : (List.range n).mapM fun i => hidAt F (j + i) with
  | none =>
    rw [h1] at h
    cases h
  | some l =>
    rw [h1] at h
    rw [mapM_fwd (f := fun i => hidAt F (j + i)) (g := fun i => hidAt G (j + i))
      (fun a b hab => hidAt_fwd hL hab) _ l h1]
    exact h

theorem sumOf_fwd {F G : Fork} (hL : Later F G) {t : OnBytes.Model.Tsc} {r : Array E} {n : Nat}
    {y : _} (h : sumOf F t r n = some y) : sumOf G t r n = some y := by
  unfold sumOf at h ⊢
  cases h1 : hidAt F t.sCl with
  | none =>
    rw [h1] at h
    cases h
  | some a1 =>
    cases h2 : hidsAt F t.sEnd n with
    | none =>
      rw [h1, h2] at h
      cases h
    | some a2 =>
      rw [h1, h2] at h
      rw [hidAt_fwd hL h1, hidsAt_fwd hL h2]
      exact h

/-- **All that was heard.** -/
theorem allOf_fwd {F G : Fork} (hL : Later F G) {x : OnBytes.Model.Head.Heard}
    {q : Option VerifiableInference.Desc.Part.MaskedSum.Heard}
    {H : VerifiableInference.Desc.Kinds.Head.HeardAll} (h : allOf F x q = some H) :
    allOf G x q = some H := by
  unfold allOf at h ⊢
  cases h1 : hidsAt F x.sW 9 with
  | none =>
    rw [h1] at h
    cases h
  | some a1 =>
    cases h2 : x.gp[1]? with
    | none =>
      rw [h1, h2] at h
      cases h
    | some a2 =>
      cases h3 : hidAt F x.wpl.sL with
      | none =>
        rw [h1, h2, h3] at h
        cases h
      | some a3 =>
        cases h4 : hidAt F x.wpl.sR with
        | none =>
          rw [h1, h2, h3, h4] at h
          cases h
        | some a4 =>
          cases h5 : hidsAt F x.sPv 7 with
          | none =>
            rw [h1, h2, h3, h4, h5] at h
            cases h
          | some a5 =>
            cases h6 : x.omV[1]? with
            | none =>
              rw [h1, h2, h3, h4, h5, h6] at h
              cases h
            | some a6 =>
              cases h7 : sumOf F x.tV x.tV.r 4 with
              | none =>
                rw [h1, h2, h3, h4, h5, h6, h7] at h
                cases h
              | some a7 =>
                cases h8 : sumOf F x.tN x.tN.r 2 with
                | none =>
                  rw [h1, h2, h3, h4, h5, h6, h7, h8] at h
                  cases h
                | some a8 =>
                  cases h9 : sumOf F x.tH (x.tH.r ++ x.rs.reverse) 2 with
                  | none =>
                    rw [h1, h2, h3, h4, h5, h6, h7, h8, h9] at h
                    cases h
                  | some a9 =>
                    rw [h1, h2, h3, h4, h5, h6, h7, h8, h9] at h
                    rw [hidsAt_fwd hL h1, hidAt_fwd hL h3, hidAt_fwd hL h4, hidsAt_fwd hL h5,
                      sumOf_fwd hL h7, sumOf_fwd hL h8, sumOf_fwd hL h9]
                    exact h

end VerifiableInference.Reads.Pass

#print axioms VerifiableInference.Reads.Pass.shown_fwd
#print axioms VerifiableInference.Reads.Pass.hidAt_fwd
#print axioms VerifiableInference.Reads.Pass.mapM_fwd
#print axioms VerifiableInference.Reads.Pass.hidsAt_fwd
#print axioms VerifiableInference.Reads.Pass.sumOf_fwd
#print axioms VerifiableInference.Reads.Pass.allOf_fwd
