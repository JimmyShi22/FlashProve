-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/FourBehindDigits.lean: THE CLAUSES «four» AND «ents4» OF A LINK's Ok (`OkCore`, OkOne.lean beside this file) BEHIND AN ACCEPT OF THE
SEATED LOOKUP ON THE APPROXIMATE RANGE PROOF's DIGITS, THE STEP WITHOUT A ROUND BEHIND IT INCLUDED. Theorems on the decisions' texts.

Why. `k3_digits_four` (Johnson/Top/H/Keep/Four8Slots.lean) has both clauses' bodies at an accept of `K3.block`'s decision at the digits' seat.
What is seated in the first chain is `K3.theStated`'s value: that block, and behind it a step without a round. This file carries the two bodies over that step,
and brings them to the letters of `OkCore`: the snapshot `fixed9` and the reader π of the structure.

What is said.
  `putFork_tl`, `quietAt_tl`: laying a ledger, and the step behind the digits' rounds, leave the structure of the approximate range proof.
  `four_behind_digits`: **a yes of `K3.theStated`'s value at the digits' address, from a state s whose ledger F is there and has its sizes, to a state c ⊢ there
    are g, G: c's structure has heard g; c's ledger is G, with its sizes; no form of `four8 tl g` names an entry; at every ledger H later than G each slot
    of each form of `four8 tl g` lies in the leaves' window or is filled in H.**
  `four_fixed`: so, at q := `fixed9 φ c` and a reader π with π (φ s) = (s.tl?.map (blank u), s.funs?): `OkCore`'s clauses four and ents4, to the letter.

Limits. On the decision alone: nothing on «reached». **The ledger's sizes in front (s.fork? = some F, Sized F) are a premise.** No state is shown at
which the lookup accepts. It holds right behind the seated sub-protocol: at the head's link the merge stands between it and the batching. Nothing on soundness.

-/
import Johnson.Top.H.Keep.Four8Slots
import Johnson.Desc.First.Look.K3DigitsSeatedLeaves
import Johnson.Desc.First.Batch.BlindK3
import Johnson.Desc.First.Link.Law.OkOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model
open OnBytes.PscRun (Sized Filled)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.K4Values (winOf)
open VerifiableInference.Desc.First.TailClaims.Law (blank)
open VerifiableInference.OnPublicFiles (theStated_yes_digits k3_digits_four quietAt_ledger decide_exact
        seatDigits_keeps later_planClaims)

/-- Laying a ledger leaves the structure. -/
theorem putFork_tl (s : S) (G : Fork) : (s.putFork G).tl? = s.tl? := by
  cases hh : s.here with
  | between => simp [S.putFork, S.tl?, hh]
  | fin _ => simp [S.putFork, S.tl?, hh]
  | mem _ => simp [S.putFork, S.tl?, hh]
  | lay a => simp [S.putFork, S.tl?, hh]
  | att a => simp [S.putFork, S.tl?, hh]
  | head a =>
    cases ho : a.opened with
    | false => simp [S.putFork, S.tl?, hh, ho]
    | true => simp [S.putFork, S.tl?, hh, ho]

/-- The step behind the digits' rounds leaves the structure. -/
theorem quietAt_tl (X : Verify.Public) (i : ℕ) (f : S → Except String S)
    (hf : K3.quietAt X i true = some f) (s t : S) (h : f s = .ok t) : t.tl? = s.tl? := by
  unfold K3.quietAt at hf
  simp only [if_true] at hf
  split at hf
  · obtain rfl := Option.some.inj hf
    obtain ⟨ah, c, ha, ho, e⟩ := K3.quietHead_ok X s t h
    rw [e]
    simp [S.tl?, ha]
  · split at hf <;> split at hf <;>
      (obtain ⟨_, -, rfl⟩ := Option.map_eq_some_iff.1 hf
       obtain ⟨F, hF, -, e⟩ := K3.quietDigits_ok _ _ s t h
       rw [e]
       exact putFork_tl s _)

/-- **BEHIND A YES OF THE SEATED LOOKUP ON THE DIGITS.** -/
theorem four_behind_digits {Cl : Type} (claim : Aff → Cl) (readers : ℕ → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place) (B : Block S Cl)
    (h : K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true) (i : ℕ)
    (hi : a.link = some i) (hpc : a.piece = K3.pieceAt X i true) (s c : S) (rs : List Fmt.RoundView)
    (gs : List (List (ℕ × List UInt64))) (hd : B.decide s rs gs = .ok c) {F : Fork}
    (hF : s.fork? = some F) (hS : Sized F) :
    ∃ g G, c.tl?.bind (·.heard) = some g ∧ c.fork? = some G ∧ Sized G ∧
      (∀ tl, ∀ cl ∈ four8 tl g, cl.form.ents = #[]) ∧
      ∀ H, _root_.Fo.Later G H → ∀ tl, ∀ cl ∈ four8 tl g, ∀ x ∈ cl.form.slots.toList,
        K4Values.InWin (winOf g.leaves) x.1 ∨ Filled H x.1 := by
  obtain ⟨P', sent, laid, n, gs', s', -, hyes, hstep⟩ :=
    theStated_yes_digits claim readers X codes shape a B h hOk i hi hpc s c rs gs hd
  obtain ⟨g, G, h1, h2, h3, h4⟩ :=
    k3_digits_four claim a.piece laid sent P' [] s s' _ gs' hyes hF hS
  obtain ⟨F₁, y, hF₁, hn, e, hE⟩ :=
    decide_exact (K3.seatDigits claim) a.piece laid sent P' [] s s' _ gs' hyes
  obtain rfl : F = F₁ := Option.some.inj (hF.symm.trans hF₁)
  have hsome : ((K3.seatDigits claim).fork s).isSome = true := by
    rw [hF₁]
    rfl
  have hy : s'.fork? = some y.2 := by
    rw [e]
    exact seatDigits_keeps claim _ _ _ hsome hn
  obtain rfl : G = y.2 := Option.some.inj (h2.symm.trans hy)
  have hz : Sized y.2 := (hE hS).2.sized hS
  rcases hstep with rfl | ⟨f, hf, hfs⟩
  · exact ⟨g, _, h1, h2, hz, h3, h4⟩
  · obtain ⟨F₂, k, hF₂, hG₂, -⟩ := quietAt_ledger X i f hf s' c hfs
    obtain rfl : y.2 = F₂ := Option.some.inj (hy.symm.trans hF₂)
    refine ⟨g, _, ?_, hG₂, hz, h3, fun H hH => h4 H ((later_planClaims y.2 k).trans hH)⟩
    rw [quietAt_tl X i f hf s' c hfs]
    exact h1

/-- **OkCore's CLAUSES four AND ents4, TO THE LETTER, AT WHAT IS FIXED BEHIND THAT YES.** -/
theorem four_fixed {α : Type} (π : α → Option HTailF2 × Option (Array HFun)) (φ : S → α)
    (u : HTailF2) (hπ : ∀ s, π (φ s) = (s.tl?.map (blank u), s.funs?)) {c : S}
    {g : Forest.Heard} {G : Fork} (h1 : c.tl?.bind (·.heard) = some g) (h2 : c.fork? = some G)
    (hz : Sized G) (h3 : ∀ tl, ∀ cl ∈ four8 tl g, cl.form.ents = #[])
    (h4 : ∀ tl, ∀ cl ∈ four8 tl g, ∀ x ∈ cl.form.slots.toList,
      K4Values.InWin (winOf g.leaves) x.1 ∨ Filled G x.1) :
    (∀ v tlb g', (fixed9 φ c).2 = some v → (π (fixed9 φ c).1).1 = some tlb →
      tlb.heard = some g' → Sized v.F ∧ ∀ cl ∈ four8 tlb g', ∀ x ∈ cl.form.slots.toList,
        K4Values.InWin (winOf g'.leaves) x.1 ∨ Filled v.F x.1) ∧
      ∀ tlb g', (π (fixed9 φ c).1).1 = some tlb → tlb.heard = some g' →
        ∀ cl ∈ four8 tlb g', ∀ x ∈ cl.form.ents.toList, Row4 tlb x.tree x.row := by
  have key : ∀ tlb g', (π (fixed9 φ c).1).1 = some tlb → tlb.heard = some g' → g' = g := by
    intro tlb g' ht hg
    have e : (π (fixed9 φ c).1).1 = c.tl?.map (blank u) := by
      show (π (φ c)).1 = _
      rw [hπ]
    rw [e] at ht
    obtain ⟨tl, htl, rfl⟩ := Option.map_eq_some_iff.1 ht
    rw [htl] at h1
    have h1' : tl.heard = some g := h1
    have hg' : tl.heard = some g' := hg
    exact Option.some.inj (hg'.symm.trans h1')
  refine ⟨fun v tlb g' hv ht hg => ?_, fun tlb g' ht hg cl hcl x hx => ?_⟩
  · obtain rfl := key tlb g' ht hg
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.1 hv
    have e : (pubOf b).F = G := Option.some.inj ((K9.get_fork c b hb).symm.trans h2)
    rw [e]
    exact ⟨hz, h4 tlb⟩
  · obtain rfl := key tlb g' ht hg
    rw [h3 tlb cl hcl] at hx
    exact absurd hx (by simp)

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.putFork_tl
#print axioms VerifiableInference.Desc.LinkJoin.quietAt_tl
#print axioms VerifiableInference.Desc.LinkJoin.four_behind_digits
#print axioms VerifiableInference.Desc.LinkJoin.four_fixed
