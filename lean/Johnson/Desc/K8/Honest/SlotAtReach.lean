-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/SlotAtReach.lean: THE SMALLNESS TEST: THE WINDOW OF THE LEDGER's SLOTS THAT
THE DIGITS' LOOKUP LAYS IN THE TEST's DATA ENDS INSIDE THE LEDGER's NUMBER OF SLOTS (tl.slotB ≤
G.ns), AT EVERY STATE THAT THE FIRST CHAIN's OWN BLOCKS REACH IN FRONT OF THE BATCHING OF ONE OF THE
24 SEGMENTS IN FRONT OF THE HEAD's, IN THE GOALS' SCOPE. The first of the two facts of `FrontLeftN`
(Johnson/Desc/ProofFile/Honest/K8/RestJoinOk.lean). Lemmas; none of the library's goals.

  `seatDigits_slot` what the digits' seat lays as the window's end is the next free slot of the
                   ledger that it lays
  **`slot_behind_digits`** behind a yes of the seated lookup on the digits, from a ledger with its
                   sizes: a ledger is open, the data are there, and the window's end is at most the
                   ledger's number of slots
  **`slot_at_batch`** at a reached state, l < 24: tl.slotB ≤ G.ns
By: the library's `decide_left_some` (Johnson/Top/H/Keep/K3LeftAnyWords.lean) · `left_room`
(K3LeftWindow.lean: all the lookup's slots are there) · PadLeft.next · `theStated_yes_digits`,
`quietAt_ledger`, `quietAt_tl`, `seatDigits_keeps`, `sizes_behind_digits`, `piece_digits` · IM.k3_of
· `sized_at_batch` (Johnson/P1K8R/HeardAtBatch.lean).
WRITTEN A FURTHER TIME: the walks of `slot_behind_digits` and `slot_at_batch` are those of the
library's `leftOn_behind_digits` and `leftOn_digits_behind`
(Johnson/Desc/First/Link/Law/KxAtFront.lean), whose statements do not hand the window's end;
`seatDigits_slot`'s cases are those of `seatDigits_reads` (Johnson/Desc/First/Look/K3SeatLaw.lean).
ONE DEVICE STANDS IN IT, as in the library's KxAtFront.lean: `attribute [-instance]
Inst.Model.Scl.ref`.
Limits. NOTHING AT THE HEAD's SEGMENT: there one block more (the merge, member 346) stands between
the lookup's member and the batching's. Nothing on the window's beginning. IN SCOPE ALONE: under an
opening of the description and its test on its plan; the first chain; the family of states from the
description's own first state. Nothing says that any state is reached. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.First.Link.Law.KxAtFront
import Johnson.Top.H.Keep.K3LeftWindow
import Johnson.Desc.PlanPasses
import Johnson.P1K8R.HeardAtBatch

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model
open OnBytes.PscRun (Sized)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.OnPublicFiles (decide_left_some theStated_yes_digits quietAt_ledger
        seatDigits_keeps left_room)
open VerifiableInference.Desc.LinkJoin (quietAt_tl sizes_behind_digits piece_digits)
open Johnson.Desc.First.Walk.Tied (Reach StepYes stepYes_decide)
open OnBytes.Road.K4 (reach_pred)

/-- What the digits' seat lays as the end of the window is the next free slot of the ledger that it
lays. -/
theorem seatDigits_slot {Cl : Type} (claim : Aff → Cl) (s : S) (g : Forest.Heard) (G : Fork)
    (hf : ((K3.seatDigits claim).fork s).isSome = true) :
    (((K3.seatDigits claim).put s g G).tl?.map (·.slotB)) = some G.next := by
  simp only [K3.seatDigits] at hf ⊢
  cases hh : s.here with
  | between => simp [S.fork?, hh] at hf
  | fin _ => simp [S.fork?, hh] at hf
  | mem _ => simp [S.fork?, hh] at hf
  | lay a => simp [S.tl?, S.fork?, S.putTl, S.putFork, hh]
  | att a => simp [S.tl?, S.fork?, S.putTl, S.putFork, hh]
  | head a =>
    cases ho : a.opened with
    | false => simp [S.fork?, hh, ho] at hf
    | true => simp [S.tl?, S.fork?, S.putTl, S.putFork, hh, ho]

/-- **BEHIND A YES OF THE SEATED LOOKUP ON THE DIGITS THE WINDOW ENDS INSIDE THE LEDGER's NUMBER OF
SLOTS.** -/
theorem slot_behind_digits {Cl : Type} (claim : Aff → Cl) (readers : ℕ → Option (K3.Readers S))
    (X : Verify.Public) (codes : Codes) (shape : Params.ReqShape) (a : Place) (B : Block S Cl)
    (h : K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true) (i : ℕ)
    (hi : a.link = some i) (hpc : a.piece = K3.pieceAt X i true) (s c : S)
    (rs : List Fmt.RoundView) (gs : List (List (ℕ × List UInt64))) (hd : B.decide s rs gs = .ok c)
    {F : Fork} (hF : s.fork? = some F) (hS : Sized F) :
    ∃ G n, c.fork? = some G ∧ c.tl?.map (·.slotB) = some n ∧ n ≤ G.ns := by
  obtain ⟨P', sent, laid, n, gs', s', hP, hyes, hstep⟩ :=
    theStated_yes_digits claim readers X codes shape a B h hOk i hi hpc s c rs gs hd
  cases hsh : P'.shape with
  | none =>
    exfalso
    obtain ⟨_, x, _, _, hx, _⟩ := VerifiableInference.OnPublicFiles.decide_ok (K3.seatDigits claim)
      a.piece laid sent P' [] s s' _ gs' hyes
    unfold K3.hear at hx
    simp [hsh] at hx
  | some hh =>
    obtain ⟨F₁, y, hF₁, hn, e, hE⟩ := decide_left_some (K3.seatDigits claim) a.piece laid sent P' []
      (K3.seatDigits_reads claim) hh hsh Reading.gl 5 s s' _ gs' hyes
    obtain rfl : F = F₁ := Option.some.inj (hF.symm.trans hF₁)
    obtain ⟨rs', hL⟩ := hE hS
    have hsome : ((K3.seatDigits claim).fork s).isSome = true := by
      rw [hF₁]
      rfl
    have hy : s'.fork? = some y.2 := by
      rw [e]
      exact seatDigits_keeps claim _ _ _ hsome hn
    have hb : s'.tl?.map (·.slotB) = some y.2.next := by
      rw [e]
      exact seatDigits_slot claim _ _ _ hsome
    have hle : y.2.next ≤ y.2.ns := by
      rw [hL.padLeft.next]
      exact left_room hL
    rcases hstep with rfl | ⟨f, hf, hfs⟩
    · exact ⟨y.2, y.2.next, hy, hb, hle⟩
    · obtain ⟨F₂, k, hF₂, hG₂, -⟩ := quietAt_ledger X i f hf s' c hfs
      obtain rfl : y.2 = F₂ := Option.some.inj (hy.symm.trans hF₂)
      refine ⟨_, y.2.next, hG₂, ?_, hle⟩
      rw [quietAt_tl X i f hf s' c hfs]
      exact hb

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **AT EVERY STATE REACHED IN FRONT OF THE BATCHING OF A SEGMENT l < 24.** -/
theorem slot_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 24) {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + 9) (z, s)) {tl : HTailF2} {G : Fork}
    (ht : s.tl? = some tl) (hG : s.fork? = some G) : tl.slotB ≤ G.ns := by
  have hp : ∀ b ∈ c.blocksInOrder, b.planOk = true := by
    have e := O.desc
    subst e
    exact (Keeps.planOk_blocks _ hOk).1
  have i3 : IM.k3Ix l true = 6 := by
    show (if true = true then 6 else 1) + (if l = 24 then 1 else 0) = 6
    rw [if_neg (by omega : ¬ l = 24)]
    rfl
  have h1 : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + IM.k3Ix l true + 2 + 1) (z, s) := by
    rw [i3]
    exact h
  obtain ⟨Lk, b, b', e1, e2, e3, e4⟩ := IM.k3_of hS hR O l (by omega) true
  obtain ⟨z', s₀, s'', b₀, e, hr, hb, hy⟩ := reach_pred h1
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e
  have hf : c.blocksInOrder[14 * l + IM.k3Ix l true + 2]? = some b := by
    rw [← IM.flatIx_scope hS hR O (by omega : l ≤ 24) (IM.k3Ix l true)]
    exact IM.hear_at_flat e1 e2
  obtain rfl : b = b₀ := Option.some.inj (hf.symm.trans hb)
  obtain ⟨rs, gs, hd⟩ := stepYes_decide hy
  have hd' := ((IM.yes_alone e4 (fun h => nomatch h) s₀ _ rs gs).1 hd).1
  have hOk' : b'.planOk = true := by
    rw [← IM.alone_planOk e4]
    exact hp b (List.mem_of_getElem? hf)
  have h7 : 7 ≤ (IM.k3Place l true).piece := by
    show 7 ≤ (if true = true then 6 else 1) + (if l = 24 then 1 else 0) + 1
    simp
  have hpc := piece_digits _ _ _ _ _ _ b' e3 l rfl h7
  obtain ⟨G₀, hG₀, hz⟩ :=
    (sizes_behind_digits _ _ _ _ _ _ b' l e3 hOk' rfl hpc s₀ rs gs _ hd').pulls
      (_root_.P1K8.sized_at_batch hS hR O hOk hl h)
  obtain ⟨G', n, a1, a2, a3⟩ :=
    slot_behind_digits _ _ _ _ _ _ b' e3 hOk' l rfl hpc s₀ _ rs gs hd' hG₀ hz
  obtain rfl : G' = G := Option.some.inj (a1.symm.trans hG)
  rw [ht] at a2
  obtain rfl : tl.slotB = n := Option.some.inj a2
  exact a3

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.seatDigits_slot
#print axioms VerifiableInference.Desc.First.K8.Honest.slot_behind_digits
#print axioms VerifiableInference.Desc.First.K8.Honest.slot_at_batch
