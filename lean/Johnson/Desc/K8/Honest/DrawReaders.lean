-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/- Johnson/Desc/K8/Honest/DrawReaders.lean: THE SMALLNESS TEST's DRAW AND THE READERS OF A SEGMENT's
RUNS OF CLAIMS: WHAT A SEGMENT's READERS ANSWER IN FRONT OF THE DRAW THEY ANSWER BEHIND IT, AT ALL
25 SEGMENTS, FROM THE HEAD `P5J.AtMgA` ALONE: for every item "forms" that the written tables hold
open in front of the draw. A joining of the library's own theorems; nothing new is shown of any run.
None of the library's goals.

  `fwd_of_blind` a reader that is `TlBlind` (Johnson/Desc/First/K8/BlindPub.lean) goes forward over
                   `Drawn`: the library's Reads.Pass.Fwd (Johnson/Desc/Reads/FormsPass.lean)
  **`readers_at_draw`** from the head, l ≤ 24: for every piece k < pcOf l, every name and every run
                   p of the table there: the reader of segment l in the head's data (its field Rd)
                   is TlBlind at p
  `forms_open_at` on the written tables: an item forms m k ρ that is open at the border drawAt l has
                   m = l and k < pcOf l
  **`k8_draw_readers_head`** the head · l < 25 · Drawn s s' · forms m k ρ open at drawAt l ⊢ for
                   every run p that the head's data name at m, k, ρ: Reads.Pass.Fwd at the reader of
                   segment m, at p, from s to s'
WHERE IT LAY: `readers_at_draw` is the field readers of the library's `BlindOwes`
(Johnson/P1K8R/BlindJoin.lean), which Johnson/P1K8R/BlindOwesAt.lean fills at the three sorts of
segment beside two premises (wt, fence) that this field does not use: its three terms stand here a
further time, without these premises.
By: `readers_const_layers`, `readers_const_attention`, `readers_const_head2`
(Johnson/P1K8R/ReadersAll.lean) · `k5_states_blind` (WalkK5.lean) · `k6_states_blind`,
`callerReaders_blind` (WalkK6.lean) · `headLink_at` (BlindOwesAt.lean) · `k8RidersB_full`,
`k8_row_full` (TableAtK8.lean: closed facts on the tables, by the kernel's evaluation) ·
IM.linksW_full (Johnson/IMR/K8Owed.lean).
TWO DEVICES STAND IN IT, as in the library's Johnson/P1K8R/BlindOwesAt.lean: `set_option
maxHeartbeats 1000000` · `attribute [-instance] Inst.Model.Scl.ref`.
Limits. At OnBytes.secondHashFunction alone. A member of the head `AtMgA` is proved at `storedPublicFiles` and `zGap` alone
(at secondHashFunction; side library AtFullSide/Top/). The item "small",
which the draw itself opens, is not open in front and does not ride here. Nothing on the sentence
"weights" (the letter wt). No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.P1K8R.BlindOwesAt
import Johnson.P1K8R.TableAtK8
import Johnson.IMR.K8Owed
import Johnson.IMR.HandsDef
import Johnson.Desc.Reads.FormsPass

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S Item flatPlacesOf openSets start)
open VerifiableInference.Desc.First.K8 (TlBlind Drawn drawAt)
open ProofFile (Cl)
open P5J (AtMgA)
open _root_.P1K8T (pcOf ixOf headLink_at readers_const_layers readers_const_attention
  readers_const_head2 k5_states_blind k6_states_blind callerReaders_blind k8RidersB_full k8RidersAt
  k8ItemSort k8_row_full)

/-- A reader that has one value in front of the draw's yes and behind it answers behind what it
answers in front. -/
theorem fwd_of_blind {Rd : K9.Readers} {piece : ℕ} {run : String}
    (hb : TlBlind (Rd.forms piece run)) {s s' : S} (hD : Drawn s s') :
    Reads.Pass.Fwd Rd piece run s s' := fun R hR => by
  rw [hb s s' hD]
  exact hR

section
variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **FROM THE HEAD ALONE, AT EACH OF THE 25 SEGMENTS: the readers of the runs in front of the
draw's piece are blind to the draw.** -/
theorem readers_at_draw (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {l : ℕ} (hl : l ≤ 24) :
    ∀ k ρ, k < pcOf l → ∀ p ∈ h.𝔇.runs l k ρ, TlBlind ((h.𝔇.Rd l).forms p.1 p.2) := by
  obtain ⟨Bs, bs, O⟩ := h.laid.opened
  rcases Nat.lt_or_ge l 24 with h24 | h24
  · rcases Nat.even_or_odd' l with ⟨g, rfl | rfl⟩
    · exact readers_const_layers _ _ _ _ _ _ _ _ _ _ _ _ _ _ h.scope h.reads O (headLink_at h) O.W
        g (by omega)
    · exact readers_const_attention _ _ _ _ _ _ _ _ _ _ _ _ _ _ h.scope h.reads O (headLink_at h)
        O.W g (by omega) (k5_states_blind h.scope h.reads O g (by omega))
  · obtain rfl : l = 24 := Nat.le_antisymm hl h24
    exact readers_const_head2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ h.scope h.reads O (headLink_at h)
      callerReaders_blind (k6_states_blind h.scope h.reads O)

end

/-- **On the written tables: an item "forms" that is open in front of segment l's draw is the
segment's own, at a piece in front of the draw's.** -/
theorem forms_open_at {l : ℕ} (hl : l ≤ 24) {m k : ℕ} {ρ : String}
    (ho : Item.forms m k ρ ∈ IM.openAt IM.linksW IM.placesW (drawAt l)) :
    m = l ∧ k < pcOf l := by
  have hR := List.all_eq_true.1 k8RidersB_full l (List.mem_range.2 (Nat.lt_succ_of_le hl))
  unfold k8RidersAt at hR
  have ho' : Item.forms m k ρ ∈ (openSets linksFull (flatPlacesOf linksFull true)
      (start linksFull))[ixOf l]?.getD [] := by
    have e := ho
    unfold IM.openAt IM.placesW at e
    rw [IM.linksW_full] at e
    exact e
  obtain ⟨r1, -, r3⟩ := k8_row_full hl
  have hn : (!(insL linksFull (flatPlacesOf linksFull true) (ixOf l)).contains
      (Item.forms m k ρ)) = true := by
    unfold insL
    rw [r1, r3]
    simp
  have hs := List.all_eq_true.1 hR (Item.forms m k ρ) (List.mem_filter.2 ⟨ho', hn⟩)
  simp only [k8ItemSort, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hs
  exact hs

section
variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **WHAT A SEGMENT's READERS ANSWER IN FRONT OF THE SMALLNESS TEST's DRAW THEY ANSWER BEHIND
IT.** -/
theorem k8_draw_readers_head (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀) {l : ℕ} (hl : l < 25)
    {s s' : S} (hD : Drawn s s') (m k : ℕ) (ρ : String)
    (ho : Item.forms m k ρ ∈ IM.openAt IM.linksW IM.placesW (drawAt l)) :
    ∀ p ∈ h.𝔇.runs m k ρ, Reads.Pass.Fwd (h.𝔇.Rd m) p.1 p.2 s s' := by
  obtain ⟨rfl, hk⟩ := forms_open_at (by omega : l ≤ 24) ho
  exact fun p hp => fwd_of_blind (readers_at_draw h (by omega) k ρ hk p hp) hD

end

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.fwd_of_blind
#print axioms VerifiableInference.Desc.First.K8.Honest.readers_at_draw
#print axioms VerifiableInference.Desc.First.K8.Honest.forms_open_at
#print axioms VerifiableInference.Desc.First.K8.Honest.k8_draw_readers_head
