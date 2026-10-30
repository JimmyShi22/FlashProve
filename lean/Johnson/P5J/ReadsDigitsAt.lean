-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/ReadsDigitsAt.lean: THE READING LAWS: WHAT THE LOOKUP ON THE DIGITS' SENTENCES READ OF
THE WITNESS IS BOOKED BY THE TABLE OF JOINTS, AT THE CLOSED CONSTANT, UNDER THE HEAD `AtMgA`.

Why. The lookup's files say which components of the witness their sentences read
(`readsK3`, Johnson/Desc/First/Look/K3FillReads.lean) and leave open whether readsK3 i ⊆
Item.reads i: left to a test in the files that fill the letters (Johnson/P5J/), since it hangs on
L.seat against the numbers N. Here that inclusion is shown for the digits' list, and spent twice.
  `readsDig_booked`: each component that `readsDig` names at segment l is the message or the pad of
    a tenant of every list T that holds what segment l sends at its moments 2, 0 and 1. From
    `k03_digits_seats` (Johnson/P5J/K03SeatsAt.lean: off the head's named test `At.k3SeatsB`).
  **`digits_reads_at`**: THE FIELD digits OF `HidReads` (Johnson/Desc/Sound/ReadsConstr.lean), to
    the letter: by `digitsPart_reads`; the table books `N.group k` for `constr k lookDigits`, and
    that is the three moments' lists by its text.
  **`worth_reads_at`**: THE RIDER `worth m j r`, AT 3 < j AND m < At.links.length:
    by `worthK3_reads`.

THE FENCE 3 < j. By the table's text the sentences of the lookup on the calls (j = 2 or 3) are
closed by the very next row: they ride past nothing. Those of the lookup on the digits ride past one
sub-protocol in all: at the output head's segment, opened at piece 8 and closed at piece 10. At 3 <
j the arm "on the calls" and the head's calls' own arm are not reached.

Premises: the head; hMg: the meaning beneath's own sentence at `worth` reads nothing of the witness
(at the closed base: by its text).
Limits. Implications between a sentence at two witnesses: that the sentence holds at some witness is
not shown. The head is a premise; a member of it is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction;
side library AtFullSide/Top/). Nothing on soundness.

-/
import Johnson.P5J.K03SeatsAt
import Johnson.P5J.K03Terms
import Johnson.Desc.Sound.ReadsConstr
import Johnson.Desc.First.Look.K3FillReads

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit Place)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Item Comp Meaning Numbers)
open VerifiableInference.Desc.First.Look (lookAt digAt k3SortAt)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **What the digits' sentences read is booked**, at every list that holds the three moments'. -/
theorem readsDig_booked (h : AtMgA o Z D r Zp Np cF x₀) {l : ℕ} (hl : l < 25) (T : List (ℕ × ℕ))
    (hT : ∀ t ∈ [2, 0, 1], ∀ s ∈ (h.toAtMg.𝔇 h.𝔇).N.sent l t, s ∈ T) :
    ∀ c ∈ readsDig (At.X Zp) (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).l3 l,
      c ∈ T.flatMap fun x => [Comp.msg ((h.toAtMg.𝔇 h.𝔇).arr x.1 x.2), Comp.pad x.1 x.2] := by
  intro c hc
  unfold readsDig at hc
  cases hx : digAt (At.X Zp) l with
  | none =>
    rw [hx] at hc
    simp at hc
  | some v =>
    rw [hx] at hc
    have hlook : lookAt (At.X Zp) l true = some v.1 := by
      unfold digAt at hx
      obtain ⟨x', h1, hx⟩ := Option.bind_eq_some_iff.1 hx
      obtain ⟨tl', -, hx⟩ := Option.bind_eq_some_iff.1 hx
      obtain ⟨h', -, hx⟩ := Option.map_eq_some_iff.1 hx
      subst hx
      exact h1
    obtain ⟨j, hj, hcj⟩ := List.mem_flatMap.1 hc
    obtain ⟨t, ht, hs⟩ := (k03_digits_seats h hl hlook).2.1 ⟨j, List.mem_range.1 hj⟩
    exact List.mem_flatMap.2 ⟨_, hT t ht _ hs, hcj⟩

/-- **THE FIELD digits OF `HidReads`, AT THE CONSTANT.** -/
theorem digits_reads_at (h : AtMgA o Z D r Zp Np cF x₀) :
    ∀ k a y w w', k < At.links.length →
      SameAt (h.toAtMg.𝔇 h.𝔇) At.links k .lookDigits w w' →
      (h.toAtMg.𝔇 h.𝔇).digitsPart k a y w → (h.toAtMg.𝔇 h.𝔇).digitsPart k a y w' := by
  intro k a y w w' hk hS hw
  have hk' : k < 25 := hk
  rw [k03_hD h] at hw ⊢
  refine digitsPart_reads _ _ _ k a y w w' (fun c hc => hS c ?_) hw
  refine List.mem_append_left _ (readsDig_booked h hk' _ ?_ c hc)
  intro t ht s hs
  show s ∈ (h.toAtMg.𝔇 h.𝔇).N.group k
  unfold Numbers.group
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl <;> simp [hs]

/-- The piece of a lookup on the calls is 2 or 3. -/
theorem sort_calls_early {X : Verify.Public} {m j : ℕ} (hs : k3SortAt X m j = some false) :
    j ≤ 3 := by
  unfold k3SortAt at hs
  split at hs
  · cases hs
  · split at hs
    · rename_i e
      have e' : j = VerifiableInference.Desc.K3.pieceAt X m false := by simpa using e
      rw [e']
      unfold VerifiableInference.Desc.K3.pieceAt
      split <;> simp
    · cases hs

/-- **THE RIDER `worth m j r`, AT 3 < j.** -/
theorem worth_reads_at (h : AtMgA o Z D r Zp Np cF x₀)
    (Mg : Meaning ProofFile.InstPub (Wit (CellsQ numsFull.rows (colsAt numsFull)) At.Tok MsgT))
    (hMg : ∀ m k r a y w w', Mg.worth m k r a y w → Mg.worth m k r a y w')
    {A : Type} {Fr : Frame} (ps : List Place)
    (get : A → ProofFile.InstPub × VerifiableInference.Desc.First.S) (Rch : ℕ → A × Fr.E.Str → Prop)
    (b : ℕ) :
    ∀ m j r, 3 < j → m < At.links.length →
      ReadsItemQR (h.toAtMg.𝔇 h.𝔇).arr (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) Mg) At.links ps
        get Rch b (.worth m j r) := by
  intro m j r hj hm a w w' _ _ _ _ _ hc hw
  have hm' : m < 25 := hm
  have hw0 : (mgAll (h.toAtMg.𝔇 h.𝔇) Mg).worth m j r (get a.1) (strsOf Fr a.2) w := hw
  show (mgAll (h.toAtMg.𝔇 h.𝔇) Mg).worth m j r (get a.1) (strsOf Fr a.2) w'
  rw [mgAll_worth] at hw0 ⊢
  have hne : ¬ (m = headLink (At.X Zp) ∧ j = 3) := fun e => by omega
  refine worthK3_reads (At.X Zp) (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).l3
    (fun u u' e => by
      show VerifiableInference.Desc.First.Look.Stored.msgWc u =
        VerifiableInference.Desc.First.Look.Stored.msgWc u'
      unfold VerifiableInference.Desc.First.Look.Stored.msgWc
      rw [e]) _ m j r _ _ w w' (fun h0 => ?_) (fun c hcc => ?_) hw0
  · have h1 : (if m = headLink (At.X Zp) ∧ j = 3 then _
        else Mg.worth m j r (get a.1) (strsOf Fr a.2) w) := h0
    rw [if_neg hne] at h1
    show (if m = headLink (At.X Zp) ∧ j = 3 then _
        else Mg.worth m j r (get a.1) (strsOf Fr a.2) w')
    rw [if_neg hne]
    exact hMg _ _ _ _ _ _ _ h1
  · have hcc' : c ∈ (match k3SortAt (At.X Zp) m j with
        | some true => readsDig (At.X Zp) (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).l3 m
        | some false => readsCalls (At.X Zp) (h.toAtMg.𝔇 h.𝔇).sent (h.toAtMg.𝔇 h.𝔇).l3 m
        | none => []) := hcc
    cases hs : k3SortAt (At.X Zp) m j with
    | none =>
      rw [hs] at hcc'
      simp at hcc'
    | some dg =>
      cases dg with
      | false => exact absurd (sort_calls_early hs) (by omega)
      | true =>
        rw [hs] at hcc'
        refine hc c (List.mem_append_left _ ?_)
        show c ∈ ((Item.worth m j r).tenants (h.toAtMg.𝔇 h.𝔇).N).flatMap _
        have et : (Item.worth m j r).tenants (h.toAtMg.𝔇 h.𝔇).N =
            (h.toAtMg.𝔇 h.𝔇).N.sent m 2 ++ (h.toAtMg.𝔇 h.𝔇).N.sent m 0 ++
              (h.toAtMg.𝔇 h.𝔇).N.sent m 1 := if_neg (by omega)
        rw [et]
        refine readsDig_booked h hm' _ ?_ c hcc'
        intro t ht s hs'
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
        rcases ht with rfl | rfl | rfl <;> simp [hs']

end P5J

#print axioms P5J.readsDig_booked
#print axioms P5J.digits_reads_at
#print axioms P5J.sort_calls_early
#print axioms P5J.worth_reads_at
