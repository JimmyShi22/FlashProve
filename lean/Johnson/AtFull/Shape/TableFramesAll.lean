-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/TableFramesAll.lean: ONE TABLE MEETS THE FRAMES' EQUATIONS AT 333 OF THE 358
NUMBERS AT ONCE. Behind the batching, the one equation, the closing; and the sum. Under the head
P5J.AtMgA. One closed count is evaluated by the kernel.

  1 `tab_behind_att`, `tab_behind_head`, `tab_behind_lay`, `tab_equation`, `tab_equation_head`,
    `tab_close`, `tab_close_head`: Both (TableFrames.lean) at these members' numbers.
  2 `framed` : Nat → Bool: the numbers of the members at which both premises are shown: with code.
    `framed_count`: below 358 they are 333: all but the 25 batching members. **`table_frames`**:
    under the head, with Bs what the maker's own ProofFile.baseOf returns at the public part: for every n
    with framed n = true: Both cF Zp Bs.G₀ n: for every ft: Carries and Returns at n at firstZA
    (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀).

What it adds to the seats' frames: each of these says "for all g and vals that meet my equation at
my one number". Here g and vals are two named terms, the same at all 333 numbers.

Limits. 333 OF 358: not the batching's 25 (TableBatch.lean has them in a weaker form). That a member
stands at each number below 358 is another file's law (Numbers.lean: flat_len). The rule for
acceptance (accepted_of_shape, Johnson/Desc/ProofFile/Honest/Thread/Shape.lean) asks more: both
premises at every member; that the run on shapes returns; the fits; the values; the first state's
shape. THE TABLE's TEST "ON VALUES" AT THE ONE EQUATION (oneV: 14 l + 11, l < 24, and 349) IS MORE
THAN A TEST ON VALUES: it asks (usedOf s).isSome and four tests on sizes besides (ValsBool.lean's
head); at the closings it is closeInOrdB (CloseInOrder.lean). No law that this file reaches shows
oneV to accept. closeInOrdB is shown to accept at every state reached in front of a closing
(closeInOrdB_reached, closeInOrdB_at_closing: CloseInOrder.lean; "reached" in that file's own form;
these laws do not show that a state is reached there); nothing here spends that. No state is shown
at which a step returns. That the head has a member is shown in scope, where the reader returns and
`protocolDataWellFormed` accepts (`head_of_live`, Johnson/P5J/HeadOfLive.lean); that these three hold together, at
two named sets of public files, in a side library. At the format's second hash function. Nothing on
soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.TableSwitch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link Place KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open OnBytes.Maker (WholeD)
open IM (subAt)
open P5J (AtMgA F0T)
open ProofFile.Honest (Carries Returns)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place} {Bs : ProofFile.PureBase}

/-! ## 1 Behind the batching, the one equation, the closing -/

/-- Behind the batching of an attention link: both premises at 14 (2 k + 1) + 10, at the table's own
cell. -/
theorem tab_behind_att (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) (k : Nat)
    (hk : k < 12) : Both cF Zp Bs.G₀ (14 * (2 * k + 1) + 10) := fun ft => by
  obtain ⟨B', Xl, w, e1, e2, e3, hf⟩ := behind_frame h (2 * k + 1) (by omega)
    (by rw [sub_odd]; exact fun e => nomatch e)
  obtain rfl := base_one hB e1
  rw [show VerifiableInference.Desc.LinkJoin.batchAt P5J.fullLinks P5J.At.ps (2 * k + 1) + 1 =
    14 * (2 * k + 1) + 10 from by rw [batch_no _ (by omega), if_neg (by omega)]] at hf
  have hc : Tab.cells Zp Bs.G₀ (14 * (2 * k + 1) + 10) = Tab.behind Zp Bs.G₀ (2 * k + 1) :=
    cells_link Zp Bs.G₀ (2 * k + 1) 9 (by omega) (by omega) rfl
  unfold Tab.behind at hc
  rw [e2, e3] at hc
  simp only [show ((2 * k + 1) % 2 == 0) = false from beq_eq_false_iff_ne.2 (by omega),
    Bool.false_and, Bool.false_eq_true, if_false] at hc
  exact hf ft _ _ (cell_g hc) fun s rs gs => by rw [cell_v hc]

/-- Behind the batching of the head's link: both premises at 348. -/
theorem tab_behind_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    Both cF Zp Bs.G₀ 348 := fun ft => by
  obtain ⟨B', Xl, w, e1, e2, e3, hf⟩ := behind_frame h 24 (by omega) (fun e => nomatch e)
  obtain rfl := base_one hB e1
  rw [show VerifiableInference.Desc.LinkJoin.batchAt P5J.fullLinks P5J.At.ps 24 + 1 = 348 from by
    rw [batch_no _ (by omega), if_pos rfl]] at hf
  have hc : Tab.cells Zp Bs.G₀ 348 = Tab.behind Zp Bs.G₀ 24 :=
    cells_head Zp Bs.G₀ 11 (by omega) rfl
  unfold Tab.behind at hc
  rw [e2, e3] at hc
  exact hf ft _ _ (cell_g hc) fun s rs gs => by rw [cell_v hc]; rfl

/-- Behind the batching of a layers' link: both premises at 14 (2 k) + 10. -/
theorem tab_behind_lay (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) (k : Nat)
    (hk : k < 12) : Both cF Zp Bs.G₀ (14 * (2 * k) + 10) := fun ft => by
  obtain ⟨B', Xl, hp, w, e1, e2, e4, e3, hf⟩ := layers_frame h k hk
  obtain rfl := base_one hB e1
  rw [show VerifiableInference.Desc.LinkJoin.batchAt P5J.fullLinks P5J.At.ps (2 * k) + 1 =
    14 * (2 * k) + 10 from by rw [batch_no _ (by omega), if_neg (by omega)]] at hf
  have hc : Tab.cells Zp Bs.G₀ (14 * (2 * k) + 10) = Tab.behind Zp Bs.G₀ (2 * k) :=
    cells_link Zp Bs.G₀ (2 * k) 9 (by omega) (by omega) rfl
  unfold Tab.behind at hc
  rw [e2, e3] at hc
  simp only [show ((2 * k) % 2 == 0) = true from beq_iff_eq.2 (by omega),
    show (2 * k != 24) = true from bne_iff_ne.2 (by omega), Bool.and_self, if_true,
    show 2 * k / 2 = k from by omega, e4] at hc
  exact hf ft _ _ (cell_g hc) fun s rs gs => by rw [cell_v hc]

/-- The one equation of a link below the head's: both premises at 14 l + 11. General in the ground:
the cell does not read it. -/
theorem tab_equation (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G : ProofFile.Ground)
    (l : Nat) (hl : l < 24) : Both cF Zp G (14 * l + 11) := fun ft => by
  obtain ⟨L, hL, hf⟩ := equation_frame h l (by omega)
  rw [(numbers_at h hl hL).2.2.1] at hf
  have hc : Tab.cells Zp G (14 * l + 11) = Tab.equation :=
    cells_link Zp G l 10 hl (by omega) rfl
  exact hf ft _ _ (cell_g hc) fun s rs gs => by rw [cell_v hc]; rfl

/-- The one equation of the head's link: both premises at 349. -/
theorem tab_equation_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G : ProofFile.Ground)
    : Both cF Zp G 349 := fun ft => by
  obtain ⟨L, hL, hf⟩ := equation_frame h 24 (by omega)
  rw [(numbers_head h hL).2.2.2.1] at hf
  have hc : Tab.cells Zp G 349 = Tab.equation := cells_head Zp G 12 (by omega) rfl
  exact hf ft _ _ (cell_g hc) fun s rs gs => by rw [cell_v hc]; rfl

/-- The closing of a link below the head's: both premises at 14 l + 12. -/
theorem tab_close (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G : ProofFile.Ground)
    (l : Nat) (hl : l < 24) : Both cF Zp G (14 * l + 12) := fun ft => by
  obtain ⟨p, Q, e1, e2, hf⟩ := close_frame_ord h l (by omega)
  rw [close_no, if_neg (by omega)] at hf
  have hc : Tab.cells Zp G (14 * l + 12) = Tab.close Zp l :=
    cells_link Zp G l 11 hl (by omega) rfl
  unfold Tab.close at hc
  rw [e1] at hc
  simp only [Option.bind_some, e2] at hc
  exact hf ft _ _ (cell_g hc) fun s rs gs => by rw [cell_v hc]

/-- The closing of the head's link: both premises at 350. -/
theorem tab_close_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G : ProofFile.Ground) :
    Both cF Zp G 350 := fun ft => by
  obtain ⟨p, Q, e1, e2, hf⟩ := close_frame_ord h 24 (by omega)
  rw [close_no, if_pos rfl] at hf
  have hc : Tab.cells Zp G 350 = Tab.close Zp 24 := cells_head Zp G 13 (by omega) rfl
  unfold Tab.close at hc
  rw [e1] at hc
  simp only [Option.bind_some, e2] at hc
  exact hf ft _ _ (cell_g hc) fun s rs gs => by rw [cell_v hc]

/-! ## 2 All together -/

/-- The numbers of the members at which both premises are shown at the table: with code. -/
def framed (n : Nat) : Bool :=
  if n == 0 then true
  else if n < 337 then
    let j := (n - 1) % 14
    j == 0 || j == 1 || j == 2 || j == 3 || j == 4 || j == 5 || j == 6 || j == 7 ||
      j == 9 || j == 10 || j == 11 || j == 12 || j == 13
  else if n < 353 then
    let j := n - 337
    j == 0 || j == 1 || j == 2 || j == 3 || j == 4 || j == 5 || j == 6 || j == 7 || j == 8 ||
      j == 9 || j == 11 || j == 12 || j == 13 || j == 14 || j == 15
  else n == 353 || n == 354 || n == 355 || n == 356 || n == 357

/-- How many they are. -/
theorem framed_count : ((List.range 358).filter framed).length = 333 := by decide +kernel

/-- **ONE TABLE MEETS THE FRAMES' EQUATIONS AT 333 NUMBERS AT ONCE**: under the head, at the maker's
own base: at every number that `framed` names (333 of the 358: not the 25 batchings), the frame's
two premises hold at the table's own steps and tests. -/
theorem table_frames (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) (n : Nat)
    (hn : framed n = true) : Both cF Zp Bs.G₀ n := by
  unfold framed at hn
  by_cases h0 : n = 0
  · subst h0
    exact tab_front h _
  rw [if_neg (by simpa using h0)] at hn
  by_cases h1 : n < 337
  · rw [if_pos h1] at hn
    obtain ⟨l, j, hl, hj, rfl⟩ : ∃ l j, l < 24 ∧ j < 14 ∧ n = 14 * l + j + 1 :=
      ⟨(n - 1) / 14, (n - 1) % 14, by omega, by omega, by omega⟩
    have ej : (14 * l + j + 1 - 1) % 14 = j := by omega
    simp only [ej, Bool.or_eq_true, beq_iff_eq] at hn
    obtain ⟨k, hk⟩ : ∃ k, l = 2 * k ∨ l = 2 * k + 1 := ⟨l / 2, by omega⟩
    rcases hn with ((((((((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) |
      rfl) | rfl) | rfl) | rfl)
    · exact tab_laid h _ l (by omega)
    · rcases hk with rfl | rfl
      · by_cases k0 : k = 0
        · subst k0
          exact tab_opening h hB
        · exact tab_switch_lay h hB k (by omega) (by omega)
      · exact tab_switch_att h hB k (by omega)
    · exact tab_calls h _ l hl
    · rcases hk with rfl | rfl
      · have := tab_k4 h hB k (by omega)
        rwa [show 28 * k + 4 = 14 * (2 * k) + 3 + 1 from by omega] at this
      · have := tab_k5 h Bs.G₀ k (by omega)
        rwa [show 28 * k + 18 = 14 * (2 * k + 1) + 3 + 1 from by omega] at this
    · rcases hk with rfl | rfl
      · exact tab_reads_lay h hB k (by omega)
      · exact tab_reads_att h hB k (by omega)
    · exact tab_draw h hB l hl
    · exact tab_digits h hB l hl
    · exact tab_look_digits h _ l hl
    · rcases hk with rfl | rfl
      · exact tab_behind_lay h hB k (by omega)
      · exact tab_behind_att h hB k (by omega)
    · exact tab_equation h _ l hl
    · exact tab_close h _ l hl
    · exact tab_shut h _ l hl
    · rcases hk with rfl | rfl
      · exact tab_cleared_lay h _ k (by omega)
      · exact tab_cleared_att h _ k (by omega)
  rw [if_neg h1] at hn
  by_cases h2 : n < 353
  · rw [if_pos h2] at hn
    obtain ⟨j, hj, rfl⟩ : ∃ j, j < 16 ∧ n = 337 + j := ⟨n - 337, by omega, by omega⟩
    simp only [show 337 + j - 337 = j from by omega, Bool.or_eq_true, beq_iff_eq] at hn
    rcases hn with ((((((((((((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) |
      rfl) | rfl) | rfl) | rfl) | rfl) | rfl)
    · exact tab_laid h _ 24 (by omega)
    · exact tab_reply h hB
    · exact tab_switch_head h hB
    · exact tab_calls_head h _
    · exact tab_k6 h _
    · exact tab_reads_head h hB
    · exact tab_draw_head h hB
    · exact tab_digits_head h hB
    · exact tab_look_head h _
    · exact tab_merge h hB
    · exact tab_behind_head h hB
    · exact tab_equation_head h _
    · exact tab_close_head h _
    · exact tab_shut_head h _
    · exact tab_cleared_head h _
  rw [if_neg h2] at hn
  simp only [Bool.or_eq_true, beq_iff_eq] at hn
  rcases hn with (((rfl | rfl) | rfl) | rfl) | rfl
  · exact tab_finish h hB
  · exact tab_test h _
  · exact tab_batt h _
  · exact tab_sendW h _
  · exact tab_seal h _

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.tab_behind_att
#print axioms Johnson.AtFull.Shape.tab_behind_head
#print axioms Johnson.AtFull.Shape.tab_behind_lay
#print axioms Johnson.AtFull.Shape.tab_equation
#print axioms Johnson.AtFull.Shape.tab_equation_head
#print axioms Johnson.AtFull.Shape.tab_close
#print axioms Johnson.AtFull.Shape.tab_close_head
#print axioms Johnson.AtFull.Shape.framed_count
#print axioms Johnson.AtFull.Shape.table_frames
#print axioms Johnson.AtFull.Shape.framed
