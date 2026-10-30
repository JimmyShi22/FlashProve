-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/TableFramesV.lean: THE TABLE MEETS THE FRAMES, SECOND PART: K1's members (the
opening, the reads, the digits, W's sending), K4, K5, K6 and K7. Under the head P5J.AtMgA. Nothing
is evaluated. K1's 52 members go over SeedsFree.lean's frames: "no seed's factor is spelt by three
words 0" falls to the frame's own test on the rounds, so 39 of them have no test on values in the
table, and the reads of the attention links and of the head's link (13) keep midV alone.

  `cell_g`, `cell_v`: from a cell's equation to the two equations that a frame asks. `nums_of`.
  `tab_opening`, `tab_digits`, `tab_digits_head`, `tab_reads_lay`, `tab_reads_att`,
    `tab_reads_head`, `tab_sendW`, `tab_k4` (the table's record of the place has an empty name and
    link 0: the step and the test read the plan, the sub-proof's plan and the group alone:
    k4StepW_reads, k4ValsV_reads), `tab_k5` (over another house's k5_frame), `tab_k6`, `tab_reply`:
    Both (TableFrames.lean) at these members' numbers.

Limits. As the frames'. midV (ReadsFrames.lean) ANSWERS false WHERE THE COMMITMENT's OWN DECISION
REFUSES: so at the 13 members that keep it the test on values is no test on values alone: whoever
pays the values there owes the commitment's acceptance once more. At the format's second hash function.
Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.TableFrames
import Johnson.AtFull.Shape.SeedsFree

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

/-- From a cell's equation to the equation on the step that a frame asks. -/
theorem cell_g {Z : ProofFile.Pub} {G : ProofFile.Ground} {n : Nat} {c : Cell}
    (h : Tab.cells Z G n = c) : Tab.g Z G n = c.1 := by
  unfold Tab.g
  rw [h]

/-- From a cell's equation to the equation on the test on values. -/
theorem cell_v {Z : ProofFile.Pub} {G : ProofFile.Ground} {n : Nat} {c : Cell}
    (h : Tab.cells Z G n = c) : Tab.vals Z G n = c.2 := by
  unfold Tab.vals
  rw [h]

/-! ## 1 K1 -/

theorem nums_of {G : ProofFile.Ground} {l : Nat} {Xl : Stages.LinkH}
    {q : Nat × Nat × Option (List Nat) × Option (List Nat)} (e2 : G.built[l]? = some Xl)
    (e3 : VerifiableInference.Desc.K1.linkNumbers G Xl = some q) : Tab.nums G l = some q := by
  unfold Tab.nums
  rw [e2]
  exact e3

theorem tab_opening (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    Both cF Zp Bs.G₀ 2 := fun ft => by
  obtain ⟨B', X, hp, P, -, e1, x1, x3, rfl, hf⟩ := opening_frame_free h
  obtain rfl := base_one hB e1
  have hc : Tab.cells Zp Bs.G₀ 2 = Tab.opening Zp Bs.G₀ :=
    cells_link Zp Bs.G₀ 0 1 (by omega) (by omega) rfl
  unfold Tab.opening at hc
  rw [x1] at hc
  simp only [x3] at hc
  exact hf ft _ _ (cell_g hc)

theorem tab_digits (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) (l : Nat)
    (hl : l < 24) : Both cF Zp Bs.G₀ (14 * l + 7) := fun ft => by
  obtain ⟨B', Xl, pr, reads, digits, -, e1, e2, e3, hf⟩ := digits_frame_free h l (by omega)
  obtain rfl := base_one hB e1
  have hn : 14 * l + IM.k1Ix l true + 2 = 14 * l + 7 := by
    rw [k1_no, if_neg (by omega)]
    rfl
  rw [hn] at hf
  have hc : Tab.cells Zp Bs.G₀ (14 * l + 7) = Tab.digits Zp Bs.G₀ l :=
    cells_link Zp Bs.G₀ l 6 hl (by omega) rfl
  unfold Tab.digits at hc
  rw [nums_of e2 e3] at hc
  exact hf ft _ _ (cell_g hc)

theorem tab_digits_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    Both cF Zp Bs.G₀ 344 := fun ft => by
  obtain ⟨B', Xl, pr, reads, digits, -, e1, e2, e3, hf⟩ := digits_frame_free h 24 (by omega)
  obtain rfl := base_one hB e1
  rw [show 14 * 24 + IM.k1Ix 24 true + 2 = 344 from rfl] at hf
  have hc : Tab.cells Zp Bs.G₀ 344 = Tab.digits Zp Bs.G₀ 24 :=
    cells_head Zp Bs.G₀ 7 (by omega) rfl
  unfold Tab.digits at hc
  rw [nums_of e2 e3] at hc
  exact hf ft _ _ (cell_g hc)

theorem tab_reads_lay (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) (k : Nat)
    (hk : k < 12) : Both cF Zp Bs.G₀ (14 * (2 * k) + 5) := fun ft => by
  obtain ⟨B', Xl, pd, reads, digits, hp, -, e1, e2, e3, e4, hf⟩ := reads_layers_frame_free h k hk
  obtain rfl := base_one hB e1
  have hc : Tab.cells Zp Bs.G₀ (14 * (2 * k) + 5) = Tab.reads Zp Bs.G₀ (2 * k) :=
    cells_link Zp Bs.G₀ (2 * k) 4 (by omega) (by omega) rfl
  unfold Tab.reads at hc
  rw [nums_of e2 e3] at hc
  simp only [show ((2 * k) % 2 == 0) = true from beq_iff_eq.2 (by omega), if_true,
    show 2 * k / 2 = k from by omega, e4] at hc
  exact hf ft _ _ (cell_g hc)

theorem tab_reads_att (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) (k : Nat)
    (hk : k < 12) : Both cF Zp Bs.G₀ (14 * (2 * k + 1) + 5) := fun ft => by
  obtain ⟨B', Xl, pd, reads, digits, A, -, e1, e2, e3, e4, hf⟩ := reads_att_frame_free h k hk
  obtain rfl := base_one hB e1
  have hc : Tab.cells Zp Bs.G₀ (14 * (2 * k + 1) + 5) = Tab.reads Zp Bs.G₀ (2 * k + 1) :=
    cells_link Zp Bs.G₀ (2 * k + 1) 4 (by omega) (by omega) rfl
  unfold Tab.reads at hc
  rw [nums_of e2 e3] at hc
  simp only [show ((2 * k + 1) % 2 == 0) = false from beq_eq_false_iff_ne.2 (by omega),
    Bool.false_eq_true, if_false, show (2 * k + 1) / 2 = k from by omega, e4] at hc
  exact hf ft _ _ (cell_g hc) fun s rs gs => by rw [cell_v hc]; rfl

theorem tab_reads_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    Both cF Zp Bs.G₀ 342 := fun ft => by
  obtain ⟨B', Xl, pd, reads, digits, -, e1, e2, e3, hf⟩ := reads_head_frame_free h
  obtain rfl := base_one hB e1
  have hc : Tab.cells Zp Bs.G₀ 342 = Tab.readsHead Zp Bs.G₀ :=
    cells_head Zp Bs.G₀ 5 (by omega) rfl
  unfold Tab.readsHead at hc
  rw [nums_of e2 e3] at hc
  exact hf ft _ _ (cell_g hc) fun s rs gs => by rw [cell_v hc]; rfl

theorem tab_sendW (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G : ProofFile.Ground) :
    Both cF Zp G 356 := fun ft => by
  obtain ⟨msg, -, e1, hf⟩ := sendW_frame_free h
  have hc : Tab.cells Zp G 356 = Tab.sendW Zp := cells_back Zp G 3 rfl
  unfold Tab.sendW at hc
  rw [e1] at hc
  exact hf ft _ _ (cell_g hc)

/-! ## 2 K4, K5, K6, K7 -/

theorem tab_k4 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) (g : Nat)
    (hg : g < 12) : Both cF Zp Bs.G₀ (28 * g + 4) := fun ft => by
  obtain ⟨B', y, e1, -, e3, e4, e5, hf⟩ := k4_frame_fit h g hg
  obtain rfl := base_one hB e1
  have hc : Tab.cells Zp Bs.G₀ (28 * g + 4) = Tab.k4 Bs.G₀ g := by
    rw [cells_link Zp Bs.G₀ (2 * g) 3 (by omega) (by omega) (by omega)]
    show (if (2 * g) % 2 == 0 then Tab.k4 Bs.G₀ (2 * g / 2) else Tab.k5 Zp (2 * g / 2)) = _
    rw [if_pos (beq_iff_eq.2 (by omega)), show 2 * g / 2 = g from by omega]
  unfold Tab.k4 at hc
  rw [e5] at hc
  refine hf ft _ _ ?_ fun s rs gs => ?_
  · rw [cell_g hc]
    exact congrArg liftO (k4StepW_reads
      (p := ⟨"", 0, 3, [], true, Bs.G₀.W.layers, y.2.hp, g⟩) (q := { y.2 with k3Runs := true })
      e3.symm rfl e4.symm)
  · rw [cell_v hc]
    exact congrFun (congrFun (k4ValsV_reads
      (p := ⟨"", 0, 3, [], true, Bs.G₀.W.layers, y.2.hp, g⟩) (q := { y.2 with k3Runs := true })
      e3.symm rfl e4.symm) s) rs

theorem tab_k5 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G : ProofFile.Ground) (g : Nat)
    (hg : g < 12) : Both cF Zp G (28 * g + 18) := fun ft => by
  obtain ⟨a, -, e1, hf⟩ := ProofFile.Honest.K5.k5_frame h g hg
  have hc : Tab.cells Zp G (28 * g + 18) = Tab.k5 Zp g := by
    rw [cells_link Zp G (2 * g + 1) 3 (by omega) (by omega) (by omega)]
    show (if (2 * g + 1) % 2 == 0 then Tab.k4 G ((2 * g + 1) / 2)
      else Tab.k5 Zp ((2 * g + 1) / 2)) = _
    rw [if_neg (by simp), show (2 * g + 1) / 2 = g from by omega]
  unfold Tab.k5 at hc
  rw [e1] at hc
  exact hf ft _ _ (cell_g hc) fun s rs gs => by rw [cell_v hc]

theorem tab_k6 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G : ProofFile.Ground) :
    Both cF Zp G 341 := fun ft => by
  have hc : Tab.cells Zp G 341 = (Tab.headRow Zp G).at 4 := cells_head Zp G 4 (by omega) rfl
  exact (k6_frame h).2 ft _ _ (cell_g hc) fun s rs gs => by rw [cell_v hc]; rfl

theorem tab_reply (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) :
    Both cF Zp Bs.G₀ 338 := fun ft => by
  obtain ⟨B', -, e1, hf⟩ := reply_frame h
  obtain rfl := base_one hB e1
  have hc : Tab.cells Zp Bs.G₀ 338 = (Tab.headRow Zp Bs.G₀).at 1 :=
    cells_head Zp Bs.G₀ 1 (by omega) rfl
  exact hf ft _ _ (cell_g hc) fun s rs gs => by rw [cell_v hc]; rfl

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.tab_opening
#print axioms Johnson.AtFull.Shape.tab_digits
#print axioms Johnson.AtFull.Shape.tab_digits_head
#print axioms Johnson.AtFull.Shape.tab_reads_lay
#print axioms Johnson.AtFull.Shape.tab_reads_att
#print axioms Johnson.AtFull.Shape.tab_reads_head
#print axioms Johnson.AtFull.Shape.tab_sendW
#print axioms Johnson.AtFull.Shape.tab_k4
#print axioms Johnson.AtFull.Shape.tab_k5
#print axioms Johnson.AtFull.Shape.tab_k6
#print axioms Johnson.AtFull.Shape.tab_reply
#print axioms Johnson.AtFull.Shape.cell_g
#print axioms Johnson.AtFull.Shape.cell_v
#print axioms Johnson.AtFull.Shape.nums_of
