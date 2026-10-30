-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K4/Law/ValuesAtHead.lean: CONDITIONAL.

What is here. `Values` (Honest/Thread/Shape.lean) and `ValuesJ` (Honest/Thread/ShapeJV.lean) AT ONE MEMBER OF THE FEED-FORWARD LAYERS' OWN ROUNDS
(sub-protocol K4; member number k = 28 g + 4 of the first chain, under `LaidK4`), AT THE TABLE OF THE ROAD ON SHAPES
(`firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)`, Johnson/AtFull/Shape/), where the first chain's thread stands at the library's own values
(`lettersHead`, Honest/Thread/FirstHead.lean, at all its letters). All twelve members at once, in the text of the field for which this is
meant: Law/ValuesField.lean. FROM: the head h · hB (the table's base) · `LaidK4` (Law/SeatedHead.lean; `laid_head` has it under h at each of the
twelve) · half: the search of the prover's list of sides at K4's place finds K4's side · hf: where the table of falls is silent at the
member, so is `k4CoinZero`.

  `k4_lay_head`      wherever the thread stands in front of the member a layers' segment is open: out of the promise's test "look"
                     (`two_tests`, Law/LookOfPromise.lean; `nine_head`, Law/ElevenHead.lean)
  `k4_merged_head`   there the table's test on the merged point says yes: one step back (`thr_back_head`, Honest/Thread/ReachFacts.lean) and the
                     lookups' law on every accepting step of the member 28 g + 3 (`look_rest_link`, Honest/K3/Law/Thread/AtLink.lean). A law
                     on the verifier: it holds of any prover.
  `k4_cell_values`   the table's test on values at the member is `k4ValsV (parOf x)`: the lines of the library's `tab_k4`
  **`k4_layers_values`**   `Values` at the member · `k4_layers_valuesJ`: `ValuesJ`, at every Said and every first shape a₀

THE MEMBER's TEST ON VALUES READS NO VALUE THAT K4's SIDE SENDS (Law/ValuesAtMember.lean's head): cells, weights, tokens and look are free letters of half.

Limits. NOT WHOLLY OVER THE TRUNK: beside Law/ValuesAtMember.lean its cone holds ONE working file that is no row of laws.14: Law/TokensHead.lean
(`tokens_head`; all beneath it rows, by a reader's walk). WHOSE PREMISE "THE REQUEST's TOKENS FIT" IS: nobody's by name:
it hides in "the thread stands": `tokens_head` has it because the state is reached from the description's own first state and bears no mark, and
that first state is marked where the request's words fail: so at a request whose tokens do not fit the thread stands nowhere and the statements
are idle; that a served request passes is owed by whoever shows that the thread begins. THAT THE THREAD STANDS ANYWHERE, that the fall is ever silent:
not shown. On h: the side library AtFullSide proves, with no hypothesis, that h has a member at one place (AtFullSide.Top.headMember_zFull). Of h
together with half and hf no example has been through Lean. half: at the maker's prover `half_atPure_at` (Law/HalfAtPureBy.lean, no row) has it from
three premises on the filling's lots; at the filling of the term's base prover its payer is being typed by another pen of this house. hf:
`hf_head` (Law/HalfHead.lean) has it at every list of falls that holds `k4Fall`; that the list of record holds it is its keeper's. AT
`lettersHead`'s THREAD ALONE, not at any thread over the chain's list: what nails it there is that the two tests on the state are read off the
thread's form and its reach. THE FULL SIZE ALONE; the format's second hash function alone. Nothing on what any value is worth.
No property is claimed.
A LAW, NOT A PART: it rests on modules under Johnson/Goal/: no file that defines a part of the proof file's description may import this one.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.ElevenHead
import Johnson.Desc.ProofFile.Honest.K4.Law.FrontCount
import Johnson.Desc.ProofFile.Honest.K4.Law.TableFitsMember
import Johnson.Desc.ProofFile.Honest.K4.Law.TokensHead
import Johnson.Desc.ProofFile.Honest.K4.Law.ValuesAtMember
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.AtLink
import Johnson.AtFull.Shape.TableFramesV

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par seatS)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Desc.First.K4.RtPub (tokensFit)
open OnBytes.Road.K4 (parOf)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Claim Block)
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.Desc.First.FillK4 (lookLayB)
open VerifiableInference.Desc.Sound (MsgT mgAll_more_base)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead thr_back_head thr_pub)
open ProofFile.Honest.K4.SeatedHead (LaidK4)
open Johnson.AtFull.Shape (Tab.g Tab.vals Tab.cells Tab.k4 Tab.k5 firstZA ShA k4ValsV k4ValsV_reads mergedB cells_link cell_v
  base_one)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL on h, hB and `LaidK4`. The table's test on values at K4's member. -/
theorem k4_cell_values (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {k m g : ℕ} {x : Bool × Par}
    {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk) :
    ∀ s rs gs, Tab.vals Zp Bs.G₀ k s rs gs = k4ValsV (parOf x) s rs := by
  obtain ⟨Bs', base, O⟩ := h.laid.opened
  obtain rfl := base_one hB O.made
  have hg := Lh.lt
  have hc : Tab.cells Zp Bs.G₀ (28 * g + 4) = Tab.k4 Bs.G₀ g := by
    rw [cells_link Zp Bs.G₀ (2 * g) 3 (by omega) (by omega) (by omega)]
    show (if (2 * g) % 2 == 0 then Tab.k4 Bs.G₀ (2 * g / 2) else Tab.k5 Zp (2 * g / 2)) = _
    rw [if_pos (beq_iff_eq.2 (by omega)), show 2 * g / 2 = g from by omega]
  have ehp : Bs.G₀.W.G[g]? = some x.2.hp := by
    rw [O.W]
    exact Lh.hp
  have eP : Bs.G₀.W.layers = x.2.P := by
    rw [O.W]
    exact Lh.P.symm
  unfold Tab.k4 at hc
  rw [ehp] at hc
  intro s rs gs
  rw [Lh.num, cell_v hc]
  exact congrFun (congrFun (k4ValsV_reads
    (p := ⟨"", 0, 3, [], true, Bs.G₀.W.layers, x.2.hp, g⟩) (q := parOf x) eP rfl Lh.grp.symm) s) rs

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- CONDITIONAL on h, `LaidK4` and hT. Wherever the thread stands in front of the member a layers' segment is open. -/
theorem k4_lay_head {k m g : ℕ} {x : Bool × Par} {blk : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk) {c : Coins Bk} {s : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread k c s mm E) :
    ∃ a : LayOwn, s.here = .lay a := by
  obtain ⟨hH, Sx, Sd, -, -⟩ := nine_head h Lh
  obtain ⟨-, t2⟩ := two_tests (Dm := h.𝔇) (P5J.At.E Zp cF VerifiableInference.Desc.K13.Law.LFull)
    (Mg := (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).mgP) rfl
    (mgAll_more_base h.𝔇) hH (atK4_of_laid Lh) Sx Sd
    (fun q hq => thr_pub (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hT hq)
  cases ha : s.here with
  | lay a => exact ⟨a, rfl⟩
  | _ => simp [lookLayB, ha] at t2

/-- CONDITIONAL on h, `LaidK4` and hT. **WHEREVER THE THREAD STANDS IN FRONT OF THE MEMBER, the table's test on the merged point says yes.** -/
theorem k4_merged_head {k m g : ℕ} {x : Bool × Par} {blk : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk) {c : Coins Bk} {s : TS}
    {mm : Mid (Local W₀ Rc ProofFile.Inst Tr) X'} {E : Env}
    (hT : Thr (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread k c s mm E) :
    (s.look?.all fun fo => mergedB (parOf x).P fo) = true := by
  obtain ⟨a, ha⟩ := k4_lay_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Lh hT
  have hbd := (nine_head h Lh).border
  have hg := Lh.lt
  have e : s.look? = a.fo := by simp [S.look?, ha]
  rw [e]
  cases hfo : a.fo with
  | none => rfl
  | some fo =>
    have hk : k = (28 * g + 3) + 1 := by
      have := Lh.num
      omega
    subst hk
    obtain ⟨s₀, blk₃, hblk, -, hy⟩ :=
      thr_back_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (by omega) hT
    have eb : VerifiableInference.Desc.Sound.MgAt.borderOf (2 * g) false = 28 * g + 3 := by
      show 14 * (2 * g) + ((if false = true then 6 else 1) + (if 2 * g = 24 then 1 else 0)) + 2 =
        28 * g + 3
      rw [if_neg (by omega : ¬ 2 * g = 24), if_neg (by decide : ¬ false = true)]
      omega
    obtain ⟨hm, -⟩ := ProofFile.Honest.K3.Law.AtThr.look_rest_link h (2 * g) (by omega) blk₃
      (by rw [eb]; exact hblk) 0 s₀ s hy a fo ha hfo
    show mergedB (parOf x).P fo = true
    unfold mergedB
    cases hZ : (lastOf fo.zx (parOf x).P.y.h.la).toOption with
    | none => rfl
    | some Zq =>
      obtain ⟨ends, he, hv⟩ := hm _ Zq hZ
      rw [he]
      exact hv

/-- CONDITIONAL on h, hB, `LaidK4`, half and hf. **K4's MEMBER's TEST ON VALUES SAYS YES AT WHAT THE SIDE HAS PLAYED, AT THE TABLE OF THE ROAD ON
SHAPES.** -/
theorem k4_layers_values {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs) {k m g : ℕ}
    {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk)
    {cells : Tr → Cells} {weights : W₀ → Weights}
    {tokens : ProofFile.Inst → Array Nat} {look : K4Pub → List Fmt.Drawn → Forest.Heard}
    {fall : Nat → S → List Fmt.Drawn → Option String}
    (half : H.first.find? (fun z => z.place == IM.k4Place g) =
      some (k4Half cells weights tokens look (k4PubAt cF k x)))
    (hf : ∀ s ds, fall k s ds = none → k4CoinZero (k4PubAt cF k x) ds = none) :
    Values (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) fall k :=
  k4_values_of_tests _
    (k4SeatedA_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Lh (k4Pub_head h Lh) half)
    (fun _ _ _ _ hT => ⟨tokens_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Lh hT,
      k4_merged_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Lh hT⟩) hf
    (k4_cell_values h hB Lh)

/-- CONDITIONAL as `k4_layers_values`. The weaker form, at every Said and every first shape. -/
theorem k4_layers_valuesJ {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop) {k m g : ℕ}
    {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk)
    {cells : Tr → Cells} {weights : W₀ → Weights}
    {tokens : ProofFile.Inst → Array Nat} {look : K4Pub → List Fmt.Drawn → Forest.Heard}
    {fall : Nat → S → List Fmt.Drawn → Option String}
    (half : H.first.find? (fun z => z.place == IM.k4Place g) =
      some (k4Half cells weights tokens look (k4PubAt cF k x)))
    (hf : ∀ s ds, fall k s ds = none → k4CoinZero (k4PubAt cF k x) ds = none) (a₀ : ShA) :
    ValuesJ (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said
      (shapeJ (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) a₀)
      (firstZA (Tab.g Zp Bs.G₀) (Tab.vals Zp Bs.G₀)) fall k :=
  valuesJ_of _ Said (k4_layers_values h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hB Lh half hf)

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4_cell_values
#print axioms ProofFile.Honest.K4.k4_lay_head
#print axioms ProofFile.Honest.K4.k4_merged_head
#print axioms ProofFile.Honest.K4.k4_layers_values
#print axioms ProofFile.Honest.K4.k4_layers_valuesJ
