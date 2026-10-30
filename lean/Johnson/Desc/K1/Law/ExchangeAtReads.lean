-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/ExchangeAtReads.lean: **hback**: the binder hback of k01_fifty
(Johnson/Desc/K1/Law/K01Law.lean) at the wider meaning
`plus13 (d13 Dm) dk (mgAll Dm Mg₀)` and N := Dm.N, IN A POINTWISE FORM: at a link's reads, behind
the piece's accept and from inside the promise: what the table's row closes and reads holds in
front, if what it opens and reads holds behind.
THE ROW, by evaluation in Lean's kernel at all 25 links (`readsRow_full`; read off the print of
LookRowsAtReads.lean [not in this library], first): it closes items `formsT l j n`
alone; it opens `forms l j n`
for each of them; it reads `pin l 0` and `constr l small`; the public item `formsInT l j n` is tied
to an item open in front; and none of these items' runs is the one whose forms may name what is
ahead.
THE EXCHANGE, a run at a time: `formsTQ_of_step` (K1/Law/ExchangeStep.lean). PAID
HERE: `StatedIs` (`statedIs_of`: `Dm.St` is `Stated.of` by its make) · the public test `formsInT`
(off the promise) · `Rides` (`rides_of_rec` over `laterSend_k1Reads` and `laterGrows_k1Reads`) ·
that both states hold an open segment's part · the reader's ONE answer, from the weaker "what it
gave in front it gives behind" and the public test · `ArmCell` from `ArmCellIn` (`armCell_of_in`,
Sound/StatedCellIn.lean).
PREMISES. hlk : Dm.links = linksFull. AND FIVE AT THE PIECE's OWN TWO STATES AND THIS WITNESS ALONE,
behind the promise, "no mark" and the piece's accept:
  `ReadersStay` at each item closed (as in hpub_point) · `ArmCellIn` at each run (each sort of
  segment's own half) · `Dm.wt l` goes back (spent at the head's run "weights" alone) · `pin l 0`
  goes back · `constr l small` goes back (the last two are arms that the top holds for items that
  ride past).
THE LETTERS. F, base, cc, e are free, and nothing is asked of d₁ d₂: the binder is an instance.
The recursion limit is raised in this file (maxRecDepth 1000000), as in FormsAtFifty.lean:
for the elaboration of the kernel's evaluations alone.
What is not claimed. The premises. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.HpubPointwise
import Johnson.Desc.K1.Law.ExchangeStep
import Johnson.Desc.Sound.StatedCellIn

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open Iop Run OnBytes.Maker OnBytes.Flat
open Cb Johnson.Pack
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More flatPlacesOf)
open VerifiableInference.Desc.K9 (segAt? formsInT)
open VerifiableInference.Desc.Sound (Frame linksFull MsgT MgData CellsQ mgAll d13 rowQ runsAt insQ
  outsQ relAt meansQ strsOf seatTab uBySort statedIs_of ArmCellIn armCell_of_in)
open VerifiableInference.Desc.K13.Law (openAt plus13)
open VerifiableInference.Desc.K12.Door (K12Data)
open OnBytes.Model.Stages (LinkH)
open IM (k1Ix)

/-! ## 1 The row: the kernel's fact -/

/-- The test on the table's row at sub-protocol k, for segment l. -/
def readsRowB (l k : ℕ) : Bool :=
  (rowQ linksFull (flatPlacesOf linksFull true) k).ctx == [.pin l 0, .constr l .small] &&
    (rowQ linksFull (flatPlacesOf linksFull true) k).ins.all fun i =>
      match i with
      | .formsT m j n =>
        m == l && (rowQ linksFull (flatPlacesOf linksFull true) k).outs.contains (.forms m j n) &&
          (First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) k)).contains
            (.formsInT m j n) &&
          (runsAt linksFull m j n).all fun p => !(p.2 == "K8.equations")
      | _ => false

theorem readsRow_full : ((List.range 25).all fun l =>
    readsRowB l (14 * l + k1Ix l false + 2)) = true := by
  decide +kernel

/-- **The test can fail**: at segment 3's digits' place; and at another segment's number. -/
theorem readsRow_fails :
    readsRowB 3 (14 * 3 + k1Ix 3 true + 2) = false ∧
    readsRowB 4 (14 * 3 + k1Ix 3 false + 2) = false := by
  decide +kernel

/-! ## 2 The binder -/

section
variable {Xi Tok Cl : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public} {F : Frame}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)
  (Mg₀ : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))

/-- **THE BINDER hback OF k01_fifty, AT THE WIDER MEANING, POINTWISE.** -/
theorem hback_point (hlk : Dm.links = linksFull) (Z : ProofFile.Pub) (Bs : ProofFile.PureBase) :
    ∀ l, l < 25 → ∀ (base : ℕ) (d₁ d₂ : RDT) (cc e : ℕ),
      ∀ X arrs, Bs.G₀.built[l]? = some X → ∀ (c' : Block S Cl),
      c'.UnderR ((blkL Z Bs.G₀ l false X arrs).retype : Block S Cl) →
      ∀ (z : ProofFile.InstPub) (a : S × F.E.Str) τ x (w : Wit (CellsQ rows cols) Tok MsgT),
      Sound.onQ Dm.N (plus13 (d13 Dm) dk (mgAll Dm Mg₀)) linksFull (flatPlacesOf linksFull true)
        (fun s : S => (z, s)) (noL l false) a → a.1.failed = none →
      (sendPiece (W := Wit (CellsQ rows cols) Tok MsgT) (F := F) c' base d₁ d₂ cc e).ior.red.out
        a τ = some x →
      (∀ j n, Item.formsT l j n ∈ (rowQ linksFull (flatPlacesOf linksFull true) (noL l false)).ins →
        ReadersStay Dm.pubD l j n a.1 x.1) →
      (∀ j n, Item.formsT l j n ∈ (rowQ linksFull (flatPlacesOf linksFull true) (noL l false)).ins →
        ∀ p ∈ Dm.runs l j n, ∀ A B, segAt? a.1 = some A → segAt? x.1 = some B →
        ArmCellIn (Dm.Rd l) (Dm.N.sent l 0) (Dm.N.group l) p.1 p.2 a.1 A B
          (seatTab Dm.cs Dm.arr Dm.ms w) (uBySort Dm.uL Dm.uA Dm.uH)) →
      (Dm.wt l (z, x.1) (strsOf F x.2) w → Dm.wt l (z, a.1) (strsOf F a.2) w) →
      ((Item.pin l 0).holds Dm.N (plus13 (d13 Dm) dk (mgAll Dm Mg₀)) (z, x.1) (strsOf F x.2) w →
        (Item.pin l 0).holds Dm.N (plus13 (d13 Dm) dk (mgAll Dm Mg₀)) (z, a.1) (strsOf F a.2) w) →
      ((plus13 (d13 Dm) dk (mgAll Dm Mg₀)).constr l .small (z, x.1) (strsOf F x.2) w →
        (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).constr l .small (z, a.1) (strsOf F a.2) w) →
      relAt (meansQ Dm.N (plus13 (d13 Dm) dk (mgAll Dm Mg₀)) fun s : S => (z, s))
        (outsQ linksFull (flatPlacesOf linksFull true) (noL l false)) x w →
      relAt (meansQ Dm.N (plus13 (d13 Dm) dk (mgAll Dm Mg₀)) fun s : S => (z, s))
        (insQ linksFull (flatPlacesOf linksFull true) (noL l false)) a w := by
  intro l hl base d₁ d₂ cc e X arrs _ c' hu z a τ x w ha hm hx hl' hArm hwt hPin hCon hout i hi
  have hrow : readsRowB l (noL l false) = true :=
    List.all_eq_true.1 readsRow_full l (List.mem_range.2 hl)
  unfold readsRowB at hrow
  rw [Bool.and_eq_true, beq_iff_eq] at hrow
  obtain ⟨hctx, hins⟩ := hrow
  have hi' : i ∈ (rowQ linksFull (flatPlacesOf linksFull true) (noL l false)).ins ++
      (rowQ linksFull (flatPlacesOf linksFull true) (noL l false)).ctx ++ [.unmarked] := hi
  have hoc : ∀ i', i' ∈ (rowQ linksFull (flatPlacesOf linksFull true) (noL l false)).ctx →
      outsQ linksFull (flatPlacesOf linksFull true) (noL l false) i' := fun i' h =>
    List.mem_append_left _ (List.mem_append_right _ h)
  rcases List.mem_append.1 hi' with h1 | h1
  · rcases List.mem_append.1 h1 with h2 | h2
    · -- an item that the row closes
      have t := List.all_eq_true.1 hins i h2
      cases i with
      | formsT m j n =>
        simp only [Bool.and_eq_true] at t
        obtain ⟨⟨⟨tm, tout⟩, tpub⟩, truns⟩ := t
        obtain rfl : m = l := eq_of_beq tm
        have hF : (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).forms m j n (z, x.1) (strsOf F x.2) w :=
          hout (.forms m j n)
            (List.mem_append_left _ (List.mem_append_left _ (List.contains_iff_mem.1 tout)))
        obtain ⟨rs, gs, h2', hd⟩ := yes_of_piece (W := Wit (CellsQ rows cols) Tok MsgT) (F := F)
          (blkL Z Bs.G₀ m false X arrs) (rounds_blkL Z Bs.G₀ m false X arrs) c' hu base d₁ d₂ cc
          e a τ x hx
        have hIn : InAt Dm.N (plus13 (d13 Dm) dk (mgAll Dm Mg₀)) linksFull
            (flatPlacesOf linksFull true) (noL m false) (z, a.1) (strsOf F a.2) := ⟨ha, hm⟩
        have h0 := inAt_pub hIn _ (List.mem_append_right _ (List.contains_iff_mem.1 tpub))
        rw [pub_plus13, First.pubAll_formsInT, List.all_eq_true] at h0
        refine ⟨fun p hp => ?_, fun hw => hwt (hF.2 hw)⟩
        have hin : formsInT (Dm.Rd m) (Dm.N.sent m 0) p.1 p.2 a.1 = true := h0 p hp
        have hp' : p ∈ runsAt linksFull m j n := by
          have e0 : Dm.runs m j n = runsAt linksFull m j n := by
            show runsAt Dm.links m j n = _
            rw [hlk]
          rw [← e0]
          exact hp
        have hah : Dm.ah p.1 p.2 = false := by
          have t2 := List.all_eq_true.1 truns p hp'
          show (p.2 == "K8.equations") = false
          cases hq : (p.2 == "K8.equations") with
          | false => rfl
          | true =>
            rw [hq] at t2
            cases t2
        have hQ := hF.1 p hp
        rw [if_neg (by rw [hah]; exact Bool.false_ne_true)] at hQ
        cases hA : segAt? a.1 with
        | none =>
          unfold formsInT at hin
          rw [hA] at hin
          cases hin
        | some A =>
          have hlE : (Dm.Rd m).forms p.1 p.2 x.1 = (Dm.Rd m).forms p.1 p.2 a.1 := by
            cases hR : (Dm.Rd m).forms p.1 p.2 a.1 with
            | none =>
              unfold formsInT at hin
              rw [hA, hR] at hin
              cases hin
            | some R => exact hl' j n h2 p hp R hR
          obtain ⟨B, hB, _, hr, _⟩ := rides_of_rec
            (laterSend_k1Reads Z Bs.G₀ m X _ arrs a.1 x.1 rs gs h2' hd).2.1
            (laterGrows_k1Reads Z Bs.G₀ m X _ arrs a.1 x.1 rs gs hd) (inAt_book hIn).1
            (Dm.N.sent m 0) hA
          exact formsTQ_of_step (Dm.Rd m) Dm.St (uBySort Dm.uL Dm.uA Dm.uH) (Dm.N.sent m 0)
            (Dm.N.group m) p.1 p.2 a.1 x.1 A B (seatTab Dm.cs Dm.arr Dm.ms w)
            (fun y hy => by
              unfold First.Numbers.group
              exact List.mem_append_left _ (List.mem_append_left _ hy))
            (statedIs_of _ a.1) hA hB hlE hin hr
            (armCell_of_in (Dm.Rd m) (Dm.N.sent m 0) (Dm.N.group m) p.1 p.2 a.1 A B
              (seatTab Dm.cs Dm.arr Dm.ms w) _ hA hin (hArm j n h2 p hp A B hA hB)) hQ
      | _ => cases t
    · -- an item that the row reads
      have h3 := h2
      rw [hctx] at h3
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h3
      rcases h3 with rfl | rfl
      · exact hPin (hout _ (hoc _ h2))
      · exact hCon (hout _ (hoc _ h2))
  · obtain rfl := List.mem_singleton.1 h1
    exact hm

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.readsRow_full
#print axioms VerifiableInference.Desc.K1.readsRow_fails
#print axioms VerifiableInference.Desc.K1.hback_point
