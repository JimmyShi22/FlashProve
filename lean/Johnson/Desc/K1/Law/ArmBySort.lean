-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/ArmBySort.lean: the premise `ArmCellIn`
of hback_point (Johnson/Desc/K1/Law/ExchangeAtReads.lean), which speaks at the ONE stated function
`uBySort Dm.uL Dm.uA Dm.uH`, from each sort of segment's own half at ITS stated function of link l.
  `armCellIn_congr`   `ArmCellIn` reads the stated function at the state in front alone
  `armOf uL uA uH sub`   the arm of a sort; `uBySort_at`: where a state stands inside a segment of
                   the sort sub, `uBySort` is that arm at the open link's number
                   (Sound/StatedAll.lean's three lemmas, by the six cases of where a state stands)
  `standB`, `stand_full`   [kernel] at each of the 25 reads' places the table has the chain stand
                   inside a segment of link l's own sort. `stand_fails`: the test can fail
  `stand_of_promise`   so, inside the promise in front of link l's reads, the state stands so (the
                   promise's clause `shapeAt`)
  `linkNo_of_promise`   and the open link's number is l ("frame.sentIs" off the promise)
  `armCellIn_bySort`   **the join**, at one run
  `hback_sorts`    **hback_point with `ArmCellIn` asked at the arm of link l's own sort**
PREMISES OF hback_sorts: hM · hlk, and hback_point's five pointwise, the second now at
`armOf Dm.uL Dm.uA Dm.uH ((linksFull[l]?).getD .layers) l`: at a layers' link `Dm.uL l`, at an
attention link `Dm.uA l`, at the head `Dm.uH l`. What a sort's own lemma asks beside is not looked
at here.
The recursion limit is raised in this file (maxRecDepth 1000000):
for the elaboration of the kernel's evaluations alone.
What is not claimed. Any sort's half. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.ExchangeAtReads

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open Iop Run OnBytes.Maker OnBytes.Flat
open Cb Johnson.Pack
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More flatPlacesOf Stand standOf
  standAt)
open VerifiableInference.Desc.First.FillSent (link_of_sentIs)
open VerifiableInference.Desc.K9 (segAt? Readers)
open VerifiableInference.Desc.Sound (Frame linksFull MsgT MsgQ MgData CellsQ mgAll d13 rowQ insQ
  outsQ relAt meansQ strsOf seatTab UFn uBySort uBySort_lay uBySort_att uBySort_head linkNo
  ArmCellIn)
open VerifiableInference.Desc.K13.Law (openAt plus13)
open VerifiableInference.Desc.K12.Door (K12Data)
open OnBytes.Model.Stages (LinkH)
open IM (k1Ix)

/-! ## 1 The stated function by the sort -/

theorem armCellIn_congr (Rd : Readers) (own own' : List (ℕ × ℕ)) (piece : ℕ) (run : String) (s : S)
    (a b : K9.Part) (rd : ℕ × ℕ → MsgQ) {u u' : UFn} (e : u s = u' s)
    (h : ArmCellIn Rd own own' piece run s a b rd u') :
    ArmCellIn Rd own own' piece run s a b rd u := fun R hR f hf x hx hin c hc hs => by
  rw [e]
  exact h R hR f hf x hx hin c hc hs

/-- The arm of a sort. -/
def armOf (uL uA uH : ℕ → UFn) : ModelPart → ℕ → UFn
  | .layers => uL
  | .attention => uA
  | .head => uH

theorem uBySort_at (uL uA uH : ℕ → UFn) (s : S) (sub : ModelPart) (h : standOf s = .link sub) :
    uBySort uL uA uH s = armOf uL uA uH sub (linkNo s) s := by
  unfold standOf at h
  cases hh : s.here with
  | between =>
    rw [hh] at h
    cases h
  | lay a =>
    rw [hh] at h
    cases h
    exact uBySort_lay uL uA uH s a hh
  | att a =>
    rw [hh] at h
    cases h
    exact uBySort_att uL uA uH s a hh
  | head a =>
    rw [hh] at h
    dsimp only at h
    split at h
    · cases h
      exact uBySort_head uL uA uH s a hh
    · cases h
  | fin a =>
    rw [hh] at h
    cases h
  | mem a =>
    rw [hh] at h
    cases h

/-! ## 2 Where the chain stands at the reads: the kernel's fact -/

/-- At place number k the table has the chain stand inside a segment of link l's own sort. -/
def standB (l k : ℕ) : Bool :=
  ((flatPlacesOf linksFull true)[k]?).map (standAt linksFull) ==
    some (.link ((linksFull[l]?).getD .layers))

theorem stand_full : ((List.range 25).all fun l =>
    standB l (14 * l + k1Ix l false + 2)) = true := by
  decide +kernel

/-- **The test can fail**: at the chain's first place; and link 3's reads' place is no place of link
4's sort. -/
theorem stand_fails : standB 0 0 = false ∧ standB 4 (14 * 3 + k1Ix 3 false + 2) = false := by
  decide +kernel

section
variable {Pp W : Type} {N : Numbers} {Mg : Meaning Pp W}

theorem stand_of_promise (l : ℕ) (hl : l < 25) (x : Pp × S) (y : Strs)
    (hIn : InAt N Mg linksFull (flatPlacesOf linksFull true) (noL l false) x y) :
    standOf x.2 = .link ((linksFull[l]?).getD .layers) := by
  have hk : standB l (noL l false) = true := List.all_eq_true.1 stand_full l (List.mem_range.2 hl)
  unfold standB at hk
  obtain ⟨p, hp, hst⟩ := Option.map_eq_some_iff.1 (eq_of_beq hk)
  obtain ⟨hon, hm⟩ := hIn
  unfold First.onAt at hon
  obtain ⟨-, hr⟩ := hon
  rcases hr with hx | ⟨h1, -, -, -⟩
  · exact absurd hm hx
  · simp only [Bool.and_eq_true] at h1
    have hs := h1.1.1.1.1.1
    rw [hp] at hs
    simp only [First.shapeAt, Bool.and_eq_true, beq_iff_eq] at hs
    rw [hs.1.1, hst]

end

/-! ## 3 The join -/

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi P Tok rows cols nR XV) (dk : K12Data)
  (Mg₀ : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

theorem linkNo_of_promise (hM : Mg₀.more = {}) (l : ℕ) (hl : l < 25) (x : P × S) (y : Strs)
    (hIn : InAt Dm.N (plus13 (d13 Dm) dk (mgAll Dm Mg₀)) linksFull (flatPlacesOf linksFull true)
      (noL l false) x y) (A : K9.Part) (hA : segAt? x.2 = some A) : linkNo x.2 = l := by
  have hin : Pub.more (some l) "frame.sentIs" ∈
      (First.pubSets (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).more linksFull
        (flatPlacesOf linksFull true))[noL l false]?.getD [] := by
    rw [plus13_more_closed Dm dk Mg₀ hM]
    exact inSet_of (List.all_eq_true.1 sentIn_mw l (List.mem_range.2 hl))
  have h0 := inAt_pub hIn _ (List.mem_append_left _ hin)
  rw [pub_plus13, First.pubAll_more_sentIs] at h0
  obtain ⟨_, hLa, _, _, _⟩ := segAt_some hA
  unfold linkNo
  rw [hLa]
  exact link_of_sentIs hLa h0

/-- **THE JOIN**, at one run. -/
theorem armCellIn_bySort (hM : Mg₀.more = {}) (l : ℕ) (hl : l < 25) (x : P × S) (y : Strs)
    (hIn : InAt Dm.N (plus13 (d13 Dm) dk (mgAll Dm Mg₀)) linksFull (flatPlacesOf linksFull true)
      (noL l false) x y) (A B : K9.Part) (hA : segAt? x.2 = some A) (Rd : Readers)
    (own own' : List (ℕ × ℕ)) (piece : ℕ) (run : String) (rd : ℕ × ℕ → MsgQ)
    (h : ArmCellIn Rd own own' piece run x.2 A B rd
      (armOf Dm.uL Dm.uA Dm.uH ((linksFull[l]?).getD .layers) l)) :
    ArmCellIn Rd own own' piece run x.2 A B rd (uBySort Dm.uL Dm.uA Dm.uH) := by
  refine armCellIn_congr Rd own own' piece run x.2 A B rd ?_ h
  rw [uBySort_at Dm.uL Dm.uA Dm.uH x.2 _ (stand_of_promise l hl x y hIn),
    linkNo_of_promise Dm dk Mg₀ hM l hl x y hIn A hA]

end

section
variable {Xi Tok Cl : Type} {rows cols nR : ℕ} {XV : OnBytes.Model.Verify.Public} {F : Frame}
  (Dm : MgData Xi ProofFile.InstPub Tok rows cols nR XV) (dk : K12Data)
  (Mg₀ : Meaning ProofFile.InstPub (Wit (CellsQ rows cols) Tok MsgT))

/-- **hback_point, with `ArmCellIn` asked at the arm of link l's own sort.** -/
theorem hback_sorts (hM : Mg₀.more = {}) (hlk : Dm.links = linksFull) (Z : ProofFile.Pub)
    (Bs : ProofFile.PureBase) :
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
          (seatTab Dm.cs Dm.arr Dm.ms w)
          (armOf Dm.uL Dm.uA Dm.uH ((linksFull[l]?).getD .layers) l)) →
      (Dm.wt l (z, x.1) (strsOf F x.2) w → Dm.wt l (z, a.1) (strsOf F a.2) w) →
      ((Item.pin l 0).holds Dm.N (plus13 (d13 Dm) dk (mgAll Dm Mg₀)) (z, x.1) (strsOf F x.2) w →
        (Item.pin l 0).holds Dm.N (plus13 (d13 Dm) dk (mgAll Dm Mg₀)) (z, a.1) (strsOf F a.2) w) →
      ((plus13 (d13 Dm) dk (mgAll Dm Mg₀)).constr l .small (z, x.1) (strsOf F x.2) w →
        (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).constr l .small (z, a.1) (strsOf F a.2) w) →
      relAt (meansQ Dm.N (plus13 (d13 Dm) dk (mgAll Dm Mg₀)) fun s : S => (z, s))
        (outsQ linksFull (flatPlacesOf linksFull true) (noL l false)) x w →
      relAt (meansQ Dm.N (plus13 (d13 Dm) dk (mgAll Dm Mg₀)) fun s : S => (z, s))
        (insQ linksFull (flatPlacesOf linksFull true) (noL l false)) a w := by
  intro l hl base d₁ d₂ cc e X arrs hX c' hu z a τ x w ha hm hx hRd hArm
  exact hback_point Dm dk Mg₀ hlk Z Bs l hl base d₁ d₂ cc e X arrs hX c' hu z a τ x w ha hm hx hRd
    fun j n hj p hp A B hA hB =>
      armCellIn_bySort Dm dk Mg₀ hM l hl (z, a.1) (strsOf F a.2) ⟨ha, hm⟩ A B hA _ _ _ _ _ _
        (hArm j n hj p hp A B hA hB)

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.uBySort_at
#print axioms VerifiableInference.Desc.K1.stand_full
#print axioms VerifiableInference.Desc.K1.stand_fails
#print axioms VerifiableInference.Desc.K1.armCellIn_bySort
#print axioms VerifiableInference.Desc.K1.hback_sorts
