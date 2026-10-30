-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/HeadViewsWritten.lean: THE VIEW OF THE WRITTEN VALUES IS THE WRITTEN VIEW: so
the two cheap public tests planK6AtZ and padsAtZ (Johnson/Desc/Kinds/HeadDoorAtZ.lean) ACCEPT
wherever five values of Z are the written ones. Theorems; four evaluations by Lean's kernel.

Why. Both tests are functions of plain Views (Law/PlanK6View.lean, Law/PadsView.lean), and Lean's
kernel accepts both at written Views (Law/PlanK6ViewFull.lean, Law/PadsViewFull.lean). What was
left: that the Views of Z's own values ARE the written Views.

  Written Z    five equations: Z.first.codes, Z.first.shape, Z.first.layout and Z.made.proof are
          the written values (proofSizedFull.codes, proofSizedFull.request, layoutFull,
          proofSendsFull: Johnson/Desc/Ok/PlanWritten/SizedLit.lean, Johnson/G/LayoutLit.lean,
          Johnson/G/SendsWritten.lean), and the table of counts of roots rootsOf Z.made.proof Z.D is
          rootsFull.
  rootsFull    97 numbers, written by a program off one printout (sha256
          abb7fb0e83c3b2d747fa0e67ccff3edee1a3241c70cb7a7b1f554d2a4a5b3f36).

What is proved.
  view_closed, num_closed, pads_closed, ell_closed   BY LEAN's KERNEL, at the written values: the
          first test's View with 8192 in ns's place is viewFull's with 8192 there; the number of the
          head's first oracle message is 145; the second test's View is padsFull; the mask code's
          message length is 8192.
  viewPlain_labs, padsViewOf_labs, pairsOf_nas   the Views read of the labels their owners alone,
          and of nas its values below 12.
  **padsAtZ_of_written**    Written Z and XPart Z.p.X imply padsAtZ Z = true.
  **planK6AtZ_of_written**  ProofFile.pureRoad.pub o pol lay KL = .ok Z, Written Z and XPart Z.p.X imply
          planK6AtZ Z = true. The number of mask entries in use needs no written value: head_ns_le
          (Law/HeadNsFits.lean) bounds it by the mask code's message length, and the test is
          monotone (Law/PlanK6NoNs.lean).

No existential quantifier in these statements.
Not proved here. Written Z: four of its equations are what the public test madeRow
compares; the fifth follows from the declared rounds. XPart Z.p.X: Goal/Meaning/HeadXPartScope.lean,
in the goals' scope, at publicOf's X. Nothing on soundness.

-/
import Johnson.Desc.Kinds.Law.HeadDoorByLaw
import Johnson.Desc.Kinds.Law.PlanK6NoNs
import Johnson.Desc.Kinds.Law.PadsViewFull
import Johnson.Desc.Kinds.Law.HeadNsFits
import Johnson.Goal.Meaning.HeadXPartScope
import Johnson.G.LayoutLit
import Johnson.G.SendsWritten
import Johnson.Desc.Ok.PlanWritten.SizedLit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.OffPad

open OnBytes.Params (ReqLayout)
open VerifiableInference.PlanWritten (proofSizedFull)
open Johnson.G (proofSendsFull layoutFull)

/-- The written table of counts of roots. Written by a program off a printout: see the header. -/
def rootsFull : RootsV :=
  { r1 :=
      [0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
      26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48,
      49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71,
      72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82]
    r2 := [0, 1, 3, 4, 5, 6, 8, 9, 10]
    r3 := [0, 1, 2, 3]
    t1 := 83
    t2 := 11 }

/-- The five arguments at the written values. -/
def lettersW : DoorLetters := lettersBy proofSendsFull proofSizedFull.request rootsFull

/-- Labels with the owners that XPart names. -/
def labW (k a : Nat) : Nat :=
  if k = 24 then (if a = 7 then 12 * 256 + 7 else 13 * 256 + a)
  else if k % 2 = 0 then k / 2 * 256 + 7 else (k / 2 + 1) * 256 + 6

/-- Lean's kernel evaluates it. -/
theorem view_closed :
    viewPlain proofSizedFull.codes layoutFull 8 4 8192 (labW 24) lettersW.num lettersW.arr
      (lettersW.group 24) lettersW.sent0 lettersW.mems = { viewFull with ns := 8192 } := by
  decide +kernel

/-- Lean's kernel evaluates it. -/
theorem num_closed : lettersW.num 24 0 = 145 := by
  decide +kernel

/-- Lean's kernel evaluates it. -/
theorem pads_closed :
    padsViewOf proofSizedFull.codes layoutFull labW lettersW.num lettersW.arr lettersW.group
      lettersW.mems 8 (fun _ => 1) 4 = padsFull := by
  decide +kernel

/-- Lean's kernel evaluates it. -/
theorem ell_closed :
    (proofSizedFull.codes.mask[proofSizedFull.request.maskCode]?).map (·.ell) = some 8192 := by
  decide +kernel

/-- Five values of Z are the written ones. -/
structure Written (Z : ProofFile.Pub) : Prop where
  codes : Z.first.codes = proofSizedFull.codes
  shape : Z.first.shape = proofSizedFull.request
  layout : Z.first.layout = layoutFull
  sends : Z.made.proof = proofSendsFull
  roots : rootsOf Z.made.proof Z.D = rootsFull

/-- The five arguments at such a Z are those at the written values. -/
theorem letters_written {Z : ProofFile.Pub} (W : Written Z) : lettersAt Z = lettersW := by
  rw [lettersAt_by, W.roots, W.sends, W.shape]
  rfl

/-- The first View reads of the labels their owners alone. -/
theorem viewPlain_labs (cs : OnBytes.Codes) (layout : ReqLayout) (NM NHf ns : Nat)
    (labs labs' : Nat → Nat) (num arr : Nat → Nat → Nat) (group sent0 : List (Nat × Nat))
    (mems : List (OnBytes.OracleShape × (Nat × Nat)))
    (h : ∀ a, a < NM → ownerP (labs a) = ownerP (labs' a)) :
    viewPlain cs layout NM NHf ns labs num arr group sent0 mems =
      viewPlain cs layout NM NHf ns labs' num arr group sent0 mems := by
  unfold viewPlain
  congr 1
  refine List.map_congr_left fun a ha => ?_
  rw [h a (List.mem_range.1 ha)]

/-- The list of pairs reads of nas its values below 12 alone. -/
theorem pairsOf_nas (iXI NHf : Nat) (nas nas' : Nat → Nat) (h : ∀ g, g < 12 → nas g = nas' g) :
    pairsOf iXI nas NHf = pairsOf iXI nas' NHf := by
  unfold pairsOf
  congr 1
  refine flatMap_same _ _ _ fun g hg => ?_
  rw [h g (List.mem_range.1 hg)]

/-- The second View reads of the labels their owners alone, at the pairs. -/
theorem padsViewOf_labs (cs : OnBytes.Codes) (layout : ReqLayout) (labs labs' : Nat → Nat → Nat)
    (num arr : Nat → Nat → Nat) (group : Nat → List (Nat × Nat))
    (mems : List (OnBytes.OracleShape × (Nat × Nat))) (iXI : Nat) (nas : Nat → Nat) (NHf : Nat)
    (h : ∀ x ∈ pairsOf iXI nas NHf, ownerP (labs x.1 x.2.2) = ownerP (labs' x.1 x.2.2)) :
    padsViewOf cs layout labs num arr group mems iXI nas NHf =
      padsViewOf cs layout labs' num arr group mems iXI nas NHf := by
  unfold padsViewOf
  congr 1
  refine List.map_congr_left fun x hx => ?_
  rw [h x hx]

/-- The written labels have the owners that XPart names: the head's list. -/
theorem labW_head : ∀ a, a < 8 →
    ownerP (labW 24 a) = if a = 7 then (22, Meaning.nameOf 7) else (24, Meaning.nameOf a) := by
  decide +kernel

/-- At the layers' segments. -/
theorem labW_layers : ∀ g, g < 12 → 0 < g →
    ownerP (labW (2 * g) 8) = (2 * (g - 1), Meaning.nameOf 7) := by
  decide +kernel

/-- At the attention's segments. -/
theorem labW_att : ∀ g, g < 12 → ownerP (labW (2 * g + 1) 4) = (2 * g, Meaning.nameOf 6) := by
  decide +kernel

/-- A pair of the written list is one of three kinds. -/
theorem pairs_kinds {x : Nat × Nat × Nat} (hx : x ∈ pairsOf 8 (fun _ => 1) 4) :
    (∃ g, 0 < g ∧ g < 12 ∧ x.1 = 2 * g ∧ x.2.2 = 8) ∨ (∃ g, g < 12 ∧ x.1 = 2 * g + 1 ∧ x.2.2 = 4) ∨
      (x.1 = 24 ∧ x.2.2 = 7) := by
  unfold pairsOf at hx
  rcases List.mem_append.1 hx with hx | hx
  · obtain ⟨g, hg, hx⟩ := List.mem_flatMap.1 hx
    have hg' := List.mem_range.1 hg
    rcases List.mem_append.1 hx with hx | hx
    · by_cases h0 : g = 0
      · subst h0
        cases hx
      · rw [if_neg (by simpa using h0)] at hx
        obtain rfl := List.mem_singleton.1 hx
        exact Or.inl ⟨g, Nat.pos_of_ne_zero h0, hg', rfl, rfl⟩
    · obtain rfl := List.mem_singleton.1 hx
      exact Or.inr (Or.inl ⟨g, hg', rfl, rfl⟩)
  · obtain rfl := List.mem_singleton.1 hx
    exact Or.inr (Or.inr ⟨rfl, rfl⟩)

/-- **The second test accepts wherever the five values are the written ones.** -/
theorem padsAtZ_of_written {Z : ProofFile.Pub} (W : Written Z) (hx : XPart Z.p.X) :
    padsAtZ Z = true := by
  unfold padsAtZ padsRow
  rw [padsDoor_eq, letters_written W, W.codes, W.layout, hx.ixi, hx.nhf]
  have e1 : pairsOf 8 (nasOf Z.p.X) 4 = pairsOf 8 (fun _ => 1) 4 :=
    pairsOf_nas 8 4 _ _ hx.nas
  have e2 : padsViewOf proofSizedFull.codes layoutFull (labsOf Z.p.X) lettersW.num lettersW.arr
      lettersW.group lettersW.mems 8 (nasOf Z.p.X) 4 = padsFull := by
    rw [← pads_closed]
    have e3 : padsViewOf proofSizedFull.codes layoutFull (labsOf Z.p.X) lettersW.num lettersW.arr
        lettersW.group lettersW.mems 8 (nasOf Z.p.X) 4 =
        padsViewOf proofSizedFull.codes layoutFull (labsOf Z.p.X) lettersW.num lettersW.arr
          lettersW.group lettersW.mems 8 (fun _ => 1) 4 := by
      unfold padsViewOf
      rw [e1]
    rw [e3]
    refine padsViewOf_labs _ _ _ _ _ _ _ _ _ _ _ fun x hxm => ?_
    rcases pairs_kinds hxm with ⟨g, h0, hg, a1, a2⟩ | ⟨g, hg, a1, a2⟩ | ⟨a1, a2⟩
    · rw [a1, a2, hx.layers g h0 hg, labW_layers g hg h0]
    · rw [a1, a2, hx.att g hg, labW_att g hg]
    · rw [a1, a2, hx.head 7 (by decide), labW_head 7 (by decide)]
  rw [e2]
  exact padsFull_yes

/-- **The first test accepts wherever the public part is made and the five values are the written
ones.** -/
theorem planK6AtZ_of_written {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z) (W : Written Z) (hx : XPart Z.p.X) :
    planK6AtZ Z = true := by
  have hns : Z.p.X.H.ns ≤ 8192 := by
    obtain ⟨zk, hz, hle⟩ := head_ns_le h
    rw [W.codes, W.shape] at hz
    have e := ell_closed
    rw [hz] at e
    have : zk.ell = 8192 := Option.some.inj e
    omega
  unfold planK6AtZ planK6Row planK6Door
  rw [letters_written W, W.codes, W.layout, hx.nm, hx.nhf, num_closed]
  have e : viewPlain proofSizedFull.codes layoutFull 8 4 8192 (labsOf Z.p.X 24) lettersW.num
      lettersW.arr (lettersW.group 24) lettersW.sent0 lettersW.mems =
      { viewFull with ns := 8192 } := by
    rw [← view_closed]
    refine viewPlain_labs _ _ _ _ _ _ _ _ _ _ _ _ fun a ha => ?_
    rw [hx.head a ha, labW_head a ha]
  have b : planK6V { viewPlain proofSizedFull.codes layoutFull 8 4 Z.p.X.H.ns (labsOf Z.p.X 24)
      lettersW.num lettersW.arr (lettersW.group 24) lettersW.sent0 lettersW.mems with
      ns := 8192 } 145 0 = true := by
    have : { viewPlain proofSizedFull.codes layoutFull 8 4 Z.p.X.H.ns (labsOf Z.p.X 24)
        lettersW.num lettersW.arr (lettersW.group 24) lettersW.sent0 lettersW.mems with
        ns := 8192 } = viewPlain proofSizedFull.codes layoutFull 8 4 8192 (labsOf Z.p.X 24)
          lettersW.num lettersW.arr (lettersW.group 24) lettersW.sent0 lettersW.mems := rfl
    rw [this, e]
    exact viewFull_bound
  exact planK6V_mono b hns

end VerifiableInference.Desc.Kinds.Head.Law.OffPad

#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.view_closed
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.num_closed
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.pads_closed
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.ell_closed
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.letters_written
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.viewPlain_labs
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.pairsOf_nas
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.padsViewOf_labs
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.labW_head
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.labW_layers
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.labW_att
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.pairs_kinds
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.padsAtZ_of_written
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.planK6AtZ_of_written
