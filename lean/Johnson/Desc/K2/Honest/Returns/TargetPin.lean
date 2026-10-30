-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/TargetPin.lean: THE YES OF THE PROGRAM's TEST ON A SWITCH's TARGET
(`switchTargetCheck`, OnBytes/Iop/Cs.lean) PASSES FROM A FRONT x₀ TO EVERY FRONT x THAT HAS x₀'s
PUBLIC SIDE, BY PLACE (`Pinned`, Johnson/Top/H0/K2Hands/FrameOne.lean). So do three further clauses
of the law "the kind's own decision says yes": the kept old messages have the old main code
(`OldFits.keptCode`), the count of kept rows is the sum of their main rows (`OldFits.rows`), and
their main tables have at most 63 index bits (`TablesFit.bitsKept`). No state, no plan, no size. x₀
and x may differ in all that `Pinned` does not pin: the messages' numbers, the classes of leaves,
which copies are kept again, the claim's forms and vectors. Statements with their proofs: rewriting,
and calls.

WHY IT MATTERS. A law that says when the verifier's text RETURNS cannot draw the test's yes from a
verifier's yes: it needs it from what is public. With this file: from the same test at one written
front.

  `alike_shapes` two lists of messages' numbers that are alike name the same shapes, in order
  `keptShapes_pin` the kept old messages' shapes, as `sizesAt` lists them, are the same
  `pin_counts` as many copies, as many kept old messages
  `pin_at` at each place: the same old shape, the same shape of the copy
  `targetFits_pin` the test's eighteen plain facts (`TargetFits`) pass from x₀ to x
  `check_pin` so the test's yes does
  `keptCode_pin`, `rows_pin`, `bitsKept_pin` the three further clauses, each in its structure's own
                    letters

By, all the library's: `front_alike` (K2Hands/FrameOne.lean) · `shape_at`, `parts_alike`
(K2Hands/FrameRenumber.lean) · `places_bare`, `alike_length` (K2Hands/FrameRenumbered.lean) ·
`targetOk_eq`, `targetOk_means` (Johnson/Top/H0/Tw/K2/). Near relatives, not called: `check_congr`
(Johnson/Top/H/SwitchPads.lean): the test has one value at two statements, with ONE claim in front
and ONE target; `check_skel` (Johnson/Top/H0/K2Hears/CheckSkel.lean) is a call of it · `frame_pin`
(K2Hands/FrameOne.lean): the frame's maker at two pinned fronts · `keptPos_pin` (the same file): its
proof's lines on the copies' shapes stand in `pin_at` again.

Limits. Stated from x₀ to x; the way back would follow from the symmetry of `Pinned`, which is not
typed. That the test says yes at any front is not shown here. Nothing on any property.


-/
import Johnson.Desc.K2.Honest.Inner.Statement
import Johnson.Top.H0.K2Hands.FrameOne
import Johnson.Top.H0.Tw.K2.TargetMeans

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open VerifiableInference.Desc.First.K2Hands (Pinned Alike front_alike shape_at parts_alike
  places_bare alike_length)
open _root_.Tw.K2 (Front TargetFits KeptFits BlocksFill targetOk_eq targetOk_means)

theorem alike_shapes {S S₀ : Statement} : ∀ {ks ks₀ : List Nat}, Alike S S₀ ks ks₀ →
    (ks.map fun o => (S.oracles.getD o default).shape) =
      ks₀.map fun o => (S₀.oracles.getD o default).shape
  | _, _, .nil => rfl
  | _, _, .cons e t => by
    rw [List.map_cons, List.map_cons, shape_at e, alike_shapes t]

variable {x₀ x : Front}

theorem keptShapes_pin (P : Pinned x₀ x) :
    (sizesAt x.st x.f.rows x.T).kept = (sizesAt x₀.st x₀.f.rows x₀.T).kept :=
  alike_shapes (front_alike P)

theorem pin_counts (P : Pinned x₀ x) : x.T.kept.size = x₀.T.kept.size ∧
    (switchKept x.f.rows).size = (switchKept x₀.f.rows).size := by
  constructor
  · have h := congrArg List.length P.kept
    simpa using h
  · have h := alike_length (front_alike P)
    simpa using h

theorem pin_at (P : Pinned x₀ x) (i : Nat) (h1 : i < (switchKept x.f.rows).size)
    (h1' : i < (switchKept x₀.f.rows).size) (h2 : i < x.T.kept.size) (h2' : i < x₀.T.kept.size) :
    (x.st.oracles.getD (switchKept x.f.rows)[i] default).shape =
        (x₀.st.oracles.getD (switchKept x₀.f.rows)[i] default).shape ∧
      x.T.kept[i].shape = x₀.T.kept[i].shape := by
  constructor
  · have e := congrArg (·[i]?) (alike_shapes (front_alike P))
    simp only [List.getElem?_map, Array.getElem?_toList, Array.getElem?_eq_getElem h1,
      Array.getElem?_eq_getElem h1', Option.map_some, Option.some.injEq] at e
    exact e
  · have e := congrArg (·[i]?) P.kept
    simp only [List.getElem?_map, Array.getElem?_toList, Array.getElem?_eq_getElem h2,
      Array.getElem?_eq_getElem h2', Option.map_some, Option.some.injEq] at e
    exact e

/-- **The test's plain facts pass from one pinned front to the other.** -/
theorem targetFits_pin (P : Pinned x₀ x) (F : TargetFits x₀.st x₀.f.rows x₀.T) :
    TargetFits x.st x.f.rows x.T where
  masks := by rw [P.masks]; exact F.masks
  oldCode := by rw [P.code, P.codes]; exact F.oldCode
  oldMaskCode := by rw [P.maskCode, P.codes]; exact F.oldMaskCode
  code := by rw [P.shape, P.codes]; exact F.code
  rows := by rw [P.shape]; exact F.rows
  degree := by rw [P.shape]; exact F.degree
  sampled := by rw [P.shape]; exact F.sampled
  pad := by rw [P.codes, P.shape]; exact F.pad
  mainPart := by rw [P.main]; exact F.mainPart
  power := by rw [P.codes, P.code]; exact F.power
  mainAligned := by rw [P.main]; exact F.mainAligned
  restAligned := by rw [P.rest]; exact F.restAligned
  fill := by
    have h := F.fill
    unfold BlocksFill at h ⊢
    rw [P.rest, P.shape, P.main, P.codes]
    exact h
  mainSmall := by rw [P.main, P.codes, P.code]; exact F.mainSmall
  mainRoom := by rw [P.codes, P.code, P.shape, P.main]; exact F.mainRoom
  restRoom := by
    rw [parts_alike P.codes P.code P.maskCode P.masks P.keptRows (front_alike P),
      places_bare P.codes P.shape P.rest]
    exact F.restRoom
  keptCount := by
    rw [(pin_counts P).1, (pin_counts P).2]
    exact F.keptCount
  keptShapes := by
    intro p hp
    obtain ⟨k1, k2⟩ := pin_counts P
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hp
    simp only [Array.size_zip] at hi
    have h1 : i < (switchKept x.f.rows).size := by omega
    have h2 : i < x.T.kept.size := by omega
    have h1' : i < (switchKept x₀.f.rows).size := by omega
    have h2' : i < x₀.T.kept.size := by omega
    have hm : ((switchKept x₀.f.rows)[i], x₀.T.kept[i]) ∈ (switchKept x₀.f.rows).zip x₀.T.kept :=
      Array.mem_iff_getElem.2 ⟨i, by simp only [Array.size_zip]; omega, by simp⟩
    obtain ⟨e1, e2⟩ := pin_at P i h1 h1' h2 h2'
    simp only [Array.getElem_zip]
    rw [P.codes, e1, e2]
    exact F.keptShapes _ hm

/-- **So the test's yes passes.** -/
theorem check_pin (P : Pinned x₀ x) (h : switchTargetCheck x₀.st x₀.f.rows x₀.T = true) :
    switchTargetCheck x.st x.f.rows x.T = true := by
  have F := (targetOk_means x₀.st x₀.f.rows x₀.T).1 (by rw [targetOk_eq]; exact h)
  have G := (targetOk_means x.st x.f.rows x.T).2 (targetFits_pin P F)
  rw [targetOk_eq] at G
  exact G

theorem keptCode_pin (P : Pinned x₀ x)
    (h : ∀ o ∈ (switchKept x₀.f.rows).toList,
      (x₀.st.oracles.getD o default).shape.code = x₀.f.rows.code) :
    ∀ o ∈ (switchKept x.f.rows).toList,
      (x.st.oracles.getD o default).shape.code = x.f.rows.code := by
  intro o ho
  have hm : (x.st.oracles.getD o default).shape ∈
      (switchKept x.f.rows).toList.map fun o => (x.st.oracles.getD o default).shape :=
    List.mem_map.2 ⟨o, ho, rfl⟩
  rw [alike_shapes (front_alike P)] at hm
  obtain ⟨o₀, ho₀, e⟩ := List.mem_map.1 hm
  rw [← e, P.code]
  exact h o₀ ho₀

theorem rows_pin (P : Pinned x₀ x)
    (h : x₀.f.rows.keptRows = ((switchKept x₀.f.rows).toList.map fun o =>
      (x₀.st.oracles.getD o default).shape.mainRows).sum) :
    x.f.rows.keptRows = ((switchKept x.f.rows).toList.map fun o =>
      (x.st.oracles.getD o default).shape.mainRows).sum := by
  have e := congrArg (fun l : List OracleShape => (l.map (·.mainRows)).sum)
    (alike_shapes (front_alike P))
  simp only [List.map_map] at e
  rw [P.keptRows, h]
  exact e.symm

theorem bitsKept_pin (P : Pinned x₀ x)
    (h : ∀ s ∈ (sizesAt x₀.st x₀.f.rows x₀.T).kept,
      ceilLog2 s.mainRows + (x₀.st.codes.base.getD x₀.f.rows.code default).logEll ≤ 63) :
    ∀ s ∈ (sizesAt x.st x.f.rows x.T).kept,
      ceilLog2 s.mainRows + (x.st.codes.base.getD x.f.rows.code default).logEll ≤ 63 := by
  intro s hs
  rw [keptShapes_pin P] at hs
  rw [P.codes, P.code]
  exact h s hs

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.alike_shapes
#print axioms VerifiableInference.Desc.K2.Honest.Returns.keptShapes_pin
#print axioms VerifiableInference.Desc.K2.Honest.Returns.pin_counts
#print axioms VerifiableInference.Desc.K2.Honest.Returns.pin_at
#print axioms VerifiableInference.Desc.K2.Honest.Returns.targetFits_pin
#print axioms VerifiableInference.Desc.K2.Honest.Returns.check_pin
#print axioms VerifiableInference.Desc.K2.Honest.Returns.keptCode_pin
#print axioms VerifiableInference.Desc.K2.Honest.Returns.rows_pin
#print axioms VerifiableInference.Desc.K2.Honest.Returns.bitsKept_pin
