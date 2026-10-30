-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/SkelStack.lean: CONDITIONAL: on `PtsSkel` and a length.

What is here. CONGRUENCE: THE BATCHED SUMCHECK OF ALL INNER PRODUCTS (`jobStack`,
Johnson/Desc/K4/Honest/Stack.lean) at two inputs, two lists of sampled values of one skeleton AND
WITH AS MANY POWERS OF THE ELEMENT THAT JOINS THE TWO PASSES (hom; not in `PtsSkel`), and two lists
of shown values. One definition, and eleven statements with their proofs.

  `panelTabs_rel`   a panel's two sides are made together.
  `fillAt_size`, `longTabs_size`   the two long vectors have 2 ^ lam entries, whatever is laid.
  `DataSkel`, `stackDataOn_rel`   what the job's functions read.
  `val_rel`, `claimVals_size`, `endsAt_rel`   the true end values: as many.
  `summandOn_rel`, `stackData_rel`   the summand on given end values; the data, of a place.
  `jobStackOn_skel`, `jobStack_skel`   **the job**: both makers return or neither, and the public
      test on a job's shape (`k4JobFits`) gives one answer at every call (`JobSkel`,
      Law/SkelJobs.lean).

Debts and ends. `DataSkel` IS AN END: NO DEBT: WHEREVER A LAW THAT TAKES IT IS CALLED BY A LAW THAT
DOES NOT TAKE IT ITSELF, IT IS PAID ON THE SPOT. It is concluded by `stackDataOn_rel` and
`stackData_rel`, here, and of a thing and itself by `dataSkel_refl` (Law/AtEnds.lean). It is the
hypothesis K of four inner laws here (`val_rel`, `endsAt_rel`, `jobStackOn_skel`, `summandOn_rel`);
outside this file such a law is called in Law/AtEnds.lean alone, at one data, with `dataSkel_refl`.
ITS FIVE FIELDS: `SidesSkel` and `HasSame`, ends of sister files (Law/SkelSides.lean,
Law/SkelReads.lean); the panels' keys, member by member (the library's `BlkKeys False`); the two
long vectors' sizes. `SidesSkel` is besides the hypothesis K of `stackDataOn_rel`; `stackData_rel`
pays it on the spot with `sidesOf_rel`, from the field fo of `PtsSkel`. `BlkKeys` and the library's
`FormKeys` are hypotheses of `panelTabs_rel` (hb; inside hval), and `FormKeys` of `val_rel` (h):
paid on the spot in `stackDataOn_rel` (from `panelsOn_rel`, Law/SkelTerms.lean, and with
`valAff_rel`, Law/SkelReads.lean) and in `endsAt_rel` (from `stackEnd_keys`). `jobStack_skel`, the
law at two inputs that other files call (Law/MakersSkel.lean, Law/MakersAt.lean), does not name
`DataSkel`: IT ASKS `PtsSkel` AND ONE LENGTH (hom: the field om of `PtsFull`), as do `stackData_rel`
and `stackDataOn_rel` beneath it, to which it hands them down; the two inputs w and w₀ and the two
lists of shown values are free letters. `PtsSkel` (Law/SkelEnv.lean) IS A FIELD OF A DEBT: the first
field of `PtsFull` (Law/MakersAt.lean: see there for its payers): `LookSkel` and seven lengths.
`JobSkel` IS AN END: `jobStackOn_skel` and `jobStack_skel` end in it.

Not shown here. BOTH LISTS OF SAMPLED VALUES ARE TAKEN AT ONE AND THE SAME POINT OF THE ROUNDS:
`PtsSkel` asks seven equal lengths, which is more than that the same points are whole. IT DOES NOT
HOLD BETWEEN A LIST IN WHICH ALL OF THE SUB-PROTOCOL's CHALLENGES HAVE BEEN HEARD AND THE LIST THAT
THE BATCHED SUMCHECK's OWN MOVES SEE, in which the two gated products' challenges are not yet
sampled: so nothing here carries a yes at the first to the second. It stands on `sidesOf_rel`
(Law/SkelSides.lean). NO MAKER IS SHOWN TO RETURN ANYWHERE: a statement on a maker compares two
calls. Nothing on what a table or an end value is worth.

Kin. `panelTabs_rel` and `tripsOf_rel` (Law/SkelTerms.lean) take a panel apart in the same way.
`endsAt_rel` and `summandOn_rel` stand on the library's `stackEnd_keys`
(Johnson/Desc/First/K4/Returns/Pub/EndKeys.lean). No definition of the library under the short name
DataSkel was found. No twin in the library is known to its writers.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SkelTerms
import Johnson.Desc.First.K4.Returns.Pub.EndKeys
import Johnson.Desc.K4.Honest.Stack

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E F zeroE)
open OnBytes.Model (Aff)
open OnBytes.Model.Layer (SBlk)
open OnBytes.Flat (All2 OptRel optRel_bind optRel_bind_same optRel_map')
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.Honest.CubeLaw (fits_sizes)
open OnBytes.Desc.First.K4.RtPub

variable {S S₀ : Sides}

/-- A panel's two sides are made together. -/
theorem panelTabs_rel {W : Prop} {val val₀ : Aff → Option E}
    (hval : ∀ a a₀, FormKeys a a₀ → OptRel (fun _ _ => True) (val a) (val₀ a₀))
    (om om₀ : Array E) (F F₀ : Array (Array E)) (hZ hR hZ₀ hR₀ : Tab) {b b₀ : SBlk}
    (hb : BlkKeys W b b₀) :
    OptRel (fun _ _ => True) (panelTabs S val om F hZ hR b)
      (panelTabs S₀ val₀ om₀ F₀ hZ₀ hR₀ b₀) := by
  obtain ⟨tri, v0, claim, ec, ni, ny, wy, w, off, A, B, wt, sl, xx, virt⟩ := b
  obtain ⟨tri₀, v0₀, claim₀, ec₀, ni₀, ny₀, wy₀, w₀, off₀, A₀, B₀, wt₀, sl₀, xx₀, virt₀⟩ := b₀
  obtain ⟨e1, e2, e9, e3, e4, e5, e6, e7, e8, hA, hB, hx, _, _⟩ := hb
  dsimp only at e1 e2 e9 e3 e4 e5 e6 e7 e8 hA hB hx
  subst e1 e2 e9 e3 e4 e5 e6 e7 e8
  unfold panelTabs
  dsimp only
  refine optRel_ite ?_ ?_
  · refine optRel_bind_same fun v0 => optRel_bind (S := fun _ _ => True) ?_ fun _ _ _ => by trivial
    refine OptRel.mono (fun _ _ _ => by trivial) (amapM_size_rel ny fun yv _ => ?_)
    cases virt with
    | some k => rfl
    | none => exact OptRel.isSome_eq (hval _ _ (hx yv))
  · cases virt with
    | some k => exact optRel_bind_same fun _ => trivial
    | none =>
      refine optRel_bind hA fun f f₀ hf => ?_
      refine optRel_bind (S := fun _ _ => True) ?_ fun _ _ _ => ?_
      · refine OptRel.mono (fun _ _ _ => True.intro) (amapM_size_rel (ni * ny) fun x _ => ?_)
        exact OptRel.isSome_eq (R := fun _ _ => True)
          (optRel_bind (hf _ _) fun q q₀ hq =>
            optRel_bind (hval q q₀ hq) fun _ _ _ => True.intro)
      · cases v0 with
        | some v0 => exact True.intro
        | none =>
          cases B with
          | none =>
            cases B₀ with
            | none => exact True.intro
            | some _ => exact False.elim hB
          | some g =>
            cases B₀ with
            | none => exact False.elim hB
            | some g₀ =>
              refine optRel_bind (S := fun _ _ => True) (OptRel.mono (fun _ _ _ => True.intro)
                (amapM_size_rel (ni * ny) fun x _ => ?_)) fun _ _ _ => True.intro
              exact OptRel.isSome_eq (R := fun _ _ => True)
                (optRel_bind (hB _ _) fun q q₀ hq => hval q q₀ hq)

/-- Laying a panel's side into a table keeps the table's size. -/
theorem fillAt_size (b : SBlk) (x : Array E) (t : Tab) : (fillAt b x t).size = t.size := by
  unfold fillAt
  exact foldl_size (fun _ _ => Array.size_setIfInBounds ..) _ t

/-- The two long vectors have 2 ^ lam entries, whatever is laid. -/
theorem longTabs_size (lam : Nat) (bl : Array SBlk) (sides : Array (Array E × Array E)) :
    (longTabs lam bl sides).1.size = 2 ^ lam ∧ (longTabs lam bl sides).2.size = 2 ^ lam := by
  unfold longTabs
  dsimp only
  refine ⟨?_, ?_⟩
  · rw [afoldl_size (fun _ _ => fillAt_size ..), Array.size_replicate]
  · rw [afoldl_size (fun _ _ => fillAt_size ..), Array.size_replicate]

/-- What of the job's data its shape reads at most: that it is enough: `jobStackOn_skel`. NOT in it:
the two passes' weights om, the claims' tables F, the gated products hZ and hR, any entry of the two
long vectors, a panel's call weight and rows' weights (ec, wt) and its selector's shown values (sl).
IN it, of elements: what the public data in the field S hold (see `SidesSkel`). -/
structure DataSkel (D D₀ : StackData) : Prop where
  S : SidesSkel D.S D₀.S
  R : HasSame D.R D₀.R
  bl : All2 (BlkKeys False) D.bl.toList D₀.bl.toList
  SA : D.SA.size = D₀.SA.size
  SB : D.SB.size = D₀.SB.size

/-- CONDITIONAL: on K, P and hom. What the job's functions read, at two shared data and two lists of
sampled values of one skeleton each, with as many powers of the element that joins the two passes
(hom). -/
theorem stackDataOn_rel (K : SidesSkel S S₀) {p p₀ : Pts} (P : PtsSkel p p₀)
    (hom : p.om.size = p₀.om.size) (sh sh₀ : Array E) :
    OptRel DataSkel (stackDataOn S p sh) (stackDataOn S₀ p₀ sh₀) := by
  unfold stackDataOn
  dsimp only
  rw [K.Q]
  refine optRel_bind (readsAt_has _ _ _ K.fo (namedPts_skel S₀.Q
    (p := { p with fo := S.fo }) (p₀ := { p₀ with fo := S₀.fo })
    ⟨K.fo, P.PV, P.ZE, P.r6, P.rtV, P.rt, P.r12, P.r14⟩)) fun R R₀ hR => ?_
  refine optRel_bind (panelsOn_rel K sh sh₀) fun x x₀ hx => ?_
  obtain ⟨bl, n⟩ := x
  obtain ⟨bl₀, n₀⟩ := x₀
  obtain rfl : n = n₀ := hx.2
  dsimp only
  refine optRel_iteB (by rw [hom, K.opens]) (by trivial) (optRel_bind_same fun _ => ?_)
  refine optRel_bind (S := fun _ _ => True)
    (OptRel.mono (fun _ _ _ => by trivial) (amapM_all2_rel (S := BlkKeys False)
      (R := fun _ _ : Array E × Array E => True) (fun b b₀ hb => panelTabs_rel
        (fun a a₀ k => valAff_rel K.v.keys.iU3 K.v.keys.K3 hR k _ _) _ _ _ _ _ _ _ _ hb) hx.1))
    fun sides sides₀ _ => ?_
  exact optRel_pure ⟨K, hR, hx.1,
    (longTabs_size _ _ _).1.trans (longTabs_size _ _ _).1.symm,
    (longTabs_size _ _ _).2.trans (longTabs_size _ _ _).2.symm⟩

variable {D D₀ : StackData}

/-- A form's value at two data of one skeleton: there at both or at neither. -/
theorem val_rel (K : DataSkel D D₀) {a a₀ : Aff} (h : FormKeys a a₀) :
    OptRel (fun _ _ => True) (D.val a) (D₀.val a₀) := by
  unfold StackData.val
  rw [affFits_rel K.S.v.keys.iU3 K.S.v.keys.K3 K.R h]
  exact optRel_ite trivial trivial

/-- The weight claims' values: one for each claim, whatever the panels. -/
theorem claimVals_size (D : StackData) (rs : Array E) (n : Nat) :
    (D.bl.foldl
      (fun (V : Array E) b =>
        match b.v0 with
        | none => V
        | some v0 =>
          let EY := OnBytes.Model.eqLow rs 0 b.wy
          if b.tri then
            V.setIfInBounds v0
              (StackData.under (OnBytes.Model.eqLow rs b.wy b.w) EY b.ni b.ny
                (at2 (D.F.getD v0 #[]) (D.S.kkOf v0)))
          else
            (List.range b.ni).foldl
              (fun V i =>
                V.setIfInBounds (v0 + i)
                  (StackData.under #[OnBytes.oneE] EY 1 b.ny
                    fun _ yv => at2 (D.F.getD (v0 + i) #[]) (D.S.kkOf (v0 + i)) 0 yv))
              V)
      (Array.replicate n zeroE)).size = n := by
  rw [afoldl_size (fun V b => ?_), Array.size_replicate]
  cases b.v0 with
  | none => rfl
  | some v0 =>
    dsimp only
    split
    · exact Array.size_setIfInBounds ..
    · exact foldl_size (fun _ _ => Array.size_setIfInBounds ..) _ V

/-- **The true end values: as many**, at two lists of challenges of one length. -/
theorem endsAt_rel (K : DataSkel D D₀) {rs rs₀ : Array E} (hr : rs.size = rs₀.size) :
    OptRel (fun l l₀ : List E => l.length = l₀.length) (D.endsAt rs) (D₀.endsAt rs₀) := by
  unfold StackData.endsAt
  dsimp only
  rw [K.S.v.keys.y, K.S.Q]
  refine optRel_bind (stackEnd_keys (W := False) _ _ _ _ _ _ _ _ _ _ _ _ K.bl hr)
    fun fin fin₀ hf => ?_
  refine optRel_bind (val_rel K hf.2.1) fun _ _ _ => optRel_bind (val_rel K hf.2.2) fun _ _ _ => ?_
  refine optRel_bind (S := fun _ _ => True) (OptRel.mono (fun _ _ _ => by trivial)
    (afind_all2 (R := BlkKeys False) (fun b b₀ hb => by rw [hb.tri, hb.virt]) K.bl))
    fun _ _ _ => optRel_pure ?_
  have e1 := claimVals_size D rs D.S.opens.size
  have e2 := claimVals_size D₀ rs₀ D₀.S.opens.size
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_map,
    List.length_range, Array.length_toList]
  exact congrArg (_ + ·) (e1.trans (K.S.opens.trans e2.symm))

/-- **The batched sumcheck**, of what its functions read. -/
theorem jobStackOn_skel (K : DataSkel D D₀) : JobSkel (jobStackOn D) (jobStackOn D₀) := by
  have hq : D.S.Q.hp.lamS = D₀.S.Q.hp.lamS := by rw [K.S.Q]
  refine jobSkel_of (fits_sizes _ _ hq (by
      show OnBytes.Model.orderDefault _ = OnBytes.Model.orderDefault _
      rw [hq]) (by
      show #[D.SA, D.SB].map Array.size = #[D₀.SA, D₀.SB].map Array.size
      simp [K.SA, K.SB]) rfl rfl) hq rfl rfl rfl fun rs => ?_
  show ((D.endsAt rs.toArray.reverse).getD []).length = ((D₀.endsAt rs.toArray.reverse).getD
  []).length
  have r := endsAt_rel K (rs := rs.toArray.reverse) (rs₀ := rs.toArray.reverse) rfl
  revert r
  cases D.endsAt rs.toArray.reverse <;> cases D₀.endsAt rs.toArray.reverse <;> intro r
  · rfl
  · exact False.elim r
  · exact False.elim r
  · exact r

/-- The summand on given end values: there at both or at neither, at two lists of challenges of one
length. -/
theorem summandOn_rel (K : DataSkel D D₀) {rs rs₀ : Array E} (hr : rs.size = rs₀.size)
    (e e₀ : Array E) : OptRel (fun _ _ => True) (D.summandOn rs e) (D₀.summandOn rs₀ e₀) := by
  unfold StackData.summandOn StackData.sidesOn
  dsimp only
  rw [K.S.v.keys.y, K.S.Q]
  exact optRel_map' (R := fun _ _ => True)
    (optRel_bind (stackEnd_keys (W := False) _ _ _ _ _ _ _ _ _ _ _ _ K.bl hr)
      fun _ _ _ => True.intro) fun _ _ _ => True.intro

/-- CONDITIONAL: on P and hom. What the job's functions read, of a place. -/
theorem stackData_rel (Q : K4Pub) (w w₀ : K4In) {p p₀ : Pts} (P : PtsSkel p p₀)
    (hom : p.om.size = p₀.om.size) (sh sh₀ : Array E) :
    OptRel DataSkel (stackData Q w p sh) (stackData Q w₀ p₀ sh₀) := by
  unfold stackData
  exact optRel_bind (sidesOf_rel Q w w₀ P.fo) fun _ _ K => stackDataOn_rel K P hom sh sh₀

/-- CONDITIONAL: on P and hom. **The batched sumcheck**, at two inputs, two lists of sampled values
of one skeleton with as many powers of the element that joins the two passes (hom), and two lists of
shown values. -/
theorem jobStack_skel (Q : K4Pub) (w w₀ : K4In) {p p₀ : Pts} (P : PtsSkel p p₀)
    (hom : p.om.size = p₀.om.size) (sh sh₀ : Array E) :
    OptRel JobSkel (jobStack Q w p sh) (jobStack Q w₀ p₀ sh₀) := by
  unfold jobStack
  exact optRel_map' (stackData_rel Q w w₀ P hom sh sh₀) fun _ _ K => jobStackOn_skel K

end ProofFile.Honest.K4


#print axioms ProofFile.Honest.K4.panelTabs_rel
#print axioms ProofFile.Honest.K4.fillAt_size
#print axioms ProofFile.Honest.K4.longTabs_size
#print axioms ProofFile.Honest.K4.DataSkel
#print axioms ProofFile.Honest.K4.stackDataOn_rel
#print axioms ProofFile.Honest.K4.val_rel
#print axioms ProofFile.Honest.K4.claimVals_size
#print axioms ProofFile.Honest.K4.endsAt_rel
#print axioms ProofFile.Honest.K4.jobStackOn_skel
#print axioms ProofFile.Honest.K4.summandOn_rel
#print axioms ProofFile.Honest.K4.stackData_rel
#print axioms ProofFile.Honest.K4.jobStack_skel
