-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/CarriedRows.lean (kind K10; for the code switching's condition in
front): FOUR FACTS ON THE ROWS THAT A CLOSING LAYS INTO THE FRAME, OFF THE CLOSING's OWN YES. A
definition, statements and proofs.

Why. The next link's code switching reads the frame's field rows (`SingleRows`,
OnBytes/Iop/Fold.lean): what the last closing returned. Its one test on a switch's front
asks nineteen plain facts; four of them speak of these rows and had no payer. All four follow from
the closing's yes and the text of `foldOutput`.
  `foldLowOnce_size`, `foldLow_size`, `foldMaskForm_size`, `later_length`, `foldMaskWeights_size`:
    lengths: a fold at one element halves a vector; the folded old mask's coefficients; the fresh
    mask's public weights are len many where h ≤ k and 2 k + 1 - h ≤ len.
  `fold_range_zip`, `kept_sum`: a fold over the places of two equally long lists against a sum over
    the pairs whose flag is true.
  `out_kept`, `out_keptRows`, `out_vars`, `out_d0`, `out_d1`: the facts at `foldOutput S' F row m
    eps gs claim`, each under what it spends: the layout has a flag a member; `foldRowOk S' F row`;
    as many challenges as row variables; h ≤ k; the hiding polynomial's columns fit the mask code.
  `CarriedOk P G S' out`: THE FOUR, AS ONE STRUCTURE: kept: `switchKept out` is the group G's
    members whose flag says "kept", in order; keptRows: out.keptRows is the sum of these messages'
    main rows in S'; vars: every tensor of out.c has the exponent of the main code's message length
    as its number of variables; d0, d1: out.d's two vectors have JUST the mask code's message length
    (asked was: at most).
  `closing_carried`: closing P S g mask rs = .ok (out, S') gives a group G at S.groups[g] with
    `CarriedOk P G S' out`. `closeFrame_carried`: the like at a yes of `closeFrame`, of x.1.rows:
    the rows that the frame behind carries; the plan's two code numbers are the frame's shape's. By:
    `closing_iff`, `fold_iff`, `bat_iff`, `closeFrame_iff` (CloseMeans.lean, beside this file);
    `bat_inv_layout` (BatAtClosing.lean); `fold_inv2` (InvMore.lean); `foldShapeFits_iff`
    (Johnson/Desc/Own/FoldMean.lean); `Form.fixLow_shape` (OnBytes/Iop/FixLaws.lean); `layout_eq`
    (LayBlocks.lean).
Limits. THE STATE RIGHT BEHIND THE CLOSING ALONE: that nobody turns the frame's rows, the messages'
shapes or the codes between the closing and the next code switching is a walk's, not shown here. G
is the group IN FRONT of the closing (its members and flags ride: GroupsStay.lean). Which numbers
G's members are is not said. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.Whole
import Johnson.Desc.First.Close.Law.CloseMeans
import Johnson.Desc.Own.FoldMean
import OnBytes.Iop.FixLaws
import OnBytes.Iop.Cs
import Johnson.Desc.First.Close.Law.LayBegun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes

/-! ### Lengths -/

theorem foldLowOnce_size (v : Array E) (g : E) : (foldLowOnce v g).size = v.size / 2 := by
  unfold foldLowOnce
  rw [Array.size_ofFn]

theorem foldLow_size : ∀ (g : List E) (v : Array E), (foldLow v g).size = v.size / 2 ^ g.length
  | [], v => by simp [foldLow]
  | a :: g, v => by
    have e : foldLow v (a :: g) = foldLow (foldLowOnce v a) g := rfl
    rw [e, foldLow_size g, foldLowOnce_size, List.length_cons, Nat.div_div_eq_div_mul, pow_succ,
      Nat.mul_comm]

/-- The folded old mask's coefficients: as many as the written-out vector has, divided by 2 to the
number of the variables that are folded. -/
theorem foldMaskForm_size (h : ℕ) (d : Array E) (eps : E) (g : List E) :
    (foldMaskForm h d eps g).size = d.size / 2 ^ min h g.length := by
  unfold foldMaskForm
  rw [Array.size_map, foldLow_size, List.length_take]

theorem later_length {α : Type} (a b : ℕ → α) : ∀ n : ℕ,
    ((List.range n).flatMap fun i => (if i == 0 then [] else [a i]) ++ [b i]).length = 2 * n - 1
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, List.length_append, later_length a b n]
    cases n with
    | zero => rfl
    | succ m =>
      simp
      omega

/-- The fresh mask's public weights: len of them, where the hiding polynomial's columns fit. -/
theorem foldMaskWeights_size (k h len : ℕ) (g : Array E) (hh : h ≤ k) (hc : 2 * k + 1 - h ≤ len) :
    (foldMaskWeights k h len g).size = len := by
  unfold foldMaskWeights
  simp only [List.size_toArray, List.length_append, List.length_replicate, List.length_cons,
    List.length_map, List.length_range, later_length]
  by_cases e : h < k
  · simp only [e, if_true, List.length_cons, List.length_nil]
    omega
  · simp only [e, if_false, List.length_nil]
    omega

/-! ### The kept rows: a fold against a sum -/

theorem fold_range_zip (f : ℕ → ℕ) (d : ℕ) : ∀ (ml : List ℕ) (kl : List Bool) (a : ℕ),
    ml.length = kl.length →
    (List.range ml.length).foldl
        (fun n i => if kl.getD i false then n + f (ml.getD i d) else n) a =
      a + (((ml.zip kl).filter (·.2)).map fun p => f p.1).sum
  | [], _, a, _ => by simp
  | x :: ml, [], _, h => by simp at h
  | x :: ml, y :: kl, a, h => by
    have h' : ml.length = kl.length := by simpa using h
    rw [List.length_cons, List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    rw [fold_range_zip f d ml kl _ h', List.zip_cons_cons]
    cases y with
    | true => simp; omega
    | false => simp

/-- The same on arrays. -/
theorem kept_sum (f : ℕ → ℕ) (mem : Array ℕ) (kept : Array Bool) (hk : kept.size = mem.size) :
    (List.range mem.size).foldl
        (fun n i => if kept.getD i false then n + f (mem.getD i noId) else n) 0 =
      ((((mem.zip kept).filter (·.2)).map (·.1)).toList.map f).sum := by
  obtain ⟨ml⟩ := mem
  obtain ⟨kl⟩ := kept
  have h' : ml.length = kl.length := by simpa using hk.symm
  have e := fold_range_zip f noId ml kl 0 h'
  have g1 : ∀ i, (ml.toArray).getD i noId = ml.getD i noId := fun i => by
    simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  have g2 : ∀ i, (kl.toArray).getD i false = kl.getD i false := fun i => by
    simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  simp only [g1, g2, List.size_toArray]
  rw [e]
  simp [List.map_map, Function.comp_def]

/-! ### The four facts at the fold's new statement -/

section
variable (S' : Statement) (F : FoldShape) (row : GroupRow) (m : ℕ) (eps : E) (gs : List E)
  (claim : E)

/-- (2) What the next code switching keeps is read off the fold's layout. -/
theorem out_kept : switchKept (foldOutput S' F row m eps gs claim) =
    ((F.layout.members.zip F.layout.kept).filter (·.2)).map (·.1) := rfl

/-- (16) **The number of kept rows is the sum of the kept members' main rows.** -/
theorem out_keptRows (hk : F.layout.kept.size = F.layout.members.size) :
    (foldOutput S' F row m eps gs claim).keptRows =
      ((switchKept (foldOutput S' F row m eps gs claim)).toList.map fun o =>
        ((S'.oracles[o]?).map (·.shape.mainRows)).getD 0).sum := by
  rw [out_kept]
  exact kept_sum (fun o => ((S'.oracles[o]?).map (·.shape.mainRows)).getD 0) _ _ hk

/-- (17) **Every tensor of the main row's coefficients has the code's number of place bits.** -/
theorem out_vars (hr : foldRowOk S' F row = true) (hl : gs.length = F.layout.k) :
    ∀ v ∈ (foldOutput S' F row m eps gs claim).c.tensors,
      v.vars = (S'.codes.base.getD F.code default).logEll := by
  intro v hv
  unfold foldRowOk at hr
  simp only [Bool.and_eq_true] at hr
  have hf := hr.1.1
  have hall : ∀ t ∈ row.c.tensors,
      t.vars = F.layout.k + ceilLog2 (S'.codes.base.getD F.code default).ell ∧ t.InOrder := by
    intro t ht
    unfold Form.fits at hf
    simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hf
    exact ⟨(hf.1 t ht).1, t.inOrder_of_ok (hf.1 t ht).2⟩
  have h := (Form.fixLow_shape row.c gs eps _ hall v hv).1
  rw [h, hl]
  unfold Code.logEll
  omega

/-- (18) The folded old mask's coefficients are at most the mask code's message length. -/
theorem out_d0 (hr : foldRowOk S' F row = true) (hl : gs.length = F.layout.k)
    (hh : F.layout.h ≤ F.layout.k) :
    ((foldOutput S' F row m eps gs claim).d.getD 0 #[]).size =
      (S'.codes.mask.getD F.maskCode default).ell := by
  unfold foldRowOk at hr
  simp only [Bool.and_eq_true, beq_iff_eq] at hr
  show (foldMaskForm F.layout.h row.d eps gs).size = _
  rw [foldMaskForm_size, hr.1.2, hl, Nat.min_eq_left hh, Nat.mul_div_cancel _ (by positivity)]

/-- (19) The fresh mask's public weights likewise. -/
theorem out_d1 (hh : F.layout.h ≤ F.layout.k)
    (hc : 2 * F.layout.k + 1 - F.layout.h ≤ (S'.codes.mask.getD F.maskCode default).ell) :
    ((foldOutput S' F row m eps gs claim).d.getD 1 #[]).size =
      (S'.codes.mask.getD F.maskCode default).ell :=
  foldMaskWeights_size _ _ _ _ hh hc

end

/-! ### At a yes of the closing -/

/-- **THE FOUR FACTS ON THE ROWS THAT A CLOSING LAYS.** -/
structure CarriedOk (P : Plan) (G : Group) (S' : Statement) (out : SingleRows) : Prop where
  /-- (2) what the next code switching keeps: the group's members whose flag says "kept" -/
  kept : switchKept out = ((G.members.zip G.kept).filter (·.2)).map (·.1)
  /-- (16) -/
  keptRows : out.keptRows =
    ((switchKept out).toList.map fun o => ((S'.oracles[o]?).map (·.shape.mainRows)).getD 0).sum
  /-- (17) -/
  vars : ∀ v ∈ out.c.tensors, v.vars = (S'.codes.base.getD P.code default).logEll
  /-- (18) -/
  d0 : (out.d.getD 0 #[]).size = (S'.codes.mask.getD P.maskCode default).ell
  /-- (19) -/
  d1 : (out.d.getD 1 #[]).size = (S'.codes.mask.getD P.maskCode default).ell

theorem closing_carried {P : Plan} {S S' : Statement} {g : ℕ} {mask : Option ℕ}
    {rs : List Fmt.RoundView} {out : SingleRows} (h : closing P S g mask rs = .ok (out, S')) :
    ∃ G, S.groups[g]? = some G ∧ CarriedOk P G S' out := by
  obtain ⟨eB, es, rB, rs', -, -, m, -, row, L, S1, hB, ⟨-, -⟩, hF⟩ :=
    (closing_iff P S g mask rs out S').1 h
  obtain ⟨G, x, hG, -, -, hS1, hl0, -⟩ := bat_inv_layout ((bat_iff _ _ _ _ _ _ _).2 hB)
  have hfold := (fold_iff _ _ _ _ _ _ _ _).2 hF
  obtain ⟨-, -, -, -, -, -, -, -, hshape, -⟩ := hF
  obtain ⟨rE, rR, sum, eps, qs, gs, S2, -, -, -, -, b5, b6, b7, b8, b9⟩ := fold_inv2 hfold
  subst b8
  obtain ⟨c, zk, -, hzk, -, f2, -, f4, f5, -⟩ := (Own.foldShapeFits_iff _ _).1 hshape
  have hz : (S'.codes.mask.getD P.maskCode default) = zk := by
    rw [b7, Array.getD_eq_getD_getElem?]
    have : S1.codes.mask[P.maskCode]? = some zk := hzk
    rw [this]
    rfl
  have hLm : L.members = G.members ∧ L.kept = G.kept := by
    rw [OnBytes.LayLaw.layout_eq S g G hG] at hl0
    obtain rfl := Option.some.inj hl0
    exact ⟨rfl, rfl⟩
  refine ⟨G, hG, ?_⟩
  subst b9
  refine ⟨?_, out_keptRows _ _ _ _ _ _ _ f5, out_vars _ _ _ _ _ _ _ b6 b5,
    out_d0 _ _ _ _ _ _ _ b6 b5 f2, out_d1 _ _ _ _ _ _ _ f2 ?_⟩
  · rw [out_kept]
    show ((L.members.zip L.kept).filter (·.2)).map (·.1) = _
    rw [hLm.1, hLm.2]
  · show _ ≤ (S'.codes.mask.getD P.maskCode default).ell
    rw [hz]
    exact f4

/-- **At a yes of the frame's closing of a link**: of the rows that the frame behind carries. -/
theorem closeFrame_carried {owed : Option ℕ} {f : ReqFrame} {S : Statement}
    {es : List Fmt.Entry} {rs : List Fmt.RoundView} {x : ReqFrame × Statement}
    (h : closeFrame owed f S es rs = .ok x) :
    ∃ (Gf : ReqGroup) (G : Group), f.groups[f.link]? = some Gf ∧ S.groups[f.group]? = some G ∧
      CarriedOk { code := f.shape.code, maskCode := f.shape.maskCode, k := Gf.k, h := Gf.h,
                  entries := es } G x.2 x.1.rows := by
  obtain ⟨-, Lk, -, Gf, hGf, -, rows, hc, e⟩ := (closeFrame_iff owed f S es rs x.1 x.2).1 h
  obtain ⟨G, hG, hC⟩ := closing_carried ((closing_iff _ _ _ _ _ _ _).2 hc)
  refine ⟨Gf, G, hGf, hG, ?_⟩
  rw [e]
  exact hC

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.closing_carried
#print axioms VerifiableInference.Desc.First.Close.closeFrame_carried
#print axioms VerifiableInference.Desc.First.Close.out_keptRows
#print axioms VerifiableInference.Desc.First.Close.out_vars
#print axioms VerifiableInference.Desc.First.Close.out_d0
#print axioms VerifiableInference.Desc.First.Close.out_d1
#print axioms VerifiableInference.Desc.First.Close.foldMaskForm_size
#print axioms VerifiableInference.Desc.First.Close.foldMaskWeights_size
#print axioms VerifiableInference.Desc.First.Close.fold_range_zip
