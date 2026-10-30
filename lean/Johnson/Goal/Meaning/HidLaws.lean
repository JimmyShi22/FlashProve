-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HidLaws.lean: from what the library's laws on single sub-proofs conclude to
Means at hidOf.

Johnson/Goal/Meaning/HidOwn.lean leaves eleven clauses (OwnG, OwnA, HeadPlain). The library's laws
on a sub-proof end in records: LayerOrd at mzTot Mz (layer_start_base,
Johnson/Road/Rows/LayerStart.lean) and AttOrd at zsOf pl Mz (att_ord_base,
Johnson/Road/Rows/AttStartBase.lean). This file carries these records to Means at hidOf, and to the
lists ownOf s y that Part B of Johnson/Goal/Meaning/HidOwn.lean makes of the committed symbols.

Main names:
  Inside s S   a public premise: the place addrA S c of every valid name c lies within the sizes s.
  PlanSizes, Fills, inside_of_plan   Inside holds if s has the sizes of the plan's list, the shape
    has the reference sizes (AttSized) and four of its numbers are at least the library's (Fills).
  attOrd_mzTot, attOrd_ownOf   under PlaceOK pl and Inside, AttOrd at zsOf pl Mz gives AttOrd at
    mzTot Mz: the relation reads valid names only (rfraw_valid, Johnson/Road/Lane5AttValid.lean).
  layerOrd_ownOf   LayerOrd at mzTot Mz, with BaseAt, is LayerOrd at ownOf.
  ownApart_of_sized, ownApart_of_core   the public premise OwnApart of means_of_seen holds at the
    reference sizes, and so in scope.
  oneWord_of_rect   OneWord from equations within rectangles: qa's at rows below 65,536 and columns
    below 1,536, the library's sizes of qa.
  means_of_ords   THE SUM: in scope, for every family seen of 25 lists: from the 24 records at seen,
    the head's clause at the stream that the library reads in the head's own cells, and the 24
    equations, Means at hidOf X tok seen. (seen is a letter: seen (2 g + 1) may be ownOf, or zsOf pl
    Mz as att_ord_base has it; what OneWord's payer needs at zsOf stands in the head of
    Johnson/Goal/Meaning/HidOwn.lean.)

What is not claimed. The 24 equations (OneWord, HeadWord) are derived from no run and from no
commitment (Johnson/Goal/Meaning/HidWord.lean brings them down to "the same sizes and the same
symbols"). That a sub-proof's signature has the sizes of the plan's list (PlanSizes): a statement on
public numbers alone; it holds of sizes that follow the plans
(Johnson/Goal/Meaning/HidPlanSizes.lean); that a real signature does is shown nowhere. (Fills holds
in scope: Johnson/Goal/Meaning/HidFills.lean.) That any run meets the records. Nothing on
probabilities or on hiding. The program does not import this file.
-/
import Johnson.Goal.Meaning.HidHead
import Johnson.Road.Lane5AttValid
import Johnson.Road.Lane5AttMx

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open Inst.Model Inst.Model.All
open OnBytes OnBytes.Road OnBytes.Road.L5 OnBytes.Road.Rows.Norms
open OnBytes.Model.Verify (publicOf layerShape)
open OnBytes.Model.Layer (Lay matIx)
open Inst.Model.AttSeg (Raw)
open Cb.Pv.Tail (Size Syms JCell BaseAt Base)

/-! ## Attention: from the map of places to the total matrices -/

/-- **Every valid name's place lies within the sizes**: its number in the list is below the number
of matrices, its column and its row are below that matrix's. -/
def Inside (s : Size) (S : Attention.Shape) : Prop :=
  ∀ c : Raw, c.Valid (dimOf S) → (addrA S c).1 < s.NM ∧
    (addrA S c).2.2 < s.k (addrA S c).1 ∧ (addrA S c).2.1 < s.m (addrA S c).1

/-- Within the sizes the two total forms have one entry. -/
theorem zsOf_mzTot {s : Size} {pl : ℕ → ℕ → ℕ → JCell s} (hp : Rows.PlaceOK pl)
    (Mz : ∀ μ : Fin s.NM, Fin (s.k μ) → Fin (s.m μ) → ℤ) {a r c : ℕ} (h : a < s.NM)
    (hc : c < s.k a) (hr : r < s.m a) : Rows.zsOf pl Mz a r c = mzTot Mz a r c := by
  have e := Rows.zsOf_at hp Mz ⟨a, h⟩ ⟨c, hc⟩ ⟨r, hr⟩
  unfold mzTot
  rw [dif_pos h, dif_pos hc, dif_pos hr]
  exact e

/-- **The record at the map of places gives the record at the total matrices.** -/
theorem attOrd_mzTot {s : Size} {S : Attention.Shape} {pl : ℕ → ℕ → ℕ → JCell s}
    (hp : Rows.PlaceOK pl) (hin : Inside s S)
    {Mz : ∀ μ : Fin s.NM, Fin (s.k μ) → Fin (s.m μ) → ℤ} (O : AttOrd S (Rows.zsOf pl Mz)) :
    AttOrd S (mzTot Mz) :=
  ⟨V.rfraw_valid (scl := sclOf S) (fun c hc => by
    obtain ⟨h, hc', hr⟩ := hin c hc
    exact zsOf_mzTot hp Mz h hc' hr) O.rel⟩

/-! ## Inside, at the sizes of the plan's list and the reference numbers -/

/-- The sizes s are those of the list of matrices of the attention sub-proof's plan
(OnBytes/Model/AttentionPlan.lean: matrices): the parts of as, then ah, ao, bA and qa. (bA's sizes
are not asked: no name of a cell has its place there.) -/
structure PlanSizes (s : Size) (S : Attention.Shape) : Prop where
  NM : s.NM = S.cf.NAs + 4
  asM : ∀ q < S.cf.NAs, s.m q = 2 ^ S.cf.lmS
  asK : ∀ q < S.cf.NAs, s.k q = S.kAs / S.cf.NAs
  ahM : s.m S.cf.NAs = S.cf.wcH * S.T
  ahK : s.k S.cf.NAs = S.fillH / S.cf.wcH
  aoM : s.m (S.cf.NAs + 1) = S.cf.wcO * S.T
  aoK : s.k (S.cf.NAs + 1) = S.fillO / S.cf.wcO
  qaM : s.m (S.cf.NAs + 3) = S.cf.wcQ * S.T
  qaK : s.k (S.cf.NAs + 3) = S.fillQ / S.cf.wcQ

/-- Four numbers of the shape are at least the library's: the columns of as, all parts together, and
the features, with filler, of ah, ao and qa. -/
structure Fills (S : Attention.Shape) : Prop where
  as : 7200 ≤ S.kAs / S.cf.NAs * S.cf.NAs
  ah : 2880 ≤ S.fillH
  ao : 40960 ≤ S.fillO
  qa : 98304 ≤ S.fillQ

/-- **At the reference sizes every valid name's place lies within the sizes of the plan's list.** By
the library's own statement that every cell lies inside its matrix (addrRange,
Inst/Model/Att/AddrFacts.lean) and addrA_ref (Johnson/Road/Lane5AttAddr.lean). -/
theorem inside_of_plan {s : Size} {S : Attention.Shape} (hS : AttSized S) (F : Fills S)
    (P : PlanSizes s S) : Inside s S := by
  intro c hv
  have hv' : c.Valid DA := by
    rw [dimOf_ref hS, hS.u0] at hv
    exact hv
  obtain ⟨h1, h2⟩ := AttSeg.AddrFacts.addrRange DA KA AttSeg.Calls.ref AttSeg.ref_dim_ok c hv'
  rw [addrA_ref hS c]
  have hb : (AttSeg.addr DA KA c).1 ≠ .b := by
    cases c with
    | c ρ jj b x => cases ρ <;> exact fun e => by cases e
    | _ => exact fun e => by cases e
  generalize AttSeg.addr DA KA c = a at h1 h2 hb ⊢
  obtain ⟨μ, r, col⟩ := a
  cases μ with
  | as =>
    have h1' : r < 65536 := Cm.Seg.attRow_as ▸ h1
    have h2' : col < 7200 := AttSeg.ref_cols.1 ▸ h2
    have hw : col < S.kAs / S.cf.NAs * S.cf.NAs := lt_of_lt_of_le h2' F.as
    have hq : col / (S.kAs / S.cf.NAs) < S.cf.NAs := Nat.div_lt_of_lt_mul hw
    have hpos : 0 < S.kAs / S.cf.NAs := Nat.pos_of_ne_zero fun e => by
      rw [e, Nat.zero_mul] at hw
      exact absurd hw (Nat.not_lt_zero _)
    show col / (S.kAs / S.cf.NAs) < s.NM ∧
      col % (S.kAs / S.cf.NAs) < s.k (col / (S.kAs / S.cf.NAs)) ∧
      r < s.m (col / (S.kAs / S.cf.NAs))
    rw [P.NM, P.asK _ hq, P.asM _ hq, hS.lmS]
    exact ⟨by omega, Nat.mod_lt _ hpos, h1'⟩
  | ah =>
    have h1' : r < 8192 := Cm.Seg.attRow_ah ▸ h1
    have h2' : col < 360 := AttSeg.ref_cols.2.1 ▸ h2
    have hF := F.ah
    show S.cf.NAs < s.NM ∧ col < s.k S.cf.NAs ∧ r < s.m S.cf.NAs
    rw [P.NM, P.ahK, P.ahM, hS.wcH, hS.T]
    exact ⟨by omega, by omega, by omega⟩
  | ao =>
    have h1' : r < 65536 := Cm.Seg.attRow_ao ▸ h1
    have h2' : col < 640 := AttSeg.ref_cols.2.2.1 ▸ h2
    have hF := F.ao
    show S.cf.NAs + 1 < s.NM ∧ col < s.k (S.cf.NAs + 1) ∧ r < s.m (S.cf.NAs + 1)
    rw [P.NM, P.aoK, P.aoM, hS.wcO, hS.T]
    exact ⟨by omega, by omega, by omega⟩
  | b => exact absurd rfl hb
  | qa =>
    have h1' : r < 65536 := attRow_qa ▸ h1
    have h2' : col < 1536 := AttSeg.ref_cols.2.2.2.2 ▸ h2
    have hF := F.qa
    show S.cf.NAs + 3 < s.NM ∧ col < s.k (S.cf.NAs + 3) ∧ r < s.m (S.cf.NAs + 3)
    rw [P.NM, P.qaK, P.qaM, hS.wcQ, hS.T]
    exact ⟨by omega, by omega, by omega⟩

section Own
variable {s : ℕ → Size} {y : ∀ k, Syms Cb.Gl.E (s k)} {k : ℕ}

/-- The same at the list behind the committed symbols. -/
theorem attOrd_ownOf {S : Attention.Shape} {pl : ℕ → ℕ → ℕ → JCell (s k)} (hp : Rows.PlaceOK pl)
    (hin : Inside (s k) S) (O : AttOrd S (Rows.zsOf pl (Rows.mzAt (y k)))) :
    AttOrd S (ownOf s y k) := attOrd_mzTot hp hin O

/-- The layers' record, at whatever integers stand behind the symbols, is the record at ownOf. -/
theorem layerOrd_ownOf (p : ℕ) [CharP Cb.Gl.E p] (hu : (s k).Uniq p)
    {Mz : ∀ μ : Fin (s k).NM, Fin ((s k).k μ) → Fin ((s k).m μ) → ℤ} (hB : BaseAt (y k) Mz)
    {h : Model.Layer.Shape} {sc : Model.Layer.Scales} {yl : Lay} {g : ℕ} {Wi : Mat}
    {x : Cm.Seg.XI} (O : LayerOrd h sc yl g (mzTot Mz) Wi x) :
    LayerOrd h sc yl g (ownOf s y k) Wi x := by
  rw [ownOf_unique p hu hB]
  exact O

end Own

/-! ## The fence's two public lemmas -/

/-- At the reference sizes a valid name is valid at the library's sizes. -/
theorem valid_ref {S : Attention.Shape} (hS : AttSized S) {c : Raw} (hv : c.Valid (dimOf S)) :
    c.Valid DA := by
  rw [dimOf_ref hS, hS.u0] at hv
  exact hv

/-- **No own cell of an attention sub-proof lies in number NAs + 3 of the list**, at the reference
sizes, if the parts of as have 7,200 columns together. -/
theorem ownApart_of_sized {S : Attention.Shape} (hS : AttSized S)
    (hw : 7200 ≤ S.kAs / S.cf.NAs * S.cf.NAs) : OwnApart S := by
  intro c hv ho
  have hv' := valid_ref hS hv
  obtain ⟨-, h2⟩ := AttSeg.AddrFacts.addrRange DA KA AttSeg.Calls.ref AttSeg.ref_dim_ok c hv'
  cases c with
  | c ρ jj b x =>
    rw [addrA_ref hS]
    have e : (AttSeg.addr DA KA (.c ρ jj b x)).1 = .as := by cases ρ <;> rfl
    generalize AttSeg.addr DA KA (.c ρ jj b x) = a at h2 e ⊢
    obtain ⟨μ, r, col⟩ := a
    simp only at e
    subst e
    have h2' : col < 7200 := AttSeg.ref_cols.1 ▸ h2
    have hq : col / (S.kAs / S.cf.NAs) < S.cf.NAs :=
      Nat.div_lt_of_lt_mul (lt_of_lt_of_le h2' hw)
    show col / (S.kAs / S.cf.NAs) ≠ S.cf.NAs + 3
    omega
  | mx k b g i => exact fun e => by have e' : S.cf.NAs = S.cf.NAs + 3 := e; omega
  | den k b g i => exact fun e => by have e' : S.cf.NAs = S.cf.NAs + 3 := e; omega
  | ib k b g i => exact fun e => by have e' : S.cf.NAs = S.cf.NAs + 3 := e; omega
  | qh b g i n => exact fun e => by have e' : S.cf.NAs + 1 = S.cf.NAs + 3 := e; omega
  | qh' b g i n => exact fun e => by have e' : S.cf.NAs + 1 = S.cf.NAs + 3 := e; omega
  | qry k b g i n => exact Bool.noConfusion (ho : false = true)
  | out k b g i n => exact Bool.noConfusion (ho : false = true)
  | key k lam g j n => exact Bool.noConfusion (ho : false = true)
  | val k lam g j n => exact Bool.noConfusion (ho : false = true)

/-- In scope. -/
theorem ownApart_of_core {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}
    (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) :
    ∀ g < 12, OwnApart (Hd.shapeA X g) := fun g hg =>
  have E := Hd.eleven_of_core h C (Hd.npOf X.hS)
  ownApart_of_sized (E.2.1 g hg) (E.2.2.2.2 g hg)

/-- **OneWord from equations within rectangles**: the 12 on qa at rows below 65,536 and columns
below 1,536. -/
theorem oneWord_of_rect {X : Model.Verify.Public} {seen : ℕ → Mats ℤ}
    (hS : ∀ g < 12, AttSized (Hd.shapeA X g))
    (ff : ∀ g, 0 < g → g < 12 → ∀ r c,
      seen (2 * g) (matIx X.y).iXI r c = seen (2 * (g - 1)) (matIx X.y).iXO r c)
    (att : ∀ g < 12, ∀ r < 65536, ∀ c < 1536,
      seen (2 * g + 1) ((Hd.shapeA X g).cf.NAs + 3) r c = seen (2 * g) (matIx X.y).iQA r c) :
    OneWord X seen :=
  ⟨ff, fun g hg c hv ho => by
    have hq : (AttSeg.addr DA KA c).1 = .qa := by
      cases c <;> first | rfl | exact Bool.noConfusion (ho : true = false)
    obtain ⟨b1, b2⟩ := qa_range c (valid_ref (hS g hg) hv) hq
    have e := addrA_ref (hS g hg) c
    have e1 : (addrA (Hd.shapeA X g) c).2.1 = (AttSeg.addr DA KA c).2.1 := by
      rw [e]
      unfold portOf
      rw [hq]
    have e2 : (addrA (Hd.shapeA X g) c).2.2 = (AttSeg.addr DA KA c).2.2 := by
      rw [e]
      unfold portOf
      rw [hq]
    unfold zAt
    rw [addrA_borrowed _ ho]
    exact att g hg _ (e1 ▸ b1) _ (e2 ▸ b2)⟩

/-! ## The sum -/

/-- **In scope, for every family seen of 25 lists: the 24 records at seen, the head's clause at the
stream that the library reads in the head's own cells, and the 24 equations give Means at hidOf.**
-/
theorem means_of_ords {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}
    (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) {seen : ℕ → Mats ℤ} {pp : ScalesAndPolicy}
    {i : Cm.Idx} {x : Instance ppref} (tok : Fin ppref.V) (A : OneWord X seen)
    (W : HeadWord X seen)
    (G : ∀ g < 12, LayerOrd (layerShape X.P) X.layers.sc X.y g (seen (2 * g)) i.mat x)
    (At : ∀ g < 12, AttOrd (Hd.shapeA X g) (seen (2 * g + 1)))
    (H : HeadPlain pp i x (headStream X (seen 24))) : Means X pp i x (hidOf X tok seen) :=
  means_of_cells h C tok A W (ownApart_of_core h C) (fun g hg => ownG_of_ord (G g hg))
    (fun g hg => ownA_of_ord (At g hg)) H

end Meaning

#print axioms Meaning.zsOf_mzTot
#print axioms Meaning.attOrd_mzTot
#print axioms Meaning.inside_of_plan
#print axioms Meaning.attOrd_ownOf
#print axioms Meaning.layerOrd_ownOf
#print axioms Meaning.valid_ref
#print axioms Meaning.ownApart_of_sized
#print axioms Meaning.ownApart_of_core
#print axioms Meaning.oneWord_of_rect
#print axioms Meaning.means_of_ords
