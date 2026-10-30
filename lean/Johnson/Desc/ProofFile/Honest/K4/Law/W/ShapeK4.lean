-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/ShapeK4.lean: CONDITIONAL: on h, Lh and hx. On
public data alone. AT EACH OF THE TWELVE GROUPS.

What is here. THE PLAN's ENTRY HAS THE ROWS AND THE COLUMNS OF THE FULL-SIZE EXAMPLE's TYPED SIZES
(`Sz.ref.shape`, Johnson/HonestTrace/Places.lean), AT EVERY MATRIX BUT THE PLANES' OF THE LIST OF
THE FEED-FORWARD LAYERS' OWN ROUNDS (sub-protocol K4), AT EVERY GROUP, UNDER THE LIBRARY's HEAD. It
is the premise hShape of `k4SymsRaw_all` (Law/W/SymsOfLaysCells.lean); `cellIsList_at`
(Law/W/CellIsListAt.lean) lays it in. It has the form of another house's `shape_at_plan`
(Honest/K5/Law/PackedAtSeg.lean) with the layers' segment for attention's. That house's law calls
`shapeNo_in_scope`, a law under Johnson/Goal/; this one does not call that law (on what it does rest
there: below). How. The columns, and the number of rows of symbols, are numerals under the head
(`XNine`, field size, Johnson/Road/K4/K4PlanNine.lean, by `xNine_of_laid`; the plan's sizes are the
segment's by `symsOne_head`, Law/W/SeatNumberK4.lean). That leaves each number of rows free within
three values. But it is a power of two: the plan's rows and columns are those of the verifier's own
list `tailsOf` (the field htm of `PubLines`, Johnson/Road/K4/PubAt.lean, had under the head by
`refPub_in_scope`, Johnson/Road/K4/RefInScope.lean), and the layout's rows are powers of two
(`Laid2`, Johnson/Road/FormsKeysAddr.lean: by its lemmas mrow0 to mrow3 and its field mxb; the
planes' row is a power of two in `tailsOf`'s own text), where af has three parts and ad one
(`Hd.parts_ref`, Johnson/Road/HeadZ.lean, at `Hd.eleven_of_core`). Of three neighbours from 4 on one
alone is a power of two. The typed sizes' own numbers: the rows by unfolding; the columns by the
library's `ref_cols`. Five statements with their proofs.

  `pow_of_symRows`   a power of two with as many rows of symbols as 2 ^ n, 2 ≤ n, is 2 ^ n.
  `tails_pow`   each entry of a group's list in `tailsOf` has a power of two as its number of rows.
  `shape_ref_ff`   on the typed sizes alone: the shape of the name with the number i is `sizeW i`.
  `plan_sizeW`   under h: the plan's entry has `sizeW i`'s rows and columns.
  `k4_shape_at_plan`   **the plan's entry has the typed sizes' rows and columns.**

Not shown here. Nothing on the planes' matrix in the last statement. Nothing on what a cell holds.
h: the library's hypothesis `P5J.AtMgA` on the public files; Lh (`LaidK4`, Law/SeatedHead.lean) and
hx follow from it at each of the twelve groups, as Law/W/MatsAreHead.lean's head says. All limits of
the heads of the files that it imports hold here; among them: closed facts by evaluation in Lean's
kernel lie beneath (`ref_cols`; those beneath `xNine_of_laid` and `symsOne_head`); no independent
checker that its writers know of has replayed them; through its imports it stands over files under
Johnson/Goal/. `plan_sizeW` RESTS ON A LAW OF A FILE UNDER Johnson/Goal/, CALLED BY NAME
(`Hd.core_of_scope`), as the library's own files call it; `refPub_in_scope` and `xNine_of_laid`,
which it calls too, rest on laws there, as their files' heads say. What those laws call its writers
have not read. TWO PREMISES ARE NEEDLESS, NOT IDLE: `shape_ref_ff`'s i ≠ 5 shuts a case that, by a
reader's arithmetic, holds too; hx could be paid inside (`layAt_laid`, Law/W/LayAtHead.lean); the
last statement keeps «μ ≠ .b» to have the premise's form to the sign. THE FULL SIZE ALONE, and the
format's second hash function alone (`OnBytes.secondHashFunction`). A LAW, NOT A PART: no file that defines a part of
the proof file's description may import this one. Nothing on soundness, on completeness or on any
other property.

Kin. `ProofFile.Honest.K5.shape_at_plan_ff_head` (Honest/K5/Law/ShapeAtLayers.lean; no part of the
library; not imported here; not read
here): from the head in the form `P5J.AtMg`, g < 12 and hP : (P5J.At.X Zp).G[g]? = some P it
has the same end at a plan P, at all twelve groups. hP at P := x.2.hp is `LaidK4`'s field hp. It is
said to call one law of a file under Johnson/Goal/; so does `plan_sizeW`, another one.
Neither is shown from the other.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.SeatNumberK4
import Johnson.HonestTrace.Packed
import Johnson.IMR.OwnKinds
import Johnson.Road.K4.RefInScope
import Johnson.Road.K4.Names.BorderKinds
import Johnson.Road.FormsKeysAddr

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes.Model.Layer (tailsOf matIx)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.HonestTrace (Sz Seg MatName nameNo_eq_some_iff no?_lt ref_cols)
open OnBytes.Road (Laid2 laid2_of_layout)
open OnBytes.Road.K4 (XNine xNine_of_laid written_of_head sizeW refPub_in_scope)
open OnBytes.Road.K4.Names (getD_map_range)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Block)
open VerifiableInference.Desc.First.Look (layAt)
open P5J (AtMgA TS)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

/-- A power of two with as many rows of symbols (three rows to a symbol) as 2 ^ n, 2 ≤ n, is
2 ^ n. -/
theorem pow_of_symRows {e n : ℕ} (hn : 2 ≤ n) (h : Alg.symRows (2 ^ e) = Alg.symRows (2 ^ n)) :
    2 ^ e = 2 ^ n := by
  unfold Alg.symRows at h
  have h4' : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (show 0 < 2 by decide) hn
  have h4 : 4 ≤ 2 ^ n := h4'
  rcases Nat.lt_trichotomy e n with c | c | c
  · have h1 : 2 ^ (e + 1) ≤ 2 ^ n := Nat.pow_le_pow_right (show 0 < 2 by decide) c
    rw [Nat.pow_succ] at h1
    omega
  · rw [c]
  · have h1 : 2 ^ (n + 1) ≤ 2 ^ e := Nat.pow_le_pow_right (show 0 < 2 by decide) c
    rw [Nat.pow_succ] at h1
    omega

/-- CONDITIONAL: the layout's plain facts L; af has three parts and ad one; g is a group; i is below
9. **Each entry of a group's list has a power of two as its number of rows.** -/
theorem tails_pow {y : OnBytes.Model.Layer.Lay} (L : Laid2 y) (p0 : y.parts.getD 0 0 = 3)
    (p1 : y.parts.getD 1 0 = 1) {g : ℕ} (hg : g < y.NGr) {i : ℕ} (hi : i < 9) :
    ∃ e, (((tailsOf y).getD g {}).mats.getD i {}).m = 2 ^ e := by
  have e8 : (matIx y).iXI = 8 := by
    show y.parts.getD 0 0 + y.parts.getD 1 0 + 4 = 8
    rw [p0, p1]
  unfold tailsOf
  dsimp only
  rw [getD_map_range _ hg]
  dsimp only
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getElem?_map, p0, p1, e8]
  by_cases h0 : g = 0
  · subst h0
    simp only [bne_self_eq_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    interval_cases i
    · exact ⟨_, L.mrow0⟩
    · exact ⟨_, L.mrow0⟩
    · exact ⟨_, L.mrow0⟩
    · exact ⟨_, L.mrow1⟩
    · exact ⟨_, L.mrow2⟩
    · exact ⟨_, rfl⟩
    · exact ⟨_, L.mrow3⟩
    · exact ⟨_, L.mxb⟩
    · exact ⟨_, L.mxb⟩
  · have hb : (g != 0) = true := bne_iff_ne.2 h0
    simp only [hb, Bool.and_true]
    interval_cases i
    · exact ⟨_, L.mrow0⟩
    · exact ⟨_, L.mrow0⟩
    · exact ⟨_, L.mrow0⟩
    · exact ⟨_, L.mrow1⟩
    · exact ⟨_, L.mrow2⟩
    · exact ⟨_, rfl⟩
    · exact ⟨_, L.mrow3⟩
    · exact ⟨_, L.mxb⟩
    · exact ⟨_, L.mxb⟩

/-- On the full-size example's typed sizes alone. At a group below 12, at a number that is not 5:
the shape of the name with the number i in the layers' segment's list is the library's `sizeW i`. -/
theorem shape_ref_ff {g i : ℕ} (hg : g < 12) (hi5 : i ≠ 5) {μ : MatName}
    (hμ : Sz.ref.nameNo (.ff g) i = some μ) : Sz.ref.shape (.ff g) μ = sizeW i := by
  have hno := (nameNo_eq_some_iff Sz.ref _ _ _).1 hμ
  have hi9 : i < 9 := no?_lt Sz.ref hno
  have hmu : Sz.ref.mu (.ff g) μ = some i := by
    unfold Sz.mu
    rw [if_pos (show Seg.Below Sz.ref.nGr (.ff g) from hg)]
    exact hno
  unfold Sz.shape
  rw [hmu, if_pos (show (some i).isSome = true from rfl)]
  clear hmu hno
  interval_cases i
  · obtain rfl : MatName.af 0 = μ := Option.some.inj hμ
    exact Prod.ext rfl (congrArg (fun l : List ℕ => l.getD 0 0) ref_cols)
  · obtain rfl : MatName.af 1 = μ := Option.some.inj hμ
    exact Prod.ext rfl (congrArg (fun l : List ℕ => l.getD 0 0) ref_cols)
  · obtain rfl : MatName.af 2 = μ := Option.some.inj hμ
    exact Prod.ext rfl (congrArg (fun l : List ℕ => l.getD 0 0) ref_cols)
  · obtain rfl : MatName.ad 0 = μ := Option.some.inj hμ
    exact Prod.ext rfl (congrArg (fun l : List ℕ => l.getD 1 0) ref_cols)
  · obtain rfl : MatName.ar = μ := Option.some.inj hμ
    exact Prod.ext rfl (congrArg (fun l : List ℕ => l.getD 2 0) ref_cols)
  · exact absurd rfl hi5
  · obtain rfl : MatName.qa = μ := Option.some.inj hμ
    exact Prod.ext rfl (congrArg (fun l : List ℕ => l.getD 4 0) ref_cols)
  · obtain rfl : MatName.xbO = μ := Option.some.inj hμ
    exact Prod.ext rfl (congrArg (fun l : List ℕ => l.getD 5 0) ref_cols)
  · obtain rfl : MatName.xbI = μ := Option.some.inj hμ
    exact Prod.ext rfl (congrArg (fun l : List ℕ => l.getD 6 0) ref_cols)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL: on h, Lh and hx; i is below 9. **The plan's entry has `sizeW i`'s rows and
columns**, the planes' too. -/
theorem plan_sizeW (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ} {x : Bool × Par}
    {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    {xl : VerifiableInference.Desc.First.Look.Place} (hx : layAt (P5J.At.X Zp) m = some xl)
    {i : ℕ} (hi : i < 9) :
    (x.2.hp.tl.mats.getD i {}).m = (sizeW i).1 ∧ (x.2.hp.tl.mats.getD i {}).k = (sizeW i).2 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hpub : OnBytes.Model.Verify.publicOf Z.pol Z.KL (some Z.lay) = .ok Zp.p.X :=
    O.W ▸ O.public
  have C := OnBytes.Road.Hd.core_of_scope h.scope h.reads hpub
  have H9 : XNine Zp.p.X := xNine_of_laid hpub C (written_of_head h.toAtMg).layout h.plan.laid
  obtain ⟨hσ, -, -, -⟩ := symsOne_head h Lh hx
  have sz := H9.size g Lh.lt i hi
  rw [← hσ] at sz
  have s1 : Alg.symRows (x.2.hp.tl.mats.getD i {}).m = Alg.symRows (sizeW i).1 :=
    congrArg Prod.fst sz
  have s2 : (x.2.hp.tl.mats.getD i {}).k = (sizeW i).2 := congrArg Prod.snd sz
  obtain ⟨s0, PL, -⟩ := (refPub_in_scope h.scope h.reads hpub Lh.lt).lines x.2.hp Lh.hp
  have P0 := PL #[]
  have B := (OnBytes.Road.Hd.eleven_of_core hpub C (OnBytes.Road.Hd.npOf Zp.p.X.hS)).1
  obtain ⟨p0, p1⟩ := OnBytes.Road.Hd.parts_ref P0.hy P0.S B.sized2
  obtain ⟨e, he⟩ := tails_pow (laid2_of_layout P0.hy) p0 p1 P0.hg hi
  have em : (x.2.hp.tl.mats.getD i {}).m = 2 ^ e :=
    (congrArg Prod.fst (IM.Own.getD_of_map (fun M : OnBytes.Model.TMat => (M.m, M.k)) P0.htm i
      {})).trans he
  refine ⟨?_, s2⟩
  rw [em] at s1 ⊢
  clear em he sz s2
  interval_cases i
  · exact pow_of_symRows (n := 16) (by decide) s1
  · exact pow_of_symRows (n := 16) (by decide) s1
  · exact pow_of_symRows (n := 16) (by decide) s1
  · exact pow_of_symRows (n := 15) (by decide) s1
  · exact pow_of_symRows (n := 13) (by decide) s1
  · exact pow_of_symRows (n := 16) (by decide) s1
  · exact pow_of_symRows (n := 16) (by decide) s1
  · exact pow_of_symRows (n := 16) (by decide) s1
  · exact pow_of_symRows (n := 16) (by decide) s1

/-- CONDITIONAL: on h, Lh and hx. **THE PLAN's ENTRY HAS THE TYPED SIZES' ROWS AND COLUMNS**, at
every matrix of the list but the planes'. -/
theorem k4_shape_at_plan (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {k m g : ℕ}
    {x : Bool × Par} {blk₀ : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk₀)
    {xl : VerifiableInference.Desc.First.Look.Place} (hx : layAt (P5J.At.X Zp) m = some xl) :
    ∀ i μ, Sz.ref.nameNo (.ff g) i = some μ → μ ≠ .b →
      (x.2.hp.tl.mats.getD i {}).m = (Sz.ref.shape (.ff g) μ).1 ∧
        (x.2.hp.tl.mats.getD i {}).k = (Sz.ref.shape (.ff g) μ).2 := by
  intro i μ hμ hb
  have hno := (nameNo_eq_some_iff Sz.ref _ _ _).1 hμ
  have hi9 : i < 9 := no?_lt Sz.ref hno
  have hi5 : i ≠ 5 := by
    rintro rfl
    exact hb (Option.some.inj hμ).symm
  rw [shape_ref_ff Lh.lt hi5 hμ]
  exact plan_sizeW h Lh hx hi9

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.pow_of_symRows
#print axioms ProofFile.Honest.K4.W.tails_pow
#print axioms ProofFile.Honest.K4.W.shape_ref_ff
#print axioms ProofFile.Honest.K4.W.plan_sizeW
#print axioms ProofFile.Honest.K4.W.k4_shape_at_plan
