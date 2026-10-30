-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HidPlanNM.lean: in the verifier's plans each record's number of matrices is the
length of its list, at every public file in scope; so the library's own sizes follow the plans.

nmFit X (Johnson/Goal/Meaning/HidPlan.lean) asks, of each of the 25 records of a smallness test in
X's plans, that its field NM is the length of its list of matrices. The library has this of the
plans of the groups of layers (plan_sizes, Johnson/Road/FormsKeysPlan.lean). For an attention
sub-proof's plan and for the head's the library's lemmas on the makers of records keep NM beside the
list (shape_mats, addTrees_keeps, borderMeans_keeps, ownerHeld_keeps), but its theorems on these
plans state the list alone. This file walks the same steps for NM.

Main names:
  seamShape_nm, seamPlan_nm, plan_nm   the plan that Attention.plan returns.
  place_nm, owners_nm   attentionOwners keeps each record's list and NM.
  planH2_nm   the plan that planH2 returns.
  nmFit_of_core   nmFit X = true, in scope.
  follows_of_core, follows_closed   Follows X (sizesOf X): the library's own sizes (sizeOf) follow
    the plans, in scope; and so at every family of records with the plans' lists and numbers of
    matrices (the closed records, at which the smallness test stands, among them).
  words_sizesOf   so, in scope, at s := sizesOf X, the 24 equations hold at the lists of every
    witness, whatever function of the label the seats are: with no premise on the sizes; the seats
    enter in the form seatBy f alone.
  fit_sizesOf, means_sizesOf, means_closed   the two premises of Johnson/Goal/Meaning/HidSeat.lean
    hold there; the sum means_follows (Johnson/Goal/Meaning/HidPlanFit.lean) at the plans' own, OPEN
    records, and at every family of records with the plans' lists and numbers of matrices.

What is not claimed. THE SEAMS ARE STILL MOVED, NOT PAID. sizesOf X k is NOT the signature of a real
sub-proof's typed smallness test: that stands at the closed record (the head of
OnBytes/Tie/Pv/Tail/SizeOf.lean); means_closed is stated for it, and its premise e, that the closed
records have the plans' lists and numbers of matrices, is shown by no theorem here. What else is
owed: that the layout's seats ARE seatBy f for one f (the theorems hold at a constant f too); that
the messages msg are what is committed; the premises G, At and H, met by no theorem here and guarded
in this form by none. The full size alone. The program does not import this file.
-/
import Johnson.Goal.Meaning.HidPlanFit
import Johnson.Road.HeadSeg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open OnBytes OnBytes.Road OnBytes.Road.L5
open OnBytes.Model (TMat HTailF2 Settings)
open OnBytes.Model.Verify (publicOf layerShape SubPlan attentionOwnerPlace attentionOwnerPlaces
  attentionOwners)
open OnBytes.Model.Head (HL Border Owner HPlanH2 planH2)
open Cb.Pv.Tail (Size)

/-! ## An attention sub-proof's plan -/

theorem seamShape_nm {g : Model.Settings} {m : Array TMat} {tau col0F ktO aO : ℕ}
    {s : Attention.Seam} (h : Attention.Seam.shape g m tau col0F ktO aO = Except.ok s) :
    s.tl.NM = s.tl.mats.size := by
  unfold Attention.Seam.shape at h
  obtain ⟨-, h⟩ := jp_ok h
  obtain ⟨-, h⟩ := jp_ok h
  obtain ⟨tl, ht, h⟩ := L5.bind_ok h
  have e := Except.ok.inj h
  subst e
  obtain ⟨a, b⟩ := shape_mats ht
  show tl.NM = tl.mats.size
  rw [b, a]

theorem seamPlan_nm {s s' : Attention.Seam} {nU3 hb hbLine : ℕ}
    (h : s.plan nU3 hb hbLine = Except.ok s') : s'.tl.NM = s.tl.NM := by
  unfold Attention.Seam.plan at h
  obtain ⟨r, hr, h⟩ := L5.bind_ok h
  have k := (addTrees_keeps hr).2
  obtain ⟨tl, Fp, T⟩ := r
  obtain ⟨-, h⟩ := jp_ok h
  obtain ⟨Tp, -, h⟩ := L5.bind_ok h
  have e := Except.ok.inj h
  subst e
  exact k

/-- In the plan that Attention.plan returns the record's NM is the length of its list. -/
theorem plan_nm {settings : Model.Settings} {i : Attention.In} {cf : Attention.Cfg}
    {X : Attention.Plan} (h : Attention.plan settings i cf = Except.ok X) :
    X.seam.tl.NM = X.seam.tl.mats.size := by
  unfold Attention.plan at h
  obtain ⟨-, h⟩ := jp_ok h
  obtain ⟨-, h⟩ := jp_ok h
  obtain ⟨-, h⟩ := jp_ok h
  obtain ⟨r, hr, h⟩ := L5.bind_ok h
  obtain ⟨S, fs⟩ := r
  obtain ⟨-, h⟩ := jp_ok h
  obtain ⟨seam0, h0, h⟩ := L5.bind_ok h
  obtain ⟨-, h⟩ := jp_ok h
  obtain ⟨-, h⟩ := jp_ok h
  obtain ⟨seam, h1, h⟩ := L5.bind_ok h
  have e := Except.ok.inj h
  subst e
  show seam.tl.NM = seam.tl.mats.size
  rw [seamPlan_nm h1, seamPlan_mats h1]
  exact seamShape_nm h0

/-- attentionOwnerPlace keeps NM. -/
theorem place_nm {g : ℕ} {O X X' : SubPlan} (h : attentionOwnerPlace g O X = Except.ok X') :
    X'.tl.NM = X.tl.NM := by
  unfold attentionOwnerPlace at h
  obtain ⟨tl, ht, h⟩ := L5.bind_ok h
  obtain ⟨own, -, h⟩ := L5.bind_ok h
  obtain ⟨-, h⟩ := jp_ok h
  have e := Except.ok.inj h
  subst e
  exact (borderMeans_keeps ht).2

/-- attentionOwners keeps every plan's NM. -/
theorem owners_nm {p4 : Bool} {NGr : ℕ} {G A A' : Array SubPlan}
    (h : attentionOwners p4 NGr G A = Except.ok A') (j : ℕ) :
    (A'[j]?).map (fun X => X.tl.NM) = (A[j]?).map (fun X => X.tl.NM) := by
  unfold attentionOwners at h
  cases p4 with
  | false =>
    have e : A = A' := Except.ok.inj h
    rw [e]
  | true =>
    have h' : (Model.Verify.attentionOwnerShapes NGr G A >>= fun _ =>
        attentionOwnerPlaces NGr G A) = Except.ok A' := h
    obtain ⟨-, -, h2⟩ := L5.bind_ok h'
    unfold attentionOwnerPlaces at h2
    refine foldlM_inv
      (Q := fun out => ∀ j, (out[j]?).map (fun X => X.tl.NM) = (A[j]?).map fun X => X.tl.NM)
      (fun out g out' hq hs => ?_) _ _ _ (fun _ => rfl) h2 j
    cases hG : G[g]? with
    | none =>
      simp only [hG] at hs
      have hs' : (Except.error "internal-a-owner-shape" : Except String (Array SubPlan)) =
          Except.ok out' := hs
      cases hs'
    | some O =>
      cases hO : out[g]? with
      | none =>
        simp only [hG, hO] at hs
        have hs' : (Except.error "internal-a-owner-shape" : Except String (Array SubPlan)) =
            Except.ok out' := hs
        cases hs'
      | some X =>
        simp only [hG, hO] at hs
        obtain ⟨X', hX, hs⟩ := L5.bind_ok hs
        have e : out.setIfInBounds g X' = out' := Except.ok.inj hs
        intro i
        rw [← e, set_keeps (fun X => X.tl.NM) out hO (place_nm hX) i]
        exact hq i

/-! ## The head's plan -/

/-- In the plan that planH2 returns the record's NM is the length of its list. -/
theorem planH2_nm {g : Settings} {h : Model.Head.Shape} {L : HL} {b : Border} {O : Owner}
    {NGr lkW : ℕ} {hp : HPlanH2} (hpl : planH2 g h L b O NGr lkW = .ok hp) :
    hp.tl.NM = hp.tl.mats.size := by
  unfold Model.Head.planH2 at hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨pc, -, hpl⟩ := ok_of_bind hpl
  obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
  cases hs : O.tl.mats[O.iXO]? with
  | none =>
    simp only [hs] at hpl
    have h' : (Except.error "internal-h-owner-TX" : Except String HPlanH2) = .ok hp := hpl
    cases h'
  | some M0 =>
    simp only [hs] at hpl
    obtain ⟨stream, hst, hpl⟩ := ok_of_bind (x := (pure M0 : Except String TMat)) hpl
    obtain ⟨t1, h1, hpl⟩ := ok_of_bind hpl
    obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
    obtain ⟨r, hr, hpl⟩ := ok_of_bind hpl
    obtain ⟨t2, Fp, Tp⟩ := r
    obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
    obtain ⟨Tp2, -, hpl⟩ := ok_of_bind hpl
    obtain ⟨t3, h3, hpl⟩ := ok_of_bind hpl
    obtain ⟨-, -, hpl⟩ := ok_of_bind hpl
    have e := (Except.ok.inj hpl).symm
    subst e
    show t3.NM = t3.mats.size
    rw [(Hd.ownerHeld_keeps h3).2, (Hd.ownerHeld_keeps h3).1, (addTrees_keeps hr).2,
      (addTrees_keeps hr).1, (shape_mats h1).2, (shape_mats h1).1]

/-! ## In scope -/

section Core
variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}

/-- **In scope each of the 25 records' number of matrices is the length of its list.** -/
theorem nm_of_core (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) {k : ℕ} (hk : k < 25) :
    (tlAt X k).NM = (tlAt X k).mats.size := by
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  by_cases h24 : k = 24
  · subst h24
    obtain ⟨H0, hH, e⟩ := (Hd.publicH_of_public h).plan
    have e1 : tlAt X 24 = H0.tl := by
      unfold tlAt
      rw [if_neg (by omega), if_pos rfl, e]
    rw [e1]
    exact planH2_nm hH
  · by_cases hev : k % 2 = 0
    · obtain ⟨sc, rope, wsLay, V, tokv, set, hP, hG⟩ := Hd.public_plans h
      obtain ⟨hsz, -⟩ := Hd.plan_labels hP hG
      have hgs : k / 2 < X.G.size := by
        rw [hsz, B.groups]
        omega
      have e : X.G[k / 2]? = some X.G[k / 2] := Array.getElem?_eq_getElem hgs
      have e1 : tlAt X k = X.G[k / 2].tl := by
        unfold tlAt
        rw [if_neg (by omega), if_neg h24, if_pos hev, e]
        rfl
      rw [e1]
      exact (plan_sizes hP hG e).2
    · obtain ⟨lines, A0, seenG, seenA, hO, H⟩ := Hd.groups_of_public h B.p4
      obtain ⟨Xg, Ag, s, hG, h0, hs, hA, -, -, -, etl, -⟩ :=
        H (k / 2) (by rw [B.groups]; omega)
      obtain ⟨cf, -, hp, -⟩ := group_plan hG
      have e1 : tlAt X k = Ag.seam.tl := by
        unfold tlAt
        rw [if_neg (by omega), if_neg h24, if_neg hev, hA]
        rfl
      have n1 := owners_nm hO (k / 2)
      rw [hs, Array.getElem?_map, h0] at n1
      have n2 : s.tl.NM = Xg.seam.tl.NM := Option.some.inj n1
      rw [e1, etl, n2, owners_plan hO h0 hs]
      exact plan_nm hp

theorem nmFit_of_core (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) :
    nmFit X = true := by
  unfold nmFit
  rw [List.all_eq_true]
  exact fun k hk => decide_eq_true (nm_of_core h C (List.mem_range.1 hk))

/-- **In scope the library's own sizes follow the plans.** -/
theorem follows_of_core (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) :
    Follows X (sizesOf X) := follows_sizesOf (nmFit_of_core h C)

/-- The same at every family of records with the plans' lists and numbers of matrices: the closed
records among them. -/
theorem follows_closed (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P)
    {tl : ℕ → HTailF2}
    (e : ∀ k < 25, (tl k).NM = (tlAt X k).NM ∧ (tl k).mats = (tlAt X k).mats) :
    Follows X fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size :=
  follows_sizeOf e (nmFit_of_core h C)

/-- **In scope, at the library's own sizes, the 24 equations hold at the lists of every witness**,
whatever function of the label the seats are. -/
theorem words_sizesOf (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P)
    (f : ℕ → ℕ → ℕ → ℕ × ℕ × ℕ) (msg : Msgs) :
    OneWord X (ownAt (sizesOf X) (seatBy f X (sizesOf X)) msg) ∧
      HeadWord X (ownAt (sizesOf X) (seatBy f X (sizesOf X)) msg) :=
  words_of_core h C (follows_of_core h C) f msg

/-- The two premises of Johnson/Goal/Meaning/HidSeat.lean hold in scope, at the library's own sizes
and seats that are a function of the label. -/
theorem fit_sizesOf (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P)
    (f : ℕ → ℕ → ℕ → ℕ × ℕ × ℕ) :
    sizesFit X (sizesOf X) = true ∧ SeatsOne X (sizesOf X) (seatBy f X (sizesOf X)) :=
  ⟨sizesFit_of_planFit (follows_of_core h C) (planFit_of_core h C),
    seatsOne_of_planFit f (planFit_of_core h C)⟩

/-- The sum at the plans' own, open records: with no premise on the sizes; the seats enter in the
form seatBy f alone. -/
theorem means_sizesOf (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P)
    (f : ℕ → ℕ → ℕ → ℕ × ℕ × ℕ) {pp : Inst.Model.ScalesAndPolicy} {i : Cm.Idx}
    {x : Inst.Model.Instance Inst.Model.ppref} (tok : Fin Inst.Model.ppref.V) (msg : Msgs)
    (G : ∀ g < 12, LayerOrd (layerShape X.P) X.layers.sc X.y g
      (ownAt (sizesOf X) (seatBy f X (sizesOf X)) msg (2 * g)) i.mat x)
    (At : ∀ g < 12, AttOrd (Hd.shapeA X g)
      (ownAt (sizesOf X) (seatBy f X (sizesOf X)) msg (2 * g + 1)))
    (H : HeadPlain pp i x (headStream X (ownAt (sizesOf X) (seatBy f X (sizesOf X)) msg 24))) :
    Means X pp i x (hidAt X (sizesOf X) (seatBy f X (sizesOf X)) tok msg) :=
  means_follows h C (follows_of_core h C) f tok msg G At H

/-- **The sum at every family of records with the plans' lists and numbers of matrices**: the closed
records, at which the smallness test stands, are meant. -/
theorem means_closed (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) {tl : ℕ → HTailF2}
    (e : ∀ k < 25, (tl k).NM = (tlAt X k).NM ∧ (tl k).mats = (tlAt X k).mats)
    (f : ℕ → ℕ → ℕ → ℕ × ℕ × ℕ) {pp : Inst.Model.ScalesAndPolicy} {i : Cm.Idx}
    {x : Inst.Model.Instance Inst.Model.ppref} (tok : Fin Inst.Model.ppref.V) (msg : Msgs)
    (G : ∀ g < 12, LayerOrd (layerShape X.P) X.layers.sc X.y g
      (ownAt (fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size)
        (seatBy f X fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size) msg (2 * g)) i.mat x)
    (At : ∀ g < 12, AttOrd (Hd.shapeA X g)
      (ownAt (fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size)
        (seatBy f X fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size) msg (2 * g + 1)))
    (H : HeadPlain pp i x (headStream X
      (ownAt (fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size)
        (seatBy f X fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size) msg 24))) :
    Means X pp i x (hidAt X (fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size)
      (seatBy f X fun k => (OnBytes.Tie.Pv.Tail.sizeOf (tl k)).size) tok msg) :=
  means_follows h C (follows_closed h C e) f tok msg G At H

end Core

end Meaning

#print axioms Meaning.seamShape_nm
#print axioms Meaning.seamPlan_nm
#print axioms Meaning.plan_nm
#print axioms Meaning.place_nm
#print axioms Meaning.owners_nm
#print axioms Meaning.planH2_nm
#print axioms Meaning.nm_of_core
#print axioms Meaning.nmFit_of_core
#print axioms Meaning.follows_of_core
#print axioms Meaning.follows_closed
#print axioms Meaning.words_sizesOf
#print axioms Meaning.fit_sizesOf
#print axioms Meaning.means_sizesOf
#print axioms Meaning.means_closed
