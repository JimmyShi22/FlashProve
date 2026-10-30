-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import OnBytes.Model.Fit.FitLinks
/-
Johnson/Loose/H2K12/LinksKeepAtFacts.lean: TWINS OF THIRTEEN LEMMAS UNDER OnBytes/Model/, AT A
PREDICATE IN hX's PLACE.
WHY: the original link_keeps (OnBytes/Model/Fit/FitLinks.lean)
says of what publicOf returns that the sub-proofs' rounds keep every entry small; the proof file's
seated description's public record is publicOfO o's, o the second hash function as a letter:
publicOf's yes is not at hand there. ON THE PLAN ALONE. NO
SOUNDNESS IS CLAIMED. NOTHING ON HIDING. NO NEW MATHEMATICS.
  LinkFacts pol KL X   what link_keeps and its lemmas read of the public record: FIVE READBACKS'
      CONCLUSIONS, AS THEY STAND, none of which names a hash: Fo.Pub.publicOf_cut's first conjunct
      (OnBytes/Tie/Pv/Lookup/Ends/FoPublic.lean) · OnBytes.Model.Fit.public_reads'
      (OnBytes/Model/Fit/LayerCaps.lean) · Fo.Pub.public_G's · public_H's (FoPublic.lean) ·
      public_A's (FoPublicA.lean).
  linkFacts_of_publicOf     paid at publicOf's yes, by these five: so the predicate is not empty
      where publicOf returns.
  THE THIRTEEN, EACH THE ORIGINAL's PROOF TO THE LETTER BUT FOR WHAT STANDS IN hX's PLACE, UNDER THE
      ORIGINAL's NAME WITH A PRIME: OnBytes.Model.Verify.head_walk (Fit/HeadWalk.lean) · head_cap ·
      head_small · head_keeps (Fit/HeadCaps.lean) · OnBytes.Model.Fit.att_nums · att_zero_cap ·
      att_small_cap (Fit/AttCaps.lean) · att_keeps · link_att_keeps (Fit/AttKeeps.lean) · layers_cap
      · layers_keeps (Fit/LayerCaps.lean) · OnBytes.Model.layers_small (Fit/LayerTail.lean) ·
      OnBytes.Model.Verify.link_keeps (Fit/FitLinks.lean).
  link_keeps'          LinkFacts pol KL X → SetCap s → Keeps s Small (linkRounds X link moment).
WHAT IS NOT HERE: LinkFacts AT publicOfO o's RETURN: it stands in H2K12/PlainParts.lean
(linkFacts_of_cut, off the predicate PublicCut, PublicAtCut.lean, and its five readbacks by name).
-/
set_option autoImplicit false
namespace H2K.Made
open OnBytes OnBytes.Model OnBytes.Model.Verify OnBytes.Model.Fit
open OnBytes.Params (Keeps Small SetCap AttentionCap SmallCap)
open Fo.Pub (midQ)

/-- What link_keeps and its lemmas read of the public record: the five readbacks' conclusions. -/
structure LinkFacts (pol KL : ByteArray) (X : Public) : Prop where
  layout : polLayout pol = .ok (X.P, X.layers.y)
  reads : Layer.readsOf X.layers.y = .ok X.layers.rd
  G : ∀ (g : Nat) (hp : Layer.HPlan2), X.G[g]? = some hp →
    Layer.planG X.layers g (if g = 0 then none else X.G[g - 1]?) = .ok hp
  H : ∃ H0, Head.planH2 X.P.settings X.hS X.HLy (borderOf X.layers.y) X.owner
      X.layers.y.NGr X.P.lkW = .ok H0 ∧ X.H = { H0 with Fp := H0.Fp.trimL }
  A : ∀ (g : Nat) (a : Attention.Plan), X.A[g]? = some a →
    ∃ (sc : Layer.Scales) (lines : List Attention.Line) (cf : Attention.Cfg)
      (a0 : Attention.Plan),
      Layer.scalesOf X.layers.y.h (fileWords KL) = .ok sc ∧
      Attention.readLines X.P.polCallsA = .ok lines ∧
      Attention.fill X.P X.layers.y sc lines g = .ok cf ∧
      Attention.plan X.P.settings
        (Attention.inOf X.P.settings X.layers.y (midQ X.layers.y g) g) cf = .ok a0 ∧
      a = { a0 with seam := { a0.seam with tl := a.seam.tl } } ∧
      a.seam.tl.mats = a0.seam.tl.mats ∧ a.seam.tl.tau = a0.seam.tl.tau

/-- Paid by publicOf's yes: the five readback lemmas. -/
theorem linkFacts_of_publicOf {pol KL : ByteArray} {lay : Option ByteArray} {X : Public}
    (h : publicOf pol KL lay = .ok X) : LinkFacts pol KL X :=
  ⟨(Fo.Pub.publicOf_cut pol KL lay X h).1, public_reads h, Fo.Pub.public_G h, Fo.Pub.public_H h,
    Fo.Pub.public_A h⟩

variable {pol KL : ByteArray} {X : Public}

theorem head_walk' (hX : LinkFacts pol KL X) :
    (∃ (m : Array TMat) (f : Array T2Foreign) (tl1 : HTailF2),
      ({ tau := X.P.settings.tau, lidb := X.P.settings.lidb } : HTailF2).shapeF m
        (Array.replicate m.size none) f #[false, false, true, false] X.P.settings.tau = .ok tl1 ∧
      X.H.tl.mats = tl1.mats ∧ X.H.tl.tau = tl1.tau) ∧
      X.hS.lt < 2 ^ 30 := by
  obtain ⟨H0, h1, h2⟩ := hX.H
  obtain ⟨m, f, tl1, hsh, hm, ht, hs⟩ := planH2_walk h1
  have e : X.H.tl = H0.tl := by rw [h2]
  exact ⟨⟨m, f, tl1, hsh, by rw [e]; exact hm, by rw [e]; exact ht⟩,
    Nat.lt_of_le_of_lt (lt_le_slots X.hS X.HLy tl1 X.P.lkW) hs⟩

theorem head_cap' (hX : LinkFacts pol KL X) : Params.HeadCap (X.H.own X.hS) :=
  ⟨Nat.le_of_lt (Nat.lt_of_lt_of_le (head_walk' hX).2
    (Nat.pow_le_pow_right (by decide) (by decide)))⟩

theorem head_small' (hX : LinkFacts pol KL X) : Params.SmallCap (smallSize X.H.tl) := by
  obtain ⟨_, _, tl1, hsh, hm, _⟩ := (head_walk' hX).1
  have e : X.H.tl.foldColumns = tl1.foldColumns := by
    unfold HTailF2.foldColumns
    rw [hm]
  refine ⟨?_⟩
  show X.H.tl.foldColumns * 276 ≤ 2 ^ 45
  rw [e]
  exact small_cap hsh

theorem head_keeps' (hX : LinkFacts pol KL X) {s : Params.Setting} (S : Params.SetCap s)
    (moment : Nat) : Params.Keeps s Params.Small (X.H.rounds X.hS X.HLy moment) :=
  Params.keeps_headRounds (Params.subBase_small S) _ (head_cap' hX) (head_small' hX) moment

theorem att_nums' (hX : LinkFacts pol KL X) {g : Nat} {a : Attention.Plan}
    (hg : X.A[g]? = some a) : a.own.lt ≤ 16 ∧ a.own.lgk ≤ 6 := by
  obtain ⟨sc, lines, cf, a0, _, _, hf, hp, ea, _, _⟩ := hX.A g a hg
  have C := polLayout_caps hX.layout
  obtain ⟨f1, f2⟩ := fill_nums hf
  obtain ⟨p1, p2⟩ := plan_own hp
  have e1 : a.own = a0.own := (congrArg Attention.Plan.own ea).trans rfl
  have hlt : X.P.h.lt ≤ 16 := C.lt
  have hGk : X.P.h.Gk ≤ 2 ^ 6 := by
    have h64 : X.P.h.H + X.P.h.Gk ≤ 64 := C.heads
    omega
  rw [e1, p1, p2, f1, f2]
  exact ⟨hlt, OnBytes.Slice.ceilLog2_le _ 6 hGk⟩

theorem att_zero_cap' (hX : LinkFacts pol KL X) {g : Nat} {a : Attention.Plan}
    (hg : X.A[g]? = some a) : AttentionCap a.own := by
  obtain ⟨h1, h2⟩ := att_nums' hX hg
  exact ⟨by omega⟩

theorem att_small_cap' (hX : LinkFacts pol KL X) {g : Nat} {a : Attention.Plan}
    (hg : X.A[g]? = some a) : SmallCap (smallSize a.seam.tl) := by
  obtain ⟨sc, lines, cf, a0, _, _, _, hp, _, hm, _⟩ := hX.A g a hg
  obtain ⟨seam0, h0, h1, _⟩ := Fo.BatRows.planA_rows0 _ _ _ _ hp
  obtain ⟨k1, _⟩ := Fo.BatRows.seamPlan_keeps _ _ _ _ _ h1
  obtain ⟨f, hF⟩ := seamShape_F h0
  have hc := small_cap hF
  have e : a.seam.tl.foldColumns = seam0.tl.foldColumns := by
    unfold HTailF2.foldColumns
    rw [hm, k1]
  refine ⟨?_⟩
  show a.seam.tl.foldColumns * 276 ≤ 2 ^ 45
  rw [e]
  exact hc

theorem att_keeps' {s : Params.Setting} (hX : LinkFacts pol KL X) (S : SetCap s)
    (g : Nat) (a : Attention.Plan) (hg : X.A[g]? = some a) (moment : Nat) :
    Keeps s Small (Attention.rounds a moment) := by
  unfold Attention.rounds
  exact Params.keeps_attentionRounds (Params.subBase_small S) _ (att_zero_cap' hX hg)
    (att_small_cap' hX hg) moment

theorem link_att_keeps' {s : Params.Setting} (hX : LinkFacts pol KL X)
    (S : SetCap s) (g moment : Nat) :
    Keeps s Small (match X.A[g]? with
      | some a => Attention.rounds a moment
      | none => Params.needs false) := by
  cases hg : X.A[g]? with
  | none => exact (Params.keeps_needs _ _).any
  | some a => exact att_keeps' hX S g a hg moment

theorem layers_cap' (hX : LinkFacts pol KL X) (hp : Layer.HPlan2) (g : Nat) :
    Params.LayerCap (Verify.layerNumbers X.layers hp g) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := layer_nums (polLayout_caps hX.layout) hX.reads
  have big : (20 : Nat) ≤ 2 ^ 40 := by decide
  exact ⟨Nat.le_trans h1 (by omega), Nat.le_trans h2 (by omega), Nat.le_trans h3 big,
    Nat.le_trans h4 (by omega), Nat.le_trans h5 (by omega)⟩

theorem layers_small' (h : LinkFacts pol KL X) (g : Nat) (hp : Layer.HPlan2)
    (hg : X.G[g]? = some hp) : (smallSize hp.tl).columns * 276 ≤ 2 ^ 45 :=
  planG_cap (h.G g hp hg)

theorem layers_keeps' {s : Params.Setting} {Q : Fmt.Entry → Prop} (B : Params.SubBase s Q)
    (hX : LinkFacts pol KL X) (g : Nat) (hp : Layer.HPlan2)
    (hg : X.G[g]? = some hp) (moment : Nat) :
    Params.Keeps s Q (Params.layerRounds (forestSize X.y.fo) (Verify.layerNumbers X.layers hp g)
      (smallSize hp.tl) hp.nBatched moment) :=
  Params.keeps_layerRounds B _ (layers_cap' hX hp g) ⟨layers_small' hX g hp hg⟩ _ _

/-- link_keeps at the five facts. -/
theorem link_keeps' {s : Params.Setting} (hX : LinkFacts pol KL X) (S : SetCap s)
    (link moment : Nat) : Keeps s Small (linkRounds X link moment) := by
  unfold linkRounds
  dsimp only
  refine Params.keeps_ite (fun _ => head_keeps' hX S moment) fun _ => ?_
  refine Params.keeps_ite (fun _ => ?_) fun _ => link_att_keeps' hX S _ moment
  split
  · rename_i hp hg
    exact layers_keeps' (Params.subBase_small S) hX _ hp hg moment
  · exact (Params.keeps_needs _ _).any

end H2K.Made

#print axioms H2K.Made.linkFacts_of_publicOf
#print axioms H2K.Made.link_keeps'
