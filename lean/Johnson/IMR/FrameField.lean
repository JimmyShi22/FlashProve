-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/FrameField.lean: THE FIELD "frameIs" OF THE LIST OF FACTS ALONG THE FOLD
(Johnson/Desc/First/FoldFacts.lean), at every border that it
asks, UNDER FOUR NAMED PREMISES. ITS END IS THE FIELD's TYPE ONCE momentW AND shiftW ARE UNFOLDED:
this file does not import FoldFacts.lean, so Lean has not checked the fit; a program has held the
two texts against each other. "The state", "the cut k": as in Johnson/IMR/FrameAll.lean.
WHAT THE FIELD ASKS: at a reached border k whose entry's place p bears a link m, of every L with
s.link? = some L: the frame's moment is momentAt of p.piece; its list own is ownAt m of that moment;
its list keptBefore is keptAt m; and, up to in front of the closing, its link is m and its next is
"later or close".
  shiftOf l: 1 at the head's link, else 0. entryCut l: the cut behind the sub-protocol that opens
    link l: 14 l + 3 + shiftOf l.
  nosAt, keptSize, keptN, ownFirst, ownN: THE TWO LISTS AS TERMS WITH CODE of two letters: cnt (the
    number of messages at a cut) and sh (the request's shape).
  EntryIs cnt sh m f: the frame behind the sub-protocol that opens link m, in these terms.
    EntryIs.seq: so at every later cut.
  CountsBy c Z cnt, ShapeBy c Z sh: THE TWO PREMISES ON THE FOLD's STATES. laid_clean, h1_clean: the
    cuts at which ShapeBy is spent (14 l + 2 at l < 24; 339) bear no mark.
  shape_paid: ShapeBy c Z Z.first.shape: PROVED, from the fold's return alone.
  entry_is_zero, entry_is_link, entry_is_head: EntryIs at all 25 links.
  frame_is_at: what the field reads, at the cut entryCut l + i, i ≤ 11 + shiftOf l: moment, own and
    keptBefore at all of these; link and next at i ≤ 9 + shiftOf l.
  pieceFit, piece_numbers, piece_number_at: a closed test on the written list of places: an entry
    number k that bears the link m has the piece k - (14 m + 1). piece_bent_fails: four negative
    tests; piece_bent_control.
  momentW, shiftW: that file's momentAt, and its shiftAt at links := IM.linksW, said again (this
    file does not import it). shiftW_is: shiftW m = shiftOf m at m < 25, by the kernel.
  frameIs_field: THE TOP.
THE FOUR PREMISES: hN : CountsBy c Z cnt. hSh : ShapeBy c Z sh. hKept : keptAt m = keptN cnt sh m
and hOwn : ownAt m j = ownN cnt sh m j (m < 25, 1 ≤ j ≤ 3): two equations with no state in them.
NOT HERE: hN; hKept and hOwn (Johnson/IMR/FrameClosed.lean proves these two). That the flat list's
places are
placesW. It says nothing on the group's members.
OBJECT: ProofFile.onlineDescription's value at OnBytes.secondHashFunction, in scope. USERS: whoever makes a value of the list
of facts along the fold.
Every theorem on states starts from the premise that a fold returns; no proof file is exhibited for
which one does. No soundness.
-/
import Johnson.IMR.FrameAll
import Johnson.IMR.GroupField

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open ProofFile (Cl)

/-- 1 at the head's link, else 0. -/
def shiftOf (l : Nat) : Nat := if l = 24 then 1 else 0

/-- The cut behind the sub-protocol that opens link l. -/
def entryCut (l : Nat) : Nat := 14 * l + 3 + shiftOf l

/-- The numbers base, base + 1, …: as many as link m has messages of moment j in the shape sh. -/
def nosAt (sh : Params.ReqShape) (m j base : Nat) : Array Nat :=
  (Array.range (((sh.link[m]?.map (·.messages)).getD []).filter fun x =>
    x.moment == j).length).map (· + base)

/-- How many old messages the code switching into group m keeps. -/
def keptSize (sh : Params.ReqShape) (m : Nat) : Nat :=
  (((reqGroups sh)[m]?).map (·.target.kept.size)).getD 0

/-- The frame's list keptBefore at link m; cnt k: the number of oracle messages at the cut k. -/
def keptN (cnt : Nat → Nat) (sh : Params.ReqShape) (m : Nat) : Array Nat :=
  if m = 0 then #[] else (Array.range (keptSize sh m)).map (· + (cnt (entryCut m - 1) + 1))

/-- The frame's list own at link m behind the first sending. -/
def ownFirst (cnt : Nat → Nat) (sh : Params.ReqShape) (m : Nat) : Array Nat :=
  nosAt sh m 0 (cnt (entryCut m - 1) + (if m = 0 then 0 else 1 + keptSize sh m))

/-- The frame's list own at link m, where the frame's field moment is j. -/
def ownN (cnt : Nat → Nat) (sh : Params.ReqShape) (m j : Nat) : Array Nat :=
  if j ≤ 1 then ownFirst cnt sh m
  else if j = 2 then ownFirst cnt sh m ++ nosAt sh m 1 (cnt (entryCut m + 2))
  else ownFirst cnt sh m ++ nosAt sh m 1 (cnt (entryCut m + 2)) ++
    nosAt sh m 2 (cnt (entryCut m + 4))

theorem nosAt_frame {f : ReqFrame} {sh : Params.ReqShape} {m : Nat} (hs : f.shape = sh)
    (hl : f.link = m) (j base : Nat) :
    (Array.range (f.atMoment j).length).map (· + base) = nosAt sh m j base := by
  unfold ReqFrame.atMoment nosAt
  rw [hs, hl]

/-- Six fields of the frame behind the sub-protocol that opens link m, in the closed terms. -/
structure EntryIs (cnt : Nat → Nat) (sh : Params.ReqShape) (m : Nat) (f : ReqFrame) : Prop where
  moment : f.moment = 1
  link : f.link = m
  next : f.next = .laterOrClose
  shape : f.shape = sh
  kept : f.keptBefore = keptN cnt sh m
  own : f.own = ownFirst cnt sh m

/-- The five that the field reads, of the walk's i-th frame seqF f … i, at every i. -/
theorem EntryIs.seq {cnt : Nat → Nat} {sh : Params.ReqShape} {m : Nat} {f : ReqFrame}
    (E : EntryIs cnt sh m f) (i : Nat) :
    (seqF f (cnt (entryCut m + 2)) (cnt (entryCut m + 4)) i).moment =
        (if i ≤ 2 then 1 else if i ≤ 4 then 2 else 3) ∧
      (seqF f (cnt (entryCut m + 2)) (cnt (entryCut m + 4)) i).own =
        ownN cnt sh m (if i ≤ 2 then 1 else if i ≤ 4 then 2 else 3) ∧
      (seqF f (cnt (entryCut m + 2)) (cnt (entryCut m + 4)) i).keptBefore = keptN cnt sh m ∧
      (seqF f (cnt (entryCut m + 2)) (cnt (entryCut m + 4)) i).link = m ∧
      (seqF f (cnt (entryCut m + 2)) (cnt (entryCut m + 4)) i).next = .laterOrClose := by
  have o2 : (laterF f (cnt (entryCut m + 2))).own =
      ownFirst cnt sh m ++ nosAt sh m 1 (cnt (entryCut m + 2)) := by
    show f.own ++ _ = _
    rw [E.own, E.moment, nosAt_frame E.shape E.link]
  have o3 : (laterF (laterF f (cnt (entryCut m + 2))) (cnt (entryCut m + 4))).own =
      ownFirst cnt sh m ++ nosAt sh m 1 (cnt (entryCut m + 2)) ++
        nosAt sh m 2 (cnt (entryCut m + 4)) := by
    show (laterF f (cnt (entryCut m + 2))).own ++
      (Array.range ((laterF f (cnt (entryCut m + 2))).atMoment (f.moment + 1)).length).map _ = _
    rw [o2, E.moment, nosAt_frame (f := laterF f (cnt (entryCut m + 2))) E.shape E.link]
  unfold seqF
  by_cases h2 : i ≤ 2
  · simp only [if_pos h2]
    exact ⟨E.moment, by rw [E.own]; rfl, E.kept, E.link, E.next⟩
  · by_cases h4 : i ≤ 4
    · simp only [if_neg h2, if_pos h4]
      exact ⟨by show f.moment + 1 = 2; rw [E.moment], by rw [o2]; rfl, E.kept, E.link, E.next⟩
    · simp only [if_neg h2, if_neg h4]
      exact ⟨by show f.moment + 1 + 1 = 3; rw [E.moment], by rw [o3]; rfl, E.kept, E.link, E.next⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- THE FIRST NAMED PREMISE: cnt k is the number of oracle messages at the cut k, k ≤ 358. -/
def CountsBy (c : Chain S Cl) (Z : ProofFile.Pub) (cnt : Nat → Nat) : Prop :=
  ∀ (p : ProofFile.InstPub) (R : List Fmt.RoundView) (C : List VerifiableInference.Desc.OpenedColumn) (k : Nat)
    (r : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn), k ≤ 358 →
    foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) R C = .ok r → r.1.st.oracles.size = cnt k

/-- THE SECOND NAMED PREMISE: at a cut k from 2 to 339, at a state without a mark: the walk's frame
has the shape sh, and its groups are reqGroups sh. (At sh := Z.first.shape: shape_paid.) -/
def ShapeBy (c : Chain S Cl) (Z : ProofFile.Pub) (sh : Params.ReqShape) : Prop :=
  ∀ (p : ProofFile.InstPub) (R : List Fmt.RoundView) (C : List VerifiableInference.Desc.OpenedColumn) (k : Nat)
    (r : S × List Fmt.RoundView × List VerifiableInference.Desc.OpenedColumn), 2 ≤ k → k ≤ 339 →
    foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z p) R C = .ok r → r.1.failed = none →
    r.1.check.frame.shape = sh ∧ r.1.check.frame.groups = reqGroups sh

/-- Behind "laid" the state bears no mark. -/
theorem laid_clean (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (hl : l < 25)
    {p : ProofFile.InstPub} {R R₀ : List Fmt.RoundView} {C C₀ : List VerifiableInference.Desc.OpenedColumn} {t₀ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 2)) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀)) :
    t₀.failed = none := by
  obtain ⟨-, fs, -, hfr⟩ := IM.frame_of hS hR O
  obtain ⟨LkF, f, bL, bB, bC, -, -, -, -, efl, hlay, -, iL, -, dL, -⟩ := hfr l hl
  obtain ⟨tm, Rm, Cm, fm⟩ := fold_back (k := 14 * l + 1) f₀
  obtain ⟨rs, gs, d⟩ := fold_next iL fm f₀
  rw [dL] at d
  exact ((hlay tm t₀).1 d).2.1

/-- Behind the place "H:1" the state bears no mark. -/
theorem h1_clean (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {p : ProofFile.InstPub} {R R₁ : List Fmt.RoundView} {C C₁ : List VerifiableInference.Desc.OpenedColumn} {t₁ : S}
    (f₁ : foldBlocks 0 (c.blocksInOrder.take 339) (ProofFile.startS Z p) R C = .ok (t₁, R₁, C₁)) :
    t₁.failed = none := by
  obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_back (k := 338) f₁
  obtain ⟨Lk, b0, eL, e0, J, -⟩ := IM.k7_sits hS hR O
  have i0 : c.blocksInOrder[338]? = some b0 := by
    have q := IM.hear_at_flat eL e0
    rwa [IM.flatIx_scope hS hR O (by omega : 24 ≤ 24) 0] at q
  obtain ⟨rs0, gs0, d0⟩ := fold_next i0 f₀ f₁
  exact (IM.k7_sits_yes hS hR O J d0).2

/-- **THE SECOND NAMED PREMISE, PROVED at the public shape**: by Johnson/IMR/ListsEnds.lean's
open_recAll, from the fold's return alone. (The fence "no mark" is not spent.) -/
theorem shape_paid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) : ShapeBy c Z Z.first.shape := by
  intro p R C k r h2 hk f _
  have hf : 339 ≤ (frontOf c).length := by
    obtain ⟨Lk, b1, x, eL, e1, -⟩ := IM.k2_head_of hS hR O
    have q := flatIx_le (chainBy_noFront O.chain) eL e1
    rwa [IM.flatIx_scope hS hR O (by omega : 24 ≤ 24) 1] at q
  have Rr := open_recAll hS hR O h2 (by omega) f
  exact ⟨Rr.walk.shape, Rr.walk.groups⟩

variable {cnt : Nat → Nat} {sh : Params.ReqShape}

theorem entry_is_zero (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hN : CountsBy c Z cnt)
    (hSh : ShapeBy c Z sh) {p : ProofFile.InstPub} {R R₁ : List Fmt.RoundView}
    {C C₁ : List VerifiableInference.Desc.OpenedColumn} {t₁ : S}
    (f₁ : foldBlocks 0 (c.blocksInOrder.take (14 * 0 + 3)) (ProofFile.startS Z p) R C = .ok (t₁, R₁, C₁)) :
    ∃ f, Opn 0 f t₁ ∧ EntryIs cnt sh 0 f := by
  obtain ⟨f, HA, -, m1, m2, -, m4, m5, m6, m7⟩ := entry_at_zero hS hR O f₁
  obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_back (k := 14 * 0 + 2) f₁
  have hc := laid_clean hS hR O (l := 0) (by omega) f₀
  obtain ⟨s1, -⟩ := hSh p R C _ _ (by omega) (by omega) f₀ hc
  have n0 := hN p R C _ _ (by omega) f₀
  obtain ⟨-, hk0⟩ := laid_at hS hR O (l := 0) (by omega) f₀
  obtain rfl := laid_is_start hS hR O f₀
  refine ⟨f, HA.opn, m1, m2, m4, m5.trans s1, ?_, ?_⟩
  · rw [m6]
    rfl
  · rw [m7, nosAt_frame s1 hk0]
    show nosAt sh 0 0 (ProofFile.startS Z p).st.oracles.size = _
    rw [show (ProofFile.startS Z p).st.oracles.size = cnt (14 * 0 + 2) from n0]
    rfl

theorem entry_is_link (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hN : CountsBy c Z cnt)
    (hSh : ShapeBy c Z sh) {l : Nat} (h1 : 1 ≤ l) (h24 : l < 24) {p : ProofFile.InstPub}
    {R R₁ : List Fmt.RoundView} {C C₁ : List VerifiableInference.Desc.OpenedColumn} {t₁ : S}
    (f₁ : foldBlocks 0 (c.blocksInOrder.take (14 * l + 3)) (ProofFile.startS Z p) R C = .ok (t₁, R₁, C₁)) :
    ∃ f, Opn l f t₁ ∧ EntryIs cnt sh l f := by
  obtain ⟨t₀, R₀, C₀, f₀⟩ := fold_back (k := 14 * l + 2) f₁
  obtain ⟨x, f, hx, HA, -, m1, m2, -, m4, m5, m6, m7⟩ := entry_at hS hR O h1 h24 f₀ f₁
  obtain ⟨L0, G0, S0, g, a⟩ := (_root_.Tw.K2.firstFront_iff _ _ _).1 hx
  have hc := laid_clean hS hR O (by omega : l < 25) f₀
  obtain ⟨s1, s2⟩ := hSh p R C _ _ (by omega) (by omega) f₀ hc
  have n0 : t₀.st.oracles.size = cnt (14 * l + 2) := hN p R C _ _ (by omega) f₀
  obtain ⟨-, hk0⟩ := laid_at hS hR O (by omega : l < 25) f₀
  have s1' : t₀.check.frame.shape = sh := s1
  have s2' : t₀.check.frame.groups = reqGroups sh := s2
  have xT : x.T = G0.target := by rw [a.out]
  have xO : x.own = t₀.check.frame.atMoment 0 := by rw [a.out]
  have eT : x.T.kept.size = keptSize sh l := by
    have g' := a.group
    rw [hk0, s2'] at g'
    unfold keptSize
    rw [g', xT]
    rfl
  have ec : entryCut l - 1 = 14 * l + 2 := by
    unfold entryCut shiftOf
    rw [if_neg (by omega : ¬ l = 24)]
    omega
  refine ⟨f, HA.opn, m1, m2, m4, m5.trans s1', ?_, ?_⟩
  · rw [m6, eT, n0]
    unfold keptN
    rw [if_neg (by omega : ¬ l = 0), ec]
  · rw [m7, xO, nosAt_frame s1' hk0, eT, n0]
    unfold ownFirst
    rw [if_neg (by omega : ¬ l = 0), ec]

theorem entry_is_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hN : CountsBy c Z cnt)
    (hSh : ShapeBy c Z sh) {p : ProofFile.InstPub} {R R₂ : List Fmt.RoundView}
    {C C₂ : List VerifiableInference.Desc.OpenedColumn} {t₂ : S}
    (f₂ : foldBlocks 0 (c.blocksInOrder.take 340) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂)) :
    ∃ f, Opn 24 f t₂ ∧ EntryIs cnt sh 24 f := by
  obtain ⟨t₁, R₁, C₁, f₁⟩ := fold_back (k := 339) f₂
  obtain ⟨G, f, g1, hk1, HO, m1, m2, -, m4, m5, m6, m7⟩ := entry_head_frame hS hR O f₁ f₂
  have hc := h1_clean hS hR O f₁
  obtain ⟨s1, s2⟩ := hSh p R C _ _ (by omega) (by omega) f₁ hc
  have n0 : t₁.st.oracles.size = cnt 339 := hN p R C _ _ (by omega) f₁
  have s1' : t₁.check.frame.shape = sh := s1
  have s2' : t₁.check.frame.groups = reqGroups sh := s2
  have eT : G.target.kept.size = keptSize sh 24 := by
    rw [s2'] at g1
    unfold keptSize
    rw [g1]
    rfl
  refine ⟨f, HO, m1, m2, m4, m5.trans s1', ?_, ?_⟩
  · rw [m6, eT, n0]
    rfl
  · rw [m7, nosAt_frame s1' hk1, eT, n0]
    rfl

/-- The five that the field reads, off an open link with the frame of the walk's i-th cut. -/
theorem fields_of_opn {m : Nat} {f : ReqFrame} (E : EntryIs cnt sh m f) {i : Nat} {t : S}
    (H : Opn m (seqF f (cnt (entryCut m + 2)) (cnt (entryCut m + 4)) i) t) :
    ∀ L, t.link? = some L →
      L.check.frame.moment = (if i ≤ 2 then 1 else if i ≤ 4 then 2 else 3) ∧
      L.check.frame.own = ownN cnt sh m (if i ≤ 2 then 1 else if i ≤ 4 then 2 else 3) ∧
      L.check.frame.keptBefore = keptN cnt sh m ∧
      L.check.frame.link = m ∧ L.check.frame.next = .laterOrClose := by
  intro L hL
  obtain ⟨L', hL', e, -⟩ := H
  obtain rfl : L = L' := Option.some.inj (hL.symm.trans hL')
  rw [e]
  exact E.seq i

/-- Behind the closing: the first three. -/
theorem fields_of_closed {m : Nat} {f : ReqFrame} (E : EntryIs cnt sh m f) {i : Nat} (h5 : 5 ≤ i)
    {t : S} {rows : SingleRows}
    (H : Opn m (closedF (laterF (laterF f (cnt (entryCut m + 2))) (cnt (entryCut m + 4))) rows) t) :
    ∀ L, t.link? = some L →
      L.check.frame.moment = (if i ≤ 2 then 1 else if i ≤ 4 then 2 else 3) ∧
      L.check.frame.own = ownN cnt sh m (if i ≤ 2 then 1 else if i ≤ 4 then 2 else 3) ∧
      L.check.frame.keptBefore = keptN cnt sh m := by
  intro L hL
  obtain ⟨L', hL', e, -⟩ := H
  obtain rfl : L = L' := Option.some.inj (hL.symm.trans hL')
  have k := E.seq i
  have es : seqF f (cnt (entryCut m + 2)) (cnt (entryCut m + 4)) i =
      laterF (laterF f (cnt (entryCut m + 2))) (cnt (entryCut m + 4)) := by
    unfold seqF
    rw [if_neg (by omega : ¬ i ≤ 2), if_neg (by omega : ¬ i ≤ 4)]
  rw [es] at k
  rw [e]
  exact ⟨k.1, k.2.1, k.2.2.1⟩

/-- **THE FIVE THAT THE FIELD READS, AT EVERY CUT OF EVERY LINK AT WHICH A LINK IS OPEN**: the cut
entryCut l + i, i ≤ 11 + shiftOf l; link and next up to in front of the closing. -/
theorem frame_is_at (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hN : CountsBy c Z cnt)
    (hSh : ShapeBy c Z sh) {l : Nat} (hl : l < 25) {p : ProofFile.InstPub} {R r : List Fmt.RoundView}
    {C q : List VerifiableInference.Desc.OpenedColumn} {t : S} {i : Nat} (hi : i ≤ 11 + shiftOf l)
    (g : foldBlocks 0 (c.blocksInOrder.take (entryCut l + i)) (ProofFile.startS Z p) R C = .ok (t, r, q)) :
    ∀ L, t.link? = some L →
      L.check.frame.moment = (if i ≤ 2 then 1 else if i ≤ 4 then 2 else 3) ∧
      L.check.frame.own = ownN cnt sh l (if i ≤ 2 then 1 else if i ≤ 4 then 2 else 3) ∧
      L.check.frame.keptBefore = keptN cnt sh l ∧
      (i ≤ 9 + shiftOf l → L.check.frame.link = l ∧ L.check.frame.next = .laterOrClose) := by
  intro L hL
  obtain ⟨te, Re, Ce, fe⟩ := fold_cut (k := entryCut l) i g
  have fin : ∀ f, EntryIs cnt sh l f →
      ((∀ k ≤ 9 + shiftOf l, ∀ t r q,
        foldBlocks 0 (c.blocksInOrder.take (entryCut l + k)) (ProofFile.startS Z p) R C = .ok (t, r, q) →
        Opn l (seqF f (cnt (entryCut l + 2)) (cnt (entryCut l + 4)) k) t) ∧
      ∀ n ≤ 1, ∀ t r q,
        foldBlocks 0 (c.blocksInOrder.take (entryCut l + (10 + shiftOf l) + n)) (ProofFile.startS Z p) R C =
          .ok (t, r, q) →
        ∃ rows, Opn l
          (closedF (laterF (laterF f (cnt (entryCut l + 2))) (cnt (entryCut l + 4))) rows) t) →
      L.check.frame.moment = (if i ≤ 2 then 1 else if i ≤ 4 then 2 else 3) ∧
      L.check.frame.own = ownN cnt sh l (if i ≤ 2 then 1 else if i ≤ 4 then 2 else 3) ∧
      L.check.frame.keptBefore = keptN cnt sh l ∧
      (i ≤ 9 + shiftOf l → L.check.frame.link = l ∧ L.check.frame.next = .laterOrClose) := by
    intro f E W
    by_cases hK : i ≤ 9 + shiftOf l
    · obtain ⟨a1, a2, a3, a4, a5⟩ := fields_of_opn E (W.1 i hK t r q g) L hL
      exact ⟨a1, a2, a3, fun _ => ⟨a4, a5⟩⟩
    · obtain ⟨rows, Hc⟩ := W.2 (i - (10 + shiftOf l)) (by omega) t r q
        (by rw [show entryCut l + (10 + shiftOf l) + (i - (10 + shiftOf l)) = entryCut l + i by
          omega]; exact g)
      obtain ⟨a1, a2, a3⟩ := fields_of_closed E (i := i) (by omega) Hc L hL
      exact ⟨a1, a2, a3, fun h => absurd h hK⟩
  have hle : entryCut l + 4 ≤ 358 := by
    unfold entryCut shiftOf
    split <;> omega
  have h₃ : ∀ t r q, foldBlocks 0 (c.blocksInOrder.take (entryCut l + 2)) (ProofFile.startS Z p) R C =
      .ok (t, r, q) → t.st.oracles.size = cnt (entryCut l + 2) :=
    fun _ _ _ h => hN p R C _ _ (by omega) h
  have h₅ : ∀ t r q, foldBlocks 0 (c.blocksInOrder.take (entryCut l + 4)) (ProofFile.startS Z p) R C =
      .ok (t, r, q) → t.st.oracles.size = cnt (entryCut l + 4) :=
    fun _ _ _ h => hN p R C _ _ (by omega) h
  by_cases h24 : l = 24
  · subst h24
    obtain ⟨f, HO, E⟩ := entry_is_head hS hR O hN hSh (p := p) (R := R) (C := C) fe
    exact fin f E (frame_walk_head hS hR O h₃ h₅ fe HO)
  · have es : shiftOf l = 0 := if_neg h24
    have ee : entryCut l = 14 * l + 3 := by
      unfold entryCut
      rw [es]
    obtain ⟨f, HO, E⟩ : ∃ f, Opn l f te ∧ EntryIs cnt sh l f := by
      rw [ee] at fe
      by_cases h0 : l = 0
      · subst h0
        exact entry_is_zero hS hR O hN hSh fe
      · exact entry_is_link hS hR O hN hSh (by omega) (by omega) fe
    refine fin f E ?_
    rw [es, ee]
    rw [ee] at h₃ h₅ fe
    exact frame_walk_link hS hR O (by omega) h₃ h₅ fe HO

end

/-- On a list of places: an entry number k that bears the link m has the piece k - (14 m + 1). A
Boolean check, run by the kernel in piece_numbers. -/
def pieceFit (ps : List Place) : Bool :=
  (List.range ps.length).all fun k =>
    match ps[k]? with
    | some p =>
      (match p.link with
       | some m => p.piece + (14 * m + 1) == k
       | none => true)
    | none => true

set_option maxRecDepth 1000000 in
theorem piece_numbers : pieceFit IM.placesW = true := by decide +kernel

/-- The written list with a place of link m and piece j at number k. -/
def pieceBentAt (k m j : Nat) : List Place :=
  IM.placesW.take k ++ { chain := 1, link := some m, piece := j, kind := .frame } ::
    IM.placesW.drop (k + 1)

set_option maxRecDepth 1000000 in
/-- Four negative tests: a piece one too high and one too low, at a link in front of the head's and
at the head's. -/
theorem piece_bent_fails : pieceFit (pieceBentAt 20 1 6) = false ∧
    pieceFit (pieceBentAt 20 1 4) = false ∧ pieceFit (pieceBentAt 340 24 4) = false ∧
    pieceFit (pieceBentAt 340 24 2) = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with the entry's own piece the same form passes. -/
theorem piece_bent_control : pieceFit (pieceBentAt 20 1 5) = true ∧
    pieceFit (pieceBentAt 340 24 3) = true := by decide +kernel

theorem piece_number_at {k m : Nat} {p : Place} (hp : IM.placesW[k]? = some p)
    (hl : p.link = some m) : p.piece + (14 * m + 1) = k := by
  have q := piece_numbers
  unfold pieceFit at q
  rw [List.all_eq_true] at q
  have q' := q k (List.mem_range.2 (List.getElem?_eq_some_iff.1 hp).1)
  simp only [hp, hl, beq_iff_eq] at q'
  exact q'

/-- The list of facts along the fold's momentAt, letter for letter. -/
def momentW (o j : Nat) : Nat := if j ≤ 4 + o then 1 else if j ≤ 6 + o then 2 else 3

/-- The list of facts along the fold's shiftAt at links := IM.linksW. -/
def shiftW (m : Nat) : Nat := if IM.linksW[m]? == some ModelPart.head then 1 else 0

theorem shiftW_is : ∀ m < 25, shiftW m = shiftOf m := by decide +kernel

/-- **THE FIELD "frameIs", WHOLE**, at ps := IM.placesW and links := IM.linksW: its end is the
field's type once momentW and shiftW are unfolded (they are that file's momentAt and shiftAt, said
again: this file does not import it, so Lean has not checked the fit), UNDER FOUR NAMED PREMISES:
hN, hSh: on the fold's states; hKept, hOwn: two closed equations on the letters keptAt and ownAt.
General in Rch and at_, with one premise on Rch: what is reached is the return of a fold over the
flat list's first k entries from ProofFile.startS Z. The fence "no mark" is not spent. -/
theorem frameIs_field {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {cnt : Nat → Nat} {sh : Params.ReqShape} (hN : CountsBy c Z cnt) (hSh : ShapeBy c Z sh)
    (ownAt : Nat → Nat → Array Nat) (keptAt : Nat → Array Nat)
    (hKept : ∀ m < 25, keptAt m = keptN cnt sh m)
    (hOwn : ∀ m < 25, ∀ j, 1 ≤ j → j ≤ 3 → ownAt m j = ownN cnt sh m j) {X : Type}
    (Rch : Nat → X → Prop) (at_ : X → ProofFile.InstPub × S)
    (hRch : ∀ k a, Rch k a → ∃ rs cols r q,
      foldBlocks 0 (c.blocksInOrder.take k) (ProofFile.startS Z (at_ a).1) rs cols = .ok ((at_ a).2, r, q)) :
    ∀ k a p m L, Rch k a → (at_ a).2.failed = none → IM.placesW[k]? = some p → p.link = some m →
      (at_ a).2.link? = some L →
      L.check.frame.moment = momentW (shiftW m) p.piece ∧
        L.check.frame.own = ownAt m (momentW (shiftW m) p.piece) ∧
        L.check.frame.keptBefore = keptAt m ∧
        (p.piece ≤ 11 + 2 * shiftW m →
          L.check.frame.link = m ∧ L.check.frame.next = .laterOrClose) := by
  intro k a p m L hr _ hp hl hL
  obtain ⟨rs, cols, r, q, f⟩ := hRch k a hr
  obtain ⟨h25, h1, h2⟩ := link_number_at hp hl
  have hpc := piece_number_at hp hl
  have hs := shiftW_is m h25
  have h2' : k ≤ 14 * m + 14 + 2 * shiftOf m := by
    unfold shiftOf
    by_cases e : m = 24
    · rw [if_pos e] at h2 ⊢
      omega
    · rw [if_neg e] at h2 ⊢
      omega
  have hk : entryCut m ≤ k := by
    by_contra hlt
    have hc : k = 14 * m + 1 ∨ k = 14 * m + 2 ∨ k = 339 := by
      unfold entryCut shiftOf at hlt
      split at hlt <;> omega
    have hn : (at_ a).2.link? = none := by
      rcases hc with e | e | e
      · exact shut_between hS hR O (Or.inr (Or.inl ⟨m, h25, Or.inl e⟩)) f
      · exact shut_between hS hR O (Or.inr (Or.inl ⟨m, h25, Or.inr e⟩)) f
      · exact shut_between hS hR O (Or.inr (Or.inr (Or.inl e))) f
    rw [hn] at hL
    cases hL
  obtain ⟨i, rfl⟩ : ∃ i, k = entryCut m + i := ⟨k - entryCut m, by omega⟩
  have hi : i ≤ 11 + shiftOf m := by
    unfold entryCut at h2'
    omega
  have hpi : p.piece = i + 2 + shiftOf m := by
    unfold entryCut at hpc
    omega
  obtain ⟨a1, a2, a3, a4⟩ := frame_is_at hS hR O hN hSh h25 hi f L hL
  have hm : momentW (shiftW m) p.piece = (if i ≤ 2 then 1 else if i ≤ 4 then 2 else 3) := by
    rw [hs, hpi]
    unfold momentW
    by_cases c2 : i ≤ 2
    · rw [if_pos c2, if_pos (by omega : i + 2 + shiftOf m ≤ 4 + shiftOf m)]
    · by_cases c4 : i ≤ 4
      · rw [if_neg c2, if_pos c4, if_neg (by omega : ¬ i + 2 + shiftOf m ≤ 4 + shiftOf m),
          if_pos (by omega : i + 2 + shiftOf m ≤ 6 + shiftOf m)]
      · rw [if_neg c2, if_neg c4, if_neg (by omega : ¬ i + 2 + shiftOf m ≤ 4 + shiftOf m),
          if_neg (by omega : ¬ i + 2 + shiftOf m ≤ 6 + shiftOf m)]
  have hM : 1 ≤ (if i ≤ 2 then 1 else if i ≤ 4 then 2 else 3) ∧
      (if i ≤ 2 then 1 else if i ≤ 4 then 2 else 3) ≤ 3 := by
    by_cases c2 : i ≤ 2
    · rw [if_pos c2]
      omega
    · by_cases c4 : i ≤ 4
      · rw [if_neg c2, if_pos c4]
        omega
      · rw [if_neg c2, if_neg c4]
        omega
  rw [hm]
  refine ⟨a1, ?_, a3.trans (hKept m h25).symm, fun hp' => a4 ?_⟩
  · rw [a2, hOwn m h25 _ hM.1 hM.2]
  · rw [hs, hpi] at hp'
    omega

#print axioms shape_paid
#print axioms frame_is_at
#print axioms piece_numbers
#print axioms piece_bent_fails
#print axioms piece_bent_control
#print axioms shiftW_is
#print axioms frameIs_field

end Meaning.K2
