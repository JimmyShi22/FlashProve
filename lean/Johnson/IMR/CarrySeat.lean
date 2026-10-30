-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/CarrySeat.lean: a
property of blocks
that the lots' blocks have is had by every block that the description of the kinds' blocks alone
(ProofFile.onlineDescriptionFromPublicPart) lays in front of the blocks behind the last link: GENERAL IN THE PROPERTY AND IN THE
SEAT. The like of Johnson/IMR/KeepsSeat.lean, which is not turned.

A law ABOUT the harness's texts (ProofFile's Frames1.lean: guardMark, chainBy, roleOf; FillCore.lean:
fill, chainC; LotCore.lean: Lot.blocks; Pure.lean: partsAt, onlineDescriptionFromPublicPart): it turns none of them.
  guardMark_underP, named_underP: two more wrappers are UnderP (the parts also rename a block).
      andThen_wholeP, named_wholeP, guardMark_wholeP.
  QuietW R₀ b: b has no round and tells no oracle message, and its decision and all its runs keep
      R₀. FrameAsk Pr R₀ x: WHAT IS
      ASKED OF A BLOCK OF THE FRAMES' PLACES, BY ITS ROLE: at the role "front" (it is laid as a
      block): Pr · at every other role that the parts keep (lay, clear: its decision is laid as the
      link's lay | clear; behind: it is joined behind a place): QuietW.
  fill_carry, chainBy_frontP: every block of frontOf c has Pr, for the chain c that chainBy returns.
  LotsCarry Pr R₀ lots G: WHAT IS ASKED OF A SEAT's LOTS: blocks (inside a link: WholeP) · framesIn
      (of the kind "frame", inside a link: QuietW) · framesOut (of that kind, outside: Pr: THE SEAL
      IS OF THAT KIND AND HAS A ROUND) · batch (at every gatherer that keeps R₀: WholeP).
  role_link: by roleOf's text: the role "front" stands outside the links; a role that is none of
      front, common, stray stands inside.
  partsAt_roadP, partsAt_framesP, partsAt_baseP, pureZ_frontP.
FELLOWS, NOT CALLED. role_lay, role_clear (Johnson/IMR/FrameSeat.lean), role_behind
(Johnson/IMR/LaidFirst.lean) each end in p.link = some l: role_link's second half in three pieces;
they stand
over a far wider cone. frames_from_lots (Johnson/IMR/LaidFirst.lean) opens the parts' frames
as
partsAt_framesP does, and does not hand out that the role is neither common nor stray, which is
spent here.
CALLED, NOT TYPED: our chainC_first, mem_of_mapM_ok, all_of_made, chainBy_noFront, guardMark_whole
(Johnson/IMR/KeepsSeat.lean, KeepsDriver.lean) · pure_chain, base_made (Johnson/IMR/PureJoin.lean).
OBJECT: ProofFile.onlineDescriptionFromPublicPart's value at any seat T. USER: Johnson/IMR/RootsCut.lean. LETTERS: Pr, R₀, T: free.
OVER WHICH FILES: Johnson/IMR/KeepsSeat.lean and Johnson/Goal/Meaning/KeepsDriver.lean.



Limits. Nothing on the blocks behind the last link. Nothing on soundness.
-/
import Johnson.Desc.ProofFile.OnlineDescriptionFromBlockTables
import Johnson.IMR.PureJoin
import Johnson.IMR.KeepsSeat
import Johnson.Goal.Meaning.CarryDriver

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.Carry

open VerifiableInference.Desc
open VerifiableInference.Desc.First (S firstChain)
open VerifiableInference.Desc.Keeps (Decides Fn FnCl)
open Meaning.K2 (frontOf chainC_first mem_of_mapM_ok all_of_made chainBy_noFront)
open ProofFile (guardMark fill chainC chainBy Frames Gather FrameRole Lot Ground)

/-! ## 1 Two more wrappers; two blocks as one -/

theorem guardMark_underP (b : Block S ProofFile.Cl) : UnderP (guardMark b) b :=
  ⟨⟨rfl, fun s rs gs s' h => by
    obtain ⟨t, e, h⟩ := Keeps.ebind_ok (x := b.decide s rs gs) h
    split at h
    · cases h
      exact e
    · cases h⟩, id, rfl⟩

section
variable {T Cl : Type} {Pr : Block T Cl → Prop} {R₀ : T → T → Prop}

theorem andThen_wholeP (C : Carried Pr R₀) (n : String) {p q : Block T Cl}
    (W₁ : WholeP Pr R₀ p) (W₂ : WholeP Pr R₀ q) : WholeP Pr R₀ (p.andThen n q) :=
  ⟨C.andThen W₁.1 W₂.1,
    fun c hc => (List.mem_append.1 hc).elim (W₁.2.1 c) (W₂.2.1 c),
    fun c hc => (List.mem_append.1 hc).elim (W₁.2.2 c) (W₂.2.2 c)⟩

theorem named_underP (b : Block T Cl) (n : String) : UnderP { b with name := n } b :=
  ⟨⟨rfl, fun _ _ _ _ h => h⟩, id, rfl⟩

theorem named_wholeP (C : Carried Pr R₀) (n : String) {b : Block T Cl} (W : WholeP Pr R₀ b) :
    WholeP Pr R₀ { b with name := n } := ⟨C.under (named_underP b n) W.1, W.2.1, W.2.2⟩

/-- A block without a round, which tells no oracle message, all of whose functions keep R₀. -/
def QuietW (R₀ : T → T → Prop) (b : Block T Cl) : Prop :=
  b.rounds = [] ∧ b.oracles.flatten = [] ∧ Keeps.Whole R₀ b

theorem QuietW.wholeP (C : Carried Pr R₀) {b : Block T Cl} (W : QuietW R₀ b) : WholeP Pr R₀ b :=
  ⟨C.quiet W.1 W.2.1 W.2.2.1, W.2.2.2.1, W.2.2.2.2⟩

end

variable {Pr : Block S ProofFile.Cl → Prop} {R₀ : S → S → Prop}

theorem guardMark_wholeP (C : Carried Pr R₀) {b : Block S ProofFile.Cl} (W : WholeP Pr R₀ b) :
    WholeP Pr R₀ (guardMark b) := ⟨C.under (guardMark_underP b) W.1, W.2.1, W.2.2⟩

theorem guardMark_quietW {b : Block S ProofFile.Cl} (W : QuietW R₀ b) : QuietW R₀ (guardMark b) :=
  ⟨W.1, W.2.1, Meaning.K2.guardMark_whole W.2.2⟩

/-! ## 2 The driver's record that fill makes -/

theorem fill_carry {bs : List (Block S ProofFile.Cl)} {z : Block S ProofFile.Cl} {fr : Frames S ProofFile.Cl}
    (hb : ∀ b ∈ bs, b.place.link ≠ none → WholeP Pr R₀ b)
    (hbat : ∀ a mk, fr.batch a = some mk → ∀ f, FnCl R₀ f → Pr (mk f))
    (hl : ∀ l, Fn R₀ (fr.lay l)) (hc : ∀ l, Fn R₀ (fr.clear l)) (hf : Pr fr.first) :
    BlocksCarry Pr R₀ (fill bs z fr) where
  block a b ha h := by
    have h' : (bs.find? fun b => b.place == a) = some b := h
    have hp : (b.place == a) = true :=
      List.find?_some (p := fun x : Block S ProofFile.Cl => x.place == a) h'
    have e : b.place = a := eq_of_beq hp
    exact hb b (List.mem_of_find?_eq_some h') (e ▸ ha)
  batch a mk ha h f hf' := by
    have h' : (fr.batch a <|> (bs.find? fun b => b.place == a).map fun b _ => b) = some mk := h
    cases hq : fr.batch a with
    | some m =>
      rw [hq] at h'
      have e : some m = some mk := h'
      cases e
      exact hbat a _ hq f hf'
    | none =>
      rw [hq] at h'
      have h'' : ((bs.find? fun b => b.place == a).map fun b _ => b) = some mk := h'
      obtain ⟨b, hb', rfl⟩ := Option.map_eq_some_iff.1 h''
      have hp : (b.place == a) = true :=
        List.find?_some (p := fun x : Block S ProofFile.Cl => x.place == a) hb'
      have e : b.place = a := eq_of_beq hp
      exact (hb b (List.mem_of_find?_eq_some hb') (e ▸ ha)).1
  lay := hl
  clear := hc
  first := hf

/-- What is asked of a block of the frames' places, by its role: the chain's front is laid as a
block; the others' decisions are also laid as a link's lay | clear, or joined behind a place. -/
def FrameAsk (Pr : Block S ProofFile.Cl → Prop) (R₀ : S → S → Prop) (x : FrameRole × Block S ProofFile.Cl) :
    Prop :=
  (x.1 = FrameRole.front → Pr x.2) ∧ (x.1 ≠ FrameRole.front → QuietW R₀ x.2)

/-- **The first chain that chainBy makes: every block in front of the blocks behind the last
link.** -/
theorem chainBy_frontP (C : Carried Pr R₀) {Z : ProofFile.Pub} {base : List (Block S ProofFile.Cl)}
    {fr : List (FrameRole × Block S ProofFile.Cl)} {road : Gather S ProofFile.Cl} {c : Chain S ProofFile.Cl}
    (h : chainBy Z base fr road = .ok c)
    (hb : ∀ b ∈ base, b.place.link ≠ none → WholeP Pr R₀ b) (hfr : ∀ x ∈ fr, FrameAsk Pr R₀ x)
    (hbat : ∀ a mk, road.batch a = some mk → ∀ f, FnCl R₀ f → Pr (mk f)) :
    ∀ b ∈ frontOf c, Pr b := by
  unfold chainBy at h
  obtain ⟨z, several, hc⟩ := chainC_first h
  refine firstChain_frontP C (fill_carry ?_ hbat ?_ ?_ ?_) hc
  · intro b hb' hl
    obtain ⟨b₀, h₀, rfl⟩ := List.mem_map.1 (List.mem_of_mem_dropLast hb')
    split
    · rename_i x hx
      simp only [hx] at hl
      have hne : x.1 ≠ FrameRole.front := fun e => by
        have hq := List.find?_some hx
        rw [e] at hq
        cases hq
      exact andThen_wholeP C _ (hb b₀ h₀ hl)
        (guarded_wholeP C _ _ (((hfr x (List.mem_of_find?_eq_some hx)).2 hne).wholeP C))
    · rename_i hx
      simp only [hx] at hl
      exact hb b₀ h₀ hl
  · intro l t s' k
    dsimp only at k
    split at k
    · rename_i o ho
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 ho
      have hne : x.1 ≠ FrameRole.front := fun e => by
        have hq := List.find?_some hx
        rw [e] at hq
        cases hq
      exact ((hfr x (List.mem_of_find?_eq_some hx)).2 hne).2.2.1 _ _ _ _ k
    · cases k
      exact C.refl _
  · intro l t s' k
    dsimp only at k
    split at k
    · rename_i o ho
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 ho
      have hne : x.1 ≠ FrameRole.front := fun e => by
        have hq := List.find?_some hx
        rw [e] at hq
        cases hq
      exact ((hfr x (List.mem_of_find?_eq_some hx)).2 hne).2.2.1 _ _ _ _ k
    · cases k
      exact C.refl _
  · dsimp only
    split
    · rename_i o ho
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 ho
      have he : x.1 = FrameRole.front := by
        have hq := List.find?_some hx
        cases h1 : x.1 <;> rw [h1] at hq <;> first | rfl | cases hq
      exact C.under (named_underP _ _) ((hfr x (List.mem_of_find?_eq_some hx)).1 he)
    · exact C.quiet rfl rfl fun s _ _ s' k => by cases k; exact C.refl _

/-! ## 3 The lots -/

/-- **What is asked of a seat's lots.** -/
structure LotsCarry (Pr : Block S ProofFile.Cl → Prop) (R₀ : S → S → Prop) (lots : List Lot)
    (G : Ground) : Prop where
  blocks : ∀ L ∈ lots, ∀ b ∈ L.blocks G, b.place.link ≠ none → WholeP Pr R₀ b
  framesIn : ∀ L ∈ lots, ∀ b ∈ L.blocks G, (b.place.kind == KindName.frame) = true →
    b.place.link ≠ none → QuietW R₀ b
  framesOut : ∀ L ∈ lots, ∀ b ∈ L.blocks G, (b.place.kind == KindName.frame) = true →
    b.place.link = none → Pr b
  batch : ∀ L ∈ lots, ∀ a mk, L.batch G a = some mk → ∀ f, FnCl R₀ f → WholeP Pr R₀ (mk f)

variable {T : ProofFile.PureSeat} {B : ProofFile.PureBase}

theorem partsAt_roadP (C : Carried Pr R₀) (K : LotsCarry Pr R₀ T.lots B.G₀) {a : Place}
    {mk : (S → Except String (List ProofFile.Cl × S)) → Block S ProofFile.Cl}
    (h : (ProofFile.partsAt T B).road.batch a = some mk) :
    ∀ f, FnCl R₀ f → WholeP Pr R₀ (mk f) := by
  intro f hf
  simp only [ProofFile.partsAt] at h
  obtain ⟨mk₀, h₀, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨L, hL, e⟩ := List.exists_of_findSome?_eq_some h₀
  exact named_wholeP C _ (guardMark_wholeP C (K.batch L (List.mem_of_mem_filter hL) a mk₀ e f hf))

/-- The role, off ProofFile's text: the front stands outside the links; lay, clear and behind inside. -/
theorem role_link (shape : List (String × Place)) (p : Place) :
    (ProofFile.roleOf shape p = FrameRole.front → p.link = none) ∧
      (ProofFile.roleOf shape p ≠ FrameRole.front → ProofFile.roleOf shape p ≠ FrameRole.common →
        ProofFile.roleOf shape p ≠ FrameRole.stray → p.link ≠ none) := by
  have key : ∀ r, ProofFile.roleOf shape p = r → (r = FrameRole.front → p.link = none) ∧
      (r ≠ FrameRole.front → r ≠ FrameRole.common → r ≠ FrameRole.stray → p.link ≠ none) := by
    intro r hr
    unfold ProofFile.roleOf at hr
    split at hr
    · subst hr
      exact ⟨fun h => (nomatch h), fun _ _ h => absurd rfl h⟩
    · rename_i e hf hl
      refine ⟨fun _ => hl, fun h1 h2 h3 => ?_⟩
      split at hr
      · exact absurd hr.symm h3
      · split at hr
        · exact absurd hr.symm h1
        · exact absurd hr.symm h2
    · rename_i e l hf hl
      refine ⟨fun h => ?_, fun _ _ _ => by rw [hl]; exact Option.some_ne_none l⟩
      subst h
      split at hr
      · cases hr
      · split at hr
        · cases hr
        · split at hr <;> cases hr
  exact key _ rfl

theorem partsAt_framesP (C : Carried Pr R₀) (K : LotsCarry Pr R₀ T.lots B.G₀)
    (hall : ∀ x ∈ B.all, x.1 ∈ T.lots ∧ x.2 = x.1.blocks B.G₀) :
    ∀ x ∈ (ProofFile.partsAt T B).frames, FrameAsk Pr R₀ x := by
  intro x hx
  simp only [ProofFile.partsAt] at hx
  obtain ⟨y, hy, hx⟩ := List.mem_flatMap.1 hx
  split at hx
  · cases hx
  · obtain ⟨b, hb, e⟩ := List.mem_filterMap.1 hx
    obtain ⟨hb1, hb2⟩ := List.mem_filter.1 hb
    obtain ⟨k1, k2⟩ := hall y hy
    have hm : b ∈ y.1.blocks B.G₀ := k2 ▸ hb1
    split at e
    · cases e
    · cases e
    · rename_i r n1 n2
      cases e
      refine ⟨fun h0 => C.under (guardMark_underP b)
        (K.framesOut y.1 k1 b hm hb2 ((role_link _ _).1 h0)), fun h0 => guardMark_quietW
        (K.framesIn y.1 k1 b hm hb2 ((role_link _ _).2 h0 n1 n2))⟩

theorem partsAt_baseP (C : Carried Pr R₀) (K : LotsCarry Pr R₀ T.lots B.G₀)
    (hall : ∀ x ∈ B.all, x.1 ∈ T.lots ∧ x.2 = x.1.blocks B.G₀) {base : List (Block S ProofFile.Cl)}
    (h : (ProofFile.partsAt T B).base = .ok base) :
    ∀ b ∈ base, b.place.link ≠ none → WholeP Pr R₀ b := by
  intro b hb hl
  unfold ProofFile.PureParts.base at h
  obtain ⟨x, hx, e⟩ := mem_of_mapM_ok _ _ _ h b hb
  simp only [ProofFile.partsAt] at hx
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
  dsimp only at e
  split at e
  · rename_i _ _ f hface
    obtain ⟨mk, hmk, rfl⟩ := Option.map_eq_some_iff.1 hface
    obtain ⟨mk₀, h₀, rfl⟩ := Option.map_eq_some_iff.1 hmk
    obtain ⟨L, hL, eL⟩ := List.exists_of_findSome?_eq_some h₀
    cases e
    exact named_wholeP C _ (guardMark_wholeP C (K.batch L (List.mem_of_mem_filter hL) _ mk₀ eL
      (fun s => .ok ([], s)) (fun s y k => by cases k; exact C.refl s)))
  · rename_i _ _ y _ hs
    obtain ⟨z, hz, ez⟩ := List.mem_filterMap.1 (List.mem_of_find?_eq_some hs)
    obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 ez
    obtain ⟨k1, k2⟩ := hall z hz
    cases e
    exact named_wholeP C _
      (guardMark_wholeP C (K.blocks z.1 k1 b₀ (k2 ▸ List.mem_of_find?_eq_some hb₀) hl))
  · split at e <;> cases e

/-- **The description of the lots' blocks alone: every block in front of the blocks behind the last
link has the property that the lots' blocks have.** -/
theorem pureZ_frontP (C : Carried Pr R₀) {Z : ProofFile.Pub} (K : ∀ G, LotsCarry Pr R₀ T.lots G)
    {F : FileDescription ProofFile.Inst} (h : ProofFile.onlineDescriptionFromPublicPart Z T = .ok F) :
    ∃ (A : ProofFile.SharedSeat) (B' : ProofFile.SecondSeat) (c : Chain S ProofFile.Cl),
      F = ProofFile.fileDescBy T.older T.links Z A B' (fun s => s) (ProofFile.startS Z) c ∧ c.front = [] ∧
        ∀ b ∈ frontOf c, Pr b := by
  obtain ⟨B, base, c, A, B', hB, -, -, hbase, hc, -, -, e⟩ := IM.pure_chain h
  have hall := all_of_made (IM.base_made hB).2.2.2
  exact ⟨A, B', c, e, chainBy_noFront hc, chainBy_frontP C hc
    (partsAt_baseP C (K _) hall hbase) (partsAt_framesP C (K _) hall)
    (fun a mk e f hf => (partsAt_roadP C (K _) e f hf).1)⟩

#print axioms chainBy_frontP
#print axioms pureZ_frontP

end Meaning.Carry
