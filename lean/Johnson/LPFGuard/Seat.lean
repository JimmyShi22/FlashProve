-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFGuard/Seat.lean: THE GUARD ON THE REPLY: from the lots to the driver's structure, and two
seats that part in the guard's test alone. Theorems with their proofs. General in the seat T.

What the file is. `ProofFile.onlineDescriptionFromPublicPart Z T` (Johnson/Desc/ProofFile/OnlineDescriptionFromBlockTables.lean) makes the proof file's
description from a seat's lots: by `baseOf` and `partsAt` (Pure.lean), `chainBy` (Frames1.lean),
`chainC` and `fill` (FillCore.lean) and the driver's `firstChain`. Here that road is walked once, at
the relation "the reply stays", with K7's place exempted, down to what Driver.lean asks of the
driver's structure (`BlocksBut`); and then it is walked at two seats that part in the field `same`
alone.

Main names, in the file's order.
* `AlikeE P x y`: two values that may be refusals: both are values, related by P, or both are
  refusals with the same words. `AlikeE.bind`, `AlikeE.refl`.
* `But b`: b stands at a place of the kind K7 or its decision leaves the reply; its runs leave it.
* `partsAt_roadBut`, `partsAt_framesBut`, `partsAt_baseBut`: what `LotsBut` gives of the parts that
  `partsAt` makes: the batchings, the blocks of the kind "frame", the places' blocks.
* `fill_but`: the driver's structure that `fill` makes has `BlocksBut`.
* `FlatOne c c'`: one flat list, one last block's rounds. `chainC_alike`: `chainC` at the seat's
  test and at a test that always says yes: made or refused together, `FlatOne` where made.
* `but_andThen`, `chainBy_alike`: the like for `chainBy`. There the guard at place (b), around what
  is joined behind a block, falls at both tests (`guarded_self`, `guarded_idle_self`), so the two
  lists of blocks are one list.
* `base_last`, `base_last_decides`: the last of the places' blocks stems from the plan's last place;
  where that place is of the kind "frame" it is no block at K7's place, so its decision leaves the
  reply. (`chainC` takes the chain's last block by its position, and the driver guards it.)
* `pureZ_alike`: **`onlineDescriptionFromPublicPart Z T` and `onlineDescriptionFromPublicPart Z { T with same := same' }`** are made or refused
  together, and `Alike` where made: for T.same = `sameReply`, a same' that always says yes, lots
  with `LotsBut`, and a Z whose table of steps is `cutOf`'s.

What it leans on. In this folder: Ground.lean, Driver.lean (`BlocksBut`, `strike_at`, `idle_at`),
Unguarded.lean (`Alike`). In the library, called: `guardMark_decides`, `guardMark_whole`,
`all_of_made` (Johnson/IMR/KeepsSeat.lean), `mem_of_mapM_ok`, `guarded_whole`
(Johnson/Goal/Meaning/KeepsDriver.lean), `Keeps.andThen_decides`, `Keeps.andThen_whole`
(Johnson/Desc/BlockKeeps.lean), `IM.base_made` (Johnson/IMR/PureJoin.lean), `IM.places_spots`
(Johnson/IMR/BackSeat.lean), `Fo.Pub.mapM_at` (OnBytes/Tie/Pv/Lookup/Ends/FoPublicA.lean),
`OnBytes.Road.Hd.mapM_length` (Johnson/Road/HeadL5Grp.lean), `ProofFile.Law.spotsOf_cutOf`
(Johnson/Desc/ProofFile/Law/LastSpot.lean).
Carried proofs. `partsAt_roadBut`, `partsAt_framesBut`, `partsAt_baseBut`, `fill_but` and the five
bullets of `chainBy_alike` follow `partsAt_roadW`, `partsAt_frames`, `partsAt_baseAll`, `fill_keeps`
and `chainBy_front` (Johnson/IMR/KeepsSeat.lean), with the alternative "or the block stands at a
place of the kind K7" added; `base_last` follows `IM.chain_last` (Johnson/IMR/BackSeat.lean). Those
cannot be called: they ask the relation of every block, K7's too.

Limits. Theorems about the definitions named above, as they are written. `LotsBut` is a premise
here: it is proved in Lots.lean and Makers.lean. That `onlineDescriptionFromPublicPart` makes anything is not shown. Nothing
on soundness.


-/
import Johnson.LPFGuard.Ground
import Johnson.LPFGuard.Driver
import Johnson.IMR.KeepsSeat
import Johnson.IMR.BackSeat
import Johnson.Desc.ProofFile.Law.LastSpot
import Johnson.LPFGuard.Unguarded

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFGuard

open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.Keeps (Whole Decides Fn FnCl)
open ProofFile (guardMark fill chainC chainBy Frames Gather FrameRole Lot Ground)
open Meaning.K2 (guardMark_decides guardMark_whole mem_of_mapM_ok guarded_whole)

/-! ## 0 Two values that may be refusals -/

universe u v

/-- Both are values, related by P; or both are refusals with the same words. -/
def AlikeE {α : Type u} (P : α → α → Prop) : Except String α → Except String α → Prop
  | .ok a, .ok b => P a b
  | .error e, .error e' => e' = e
  | _, _ => False

theorem AlikeE.bind {α : Type u} {β : Type v} {P : α → α → Prop} {Q : β → β → Prop}
    {x y : Except String α} {f g : α → Except String β} (h : AlikeE P x y)
    (k : ∀ a b, P a b → AlikeE Q (f a) (g b)) : AlikeE Q (x.bind f) (y.bind g) := by
  cases x <;> cases y
  · exact h
  · exact h.elim
  · exact h.elim
  · exact k _ _ h

theorem AlikeE.refl {α : Type u} {P : α → α → Prop} (hP : ∀ a, P a a) (x : Except String α) :
    AlikeE P x x := by
  cases x
  · exact rfl
  · exact hP _

/-! ## 1 What the lots' blocks give of the parts -/

variable {T : ProofFile.PureSeat} {B : ProofFile.PureBase}

/-- A block stands at a place of the kind K7 or its decision leaves the reply; its runs leave it. -/
def But (b : Block S ProofFile.Cl) : Prop :=
  (b.place.kind = KindName.K7 ∨ Decides ReplyR b) ∧ Runs ReplyR b

theorem partsAt_roadBut (K : LotsBut ReplyR T.lots B.G₀) {a : Place}
    {mk : (S → Except String (List ProofFile.Cl × S)) → Block S ProofFile.Cl}
    (h : (ProofFile.partsAt T B).road.batch a = some mk) :
    ∀ f, FnCl ReplyR f → Whole ReplyR (mk f) := by
  intro f hf
  simp only [ProofFile.partsAt] at h
  obtain ⟨mk₀, h₀, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨L, hL, e⟩ := List.exists_of_findSome?_eq_some h₀
  exact guardMark_whole (K.batch L (List.mem_of_mem_filter hL) a mk₀ e f hf)

theorem partsAt_framesBut (K : LotsBut ReplyR T.lots B.G₀)
    (hall : ∀ x ∈ B.all, x.1 ∈ T.lots ∧ x.2 = x.1.blocks B.G₀) :
    ∀ x ∈ (ProofFile.partsAt T B).frames, Whole ReplyR x.2 := by
  intro x hx
  simp only [ProofFile.partsAt] at hx
  obtain ⟨y, hy, hx⟩ := List.mem_flatMap.1 hx
  split at hx
  · cases hx
  · obtain ⟨b, hb, e⟩ := List.mem_filterMap.1 hx
    obtain ⟨hb1, hb2⟩ := List.mem_filter.1 hb
    obtain ⟨k1, k2⟩ := hall y hy
    have hk : b.place.kind = KindName.frame := eq_of_beq hb2
    have W : Whole ReplyR b :=
      ⟨(K.blocks y.1 k1 b (k2 ▸ hb1)).resolve_left (by rw [hk]; exact fun q => nomatch q),
        K.runs y.1 k1 b (k2 ▸ hb1)⟩
    split at e
    · cases e
    · cases e
    · cases e
      exact guardMark_whole W

theorem partsAt_baseBut (K : LotsBut ReplyR T.lots B.G₀)
    (hall : ∀ x ∈ B.all, x.1 ∈ T.lots ∧ x.2 = x.1.blocks B.G₀) {base : List (Block S ProofFile.Cl)}
    (h : (ProofFile.partsAt T B).base = .ok base) : ∀ b ∈ base, But b := by
  intro b hb
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
    have W := guardMark_whole (K.batch L (List.mem_of_mem_filter hL) _ mk₀ eL
      (fun s => .ok ([], s)) (fun s y k => by cases k; exact replyR_refl s))
    exact ⟨Or.inr W.1, W.2⟩
  · rename_i _ _ y _ hs
    obtain ⟨z, hz, ez⟩ := List.mem_filterMap.1 (List.mem_of_find?_eq_some hs)
    obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 ez
    obtain ⟨k1, k2⟩ := hall z hz
    cases e
    have m := k2 ▸ List.mem_of_find?_eq_some hb₀
    exact ⟨(K.blocks z.1 k1 b₀ m).imp id guardMark_decides, K.runs z.1 k1 b₀ m⟩
  · split at e <;> cases e

/-! ## 2 The driver's structure that fill makes -/

theorem leaves_of_but {b : Block S ProofFile.Cl} {a : Place} (h : But b) (e : b.place = a) :
    a.kind = KindName.K7 ∨ b.Leaves hR := by
  subst e
  exact h.1.imp id leaves_of_decides

/-- **The driver's structure that fill makes**, from a list whose blocks stand at K7 or leave the
reply. The last block and the first leave it outright. -/
theorem fill_but {bs : List (Block S ProofFile.Cl)} {z : Block S ProofFile.Cl} {fr : Frames S ProofFile.Cl}
    (hb : ∀ b ∈ bs, But b) (hz : Whole ReplyR z)
    (hbat : ∀ a mk, fr.batch a = some mk → ∀ f, FnCl ReplyR f → Whole ReplyR (mk f))
    (hl : ∀ l, Fn ReplyR (fr.lay l)) (hc : ∀ l, Fn ReplyR (fr.clear l))
    (hf : Whole ReplyR fr.first) : BlocksBut hR (fill bs z fr) where
  block a b h := by
    have h' : (bs.find? fun b => b.place == a) = some b := h
    have hp : (b.place == a) = true :=
      List.find?_some (p := fun x : Block S ProofFile.Cl => x.place == a) h'
    exact leaves_of_but (hb b (List.mem_of_find?_eq_some h')) (eq_of_beq hp)
  runs a b h := by
    have h' : (bs.find? fun b => b.place == a) = some b := h
    exact runsLeave_of_runs (hb b (List.mem_of_find?_eq_some h')).2
  batch a mk ha h f hf' := by
    have h' : (fr.batch a <|> (bs.find? fun b => b.place == a).map fun b _ => b) = some mk := h
    cases hq : fr.batch a with
    | some m =>
      rw [hq] at h'
      have e : some m = some mk := h'
      cases e
      have W := hbat a _ hq f hf'
      exact ⟨leaves_of_decides W.1, runsLeave_of_whole W⟩
    | none =>
      rw [hq] at h'
      have h'' : ((bs.find? fun b => b.place == a).map fun b _ => b) = some mk := h'
      obtain ⟨b, hb', rfl⟩ := Option.map_eq_some_iff.1 h''
      have hp : (b.place == a) = true :=
        List.find?_some (p := fun x : Block S ProofFile.Cl => x.place == a) hb'
      have e : b.place = a := eq_of_beq hp
      have B := hb b (List.mem_of_find?_eq_some hb')
      refine ⟨leaves_of_decides (B.1.resolve_left ?_), runsLeave_of_runs B.2⟩
      rw [e, ha]
      exact fun q => nomatch q
  lay l s s' k := hl l s s' k
  clear l s s' k := hc l s s' k
  first := ⟨leaves_of_decides hf.1, runsLeave_of_whole hf⟩
  last := ⟨leaves_of_decides hz.1, runsLeave_of_whole hz⟩

/-! ## 3 Two chains that part in the guard's test alone -/

/-- Two chains have one flat list and one last block's rounds. -/
def FlatOne (c c' : Chain S ProofFile.Cl) : Prop :=
  c'.blocksInOrder = c.blocksInOrder ∧ c'.last.rounds = c.last.rounds

/-- **chainC at the seat's test and at a test that always says yes.** -/
theorem chainC_alike {bs bs' : List (Block S ProofFile.Cl)} {links : List ModelPart}
    {fr : Frames S ProofFile.Cl} {same' : S → S → Bool} (e : bs' = bs)
    (hs : fr.same = ProofFile.sameReply) (hs' : ∀ t s, same' t s = true)
    (K : ∀ z, bs.getLast? = some z → BlocksBut hR (fill bs.dropLast z fr)) :
    AlikeE FlatOne (chainC bs links fr) (chainC bs' links { fr with same := same' }) := by
  subst e
  unfold chainC
  cases hz : bs'.getLast? with
  | none => exact rfl
  | some z =>
    dsimp only
    have hb : firstChainWithoutReplyGuard (fill bs'.dropLast z { fr with same := same' }) links
        (bs'.any fun b => b.place.kind == KindName.K13) =
        firstChainWithoutReplyGuard (fill bs'.dropLast z fr) links
          (bs'.any fun b => b.place.kind == KindName.K13) :=
      bare_same_with (fill bs'.dropLast z fr) same' links _
    cases h1 : firstChain (fill bs'.dropLast z fr) links
        (bs'.any fun b => b.place.kind == KindName.K13) with
    | none =>
      have h2 : firstChain (fill bs'.dropLast z { fr with same := same' }) links
          (bs'.any fun b => b.place.kind == KindName.K13) = none := by
        unfold firstChain at h1 ⊢
        rw [hb]
        cases hq : firstChainWithoutReplyGuard (fill bs'.dropLast z fr) links
            (bs'.any fun b => b.place.kind == KindName.K13) with
        | none => rfl
        | some c₀ => rw [hq] at h1; cases h1
      rw [h2]
      exact rfl
    | some c =>
      obtain ⟨c₀, q₀, f₀, l₀⟩ := strike_at (h := hR)
        (show (fill bs'.dropLast z fr).same = sameBy hR from hs.trans sameReply_sameBy)
        (K z hz) h1
      have h2 : firstChain (fill bs'.dropLast z { fr with same := same' }) links
          (bs'.any fun b => b.place.kind == KindName.K13) =
          some (c₀.guarded same' hearsReply) := by
        unfold firstChain
        rw [hb, q₀]
        rfl
      obtain ⟨c₁, q₁, f₁, l₁⟩ := idle_at
        (H := fill bs'.dropLast z { fr with same := same' }) hs' h2
      obtain rfl : c₁ = c₀ := Option.some.inj ((q₁.symm.trans hb).trans q₀)
      rw [h2]
      dsimp only
      rw [f₀, f₁]
      cases bs'.find? fun b => !(c₁.blocksInOrder.any fun x => x.name == b.name) with
      | some b => exact rfl
      | none => exact ⟨f₁.trans f₀.symm, l₁.trans l₀.symm⟩

/-! ## 4 chainBy at the seat's test and at a test that always says yes -/

theorem but_andThen {b q : Block S ProofFile.Cl} (n : String) (hb : But b) (hq : Whole ReplyR q) :
    But (b.andThen n q) :=
  ⟨hb.1.imp id fun d => Keeps.andThen_decides ReplyR replyR_trans n b q d hq.1,
    fun c hc => (List.mem_append.1 hc).elim (hb.2.1 c) (hq.2.1 c),
    fun c hc => (List.mem_append.1 hc).elim (hb.2.2 c) (hq.2.2 c)⟩

theorem chainBy_alike {Z : ProofFile.Pub} {base : List (Block S ProofFile.Cl)}
    {fr : List (FrameRole × Block S ProofFile.Cl)} {road : Gather S ProofFile.Cl} {same' : S → S → Bool}
    (hs : road.same = ProofFile.sameReply) (hs' : ∀ t s, same' t s = true)
    (hb : ∀ b ∈ base, But b) (hlast : ∀ z, base.getLast? = some z → Decides ReplyR z)
    (hfr : ∀ x ∈ fr, Whole ReplyR x.2)
    (hbat : ∀ a mk, road.batch a = some mk → ∀ f, FnCl ReplyR f → Whole ReplyR (mk f)) :
    AlikeE FlatOne (chainBy Z base fr road) (chainBy Z base fr { road with same := same' }) := by
  unfold chainBy
  refine chainC_alike (List.map_congr_left ?_) hs hs' ?_
  · intro b _
    split
    · rename_i x hx
      have W := hfr x (List.mem_of_find?_eq_some hx)
      rw [guarded_idle_self hs' _ x.2, hs, sameReply_sameBy,
        guarded_self (leaves_of_decides W.1) (runsLeave_of_whole W)]
    · rfl
  · intro z hz
    rw [List.getLast?_map] at hz
    obtain ⟨b0, hb0, ez⟩ := Option.map_eq_some_iff.1 hz
    refine fill_but ?_ ?_ hbat ?_ ?_ ?_
    · intro b hb'
      obtain ⟨b₀, h₀, rfl⟩ := List.mem_map.1 (List.mem_of_mem_dropLast hb')
      split
      · rename_i x hx
        exact but_andThen _ (hb b₀ h₀) (guarded_whole _ _ (hfr x (List.mem_of_find?_eq_some hx)))
      · exact hb b₀ h₀
    · have W0 : Whole ReplyR b0 := ⟨hlast b0 hb0, (hb b0 (List.mem_of_getLast? hb0)).2⟩
      rw [← ez]
      split
      · rename_i x hx
        exact Keeps.andThen_whole ReplyR replyR_trans _ _ _ W0
          (guarded_whole _ _ (hfr x (List.mem_of_find?_eq_some hx)))
      · exact W0
    · intro l t s' k
      dsimp only at k
      split at k
      · rename_i o ho
        obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 ho
        exact (hfr x (List.mem_of_find?_eq_some hx)).1 _ _ _ _ k
      · cases k
        exact replyR_refl _
    · intro l t s' k
      dsimp only at k
      split at k
      · rename_i o ho
        obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 ho
        exact (hfr x (List.mem_of_find?_eq_some hx)).1 _ _ _ _ k
      · cases k
        exact replyR_refl _
    · dsimp only
      split
      · rename_i o ho
        obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 ho
        exact hfr x (List.mem_of_find?_eq_some hx)
      · exact ⟨fun s _ _ s' k => by cases k; exact replyR_refl _, (fun _ hc => nomatch hc),
          (fun _ hc => nomatch hc)⟩

/-! ## 5 The last block -/

/-- The last of the places' blocks stems from the plan's last place. -/
theorem base_last {base : List (Block S ProofFile.Cl)} (hb : (ProofFile.partsAt T B).base = .ok base)
    {b0 : Block S ProofFile.Cl} (h0 : base.getLast? = some b0) :
    ∃ sp, B.spots.getLast? = some sp ∧ (sp, Except.ok b0) ∈ (ProofFile.partsAt T B).places := by
  rw [List.getLast?_eq_getElem?] at h0
  obtain ⟨x, hx, ex⟩ := Fo.Pub.mapM_at _ _ _ hb _ b0 h0
  obtain ⟨sp, y⟩ := x
  obtain rfl : y = .ok b0 := ex
  have hlen : base.length = B.spots.length := by
    rw [OnBytes.Road.Hd.mapM_length _ _ _ hb, ← IM.places_spots T B, List.length_map]
  refine ⟨sp, ?_, List.mem_of_getElem? hx⟩
  rw [List.getLast?_eq_getElem?, ← hlen, ← IM.places_spots T B, List.getElem?_map, hx]
  rfl

/-- Where the plan's last place is of the kind "frame", the last of the places' blocks leaves the
reply by its decision: it is no block at K7's place. -/
theorem base_last_decides (K : LotsBut ReplyR T.lots B.G₀)
    (hall : ∀ x ∈ B.all, x.1 ∈ T.lots ∧ x.2 = x.1.blocks B.G₀)
    (hsp : ∀ sp, B.spots.getLast? = some sp → sp.place.kind = KindName.frame)
    {base : List (Block S ProofFile.Cl)} (hb : (ProofFile.partsAt T B).base = .ok base) :
    ∀ z, base.getLast? = some z → Decides ReplyR z := by
  intro z hz
  obtain ⟨sp, h1, hx⟩ := base_last hb hz
  have hk := hsp sp h1
  simp only [ProofFile.partsAt] at hx
  obtain ⟨p, -, e⟩ := List.mem_map.1 hx
  obtain ⟨rfl, e⟩ := Prod.mk.inj e
  split at e
  · rename_i _ _ f hface
    obtain ⟨mk, hmk, rfl⟩ := Option.map_eq_some_iff.1 hface
    obtain ⟨mk₀, h₀, rfl⟩ := Option.map_eq_some_iff.1 hmk
    obtain ⟨L, hL, eL⟩ := List.exists_of_findSome?_eq_some h₀
    cases e
    exact (guardMark_whole (K.batch L (List.mem_of_mem_filter hL) _ mk₀ eL
      (fun s => .ok ([], s)) (fun s y k => by cases k; exact replyR_refl s))).1
  · rename_i _ _ y _ hs
    obtain ⟨w, hw, ew⟩ := List.mem_filterMap.1 (List.mem_of_find?_eq_some hs)
    obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 ew
    obtain ⟨k1, k2⟩ := hall w hw
    cases e
    have hp : (b₀.place == p.place) = true :=
      List.find?_some (p := fun x : Block S ProofFile.Cl => x.place == p.place) hb₀
    have m := k2 ▸ List.mem_of_find?_eq_some hb₀
    refine guardMark_decides ((K.blocks w.1 k1 b₀ m).resolve_left ?_)
    rw [eq_of_beq hp, hk]
    exact fun q => nomatch q
  · split at e <;> cases e

/-! ## 6 Two seats that part in the guard's test alone -/

/-- **onlineDescriptionFromPublicPart at the seat's test and at a test that always says yes.** -/
theorem pureZ_alike {Z : ProofFile.Pub} {same' : S → S → Bool} (hT : T.same = ProofFile.sameReply)
    (hs' : ∀ t s, same' t s = true) (K : ∀ G, LotsBut ReplyR T.lots G)
    (hcut : ∃ es, cutOf es = some Z.cuts) :
    AlikeE Alike (ProofFile.onlineDescriptionFromPublicPart Z T) (ProofFile.onlineDescriptionFromPublicPart Z { T with same := same' }) := by
  unfold ProofFile.onlineDescriptionFromPublicPart
  show AlikeE Alike ((ProofFile.baseOf Z T).bind _) ((ProofFile.baseOf Z T).bind _)
  cases hB : ProofFile.baseOf Z T with
  | error e => exact rfl
  | ok B₀ =>
    show AlikeE Alike
      (if !(ProofFile.faultsAt T B₀).isEmpty then _
        else if !(ProofFile.lackingAt T (ProofFile.partsAt T B₀)).isEmpty then _
        else ProofFile.onlineDescriptionAfterTests Z T (ProofFile.partsAt T B₀))
      (if !(ProofFile.faultsAt T B₀).isEmpty then _
        else if !(ProofFile.lackingAt T (ProofFile.partsAt T B₀)).isEmpty then _
        else ProofFile.onlineDescriptionAfterTests Z { T with same := same' } (ProofFile.partsAt { T with same := same' } B₀))
    split
    · exact rfl
    split
    · exact rfl
    have hm := IM.base_made hB
    have hall := Meaning.K2.all_of_made hm.2.2.2
    obtain ⟨es, hes⟩ := hcut
    have hsp : ∀ sp, B₀.spots.getLast? = some sp → sp.place.kind = KindName.frame := by
      intro sp h
      obtain ⟨l0, sp', e, k, -⟩ := ProofFile.Law.spotsOf_cutOf hes hm.1
      rw [e, List.getLast?_append_of_ne_nil _ (by simp), List.getLast?_singleton] at h
      cases h
      exact k
    unfold ProofFile.onlineDescriptionAfterTests
    show AlikeE Alike ((ProofFile.partsAt T B₀).base.bind _) ((ProofFile.partsAt T B₀).base.bind _)
    cases hb : (ProofFile.partsAt T B₀).base with
    | error e => exact rfl
    | ok base =>
      show AlikeE Alike
        ((chainBy Z base (ProofFile.partsAt T B₀).frames (ProofFile.partsAt T B₀).road).bind _)
        ((chainBy Z base (ProofFile.partsAt T B₀).frames
          { (ProofFile.partsAt T B₀).road with same := same' }).bind _)
      refine AlikeE.bind (chainBy_alike (show (ProofFile.partsAt T B₀).road.same = _ from hT) hs'
        (partsAt_baseBut (K _) hall hb) (base_last_decides (K _) hall hsp hb)
        (partsAt_framesBut (K _) hall) fun a mk e => partsAt_roadBut (K _) e) ?_
      intro c c' hcc
      show AlikeE Alike (match T.shared, T.second with
          | some A, some B => _
          | _, _ => _)
        (match T.shared, T.second with
          | some A, some B => _
          | _, _ => _)
      split
      · exact ⟨_, _, _, _, _, c, c', rfl, rfl, hcc.1, hcc.2⟩
      · exact rfl

end LPFGuard

#print axioms LPFGuard.AlikeE.bind
#print axioms LPFGuard.AlikeE.refl
#print axioms LPFGuard.partsAt_roadBut
#print axioms LPFGuard.partsAt_framesBut
#print axioms LPFGuard.partsAt_baseBut
#print axioms LPFGuard.leaves_of_but
#print axioms LPFGuard.fill_but
#print axioms LPFGuard.chainC_alike
#print axioms LPFGuard.but_andThen
#print axioms LPFGuard.chainBy_alike
#print axioms LPFGuard.base_last
#print axioms LPFGuard.base_last_decides
#print axioms LPFGuard.pureZ_alike
