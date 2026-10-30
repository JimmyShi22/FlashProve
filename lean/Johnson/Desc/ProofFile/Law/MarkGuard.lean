--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Law/MarkGuard.lean: every block that `partsAt` (OnlineDescriptionFromBlockTables.lean) takes from a lot
stands behind `guardMark` (Frames1.lean), and what that is worth. Theorems only; no file of the
description imports this one.
Why. Several functions of State.lean mark the state as failed and go on. `guardMark b` refuses
where the DECISION of `b` leaves such a mark. A law that follows the state from block to block wants
to know which decisions can hand on a marked state.
`guardMark` wraps the decision alone. A block's lists of claims, and what it does after the
batching, are not wrapped. The lists are run inside the batching's decision, which is wrapped. What
is done after the batching is run by a block of the driver's own, which is not: it is one of the two
exceptions of `flat_no_mark`.
  `Marked b`      `b` is `guardMark b₀` for some `b₀`, under some name
  `NoMarkOut b`   where the decision of `b` returns a state, that state bears no mark
  `guardMark_yes`  an accept of `guardMark b` is an accept of `b` with the same state after it,
                  which bears no mark; `guardMark_claims`, `_after`, `_rounds`, `_place`: nothing
                  else of `b` turns; `guardMark_decides`: so it keeps every relation that `b`
                  keeps
  `idleFront_yes`  the first sub-protocol where no lot supplies one hands the state on as it is
  `Marked.noMark`   the first gives the second
  `NoMarkOut.of_decide`, `.guarded`, `.andThen`   the second is kept by whatever keeps the decision
                  (another name, place or test on the plan; `Block.retype`), by the driver's guard
                  (Johnson/Desc/SeatGuard.lean), and by `p.andThen n q` where `q` has it
  `parts_frames_marked`, `parts_road_marked`, `parts_base_marked`   the three lists of `partsAt`:
                  the blocks of the kind `frame`; the batching as a function; the blocks at the
                  places
  `link_no_mark`, `firstChain_no_mark`   the driver's segment and chain, over a record whose blocks
                  have the property
  `chainBy_opened`, `chainBy_frames`   what `chainBy` hands `chainC`
  `flat_no_mark`  the proof file's first chain: every block of its flat list has the property, but
                  for the chain's first block and, in each segment, the block after the batching
  `roles_of_whole`, `descPure_no_mark`   the premise of `flat_no_mark`, from the two tests of
                  `onlineDescriptionFromPublicPart`; so the law holds from `onlineDescription`'s value alone
General in the seat `T` and in `B`. `flat_no_mark` has a premise: for every segment a block of the
kind `frame` is supplied for its start and for its end. Where none is, `chainBy` hands the state on.

-/
import Johnson.Desc.ProofFile.Law.OrderStated
import Johnson.Desc.ProofFile.Law.FrameRoles
import Johnson.Desc.First.Driver.PlacesLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Law
open VerifiableInference.Desc (Block Chain Link Place KindName seatSame roundlessBlock)
open VerifiableInference.Desc.First

/-- `guardMark b₀`, under some name. -/
def Marked (b : Block S Cl) : Prop :=
  ∃ (b₀ : Block S Cl) (n : String), b = { guardMark b₀ with name := n }

/-- Where the decision returns a state, that state bears no mark. -/
def NoMarkOut {γ : Type} (b : Block S γ) : Prop :=
  ∀ s rs gs t, b.decide s rs gs = .ok t → t.failed = none

theorem guardMark_noMark (b₀ : Block S Cl) : NoMarkOut (guardMark b₀) := by
  intro s rs gs t h
  obtain ⟨u, _, hu⟩ := exBind_ok (show ((b₀.decide s rs gs).bind fun t =>
    match t.failed with
    | none => Except.ok t
    | some m => .error ("marked: " ++ m)) = .ok t from h)
  split at hu
  · rename_i hf
    cases hu
    exact hf
  · cases hu

/-- **What an accept of `guardMark b` is**: an accept of `b`, with the same state after it, and that
state bears no mark. So whatever holds of every accept of `b`'s decision holds of every accept of
`guardMark b`'s: a relation between the two states, an invariant, with or without a condition on the
rounds. -/
theorem guardMark_yes {b : Block S Cl} {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} :
    (guardMark b).decide s rs gs = .ok t ↔ b.decide s rs gs = .ok t ∧ t.failed = none := by
  constructor
  · intro h
    obtain ⟨u, hu, hm⟩ := exBind_ok (show ((b.decide s rs gs).bind fun t =>
      match t.failed with
      | none => Except.ok t
      | some m => .error ("marked: " ++ m)) = .ok t from h)
    split at hm
    · rename_i hf
      have e : u = t := Except.ok.inj hm
      rw [← e]
      exact ⟨hu, hf⟩
    · cases hm
  · rintro ⟨h1, h2⟩
    show ((b.decide s rs gs).bind fun t =>
      match t.failed with
      | none => Except.ok t
      | some m => .error ("marked: " ++ m)) = .ok t
    rw [h1]
    show (match t.failed with
      | none => Except.ok t
      | some m => .error ("marked: " ++ m)) = .ok t
    rw [h2]

/-- `guardMark` turns the decision alone. -/
theorem guardMark_claims (b : Block S Cl) : (guardMark b).claims = b.claims := rfl

theorem guardMark_after (b : Block S Cl) : (guardMark b).after = b.after := rfl

theorem guardMark_rounds (b : Block S Cl) : (guardMark b).rounds = b.rounds := rfl

theorem guardMark_place (b : Block S Cl) : (guardMark b).place = b.place := rfl

/-- In the form of `Decides` (Johnson/Desc/FoldKeeps.lean), written out: a relation that every
accept of `b`'s decision keeps is kept by every accept of `guardMark b`'s, under any name. -/
theorem guardMark_decides {R : S → S → Prop} {b : Block S Cl} (n : String)
    (h : ∀ s rs gs t, b.decide s rs gs = .ok t → R s t) :
    ∀ s rs gs t, ({ guardMark b with name := n } : Block S Cl).decide s rs gs = .ok t → R s t :=
  fun s rs gs t ht => h s rs gs t (guardMark_yes.1 ht).1

/-- The first sub-protocol of the chain where no lot supplies one: it accepts, and hands the state
on as it is. -/
theorem idleFront_yes {s t : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} :
    (idleFront : Block S Cl).decide s rs gs = .ok t ↔ t = s :=
  ⟨fun h => (Except.ok.inj h).symm, fun h => by rw [h]; rfl⟩

theorem NoMarkOut.of_decide {γ γ' : Type} {b : Block S γ} {b' : Block S γ'}
    (e : b'.decide = b.decide) (h : NoMarkOut b) : NoMarkOut b' :=
  fun s rs gs t ht => h s rs gs t (e ▸ ht)

theorem NoMarkOut.at_place {γ : Type} {b : Block S γ} (a : Place) (h : NoMarkOut b) :
    NoMarkOut { b with place := a } := h.of_decide rfl

theorem NoMarkOut.plan {γ : Type} {b : Block S γ} (ok : Bool) (h : NoMarkOut b) :
    NoMarkOut { b with planOk := ok } := h.of_decide rfl

theorem Marked.noMark {b : Block S Cl} (h : Marked b) : NoMarkOut b := by
  obtain ⟨b₀, n, rfl⟩ := h
  exact (guardMark_noMark b₀).of_decide rfl

theorem seatSame_ok {same : S → S → Bool} {s u t : S} (h : seatSame same s u = .ok t) : t = u := by
  unfold seatSame at h
  split at h
  · exact (Except.ok.inj h).symm
  · cases h

theorem NoMarkOut.guarded {γ : Type} {b : Block S γ} (same : S → S → Bool) (but : Place → Bool)
    (h : NoMarkOut b) : NoMarkOut (b.guarded same but) := by
  intro s rs gs t ht
  have ht' : (if but b.place then b.decide s rs gs
      else (b.decide s rs gs).bind (seatSame same s)) = .ok t := ht
  split at ht'
  · exact h s rs gs t ht'
  · obtain ⟨u, hu, hs⟩ := exBind_ok ht'
    rw [seatSame_ok hs]
    exact h s rs gs u hu

theorem NoMarkOut.andThen {γ : Type} (n : String) (p : Block S γ) {q : Block S γ}
    (h : NoMarkOut q) : NoMarkOut (p.andThen n q) := by
  intro s rs gs t ht
  obtain ⟨u, _, hq⟩ := exBind_ok (show
    ((p.decide s (rs.take p.rounds.length) (gs.take p.openings)).bind fun s' =>
      q.decide s' (rs.drop p.rounds.length) (gs.drop p.openings)) = .ok t from ht)
  exact h _ _ _ _ hq

/-! ### The three lists of `partsAt` -/

theorem parts_frames_marked (T : PureSeat) (B : PureBase) :
    ∀ x ∈ (partsAt T B).frames, ∃ b₀, x.2 = guardMark b₀ := by
  intro x hx
  unfold partsAt at hx
  dsimp only at hx
  obtain ⟨y, _, hy⟩ := List.mem_flatMap.1 hx
  split at hy
  · exact (List.not_mem_nil hy).elim
  · obtain ⟨b, _, hb⟩ := List.mem_filterMap.1 hy
    split at hb
    · cases hb
    · cases hb
    · cases hb
      exact ⟨b, rfl⟩

theorem parts_road_marked (T : PureSeat) (B : PureBase) {a : Place}
    {mk : Gatherer → Block S Cl} (h : (partsAt T B).road.batch a = some mk) (g : Gatherer) :
    Marked (mk g) := by
  unfold partsAt at h
  dsimp only at h
  obtain ⟨mk0, _, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨mk0 g, _, rfl⟩

theorem mapM_ok_mem {α β : Type} (f : α → Except String β) :
    ∀ (l : List α) (out : List β), l.mapM f = .ok out → ∀ y ∈ out, ∃ x ∈ l, f x = .ok y
  | [], out, h, y, hy => by
    rw [List.mapM_nil] at h
    cases h
    exact (List.not_mem_nil hy).elim
  | a :: l, out, h, y, hy => by
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := bind_ok h
    obtain ⟨bs, hbs, h⟩ := bind_ok h
    cases h
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨a, List.mem_cons_self, hb⟩
    · obtain ⟨x, hx, e⟩ := mapM_ok_mem f l bs hbs y hy
      exact ⟨x, List.mem_cons_of_mem _ hx, e⟩

theorem parts_places_marked (T : PureSeat) (B : PureBase) :
    ∀ x ∈ (partsAt T B).places, ∀ b, x.2 = .ok b → Marked b := by
  intro x hx b hb
  have hr := fun (a : Place) (mk : Gatherer → Block S Cl) =>
    parts_road_marked T B (a := a) (mk := mk)
  unfold partsAt at hx hr
  dsimp only at hx hr
  obtain ⟨p, _, rfl⟩ := List.mem_map.1 hx
  dsimp only at hb
  split at hb
  · obtain ⟨mk, hmk, e⟩ := Option.map_eq_some_iff.1 (by assumption)
    rw [← Except.ok.inj hb, ← e]
    exact hr _ mk hmk _
  · exact ⟨_, _, (Except.ok.inj hb).symm⟩
  · split at hb <;> cases hb

/-- Every block at a place stands behind `guardMark`. `base` is the list that `chainBy` is handed.
-/
theorem parts_base_marked {T : PureSeat} {B : PureBase} {base : List (Block S Cl)}
    (h : (partsAt T B).base = .ok base) : ∀ b ∈ base, Marked b := by
  intro b hb
  obtain ⟨x, hx, e⟩ := mapM_ok_mem _ _ _ h b hb
  exact parts_places_marked T B x hx b e

/-! ### The driver's chain -/

/-- The block that `Link.blocksInOrder` lays after the batching. -/
def behindOf (L : Link S Cl) : Block S Cl :=
  roundlessBlock (L.name ++ ": behind the batching") L.chain (some L.number) (L.hear.length + 2)
    L.runBehind

/-- One segment of the driver's, behind its guard: every block of its flat list hands on no mark,
but for the block after the batching. `hB`, `hM`: what the record gives has the property; `hL`,
`hC`: so has what it does where this segment starts and ends. -/
theorem link_no_mark {H : Blocks S Cl} {l : Nat} {sub : ModelPart} {L0 : Link S Cl}
    (h : linkAt H l sub = some L0) (same : S → S → Bool) (but : Place → Bool)
    (hB : ∀ a b, H.block a = some b → NoMarkOut b)
    (hM : ∀ a mk g, H.batch a = some mk → NoMarkOut (mk g))
    (hL : ∀ s t, H.lay l s = .ok t → t.failed = none)
    (hC : ∀ s t, H.clear l s = .ok t → t.failed = none) :
    ∀ E ∈ (L0.guarded same but).blocksInOrder, NoMarkOut E ∨ E = behindOf (L0.guarded same but) := by
  unfold linkAt at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  obtain ⟨hear, hh, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨batch, hb, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨close, hc, h⟩ := Option.bind_eq_some_iff.1 h
  cases h
  have atB : ∀ (as : List Place) (ys : List (Block S Cl)), as.mapM (blockAt H) = some ys →
      ∀ y ∈ ys, NoMarkOut (y.guarded same but) := by
    intro as ys hys y hy
    obtain ⟨a, _, e⟩ := mem_of_mapM (blockAt H) as ys hys y hy
    unfold blockAt at e
    obtain ⟨b, hb', rfl⟩ := Option.map_eq_some_iff.1 e
    exact ((hB a b hb').at_place a).guarded same but
  intro E hE
  unfold Link.blocksInOrder Link.guarded at hE
  dsimp only at hE
  rcases List.mem_append.1 hE with hE | hE
  · rcases List.mem_append.1 hE with hE | hE
    · rcases List.mem_append.1 hE with hE | hE
      · rcases List.mem_cons.1 hE with rfl | hE
        · refine .inl fun s rs gs t ht => ?_
          obtain ⟨u, hu, hs⟩ := exBind_ok
            (show ((H.lay l s).bind (seatSame same s)) = .ok t from ht)
          rw [seatSame_ok hs]
          exact hL s u hu
        · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hE
          exact .inl (atB _ _ hh y hy)
      · rcases List.mem_cons.1 hE with rfl | hE
        · exact .inl (((hM _ batch _ hb).at_place _).guarded same but)
        · exact .inr (List.mem_singleton.1 hE)
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hE
      exact .inl (atB _ _ hc y hy)
  · obtain rfl := List.mem_singleton.1 hE
    refine .inl fun s rs gs t ht => ?_
    obtain ⟨u, hu, hs⟩ := exBind_ok
      (show ((H.clear l s).bind (seatSame same s)) = .ok t from ht)
    rw [seatSame_ok hs]
    exact hC s u hu

/-- The driver's first chain: every block of its flat list hands on no mark, but for the chain's
first block and, in each segment, the block after the batching. -/
theorem firstChain_no_mark {H : Blocks S Cl} {links : List ModelPart} {several : Bool} {c : Chain S Cl}
    (h : firstChain H links several = some c)
    (hB : ∀ a b, H.block a = some b → NoMarkOut b)
    (hM : ∀ a mk g, H.batch a = some mk → NoMarkOut (mk g))
    (hL : ∀ l, l < links.length → ∀ s t, H.lay l s = .ok t → t.failed = none)
    (hC : ∀ l, l < links.length → ∀ s t, H.clear l s = .ok t → t.failed = none)
    (hZ : NoMarkOut H.last) :
    ∀ E ∈ c.blocksInOrder, NoMarkOut E ∨
      E = { c.first with planOk := c.first.planOk && c.first.hasNoClaimsAndNothingAfter } ∨
      ∃ Lk ∈ c.links, E = behindOf Lk := by
  unfold firstChain at h
  obtain ⟨c0, h0, rfl⟩ := Option.map_eq_some_iff.1 h
  unfold firstChainWithoutReplyGuard at h0
  simp only [Option.bind_eq_bind, Option.pure_def] at h0
  split at h0
  · cases h0
  obtain ⟨_, _, h0⟩ := Option.bind_eq_some_iff.1 h0
  obtain ⟨ls, hl, h0⟩ := Option.bind_eq_some_iff.1 h0
  obtain ⟨back, hbk, h0⟩ := Option.bind_eq_some_iff.1 h0
  cases h0
  intro E hE
  unfold Chain.blocksInOrder Chain.guarded at hE
  dsimp only at hE
  rcases List.mem_append.1 hE with hE | hE
  · rcases List.mem_append.1 hE with hE | hE
    · rcases List.mem_append.1 hE with hE | hE
      · rcases List.mem_cons.1 hE with rfl | hE
        · exact .inr (.inl rfl)
        · exact (List.not_mem_nil hE).elim
      · obtain ⟨Lg, hLg, hE⟩ := List.mem_flatMap.1 hE
        obtain ⟨L0, hL0, rfl⟩ := List.mem_map.1 hLg
        obtain ⟨x, hx, e⟩ := mem_of_mapM (fun x : ModelPart × Nat => linkAt H x.2 x.1) _ _ hl L0 hL0
        obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.1 (List.mem_zipIdx_iff_getElem?.1 hx)
        rcases link_no_mark e H.same hearsReply hB hM (hL x.2 hlt) (hC x.2 hlt) E hE with h1 | h1
        · exact .inl h1
        · exact .inr (.inr ⟨_, hLg, h1⟩)
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hE
      obtain ⟨y0, hy0, rfl⟩ := List.mem_map.1 hy
      obtain ⟨a, _, e⟩ := mem_of_mapM (blockAt H) _ _ hbk y0 hy0
      unfold blockAt at e
      obtain ⟨b, hb', rfl⟩ := Option.map_eq_some_iff.1 e
      exact .inl ((((hB a b hb').at_place a).guarded H.same hearsReply).plan _)
  · obtain rfl := List.mem_singleton.1 hE
    exact .inl (((hZ.at_place _).guarded H.same hearsReply).plan _)

/-! ### The proof file's first chain -/

/-- `chainBy`, opened: what it hands `chainC`. -/
theorem chainBy_opened {Z : Pub} {base : List (Block S Cl)} {fr : List (FrameRole × Block S Cl)}
    {road : Gather S Cl} {c : Chain S Cl} (h : chainBy Z base fr road = .ok c) :
    ∃ (join : Block S Cl → Block S Cl) (Fr : Frames S Cl),
      chainC (base.map join) (subsOf Z) Fr = .ok c ∧
      (∀ b, join b = b ∨
        ∃ x ∈ fr, join b = b.andThen b.name (x.2.guarded road.same fun _ => false)) ∧
      Fr.batch = road.batch ∧
      (∀ l t y, (fr.find? fun x => x.1 == .lay l) = some y → Fr.lay l t = y.2.decide t [] []) ∧
      (∀ l t y, (fr.find? fun x => x.1 == .clear l) = some y →
        Fr.clear l t = y.2.decide t [] []) := by
  unfold chainBy at h
  try dsimp only at h
  refine ⟨_, _, h, fun b => ?_, rfl, fun l t y hy => ?_, fun l t y hy => ?_⟩
  · try dsimp only
    split
    · rename_i x hx
      exact .inr ⟨x, List.mem_of_find?_eq_some hx, rfl⟩
    · exact .inl rfl
  · try dsimp only
    rw [hy]
    try rfl
  · try dsimp only
    rw [hy]
    try rfl

/-- What `chainBy` lays where a segment starts and ends, and in front of the chain, in both cases of
each look-up: the decision of the sub-protocol of that role, on no round; or the state as it is. -/
theorem chainBy_frames {Z : Pub} {base : List (Block S Cl)} {fr : List (FrameRole × Block S Cl)}
    {road : Gather S Cl} {c : Chain S Cl} (h : chainBy Z base fr road = .ok c) :
    ∃ (join : Block S Cl → Block S Cl) (Fr : Frames S Cl),
      chainC (base.map join) (subsOf Z) Fr = .ok c ∧
      (∀ l t, (fr.find? fun x => x.1 == .lay l) = none → Fr.lay l t = .ok t) ∧
      (∀ l t, (fr.find? fun x => x.1 == .clear l) = none → Fr.clear l t = .ok t) ∧
      ((fr.find? fun x => x.1 == .front) = none → Fr.first = idleFront) ∧
      (∀ y, (fr.find? fun x => x.1 == .front) = some y →
        Fr.first = { y.2 with name := frontName }) := by
  unfold chainBy at h
  try dsimp only at h
  refine ⟨_, _, h, fun l t hy => ?_, fun l t hy => ?_, fun hy => ?_, fun y hy => ?_⟩ <;>
    (try dsimp only) <;> rw [hy] <;> try rfl

/-- Where a block of the role `r` is in the list, the look-up by that role finds one. -/
theorem find_role {fr : List (FrameRole × Block S Cl)} {r : FrameRole} (hr : ∃ x ∈ fr, x.1 = r) :
    ∃ y ∈ fr, (fr.find? fun x => x.1 == r) = some y := by
  cases hf : fr.find? fun x => x.1 == r with
  | none =>
    obtain ⟨x, hx, rfl⟩ := hr
    exact absurd (role_beq_self x.1) (List.find?_eq_none.1 hf x hx)
  | some y => exact ⟨y, List.mem_of_find?_eq_some hf, rfl⟩

/-- **Every block of the proof file's first chain hands on no mark**, but for the chain's first
block and, in each segment, the block after the batching. `hr`: for every segment of the list a
block of the kind `frame` is supplied for its start and one for its end. -/
theorem flat_no_mark {Z : Pub} {T : PureSeat} {B : PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} (hb : (partsAt T B).base = .ok base)
    (hc : chainBy Z base (partsAt T B).frames (partsAt T B).road = .ok c)
    (hr : ∀ l, l < (subsOf Z).length →
      (∃ x ∈ (partsAt T B).frames, x.1 = .lay l) ∧ ∃ x ∈ (partsAt T B).frames, x.1 = .clear l) :
    ∀ E ∈ c.blocksInOrder, NoMarkOut E ∨
      E = { c.first with planOk := c.first.planOk && c.first.hasNoClaimsAndNothingAfter } ∨
      ∃ Lk ∈ c.links, E = behindOf Lk := by
  obtain ⟨join, Fr, hC, hj, eb, el, ec⟩ := chainBy_opened hc
  obtain ⟨z, hz, hf⟩ := chainC_first hC
  have hfr : ∀ x ∈ (partsAt T B).frames, NoMarkOut x.2 := by
    intro x hx
    obtain ⟨b₀, e⟩ := parts_frames_marked T B x hx
    rw [e]
    exact guardMark_noMark b₀
  have hjoin : ∀ b ∈ base.map join, NoMarkOut b := by
    intro b hbm
    obtain ⟨b', hb', rfl⟩ := List.mem_map.1 hbm
    rcases hj b' with e | ⟨x, hx, e⟩
    · rw [e]
      exact (parts_base_marked hb b' hb').noMark
    · rw [e]
      exact NoMarkOut.andThen _ _ ((hfr x hx).guarded _ _)
  have hfind : ∀ a b, ((base.map join).dropLast.find? fun b => b.place == a) = some b →
      NoMarkOut b := fun a b h =>
    hjoin b (List.dropLast_subset _ (List.mem_of_find?_eq_some h))
  refine firstChain_no_mark hf hfind ?_ ?_ ?_ (hjoin z (List.mem_of_getLast? hz))
  · intro a mk g hm
    have hm' : (Fr.batch a <|>
        ((base.map join).dropLast.find? fun b => b.place == a).map fun b _ => b) = some mk := hm
    rw [eb] at hm'
    cases hra : (partsAt T B).road.batch a with
    | some mk' =>
      rw [hra] at hm'
      obtain rfl : mk' = mk := Option.some.inj hm'
      exact (parts_road_marked T B hra g).noMark
    | none =>
      rw [hra] at hm'
      obtain ⟨b, hb', rfl⟩ := Option.map_eq_some_iff.1
        (show (((base.map join).dropLast.find? fun b => b.place == a).map fun b _ => b) =
          some mk from hm')
      exact hfind a b hb'
  · intro l hl s t h
    obtain ⟨y, hy, e⟩ := find_role (hr l hl).1
    exact hfr y hy s [] [] t ((el l s y e).symm.trans h)
  · intro l hl s t h
    obtain ⟨y, hy, e⟩ := find_role (hr l hl).2
    exact hfr y hy s [] [] t ((ec l s y e).symm.trans h)

/-! ### The premise on the two roles, from the two tests of `onlineDescriptionFromPublicPart` -/

/-- Where `partsAt` has a sub-protocol at a place of its list: it bears that place, or it is made by
a lot's function for the batching at that place, at the gatherer that gathers nothing. -/
theorem parts_places_at (T : PureSeat) (B : PureBase) :
    ∀ x ∈ (partsAt T B).places, ∀ b, x.2 = .ok b → x.1 ∈ B.spots ∧
      ((∃ L ∈ T.lots, ∃ mk, L.batch B.G₀ x.1.place = some mk ∧
          b.place = (mk fun s => .ok ([], s)).place) ∨ b.place = x.1.place) := by
  intro x hx b hb
  unfold partsAt at hx
  dsimp only at hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
  refine ⟨hp, ?_⟩
  dsimp only at hb ⊢
  split at hb
  · obtain ⟨mk', h1, e1⟩ := Option.map_eq_some_iff.1 (by assumption)
    obtain ⟨mk, h2, rfl⟩ := Option.map_eq_some_iff.1 h1
    obtain ⟨L, hL, h3⟩ := List.exists_of_findSome?_eq_some h2
    refine .inl ⟨L, (List.mem_filter.1 hL).1, mk, h3, ?_⟩
    rw [← Except.ok.inj hb, ← e1]
    rfl
  · have hy := List.mem_of_find?_eq_some (by assumption)
    obtain ⟨z, _, hz2⟩ := List.mem_filterMap.1 hy
    obtain ⟨bL, hbL, e2⟩ := Option.map_eq_some_iff.1 hz2
    refine .inr ?_
    rw [← Except.ok.inj hb, ← e2]
    have hbp : bL.place = p.place :=
      eq_of_beq (List.find?_some (p := fun b : Block S Cl => b.place == p.place) hbL)
    exact hbp
  · split at hb <;> cases hb

theorem ite_nil {c : Bool} {s : String} (h : (if c = true then ([] : List String) else [s]) = []) :
    c = true := by
  cases c
  · simp at h
  · rfl

theorem ite_nil' {c : Bool} {s : String}
    (h : (if c = true then [s] else ([] : List String)) = []) : c = false := by
  cases c
  · rfl
  · simp at h

/-- Where `faultsAt` finds nothing: what a lot's function for the batching makes at a place of the
list, at the gatherer that gathers nothing, bears that place. -/
theorem face_place {T : PureSeat} {B : PureBase} (hf : faultsAt T B = []) {p : Spot}
    (hp : p ∈ B.spots) {L : Lot} (hL : L ∈ T.lots) {mk : Gatherer → Block S Cl}
    (hmk : L.batch B.G₀ p.place = some mk) : (mk fun s => .ok ([], s)).place = p.place := by
  unfold faultsAt at hf
  dsimp only at hf
  have hAt := (List.append_eq_nil_iff.1 (List.append_eq_nil_iff.1
    (List.append_eq_nil_iff.1 hf).1).1).2
  have h1 := List.flatMap_eq_nil_iff.1 hAt p hp
  have hg : L ∈ T.lots.filter fun L => (L.batch B.G₀ p.place).isSome :=
    List.mem_filter.2 ⟨hL, by rw [hmk]; rfl⟩
  split at h1
  · rename_i he
    rw [List.isEmpty_iff.1 he] at hg
    exact (List.not_mem_nil hg).elim
  · have h2 := (List.append_eq_nil_iff.1 (List.append_eq_nil_iff.1 (List.append_eq_nil_iff.1
      (List.append_eq_nil_iff.1 h1).1).1).1).2
    have h3 := List.any_eq_false.1 (ite_nil' h2) L hg
    rw [hmk] at h3
    by_contra hne
    exact h3 (bne_iff_ne.2 hne)

/-- Every sub-protocol of `base` stands at a place of the list of places. -/
theorem base_place {T : PureSeat} {B : PureBase} {base : List (Block S Cl)}
    (hf : faultsAt T B = []) (hb : (partsAt T B).base = .ok base) :
    ∀ b ∈ base, ∃ p ∈ B.spots, b.place = p.place := by
  intro b hbm
  obtain ⟨x, hx, e⟩ := mapM_ok_mem _ _ _ hb b hbm
  obtain ⟨hp, h⟩ := parts_places_at T B x hx b e
  rcases h with ⟨L, hL, mk, hmk, e1⟩ | e1
  · exact ⟨x.1, hp, e1.trans (face_place hf hp hL hmk)⟩
  · exact ⟨x.1, hp, e1⟩

theorem mapM_all_some {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (r : List β), l.mapM f = some r → ∀ a ∈ l, ∃ b, f a = some b
  | [], _, _, _, ha => (List.not_mem_nil ha).elim
  | x :: l, r, h, a, ha => by
    obtain ⟨b, bs, hb, hbs, _⟩ := mapM_cons_some f x l r h
    rcases List.mem_cons.1 ha with rfl | ha
    · exact ⟨b, hb⟩
    · exact mapM_all_some f l bs hbs a ha

/-- Where the driver returns a chain, its structure `H` has a sub-protocol at the first place of
every segment of the list. -/
theorem firstChain_block_at {H : Blocks S Cl} {links : List ModelPart} {several : Bool} {c : Chain S Cl}
    (h : firstChain H links several = some c) {l : Nat} {sub : ModelPart} (hl : links[l]? = some sub) :
    ∃ k b, H.block { chain := 1, link := some l, piece := 1, kind := k } = some b := by
  unfold firstChain at h
  obtain ⟨c0, h0, _⟩ := Option.map_eq_some_iff.1 h
  unfold firstChainWithoutReplyGuard at h0
  simp only [Option.bind_eq_bind, Option.pure_def] at h0
  split at h0
  · cases h0
  obtain ⟨_, _, h0⟩ := Option.bind_eq_some_iff.1 h0
  obtain ⟨ls, hls, _⟩ := Option.bind_eq_some_iff.1 h0
  obtain ⟨L0, e⟩ := mapM_all_some (fun x : ModelPart × Nat => linkAt H x.2 x.1) _ _ hls (sub, l)
    (List.mem_zipIdx_iff_getElem?.2 hl)
  have e' : linkAt H l sub = some L0 := e
  unfold linkAt at e'
  simp only [Option.bind_eq_bind, Option.pure_def] at e'
  obtain ⟨hear, hh, _⟩ := Option.bind_eq_some_iff.1 e'
  have hk : ∃ k, ({ chain := 1, link := some l, piece := 1, kind := k } : Place) ∈
      addresses (some l) (kindsBeforeBatching sub (l == 0)) := by
    generalize (l == 0) = f
    cases sub <;> cases f <;> exact ⟨_, List.mem_cons_self⟩
  obtain ⟨k, hk⟩ := hk
  obtain ⟨y, hy⟩ := mapM_all_some (blockAt H) _ _ hh _ hk
  unfold blockAt at hy
  obtain ⟨b, hb, _⟩ := Option.map_eq_some_iff.1 hy
  exact ⟨k, b, hb⟩

/-- Every segment of the list of the segments' sorts has a place in the list of places. -/
theorem spot_of_link {Z : Pub} {T : PureSeat} {B : PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} (hf : faultsAt T B = []) (hb : (partsAt T B).base = .ok base)
    (hc : chainBy Z base (partsAt T B).frames (partsAt T B).road = .ok c) {l : Nat}
    (hl : l < (subsOf Z).length) : ∃ p ∈ B.spots, p.place.link = some l := by
  obtain ⟨join, Fr, hC, _, hj⟩ := chainBy_hands hc
  obtain ⟨z, _, hfc⟩ := chainC_first hC
  obtain ⟨k, b, hbk⟩ := firstChain_block_at hfc (List.getElem?_eq_getElem hl)
  have hfind : ((base.map join).dropLast.find? fun b =>
      b.place == { chain := 1, link := some l, piece := 1, kind := k }) = some b := hbk
  have hp : b.place = { chain := 1, link := some l, piece := 1, kind := k } :=
    eq_of_beq (List.find?_some (p := fun b : Block S Cl =>
      b.place == { chain := 1, link := some l, piece := 1, kind := k }) hfind)
  obtain ⟨b', hb', rfl⟩ :=
    List.mem_map.1 (List.dropLast_subset _ (List.mem_of_find?_eq_some hfind))
  have hpl : (join b').place = b'.place := by
    rcases hj b' with e | ⟨_, _, _, _, _, e⟩
    · rw [e]
    · rw [e]
      rfl
  obtain ⟨p, hp', e⟩ := base_place hf hb b' hb'
  exact ⟨p, hp', by rw [← e, ← hpl, hp]⟩

theorem contains_role : ∀ (rs : List FrameRole) (r : FrameRole), rs.contains r = true → r ∈ rs
  | [], _, h => by simp at h
  | a :: rs, r, h => by
    rw [List.contains_cons] at h
    rcases Bool.or_eq_true_iff.1 h with h | h
    · rw [role_eq_of_beq h]
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (contains_role rs r h)

/-- **The premise of `flat_no_mark`, from the two tests of `onlineDescriptionFromPublicPart`**: where `faultsAt` and
`lackingAt` find nothing, a sub-protocol of the kind `frame` is supplied for the start and for the
end of every segment of the list of the segments' sorts. -/
theorem roles_of_whole {Z : Pub} {T : PureSeat} {B : PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} (hf : faultsAt T B = []) (hw : lackingAt T (partsAt T B) = [])
    (hb : (partsAt T B).base = .ok base)
    (hc : chainBy Z base (partsAt T B).frames (partsAt T B).road = .ok c) :
    ∀ l, l < (subsOf Z).length →
      (∃ x ∈ (partsAt T B).frames, x.1 = .lay l) ∧ ∃ x ∈ (partsAt T B).frames, x.1 = .clear l := by
  intro l hl
  obtain ⟨p, hp, e⟩ := spot_of_link hf hb hc hl
  have hpl : ∃ x ∈ (partsAt T B).places, x.1 = p := by
    unfold partsAt
    dsimp only
    exact ⟨_, List.mem_map.2 ⟨p, hp, rfl⟩, rfl⟩
  obtain ⟨x, hx, rfl⟩ := hpl
  have hmem : l ∈ ((partsAt T B).places.filterMap fun x => x.1.place.link).eraseDups :=
    List.mem_eraseDups.2 (List.mem_filterMap.2 ⟨x, hx, e⟩)
  unfold lackingAt at hw
  dsimp only at hw
  have hfr := (List.append_eq_nil_iff.1 (List.append_eq_nil_iff.1
    (List.append_eq_nil_iff.1 hw).1).1).2
  have h1 := List.flatMap_eq_nil_iff.1 hfr l hmem
  have h3 := (List.append_eq_nil_iff.1 (List.append_eq_nil_iff.1
    (List.append_eq_nil_iff.1 h1).1).1).1
  have hclear := ite_nil (List.append_eq_nil_iff.1 h3).2
  have hlay := ite_nil (List.append_eq_nil_iff.1 (List.append_eq_nil_iff.1 h3).1).1
  obtain ⟨y, hy, ey⟩ := List.mem_map.1 (contains_role _ _ hlay)
  obtain ⟨y', hy', ey'⟩ := List.mem_map.1 (contains_role _ _ hclear)
  exact ⟨⟨y, hy, ey⟩, ⟨y', hy', ey'⟩⟩

/-- **From `onlineDescription`'s value alone**: every sub-protocol of its first chain hands on no mark by its
decision, but for the chain's first one and, in each segment, the one after the batching. -/
theorem descPure_no_mark {o : SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {F : VerifiableInference.Desc.FileDescription Inst} (h : onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : Pub) (A : SharedSeat) (B : SecondSeat) (c : Chain S Cl),
      pureRoad.pub o pol lay KL = .ok Z ∧
      F = fileDescBy o pureRoad.links Z A B (fun s => s) (startS Z) c ∧
      ∀ E ∈ c.blocksInOrder, NoMarkOut E ∨
        E = { c.first with planOk := c.first.planOk && c.first.hasNoClaimsAndNothingAfter } ∨
        ∃ Lk ∈ c.links, E = behindOf Lk := by
  obtain ⟨Z, Bs, base, c, A, B, hZ, _, hf, hw, hb, hc, _, _, hF⟩ := descPure_parts h
  exact ⟨Z, A, B, c, hZ, hF, flat_no_mark hb hc (roles_of_whole hf hw hb hc)⟩

end ProofFile.Law

#print axioms ProofFile.Law.guardMark_yes
#print axioms ProofFile.Law.idleFront_yes
#print axioms ProofFile.Law.chainBy_frames
#print axioms ProofFile.Law.roles_of_whole
#print axioms ProofFile.Law.descPure_no_mark
#print axioms ProofFile.Law.firstChain_no_mark
#print axioms ProofFile.Law.flat_no_mark
#print axioms ProofFile.Law.Marked.noMark
#print axioms ProofFile.Law.NoMarkOut.guarded
#print axioms ProofFile.Law.NoMarkOut.andThen
#print axioms ProofFile.Law.parts_frames_marked
#print axioms ProofFile.Law.parts_road_marked
#print axioms ProofFile.Law.parts_base_marked
