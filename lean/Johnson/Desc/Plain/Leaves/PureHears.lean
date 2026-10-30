-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Plain/Leaves/PureHears.lean: WHERE `onlineDescriptionFromPublicPart` (Johnson/Desc/ProofFile/OnlineDescriptionFromBlockTables.lean) MAKES THE
PROOF FILE's DESCRIPTION, THAT DESCRIPTION HEARS THE REPLY (`FileDescription.Hears`,
Johnson/Desc/Sound/FoldHeard.lean), at the one seat of the heard reply, `out.reply`.

How. The driver lays its first chain behind a guard on the reply (Johnson/Desc/SeatGuard.lean), and
`chainC` and `chainBy` hand that chain on unturned. So "no later block turns what was heard" is the
guard's own law (`firstChain_flat_leaves`, Johnson/Desc/Sound/GuardAtDriver.lean): NO PREMISE ON ANY
BLOCK. What is left is what the block of the kind K7 lays.
  `sameReply_eq`: a yes of the seat's test gives one reply.
  `chainC_first`: a yes of `chainC` is a yes of the driver's `firstChain` at `fill`.
  `chainBy_leaves`: every block of the flat list stands at a place of the kind K7 or leaves h, for
    every reading h that the road's test `same` keeps.
  `LaysAt h rd b`: if b stands at a place of the kind K7: b lays h as rd of its rounds, and rd reads
    no more than b's rounds (so that what is joined behind b does not turn what rd is shown), and b
    has just one round.
  `chainBy_lays`: every block of the flat list at such a place lays h: what `chainBy` joins behind a
    block is guarded there at every place, so it leaves h.
  `LotsLay`: THE ONE PREMISE ON THE LOTS: `LaysAt` of every block of every lot.
  `parts_lay`, `baseOf_made`: the walk through `partsAt` and `baseOf`. What `onlineDescriptionFromPublicPart`'s yes gives is
    taken from `ProofFile.Law.pureZ_ok` and `pureTail_ok` (ProofFile/Law/PureMade.lean).
  `face_label`: `partsAt` takes a batching's maker's block, at the gatherer that gathers nothing,
    before a lot's, and `fill` finds a block by its own label: so a maker whose block labelled
    itself K7 would stand at K7's address, free of the guard. Where `faultsAt` finds nothing that
    block bears the place at which the maker is given, and that place is of the kind K9.
  `shapeOf_places`, `faultsOf_nil`, **`k7_one`**: where `faultsAt` finds nothing, two blocks of the
    lots that are labelled with the kind K7 are one: each stands at a place of the shape, the
    shape's places are the driver's table's, which holds one place of that kind (OneK7.lean), and at
    a place of the shape stands at most one block.
  `faultsOf_of_faultsAt`, `frames_noRounds`: where `faultsAt` finds nothing, what `chainBy` joins
    behind a place's block has no round: so the joined block has the place's block's rounds.
  THE LAST TEST, BY ITS TEXT (`fileDescBy_fin`, `finAsked_reply`, `asked_of_y`:
    they stand in Johnson/Desc/ProofFile/Law/FileFields.lean, and
    are called from there): its yes holds `S.finAsked` at the asked element; so the end state's
    reply is that element; and that element is the first word of the reply file's bytes.
  `chainBy_has_K7`, `chainBy_count`: a block stands at a place of the kind K7, at just one entry of
    the flat list (HasK7.lean, OneK7.lean).
  **`pure_hears_at`**, **`pure_hears`**: onlineDescriptionFromPublicPart's yes, the seat's test is `sameReply`, and `LotsLay`:
    a member H of `Hears` with H.heard = out.reply, WHOSE CUT IS PINNED: its block stands at a place
    of the kind K7, has just one round, and no block in front of it or behind it stands at that
    kind: so H.pre is the flat list up to the one entry at that kind. `pure_hears_at` hands on what
    the proof knows of the description's parts. The last test's law (`fins`) is concluded from
    `S.finAsked`.
Limits. RULES ON TEXTS, AT THESE TEXTS: `face_label` reads two clauses of `faultsAt` by their places
in its list; `k7_one` reads `faultsOf`'s first and last. THE GUARD IS SCAFFOLDING: it can refuse an
honest file; nothing here is on acceptance. When it is struck, each block owes its own lemma that it
leaves the reply (`firstChain_strike`). `LotsLay` is shown of no seat here. That `onlineDescriptionFromPublicPart` makes
anything is not shown here. No count, no game, no soundness.

-/
import Johnson.Desc.Plain.Leaves.Join
import Johnson.Desc.Plain.Leaves.OneK7
import Johnson.Desc.Sound.GuardAtDriverHoldsR
import Johnson.Desc.ProofFile.Law.PureMade
import Johnson.Desc.ProofFile.Law.FileFields

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

namespace ProofFile
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain FileDescription KindName Place bindOk laysAndThenBehind
  guarded_or)
open VerifiableInference.Desc.First

/-- `bindOk` at any two universes (a lot and a file's description live one higher). -/
theorem bindOkU {ε : Type} {β : Type u} {γ : Type v} {x : Except ε β} {f : β → Except ε γ} {y : γ}
    (h : x.bind f = .ok y) : ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e => exact nomatch h
  | ok a => exact ⟨a, rfl, h⟩

theorem orSay_some {β : Type} {w : String} {x : Option β} {y : β} (h : orSay w x = .ok y) :
    x = some y := by
  cases x with
  | none => exact nomatch h
  | some z => exact congrArg some (Except.ok.inj h)

/-- What a list made entry by entry holds comes from an entry. -/
theorem mem_mapM_ok {β γ : Type} (f : β → Except String γ) : ∀ (l : List β) (ys : List γ),
    l.mapM f = .ok ys → ∀ y ∈ ys, ∃ x ∈ l, f x = .ok y
  | [], ys, h, y, hy => by
    rw [List.mapM_nil] at h
    obtain rfl := Except.ok.inj h
    cases hy
  | a :: l, ys, h, y, hy => by
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := bindOk h
    obtain ⟨bs, hbs, h⟩ := bindOk h
    obtain rfl := Except.ok.inj h
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨a, List.mem_cons_self, hb⟩
    · obtain ⟨x, hx, e⟩ := mem_mapM_ok f l bs hbs y hy
      exact ⟨x, List.mem_cons_of_mem _ hx, e⟩

/-- A yes of the seat's test gives one reply. -/
theorem sameReply_eq (t s : S) (h : sameReply t s = true) : s.out.reply = t.out.reply :=
  (eq_of_beq h).symm

variable {σ α : Type}

/-- **A yes of `chainC` is a yes of the driver's first chain.** -/
theorem chainC_first {C : Type} (bs : List (Block σ C)) (links : List ModelPart) (fr : Frames σ C)
    (c : Chain σ C) (hc : chainC bs links fr = .ok c) :
    ∃ z several, bs.getLast? = some z ∧
      firstChain (fill bs.dropLast z fr) links several = some c := by
  unfold chainC at hc
  split at hc
  · exact nomatch hc
  · rename_i z hzl
    dsimp only at hc
    split at hc
    · exact nomatch hc
    · rename_i c' hc'
      split at hc
      · exact nomatch hc
      · obtain rfl := Except.ok.inj hc
        exact ⟨z, _, hzl, hc'⟩

/-- **Every block of the flat list stands at a place of the kind K7 or leaves h.** -/
theorem chainBy_leaves (h : σ → α) (Z : Pub) (base : List (Block σ Cl))
    (fr : List (FrameRole × Block σ Cl)) (road : Gather σ Cl) (c : Chain σ Cl)
    (hc : chainBy Z base fr road = .ok c) (hs : ∀ t s, road.same t s = true → h s = h t) :
    ∀ b ∈ c.blocksInOrder, b.place.kind = .K7 ∨ b.Leaves h := by
  unfold chainBy at hc
  dsimp only at hc
  obtain ⟨z, sv, _, hf⟩ := chainC_first _ _ _ _ hc
  exact firstChain_flat_leaves (hh := h) (fun t s e => hs t s e) hf

/-- A block of the flat list stands at a place of the kind K7. -/
theorem chainBy_has_K7 (Z : Pub) (base : List (Block σ Cl)) (fr : List (FrameRole × Block σ Cl))
    (road : Gather σ Cl) (c : Chain σ Cl) (hc : chainBy Z base fr road = .ok c) :
    ∃ b ∈ c.blocksInOrder, b.place.kind = .K7 := by
  unfold chainBy at hc
  dsimp only at hc
  obtain ⟨z, sv, _, hf⟩ := chainC_first _ _ _ _ hc
  exact firstChain_has_K7 hf

/-- Just one entry of the flat list stands at a place of the kind K7. -/
theorem chainBy_count (Z : Pub) (base : List (Block σ Cl)) (fr : List (FrameRole × Block σ Cl))
    (road : Gather σ Cl) (c : Chain σ Cl) (hc : chainBy Z base fr road = .ok c) :
    c.blocksInOrder.countP (fun b => isK7 b.place) = 1 := by
  unfold chainBy at hc
  dsimp only at hc
  obtain ⟨z, sv, _, hf⟩ := chainC_first _ _ _ _ hc
  exact firstChain_count hf

/-- Of one block, if it stands at a place of the kind K7. -/
def LaysAt {C : Type} (h : σ → α) (rd : List Fmt.RoundView → α) (b : Block σ C) : Prop :=
  b.place.kind = .K7 →
    b.Lays h rd ∧ (∀ rs, rd (rs.take b.rounds.length) = rd rs) ∧ b.rounds.length = 1

/-- **Every block of the flat list at a place of the kind K7 lays h.** -/
theorem chainBy_lays (h : σ → α) (rd : List Fmt.RoundView → α) (Z : Pub) (base : List (Block σ Cl))
    (fr : List (FrameRole × Block σ Cl)) (road : Gather σ Cl) (c : Chain σ Cl)
    (hc : chainBy Z base fr road = .ok c) (hs : ∀ t s, road.same t s = true → h s = h t)
    (hB : ∀ b ∈ base, LaysAt h rd b) (hfr : ∀ x ∈ fr, x.2.rounds = []) :
    ∀ b ∈ c.blocksInOrder, b.place.kind = .K7 → b.Lays h rd ∧ b.rounds.length = 1 := by
  unfold chainBy at hc
  dsimp only at hc
  obtain ⟨z, sv, _, hf⟩ := chainC_first _ _ _ _ hc
  intro b hb hkb
  refine firstChain_flat_laysOne (hh := h) (rd := rd) (n := 1) ?_ hf b hb
    (by unfold hearsReply; rw [hkb]; rfl)
  intro a b₁ e ha
  have hm := List.mem_of_mem_dropLast (List.mem_of_find?_eq_some e)
  have hpl : b₁.place = a := eq_of_beq (by have h' := List.find?_some e; exact h')
  have hk : b₁.place.kind = .K7 := by rw [hpl]; exact ha
  clear e hpl
  obtain ⟨b₀, hb₀, rfl⟩ := List.mem_map.1 hm
  revert hk
  split
  · rename_i x hx
    intro hk
    refine ⟨laysAndThenBehind h rd _ b₀ _ (hB b₀ hb₀ hk).1 ?_ (hB b₀ hb₀ hk).2.1, ?_⟩
    · exact (guarded_or (fun _ => false) x.2 hs).resolve_left (fun e => nomatch e)
    · show (b₀.rounds ++ x.2.rounds).length = 1
      rw [hfr x (List.mem_of_find?_eq_some hx), List.append_nil]
      exact (hB b₀ hb₀ hk).2.2
  · intro hk
    exact ⟨(hB b₀ hb₀ hk).1, (hB b₀ hb₀ hk).2.2⟩

theorem guardMark_lays (h : S → α) (rd : List Fmt.RoundView → α) (b : Block S Cl) (n : String)
    (hb : LaysAt h rd b) : LaysAt h rd { guardMark b with name := n } := by
  intro hp
  refine ⟨fun s rs gs s' hd => ?_, (hb hp).2⟩
  obtain ⟨t, ht, hd⟩ := bindOk (x := b.decide s rs gs) hd
  split at hd
  · rw [← Except.ok.inj hd]
    exact (hb hp).1 s rs gs t ht
  · exact nomatch hd

/-- **The one premise on the lots.** -/
def LotsLay (h : S → α) (rd : List Fmt.RoundView → α) (T : PureSeat) (G₀ : Ground) : Prop :=
  ∀ L ∈ T.lots, ∀ b ∈ L.blocks G₀, LaysAt h rd b

/-- The gatherer that gathers nothing: at it `partsAt` lays a batching's maker's block into the list
of the places' blocks, and `faultsAt` tests that block's label. -/
def noneGathered : Gatherer := fun s => .ok ([], s)

/-- **The parts**: every place's block is as the lots' blocks are. -/
theorem parts_lay (h : S → α) (rd : List Fmt.RoundView → α) (T : PureSeat) (B : PureBase)
    (hall : B.all = T.lots.map fun L => (L, L.blocks B.G₀)) (hl : LotsLay h rd T B.G₀)
    (hface : ∀ p ∈ B.spots, ∀ L ∈ T.lots, ∀ mk, L.batch B.G₀ p.place = some mk →
      (mk noneGathered).place.kind ≠ .K7) :
    ∀ x ∈ (partsAt T B).places, ∀ b, x.2 = .ok b → LaysAt h rd b := by
  intro x hx b hb
  unfold partsAt at hx
  dsimp only at hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
  dsimp only at hb
  split at hb
  · rename_i f hf
    obtain rfl := Except.ok.inj hb
    intro hk
    exfalso
    obtain ⟨mk', hmk', rfl⟩ := Option.map_eq_some_iff.1 hf
    obtain ⟨mk, hmk, rfl⟩ := Option.map_eq_some_iff.1 hmk'
    obtain ⟨L, hL, e⟩ := List.exists_of_findSome?_eq_some hmk
    exact hface p hp L (List.mem_filter.1 hL).1 mk e hk
  · rename_i y _ hy
    obtain rfl := Except.ok.inj hb
    have hy' := List.mem_of_find?_eq_some hy
    obtain ⟨z, hz, e⟩ := List.mem_filterMap.1 hy'
    obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 e
    rw [hall] at hz
    obtain ⟨L, hL, rfl⟩ := List.mem_map.1 hz
    exact guardMark_lays h rd b₀ _ (hl L hL b₀ (List.mem_of_find?_eq_some hb₀))
  · split at hb <;> exact nomatch hb

/-- What `baseOf`'s yes gives. -/
theorem baseOf_made (Z : Pub) (T : PureSeat) (B : PureBase) (h : baseOf Z T = .ok B) :
    blankBy T.links Z = some B.G₀ ∧ (B.all = T.lots.map fun L => (L, L.blocks B.G₀)) ∧
      shapeOf Z = .ok B.shape ∧ ∀ x ∈ B.batchAt, x.2.kind = .K9 := by
  unfold baseOf at h
  obtain ⟨ps, _, h⟩ := bindOkU h
  obtain ⟨sh, hsh, h⟩ := bindOkU h
  obtain ⟨G, hG, h⟩ := bindOkU h
  obtain rfl := Except.ok.inj h
  refine ⟨orSay_some hG, rfl, hsh, fun x hx => ?_⟩
  obtain ⟨y, _, rfl⟩ := List.mem_map.1 hx
  rfl

/-- The shape's places are the driver's table's, at a list of parts that passes the driver's test.
  -/
theorem shapeOf_places (Z : Pub) (sh : List (String × Place)) (h : shapeOf Z = .ok sh) :
    ∃ several, linksOk (subsOf Z) = true ∧ sh.map (·.2) = flatPlacesOf (subsOf Z) several := by
  unfold shapeOf at h
  obtain ⟨spots, _, h⟩ := bindOk h
  obtain ⟨c, hc, h⟩ := bindOk h
  obtain rfl := Except.ok.inj h
  obtain ⟨z, sv, _, hf⟩ := chainC_first _ _ _ _ hc
  refine ⟨sv, firstChain_linksOk hf, ?_⟩
  rw [List.map_map, ← flat_places _ _ _ c hf]
  rfl

/-- What "no fault" gives of the lots' blocks: a block of a kind stands at a place of the shape; at
a place of the shape stands at most one block. -/
theorem faultsOf_nil (shape : List (String × Place)) (own : List (Block S Cl))
    (h : faultsOf shape own = []) :
    (∀ o ∈ own, o.place.kind ≠ KindName.frame → ∃ s ∈ shape, s.2 = o.place) ∧
      ∀ s ∈ shape, (own.filter fun o => o.place == s.2).length ≤ 1 := by
  unfold faultsOf at h
  dsimp only at h
  obtain ⟨h12, h3⟩ := List.append_eq_nil_iff.1 h
  obtain ⟨h1, _⟩ := List.append_eq_nil_iff.1 h12
  refine ⟨fun o ho hk => ?_, fun s hs => ?_⟩
  · have h1' := List.filter_eq_nil_iff.1 (List.map_eq_nil_iff.1 h1) o ho
    have hk' : (o.place.kind != KindName.frame) = true := by simpa using hk
    rw [hk', Bool.true_and] at h1'
    have h2 : (shape.any fun b => b.2 == o.place) = true := by simpa using h1'
    obtain ⟨s, hs, e⟩ := List.any_eq_true.1 h2
    exact ⟨s, hs, eq_of_beq e⟩
  · have h3' := List.filter_eq_nil_iff.1 (List.map_eq_nil_iff.1 h3) s hs
    simpa using h3'

/-- Whatever `faultsAt` appends behind `faultsOf`'s list: a member of the one is a member of the
other. -/
theorem faultsOf_of_faultsAt (T : PureSeat) (B : PureBase) (hf : faultsAt T B = []) :
    faultsOf B.shape (B.all.flatMap fun x => x.2) = [] := by
  refine List.eq_nil_iff_forall_not_mem.2 fun x hx => ?_
  have hm : x ∈ faultsAt T B := by
    unfold faultsAt
    dsimp only
    repeat first
      | exact hx
      | apply List.mem_append_left
  rw [hf] at hm
  cases hm

/-- **Where nothing is wrong with the lots' blocks, a block that `partsAt` takes for a role of the
kind `frame` has no round.** -/
theorem frames_noRounds (T : PureSeat) (B : PureBase) (hf : faultsAt T B = []) :
    ∀ x ∈ (partsAt T B).frames, x.2.rounds = [] := by
  intro x hx
  have hf' := faultsOf_of_faultsAt T B hf
  unfold partsAt at hx
  dsimp only at hx
  obtain ⟨z, hz, hx⟩ := List.mem_flatMap.1 hx
  split at hx
  · cases hx
  obtain ⟨b, hb, e⟩ := List.mem_filterMap.1 hx
  have hown : b ∈ B.all.flatMap fun x => x.2 :=
    List.mem_flatMap.2 ⟨z, hz, (List.mem_filter.1 hb).1⟩
  unfold faultsOf at hf'
  dsimp only at hf'
  obtain ⟨h12, _⟩ := List.append_eq_nil_iff.1 hf'
  obtain ⟨_, h2⟩ := List.append_eq_nil_iff.1 h12
  have hg := List.filterMap_eq_nil_iff.1 h2 (roleOf B.shape b.place, b)
    (List.mem_map.2 ⟨b, List.mem_filter.2 ⟨hown, (List.mem_filter.1 hb).2⟩, rfl⟩)
  dsimp only at hg
  have main : ∀ r : FrameRole, roleOf B.shape b.place = r → (r != FrameRole.common) = true →
      b.rounds = [] := by
    intro r hr hne
    rw [hr] at hg
    split at hg
    · exact nomatch hg
    split at hg
    · exact nomatch hg
    rename_i _ h2'
    cases hre : b.rounds with
    | nil => rfl
    | cons a l =>
      exfalso
      apply h2'
      rw [hne, hre]
      rfl
  cases hr : roleOf B.shape b.place with
  | common => rw [hr] at e; exact nomatch e
  | stray => rw [hr] at e; exact nomatch e
  | front => rw [hr] at e; rw [← Option.some.inj e]; exact main _ hr rfl
  | lay l => rw [hr] at e; rw [← Option.some.inj e]; exact main _ hr rfl
  | clear l => rw [hr] at e; rw [← Option.some.inj e]; exact main _ hr rfl
  | behind l n => rw [hr] at e; rw [← Option.some.inj e]; exact main _ hr rfl

/-- **Where nothing is wrong with the lots' blocks, just one of them is labelled with the kind K7**:
two such blocks are one. -/
theorem k7_one (Z : Pub) (T : PureSeat) (B : PureBase) (hB : baseOf Z T = .ok B)
    (hf : faultsAt T B = []) (L₁ L₂ : Lot) (h₁ : L₁ ∈ T.lots) (h₂ : L₂ ∈ T.lots)
    (b₁ b₂ : Block S Cl) (m₁ : b₁ ∈ L₁.blocks B.G₀) (m₂ : b₂ ∈ L₂.blocks B.G₀)
    (k₁ : b₁.place.kind = .K7) (k₂ : b₂.place.kind = .K7) : b₁ = b₂ := by
  obtain ⟨_, hall, hsh, _⟩ := baseOf_made Z T B hB
  obtain ⟨sv, hl, hp⟩ := shapeOf_places Z B.shape hsh
  have hf' := faultsOf_of_faultsAt T B hf
  obtain ⟨F1, F2⟩ := faultsOf_nil _ _ hf'
  have mem : ∀ (L : Lot) (b : Block S Cl), L ∈ T.lots → b ∈ L.blocks B.G₀ →
      b ∈ B.all.flatMap fun x => x.2 := by
    intro L b hL hb
    rw [hall]
    exact List.mem_flatMap.2 ⟨(L, L.blocks B.G₀), List.mem_map.2 ⟨L, hL, rfl⟩, hb⟩
  obtain ⟨s₁, hs₁, e₁⟩ := F1 b₁ (mem L₁ b₁ h₁ m₁) (by rw [k₁]; exact fun e => nomatch e)
  obtain ⟨s₂, hs₂, e₂⟩ := F1 b₂ (mem L₂ b₂ h₂ m₂) (by rw [k₂]; exact fun e => nomatch e)
  have p₁ : s₁.2 ∈ flatPlacesOf (subsOf Z) sv := by
    rw [← hp]; exact List.mem_map.2 ⟨s₁, hs₁, rfl⟩
  have p₂ : s₂.2 ∈ flatPlacesOf (subsOf Z) sv := by
    rw [← hp]; exact List.mem_map.2 ⟨s₂, hs₂, rfl⟩
  have e : s₁.2 = s₂.2 := flatPlaces_K7_one _ sv hl _ _ p₁ p₂ (by rw [e₁]; exact k₁)
    (by rw [e₂]; exact k₂)
  have q₁ : b₁ ∈ (B.all.flatMap fun x => x.2).filter fun o => o.place == s₁.2 :=
    List.mem_filter.2 ⟨mem L₁ b₁ h₁ m₁, by rw [e₁]; exact beq_self_eq_true _⟩
  have q₂ : b₂ ∈ (B.all.flatMap fun x => x.2).filter fun o => o.place == s₁.2 :=
    List.mem_filter.2 ⟨mem L₂ b₂ h₂ m₂, by rw [e, e₂]; exact beq_self_eq_true _⟩
  have hlen := F2 s₁ hs₁
  cases hq : (B.all.flatMap fun x => x.2).filter fun o => o.place == s₁.2 with
  | nil => rw [hq] at q₁; cases q₁
  | cons x l =>
    rw [hq] at q₁ q₂ hlen
    cases l with
    | nil => rw [List.mem_singleton.1 q₁, List.mem_singleton.1 q₂]
    | cons y l' => simp at hlen

theorem mem_ite_single {c : Prop} [Decidable c] (s : String) (h : c) :
    s ∈ (if c then [s] else []) := by
  rw [if_pos h]
  exact List.mem_singleton.2 rfl

/-- **Where nothing is wrong with the lots, a batching's maker's block, at the gatherer that gathers
nothing, bears the place at which the maker is given, and that place is of the kind K9.** -/
theorem face_label (Z : Pub) (T : PureSeat) (B : PureBase) (hB : baseOf Z T = .ok B)
    (hf : faultsAt T B = []) (p : Spot) (hp : p ∈ B.spots) (L : Lot) (hL : L ∈ T.lots)
    (mk : Gatherer → Block S Cl) (e : L.batch B.G₀ p.place = some mk) :
    (mk noneGathered).place = p.place ∧ p.place.kind = .K9 := by
  obtain ⟨_, _, _, hk9⟩ := baseOf_made Z T B hB
  have hg : L ∈ T.lots.filter fun L => (L.batch B.G₀ p.place).isSome :=
    List.mem_filter.2 ⟨hL, by rw [e]; rfl⟩
  have hne : (T.lots.filter fun L => (L.batch B.G₀ p.place).isSome).isEmpty = false := by
    cases hq : T.lots.filter fun L => (L.batch B.G₀ p.place).isSome with
    | nil => rw [hq] at hg; cases hg
    | cons _ _ => rfl
  -- no word of the spot's own list of faults is said
  have key : ∀ x : String, x ∈ faultsAt T B → False := fun x hx => by rw [hf] at hx; cases hx
  unfold faultsAt at key
  dsimp only at key
  simp only [List.mem_append, List.mem_flatMap] at key
  have key' := fun (x : String) hx => key x (Or.inl (Or.inl (Or.inr ⟨p, hp, hx⟩)))
  rw [hne] at key'
  simp only [Bool.false_eq_true, if_false, List.mem_append] at key'
  constructor
  · by_contra hn
    have hany : ((T.lots.filter fun L => (L.batch B.G₀ p.place).isSome).any fun L =>
        ((L.batch B.G₀ p.place).map fun mk =>
          (mk fun s => .ok ([], s)).place != p.place).getD false) = true :=
      List.any_eq_true.2 ⟨L, hg, by
        rw [e]
        show ((mk noneGathered).place != p.place) = true
        simpa using hn⟩
    exact key' _ (Or.inl (Or.inl (Or.inl (Or.inr (mem_ite_single _ hany)))))
  · by_contra hn
    have hany : (!(B.batchAt.any fun x => x.2 == p.place)) = true := by
      rw [Bool.not_eq_true']
      cases hq : B.batchAt.any fun x => x.2 == p.place with
      | false => rfl
      | true =>
        obtain ⟨x, hx, ex⟩ := List.any_eq_true.1 hq
        exact absurd (by rw [← eq_of_beq ex]; exact hk9 x hx) hn
    exact key' _ (Or.inl (Or.inl (Or.inl (Or.inl (mem_ite_single _ hany)))))

/-- **WHERE `onlineDescriptionFromPublicPart` MAKES THE FILE's DESCRIPTION, IT HEARS THE REPLY, AT THE ONE SEAT.** -/
theorem pure_hears_at (rd : List Fmt.RoundView → Option E) (Z : Pub) (T : PureSeat) (Fd : FileDescription Inst)
    (hFd : onlineDescriptionFromPublicPart Z T = .ok Fd) (hsame : T.same = sameReply)
    (hy : ∀ B, baseOf Z T = .ok B → faultsAt T B = [] →
      LotsLay (fun s : S => s.out.reply) rd T B.G₀) :
    ∃ (B : PureBase) (base : List (Block S Cl)) (c : Chain S Cl) (A : SharedSeat)
      (B' : SecondSeat),
      baseOf Z T = .ok B ∧ (partsAt T B).base = .ok base ∧
      chainBy Z base (partsAt T B).frames (partsAt T B).road = .ok c ∧
      T.shared = some A ∧ T.second = some B' ∧
      Fd = fileDescBy T.older T.links Z A B' (fun s => s) (startS Z) c ∧
      ∃ H : (fileDescBy T.older T.links Z A B' (fun s => s) (startS Z) c).Hears
          (fun x => x.asked) rd,
        H.heard = (fun s : S => s.out.reply) ∧ H.blk.place.kind = .K7 ∧
        H.blk.rounds.length = 1 ∧
        (∀ b ∈ H.pre, b.place.kind ≠ .K7) ∧ ∀ b ∈ H.post, b.place.kind ≠ .K7 := by
  obtain ⟨B, hB, hfa, _, ht⟩ := Law.pureZ_ok hFd
  obtain ⟨base, c, A, B', hb, hc, hA, hB', rfl⟩ := Law.pureTail_ok ht
  obtain ⟨hG, hall, hsh, _⟩ := baseOf_made Z T B hB
  have hs : ∀ t s, (partsAt T B).road.same t s = true → s.out.reply = t.out.reply := by
    intro t s e
    have e' : T.same t s = true := e
    rw [hsame] at e'
    exact sameReply_eq t s e'
  have hleave := chainBy_leaves (fun s : S => s.out.reply) Z base _ _ c hc hs
  have hlays := chainBy_lays (fun s : S => s.out.reply) rd Z base _ _ c hc hs (fun b hbm => by
    obtain ⟨x, hx, e⟩ := mem_mapM_ok _ (partsAt T B).places base hb b hbm
    exact parts_lay _ rd T B hall (hy B hB hfa)
      (fun p hp L hL mk em hk => by
        obtain ⟨e₁, e₂⟩ := face_label Z T B hB hfa p hp L hL mk em
        rw [e₁, e₂] at hk
        cases hk) x hx b e) (frames_noRounds T B hfa)
  obtain ⟨blk, hbm, hp⟩ := chainBy_has_K7 Z base _ _ c hc
  obtain ⟨pre, post, cut⟩ := List.append_of_mem hbm
  obtain ⟨hpre, hpost⟩ := cut_pins c.blocksInOrder pre post blk cut hp (chainBy_count Z base _ _ c hc)
  refine ⟨B, base, c, A, B', hB, hb, hc, hA, hB', rfl, FileDescription.hearsOfLeaves
    (fileDescBy T.older T.links Z A B' (fun s => s) (startS Z) c) (fun x => x.asked) rd
    (fun s : S => s.out.reply) (fun a => a.kind = .K7) pre blk post cut hpost
    (fun b hbm hn => (hleave b hbm).resolve_left hn) (hlays blk hbm hp).1
    (fun x e₁ e₂ e₃ hf => finAsked_reply _ _ (fileDescBy_fin _ _ Z A B' _ _ c x e₁ e₂ e₃ hf)),
    rfl, hp, (hlays blk hbm hp).2, hpre, hpost⟩

/-- The same, said of the description that was made. -/
theorem pure_hears (rd : List Fmt.RoundView → Option E) (Z : Pub) (T : PureSeat) (Fd : FileDescription Inst)
    (hFd : onlineDescriptionFromPublicPart Z T = .ok Fd) (hsame : T.same = sameReply)
    (hy : ∀ B, baseOf Z T = .ok B → faultsAt T B = [] →
      LotsLay (fun s : S => s.out.reply) rd T B.G₀) :
    ∃ H : Fd.Hears (fun x => x.asked) rd, H.blk.place.kind = .K7 ∧ H.blk.rounds.length = 1 ∧
      (∀ b ∈ H.pre, b.place.kind ≠ .K7) ∧ ∀ b ∈ H.post, b.place.kind ≠ .K7 := by
  obtain ⟨_, _, c, A, B', _, _, _, _, _, rfl, H, _, hk⟩ := pure_hears_at rd Z T Fd hFd hsame hy
  exact ⟨H, hk⟩

end ProofFile

#print axioms ProofFile.chainBy_leaves
#print axioms ProofFile.chainBy_lays
#print axioms ProofFile.parts_lay
#print axioms ProofFile.face_label
#print axioms ProofFile.frames_noRounds
#print axioms ProofFile.k7_one
#print axioms ProofFile.pure_hears_at
#print axioms ProofFile.pure_hears
