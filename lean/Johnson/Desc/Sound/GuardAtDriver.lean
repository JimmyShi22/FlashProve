-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/GuardAtDriver.lean: THE GUARD's LAWS AT THE DRIVER's OWN TEXT. The driver (Johnson/Desc/First/Driver/Chain.lean) lays firstChain H links several := (firstChainWithoutReplyGuard H links several).map (Chain.guarded H.same hearsReply): the
form at which the laws of SeatGuardLaws | SeatGuardChain | SeatGuardFaces | SeatGuardHears | StillOfLeaves hold of the text to the letter. Here they are called at it, and what they ask of a chain is brought down to what the seat supplies (the record Blocks).

  hearsReply_eq: the driver's test on places IS atK7 (rfl). firstChain_some: a first chain is a bare chain behind the guard.
  MakerMono mk | MakerFace mk: what is asked of a maker of a batching: it says no more at a function of claims that says less; its face does not hang on that function.
  bare_batchMono | bare_batchFace: where every maker that the seat hands at a batching's place has them, every segment of the bare chain has Link.BatchMono | Link.BatchFace: by the driver's own bare_batch and the stamps.
  **firstChain_chainAt**: THE GUARDED CHAIN's YES IS THE BARE CHAIN's YES, WITH THE SAME END.
  **firstChain_flat_leaves**: where same's yes gives h s = h t: every block of the first chain's flat list stands at a place of the kind K7 or leaves h. No premise on any block.
  blockAt_hears, linkAt_hearsAt, bare_hearsAt, **firstChain_flat_hears**: where every block that the seat hands at a place of the kind K7 hears once, every block of the flat list at such a place hears once.
  firstChain_faces: the plan's faces are the bare chain's. (The places: the driver's own flat_places, at the guarded chain.)
  **firstChain_strike**: WHERE THE GUARD ADDS NOTHING: same = sameBy h, the bare chain leaves h but at K7 (Chain.LeavesBut) and the runs outside "hear" leave it: the two flat lists are ONE.
  k9_makerMono | k9_makerFace: K9's batching K9.batch (Johnson/Desc/First/Batch/Kind.lean) has both.

Silly members. same := fun _ _ => true: firstChain_flat_leaves' premise fails unless h is constant: the guard is idle, as the driver's text says. A seat that hands a block at K7's place which says yes to all and lays nothing: the premise of firstChain_flat_hears fails.
Every "there is", walked. firstChain_some's c₀: the value of firstChainWithoutReplyGuard.
Limits. RULES AT THE DRIVER's TEXT, GENERAL IN THE SEAT: nothing is shown of any seat: MakerMono | MakerFace at what the real seat hands (it hands K9's batching: by report), "hears once" at K7's supplied block (a joint: it owes more: HearsOnce.lean), Chain.LeavesBut at
the bare chain (kind by kind). That a run goes by this chain is not said here. Nothing on soundness.

-/
import Johnson.Desc.First.Driver.BatchAt
import Johnson.Desc.Sound.SeatGuardChain
import Johnson.Desc.Sound.SeatGuardHears
import Johnson.Desc.Sound.StillOfLeaves
import Johnson.Desc.Sound.BatchMonoK9

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open VerifiableInference.Desc

variable {S Cl α β : Type}

theorem hearsReply_eq : hearsReply = atK7 := rfl

theorem hearsReply_kind {a : Place} (h : hearsReply a = true) : a.kind = .K7 := eq_of_beq h

/-- A first chain is a bare chain behind the guard. -/
theorem firstChain_some {H : Blocks S Cl} {links : List ModelPart} {several : Bool} {c : Chain S Cl}
    (h : firstChain H links several = some c) :
    ∃ c₀, firstChainWithoutReplyGuard H links several = some c₀ ∧ c = c₀.guarded H.same hearsReply := by
  unfold firstChain at h
  obtain ⟨c₀, h₀, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨c₀, h₀, rfl⟩

/-- A maker of a batching says no more at a function of claims that says less. -/
def MakerMono (mk : (S → Except String (List Cl × S)) → Block S Cl) : Prop :=
  ∀ f' f : S → Except String (List Cl × S), (∀ s y, f' s = .ok y → f s = .ok y) → (mk f').UnderR (mk f)

/-- Its face does not hang on the function of claims. -/
def MakerFace (mk : (S → Except String (List Cl × S)) → Block S Cl) : Prop := ∀ f' f, (mk f').face = (mk f).face

section
variable {H : Blocks S Cl} {links : List ModelPart} {several : Bool} {c c₀ : Chain S Cl}

theorem bare_batchMono (h₀ : firstChainWithoutReplyGuard H links several = some c₀)
    (hB : ∀ a ∈ batchPlacesOf links, ∀ mk, H.batch a = some mk → MakerMono mk) : ∀ L ∈ c₀.links, L.BatchMono := by
  intro L hL f' f hf
  obtain ⟨a, ha, mk, h1, h2⟩ := bare_batch H links several c₀ h₀ L hL
  rw [h2]
  exact underR_stamp (hB a ha mk h1 f' f hf) a

theorem bare_batchFace (h₀ : firstChainWithoutReplyGuard H links several = some c₀)
    (hB : ∀ a ∈ batchPlacesOf links, ∀ mk, H.batch a = some mk → MakerFace mk) : ∀ L ∈ c₀.links, L.BatchFace := by
  intro L hL f' f
  obtain ⟨a, ha, mk, h1, h2⟩ := bare_batch H links several c₀ h₀ L hL
  rw [h2]
  exact face_stamp (hB a ha mk h1 f' f) a

/-- **The guarded chain's yes is the bare chain's yes, with the same end.** -/
theorem firstChain_chainAt (h : firstChain H links several = some c) (h₀ : firstChainWithoutReplyGuard H links several = some c₀)
    (hB : ∀ a ∈ batchPlacesOf links, ∀ mk, H.batch a = some mk → MakerMono mk) {name : String} {ft : Nat} {s e : S}
    {v : Fmt.View} (Y : chainAt name ft c.blocksInOrder s v = .ok e) : chainAt name ft c₀.blocksInOrder s v = .ok e := by
  obtain ⟨c₁, h₁, rfl⟩ := firstChain_some h
  obtain rfl : c₁ = c₀ := Option.some.inj (h₁.symm.trans h₀)
  exact Chain.guarded_chainAt H.same hearsReply c₁ (bare_batchMono h₀ hB) Y

/-- **Every block of the first chain's flat list stands at a place of the kind K7 or leaves h.** -/
theorem firstChain_flat_leaves {hh : S → α} (hs : ∀ t s, H.same t s = true → hh s = hh t)
    (h : firstChain H links several = some c) : ∀ b ∈ c.blocksInOrder, b.place.kind = .K7 ∨ b.Leaves hh := by
  obtain ⟨c₁, _, rfl⟩ := firstChain_some h
  intro b hb
  exact (Chain.guarded_flat hearsReply hs c₁ b hb).imp hearsReply_kind id

variable {r : S → Option β}

theorem blockAt_hears (hK : ∀ a b, H.block a = some b → a.kind = .K7 → b.HearsOnce r) {a : Place} {b : Block S Cl}
    (h : blockAt H a = some b) (hp : hearsReply b.place = true) : b.HearsOnce r := by
  unfold blockAt at h
  obtain ⟨b₀, e₀, rfl⟩ := Option.map_eq_some_iff.1 h
  exact fun s rs gs s' D => hK a b₀ e₀ (hearsReply_kind hp) s rs gs s' D

theorem linkAt_hearsAt (hK : ∀ a b, H.block a = some b → a.kind = .K7 → b.HearsOnce r) {l : Nat} {sub : ModelPart} {L : Link S Cl}
    (h : linkAt H l sub = some L) : L.HearsAt r hearsReply := by
  unfold linkAt at h
  simp only [Option.bind_eq_bind, Option.pure_def] at h
  obtain ⟨hear, hh, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨batch, _, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨close, hc, h⟩ := Option.bind_eq_some_iff.1 h
  cases h
  refine ⟨fun b hb hp => ?_, fun b hb hp => ?_, fun _ => rfl, fun _ => rfl⟩
  · obtain ⟨a, _, e⟩ := mem_of_mapM (blockAt H) _ _ hh b hb
    exact blockAt_hears hK e hp
  · obtain ⟨a, _, e⟩ := mem_of_mapM (blockAt H) _ _ hc b hb
    exact blockAt_hears hK e hp

theorem bare_hearsAt (hK : ∀ a b, H.block a = some b → a.kind = .K7 → b.HearsOnce r)
    (h₀ : firstChainWithoutReplyGuard H links several = some c₀) : c₀.HearsAt r hearsReply := by
  unfold firstChainWithoutReplyGuard at h₀
  simp only [Option.bind_eq_bind, Option.pure_def] at h₀
  split at h₀
  · cases h₀
  obtain ⟨_, _, h₀⟩ := Option.bind_eq_some_iff.1 h₀
  obtain ⟨ls, hl, h₀⟩ := Option.bind_eq_some_iff.1 h₀
  obtain ⟨back, hb, h₀⟩ := Option.bind_eq_some_iff.1 h₀
  cases h₀
  refine ⟨fun hp => (Bool.false_ne_true hp).elim, (fun b m => nomatch m), fun L hL => ?_, fun b m hp => ?_,
    fun hp => (Bool.false_ne_true hp).elim⟩
  · obtain ⟨x, _, e⟩ := mem_of_mapM (fun x : ModelPart × Nat => linkAt H x.2 x.1) _ _ hl L hL
    exact linkAt_hearsAt hK e
  · obtain ⟨a, _, e⟩ := mem_of_mapM (blockAt H) _ _ hb b m
    exact blockAt_hears hK e hp

/-- **Every block of the first chain's flat list at a place of the kind K7 hears once.** -/
theorem firstChain_flat_hears (hK : ∀ a b, H.block a = some b → a.kind = .K7 → b.HearsOnce r)
    (h : firstChain H links several = some c) : ∀ b ∈ c.blocksInOrder, hearsReply b.place = true → b.HearsOnce r := by
  obtain ⟨c₁, h₁, rfl⟩ := firstChain_some h
  exact (bare_hearsAt hK h₁).guarded_flat H.same

/-- The plan's faces are the bare chain's. -/
theorem firstChain_faces (h : firstChain H links several = some c) (h₀ : firstChainWithoutReplyGuard H links several = some c₀)
    (hB : ∀ a ∈ batchPlacesOf links, ∀ mk, H.batch a = some mk → MakerFace mk) :
    c.blocksInOrder.map Block.face = c₀.blocksInOrder.map Block.face := by
  obtain ⟨c₁, h₁, rfl⟩ := firstChain_some h
  obtain rfl : c₁ = c₀ := Option.some.inj (h₁.symm.trans h₀)
  exact Chain.guarded_faces H.same hearsReply c₁ (bare_batchFace h₀ hB)

/-- **Where the guard adds nothing.** -/
theorem firstChain_strike [BEq α] [LawfulBEq α] {hh : S → α} (hsame : H.same = sameBy hh)
    (h : firstChain H links several = some c) (h₀ : firstChainWithoutReplyGuard H links several = some c₀)
    (L : c₀.LeavesBut hh hearsReply) (R : c₀.RunsLeave hh) : c.blocksInOrder = c₀.blocksInOrder := by
  obtain ⟨c₁, h₁, rfl⟩ := firstChain_some h
  obtain rfl : c₁ = c₀ := Option.some.inj (h₁.symm.trans h₀)
  rw [hsame]
  exact Chain.strike L R

end

/-- K9's own batching has both. -/
theorem k9_makerMono {T : Type} (X : K9.Lens T) (p : K9.Where) : MakerMono (K9.batch X p) := K9.batch_mono X p

theorem k9_makerFace {T : Type} (X : K9.Lens T) (p : K9.Where) : MakerFace (K9.batch X p) := K9.batch_face X p

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.firstChain_chainAt
#print axioms VerifiableInference.Desc.First.firstChain_flat_leaves
#print axioms VerifiableInference.Desc.First.firstChain_flat_hears
#print axioms VerifiableInference.Desc.First.firstChain_faces
#print axioms VerifiableInference.Desc.First.firstChain_strike
#print axioms VerifiableInference.Desc.First.k9_makerMono
#print axioms VerifiableInference.Desc.First.k9_makerFace
