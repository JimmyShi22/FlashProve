-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Law/OrderStated.lean: the first chain of the proof file's description is a
value of the driver's `firstChain`. Theorems only; no file of the description imports this one.
Why. Laws on `firstChain` that are general in the blocks handed to it (for one,
Johnson/Desc/First/Driver/OrderLaw.lean: every list of claims that the protocol's order names is
stated by the hearing block of its number) apply to the description only through this.
  `chainC_first`     `chainC bs links fr = .ok c` gives `firstChain (fill ...) links ... = some c`
  `chainBy_first`    the same for `chainBy`, at the kinds of the segments of the public part
  `chainBy_first_at`   the same, with the driver's flag written out
  `chainBy_joins`, `chainBy_hands`, `chainBy_joins_outside`   after which blocks `chainBy` joins a
                     block of the kind `frame`: only in the segment that the role names; outside
                     the segments never
  `fileDescBy_first`, `_shared`, `_second`, `_start₁`, `_pub`   five fields of the structure that
                     `fileDescBy` returns, each by `rfl`
  `planOk_blocksOk`  for every `FileDescription`: `planOk` gives `blocksOk` of the first chain's flat list
  `descPure_firstChain`   the three, for `onlineDescription`
All are unfoldings. They say nothing about which blocks are handed to `firstChain`.

-/
import Johnson.Desc.ProofFile.Law.PureMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Law
open VerifiableInference.Desc (Block Chain FileDescription KindName blocksOk)
open VerifiableInference.Desc.First

theorem chainC_first {bs : List (Block S Cl)} {links : List ModelPart} {fr : Frames S Cl}
    {c : Chain S Cl} (h : chainC bs links fr = .ok c) :
    ∃ z, bs.getLast? = some z ∧
      firstChain (fill bs.dropLast z fr) links
        (bs.any fun b => b.place.kind == KindName.K13) = some c := by
  unfold chainC at h
  split at h
  · exact (error_ne_ok h).elim
  · rename_i z hz
    try dsimp only at h
    split at h
    · exact (error_ne_ok h).elim
    · rename_i c' hc
      try dsimp only at h
      split at h
      · exact (error_ne_ok h).elim
      · cases h
        exact ⟨z, hz, hc⟩

theorem chainBy_first {Z : Pub} {base : List (Block S Cl)} {fr : List (FrameRole × Block S Cl)}
    {road : Gather S Cl} {c : Chain S Cl} (h : chainBy Z base fr road = .ok c) :
    ∃ (H : Blocks S Cl) (several : Bool), firstChain H (subsOf Z) several = some c := by
  unfold chainBy at h
  try dsimp only at h
  obtain ⟨z, _, hc⟩ := chainC_first h
  exact ⟨_, _, hc⟩

theorem any_kind_map (k : KindName) (f : Block S Cl → Block S Cl)
    (hf : ∀ b, (f b).place = b.place) :
    ∀ l : List (Block S Cl),
      (l.map f).any (fun b => b.place.kind == k) = l.any fun b => b.place.kind == k
  | [] => rfl
  | b :: l => by
    rw [List.map_cons, List.any_cons, List.any_cons, hf b, any_kind_map k f hf l]

/-- `chainBy_first`, with the driver's flag written out: whether one of the blocks at the places of
a kind is of the kind K13. -/
theorem chainBy_first_at {Z : Pub} {base : List (Block S Cl)}
    {fr : List (FrameRole × Block S Cl)} {road : Gather S Cl} {c : Chain S Cl}
    (h : chainBy Z base fr road = .ok c) :
    ∃ H : Blocks S Cl,
      firstChain H (subsOf Z) (base.any fun b => b.place.kind == KindName.K13) = some c := by
  unfold chainBy at h
  try dsimp only at h
  obtain ⟨z, _, hc⟩ := chainC_first h
  rw [any_kind_map KindName.K13 _ (fun b => by split <;> rfl)] at hc
  exact ⟨_, hc⟩

/-- What `chainBy` hands the driver: `chainC` is called at `base.map join`, where `join b` is `b`
itself, or `b` with a block of the list `fr` joined after it; and it is the second only where that
block's role names `b`'s own name and the segment in which `b` stands. -/
theorem chainBy_joins {σ : Type} {Z : Pub} {base : List (Block σ Cl)}
    {fr : List (FrameRole × Block σ Cl)} {road : Gather σ Cl} {c : Chain σ Cl}
    (h : chainBy Z base fr road = .ok c) :
    ∃ (join : Block σ Cl → Block σ Cl) (Fr : Frames σ Cl),
      chainC (base.map join) (subsOf Z) Fr = .ok c ∧
      ∀ b, join b = b ∨ ∃ x ∈ fr, ∃ l, x.1 = .behind l b.name ∧ b.place.link = some l ∧
        join b = b.andThen b.name (x.2.guarded road.same fun _ => false) := by
  unfold chainBy at h
  try dsimp only at h
  refine ⟨_, _, h, fun b => ?_⟩
  try dsimp only
  split
  · rename_i x hx
    refine .inr ⟨x, List.mem_of_find?_eq_some hx, ?_⟩
    have hp := List.find?_some hx
    revert hp
    cases hx1 : x.1 with
    | behind l m =>
      intro hp
      have hp' : (b.name == m && b.place.link == some l) = true := hp
      rw [Bool.and_eq_true] at hp'
      exact ⟨l, by rw [eq_of_beq hp'.1], eq_of_beq hp'.2, rfl⟩
    | _ =>
      intro hp
      exact Bool.noConfusion (show false = true from hp)
  · exact .inl rfl

/-- `chainBy_joins`, and what else `chainC` is handed: the four fields of `road`, unchanged. -/
theorem chainBy_hands {σ : Type} {Z : Pub} {base : List (Block σ Cl)}
    {fr : List (FrameRole × Block σ Cl)} {road : Gather σ Cl} {c : Chain σ Cl}
    (h : chainBy Z base fr road = .ok c) :
    ∃ (join : Block σ Cl → Block σ Cl) (Fr : Frames σ Cl),
      chainC (base.map join) (subsOf Z) Fr = .ok c ∧ Fr.toGather = road ∧
      ∀ b, join b = b ∨ ∃ x ∈ fr, ∃ l, x.1 = .behind l b.name ∧ b.place.link = some l ∧
        join b = b.andThen b.name (x.2.guarded road.same fun _ => false) := by
  unfold chainBy at h
  try dsimp only at h
  refine ⟨_, _, h, rfl, fun b => ?_⟩
  try dsimp only
  split
  · rename_i x hx
    refine .inr ⟨x, List.mem_of_find?_eq_some hx, ?_⟩
    have hp := List.find?_some hx
    revert hp
    cases hx1 : x.1 with
    | behind l m =>
      intro hp
      have hp' : (b.name == m && b.place.link == some l) = true := hp
      rw [Bool.and_eq_true] at hp'
      exact ⟨l, by rw [eq_of_beq hp'.1], eq_of_beq hp'.2, rfl⟩
    | _ =>
      intro hp
      exact Bool.noConfusion (show false = true from hp)
  · exact .inl rfl

/-- So after a block that stands in no segment nothing is joined. -/
theorem chainBy_joins_outside {σ : Type} {Z : Pub} {base : List (Block σ Cl)}
    {fr : List (FrameRole × Block σ Cl)} {road : Gather σ Cl} {c : Chain σ Cl}
    (h : chainBy Z base fr road = .ok c) :
    ∃ (join : Block σ Cl → Block σ Cl) (Fr : Frames σ Cl),
      chainC (base.map join) (subsOf Z) Fr = .ok c ∧ ∀ b, b.place.link = none → join b = b := by
  obtain ⟨join, Fr, hc, hj⟩ := chainBy_joins h
  refine ⟨join, Fr, hc, fun b hb => ?_⟩
  rcases hj b with e | ⟨_, _, l, _, hl, _⟩
  · exact e
  · rw [hb] at hl
    cases hl

theorem planOk_blocksOk {Xi : Type} {F : FileDescription Xi} (h : F.planOk = true) :
    blocksOk F.first.blocksInOrder = true := by
  cases hb : blocksOk F.first.blocksInOrder with
  | true => rfl
  | false => simp [FileDescription.planOk, FileDescription.planOkCore, hb] at h

/-! ### Five fields of `fileDescBy` -/

section
variable {σ : Type} (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : Pub) (A : SharedSeat) (B : SecondSeat)
  (get : σ → S) (start : InstPub → σ) (c : Chain σ Cl)

theorem fileDescBy_first : (fileDescBy o mk Z A B get start c).first = c := rfl

theorem fileDescBy_shared : (fileDescBy o mk Z A B get start c).shared = A.chain.retype := rfl

theorem fileDescBy_second : (fileDescBy o mk Z A B get start c).second = B.chain.retype := rfl

theorem fileDescBy_start₁ : (fileDescBy o mk Z A B get start c).start₁ = start := rfl

theorem fileDescBy_pub (x : Inst) : (fileDescBy o mk Z A B get start c).pub x = x.pub := rfl

end

/-- Where `onlineDescription` returns `F`: its first chain `c` is a value of the driver's `firstChain`, at
the kinds of the segments of the public part; and where `F.planOk` holds, so does
`blocksOk c.blocksInOrder`. -/
theorem descPure_firstChain {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription Inst}
    (h : onlineDescription o pol lay KL = .ok F) :
    ∃ (Z : Pub) (A : SharedSeat) (B : SecondSeat) (H : Blocks S Cl) (several : Bool)
      (c : Chain S Cl),
      pureRoad.pub o pol lay KL = .ok Z ∧ firstChain H (subsOf Z) several = some c ∧
      F = fileDescBy o pureRoad.links Z A B (fun s => s) (startS Z) c ∧
      (F.planOk = true → blocksOk c.blocksInOrder = true) := by
  obtain ⟨Z, _, base, c, A, B, hZ, _, _, _, _, hc, _, _, rfl⟩ := descPure_parts h
  obtain ⟨H, several, hf⟩ := chainBy_first hc
  exact ⟨Z, A, B, H, several, c, hZ, hf, rfl, fun hp => planOk_blocksOk hp⟩

end ProofFile.Law

#print axioms ProofFile.Law.descPure_firstChain
#print axioms ProofFile.Law.chainBy_first_at
#print axioms ProofFile.Law.chainBy_joins
#print axioms ProofFile.Law.chainBy_joins_outside
#print axioms ProofFile.Law.chainBy_hands
#print axioms ProofFile.Law.fileDescBy_first
#print axioms ProofFile.Law.fileDescBy_start₁
