-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/K9x/RanAtPure.lean: THE ROAD "WHO PAYS K3RanAt" AT THE DESCRIPTION MADE OF THE
KINDS' BLOCKS ALONE (Johnson/Desc/ProofFile/OnlineDescriptionFromBlockTables.lean: `onlineDescriptionFromPublicPart Z T`), over Block.lean
and the driver. For every public part Z and every seat T.
Definitions, and theorems with their proofs.

  `pureZIsN`: where `onlineDescriptionFromPublicPart Z T` is a description: `pureZ_ok` | `pureTail_ok`
    (ProofFile/Law/PureMade.lean) in one: no fault; nothing missing; `fileDescBy` at a chain c made
    by three equations (baseOf · PureParts.base · chainBy), at the seat's own two later chains.
  `chainByIsN`, `chainCIsN`: c is the driver's `firstChain (fill …) (subsOf Z) several`; each block
    that the driver is handed is a block of the base, or such a block with a guarded frame's block
    joined behind; what is done where a link starts and ends (`stepOfRole`).
  `roadBatchIs`: what the gatherer's road answers at a place is `guardMark` of a lot's maker, under
    a name.
  `LotsCarry R Q T`: THE ONE PREMISE, ONE LAW A LOT: a lot's maker of a batching calls the function
    that it is handed (`Calls`), says no more at a function that says less (`MakerMono`), and its
    block's runs step; every run of every block that a lot lays with typed runs (`hearC`) steps.
  **`onRoadOfMade`**: WHERE `onlineDescriptionFromPublicPart Z T` IS A DESCRIPTION, THE ROAD ANSWERS AT EACH PLACE AT WHICH
    THE DRIVER ASKS FOR A BATCHING (`onRoadB Z T = true`): by `baseOfIs` (batchAt is the driver's
    own place), `mem_onRoad`, `lackOnRoad` and `spotAtBatch` (the plan has a spot at that place).
  `SeatedAs T B M`: WHAT A HEARING BLOCK IS, AS AN EQUATION, with "b₀ is the only block that any
    lot brings at that place" (`onlyBlockAt`, off the seat's own test on faults; `faceAtBatch`: a
    maker's face is no hearing block), the plan's spot whose name M bears, and, where a frame's
    block is joined behind, its role in the seat's list of frames. `FromLots`: its corollary for
    laws on a block's yes; `FromLots.steps`. `Laid` | `chain_hear`
    (Johnson/IMR/SeatForm.lean, PureChain.lean) ARE THE ELDER AND SAY THE LIKE OF THE CHAIN BEHIND
    THE DRIVER's GUARD, by index.
  `HIs Z T B H`: what the record H of the kinds' blocks is beside its blocks: each · tests · same ·
    the batching at the driver's places · lay · clear: the seat's road's and frames'.
  **`ranAtPureZ`**: from `onlineDescriptionFromPublicPart Z T = .ok F` and `LotsCarry`: F's first chain c is a chain c₀ of the
    driver's make behind the driver's guard, at an H that `HIs`; every hearing block of c₀ is
    `SeatedAs`; and a yes of F gives: (i) THE FOLD OVER c PASSES THROUGH THE RECORDS OF THE FOLD
    OVER c₀, at every length; (ii) at every link and every hearing block b behind which the hearing
    blocks step where their tests on the plan say yes: the link's trace, `RanUpTo` and `RanAllUpTo`,
    from the description's own start and the first view's own rounds and columns.

Limits. A frame's law: no error; nothing on soundness. `LotsCarry` is a premise here: paid at the
seated seat in KindsAtPure.lean. UNDER "THERE IS", OF WHAT THE VERIFIER READS: the groups gs of
opened columns that are handed to b and to the batching (`Traced`'s fields `decided`, `batched`):
tied to the view's columns by the folds' equations beside them alone; in `RanAt`: the count n that a
run is told and the record at which it ran. Claims reach cls by membership: order and number of
times are not said. NO MEMBER: that `onlineDescriptionFromPublicPart` gives a description, or that it says yes, anywhere, is a
run's word.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.K9x.RanAtDriver
import Johnson.Desc.Sound.JoinedAt
import Johnson.Desc.ChainEndFold
import Johnson.Desc.Sound.DescRunsProofs
import Johnson.Road.Lane5AttCalls
import Johnson.Desc.ProofFile.Law.PureMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S ModelPart Blocks firstChain firstChainWithoutReplyGuard linkAt batchPlaceOf
  batchPlacesOf hearsReply MakerMono ranAtFirstChain)
open ProofFile (Pub Lot Ground Cl Inst guardMark PureSeat PureParts PureBase baseOf partsAt onlineDescriptionFromPublicPart onlineDescriptionAfterTests
        chainBy chainC fill Frames Gather FrameRole fileDescBy startS subsOf)

/-! ## The guard on marks -/

theorem yesGuardN (b : Block S Cl) : YesOf (guardMark b) b :=
  yesOfBind b (guardMark b)
    (fun t => match t.failed with
      | none => .ok t
      | some m => .error ("marked: " ++ m))
    (fun t t' h => by
      dsimp only at h
      split at h
      · exact (Except.ok.inj h).symm
      · exact nomatch h)
    fun _ _ _ => rfl

/-! ## The fold's own text -/

/-- **Where `onlineDescriptionFromPublicPart Z T` is a description**: ProofFile's own `pureZ_ok` and `pureTail_ok`
(Johnson/Desc/ProofFile/Law/PureMade.lean), in one. -/
theorem pureZIsN (Z : Pub) (T : PureSeat) (F : FileDescription Inst) (h : onlineDescriptionFromPublicPart Z T = .ok F) :
    ∃ B base c A B₂, baseOf Z T = .ok B ∧ ProofFile.faultsAt T B = [] ∧
      ProofFile.lackingAt T (partsAt T B) = [] ∧ (partsAt T B).base = .ok base ∧
      chainBy Z base (partsAt T B).frames (partsAt T B).road = .ok c ∧
      T.shared = some A ∧ T.second = some B₂ ∧
      F = fileDescBy T.older T.links Z A B₂ (fun s => s) (startS Z) c := by
  obtain ⟨B, hB, hf, hl, ht⟩ := ProofFile.Law.pureZ_ok h
  obtain ⟨base, c, A, B₂, h₁, h₂, h₃, h₄, h₅⟩ := ProofFile.Law.pureTail_ok ht
  exact ⟨B, base, c, A, B₂, hB, hf, hl, h₁, h₂, h₃, h₄, h₅⟩

/-- What `chainBy` lays where a link starts, or ends: the decision of the block of that role, at no
round; where there is none the record is handed on. -/
def stepOfRole {σ : Type} (fr : List (FrameRole × Block σ Cl)) (r : FrameRole) (t : σ) :
    Except String σ :=
  match (fr.find? fun x => x.1 == r).map fun x => x.2 with
  | some o => o.decide t [] []
  | none => .ok t

/-- **What `chainBy` hands the driver.** -/
theorem chainByIsN {σ : Type} (Z : Pub) (base : List (Block σ Cl))
    (fr : List (FrameRole × Block σ Cl)) (road : Gather σ Cl) (c : Chain σ Cl)
    (h : chainBy Z base fr road = .ok c) :
    ∃ (joined : List (Block σ Cl)) (F : Frames σ Cl), chainC joined (subsOf Z) F = .ok c ∧
      F.toGather = road ∧ (∀ l t, F.lay l t = stepOfRole fr (.lay l) t) ∧
      (∀ l t, F.clear l t = stepOfRole fr (.clear l) t) ∧
      ∀ x ∈ joined, ∃ b ∈ base, x = b ∨
        ∃ y ∈ fr, (∃ l, y.1 = .behind l b.name) ∧
          x = b.andThen b.name (y.2.guarded road.same fun _ => false) := by
  unfold chainBy at h
  refine ⟨_, _, h, rfl, fun _ _ => rfl, fun _ _ => rfl, fun x hx => ?_⟩
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
  refine ⟨b, hb, ?_⟩
  split
  · rename_i y hy
    have hb' := List.find?_some hy
    refine Or.inr ⟨y, List.mem_of_find?_eq_some hy, ?_, rfl⟩
    obtain ⟨r, q⟩ := y
    cases r with
    | behind l m => exact ⟨l, by rw [eq_of_beq (Bool.and_eq_true_iff.1 hb').1]⟩
    | _ => exact nomatch hb'
  · exact Or.inl rfl

theorem chainCIsN {σ Cl' : Type} (bs : List (Block σ Cl')) (links : List ModelPart) (fr : Frames σ Cl')
    (c : Chain σ Cl') (h : chainC bs links fr = .ok c) :
    ∃ z several, firstChain (fill bs.dropLast z fr) links several = some c := by
  unfold chainC at h
  split at h
  · exact nomatch h
  · rename_i z _
    dsimp only at h
    split at h
    · exact nomatch h
    · rename_i c' hc'
      split at h
      · exact nomatch h
      · obtain rfl := Except.ok.inj h
        exact ⟨z, _, hc'⟩

theorem fillBlockN {σ : Type} (bs : List (Block σ Cl)) (z : Block σ Cl) (fr : Frames σ Cl)
    (a : Place) (b : Block σ Cl) (h : (fill bs z fr).block a = some b) : b ∈ bs :=
  List.mem_of_find?_eq_some h

/-- Where the road answers at a place, the driver is handed the road's answer. -/
theorem fillBatchN {σ : Type} (bs : List (Block σ Cl)) (z : Block σ Cl) (fr : Frames σ Cl)
    (a : Place) (mk : (σ → Except String (List Cl × σ)) → Block σ Cl)
    (hr : (fr.batch a).isSome = true) (h : (fill bs z fr).batch a = some mk) :
    fr.batch a = some mk := by
  obtain ⟨mk', e⟩ := Option.isSome_iff_exists.1 hr
  have h' : (fr.batch a <|> (bs.find? fun b => b.place == a).map fun b _ => b) = some mk := h
  rw [e] at h' ⊢
  exact h'

/-- **What the gatherer's road answers**: `guardMark` of a lot's maker, under a name. -/
theorem roadBatchIs (T : PureSeat) (B : PureBase) (a : Place)
    (mk : (S → Except String (List Cl × S)) → Block S Cl)
    (h : (partsAt T B).road.batch a = some mk) :
    ∃ lot ∈ T.lots, ∃ mk₀, lot.batch B.G₀ a = some mk₀ ∧
      ∃ n : String → String, mk = fun g => { guardMark (mk₀ g) with name := n (mk₀ g).name } := by
  obtain ⟨mk₀, h₀, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨lot, hl, e⟩ := List.exists_of_findSome?_eq_some h₀
  exact ⟨lot, (List.mem_filter.1 hl).1, mk₀, e, _, rfl⟩

/-! ## The premises -/

/-- **One law a lot.** -/
structure LotsCarry (R : S → S → Prop)
    (Q : Place → S → List Fmt.RoundView → S → List Cl → S → S → Prop) (T : PureSeat) : Prop where
  calls : ∀ lot ∈ T.lots, ∀ G a mk, lot.batch G a = some mk → Calls R (Q a) mk
  mono : ∀ lot ∈ T.lots, ∀ G a mk, lot.batch G a = some mk → MakerMono mk
  face : ∀ lot ∈ T.lots, ∀ G a mk, lot.batch G a = some mk → ∀ g, (mk g).RunsStep R
  runs : ∀ lot ∈ T.lots, ∀ G, ∀ b ∈ lot.hearC G, b.RunsStep R

/-- So the runs of every block of a lot step: what a lot lays in `own` is carried over by
`Block.retype`, which states no run. -/
theorem LotsCarry.blocks {R : S → S → Prop}
    {Q : Place → S → List Fmt.RoundView → S → List Cl → S → S → Prop} {T : PureSeat}
    (H : LotsCarry R Q T) : ∀ lot ∈ T.lots, ∀ G, ∀ b ∈ lot.blocks G, b.RunsStep R := by
  intro lot hl G b hb
  rcases List.mem_append.1 hb with hb | hb
  · obtain ⟨b₀, _, rfl⟩ := List.mem_map.1 hb
    exact runsOfBare _ rfl
  · exact H.runs lot hl G b hb

/-- At each place at which the driver asks for a batching the road answers: with code. -/
def onRoadB (Z : Pub) (T : PureSeat) : Bool :=
  match baseOf Z T with
  | .ok B => (batchPlacesOf (subsOf Z)).all fun a => ((partsAt T B).road.batch a).isSome
  | .error _ => false

theorem onRoadOk (Z : Pub) (T : PureSeat) (B : PureBase) (hB : baseOf Z T = .ok B)
    (h : onRoadB Z T = true) :
    ∀ a ∈ batchPlacesOf (subsOf Z), ((partsAt T B).road.batch a).isSome = true := by
  unfold onRoadB at h
  rw [hB] at h
  exact fun a ha => List.all_eq_true.1 h a ha

/-! ## The lots' laws reach what the driver is handed -/

-- (`baseOfIs` stands here; what follows from it on the road: "The road answers where the driver
-- asks", further down.)

/-- **What `baseOf` lays**: the plan's spots; the shape; the blank letters; the lots' own tables at
these; and, a link, THE DRIVER's OWN PLACE OF THE BATCHING. -/
theorem baseOfIs (Z : Pub) (T : PureSeat) (B : PureBase) (h : baseOf Z T = .ok B) :
    ProofFile.spotsOf Z.cuts = some B.spots ∧ ProofFile.shapeOf Z = .ok B.shape ∧
      ProofFile.blankBy T.links Z = some B.G₀ ∧ B.all = (T.lots.map fun L => (L, L.blocks B.G₀)) ∧
      B.batchAt = (subsOf Z).zipIdx.map fun x => (x.2, batchPlaceOf x.2 x.1) := by
  unfold baseOf at h
  obtain ⟨ps, h₁, h⟩ := ProofFile.Law.exBind_ok h
  obtain ⟨sh, h₂, h⟩ := ProofFile.Law.exBind_ok h
  obtain ⟨G, h₃, h⟩ := ProofFile.Law.exBind_ok h
  obtain rfl := Except.ok.inj h
  exact ⟨ProofFile.Law.orSay_ok h₁, h₂, ProofFile.Law.orSay_ok h₃, rfl, rfl⟩

theorem baseOfAll (Z : Pub) (T : PureSeat) (B : PureBase) (h : baseOf Z T = .ok B) :
    B.all = T.lots.map fun L => (L, L.blocks B.G₀) := (baseOfIs Z T B h).2.2.2.1

theorem baseOfBlank (Z : Pub) (T : PureSeat) (B : PureBase) (h : baseOf Z T = .ok B) :
    ProofFile.blankBy T.links Z = some B.G₀ := (baseOfIs Z T B h).2.2.1

theorem runsGuarded {σ : Type} {R : σ → σ → Prop} (same : σ → σ → Bool) (but : Place → Bool)
    (b : Block σ Cl) (h : b.RunsStep R) : (b.guarded same but).RunsStep R := by
  intro c hc n s cl s' H
  obtain ⟨c₀, h₀, -, hh⟩ := guarded_claims_under same but b c hc
  exact h c₀ h₀ n s cl s' (hh n s (cl, s') H).1

section Reach
variable {R : S → S → Prop} {Q : Place → S → List Fmt.RoundView → S → List Cl → S → S → Prop}
  (T : PureSeat) (B : PureBase) (hall : B.all = T.lots.map fun L => (L, L.blocks B.G₀))
  (HL : LotsCarry R Q T)
include hall HL

/-- Every block of the list of places: its runs step. -/
theorem placesRuns : ∀ x ∈ (partsAt T B).places, ∀ b, x.2 = .ok b → b.RunsStep R := by
  intro x hx b hb
  obtain ⟨p, _, rfl⟩ := List.mem_map.1 hx
  dsimp only at hb
  split at hb
  · rename_i f _ hf
    obtain rfl := Except.ok.inj hb
    obtain ⟨mk, hmk, rfl⟩ := Option.map_eq_some_iff.1 hf
    obtain ⟨lot, hl, mk₀, h₀, n, rfl⟩ := roadBatchIs T B p.place mk hmk
    exact runsOfClaims (mk₀ _) _ rfl (HL.face lot hl _ _ mk₀ h₀ _)
  · rename_i w _ hw
    obtain rfl := Except.ok.inj hb
    obtain ⟨v, hv, hvw⟩ := List.mem_filterMap.1 (List.mem_of_find?_eq_some hw)
    obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 hvw
    rw [hall] at hv
    obtain ⟨lot, hlot, rfl⟩ := List.mem_map.1 hv
    exact runsOfClaims b₀ _ rfl (HL.blocks lot hlot _ b₀ (List.mem_of_find?_eq_some hb₀))
  · split at hb <;> exact nomatch hb

/-- Every block at a frame's place: its runs step. -/
theorem framesRuns : ∀ y ∈ (partsAt T B).frames, y.2.RunsStep R := by
  intro y hy
  obtain ⟨v, hv, hy⟩ := List.mem_flatMap.1 hy
  rw [hall] at hv
  obtain ⟨lot, hlot, rfl⟩ := List.mem_map.1 hv
  dsimp only at hy
  split at hy
  · exact nomatch hy
  · obtain ⟨b, hb, hby⟩ := List.mem_filterMap.1 hy
    have hr := HL.blocks lot hlot _ b (List.mem_filter.1 hb).1
    split at hby
    · exact nomatch hby
    · exact nomatch hby
    · obtain rfl := Option.some.inj hby
      exact runsOfClaims b _ rfl hr

end Reach

/-! ## The road answers where the driver asks -/

/-- The plan has a spot at the driver's place of each link's batching: by the shape's own make: the
driver's chain over idle blocks at the plan's spots, with no road: there the driver's look-up for
the batching finds a block of the list, or no chain is made. -/
theorem spotAtBatch (Z : Pub) (ps : List ProofFile.Spot) (hps : ProofFile.spotsOf Z.cuts = some ps)
    (sh : List (String × Place)) (hsh : ProofFile.shapeOf Z = .ok sh) (x : ModelPart × Nat)
    (hx : x ∈ (subsOf Z).zipIdx) : ∃ p ∈ ps, p.place = batchPlaceOf x.2 x.1 := by
  unfold ProofFile.shapeOf at hsh
  obtain ⟨ps', h₁, hsh⟩ := ProofFile.Law.bind_ok hsh
  obtain rfl : ps' = ps := Option.some.inj ((ProofFile.Law.orSay_ok h₁).symm.trans hps)
  obtain ⟨c, hc, -⟩ := ProofFile.Law.bind_ok hsh
  obtain ⟨z, several, hf⟩ := chainCIsN _ _ _ c hc
  obtain ⟨c₀, h₀, -⟩ := First.firstChain_some hf
  obtain ⟨L, hL⟩ := First.linkAt_of_bare _ _ _ c₀ h₀ x hx
  obtain ⟨mk, hmk, -⟩ := First.linkAt_batch _ x.2 x.1 L hL
  obtain ⟨b, hb, -⟩ := Option.map_eq_some_iff.1 hmk
  have hq : (b.place == batchPlaceOf x.2 x.1) = true :=
    List.find?_some (p := fun b : Block Unit Unit => b.place == batchPlaceOf x.2 x.1) hb
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 (List.mem_of_mem_dropLast (List.mem_of_find?_eq_some hb))
  exact ⟨p, hp, eq_of_beq hq⟩

/-- A link that `partsAt` counts as on the road: the road answers at the place that `baseOf` laid
for it. -/
theorem mem_onRoad (T : PureSeat) (B : PureBase) (l : Nat) (h : l ∈ (partsAt T B).onRoad) :
    ∃ y ∈ B.batchAt, y.1 = l ∧ ((partsAt T B).road.batch y.2).isSome = true := by
  obtain ⟨y, hy, e⟩ := List.mem_filterMap.1 h
  split at e
  · rename_i hm
    refine ⟨y, hy, Option.some.inj e, ?_⟩
    show (Option.map _ _).isSome = true
    rw [Option.isSome_map]
    exact hm
  · exact nomatch e

/-- Where nothing is missing, every link of the plan's spots is on the road. -/
theorem lackOnRoad (T : PureSeat) (P : PureParts) (h : ProofFile.lackingAt T P = []) (l : Nat)
    (hl : l ∈ (P.places.filterMap fun x => x.1.place.link).eraseDups) :
    P.onRoad.contains l = true := by
  unfold ProofFile.lackingAt at h
  simp only [List.append_eq_nil_iff, List.flatMap_eq_nil_iff] at h
  obtain ⟨⟨⟨-, hf⟩, -⟩, -⟩ := h
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, h4⟩, -⟩, -⟩ := hf l hl
  cases hc : P.onRoad.contains l with
  | true => rfl
  | false =>
    rw [hc] at h4
    exact absurd h4 (by simp)

/-- **WHERE `onlineDescriptionFromPublicPart Z T` IS A DESCRIPTION, THE ROAD ANSWERS AT EACH PLACE AT WHICH THE DRIVER ASKS
FOR A BATCHING**, at every seat T: so `ProofFile.fill`'s second arm, which hands on a block that never
sees the gatherer, is not taken there. By ProofFile's own tests (`baseOf`: batchAt; `partsAt`: onRoad;
`lackingAt`). -/
theorem onRoadOfMade (Z : Pub) (T : PureSeat) (F : FileDescription Inst) (h : onlineDescriptionFromPublicPart Z T = .ok F) :
    onRoadB Z T = true := by
  obtain ⟨B, _, _, _, _, hB, -, hl, -⟩ := pureZIsN Z T F h
  obtain ⟨hs, hsh, -, -, hba⟩ := baseOfIs Z T B hB
  unfold onRoadB
  rw [hB]
  refine List.all_eq_true.2 fun a ha => ?_
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
  obtain ⟨p, hp, hpp⟩ := spotAtBatch Z B.spots hs B.shape hsh x hx
  have hlink : x.2 ∈ ((partsAt T B).places.filterMap fun y => y.1.place.link).eraseDups := by
    rw [List.mem_eraseDups]
    refine List.mem_filterMap.2 ⟨_, List.mem_map.2 ⟨p, hp, rfl⟩, ?_⟩
    show p.place.link = some x.2
    rw [hpp]
    rfl
  obtain ⟨y, hy, e, hs'⟩ := mem_onRoad T B x.2
    (List.contains_iff_mem.1 (lackOnRoad T _ hl x.2 hlink))
  rw [hba] at hy
  obtain ⟨x', hx', rfl⟩ := List.mem_map.1 hy
  have e' : x'.2 = x.2 := e
  have h₁ := List.mem_zipIdx_iff_getElem?.1 hx
  have h₂ := List.mem_zipIdx_iff_getElem?.1 hx'
  rw [e'] at h₂
  have e₁ : x'.1 = x.1 := Option.some.inj (h₂.symm.trans h₁)
  have hs'' : ((partsAt T B).road.batch (batchPlaceOf x'.2 x'.1)).isSome = true := hs'
  rw [e', e₁] at hs''
  exact hs''

/-! ## What a hearing block of the chain is -/

theorem yesAndThenN {T Cl' : Type} (n n' : String) (p p' q q' : Block T Cl') (hp : YesOf p' p)
    (hq : YesOf q' q) (hr : p'.rounds = p.rounds) :
    YesOf (p'.andThen n' q') (p.andThen n q) := by
  intro s rs gs s' H
  obtain ⟨m, hm, H'⟩ := bindOk
    (x := p'.decide s (rs.take p'.rounds.length) (gs.take p'.openings)) H
  have ho : p'.openings = p.openings := by unfold Block.openings; rw [hr]
  rw [hr, ho] at hm H'
  show (p.decide s (rs.take p.rounds.length) (gs.take p.openings)).bind _ = _
  rw [hp _ _ _ _ hm]
  exact hq _ _ _ _ H'

/-- **WHAT A HEARING BLOCK OF THE CHAIN IS, AS AN EQUATION.** M is `guardMark` of a block b₀ that a
lot of the seat brings at M's own place, under the name of a spot p of the plan at that place; or
that with `guardMark` of a lot's block of the kind "frame", behind the seat's guard on the reply at
every place, joined behind: then that block stands in the seat's list of frames with the role
"behind the block of the name p.name". AND b₀ IS THE ONLY BLOCK THAT ANY LOT OF THE SEAT BRINGS AT
THAT PLACE: so a kind that brings a block there knows that b₀ is its own. (`Laid`,
Johnson/IMR/SeatForm.lean, says the like of the chain behind the driver's guard.) -/
def SeatedAs (T : PureSeat) (B : PureBase) (M : Block S Cl) : Prop :=
  ∃ lot ∈ T.lots, ∃ b₀ ∈ lot.blocks B.G₀, b₀.place = M.place ∧
    (∀ lot' ∈ T.lots, ∀ b₁ ∈ lot'.blocks B.G₀, b₁.place = M.place → b₁ = b₀) ∧
    ∃ p ∈ B.spots, p.place = M.place ∧
      (M = { guardMark b₀ with name := p.name } ∨
        ∃ y ∈ (partsAt T B).frames, (∃ l, y.1 = .behind l p.name) ∧
          ∃ lot' ∈ T.lots, ∃ fr ∈ lot'.blocks B.G₀, (fr.place.kind == KindName.frame) = true ∧
            y.2 = guardMark fr ∧
            M = ({ guardMark b₀ with name := p.name } : Block S Cl).andThen p.name
              ((guardMark fr).guarded T.same fun _ => false))

/-- What `SeatedAs` gives a law of the form "every yes of the block …": b₀'s runs are M's under
their names; b₀'s test on the plan says yes where M's does; every yes of M is a yes of b₀, or of b₀
with the frame's block joined behind. -/
def FromLots (T : PureSeat) (G₀ : Ground) (M : Block S Cl) : Prop :=
  ∃ lot ∈ T.lots, ∃ b₀ ∈ lot.blocks G₀, b₀.place = M.place ∧
    (∀ lot' ∈ T.lots, ∀ b₁ ∈ lot'.blocks G₀, b₁.place = M.place → b₁ = b₀) ∧
    (M.planOk = true → b₀.planOk = true) ∧
    (∀ n run, b₀.claims.lookup n = some run → M.claims.lookup n = some run) ∧
    (YesOf M b₀ ∨ ∃ lot' ∈ T.lots, ∃ fr ∈ lot'.blocks G₀,
      (fr.place.kind == KindName.frame) = true ∧ (M.planOk = true → fr.planOk = true) ∧
        YesOf M (b₀.andThen M.name fr))

theorem SeatedAs.fromLots {T : PureSeat} {B : PureBase} {M : Block S Cl} (h : SeatedAs T B M) :
    FromLots T B.G₀ M := by
  obtain ⟨lot, hl, b₀, hb₀, hp, ho, p, -, -, hM⟩ := h
  refine ⟨lot, hl, b₀, hb₀, hp, ho, ?_⟩
  rcases hM with rfl | ⟨-, -, -, lot', hl', fr, hfr, hk, -, rfl⟩
  · exact ⟨fun h => h, fun _ _ h => h,
      Or.inl ((yesOfDecide (guardMark b₀) _ rfl).trans (yesGuardN b₀))⟩
  · refine ⟨fun h => (Bool.and_eq_true_iff.1 h).1, fun nm run hrun => ?_,
      Or.inr ⟨lot', hl', fr, hfr, hk, fun h => (Bool.and_eq_true_iff.1 h).2,
        yesAndThenN _ p.name b₀ _ fr _ ((yesOfDecide (guardMark b₀) _ rfl).trans (yesGuardN b₀))
          (YesOf.trans (guarded_under _ _ (guardMark fr)) (yesGuardN fr)) rfl⟩⟩
    show (b₀.claims ++ _).lookup nm = some run
    rw [List.lookup_append, hrun]
    rfl

/-- So M steps WHERE ITS TEST ON THE PLAN SAYS YES, if ONE block b₁ that a lot brings at M's place,
and the lots' blocks of the kind "frame", step where their own tests on the plan say yes. (The
lookups' files' law on their seated block, `via_steps`, has that premise.) -/
theorem FromLots.steps {R : S → S → Prop} (hR : Pre R) {T : PureSeat} {G₀ : Ground}
    {M : Block S Cl} (h : FromLots T G₀ M) (lot₁ : Lot) (h₁ : lot₁ ∈ T.lots) (b₁ : Block S Cl)
    (hb₁ : b₁ ∈ lot₁.blocks G₀) (hp₁ : b₁.place = M.place) (hb : b₁.planOk = true → b₁.Steps R)
    (hf : ∀ lot ∈ T.lots, ∀ fr ∈ lot.blocks G₀, (fr.place.kind == KindName.frame) = true →
      fr.planOk = true → fr.Steps R) (hM : M.planOk = true) : M.Steps R := by
  obtain ⟨lot, hl, b₀, hb₀, hp, ho, hpl, -, hy⟩ := h
  obtain rfl := ho lot₁ h₁ b₁ hb₁ hp₁
  rcases hy with hy | ⟨lot', hl', fr, hfr, hk, hfp, hy⟩
  · exact stepsOfYes b₁ M hy (hb (hpl hM))
  · exact stepsOfYes _ M hy (stepsAndThen hR _ b₁ fr (hb (hpl hM)) (hf lot' hl' fr hfr hk (hfp hM)))

/-! ## What the seat's own tests give -/

theorem eqOfShort {α : Type} : ∀ {l : List α}, ¬ 1 < l.length → ∀ {a b : α}, a ∈ l → b ∈ l → a = b
  | [], _, _, _, ha, _ => nomatch ha
  | [x], _, a, b, ha, hb => by rw [List.mem_singleton.1 ha, List.mem_singleton.1 hb]
  | _ :: _ :: _, h, _, _, _, _ => absurd (by simp) h

/-- Where `faultsOf` finds nothing: a block of another kind than "frame" stands at a place of the
shape; and at a place of the shape stands one block at most. -/
theorem faultsOfNil (shape : List (String × Place)) (own : List (Block S Cl))
    (h : ProofFile.faultsOf shape own = []) :
    (∀ o ∈ own, (o.place.kind != KindName.frame) = true → ∃ s ∈ shape, s.2 = o.place) ∧
      ∀ s ∈ shape, ¬ 1 < (own.filter fun o => o.place == s.2).length := by
  unfold ProofFile.faultsOf at h
  simp only [List.append_eq_nil_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff] at h
  obtain ⟨⟨h₁, -⟩, h₃⟩ := h
  refine ⟨fun o ho hk => ?_, fun s hs hc => h₃ s hs (decide_eq_true hc)⟩
  have h' := h₁ o ho
  rw [hk, Bool.true_and, Bool.not_eq_true', Bool.not_eq_false] at h'
  obtain ⟨s, hs, e⟩ := List.any_eq_true.1 h'
  exact ⟨s, hs, eq_of_beq e⟩

section Come
variable (T : PureSeat) (B : PureBase) (hall : B.all = T.lots.map fun L => (L, L.blocks B.G₀))
include hall

/-- Every block of the list of places: `guardMark` of a lot's block, under a name; or (a face) of a
lot's maker of a batching, given AT A SPOT OF THE PLAN, at the gatherer that gathers nothing. -/
theorem placesCome : ∀ x ∈ (partsAt T B).places, ∀ b, x.2 = .ok b →
    (∃ lot ∈ T.lots, ∃ b₀ ∈ lot.blocks B.G₀, ∃ p ∈ B.spots, b₀.place = p.place ∧
      b = { guardMark b₀ with name := p.name }) ∨
    ∃ p ∈ B.spots, ∃ lot ∈ T.lots, ∃ mk₀, lot.batch B.G₀ p.place = some mk₀ ∧
      ∃ n, b = { guardMark (mk₀ fun s => .ok ([], s)) with name := n } := by
  intro x hx b hb
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
  dsimp only at hb
  split at hb
  · rename_i f _ hf
    obtain rfl := Except.ok.inj hb
    obtain ⟨mk, hmk, rfl⟩ := Option.map_eq_some_iff.1 hf
    obtain ⟨lot, hl, mk₀, h₀, n, rfl⟩ := roadBatchIs T B p.place mk hmk
    exact Or.inr ⟨p, hp, lot, hl, mk₀, h₀, _, rfl⟩
  · rename_i w _ hw
    obtain rfl := Except.ok.inj hb
    obtain ⟨v, hv, hvw⟩ := List.mem_filterMap.1 (List.mem_of_find?_eq_some hw)
    obtain ⟨b₀, hb₀, rfl⟩ := Option.map_eq_some_iff.1 hvw
    rw [hall] at hv
    obtain ⟨lot, hlot, rfl⟩ := List.mem_map.1 hv
    exact Or.inl ⟨lot, hlot, b₀, List.mem_of_find?_eq_some hb₀, p, hp,
      eq_of_beq (List.find?_some (p := fun b : Block S Cl => b.place == p.place) hb₀), rfl⟩
  · split at hb <;> exact nomatch hb

/-- **Where the seat has no fault: of the blocks of another kind than "frame" that its lots bring,
one at most stands at a place.** -/
theorem onlyBlockAt (hf : ProofFile.faultsAt T B = []) (lot : Lot) (hl : lot ∈ T.lots)
    (b₀ : Block S Cl) (hb₀ : b₀ ∈ lot.blocks B.G₀)
    (hk : (b₀.place.kind != KindName.frame) = true) :
    ∀ lot' ∈ T.lots, ∀ b₁ ∈ lot'.blocks B.G₀, b₁.place = b₀.place → b₁ = b₀ := by
  unfold ProofFile.faultsAt at hf
  simp only [List.append_eq_nil_iff] at hf
  obtain ⟨⟨⟨⟨hf, -⟩, -⟩, -⟩, -⟩ := hf
  obtain ⟨f₁, f₃⟩ := faultsOfNil _ _ hf
  have mem : ∀ lot' ∈ T.lots, ∀ b ∈ lot'.blocks B.G₀, b ∈ B.all.flatMap fun x => x.2 := by
    intro lot' hl' b hb
    rw [hall]
    exact List.mem_flatMap.2 ⟨_, List.mem_map.2 ⟨lot', hl', rfl⟩, hb⟩
  obtain ⟨s, hs, e⟩ := f₁ b₀ (mem lot hl b₀ hb₀) hk
  intro lot' hl' b₁ hb₁ hp
  refine eqOfShort (f₃ s hs) (List.mem_filter.2 ⟨mem lot' hl' b₁ hb₁, ?_⟩)
    (List.mem_filter.2 ⟨mem lot hl b₀ hb₀, ?_⟩)
  · rw [hp, e]
    exact beq_self_eq_true _
  · rw [e]
    exact beq_self_eq_true _

omit hall in
/-- **Where the seat has no fault: a maker of a batching that a lot gives at a spot of the plan
makes a block that bears that spot's place, and the place is one at which the driver asks for the
batching.** -/
theorem faceAtBatch (hf : ProofFile.faultsAt T B = []) (p : ProofFile.Spot) (hp : p ∈ B.spots) (lot : Lot)
    (hl : lot ∈ T.lots) (mk₀ : ProofFile.Gatherer → Block S Cl)
    (h₀ : lot.batch B.G₀ p.place = some mk₀) :
    (mk₀ fun s => .ok ([], s)).place = p.place ∧ ∃ y ∈ B.batchAt, y.2 = p.place := by
  unfold ProofFile.faultsAt at hf
  simp only [List.append_eq_nil_iff, List.flatMap_eq_nil_iff] at hf
  obtain ⟨⟨⟨⟨-, -⟩, hf⟩, -⟩, -⟩ := hf
  have hp' := hf p hp
  have hg : lot ∈ T.lots.filter fun L => (L.batch B.G₀ p.place).isSome :=
    List.mem_filter.2 ⟨hl, by rw [h₀]; rfl⟩
  have hne : (T.lots.filter fun L => (L.batch B.G₀ p.place).isSome).isEmpty = false := by
    cases hh : T.lots.filter fun L => (L.batch B.G₀ p.place).isSome with
    | nil => rw [hh] at hg; exact nomatch hg
    | cons _ _ => rfl
  rw [hne] at hp'
  simp only [Bool.false_eq_true, if_false, List.append_eq_nil_iff] at hp'
  obtain ⟨⟨⟨⟨a₁, a₂⟩, -⟩, -⟩, -⟩ := hp'
  constructor
  · cases ha : (T.lots.filter fun L => (L.batch B.G₀ p.place).isSome).any fun L =>
        ((L.batch B.G₀ p.place).map fun mk =>
          (mk fun s => .ok ([], s)).place != p.place).getD false with
    | true =>
      rw [ha] at a₂
      exact absurd a₂ (by simp)
    | false =>
      have hx := List.any_eq_false.1 ha lot hg
      rw [h₀] at hx
      have hx' : ¬ ((mk₀ fun s => .ok ([], s)).place != p.place) = true := hx
      rw [bne_iff_ne, not_not] at hx'
      exact hx'
  · cases ha : B.batchAt.any fun x => x.2 == p.place with
    | true =>
      obtain ⟨y, hy, e⟩ := List.any_eq_true.1 ha
      exact ⟨y, hy, eq_of_beq e⟩
    | false =>
      rw [ha] at a₁
      exact absurd a₁ (by simp)

/-- Every block at a frame's place is `guardMark` of a lot's block of the kind "frame". -/
theorem framesCome : ∀ y ∈ (partsAt T B).frames, ∃ lot ∈ T.lots, ∃ fr ∈ lot.blocks B.G₀,
    (fr.place.kind == KindName.frame) = true ∧ y.2 = guardMark fr := by
  intro y hy
  obtain ⟨v, hv, hy⟩ := List.mem_flatMap.1 hy
  rw [hall] at hv
  obtain ⟨lot, hlot, rfl⟩ := List.mem_map.1 hv
  dsimp only at hy
  split at hy
  · exact nomatch hy
  · obtain ⟨b, hb, hby⟩ := List.mem_filterMap.1 hy
    split at hby
    · exact nomatch hby
    · exact nomatch hby
    · obtain rfl := Option.some.inj hby
      exact ⟨lot, hlot, b, (List.mem_filter.1 hb).1, (List.mem_filter.1 hb).2, rfl⟩

end Come

/-- A hearing place is of no kind "frame" and of no kind K9. -/
theorem hearKindsPlain (sub : ModelPart) (first : Bool) :
    (First.kindsBeforeBatching sub first).all (fun k => k != KindName.frame && k != KindName.K9) = true := by
  cases sub <;> cases first <;> rfl

theorem kindOfAddress (l : Option Nat) (ks : List KindName) (a : Place)
    (ha : a ∈ First.addresses l ks) : a.kind ∈ ks := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
  exact List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.1 hx)

/-- What the record H of the kinds' blocks is, beside its blocks: the seat's road and frames. OF
`H.block`, `H.first` AND `H.last` NOTHING IS SAID HERE: what a link's hearing blocks are is
`SeatedAs`'s to say; what the closing's blocks, the blocks behind the last link, the front and the
seal are is said nowhere in this file: the road does not read them. -/
structure HIs (Z : Pub) (T : PureSeat) (B : PureBase) (H : Blocks S Cl) : Prop where
  each : H.each = (partsAt T B).road.each
  tests : H.tests = (partsAt T B).road.tests
  same : H.same = T.same
  batch : ∀ a ∈ batchPlacesOf (subsOf Z), H.batch a = (partsAt T B).road.batch a
  lay : ∀ l t, H.lay l t = stepOfRole (partsAt T B).frames (.lay l) t
  clear : ∀ l t, H.clear l t = stepOfRole (partsAt T B).frames (.clear l) t

/-- A yes of the decision: the first chain's fold said yes. -/
theorem firstChainAtOfRun {Xi : Type} (F : FileDescription Xi) (x : Xi) (v₁ v₂ v₃ : Fmt.View)
    (h : F.run x v₁ v₂ v₃ = true) :
    ∃ e₁, chainAt "the first chain" 0 F.first.blocksInOrder (F.start₁ (F.pub x)) (withEmptySealRound v₁) =
      .ok e₁ := by
  unfold FileDescription.run at h
  cases hr : F.runEnd x v₁ v₂ v₃ with
  | error e => simp [hr, Except.isOk, Except.toBool] at h
  | ok r =>
    obtain ⟨e₁, e₂, e₃⟩ := r
    unfold FileDescription.runEnd at hr
    exact ⟨e₁, (ChainEnd.runCore_chains _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr).1⟩

/-- A yes of the decision: every block of the first chain's flat list passes its own test on the
plan. (By `runEndIs`: Johnson/Desc/Sound/DescRunsProofs.lean.) -/
theorem firstPlanOfRun {Xi : Type} (F : FileDescription Xi) (x : Xi) (v₁ v₂ v₃ : Fmt.View)
    (h : F.run x v₁ v₂ v₃ = true) : ∀ b ∈ F.first.blocksInOrder, b.planOk = true := by
  unfold FileDescription.run at h
  cases hr : F.runEnd x v₁ v₂ v₃ with
  | error e => simp [hr, Except.isOk, Except.toBool] at h
  | ok r =>
    obtain ⟨e₁, e₂, e₃⟩ := r
    have hp := ((Sound.runEndIs Xi F x v₁ v₂ v₃ e₁ e₂ e₃).1 hr).1
    simp only [FileDescription.planOk, FileDescription.planOkCore, Bool.and_eq_true] at hp
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, hb⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hp
    intro b hbm
    exact (Bool.and_eq_true_iff.1 (List.all_eq_true.1 hb b hbm)).1

/-- **THE ROAD AT THE DESCRIPTION OF THE KINDS' BLOCKS ALONE.** -/
theorem ranAtPureZ (hd : S → Option Forest.Heard)
    (Q : Place → S → List Fmt.RoundView → S → List Cl → S → S → Prop) (Z : Pub) (T : PureSeat)
    (F : FileDescription Inst) (h : onlineDescriptionFromPublicPart Z T = .ok F) (HL : LotsCarry (CarriesFo S.fork? hd) Q T) :
    ∃ B c A B₂ H several c₀, baseOf Z T = .ok B ∧
      F = fileDescBy T.older T.links Z A B₂ (fun s => s) (startS Z) c ∧
      firstChainWithoutReplyGuard H (subsOf Z) several = some c₀ ∧ c = c₀.guarded H.same hearsReply ∧
      HIs Z T B H ∧ (∀ L ∈ c₀.links, ∀ M ∈ L.hear, SeatedAs T B M) ∧
      (∀ (x : Inst) (v₁ v₂ v₃ : Fmt.View), F.run x v₁ v₂ v₃ = true →
        ∀ n y, foldBlocks 0 (c₀.blocksInOrder.take n) (startS Z x.pub) (withEmptySealRound v₁).rounds
            (withEmptySealRound v₁).opened = .ok y →
          foldBlocks 0 (c.blocksInOrder.take n) (startS Z x.pub) (withEmptySealRound v₁).rounds
            (withEmptySealRound v₁).opened = .ok y) ∧
      ∀ (Ls₁ Ls₂ : List (Link S Cl)) (L : Link S Cl), c₀.links = Ls₁ ++ L :: Ls₂ →
      ∀ (h₁ h₂ : List (Block S Cl)) (b : Block S Cl), L.hear = h₁ ++ b :: h₂ →
        (∀ x ∈ h₂, x.planOk = true → x.Steps (CarriesFo S.fork? hd)) →
      ∀ (x : Inst) (v₁ v₂ v₃ : Fmt.View), F.run x v₁ v₂ v₃ = true →
        ∃ y ∈ (subsOf Z).zipIdx, linkAt H y.2 y.1 = some L ∧
          ∃ m c', foldBlocks 0 (c₀.upToLink Ls₁) (startS Z x.pub) (withEmptySealRound v₁).rounds
              (withEmptySealRound v₁).opened =
              .ok (m, behindOf (c₀.upToLink Ls₁) (withEmptySealRound v₁).rounds, c') ∧
            ∃ t t₁ u₀ z u e cls,
              Traced (CarriesFo S.fork? hd) (Q (batchPlaceOf y.2 y.1)) L h₁ b 0 m
                (behindOf (c₀.upToLink Ls₁) (withEmptySealRound v₁).rounds) c' t t₁ u₀ z u e cls ∧
              RanUpTo S.fork? hd _root_.Fo.Later OnBytes.PscRun.Sized L h₁ b t₁ e cls ∧
              RanAllUpTo S.fork? hd _root_.Fo.Later OnBytes.PscRun.Sized L t₁ e cls := by
  obtain ⟨B, base, c, A, B₂, hB, hfa, -, hbase, hc, -, -, rfl⟩ := pureZIsN Z T F h
  obtain ⟨joined, Fr, hC, hG, hlay, hclear, hj⟩ := chainByIsN Z base _ _ c hc
  obtain ⟨z, several, hf⟩ := chainCIsN joined _ Fr c hC
  have hall := baseOfAll Z T B hB
  have hon := onRoadOk Z T B hB (onRoadOfMade Z T _ h)
  have maker : ∀ a ∈ batchPlacesOf (subsOf Z), ∀ mk,
      (fill joined.dropLast z Fr).batch a = some mk →
      ∃ lot ∈ T.lots, ∃ mk₀, lot.batch B.G₀ a = some mk₀ ∧
        ∃ n : String → String, mk = fun g => { guardMark (mk₀ g) with name := n (mk₀ g).name } := by
    intro a ha mk hmk
    have e : Fr.batch a = (partsAt T B).road.batch a := by rw [← hG]
    exact roadBatchIs T B a mk (e ▸ fillBatchN _ z Fr a mk (e ▸ hon a ha) hmk)
  have hM : ∀ a ∈ batchPlacesOf (subsOf Z), ∀ mk,
      (fill joined.dropLast z Fr).batch a = some mk → MakerMono mk := by
    intro a ha mk hmk f' f hff
    obtain ⟨lot, hl, mk₀, h₀, n, rfl⟩ := maker a ha mk hmk
    obtain ⟨r, u⟩ := HL.mono lot hl _ a mk₀ h₀ f' f hff
    refine ⟨r, fun s rs gs s' D => ?_⟩
    obtain ⟨t, ht, D'⟩ := bindOk (x := (mk₀ f').decide s rs gs) D
    show ((mk₀ f).decide s rs gs).bind _ = _
    rw [u s rs gs t ht]
    exact D'
  have hCalls : ∀ a ∈ batchPlacesOf (subsOf Z), ∀ mk,
      (fill joined.dropLast z Fr).batch a = some mk →
      Calls (CarriesFo S.fork? hd) (Q a) mk := by
    intro a ha mk hmk
    obtain ⟨lot, hl, mk₀, h₀, n, rfl⟩ := maker a ha mk hmk
    intro f s rs gs s' D
    exact HL.calls lot hl _ a mk₀ h₀ f s rs gs s' (yesGuardN (mk₀ f) s rs gs s' D)
  have hRuns : ∀ a b₀, a.link.isSome = true → (fill joined.dropLast z Fr).block a = some b₀ →
      b₀.RunsStep (CarriesFo S.fork? hd) := by
    intro a b₀ _ hb₀
    obtain ⟨b, hb, hx⟩ := hj b₀ (List.mem_of_mem_dropLast (fillBlockN _ z Fr a b₀ hb₀))
    obtain ⟨pl, hpl, hplb⟩ := OnBytes.Road.L5.mapM_mem _ _ _ hbase b hb
    have rb := placesRuns T B hall HL pl hpl b hplb
    rcases hx with rfl | ⟨y, hy, -, rfl⟩
    · exact rb
    · exact runsAndThen _ _ _ rb (runsGuarded _ _ _ (framesRuns T B hall HL y hy))
  obtain ⟨c₀, h₀, hcc, same, road⟩ :=
    ranAtFirstChain S.fork? hd Q _ (subsOf Z) several c hf hM hCalls hRuns
  have hIs : HIs Z T B (fill joined.dropLast z Fr) :=
    { each := by show Fr.each = _; rw [← hG]
      tests := by show Fr.tests = _; rw [← hG]
      same := by
        have e : Fr.same = (partsAt T B).road.same := by rw [← hG]
        exact e
      batch := fun a ha => by
        have e : Fr.batch a = (partsAt T B).road.batch a := by rw [← hG]
        obtain ⟨mk, hmk⟩ := Option.isSome_iff_exists.1 (hon a ha)
        show (Fr.batch a <|> _) = _
        rw [e, hmk]
        rfl
      lay := hlay
      clear := hclear }
  refine ⟨B, c, A, B₂, _, several, c₀, hB, rfl, h₀, hcc, hIs, fun L hL M hM => ?_,
    fun x v₁ v₂ v₃ Y => ?_, fun Ls₁ Ls₂ L hl h₁ h₂ b hh hs x v₁ v₂ v₃ Y => ?_⟩
  · obtain ⟨y, _, hy⟩ := First.bare_link _ (subsOf Z) several c₀ h₀ L hL
    obtain ⟨a, ha, x, hx, rfl⟩ := First.hear_of_linkAt _ y.2 y.1 L hy M hM
    obtain rfl : x.place = a :=
      eq_of_beq (List.find?_some (p := fun b : Block S Cl => b.place == a) hx)
    have hkind := List.all_eq_true.1 (hearKindsPlain y.1 (y.2 == 0)) _ (kindOfAddress _ _ _ ha)
    obtain ⟨k₁, k₂⟩ := Bool.and_eq_true_iff.1 hkind
    obtain ⟨b, hb, hxb⟩ := hj x (List.mem_of_mem_dropLast (fillBlockN _ z Fr _ x hx))
    obtain ⟨pl, hpl, hplb⟩ := OnBytes.Road.L5.mapM_mem _ _ _ hbase b hb
    have hbx : b.place = x.place := by
      rcases hxb with rfl | ⟨y', _, _, rfl⟩ <;> rfl
    rcases placesCome T B hall pl hpl b hplb with ⟨lot, hlo, b₀, hb₀, p, hp, hpp, rfl⟩ |
      ⟨p, hp, lot, hlo, mk₀, hmk, n, rfl⟩
    · have hp₀ : b₀.place = x.place := hbx
      refine ⟨lot, hlo, b₀, hb₀, hp₀, fun lot' hl' b₁ hb₁ e => ?_, p, hp, hpp.symm.trans hp₀, ?_⟩
      · exact onlyBlockAt T B hall hfa lot hlo b₀ hb₀ (by rw [hp₀]; exact k₁) lot' hl' b₁ hb₁
          (e.trans hp₀.symm)
      · rcases hxb with rfl | ⟨y', hy', hr', rfl⟩
        · exact Or.inl rfl
        · obtain ⟨lot', hl', fr, hfr, hk, e⟩ := framesCome T B hall y' hy'
          refine Or.inr ⟨y', hy', hr', lot', hl', fr, hfr, hk, e, ?_⟩
          rw [e]
          rfl
    · exfalso
      obtain ⟨e₁, yb, hyb, e₂⟩ := faceAtBatch T B hfa p hp lot hlo mk₀ hmk
      rw [(baseOfIs Z T B hB).2.2.2.2] at hyb
      obtain ⟨x', _, rfl⟩ := List.mem_map.1 hyb
      have e₃ : x.place = batchPlaceOf x'.2 x'.1 := hbx.symm.trans (e₁.trans e₂.symm)
      rw [e₃] at k₂
      exact nomatch k₂
  · obtain ⟨e₁, he⟩ := firstChainAtOfRun _ x v₁ v₂ v₃ Y
    exact same _ 0 _ e₁ _ he
  · obtain ⟨e₁, he⟩ := firstChainAtOfRun _ x v₁ v₂ v₃ Y
    have hplan := firstPlanOfRun _ x v₁ v₂ v₃ Y
    have hs' : ∀ y ∈ h₂, y.Steps (CarriesFo S.fork? hd) := fun y hy =>
      hs y hy (First.hearPlanOfGuarded _ _ c₀ L (by rw [hl]; simp) y (by rw [hh]; simp [hy])
        (hcc ▸ hplan))
    exact road Ls₁ Ls₂ L hl h₁ h₂ b hh hs' _ 0 _ e₁ _ he

end VerifiableInference.Desc.K9

#print axioms VerifiableInference.Desc.K9.yesGuardN
#print axioms VerifiableInference.Desc.K9.pureZIsN
#print axioms VerifiableInference.Desc.K9.chainByIsN
#print axioms VerifiableInference.Desc.K9.chainCIsN
#print axioms VerifiableInference.Desc.K9.fillBlockN
#print axioms VerifiableInference.Desc.K9.fillBatchN
#print axioms VerifiableInference.Desc.K9.roadBatchIs
#print axioms VerifiableInference.Desc.K9.LotsCarry.blocks
#print axioms VerifiableInference.Desc.K9.onRoadOk
#print axioms VerifiableInference.Desc.K9.baseOfIs
#print axioms VerifiableInference.Desc.K9.baseOfAll
#print axioms VerifiableInference.Desc.K9.baseOfBlank
#print axioms VerifiableInference.Desc.K9.runsGuarded
#print axioms VerifiableInference.Desc.K9.placesRuns
#print axioms VerifiableInference.Desc.K9.framesRuns
#print axioms VerifiableInference.Desc.K9.spotAtBatch
#print axioms VerifiableInference.Desc.K9.mem_onRoad
#print axioms VerifiableInference.Desc.K9.lackOnRoad
#print axioms VerifiableInference.Desc.K9.onRoadOfMade
#print axioms VerifiableInference.Desc.K9.yesAndThenN
#print axioms VerifiableInference.Desc.K9.SeatedAs.fromLots
#print axioms VerifiableInference.Desc.K9.FromLots.steps
#print axioms VerifiableInference.Desc.K9.eqOfShort
#print axioms VerifiableInference.Desc.K9.faultsOfNil
#print axioms VerifiableInference.Desc.K9.placesCome
#print axioms VerifiableInference.Desc.K9.onlyBlockAt
#print axioms VerifiableInference.Desc.K9.faceAtBatch
#print axioms VerifiableInference.Desc.K9.framesCome
#print axioms VerifiableInference.Desc.K9.hearKindsPlain
#print axioms VerifiableInference.Desc.K9.kindOfAddress
#print axioms VerifiableInference.Desc.K9.firstChainAtOfRun
#print axioms VerifiableInference.Desc.K9.firstPlanOfRun
#print axioms VerifiableInference.Desc.K9.ranAtPureZ
