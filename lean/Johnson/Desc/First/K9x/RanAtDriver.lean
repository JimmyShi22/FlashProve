-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/K9x/RanAtDriver.lean: THE ROAD "WHO PAYS K3RanAt" AT THE DRIVER's OWN FIRST CHAIN
(Johnson/Desc/First/Driver/Chain.lean: `linkAt`, `firstChainWithoutReplyGuard`, `firstChain`), for every record H of
the kinds' blocks. Theorems with their proofs. Over Block.lean.



WHY. The driver (Chain.lean) lays true links: the
kinds' blocks in `hear`, the protocol's order uncut, and K9's batching as a function of the link's
gatherer. So the road is the link's own rule (LedgerAtFo.lean), at the link as the driver makes it.

  `bare_link`: a link of `firstChainWithoutReplyGuard` is `linkAt H l sub` at a row (sub, l) of the list of parts.
  `linkAt_of_bare`: each row has its segment. `links_ne_nil`: the list of parts is not empty.
  `hear_of_linkAt`: a hearing block of `linkAt` is H's block at one of the segment's addresses, with
    that place written in. `hearSteps`, `hearRuns`, `hearAfter`: so H's laws at a place are the
    link's.
  `calls_of_linkAt`: the batching's law at H's maker is the link's.
  `hearPlanOfGuarded`: the guard leaves a hearing block's test on the plan as it is.
  **`ranAtBareChain`**: from the makers' law `Calls`, the blocks' law on their runs, and, of the
    hearing blocks behind b, that they step: at every link of the chain and every hearing block b:
    the chain's fold's yes gives the link's trace, `RanUpTo` (b's own runs) and `RanAllUpTo` (every
    run of the link's order, of whichever hearing block: RanAtChain.lean).
  **`ranAtFirstChain`**: the same from a yes of the chain BEHIND THE GUARD (`firstChain`): the trace
    speaks of the kinds' own blocks, in front of the scaffolding: a yes behind the guard is a yes
    in front of it with the same end (Johnson/Desc/Sound/GuardAtDriver.lean: firstChain_chainAt).
    AND THE FOLD OVER THE GUARDED CHAIN PASSES THROUGH THE SAME RECORDS: at every length n the fold
    over its first n blocks gives what the fold over the bare chain's first n blocks gives
    (`foldTakeSame`).

Limits. A frame's law: no error; nothing on soundness. H's laws are premises: one a kind. That a
description's first chain is `firstChain H …` at some H is not said here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.RanAtChain
import Johnson.Desc.First.Link.Law.Shape
import Johnson.Desc.First.Driver.BatchAt
import Johnson.Desc.Sound.GuardAtDriver
import Johnson.Desc.Sound.StepsThrough

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open VerifiableInference.Desc OnBytes OnBytes.Model

variable {S Cl : Type}

/-- A member of a list whose image under `some` is an image under f. -/
theorem mem_of_map_some {α β : Type} (f : α → Option β) (l : List α) (r : List β)
    (h : r.map some = l.map f) (b : β) (hb : b ∈ r) : ∃ a ∈ l, f a = some b := by
  have hm : some b ∈ l.map f := h ▸ List.mem_map.2 ⟨b, hb, rfl⟩
  obtain ⟨a, ha, e⟩ := List.mem_map.1 hm
  exact ⟨a, ha, e⟩

/-- A link of the chain in front of the scaffolding is the driver's segment at a row of the list of
parts. -/
theorem bare_link (H : Blocks S Cl) (links : List ModelPart) (several : Bool) (c₀ : Chain S Cl)
    (h₀ : firstChainWithoutReplyGuard H links several = some c₀) (L : Link S Cl) (hL : L ∈ c₀.links) :
    ∃ x ∈ links.zipIdx, linkAt H x.2 x.1 = some L :=
  mem_of_map_some _ _ _ (Shape.bareChain_shape h₀).2.2.1 L hL

/-- And each row of the list of parts has its segment. -/
theorem linkAt_of_bare (H : Blocks S Cl) (links : List ModelPart) (several : Bool) (c₀ : Chain S Cl)
    (h₀ : firstChainWithoutReplyGuard H links several = some c₀) (x : ModelPart × Nat) (hx : x ∈ links.zipIdx) :
    ∃ L, linkAt H x.2 x.1 = some L := by
  have hm : linkAt H x.2 x.1 ∈ c₀.links.map some := by
    rw [(Shape.bareChain_shape h₀).2.2.1]
    exact List.mem_map.2 ⟨x, hx, rfl⟩
  obtain ⟨L, -, hL⟩ := List.mem_map.1 hm
  exact ⟨L, hL.symm⟩

/-- The list of parts of a chain that is made is not empty: it ends with the head (`linksOk`). -/
theorem links_ne_nil (H : Blocks S Cl) (links : List ModelPart) (several : Bool) (c₀ : Chain S Cl)
    (h₀ : firstChainWithoutReplyGuard H links several = some c₀) : links ≠ [] := by
  rintro rfl
  exact nomatch h₀

/-- A hearing block of the driver's segment is H's block at one of the segment's addresses, with
that place written in. -/
theorem hear_of_linkAt (H : Blocks S Cl) (l : Nat) (sub : ModelPart) (L : Link S Cl)
    (h : linkAt H l sub = some L) (x : Block S Cl) (hx : x ∈ L.hear) :
    ∃ a ∈ addresses (some l) (kindsBeforeBatching sub (l == 0)), ∃ b₀, H.block a = some b₀ ∧
      x = { b₀ with place := a } := by
  obtain ⟨a, ha, e⟩ := mem_of_map_some _ _ _ (Shape.linkAt_shape h).2.1 x hx
  obtain ⟨b₀, hb, rfl⟩ := Option.map_eq_some_iff.1 e
  exact ⟨a, ha, b₀, hb, rfl⟩

/-- An address of a segment names that segment. -/
theorem link_of_address (l : Option Nat) (ks : List KindName) (a : Place)
    (ha : a ∈ addresses l ks) : a.link = l := by
  obtain ⟨_, _, rfl⟩ := List.mem_map.1 ha
  rfl

section Laws
variable {R : S → S → Prop} (H : Blocks S Cl) (l : Nat) (sub : ModelPart) (L : Link S Cl)
  (h : linkAt H l sub = some L)
include h

theorem hearSteps (hS : ∀ a b₀, a.link = some l → H.block a = some b₀ → b₀.Steps R) :
    ∀ x ∈ L.hear, x.Steps R := by
  intro x hx
  obtain ⟨a, ha, b₀, hb, rfl⟩ := hear_of_linkAt H l sub L h x hx
  exact stepsOfDecide b₀ _ rfl (hS a b₀ (link_of_address _ _ a ha) hb)

theorem hearRuns (hR : ∀ a b₀, a.link = some l → H.block a = some b₀ → b₀.RunsStep R) :
    ∀ x ∈ L.hear, x.RunsStep R := by
  intro x hx
  obtain ⟨a, ha, b₀, hb, rfl⟩ := hear_of_linkAt H l sub L h x hx
  exact runsOfClaims b₀ _ rfl (hR a b₀ (link_of_address _ _ a ha) hb)

theorem hearAfter (hA : ∀ a b₀, a.link = some l → H.block a = some b₀ → b₀.AfterStep R) :
    ∀ x ∈ L.hear, x.AfterStep R := by
  intro x hx
  obtain ⟨a, ha, b₀, hb, rfl⟩ := hear_of_linkAt H l sub L h x hx
  exact afterOfAfter b₀ _ rfl (hA a b₀ (link_of_address _ _ a ha) hb)

/-- The batching's law at H's maker is the link's. -/
theorem calls_of_linkAt (Q : Place → S → List Fmt.RoundView → S → List Cl → S → S → Prop)
    (hC : ∀ mk, H.batch (batchPlaceOf l sub) = some mk → Calls R (Q (batchPlaceOf l sub)) mk) :
    Calls R (Q (batchPlaceOf l sub)) L.batch := by
  obtain ⟨mk, h₁, h₂⟩ := linkAt_batch H l sub L h
  rw [h₂]
  exact callsOfDecide mk _ (fun _ => rfl) (hC mk h₁)

end Laws

/-- Where every block of the guarded chain's flat list passes its test on the plan, so does every
hearing block in front of the guard: the guard leaves that test as it is. -/
theorem hearPlanOfGuarded (same : S → S → Bool) (but : Place → Bool) (c₀ : Chain S Cl)
    (L : Link S Cl) (hL : L ∈ c₀.links) (x : Block S Cl) (hx : x ∈ L.hear)
    (h : ∀ b ∈ (c₀.guarded same but).blocksInOrder, b.planOk = true) : x.planOk = true := by
  have h₁ : x.guarded same but ∈ (L.guarded same but).blocksInOrder := by
    rw [flatIs]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_cons_of_mem _ (List.mem_map.2 ⟨x, hx, rfl⟩))))
  have h₂ : x.guarded same but ∈ (c₀.guarded same but).blocksInOrder := by
    rw [Chain.flat_eq]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_flatMap.2 ⟨L.guarded same but, List.mem_map.2 ⟨L, hL, rfl⟩, h₁⟩)))
  exact h (x.guarded same but) h₂

/-! ## The fold behind the guard passes through the same records -/

theorem eachUnderTake {l' l : List (Block S Cl)} (u : EachUnderR l' l) :
    ∀ n, EachUnderR (l'.take n) (l.take n) := by
  induction u with
  | nil => intro n; simp only [List.take_nil]; exact .nil
  | cons h _ ih =>
    intro n
    cases n with
    | zero => exact .nil
    | succ n => exact .cons h (ih n)

/-- **Where the fold over l' goes on, and l' says no more than l, member by member: at every length
n the fold over the first n blocks of l' gives what the fold over the first n blocks of l gives.**
So the records of a trace of the chain in front of the guard ARE the records through which the fold
over the guarded chain passes. -/
theorem foldTakeSame {l' l : List (Block S Cl)} (u : EachUnderR l' l) {ft : Nat} {s : S}
    {rs : List Fmt.RoundView} {cols : List Col} {out : S × List Fmt.RoundView × List Col}
    (Y : foldBlocks ft l' s rs cols = .ok out) (n : Nat) (y : S × List Fmt.RoundView × List Col)
    (P : foldBlocks ft (l.take n) s rs cols = .ok y) :
    foldBlocks ft (l'.take n) s rs cols = .ok y := by
  rw [← List.take_append_drop n l'] at Y
  obtain ⟨m, c', -, P', -⟩ := foldAt S Cl (fun _ _ => True) preTrue ft (l'.take n) _ s rs cols out
    (fun _ _ _ _ _ _ _ => trivial) Y
  have e := (fold_under (eachUnderTake u n) P').symm.trans P
  rw [P']
  exact e

/-- **The road at the driver's chain, in front of the scaffolding.** -/
theorem ranAtBareChain (fork : S → Option Fork) (heard : S → Option Forest.Heard)
    (Q : Place → S → List Fmt.RoundView → S → List Cl → S → S → Prop) (H : Blocks S Cl)
    (links : List ModelPart) (several : Bool) (c₀ : Chain S Cl)
    (h₀ : firstChainWithoutReplyGuard H links several = some c₀)
    (hC : ∀ a ∈ batchPlacesOf links, ∀ mk, H.batch a = some mk →
      Calls (CarriesFo fork heard) (Q a) mk)
    (hR : ∀ a b₀, a.link.isSome = true → H.block a = some b₀ →
      b₀.RunsStep (CarriesFo fork heard))
    (Ls₁ Ls₂ : List (Link S Cl)) (L : Link S Cl) (hl : c₀.links = Ls₁ ++ L :: Ls₂)
    (h₁ h₂ : List (Block S Cl)) (b : Block S Cl) (hh : L.hear = h₁ ++ b :: h₂)
    (hs : ∀ x ∈ h₂, x.Steps (CarriesFo fork heard))
    (ft : Nat) (s : S) (rs : List Fmt.RoundView) (cols : List Col) (out : S × List Fmt.RoundView × List Col)
    (Y : foldBlocks ft c₀.blocksInOrder s rs cols = .ok out) :
    ∃ x ∈ links.zipIdx, linkAt H x.2 x.1 = some L ∧
      ∃ m c', foldBlocks ft (c₀.upToLink Ls₁) s rs cols =
          .ok (m, behindOf (c₀.upToLink Ls₁) rs, c') ∧
        ∃ t t₁ u₀ z u e cls,
          Traced (CarriesFo fork heard) (Q (batchPlaceOf x.2 x.1)) L h₁ b ft m
            (behindOf (c₀.upToLink Ls₁) rs) c' t t₁ u₀ z u e cls ∧
          RanUpTo fork heard _root_.Fo.Later OnBytes.PscRun.Sized L h₁ b t₁ e cls ∧
          RanAllUpTo fork heard _root_.Fo.Later OnBytes.PscRun.Sized L t₁ e cls := by
  have hL : L ∈ c₀.links := by
    rw [hl]
    simp
  obtain ⟨x, hx, e⟩ := bare_link H links several c₀ h₀ L hL
  refine ⟨x, hx, e, ?_⟩
  have hcalls := calls_of_linkAt (R := CarriesFo fork heard) H x.2 x.1 L e Q
    (hC _ (List.mem_map.2 ⟨x, hx, rfl⟩))
  exact ranAtChainFo fork heard _ c₀ Ls₁ Ls₂ L hl h₁ h₂ b hh hs
    (hearRuns H x.2 x.1 L e fun a b₀ ha hb => hR a b₀ (by rw [ha]; rfl) hb)
    (callsAtOfCalls _ _ _ _ _ hcalls _) ft s rs cols out Y

/-- **The road at the driver's first chain**: from a yes behind the guard. -/
theorem ranAtFirstChain (fork : S → Option Fork) (heard : S → Option Forest.Heard)
    (Q : Place → S → List Fmt.RoundView → S → List Cl → S → S → Prop) (H : Blocks S Cl)
    (links : List ModelPart) (several : Bool) (c : Chain S Cl)
    (hc : firstChain H links several = some c)
    (hM : ∀ a ∈ batchPlacesOf links, ∀ mk, H.batch a = some mk → MakerMono mk)
    (hC : ∀ a ∈ batchPlacesOf links, ∀ mk, H.batch a = some mk →
      Calls (CarriesFo fork heard) (Q a) mk)
    (hR : ∀ a b₀, a.link.isSome = true → H.block a = some b₀ →
      b₀.RunsStep (CarriesFo fork heard)) :
    ∃ c₀, firstChainWithoutReplyGuard H links several = some c₀ ∧ c = c₀.guarded H.same hearsReply ∧
      (∀ (name : String) (ft : Nat) (s e₁ : S) (v : Fmt.View),
        chainAt name ft c.blocksInOrder s v = .ok e₁ →
        ∀ n y, foldBlocks ft (c₀.blocksInOrder.take n) s v.rounds v.opened = .ok y →
          foldBlocks ft (c.blocksInOrder.take n) s v.rounds v.opened = .ok y) ∧
      ∀ (Ls₁ Ls₂ : List (Link S Cl)) (L : Link S Cl), c₀.links = Ls₁ ++ L :: Ls₂ →
      ∀ (h₁ h₂ : List (Block S Cl)) (b : Block S Cl), L.hear = h₁ ++ b :: h₂ →
        (∀ x ∈ h₂, x.Steps (CarriesFo fork heard)) →
      ∀ (name : String) (ft : Nat) (s e₁ : S) (v : Fmt.View),
        chainAt name ft c.blocksInOrder s v = .ok e₁ →
        ∃ x ∈ links.zipIdx, linkAt H x.2 x.1 = some L ∧
          ∃ m c', foldBlocks ft (c₀.upToLink Ls₁) s v.rounds v.opened =
              .ok (m, behindOf (c₀.upToLink Ls₁) v.rounds, c') ∧
            ∃ t t₁ u₀ z u e cls,
              Traced (CarriesFo fork heard) (Q (batchPlaceOf x.2 x.1)) L h₁ b ft m
                (behindOf (c₀.upToLink Ls₁) v.rounds) c' t t₁ u₀ z u e cls ∧
              RanUpTo fork heard _root_.Fo.Later OnBytes.PscRun.Sized L h₁ b t₁ e cls ∧
              RanAllUpTo fork heard _root_.Fo.Later OnBytes.PscRun.Sized L t₁ e cls := by
  obtain ⟨c₀, h₀, rfl⟩ := firstChain_some hc
  refine ⟨c₀, h₀, rfl, fun name ft s e₁ v Y n y P => foldTakeSame
      (Chain.guarded_flat_under H.same hearsReply c₀ (bare_batchMono h₀ hM)) (chainAtOk Y) n y P,
    fun Ls₁ Ls₂ L hl h₁ h₂ b hh hs name ft s e₁ v Y => ?_⟩
  exact ranAtBareChain fork heard Q H links several c₀ h₀ hC hR Ls₁ Ls₂ L hl h₁ h₂ b hh hs ft s _ _
    _ (chainAtOk (firstChain_chainAt hc h₀ hM Y))

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.mem_of_map_some
#print axioms VerifiableInference.Desc.First.bare_link
#print axioms VerifiableInference.Desc.First.linkAt_of_bare
#print axioms VerifiableInference.Desc.First.links_ne_nil
#print axioms VerifiableInference.Desc.First.hear_of_linkAt
#print axioms VerifiableInference.Desc.First.link_of_address
#print axioms VerifiableInference.Desc.First.hearSteps
#print axioms VerifiableInference.Desc.First.hearRuns
#print axioms VerifiableInference.Desc.First.hearAfter
#print axioms VerifiableInference.Desc.First.calls_of_linkAt
#print axioms VerifiableInference.Desc.First.hearPlanOfGuarded
#print axioms VerifiableInference.Desc.First.eachUnderTake
#print axioms VerifiableInference.Desc.First.foldTakeSame
#print axioms VerifiableInference.Desc.First.ranAtBareChain
#print axioms VerifiableInference.Desc.First.ranAtFirstChain
