-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Law/Skel/SkelRounds.lean: THE ROUNDS' COLUMN, THE DRIVER's PART: WHAT HOLDS
OF THE NAME AND THE ROUNDS OF EVERY SUPPLIED BLOCK HOLDS OF EVERY BLOCK OF THE CHAIN's FLAT LIST.
Definitions, statements and proofs. General in the state; to `chainC` also in the type of claims.
Why. A skeleton (Skel.lean) holds how many rounds a block has, not the rounds. The driver and
`chainBy` (ProofFile/Frames1.lean) move rounds about in three ways alone: they keep a block's, with
its name; they append those of a frame that is joined behind a block; they lay blocks without a
round.
  `Good Q b`      Q holds of b's name and b's rounds
  `LinkGood`, `ChainGood`; `link_flat_good`, `chain_flat_good`: under "Q holds of every name and no
                  round", from the parts to the flat list
  `link_guarded_good`, `chain_guarded_good`: the guard turns neither
  `optAll`, `mapM_all`; `HGood`; `blockAt_good` … `firstChain_good`
  `chainC_good`   from the supplied blocks, the batchings at every gatherer and the first block.
                  A BATCHING IS ASKED ONLY WHERE A LETTER A : Place → Prop HOLDS: hA: A holds at
                  `askAt l sub`, the one place at which `linkAt` asks, at each segment of the list
  `chainBy_good`, `chainBy_flat_good`: and where no supplied frame has a round
Limits. Q is a letter: nothing is said of any block's rounds. Nothing on soundness.

-/
import Johnson.Desc.ProofFile.Law.Skel.Skel
import Johnson.Desc.ProofFile.Frames1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Sk
open VerifiableInference.Desc
open VerifiableInference.Desc.First

variable {S Cl : Type}

/-- Q holds of the block's name and rounds. -/
def Good (Q : String → List Fmt.DeclaredRound → Prop) (b : Block S Cl) : Prop := Q b.name b.rounds

section
variable (Q : String → List Fmt.DeclaredRound → Prop)

structure LinkGood (L : Link S Cl) : Prop where
  hear : ∀ b ∈ L.hear, Good Q b
  batch : ∀ g, Good Q (L.batch g)
  close : ∀ b ∈ L.close, Good Q b

structure ChainGood (c : Chain S Cl) : Prop where
  first : Good Q c.first
  front : ∀ b ∈ c.front, Good Q b
  links : ∀ L ∈ c.links, LinkGood Q L
  back : ∀ b ∈ c.back, Good Q b
  last : Good Q c.last

theorem link_flat_good (hQ : ∀ n, Q n []) {L : Link S Cl} (h : LinkGood Q L) :
    ∀ b ∈ L.blocksInOrder, Good Q b := by
  intro b hb
  unfold Link.blocksInOrder at hb
  rcases List.mem_append.1 hb with hb | hb
  · rcases List.mem_append.1 hb with hb | hb
    · rcases List.mem_append.1 hb with hb | hb
      · rcases List.mem_cons.1 hb with rfl | hb
        · exact hQ _
        · exact h.hear b hb
      · rcases List.mem_cons.1 hb with rfl | hb
        · exact h.batch _
        · rcases List.mem_cons.1 hb with rfl | hb
          · exact hQ _
          · cases hb
    · exact h.close b hb
  · rcases List.mem_cons.1 hb with rfl | hb
    · exact hQ _
    · cases hb

theorem chain_flat_good (hQ : ∀ n, Q n []) {c : Chain S Cl} (h : ChainGood Q c) :
    ∀ b ∈ c.blocksInOrder, Good Q b := by
  intro b hb
  unfold Chain.blocksInOrder at hb
  dsimp only at hb
  rcases List.mem_append.1 hb with hb | hb
  · rcases List.mem_append.1 hb with hb | hb
    · rcases List.mem_append.1 hb with hb | hb
      · rcases List.mem_cons.1 hb with rfl | hb
        · exact h.first
        · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb
          exact h.front x hx
      · obtain ⟨L, hL, hb⟩ := List.mem_flatMap.1 hb
        exact link_flat_good Q hQ (h.links L hL) b hb
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb
      exact h.back x hx
  · rcases List.mem_cons.1 hb with rfl | hb
    · exact h.last
    · cases hb

theorem link_guarded_good (same : S → S → Bool) (but : Place → Bool) {L : Link S Cl}
    (h : LinkGood Q L) : LinkGood Q (L.guarded same but) := by
  refine ⟨fun b hb => ?_, fun g => h.batch g, fun b hb => ?_⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb
    exact h.hear x hx
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb
    exact h.close x hx

theorem chain_guarded_good (same : S → S → Bool) (but : Place → Bool) {c : Chain S Cl}
    (h : ChainGood Q c) : ChainGood Q (c.guarded same but) := by
  refine ⟨h.first, fun b hb => ?_, fun L hL => ?_, fun b hb => ?_, h.last⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb
    exact h.front x hx
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hL
    exact link_guarded_good Q same but (h.links x hx)
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb
    exact h.back x hx

end

/-! ### the driver -/

/-- None, or some and P. -/
def optAll {α : Type} (P : α → Prop) : Option α → Prop
  | some a => P a
  | none => True

theorem mapM_all {α β : Type} (P : β → Prop) (f : α → Option β) (h : ∀ a, optAll P (f a)) :
    ∀ l : List α, optAll (fun ys => ∀ y ∈ ys, P y) (l.mapM f)
  | [] => by
    simp only [List.mapM_nil]
    show ∀ y ∈ ([] : List β), P y
    intro y hy
    cases hy
  | a :: l => by
    have h1 := h a
    have h2 := mapM_all P f h l
    rw [List.mapM_cons]
    cases e1 : f a with
    | none => exact trivial
    | some b =>
      rw [e1] at h1
      cases e2 : l.mapM f with
      | none => exact trivial
      | some bs =>
        rw [e2] at h2
        show ∀ y ∈ b :: bs, P y
        intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact h1
        · exact h2 y hy

theorem mapM_all_mem {α β : Type} (P : β → Prop) (f : α → Option β) :
    ∀ l : List α, (∀ a ∈ l, optAll P (f a)) → optAll (fun ys => ∀ y ∈ ys, P y) (l.mapM f)
  | [], _ => by
    simp only [List.mapM_nil]
    show ∀ y ∈ ([] : List β), P y
    intro y hy
    cases hy
  | a :: l, h => by
    have h1 := h a (List.mem_cons_self ..)
    have h2 := mapM_all_mem P f l fun x hx => h x (List.mem_cons_of_mem _ hx)
    rw [List.mapM_cons]
    cases e1 : f a with
    | none => exact trivial
    | some b =>
      rw [e1] at h1
      cases e2 : l.mapM f with
      | none => exact trivial
      | some bs =>
        rw [e2] at h2
        show ∀ y ∈ b :: bs, P y
        intro y hy
        rcases List.mem_cons.1 hy with rfl | hy
        · exact h1
        · exact h2 y hy

/-- The one place at which `linkAt` asks for a batching, at the segment number l of the sort sub. -/
def askAt (l : Nat) (sub : ModelPart) : Place :=
  { chain := 1, link := some l, piece := (kindsBeforeBatching sub (l == 0)).length + 1, kind := .K9 }

section
variable (Q : String → List Fmt.DeclaredRound → Prop) (A : Place → Prop)

/-- What the driver is supplied with is good; a batching where A holds. -/
structure HGood (H : Blocks S Cl) : Prop where
  block : ∀ a b, H.block a = some b → Good Q b
  batch : ∀ a mk, A a → H.batch a = some mk → ∀ g, Good Q (mk g)
  first : Good Q H.first
  last : Good Q H.last

variable {Q A}

theorem blockAt_good {H : Blocks S Cl} (G : HGood Q A H) (a : Place) :
    optAll (Good Q) (blockAt H a) := by
  unfold blockAt
  cases e : H.block a with
  | none => exact trivial
  | some b => exact G.block a b e

theorem linkAt_good {H : Blocks S Cl} (G : HGood Q A H) (l : Nat) (sub : ModelPart)
    (hA : A (askAt l sub)) : optAll (LinkGood Q) (linkAt H l sub) := by
  have h1 := mapM_all _ _ (blockAt_good G) (addresses (some l) (kindsBeforeBatching sub (l == 0)))
  have h3 := mapM_all _ _ (blockAt_good G) (closeAddresses l (kindsBeforeBatching sub (l == 0)).length)
  unfold linkAt
  dsimp only
  cases e1 : (addresses (some l) (kindsBeforeBatching sub (l == 0))).mapM (blockAt H) with
  | none => exact trivial
  | some hear =>
    rw [e1] at h1
    cases e2 : H.batch
        { chain := 1, link := some l, piece := (kindsBeforeBatching sub (l == 0)).length + 1,
          kind := .K9 } with
    | none => exact trivial
    | some mk =>
      cases e3 : (closeAddresses l (kindsBeforeBatching sub (l == 0)).length).mapM (blockAt H) with
      | none => exact trivial
      | some close =>
        rw [e3] at h3
        show LinkGood Q _
        exact ⟨h1, fun g => G.batch _ mk hA e2 g, h3⟩

theorem bareChain_good {H : Blocks S Cl} (G : HGood Q A H) (links : List ModelPart) (several : Bool)
    (hA : ∀ x ∈ links.zipIdx, A (askAt x.2 x.1)) :
    optAll (ChainGood Q) (firstChainWithoutReplyGuard H links several) := by
  have h1 := mapM_all_mem (LinkGood Q) (fun x : ModelPart × Nat => linkAt H x.2 x.1) links.zipIdx
    fun x hx => linkAt_good G x.2 x.1 (hA x hx)
  have h2 := mapM_all _ _ (blockAt_good G) (addresses none (backKinds several))
  unfold firstChainWithoutReplyGuard
  cases hl : linksOk links
  · exact trivial
  cases e1 : links.zipIdx.mapM (fun x : ModelPart × Nat => linkAt H x.2 x.1) with
  | none => exact trivial
  | some ls =>
    rw [e1] at h1
    cases e2 : (addresses none (backKinds several)).mapM (blockAt H) with
    | none => exact trivial
    | some back =>
      rw [e2] at h2
      show ChainGood Q _
      exact ⟨G.first, (fun _ hb => by cases hb), h1, h2, G.last⟩

theorem firstChain_good {H : Blocks S Cl} (G : HGood Q A H) (links : List ModelPart) (several : Bool)
    (hA : ∀ x ∈ links.zipIdx, A (askAt x.2 x.1)) :
    optAll (ChainGood Q) (firstChain H links several) := by
  have h := bareChain_good G links several hA
  unfold firstChain
  cases e : firstChainWithoutReplyGuard H links several with
  | none => exact trivial
  | some c =>
    rw [e] at h
    exact chain_guarded_good Q _ _ h

/-! ### chainC and chainBy -/

theorem fill_good {bs : List (Block S Cl)} {z : Block S Cl} {fr : Frames S Cl}
    (hb : ∀ b ∈ bs, Good Q b) (hz : Good Q z)
    (hr : ∀ a mk, A a → fr.batch a = some mk → ∀ g, Good Q (mk g))
    (hf : Good Q fr.first) :
    HGood Q A (fill bs z fr) := by
  refine ⟨fun a b h => hb b (List.mem_of_find?_eq_some h), fun a mk hc h g => ?_, hf, hz⟩
  have h' : (fr.batch a <|> (bs.find? fun b => b.place == a).map fun b _ => b) = some mk := h
  cases e : fr.batch a with
  | some mk' =>
    rw [e] at h'
    cases h'
    exact hr a _ hc e g
  | none =>
    rw [e] at h'
    cases e2 : bs.find? fun b => b.place == a with
    | none =>
      rw [e2] at h'
      cases h'
    | some b =>
      rw [e2] at h'
      cases h'
      exact hb b (List.mem_of_find?_eq_some e2)

theorem chainC_good {bs : List (Block S Cl)} {links : List ModelPart} {fr : Frames S Cl}
    {c : Chain S Cl} (hb : ∀ b ∈ bs, Good Q b)
    (hr : ∀ a mk, A a → fr.batch a = some mk → ∀ g, Good Q (mk g))
    (hf : Good Q fr.first) (hA : ∀ x ∈ links.zipIdx, A (askAt x.2 x.1)) :
    chainC bs links fr = .ok c → ChainGood Q c := by
  unfold chainC
  cases hz : bs.getLast? with
  | none =>
    intro h
    cases h
  | some z =>
    dsimp only
    have hzm : z ∈ bs := List.mem_of_getLast? hz
    have g := firstChain_good
      (fill_good (fun b h => hb b (List.mem_of_mem_dropLast h)) (hb z hzm) hr hf) links
      (bs.any fun b => b.place.kind == KindName.K13) hA
    cases e : firstChain (fill bs.dropLast z fr) links
        (bs.any fun b => b.place.kind == KindName.K13) with
    | none =>
      intro h
      cases h
    | some c' =>
      rw [e] at g
      dsimp only
      cases bs.find? _ with
      | some b =>
        intro h
        cases h
      | none =>
        intro h
        cases h
        exact g

theorem chainBy_good (hQ : ∀ n, Q n []) {Z : Pub} {base : List (Block S ProofFile.Cl)}
    {fr : List (FrameRole × Block S ProofFile.Cl)} {road : Gather S ProofFile.Cl} {c : Chain S ProofFile.Cl}
    (hb : ∀ b ∈ base, Good Q b) (hfr : ∀ x ∈ fr, x.2.rounds = [])
    (hr : ∀ a mk, A a → road.batch a = some mk → ∀ g, Good Q (mk g))
    (hA : ∀ x ∈ (subsOf Z).zipIdx, A (askAt x.2 x.1))
    (h : chainBy Z base fr road = .ok c) : ChainGood Q c := by
  unfold chainBy at h
  dsimp only at h
  refine chainC_good (fun b hbm => ?_) hr ?_ hA h
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hbm
    split
    · rename_i y hy
      show Q x.name (x.rounds ++ y.2.rounds)
      rw [hfr y (List.mem_of_find?_eq_some hy), List.append_nil]
      exact hb x hx
    · exact hb x hx
  · show Good Q (match (fr.find? fun x => x.1 == FrameRole.front).map fun x => x.2 with
      | some o => { o with name := frontName }
      | none => idleFront)
    cases e : fr.find? fun x => x.1 == FrameRole.front with
    | none => exact hQ _
    | some y =>
      show Q frontName y.2.rounds
      rw [hfr y (List.mem_of_find?_eq_some e)]
      exact hQ _

theorem chainBy_flat_good (hQ : ∀ n, Q n []) {Z : Pub} {base : List (Block S ProofFile.Cl)}
    {fr : List (FrameRole × Block S ProofFile.Cl)} {road : Gather S ProofFile.Cl} {c : Chain S ProofFile.Cl}
    (hb : ∀ b ∈ base, Good Q b) (hfr : ∀ x ∈ fr, x.2.rounds = [])
    (hr : ∀ a mk, A a → road.batch a = some mk → ∀ g, Good Q (mk g))
    (hA : ∀ x ∈ (subsOf Z).zipIdx, A (askAt x.2 x.1))
    (h : chainBy Z base fr road = .ok c) : ∀ b ∈ c.blocksInOrder, Good Q b :=
  chain_flat_good Q hQ (chainBy_good hQ hb hfr hr hA h)

end

end ProofFile.Sk

#print axioms ProofFile.Sk.link_flat_good
#print axioms ProofFile.Sk.chain_flat_good
#print axioms ProofFile.Sk.link_guarded_good
#print axioms ProofFile.Sk.chain_guarded_good
#print axioms ProofFile.Sk.mapM_all
#print axioms ProofFile.Sk.mapM_all_mem
#print axioms ProofFile.Sk.blockAt_good
#print axioms ProofFile.Sk.linkAt_good
#print axioms ProofFile.Sk.bareChain_good
#print axioms ProofFile.Sk.firstChain_good
#print axioms ProofFile.Sk.fill_good
#print axioms ProofFile.Sk.chainC_good
#print axioms ProofFile.Sk.chainBy_good
#print axioms ProofFile.Sk.chainBy_flat_good
