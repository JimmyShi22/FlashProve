-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFPol/SkR/SkelChain.lean: A TWIN, MADE BY PROGRAM, of
Johnson/Desc/ProofFile/Law/Skel/SkelChain.lean: that file's text with two fields more in the
skeleton: a block's rounds and its oracles, whole. The namespace is LPFPol.SkR. What follows is that
file's own head, less its labels; two docstrings that are a label alone there have words here.
THE DRIVER's CHAIN READS SKELETONS ALONE:
`firstChain` (Johnson/Desc/First/Driver/Chain.lean), `chainC` (ProofFile/FillCore.lean) and
`chainBy` (ProofFile/Frames1.lean) return just where their texts on skeletons return, with the
same words of refusal, and the returned chain's flat list has the skeletons that these give.
Definitions, statements and proofs. General in the state; `firstChain`'s law also in the type of
claims.
  `BlocksSk`, `blockAtSk`, `linkAtSk`, `bareChainSk`: the driver's texts on skeletons
  `Fits H K`: K holds the skeletons of what H supplies; THE BATCHING's AT EVERY GATHERER
  `LinkFits`, `ChainFits`; `flat_fits`, `link_guarded`, `chain_guarded`
  `firstChain_skel`
  `fillSk`, `chainCSk`, `chainC_skel`
  `behindSk`, `chainBySk`, `chainBy_skel`
Limits. No return is shown. That a batching's skeleton is the same at every gatherer is a premise.
Nothing on soundness.

-/
import Johnson.LPFPol.SkR.Skel
import Johnson.Desc.ProofFile.Frames1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFPol.SkR
open ProofFile
open VerifiableInference.Desc
open VerifiableInference.Desc.First

variable {S Cl : Type}

/-! ### two options, two lists -/

/-- Both are none, or both are some and related. -/
def optRel {α β : Type} (R : α → β → Prop) : Option α → Option β → Prop
  | some a, some b => R a b
  | none, none => True
  | _, _ => False

theorem mapM_rel {α β γ : Type} (R : β → γ → Prop) (f : α → Option β) (f' : α → Option γ)
    (h : ∀ a, optRel R (f a) (f' a)) :
    ∀ l : List α, optRel (List.Forall₂ R) (l.mapM f) (l.mapM f')
  | [] => by
    simp only [List.mapM_nil]
    exact List.Forall₂.nil
  | a :: l => by
    have h1 := h a
    have h2 := mapM_rel R f f' h l
    rw [List.mapM_cons, List.mapM_cons]
    cases e1 : f a <;> cases e1' : f' a <;> rw [e1, e1'] at h1 <;>
      cases e2 : l.mapM f <;> cases e2' : l.mapM f' <;> rw [e2, e2'] at h2 <;>
      first
        | exact h1.elim
        | exact h2.elim
        | exact trivial
        | exact List.Forall₂.cons h1 h2

theorem forall₂_skel {bs : List (Block S Cl)} {ks : List Skel}
    (h : List.Forall₂ (fun b k => skel b = k) bs ks) : bs.map skel = ks := by
  induction h with
  | nil => rfl
  | cons h1 _ ih => rw [List.map_cons, h1, ih]

/-! ### the driver on skeletons -/

/-- `Blocks` less its functions. -/
structure BlocksSk where
  block : Place → Option Skel
  batch : Place → Option Skel
  first : Skel
  last : Skel

def blockAtSk (H : BlocksSk) (a : Place) : Option Skel :=
  (H.block a).map fun k => { k with place := a }

def linkAtSk (H : BlocksSk) (l : Nat) (sub : ModelPart) : Option LinkSk := do
  let ks := kindsBeforeBatching sub (l == 0)
  let hear ← (addresses (some l) ks).mapM (blockAtSk H)
  let a9 : Place := { chain := 1, link := some l, piece := ks.length + 1, kind := .K9 }
  let batch ← H.batch a9
  let close ← (closeAddresses l ks.length).mapM (blockAtSk H)
  pure { name := s!"link {l}", chain := 1, number := l, hear := hear, order := orderOf sub
         orderAfter := orderAfterOf sub, batch := { batch with place := a9 }, close := close }

def bareChainSk (H : BlocksSk) (links : List ModelPart) (several : Bool) : Option ChainSk := do
  if !linksOk links then none
  let ls ← links.zipIdx.mapM fun x => linkAtSk H x.2 x.1
  let back ← (addresses none (backKinds several)).mapM (blockAtSk H)
  let aS : Place := { chain := 1, link := none, piece := back.length + 1, kind := .frame }
  let aF : Place := { chain := 1, link := none, piece := 0, kind := .frame }
  pure { first := { H.first with place := aF }, front := [], links := ls, back := back
         last := { H.last with place := aS } }

/-- K holds the skeletons of what H supplies. -/
structure Fits (H : Blocks S Cl) (K : BlocksSk) : Prop where
  block : ∀ a, (H.block a).map skel = K.block a
  batch : ∀ a g, (H.batch a).map (fun mk => skel (mk g)) = K.batch a
  first : skel H.first = K.first
  last : skel H.last = K.last

/-- M holds the skeletons of the link L; the batching's at every gatherer. -/
def LinkFits (L : Link S Cl) (M : LinkSk) : Prop :=
  (∀ g, skel (L.batch g) = M.batch) ∧ linkSk L M.batch = M

/-- M holds the skeletons of the chain c. -/
structure ChainFits (c : Chain S Cl) (M : ChainSk) : Prop where
  first : skel c.first = M.first
  front : c.front.map skel = M.front
  links : List.Forall₂ LinkFits c.links M.links
  back : c.back.map skel = M.back
  last : skel c.last = M.last

theorem blockAt_skel {H : Blocks S Cl} {K : BlocksSk} (F : Fits H K) (a : Place) :
    optRel (fun b k => skel b = k) (blockAt H a) (blockAtSk K a) := by
  unfold blockAt blockAtSk
  rw [← F.block a]
  cases H.block a with
  | none => exact trivial
  | some b => exact rfl

theorem linkAt_skel {H : Blocks S Cl} {K : BlocksSk} (F : Fits H K) (l : Nat) (sub : ModelPart) :
    optRel LinkFits (linkAt H l sub) (linkAtSk K l sub) := by
  have h1 := mapM_rel _ _ _ (blockAt_skel F) (addresses (some l) (kindsBeforeBatching sub (l == 0)))
  have h3 := mapM_rel _ _ _ (blockAt_skel F) (closeAddresses l (kindsBeforeBatching sub (l == 0)).length)
  have h2 := F.batch
    { chain := 1, link := some l, piece := (kindsBeforeBatching sub (l == 0)).length + 1, kind := .K9 }
  unfold linkAt linkAtSk
  dsimp only
  cases e1 : (addresses (some l) (kindsBeforeBatching sub (l == 0))).mapM (blockAt H) <;>
    cases e1' : (addresses (some l) (kindsBeforeBatching sub (l == 0))).mapM (blockAtSk K) <;>
    rw [e1, e1'] at h1
  · exact trivial
  · exact h1.elim
  · exact h1.elim
  rename_i hear hear'
  cases e2 : H.batch
      { chain := 1, link := some l, piece := (kindsBeforeBatching sub (l == 0)).length + 1, kind := .K9 } <;>
    cases e2' : K.batch
      { chain := 1, link := some l, piece := (kindsBeforeBatching sub (l == 0)).length + 1, kind := .K9 } <;>
    rw [e2, e2'] at h2
  · exact trivial
  · have h := h2 fun s => .ok ([], s)
    simp at h
  · have h := h2 fun s => .ok ([], s)
    simp at h
  rename_i mk kb
  cases e3 : (closeAddresses l (kindsBeforeBatching sub (l == 0)).length).mapM (blockAt H) <;>
    cases e3' : (closeAddresses l (kindsBeforeBatching sub (l == 0)).length).mapM (blockAtSk K) <;>
    rw [e3, e3'] at h3
  · exact trivial
  · exact h3.elim
  · exact h3.elim
  rename_i close close'
  show LinkFits _ _
  refine ⟨fun g => ?_, ?_⟩
  · have := Option.some.inj (h2 g)
    show skel { mk g with place := _ } = { kb with place := _ }
    rw [← this]
    rfl
  · show linkSk _ _ = _
    unfold linkSk
    simp only [forall₂_skel h1, forall₂_skel h3]

theorem bareChain_skel {H : Blocks S Cl} {K : BlocksSk} (F : Fits H K) (links : List ModelPart)
    (several : Bool) :
    optRel ChainFits (firstChainWithoutReplyGuard H links several) (bareChainSk K links several) := by
  have h1 := mapM_rel LinkFits (fun x : ModelPart × Nat => linkAt H x.2 x.1)
    (fun x => linkAtSk K x.2 x.1) (fun x => linkAt_skel F x.2 x.1) links.zipIdx
  have h2 := mapM_rel _ _ _ (blockAt_skel F) (addresses none (backKinds several))
  unfold firstChainWithoutReplyGuard bareChainSk
  cases hl : linksOk links
  · exact trivial
  cases e1 : links.zipIdx.mapM (fun x : ModelPart × Nat => linkAt H x.2 x.1) <;>
    cases e1' : links.zipIdx.mapM (fun x : ModelPart × Nat => linkAtSk K x.2 x.1) <;>
    rw [e1, e1'] at h1
  · exact trivial
  · exact h1.elim
  · exact h1.elim
  cases e2 : (addresses none (backKinds several)).mapM (blockAt H) <;>
    cases e2' : (addresses none (backKinds several)).mapM (blockAtSk K) <;>
    rw [e2, e2'] at h2
  · exact trivial
  · exact h2.elim
  · exact h2.elim
  rename_i ls ls' back back'
  have hb := forall₂_skel h2
  have hn : back.length = back'.length := by rw [← hb, List.length_map]
  exact ⟨by show skel { H.first with place := _ } = _; rw [← F.first]; rfl, rfl, h1, hb,
    by show skel { H.last with place := _ } = _; rw [← F.last, hn]; rfl⟩

/-! ### flat lists -/

theorem links_flat {ls : List (Link S Cl)} {Ms : List LinkSk} (h : List.Forall₂ LinkFits ls Ms) :
    ls.map (fun L => L.blocksInOrder.map skel) = Ms.map LinkSk.flat := by
  induction h with
  | nil => rfl
  | cons h1 _ ih =>
    rw [List.map_cons, List.map_cons, ih, flat_link _ _ (h1.1 _), h1.2]

theorem flat_fits {c : Chain S Cl} {M : ChainSk} (h : ChainFits c M) :
    c.blocksInOrder.map skel = M.flat := by
  rw [flat_chain c M.links (links_flat h.links)]
  unfold chainSk
  rw [h.first, h.front, h.back, h.last]

theorem link_guarded {L : Link S Cl} {M : LinkSk} (same : S → S → Bool) (but : Place → Bool)
    (h : LinkFits L M) : LinkFits (L.guarded same but) M := by
  refine ⟨fun g => ?_, ?_⟩
  · show skel ((L.batch g).guarded same but) = _
    rw [skel_guarded, h.1]
  · have e := h.2
    unfold linkSk at e ⊢
    rw [← e]
    simp [Link.guarded, List.map_map, Function.comp_def, skel_guarded]

theorem links_guarded {ls : List (Link S Cl)} {Ms : List LinkSk} (same : S → S → Bool)
    (but : Place → Bool) (h : List.Forall₂ LinkFits ls Ms) :
    List.Forall₂ LinkFits (ls.map (Link.guarded same but)) Ms := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons h1 _ ih => exact List.Forall₂.cons (link_guarded same but h1) ih

theorem chain_guarded {c : Chain S Cl} {M : ChainSk} (same : S → S → Bool) (but : Place → Bool)
    (h : ChainFits c M) : ChainFits (c.guarded same but) M := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show skel (c.first.guarded same but) = _
    rw [skel_guarded, h.first]
  · show (c.front.map (Block.guarded same but)).map skel = _
    rw [← h.front]
    simp [List.map_map, Function.comp_def, skel_guarded]
  · exact links_guarded same but h.links
  · show (c.back.map (Block.guarded same but)).map skel = _
    rw [← h.back]
    simp [List.map_map, Function.comp_def, skel_guarded]
  · show skel (c.last.guarded same but) = _
    rw [skel_guarded, h.last]

/-- **The driver's chain returns just where its text on skeletons does, and its flat list has
the skeletons that this gives.** -/
theorem firstChain_skel {H : Blocks S Cl} {K : BlocksSk} (F : Fits H K) (links : List ModelPart)
    (several : Bool) :
    (firstChain H links several).map (fun c => c.blocksInOrder.map skel) =
      (bareChainSk K links several).map ChainSk.flat := by
  have h := bareChain_skel F links several
  unfold firstChain
  cases e : firstChainWithoutReplyGuard H links several <;> cases e' : bareChainSk K links several <;>
    rw [e, e'] at h
  · rfl
  · exact h.elim
  · exact h.elim
  · exact congrArg some (flat_fits (chain_guarded H.same hearsReply h))

/-! ### chainC -/

/-- `fill` on skeletons. kb: the skeletons of the batchings that are supplied as functions. -/
def fillSk (bs : List Skel) (sealed : Skel) (kb : Place → Option Skel) (first : Skel) : BlocksSk :=
  { block := fun a => bs.find? fun b => b.place == a
    batch := fun a => kb a <|> bs.find? fun b => b.place == a
    first := first, last := sealed }

theorem find_skel (bs : List (Block S Cl)) (p : Skel → Bool) :
    (bs.map skel).find? p = (bs.find? fun b => p (skel b)).map skel := by
  rw [List.find?_map]
  rfl

theorem fill_fits (bs : List (Block S Cl)) (z : Block S Cl) (fr : Frames S Cl)
    (kb : Place → Option Skel) (hb : ∀ a g, (fr.batch a).map (fun mk => skel (mk g)) = kb a) :
    Fits (fill bs z fr) (fillSk (bs.map skel) (skel z) kb (skel fr.first)) := by
  refine ⟨fun a => ?_, fun a g => ?_, rfl, rfl⟩
  · exact (find_skel bs fun k => k.place == a).symm
  · have e : (bs.map skel).find? (fun k => k.place == a) =
        (bs.find? fun b => b.place == a).map skel := find_skel bs _
    show Option.map (fun mk => skel (mk g)) ((fill bs z fr).batch a) =
      (fillSk (bs.map skel) (skel z) kb (skel fr.first)).batch a
    unfold fill fillSk
    dsimp only
    rw [e, ← hb a g]
    cases fr.batch a <;> cases (bs.find? fun b => b.place == a) <;> rfl

/-- `chainC` on skeletons: the flat list's skeletons, or the refusal's words. -/
def chainCSk (bs : List Skel) (links : List ModelPart) (kb : Place → Option Skel) (first : Skel) :
    Except String (List Skel) :=
  match bs.getLast? with
  | none => .error "the chain: no block is supplied"
  | some z =>
    match bareChainSk (fillSk bs.dropLast z kb first) links
        (bs.any fun b => b.place.kind == KindName.K13) with
    | none =>
      .error "the chain: the driver finds no block at a place, or rejects the list of links"
    | some c =>
      match bs.find? fun b => !(c.flat.any fun x => x.name == b.name) with
      | some b => .error ("the chain: the supplied block " ++ b.name ++ " is not in the chain")
      | none => .ok c.flat

/-- Premise hb: a batching that the frames supply as a function makes, at every gatherer, a block
with the skeleton that kb names, and kb names none where the frames supply none. Then `chainC`
returns just where `chainCSk` returns at the blocks' skeletons, the links, kb and the skeleton of
the frames' first block, with the same word of refusal, and its flat list has the skeletons that
`chainCSk` gives. -/
theorem chainC_skel (bs : List (Block S Cl)) (links : List ModelPart) (fr : Frames S Cl)
    (kb : Place → Option Skel) (hb : ∀ a g, (fr.batch a).map (fun mk => skel (mk g)) = kb a) :
    (chainC bs links fr).map (fun c => c.blocksInOrder.map skel) =
      chainCSk (bs.map skel) links kb (skel fr.first) := by
  unfold chainC chainCSk
  rw [List.getLast?_map]
  cases bs.getLast? with
  | none => rfl
  | some z =>
    have hs : ((bs.map skel).any fun b => b.place.kind == KindName.K13) =
        bs.any fun b => b.place.kind == KindName.K13 := by
      rw [List.any_map]
      rfl
    have hd : (bs.map skel).dropLast = bs.dropLast.map skel := by
      simp [List.map_dropLast]
    have h := firstChain_skel (fill_fits bs.dropLast z fr kb hb) links
      (bs.any fun b => b.place.kind == KindName.K13)
    dsimp only [Option.map_some]
    rw [hs, hd]
    cases e : firstChain (fill bs.dropLast z fr) links
        (bs.any fun b => b.place.kind == KindName.K13) <;>
      cases e' : bareChainSk (fillSk (bs.dropLast.map skel) (skel z) kb (skel fr.first)) links
        (bs.any fun b => b.place.kind == KindName.K13) <;>
      rw [e, e'] at h
    · rfl
    · simp at h
    · simp at h
    rename_i c M
    have hf : c.blocksInOrder.map skel = M.flat := Option.some.inj h
    have hq : ((bs.map skel).find? fun b => !(M.flat.any fun x => x.name == b.name)) =
        (bs.find? fun b => !(c.blocksInOrder.any fun x => x.name == b.name)).map skel := by
      rw [find_skel, ← hf]
      simp only [List.any_map, Function.comp_def]
      rfl
    dsimp only
    rw [hq]
    cases bs.find? fun b => !(c.blocksInOrder.any fun x => x.name == b.name) with
    | none => exact congrArg Except.ok hf
    | some b => rfl

/-! ### chainBy -/

/-- `chainBy`'s test "this block of the kind frame is joined after that block", on skeletons. -/
def behindSk : Skel → FrameRole → Bool
  | b, .behind l m => b.name == m && b.place.link == some l
  | _, _ => false

/-- `chainBy` on skeletons. -/
def chainBySk (subs : List ModelPart) (base : List Skel) (fr : List (FrameRole × Skel))
    (kb : Place → Option Skel) : Except String (List Skel) :=
  chainCSk
    (base.map fun b =>
      match fr.find? fun x => behindSk b x.1 with
      | some x => b.andThen b.name x.2
      | none => b)
    subs kb
    (match (fr.find? fun x => x.1 == FrameRole.front).map fun x => x.2 with
      | some o => { o with name := frontName }
      | none => Skel.quiet frontName 1 none 0)

theorem find_role (fr : List (FrameRole × Block S ProofFile.Cl)) (p : FrameRole → Bool) :
    ((fr.map fun x => (x.1, skel x.2)).find? fun x => p x.1) =
      (fr.find? fun x => p x.1).map fun x => (x.1, skel x.2) := by
  rw [List.find?_map]
  rfl

/-- Premise hb: as in `chainC_skel`, of the road's batchings. Then `chainBy` returns just where
`chainBySk` returns at the segments' sorts and the skeletons of the base and of the frames, with
the same word of refusal, and its flat list has the skeletons that `chainBySk` gives. -/
theorem chainBy_skel (Z : Pub) (base : List (Block S ProofFile.Cl))
    (fr : List (FrameRole × Block S ProofFile.Cl)) (road : Gather S ProofFile.Cl) (kb : Place → Option Skel)
    (hb : ∀ a g, (road.batch a).map (fun mk => skel (mk g)) = kb a) :
    (chainBy Z base fr road).map (fun c => c.blocksInOrder.map skel) =
      chainBySk (subsOf Z) (base.map skel) (fr.map fun x => (x.1, skel x.2)) kb := by
  unfold chainBy chainBySk
  dsimp only
  rw [chainC_skel _ _ _ kb hb]
  congr 1
  · rw [List.map_map, List.map_map]
    refine List.map_congr_left fun b _ => ?_
    have key : ∀ p : FrameRole × Block S ProofFile.Cl → Bool, (∀ x, p x = behindSk (skel b) x.1) →
        skel (match fr.find? p with
          | some x => b.andThen b.name (x.2.guarded road.same fun _ => false)
          | none => b) =
        (match (fr.find? fun x => behindSk (skel b) x.1).map fun x => (x.1, skel x.2) with
          | some x => (skel b).andThen (skel b).name x.2
          | none => skel b) := by
      intro p hp
      have e : p = fun x => behindSk (skel b) x.1 := funext hp
      subst e
      cases fr.find? fun x => behindSk (skel b) x.1 with
      | none => rfl
      | some x =>
        simp only [Option.map_some, skel_andThen, skel_guarded]
        rfl
    simp only [Function.comp_def]
    rw [find_role fr (behindSk (skel b))]
    exact key _ fun x => by cases x.1 <;> rfl
  · rw [find_role fr (· == FrameRole.front)]
    cases fr.find? _ with
    | none => exact skel_quiet _ _ _ _ _
    | some x => rfl

end LPFPol.SkR

#print axioms LPFPol.SkR.mapM_rel
#print axioms LPFPol.SkR.forall₂_skel
#print axioms LPFPol.SkR.blockAt_skel
#print axioms LPFPol.SkR.linkAt_skel
#print axioms LPFPol.SkR.bareChain_skel
#print axioms LPFPol.SkR.links_flat
#print axioms LPFPol.SkR.flat_fits
#print axioms LPFPol.SkR.link_guarded
#print axioms LPFPol.SkR.links_guarded
#print axioms LPFPol.SkR.chain_guarded
#print axioms LPFPol.SkR.firstChain_skel
#print axioms LPFPol.SkR.find_skel
#print axioms LPFPol.SkR.fill_fits
#print axioms LPFPol.SkR.chainC_skel
#print axioms LPFPol.SkR.find_role
#print axioms LPFPol.SkR.chainBy_skel
