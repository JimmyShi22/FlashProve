-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Law/Skel/SkelRoundsParts.lean: THE ROUNDS' COLUMN, `partsAt`'s PART
(ProofFile/OnlineDescriptionFromBlockTables.lean): from the lots' blocks to the blocks at the places, the road's batchings and
the frames; and so to every block of the first chain's flat list. Statements and proofs.
  `exMapM_mem`, `place_ok`: two small laws
  `road_good`    from hK: what a lot's batching makes AT A PLACE WHERE THE LETTER A HOLDS (a lot's
                 `batch` may answer at places that nobody asks: K9's does not read the place's
                 chain), at every gatherer, is good under the name that `partsAt` lays over it (the
                 spot's at that place, else its own)
  `base_good`    from hL: a lot's block is good UNDER THE NAME OF THE SPOT AT ITS PLACE; hK; and hs:
                 A holds at every spot's place
  `frames_bare`  no frame has a round: off `frames_skel` (SkelParts.lean) and the skeletons' numbers
  `back_good`    all three with `chainBy_flat_good` (SkelRounds.lean)
Limits. Q is a letter; hL and hK are premises. Nothing on soundness.

-/
import Johnson.Desc.ProofFile.Law.Skel.SkelRounds
import Johnson.Desc.ProofFile.Law.Skel.SkelParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Sk
open VerifiableInference.Desc
open VerifiableInference.Desc.First

theorem exMapM_mem {α β : Type} (f : α → Except String β) :
    ∀ {l : List α} {ys : List β}, l.mapM f = .ok ys → ∀ y ∈ ys, ∃ a ∈ l, f a = .ok y
  | [], ys, h, y, hy => by
    rw [List.mapM_nil] at h
    have h' : (Except.ok [] : Except String (List β)) = .ok ys := h
    cases h'
    cases hy
  | a :: l, ys, h, y, hy => by
    rw [List.mapM_cons] at h
    cases e1 : f a with
    | error w =>
      rw [e1] at h
      have h' : (Except.error w : Except String (List β)) = .ok ys := h
      cases h'
    | ok b =>
      cases e2 : l.mapM f with
      | error w =>
        rw [e1, e2] at h
        have h' : (Except.error w : Except String (List β)) = .ok ys := h
        cases h'
      | ok bs =>
        rw [e1, e2] at h
        have h' : (Except.ok (b :: bs) : Except String (List β)) = .ok ys := h
        cases h'
        rcases List.mem_cons.1 hy with rfl | hy
        · exact ⟨a, List.mem_cons_self .., e1⟩
        · obtain ⟨x, hx, hfx⟩ := exMapM_mem f e2 y hy
          exact ⟨x, List.mem_cons_of_mem _ hx, hfx⟩

/-- Where a place's verdict is a block: it is the face, or a block that sits there, renamed. -/
theorem place_ok (face : Option (Block S ProofFile.Cl)) (here : List (Lot × Block S ProofFile.Cl))
    (looks : List String) (name : String) (y : Block S ProofFile.Cl) :
    (match face, here.find? fun x => !x.1.letters && !(looks.any x.1.still.contains) with
      | some f, _ => (.ok f : Except String (Block S ProofFile.Cl))
      | none, some x => .ok { guardMark x.2 with name := name }
      | none, none =>
        match here with
        | [] => .error ""
        | x :: _ =>
          .error (if x.1.letters then
              "the table of blocks " ++ x.1.name ++ " says that it depends on the request"
            else "the table of blocks " ++ x.1.name ++
              " says that the older verifier still runs a step here")) = .ok y →
      face = some y ∨ ∃ x ∈ here, y = { guardMark x.2 with name := name } := by
  cases face with
  | some f =>
    intro h
    exact Or.inl (congrArg some (Except.ok.inj h))
  | none =>
    cases e : here.find? fun x => !x.1.letters && !(looks.any x.1.still.contains) with
    | some x =>
      intro h
      exact Or.inr ⟨x, List.mem_of_find?_eq_some e, (Except.ok.inj h).symm⟩
    | none =>
      cases here with
      | nil =>
        intro h
        cases h
      | cons x l =>
        intro h
        cases h

section
variable {Q : String → List Fmt.DeclaredRound → Prop} {A : Place → Prop} (T : PureSeat)
  (B : PureBase)

theorem road_good
    (hK : ∀ L ∈ T.lots, ∀ a mk, A a → L.batch B.G₀ a = some mk →
      ∀ g, Q (nameAtSk B.spots a (mk g).name) (mk g).rounds) :
    ∀ a mk, A a → (partsAt T B).road.batch a = some mk → ∀ g, Good Q (mk g) := by
  intro a mk hc h g
  have h' : (((T.lots.filter fun L => !L.letters).findSome? fun L => L.batch B.G₀ a).map
      fun mk0 g => ({ guardMark (mk0 g) with name := nameAtSk B.spots a (mk0 g).name } :
        Block S ProofFile.Cl)) = some mk := h
  cases e : (T.lots.filter fun L => !L.letters).findSome? fun L => L.batch B.G₀ a with
  | none =>
    rw [e] at h'
    cases h'
  | some mk0 =>
    rw [e] at h'
    cases h'
    obtain ⟨L, hL, hb⟩ := List.exists_of_findSome?_eq_some e
    exact hK L (List.mem_of_mem_filter hL) a mk0 hc hb g

theorem base_good (hB : B.all = T.lots.map fun L => (L, L.blocks B.G₀))
    (hL : ∀ L ∈ T.lots, ∀ b ∈ L.blocks B.G₀, ∀ p ∈ B.spots, p.place = b.place →
      Q p.name b.rounds)
    (hK : ∀ L ∈ T.lots, ∀ a mk, A a → L.batch B.G₀ a = some mk →
      ∀ g, Q (nameAtSk B.spots a (mk g).name) (mk g).rounds)
    (hs : ∀ p ∈ B.spots, A p.place)
    {base : List (Block S ProofFile.Cl)} (h : (partsAt T B).base = .ok base) :
    ∀ b ∈ base, Good Q b := by
  intro b hb
  unfold PureParts.base at h
  obtain ⟨x, hx, hxb⟩ := exMapM_mem _ h b hb
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
  dsimp only at hxb
  have key := place_ok
    (((partsAt T B).road.batch p.place).map fun mk => mk fun s => .ok ([], s))
    (B.all.filterMap fun x => (x.2.find? fun b => b.place == p.place).map fun b => (x.1, b))
    (p.cuts.flatMap fun c => [stepName c.look, c.look]) p.name b
  rcases key hxb with hf | ⟨y, hy, rfl⟩
  · cases e : (partsAt T B).road.batch p.place with
    | none =>
      have hf' : ((partsAt T B).road.batch p.place).map (fun mk => mk fun s => .ok ([], s)) =
          some b := hf
      rw [e] at hf'
      cases hf'
    | some mk =>
      have hf' : ((partsAt T B).road.batch p.place).map (fun mk => mk fun s => .ok ([], s)) =
          some b := hf
      rw [e] at hf'
      cases hf'
      exact road_good T B hK p.place mk (hs p hp) e _
  · obtain ⟨z, hz, hzy⟩ := List.mem_filterMap.1 hy
    rw [hB] at hz
    obtain ⟨L, hLm, rfl⟩ := List.mem_map.1 hz
    cases e : (L.blocks B.G₀).find? fun b => b.place == p.place with
    | none =>
      have hzy' : ((L.blocks B.G₀).find? fun b => b.place == p.place).map (fun b => (L, b)) =
          some y := hzy
      rw [e] at hzy'
      cases hzy'
    | some b0 =>
      have hzy' : ((L.blocks B.G₀).find? fun b => b.place == p.place).map (fun b => (L, b)) =
          some y := hzy
      rw [e] at hzy'
      cases hzy'
      have hpl : (b0.place == p.place) = true :=
        List.find?_some (p := fun b : Block S ProofFile.Cl => b.place == p.place) e
      exact hL L hLm b0 (List.mem_of_find?_eq_some e) p hp (eq_of_beq hpl).symm

theorem frames_bare (hB : B.all = T.lots.map fun L => (L, L.blocks B.G₀))
    (hf : ∀ x ∈ framesSk B.shape (T.lots.map (lotSk B.G₀)), x.2.nRounds = 0) :
    ∀ x ∈ (partsAt T B).frames, x.2.rounds = [] := by
  intro x hx
  have hm : (x.1, skel x.2) ∈ framesSk B.shape (T.lots.map (lotSk B.G₀)) := by
    rw [← frames_skel T B hB]
    exact List.mem_map_of_mem (f := fun x : FrameRole × Block S ProofFile.Cl => (x.1, skel x.2)) hx
  exact List.eq_nil_of_length_eq_zero (hf _ hm)

/-- **From the lots' blocks to every block of the first chain's flat list.** -/
theorem back_good (hQ : ∀ n, Q n []) (Z : Pub)
    (hB : B.all = T.lots.map fun L => (L, L.blocks B.G₀))
    (hL : ∀ L ∈ T.lots, ∀ b ∈ L.blocks B.G₀, ∀ p ∈ B.spots, p.place = b.place →
      Q p.name b.rounds)
    (hK : ∀ L ∈ T.lots, ∀ a mk, A a → L.batch B.G₀ a = some mk →
      ∀ g, Q (nameAtSk B.spots a (mk g).name) (mk g).rounds)
    (hs : ∀ p ∈ B.spots, A p.place) (hA : ∀ x ∈ (subsOf Z).zipIdx, A (askAt x.2 x.1))
    (hf : ∀ x ∈ framesSk B.shape (T.lots.map (lotSk B.G₀)), x.2.nRounds = 0)
    {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl} (h₄ : (partsAt T B).base = .ok base)
    (h₅ : chainBy Z base (partsAt T B).frames (partsAt T B).road = .ok c) :
    ∀ b ∈ c.blocksInOrder, Good Q b :=
  chainBy_flat_good hQ (base_good T B hB hL hK hs h₄) (frames_bare T B hB hf)
    (road_good T B hK) hA h₅

end

end ProofFile.Sk

#print axioms ProofFile.Sk.exMapM_mem
#print axioms ProofFile.Sk.place_ok
#print axioms ProofFile.Sk.road_good
#print axioms ProofFile.Sk.base_good
#print axioms ProofFile.Sk.frames_bare
#print axioms ProofFile.Sk.back_good
