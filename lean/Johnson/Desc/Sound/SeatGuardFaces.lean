-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/SeatGuardFaces.lean: THE GUARD ON ONE SEAT (Johnson/Desc/SeatGuard.lean) SHOWS THE TESTS ON THE PLAN THE SAME FACES. (The chain's yes
goes by the fold, which reads the rounds; but the file's decision also asks the tests on the plan, which read more of a block than its rounds.)

  Block.face: what a test on the plan can read of a block: its name, place, own test on the plan, rounds, oracles, "before", and the NAMES of its runs of both sorts: all but the three fields that are functions of the record (a block has nine fields: Block.lean, lines 71-101: name · place · planOk · rounds · oracles · before · decide · claims · after).
  guarded_face: a guarded block has the block's face. orderOk_guarded, orderAfterOk_guarded, bare_guarded: so the link's own tests on the plan say the same.
  Link.BatchFace: THE PREMISE's SECOND CLAUSE: the batching's face does not hang on the function of claims that it is handed. face_stamp: a driver's stamp of the place carries it.
  **Chain.guarded_faces**: every link's batching so ⇒ (c.guarded same but).blocksInOrder.map Block.face = c.blocksInOrder.map Block.face.

Every "there is", walked: no statement has one.
Limits. A rule. THAT FileDescription.planOk READS NOTHING OF THE FLAT LISTS BUT THEIR FACES is seen at Block.lean's text (its tests take name, place, planOk, rounds, oracles, before; orderOk | orderAfterOk | hasNoClaimsAndNothingAfter stand inside "laid"'s
planOk and Chain.blocksInOrder's "bare"): IT IS NOT A THEOREM HERE. Nothing on soundness, on acceptance or on hiding.

-/
import Johnson.Desc.SeatGuard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

variable {S Cl : Type}

/-- What a test on the plan can read of a block. -/
def Block.face (b : Block S Cl) :
    String × Place × Bool × List Fmt.DeclaredRound × List (List Oracle) × List (Nat × Nat) × List String × List String :=
  (b.name, b.place, b.planOk, b.rounds, b.oracles, b.before, b.claims.map (·.1), b.after.map (·.1))

section
variable (same : S → S → Bool) (but : Place → Bool)

theorem guarded_claimNames (b : Block S Cl) : (b.guarded same but).claims.map (·.1) = b.claims.map (·.1) := by
  show (b.claims.map fun c =>
    (c.1, fun n t => (c.2 n t).bind fun y => (seatSame same t y.2).map fun _ => y)).map (·.1) = _
  rw [List.map_map]; rfl

theorem guarded_afterNames (b : Block S Cl) : (b.guarded same but).after.map (·.1) = b.after.map (·.1) := by
  show (b.after.map fun c => (c.1, fun t => (c.2 t).bind (seatSame same t))).map (·.1) = _
  rw [List.map_map]; rfl

/-- **A guarded block has the block's face.** -/
theorem guarded_face (b : Block S Cl) : (b.guarded same but).face = b.face := by
  unfold Block.face
  rw [guarded_claimNames, guarded_afterNames]
  rfl

theorem bare_guarded (b : Block S Cl) : (b.guarded same but).hasNoClaimsAndNothingAfter = b.hasNoClaimsAndNothingAfter := by
  unfold Block.hasNoClaimsAndNothingAfter
  show ((b.claims.map _).isEmpty && (b.after.map _).isEmpty) = _
  rw [List.isEmpty_map, List.isEmpty_map]

/-- The runs' names with their blocks' numbers, of a list of guarded blocks. -/
theorem names_guarded {β : Type} (runs : Block S Cl → List (String × β))
    (h : ∀ b, (runs (b.guarded same but)).map (·.1) = (runs b).map (·.1)) : ∀ (bs : List (Block S Cl)) (k : Nat),
    ((bs.map (Block.guarded same but)).zipIdx k).flatMap (fun b => (runs b.1).map fun c => (b.2, c.1)) =
      (bs.zipIdx k).flatMap fun b => (runs b.1).map fun c => (b.2, c.1)
  | [], _ => rfl
  | b :: bs, k => by
    simp only [List.map_cons, List.zipIdx_cons, List.flatMap_cons]
    rw [names_guarded runs h bs (k + 1)]
    congr 1
    have e : ∀ l : List (String × β), (l.map fun c => (k, c.1)) = (l.map (·.1)).map fun n => (k, n) := by
      intro l; rw [List.map_map]; rfl
    rw [e, e, h]

theorem orderOk_guarded (bs : List (Block S Cl)) (order : List (Nat × String)) :
    orderOk (bs.map (Block.guarded same but)) order = orderOk bs order := by
  unfold orderOk
  rw [names_guarded same but (·.claims) (guarded_claimNames same but) bs 0]

theorem orderAfterOk_guarded (bs : List (Block S Cl)) (order : List (Nat × String)) :
    orderAfterOk (bs.map (Block.guarded same but)) order = orderAfterOk bs order := by
  unfold orderAfterOk
  rw [names_guarded same but (·.after) (guarded_afterNames same but) bs 0]

theorem allBare_guarded : ∀ bs : List (Block S Cl),
    (bs.map (Block.guarded same but)).all Block.hasNoClaimsAndNothingAfter = bs.all Block.hasNoClaimsAndNothingAfter
  | [] => rfl
  | b :: bs => by
    simp only [List.map_cons, List.all_cons]
    rw [bare_guarded, allBare_guarded bs]

theorem faces_guarded (bs : List (Block S Cl)) :
    (bs.map (Block.guarded same but)).map Block.face = bs.map Block.face := by
  rw [List.map_map]
  exact List.map_congr_left fun b _ => guarded_face same but b

/-- **The premise's second clause**: the batching's face, and whether it is bare, do not hang on the function that it is handed. -/
def Link.BatchFace (L : Link S Cl) : Prop := ∀ f' f, (L.batch f').face = (L.batch f).face

/-- Two blocks of one face, stamped with one place, have one face. -/
theorem face_stamp {b' b : Block S Cl} (h : b'.face = b.face) (a : Place) :
    Block.face { b' with place := a } = Block.face { b with place := a } := by
  unfold Block.face at h ⊢
  simp only [Prod.mk.injEq] at h ⊢
  obtain ⟨h1, _, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, trivial, h3, h4, h5, h6, h7, h8⟩

theorem bare_of_face {b' b : Block S Cl} (h : b'.face = b.face) : b'.hasNoClaimsAndNothingAfter = b.hasNoClaimsAndNothingAfter := by
  unfold Block.face at h
  have hc : b'.claims.map (·.1) = b.claims.map (·.1) := by
    have := congrArg (fun x => x.2.2.2.2.2.2.1) h; exact this
  have ha : b'.after.map (·.1) = b.after.map (·.1) := by
    have := congrArg (fun x => x.2.2.2.2.2.2.2) h; exact this
  unfold Block.hasNoClaimsAndNothingAfter
  rw [← List.isEmpty_map (f := (·.1)) (l := b'.claims), ← List.isEmpty_map (f := (·.1)) (l := b'.after), hc, ha,
    List.isEmpty_map, List.isEmpty_map]

theorem Link.guarded_faces (L : Link S Cl) (hb : L.BatchFace) :
    (L.guarded same but).blocksInOrder.map Block.face = L.blocksInOrder.map Block.face := by
  have hB : ∀ f' f, ((L.batch f').guarded same but).face = (L.batch f).face := fun f' f =>
    (guarded_face same but _).trans (hb f' f)
  unfold Link.blocksInOrder
  simp only [List.map_cons, List.map_append, List.map_nil]
  have e1 : (L.guarded same but).hear = L.hear.map (Block.guarded same but) := rfl
  have e2 : (L.guarded same but).close = L.close.map (Block.guarded same but) := rfl
  rw [e1, e2, faces_guarded, faces_guarded]
  have e3 : ((L.guarded same but).batch (claimsInBy (L.guarded same but).each (L.hear.map (Block.guarded same but))
      (L.guarded same but).order)).face = (L.batch (claimsInBy L.each L.hear L.order)).face := hB _ _
  rw [e3]
  have e4 : ((L.guarded same but).batch (claimsInBy (L.guarded same but).each (L.hear.map (Block.guarded same but))
      (L.guarded same but).order)).hasNoClaimsAndNothingAfter = (L.batch (claimsInBy L.each L.hear L.order)).hasNoClaimsAndNothingAfter := bare_of_face (hB _ _)
  unfold Block.face
  simp only [e4, List.length_map]
  have o1 : orderOk (L.hear.map (Block.guarded same but)) (L.guarded same but).order = orderOk L.hear L.order :=
    orderOk_guarded same but L.hear L.order
  have o2 : orderAfterOk (L.hear.map (Block.guarded same but)) (L.guarded same but).orderAfter =
      orderAfterOk L.hear L.orderAfter := orderAfterOk_guarded same but L.hear L.orderAfter
  rw [o1, o2, allBare_guarded]
  rfl

theorem bareFace {b' b : Block S Cl} (h : b'.face = b.face) :
    Block.face { b' with planOk := b'.planOk && b'.hasNoClaimsAndNothingAfter } = Block.face { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter } := by
  have hb := bare_of_face h
  unfold Block.face at h ⊢
  simp only [Prod.mk.injEq] at h ⊢
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, by rw [h3, hb], h4, h5, h6, h7, h8⟩

/-- **THE GUARDED CHAIN's FLAT LIST SHOWS THE SAME FACES.** -/
theorem Chain.guarded_faces (c : Chain S Cl) (hb : ∀ L ∈ c.links, L.BatchFace) :
    (c.guarded same but).blocksInOrder.map Block.face = c.blocksInOrder.map Block.face := by
  have hm : ∀ l : List (Block S Cl),
      ((l.map (Block.guarded same but)).map fun b => { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }).map Block.face =
      (l.map fun b => { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }).map Block.face := by
    intro l
    induction l with
    | nil => rfl
    | cons b l ih =>
      simp only [List.map_cons]
      rw [bareFace (guarded_face same but b)]
      exact congrArg _ ih
  have hl : ∀ ls : List (Link S Cl), (∀ L ∈ ls, L.BatchFace) →
      ((ls.map (Link.guarded same but)).flatMap Link.blocksInOrder).map Block.face = (ls.flatMap Link.blocksInOrder).map Block.face := by
    intro ls
    induction ls with
    | nil => intro _; rfl
    | cons L ls ih =>
      intro h
      simp only [List.map_cons, List.flatMap_cons, List.map_append]
      rw [Link.guarded_faces same but L (h L (List.mem_cons_self ..)), ih fun L' m => h L' (List.mem_cons_of_mem _ m)]
  unfold Chain.blocksInOrder
  simp only [List.map_cons, List.map_append, List.map_nil]
  have e1 : (c.guarded same but).front = c.front.map (Block.guarded same but) := rfl
  have e2 : (c.guarded same but).links = c.links.map (Link.guarded same but) := rfl
  have e3 : (c.guarded same but).back = c.back.map (Block.guarded same but) := rfl
  rw [e1, e2, e3, hm, hm, hl c.links hb]
  have f1 := bareFace (guarded_face same but c.first)
  have f9 := bareFace (guarded_face same but c.last)
  have g1 : (c.guarded same but).first = c.first.guarded same but := rfl
  have g9 : (c.guarded same but).last = c.last.guarded same but := rfl
  rw [g1, g9, f1, f9]

end

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.face_stamp
#print axioms VerifiableInference.Desc.guarded_face
#print axioms VerifiableInference.Desc.orderOk_guarded
#print axioms VerifiableInference.Desc.Link.guarded_faces
#print axioms VerifiableInference.Desc.Chain.guarded_faces
