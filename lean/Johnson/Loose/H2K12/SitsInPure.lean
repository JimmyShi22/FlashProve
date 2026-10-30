-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
import Johnson.Loose.H2K12.FirstSeatForm
import Johnson.Desc.ProofFile.OnlineDescriptionFromBlockTables
import Johnson.Desc.ProofFile.Lot.K12
import Johnson.Desc.ProofFile.Law.OrderStated
/-
Johnson/Loose/H2K12/SitsInPure.lean:
OVER Johnson/Desc/ProofFile/…, IN WHICH chainBy JOINS BY THE SEGMENT AND THE
NAME: THE PROXIMITY TEST SITS IN THE PROOF FILE's IOP AS WRITTEN IN LEAN: THE PART THAT OPENS ProofFile's
TEXTS ON THE FIRST CHAIN (partsAt · faultsAt | faultsOf · baseOf), AND THE SPINE pureZ_sits. Beside
it: LaterSeatsN.lean · DescN.lean (the two later chains) · FirstSeatForm.lean (the kind's
sub-protocol as it sits at F:2). pureZ_sits ends in FirstJ (pL N) J, that is J
= firstCore (pL N) nm. TWO THEOREMS ARE TAKEN TO THE LETTER FROM ANOTHER
COPY OF THIS FILE: chainBy_cut_alone · parts_first_cut_alone,
over ProofFile.Law.chainBy_hands (Johnson/Desc/ProofFile/Law/OrderStated.lean). So is pureZ_all's
proof (three calls of ProofFile.Law.pureZ_ok | pureTail_ok).



  chainC_ok · chainBy_cut_alone     the first chain's flat list is cut at the proximity test's
      place, at a member of the list itself; no other entry bears the kind K12.
  mapM_ok_mem · parts_base     what partsAt's list is made of.
  eq_of_short · faults_unique     of «nothing is amiss»: one sub-protocol at most at a place that is
      no frame's.
  k12_place · p12OfMade_place · atFinish_place     the kind's sub-protocol bears its place.
  NoFaceAt T G         no maker of the seat's lots makes a sub-protocol whose field «place» is
      a12: a premise of parts_first_cut_alone (paid at the pure seat in H2K12/SitsAtDescPure.lean).
  parts_first_cut_alone     the first chain is cut at the seat, and the entry is firstEntry
      T.same (firstCore (p12OfMade Z.made) nm).
  baseOf_all · pureZ_all     what onlineDescriptionFromPublicPart returns, read back.
  pureZ_sits           K12_sits, general in the seat. («∃ B, baseOf Z T = .ok B» stays in the
      statement though no caller is known to read B: the callers' patterns count it.)
LIMITS. pre, l, nm stand under «there is» at the first chain. WHAT AN ACCEPTING RUN GIVES, NOT AN
ERROR BOUND. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
-/
set_option autoImplicit false
namespace H2K.JointK
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.K12.Seat (onGu onGomega enterOwn leaveOwn onOwn)
open H2K.Pub (Letters)

/-! ### the filling and the chain -/

theorem chainC_ok {σ Cl : Type} (bs : List (Block σ Cl)) (links : List First.ModelPart)
    (fr : ProofFile.Frames σ Cl) (c : Chain σ Cl) (h : ProofFile.chainC bs links fr = .ok c) :
    ∃ z, First.firstChain (ProofFile.fill bs.dropLast z fr) links
      (bs.any fun b => b.place.kind == KindName.K13) = some c := by
  unfold ProofFile.chainC at h
  split at h
  · cases h
  · rename_i z _
    dsimp only at h
    split at h
    · cases h
    · rename_i c0 hc
      split at h
      · cases h
      · cases h
        exact ⟨z, hc⟩

/-- The first chain's flat list is cut at the proximity test's place, at a member of the list of
sub-protocols itself: nothing is joined behind it. -/
theorem chainBy_cut_alone {σ : Type} (Z : ProofFile.Pub) (base : List (Block σ ProofFile.Cl))
    (fr : List (ProofFile.FrameRole × Block σ ProofFile.Cl)) (road : ProofFile.Gather σ ProofFile.Cl)
    (c : Chain σ ProofFile.Cl) (h : ProofFile.chainBy Z base fr road = .ok c) :
    ∃ pre l b, b ∈ base ∧ b.place = a12 ∧ c.blocksInOrder = pre ++ firstEntry road.same b :: l ∧
      ∀ E ∈ c.blocksInOrder, E.place.kind = .K12 → E = firstEntry road.same b := by
  obtain ⟨join, Fr, hC, rfl, hj⟩ := ProofFile.Law.chainBy_hands h
  obtain ⟨z, h1⟩ := chainC_ok _ _ _ _ hC
  obtain ⟨b, pre, l, hb, hflat⟩ := firstChain_cut _ _ _ _ h1
  have hb' := hb
  simp only [ProofFile.fill] at hb'
  have hm := List.mem_of_find?_eq_some hb'
  have hp : (b.place == a12) = true :=
    List.find?_some (p := fun b : Block σ ProofFile.Cl => b.place == a12) hb'
  obtain ⟨b', hb0, rfl⟩ := List.mem_map.1 (List.dropLast_subset _ hm)
  have e : join b' = b' := by
    rcases hj b' with e | ⟨x, _, l', _, hl', e⟩
    · exact e
    · exfalso
      have hpl : (join b').place = a12 := eq_of_beq hp
      rw [e] at hpl
      have hpl' : b'.place = a12 := hpl
      rw [hpl'] at hl'
      cases hl'
  rw [e] at hp hflat hb
  exact ⟨pre, l, b', hb0, eq_of_beq hp, hflat, firstChain_only _ _ _ _ h1 _ hb⟩

/-! ### what the first chain is made of -/

theorem mapM_ok_mem {α β : Type} (f : α → Except String β) : ∀ (l : List α) (out : List β),
    l.mapM f = .ok out → ∀ y ∈ out, ∃ x ∈ l, f x = .ok y := by
  intro l
  induction l with
  | nil =>
    intro out h y hy
    rw [List.mapM_nil] at h
    cases h
    cases hy
  | cons a l ih =>
    intro out h y hy
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := ebind_ok h
    obtain ⟨bs, hbs, h⟩ := ebind_ok h
    cases h
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨a, List.mem_cons_self, hb⟩
    · obtain ⟨x, hx, e⟩ := ih bs hbs y hy
      exact ⟨x, List.mem_cons_of_mem _ hx, e⟩

/-- What a block of the first chain's base is: a batching's maker's face, or a lot's block at a
spot's place, behind the mark's guard, under the spot's name. -/
theorem parts_base (T : ProofFile.PureSeat) (B : ProofFile.PureBase) (base : List (Block First.S ProofFile.Cl))
    (hb : (ProofFile.partsAt T B).base = .ok base) :
    ∀ b' ∈ base, ∃ sp ∈ B.spots,
      (∃ L ∈ T.lots, ∃ mk g, L.batch B.G₀ sp.place = some mk ∧ b'.place = (mk g).place) ∨
      (∃ x ∈ B.all, ∃ bL ∈ x.2, bL.place = sp.place ∧
        b' = { ProofFile.guardMark bL with name := sp.name }) := by
  intro b' hb'
  obtain ⟨x, hx, e⟩ := mapM_ok_mem _ _ _ hb b' hb'
  unfold ProofFile.partsAt at hx
  dsimp only at hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
  refine ⟨p, hp, ?_⟩
  dsimp only at e
  split at e
  · rename_i f _ hface
    cases e
    obtain ⟨mk', h1, rfl⟩ := Option.map_eq_some_iff.1 hface
    obtain ⟨mk, h2, rfl⟩ := Option.map_eq_some_iff.1 h1
    obtain ⟨L, hL, h3⟩ := List.exists_of_findSome?_eq_some h2
    exact Or.inl ⟨L, (List.mem_filter.1 hL).1, mk, _, h3, rfl⟩
  · rename_i y _ hy
    cases e
    have hy' := List.mem_of_find?_eq_some hy
    obtain ⟨z, hz, hz2⟩ := List.mem_filterMap.1 hy'
    obtain ⟨bL, hbL, rfl⟩ := Option.map_eq_some_iff.1 hz2
    exact Or.inr ⟨z, hz, bL, List.mem_of_find?_eq_some hbL,
      eq_of_beq (List.find?_some (p := fun b : Block First.S ProofFile.Cl => b.place == p.place) hbL),
      rfl⟩
  · split at e <;> cases e

theorem eq_of_short {α : Type} : ∀ (l : List α), l.length ≤ 1 → ∀ x ∈ l, ∀ y ∈ l, x = y
  | [], _, x, hx, _, _ => by cases hx
  | [z], _, x, hx, y, hy => by
    rw [List.mem_singleton] at hx hy
    rw [hx, hy]
  | _ :: _ :: _, h, _, _, _, _ => by simp at h

/-- Where nothing is amiss in a seat's blocks: at a place that is no frame's, one block at most. -/
theorem faults_unique (shape : List (String × Place)) (own : List (Block First.S ProofFile.Cl))
    (hf : ProofFile.faultsOf shape own = []) (a : Place) (hk : a.kind ≠ KindName.frame)
    (b₁ : Block First.S ProofFile.Cl) (h₁ : b₁ ∈ own) (e₁ : b₁.place = a)
    (b₂ : Block First.S ProofFile.Cl) (h₂ : b₂ ∈ own) (e₂ : b₂.place = a) : b₁ = b₂ := by
  unfold ProofFile.faultsOf at hf
  dsimp only at hf
  obtain ⟨hAB, hC⟩ := List.append_eq_nil_iff.1 hf
  obtain ⟨hA, _⟩ := List.append_eq_nil_iff.1 hAB
  rw [List.map_eq_nil_iff, List.filter_eq_nil_iff] at hA hC
  have h1 := hA b₁ h₁
  rw [e₁] at h1
  have hs : (shape.any fun b => b.2 == a) = true := by
    cases hx : (shape.any fun b => b.2 == a) with
    | true => rfl
    | false =>
      exfalso
      apply h1
      rw [hx]
      simpa using hk
  obtain ⟨s, hs1, hs2⟩ := List.any_eq_true.1 hs
  have h2 := hC s hs1
  rw [eq_of_beq hs2] at h2
  have hlen : (own.filter fun o => o.place == a).length ≤ 1 := by
    simpa using h2
  exact eq_of_short _ hlen b₁ (List.mem_filter.2 ⟨h₁, by rw [e₁]; exact beq_self_eq_true a⟩) b₂
    (List.mem_filter.2 ⟨h₂, by rw [e₂]; exact beq_self_eq_true a⟩)

theorem k12_place {T Cl : Type} (X : Parts T) (p : P12) :
    (proximityTestKind X p : Block T Cl).place = p.place := by
  unfold proximityTestKind
  split <;> rfl

theorem p12OfMade_place (Z : ProofFile.Pub) : (H2U.p12OfMade Z.made).place = a12 := by
  unfold H2U.p12OfMade
  dsimp only
  split
  · unfold H2U.proximityTestParametersAt
    split
    · rfl
    · split <;> rfl
  · rfl

theorem atFinish_place (Z : ProofFile.Pub) : (atFinish (H2U.p12OfMade Z.made)).place = a12 := by
  show (proximityTestKind guardedProximityTestParts (H2U.p12OfMade Z.made) : Blk').place = a12
  rw [k12_place, p12OfMade_place]

/-- No batching's maker of the seat's lots makes a block that claims the proximity test's address.
-/
def NoFaceAt (T : ProofFile.PureSeat) (G : ProofFile.Ground) : Prop :=
  ∀ L ∈ T.lots, ∀ (a : Place) (mk : ProofFile.Gatherer → Block First.S ProofFile.Cl) (g : ProofFile.Gatherer),
    L.batch G a = some mk → (mk g).place ≠ a12

/-- THE FIRST CHAIN IS CUT AT THE PROXIMITY TEST's SEAT, AND THE ENTRY IS THE KIND's OWN, ALONE.
-/
theorem parts_first_cut_alone (Z : ProofFile.Pub) (T : ProofFile.PureSeat) (B : ProofFile.PureBase)
    (hall : B.all = T.lots.map fun L => (L, L.blocks B.G₀)) (hf : ProofFile.faultsAt T B = [])
    (base : List (Block First.S ProofFile.Cl)) (hb : (ProofFile.partsAt T B).base = .ok base)
    (c : Chain First.S ProofFile.Cl)
    (hc : ProofFile.chainBy Z base (ProofFile.partsAt T B).frames (ProofFile.partsAt T B).road = .ok c)
    (hL : K12.lot Z ∈ T.lots) (hface : NoFaceAt T B.G₀) :
    ∃ pre l nm, c.blocksInOrder = pre ++ firstEntry T.same (firstCore (H2U.p12OfMade Z.made) nm) :: l ∧
      ∀ E ∈ c.blocksInOrder, E.place.kind = .K12 →
        E = firstEntry T.same (firstCore (H2U.p12OfMade Z.made) nm) := by
  have hfo : ProofFile.faultsOf B.shape (B.all.flatMap fun x => x.2) = [] := by
    unfold ProofFile.faultsAt at hf
    dsimp only at hf
    exact (List.append_eq_nil_iff.1 (List.append_eq_nil_iff.1 (List.append_eq_nil_iff.1
      (List.append_eq_nil_iff.1 hf).1).1).1).1
  obtain ⟨pre, l, b', hb', hb'p, hflat, honly⟩ := chainBy_cut_alone Z base _ _ c hc
  obtain ⟨sp, _, hsp⟩ := parts_base T B base hb b' hb'
  rcases hsp with ⟨L, hLm, mk, g, hmk, hpl⟩ | ⟨x, hx, bL, hbL, _, rfl⟩
  · exact absurd (hpl ▸ hb'p) (hface L hLm _ mk g hmk)
  · have hmine : ((atFinish (H2U.p12OfMade Z.made)).retype (Cl' := ProofFile.Cl)) ∈
        B.all.flatMap fun x => x.2 := by
      rw [hall]
      refine List.mem_flatMap.2 ⟨(K12.lot Z, (K12.lot Z).blocks B.G₀),
        List.mem_map.2 ⟨K12.lot Z, hL, rfl⟩, ?_⟩
      simp [ProofFile.Lot.blocks, ProofFile.asCl, K12.lot]
    have hu : bL = (atFinish (H2U.p12OfMade Z.made)).retype (Cl' := ProofFile.Cl) :=
      faults_unique B.shape _ hfo a12 (by decide) bL (List.mem_flatMap.2 ⟨x, hx, hbL⟩) hb'p _
        hmine (atFinish_place Z)
    subst hu
    exact ⟨pre, l, sp.name, hflat, honly⟩

/-! ### onlineDescriptionFromPublicPart read back -/

theorem baseOf_all (Z : ProofFile.Pub) (T : ProofFile.PureSeat) (B : ProofFile.PureBase)
    (h : ProofFile.baseOf Z T = .ok B) : B.all = T.lots.map fun L => (L, L.blocks B.G₀) := by
  unfold ProofFile.baseOf at h
  obtain ⟨_, _, h⟩ := ebind_ok h
  obtain ⟨_, _, h⟩ := ebind_ok h
  obtain ⟨_, _, h⟩ := ebind_ok h
  cases h
  rfl

theorem pureZ_all (Z : ProofFile.Pub) (T : ProofFile.PureSeat) (F : FileDescription ProofFile.Inst)
    (hF : ProofFile.onlineDescriptionFromPublicPart Z T = .ok F) :
    ∃ B base A B' c, ProofFile.baseOf Z T = .ok B ∧ ProofFile.faultsAt T B = [] ∧
      (ProofFile.partsAt T B).base = .ok base ∧
      ProofFile.chainBy Z base (ProofFile.partsAt T B).frames (ProofFile.partsAt T B).road = .ok c ∧
      T.shared = some A ∧ T.second = some B' ∧
      F = ProofFile.fileDescBy T.older T.links Z A B' (fun s => s) (ProofFile.startS Z) c := by
  obtain ⟨B, hB, hfa, _, ht⟩ := ProofFile.Law.pureZ_ok hF
  obtain ⟨base, c, A, B', hb, hc, h2, h3, e⟩ := ProofFile.Law.pureTail_ok ht
  exact ⟨B, base, A, B', c, hB, hfa, hb, hc, h2, h3, e⟩

/-! ### the spine -/

/-- K12_sits, GENERAL IN THE SEAT. -/
theorem pureZ_sits (Z : ProofFile.Pub) (T : ProofFile.PureSeat) (F : FileDescription ProofFile.Inst)
    (hF : ProofFile.onlineDescriptionFromPublicPart Z T = .ok F) (hL : K12.lot Z ∈ T.lots)
    (hface : ∀ B, ProofFile.baseOf Z T = .ok B → NoFaceAt T B.G₀)
    (h2 : T.shared = ProofFile.laterShared Z) (h3 : T.second = ProofFile.laterSecond Z) :
    ∃ N c B, H2U.placesOfMade Z.made = .ok N ∧ F = descN T.older T.links guardedProximityTestParts Z N c ∧
      ProofFile.baseOf Z T = .ok B ∧
      ∃ pre l J, c.blocksInOrder = pre ++ firstEntry T.same J :: l ∧
        (∀ E ∈ c.blocksInOrder, E.place.kind = .K12 → E = firstEntry T.same J) ∧
        FirstJ (pL N) J := by
  obtain ⟨B, base, A, B', c, hB, hf, hb, hc, a2, a3, rfl⟩ := pureZ_all Z T F hF
  obtain ⟨N, hN⟩ := laterShared_some Z A (h2 ▸ a2)
  rw [h2, laterShared_is Z N hN] at a2
  rw [h3, laterSecond_is Z N hN] at a3
  cases a2
  cases a3
  obtain ⟨pre, l, nm, h1, ho⟩ :=
    parts_first_cut_alone Z T B (baseOf_all Z T B hB) hf base hb c hc hL (hface B hB)
  exact ⟨N, c, B, hN, rfl, hB, pre, l, _, h1, ho, nm, by rw [p12OfMade_is Z N hN]⟩

end H2K.JointK

#print axioms H2K.JointK.chainBy_cut_alone
#print axioms H2K.JointK.parts_base
#print axioms H2K.JointK.faults_unique
#print axioms H2K.JointK.parts_first_cut_alone
#print axioms H2K.JointK.pureZ_all
#print axioms H2K.JointK.pureZ_sits
