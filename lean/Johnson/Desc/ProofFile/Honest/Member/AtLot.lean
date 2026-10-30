--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Member/AtLot.lean: which value stands in the first chain of the proof
file's IOP at the place of a lot's sub-protocol: the proofs of the statements of
Johnson/Desc/ProofFile/Honest/Member/Statement.lean, but for the four uses (Uses.lean). Statements
with their proofs.

How it goes. The first chain is the driver's, at a structure filled from the list `base`
(`chainBy_first_fill`, Johnson/Desc/ProofFile/Law/FirstSame.lean). A member of its flat list that is
of a kind is what that structure gives at the member's place, behind the guard (`chain_member`,
Honest/Member/Driver.lean). What it gives is a member of `base`, with or without a member of the
frames' list laid behind it. A member of `base` is a lot's sub-protocol behind `guardMark`, under
the name of the place's entry (`places_of_lot`, Law/BaseOfLot.lean). Where `faultsAt` finds nothing,
two sub-protocols of the lots at one place are one (`IM.block_by_place`, Johnson/IMR/LinkSeat.lean),
so it is the given one.
Called from Johnson/IMR: `base_made` (PureJoin.lean), `stands_in_shape`, `block_by_place`
(LinkSeat.lean), `shape_spot`, `no_behind` (LaidFirst.lean), `no_behind_wide`, `flat_in_link`,
`link_first_piece` (CloseSeat.lean), `joined_at` (SameSpot.lean), `openedOf` (FrameSeat.lean),
`seal_seated` (SealSeat.lean), `yes_alone`, `yes_alone_K7`, `step_iff`, `guardMark_yes` and the
`alone_` laws (SeatForm.lean). From Johnson/Desc/ProofFile/Law: `mapM_ok_mem`, `parts_places_at`,
`face_place`, `ite_nil'` (MarkGuard.lean), `chainBy_places` (OrderCovered.lean). `guarded_yes`
(Johnson/Desc/Sound/SeatGuardLaws.lean). `andThen_step_noRound`
(Johnson/Top/H0/StepLaws/StepLaws.lean). Of `joined_gives`, the rounds and the step's way from an
acceptance down stand in the library too (`IM.Joined.rounds`, `Joined.step`, `Joined.step_same`,
Johnson/IMR/FirstSeats.lean); the way back is not in the library, and the equivalence is proved in
one piece.
Main names:
  `no_batch_at_block`, `no_batch_at`: where `faultsAt` finds nothing, no lot supplies the batching
    of a segment's claims as a function at the place of a lot's sub-protocol that is of a kind.
  `base_at_lot`: the member of `base` at the place of a lot's sub-protocol is that sub-protocol
    behind `guardMark`, under the name of the place's entry.
  `of_find`: from `List.find?` on the place to a member at the place.
  `member_laid`, `member_alone`, `member_first`, `alone_gives`, `joined_gives`, `joined_accepts`,
    `member_last`: **the statements**.

What is not claimed. What Statement.lean says is not covered or not claimed. Nothing on soundness,
completeness or hiding.

-/
import Johnson.Desc.ProofFile.Honest.Member.Driver
import Johnson.Desc.ProofFile.Law.BaseOfLot
import Johnson.Desc.ProofFile.Law.FirstSame
import Johnson.IMR.FrameSeat
import Johnson.Desc.ProofFile.Law.OrderCovered
import Johnson.Top.H0.StepLaws.StepLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.AtPlace
open VerifiableInference.Desc (Block Chain FileDescription KindName Place seatSame)
open VerifiableInference.Desc.First (S hearsReply)
open ProofFile.Law

/-- A lot's sub-protocol is among all lots' sub-protocols. -/
theorem mem_all {Z : Pub} {T : PureSeat} {B : PureBase} (hB : baseOf Z T = .ok B) {L : Lot}
    (hL : L ∈ T.lots) {b : Block S Cl} (hb : b ∈ L.blocks B.G₀) :
    b ∈ B.all.flatMap fun x => x.2 := by
  rw [(IM.base_made hB).2.2.2]
  exact List.mem_flatMap.2 ⟨(L, L.blocks B.G₀), List.mem_map.2 ⟨L, hL, rfl⟩, hb⟩

/-- Where `faultsAt` finds nothing: no lot supplies the batching of a segment's claims as a function
at a place of the list at which a lot's sub-protocol stands. -/
theorem no_batch_at_block {T : PureSeat} {B : PureBase} (hf : faultsAt T B = []) {p : Spot}
    (hp : p ∈ B.spots) {L : Lot} (hL : L ∈ T.lots) {mk : Gatherer → Block S Cl}
    (hmk : L.batch B.G₀ p.place = some mk) {b : Block S Cl}
    (hb : b ∈ B.all.flatMap fun x => x.2) (hbp : b.place = p.place) : False := by
  unfold faultsAt at hf
  dsimp only at hf
  have hAt := (List.append_eq_nil_iff.1 (List.append_eq_nil_iff.1
    (List.append_eq_nil_iff.1 hf).1).1).2
  have h1 := List.flatMap_eq_nil_iff.1 hAt p hp
  have hg : L ∈ T.lots.filter fun L => (L.batch B.G₀ p.place).isSome :=
    List.mem_filter.2 ⟨hL, by rw [hmk]; rfl⟩
  split at h1
  · rename_i he
    rw [List.isEmpty_iff.1 he] at hg
    exact (List.not_mem_nil hg).elim
  · have h2 := (List.append_eq_nil_iff.1 h1).2
    exact List.any_eq_false.1 (ite_nil' h2) b hb (beq_iff_eq.2 hbp)

/-- So none does at the place of a lot's sub-protocol that is of a kind. -/
theorem no_batch_at {Z : Pub} {T : PureSeat} {B : PureBase} (hB : baseOf Z T = .ok B)
    (hf : faultsAt T B = []) {L : Lot} (hL : L ∈ T.lots) {b : Block S Cl}
    (hb : b ∈ L.blocks B.G₀) (hk : b.place.kind ≠ KindName.frame) :
    ∀ L' ∈ T.lots, L'.batch B.G₀ b.place = none := by
  obtain ⟨hs, hsh, -, -⟩ := IM.base_made hB
  obtain ⟨e, he, ee⟩ := IM.stands_in_shape hf (mem_all hB hL hb) hk
  obtain ⟨p, hp, -, ep⟩ := IM.shape_spot hs hsh he (by rw [ee]; exact hk)
  intro L' hL'
  cases hmk : L'.batch B.G₀ b.place with
  | none => rfl
  | some mk =>
    exact (no_batch_at_block hf hp hL' (by rw [ep, ee]; exact hmk) (mem_all hB hL hb)
      (by rw [ep, ee])).elim

/-- **The member of `base` at the place of a lot's sub-protocol** is that sub-protocol behind
`guardMark`, under the name of the place's entry. -/
theorem base_at_lot {Z : Pub} {T : PureSeat} {B : PureBase} {base : List (Block S Cl)}
    (hB : baseOf Z T = .ok B) (hf : faultsAt T B = []) (hb : (partsAt T B).base = .ok base)
    {L : Lot} (hL : L ∈ T.lots) {b : Block S Cl} (hbL : b ∈ L.blocks B.G₀)
    (hk : b.place.kind ≠ KindName.frame) {b0 : Block S Cl} (h0 : b0 ∈ base)
    (hp0 : b0.place = b.place) :
    ∃ p ∈ B.spots, p.place = b.place ∧ b0 = IM.marked b p.name := by
  obtain ⟨x, hx, e⟩ := mapM_ok_mem _ _ _ hb b0 h0
  obtain ⟨hp, h⟩ := places_of_lot T B x hx b0 e
  obtain ⟨_, hpl⟩ := parts_places_at T B x hx b0 e
  have hxp : b0.place = x.1.place := by
    rcases hpl with ⟨L', hL', mk, hmk, e1⟩ | e1
    · exact e1.trans (face_place hf hp hL' hmk)
    · exact e1
  rcases h with ⟨L', hL', mk, hmk⟩ | ⟨y, hy, b₁, hb₁, _, _, rfl⟩
  · exact (no_batch_at_block hf hp hL' hmk (mem_all hB hL hbL) (hp0.symm.trans hxp)).elim
  · have hall := (IM.base_made hB).2.2.2
    rw [hall] at hy
    obtain ⟨L₁, hL₁, rfl⟩ := List.mem_map.1 hy
    have hp1 : b.place = b₁.place := hp0.symm
    obtain rfl : b = b₁ := IM.block_by_place hf hall hL hL₁ hbL hb₁ hk hp1
    exact ⟨x.1, hp, hxp.symm.trans hp0, rfl⟩

/-- What `List.find?` takes off a list by a place is a member of the list at that place. -/
theorem of_find {σ C : Type} {l : List (Block σ C)} {a : Place} {m : Block σ C}
    (h : (l.find? fun x => x.place == a) = some m) : m ∈ l ∧ m.place = a :=
  ⟨List.mem_of_find?_eq_some h,
    eq_of_beq (List.find?_some (p := fun x : Block σ C => x.place == a) h)⟩

/-- **`MemberLaid`**: every member at the place of a lot's sub-protocol that is of a kind is that
sub-protocol wrapped: alone, or with a named member of the frames' list laid behind it. -/
theorem member_laid : MemberLaid := by
  intro Z T B base c hB hf hb hc L hL b hbL hk m hm hpl
  obtain ⟨join, Fr, z, _, hfc, hFr, hj⟩ := chainBy_first_fill hc
  have hk' : m.place.kind ≠ KindName.frame := by
    rw [hpl]
    exact hk
  have hsame : Fr.same = T.same := congrArg Gather.same hFr
  obtain ⟨X, hX, hG⟩ : ∃ X,
      ((base.map join).dropLast.find? fun y => y.place == m.place) = some X ∧
        AsFlat (Block.guarded Fr.same hearsReply { X with place := m.place }) m := by
    rcases chain_member hfc hm hk' with ⟨X, hX, hG, _⟩ | ⟨_, mk, g, hmk, hG⟩
    · exact ⟨X, hX, hG⟩
    · have hnone : Fr.batch m.place = none := by
        have e : Fr.batch = (partsAt T B).road.batch := congrArg Gather.batch hFr
        have hmaker : ((T.lots.filter fun L => !L.letters).findSome? fun L =>
            L.batch B.G₀ b.place) = none :=
          List.findSome?_eq_none_iff.2 fun L' hL' =>
            no_batch_at hB hf hL hbL hk L' (List.mem_filter.1 hL').1
        rw [e, hpl]
        unfold partsAt
        dsimp only
        rw [hmaker]
        rfl
      have hmk' : (Fr.batch m.place <|>
          ((base.map join).dropLast.find? fun y => y.place == m.place).map fun b _ => b) =
          some mk := hmk
      rw [hnone] at hmk'
      have hmk'' : (((base.map join).dropLast.find? fun y => y.place == m.place).map
          fun (b : Block S Cl) (_ : S → Except String (List Cl × S)) => b) = some mk := hmk'
      obtain ⟨X, hX, rfl⟩ := Option.map_eq_some_iff.1 hmk''
      exact ⟨X, hX, hG⟩
  have hXm : X ∈ base.map join :=
    (List.dropLast_sublist _).subset (List.mem_of_find?_eq_some hX)
  have hXp : X.place = m.place :=
    eq_of_beq (List.find?_some (p := fun y : Block S Cl => y.place == m.place) hX)
  obtain ⟨b0, h0, rfl⟩ := List.mem_map.1 hXm
  rw [hsame, hpl] at hG
  refine ⟨_, hG, ?_⟩
  rcases hj b0 with e | ⟨x, hx, l, h1, h2, e⟩
  · rw [e] at hXp ⊢
    obtain ⟨p, hp, hpp, rfl⟩ := base_at_lot hB hf hb hL hbL hk h0 (hXp.trans hpl)
    exact ⟨p, hp, hpp, Or.inl rfl⟩
  · have ep : b0.place = b.place := by
      rw [e] at hXp
      exact hXp.trans hpl
    obtain ⟨p, hp, hpp, rfl⟩ := base_at_lot hB hf hb hL hbL hk h0 ep
    rw [e]
    exact ⟨p, hp, hpp, Or.inr ⟨x, hx, l, h1, h2, rfl⟩⟩

/-- The member's name is the name under which it is wrapped. -/
theorem name_of_laid {same : S → S → Bool} {x m b : Block S Cl} {n : String} {a : Place}
    (hF : AsFlat x m) (h : IM.LaidAlone same x b n a) : m.name = n :=
  hF.fields.2.1.trans (IM.alone_name h)

/-- **`MemberAlone`**: at `onlineDescription`, at a place of `AlonePlace`, the member is the lot's
sub-protocol wrapped alone. -/
theorem member_alone : MemberAlone := by
  intro o pol lay KL F Z Bs base c A B O L hL b hbL hk ha m hm hpl
  obtain ⟨x, hF, p, hp, hpp, h⟩ := member_laid Z (pureSeat o Z) Bs base c O.made O.sound O.places
    O.chain L hL b hbL hk m hm hpl
  rcases h with h | ⟨fr, hfr, l, h1, h2, _⟩
  · refine ⟨x, hF, ?_⟩
    rw [name_of_laid hF h]
    exact h
  · exfalso
    rcases ha with ha | ⟨k9, k10, n2, n9⟩ | ⟨hh, n2, n15, h10⟩
    · rw [ha] at h2
      cases h2
    · exact IM.no_behind O.made hp (by rw [hpp]; exact k9) (by rw [hpp]; exact k10)
        (by rw [hpp]; exact ⟨n2, n9⟩) hfr h1 rfl
    · exact IM.no_behind_wide O.made hh hp (by rw [hpp]; exact ⟨n2, n15⟩)
        (by rw [hpp]; exact h10) hfr h1 rfl

/-- The kind at a segment's first place is the first of the segment's hearing kinds. -/
theorem first_kind (l : Nat) (sub : VerifiableInference.Desc.First.ModelPart) :
    ∀ a ∈ VerifiableInference.Desc.First.linkPlaces l sub, a.piece = 1 →
      a.kind ≠ KindName.frame →
      (VerifiableInference.Desc.First.kindsBeforeBatching sub (l == 0))[0]? = some a.kind := by
  cases sub <;> cases hb : (l == 0) <;>
    simp [VerifiableInference.Desc.First.linkPlaces, VerifiableInference.Desc.First.kindsBeforeBatching,
      VerifiableInference.Desc.First.addresses, VerifiableInference.Desc.First.closeAddresses,
      VerifiableInference.Desc.First.closeKinds, VerifiableInference.Desc.First.frameAt,
      VerifiableInference.Desc.First.kindOfModelPart, hb]

/-- **`MemberFirst`**: at `onlineDescription` a member at a segment's first place is the lot's sub-protocol
with the sub-protocol `opened` of the segment's own row laid behind it. The library has it by index
(`IM.joined_at`); the member at the place is that hearing sub-protocol, since both are what one
structure of the driver gives at the place; the lot's sub-protocol is the given one. -/
theorem member_first : MemberFirst := by
  intro o pol lay KL F Z Bs base c A B O l k L hL b hbL hb hk m hm hp
  have hmem : b.place ∈ VerifiableInference.Desc.First.flatPlacesOf (subsOf Z)
      (base.any fun b => b.place.kind == KindName.K13) := by
    rw [← chainBy_places O.chain]
    exact List.mem_map.2 ⟨m, hm, hp⟩
  obtain ⟨sub, hsub, hin⟩ := IM.flat_in_link hmem (by rw [hb])
  have hk0 : (VerifiableInference.Desc.First.kindsBeforeBatching sub (l == 0))[0]? = some k := by
    have h := first_kind l sub b.place hin (by rw [hb]) (by rw [hb]; exact hk)
    rw [hb] at h
    exact h
  obtain ⟨Lk, bi, e1, e2, L', hL', b', hb', ep, hJ⟩ := IM.joined_at O hsub hk0
  have hbi : bi ∈ c.blocksInOrder := mem_flat_of_hear e1 e2
  have hbp : bi.place = ⟨1, some l, 1, k⟩ := by
    obtain ⟨_, _, _, _, e⟩ := hJ
    rw [e]
    rfl
  obtain rfl : b' = b := IM.block_by_place O.sound (IM.base_made O.made).2.2.2 hL' hL hb' hbL
    (by rw [ep]; exact hk) (ep.trans hb.symm)
  obtain ⟨join, Fr, z, _, hfc, _, _⟩ := chainBy_first_fill O.chain
  have h9 : k ≠ KindName.K9 := by
    have h := (IM.link_first_piece l sub b'.place hin (by rw [hb])).1
    rw [hb] at h
    exact h
  have hmp : m.place = ⟨1, some l, 1, k⟩ := hp.trans hb
  have e : m = bi := by
    rcases chain_member hfc hm (by rw [hmp]; exact hk) with ⟨X, hX, _, hx⟩ | ⟨q, _⟩
    · rcases chain_member hfc hbi (by rw [hbp]; exact hk) with ⟨X', hX', _, hx'⟩ | ⟨q, _⟩
      · rw [hmp] at hX
        rw [hbp, hX] at hX'
        obtain rfl := Option.some.inj hX'
        rw [hx (by rw [hmp]; exact fun q => nomatch q), hx' (by rw [hbp]; exact fun q => nomatch q),
          hmp, hbp]
      · rw [hbp] at q
        exact absurd q h9
    · rw [hmp] at q
      exact absurd q h9
  rw [e, hb]
  exact hJ

/-- **`AloneGives`**: the fields, the decision and the step of a member that is wrapped alone. -/
theorem alone_gives : AloneGives := by
  intro same x m b name a hF h
  obtain ⟨f1, f2, f3, f4, f5, f6, _, _⟩ := hF.fields
  have hd : ∀ (t : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (t' : S),
      m.decide t rs gs = .ok t' ↔
        b.decide t rs gs = .ok t' ∧ t'.failed = none ∧
          (a.kind = KindName.K7 ∨ same t t' = true) := by
    intro t rs gs t'
    rw [f6]
    by_cases h7 : a.kind = KindName.K7
    · rw [IM.yes_alone_K7 h h7]
      exact ⟨fun u => ⟨u.1, u.2, Or.inl h7⟩, fun u => ⟨u.1, u.2.1⟩⟩
    · rw [IM.yes_alone h h7]
      exact ⟨fun u => ⟨u.1, u.2.1, Or.inr u.2.2⟩, fun u => ⟨u.1, u.2.1, u.2.2.resolve_left h7⟩⟩
  refine ⟨f1.trans (IM.alone_place h), f2.trans (IM.alone_name h), f3.trans (IM.alone_rounds h),
    f4.trans (IM.alone_oracles h), f5.trans (IM.alone_before h),
    fun t t' rs gs => hd t rs gs t', fun ft t t' k rs cols => ?_⟩
  exact IM.step_iff (Q := fun t t' => t'.failed = none ∧ (a.kind = KindName.K7 ∨ same t t' = true))
    (f3.trans (IM.alone_rounds h)) hd ft t t' k rs cols

/-- **`JoinedAccepts`**: from which acceptances the decision of a member with q laid behind b
accepts. -/
theorem joined_accepts : JoinedAccepts := by
  intro same x m b q name a hF hx t u t' rs gs h1 h2 h3 h4 h5
  rw [hF.fields.2.2.2.2.2.1, hx]
  have e1 : (guardMark b).decide t (rs.take b.rounds.length) (gs.take b.openings) = .ok u :=
    (IM.guardMark_yes b t u _ _).2 ⟨h1, h2⟩
  have e2 : (q.guarded same fun _ => false).decide u (rs.drop b.rounds.length)
      (gs.drop b.openings) = .ok t' :=
    (VerifiableInference.Desc.guarded_yes same (fun _ => false) q rfl u _ _ t').2 ⟨h3, h4⟩
  have e3 : ((IM.marked b name).andThen name (q.guarded same fun _ => false)).decide t rs gs =
      .ok t' := by
    show ((guardMark b).decide t (rs.take b.rounds.length) (gs.take b.openings)).bind (fun v =>
      (q.guarded same fun _ => false).decide v (rs.drop b.rounds.length) (gs.drop b.openings)) = _
    rw [e1]
    exact e2
  show (if hearsReply a = true then
      ((IM.marked b name).andThen name (q.guarded same fun _ => false)).decide t rs gs
    else (((IM.marked b name).andThen name (q.guarded same fun _ => false)).decide t rs gs).bind
      (seatSame same t)) = .ok t'
  rw [e3]
  by_cases h7 : hearsReply a = true
  · rw [if_pos h7]
  · rw [if_neg h7]
    have hs : same t t' = true := h5.resolve_left fun e => h7 (by
      show (a.kind == KindName.K7) = true
      rw [e]
      rfl)
    show seatSame same t t' = .ok t'
    unfold seatSame
    rw [if_pos hs]

/-- The decision behind the driver's guard, at either sort of place. -/
theorem guarded_decides (same : S → S → Bool) (y : Block S Cl) (t : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (t' : S) :
    (Block.guarded same hearsReply y).decide t rs gs = .ok t' ↔
      y.decide t rs gs = .ok t' ∧ (y.place.kind = KindName.K7 ∨ same t t' = true) := by
  by_cases h7 : y.place.kind = KindName.K7
  · have hp : hearsReply y.place = true := by
      show (y.place.kind == KindName.K7) = true
      rw [h7]
      rfl
    show (if hearsReply y.place = true then y.decide t rs gs
      else (y.decide t rs gs).bind (seatSame same t)) = .ok t' ↔ _
    rw [if_pos hp]
    exact ⟨fun u => ⟨u, Or.inl h7⟩, fun u => u.1⟩
  · have hp : hearsReply y.place = false := by
      show (y.place.kind == KindName.K7) = false
      simpa using h7
    rw [VerifiableInference.Desc.guarded_yes same hearsReply y hp]
    exact ⟨fun u => ⟨u.1, Or.inr u.2⟩, fun u => ⟨u.1, u.2.resolve_left h7⟩⟩

/-- **`JoinedGives`**: the fields and the step of a member behind whose sub-protocol the segment's
own row's `opened` is laid. -/
theorem joined_gives : JoinedGives := by
  intro Z l x m b a hF hJ
  obtain ⟨fs, f, hfs, hf, e⟩ := hJ
  obtain ⟨f1, _, f3, f4, f5, f6, _, _⟩ := hF.fields
  have hr : x.rounds = b.rounds := by
    rw [e]
    exact List.append_nil _
  refine ⟨fs, f, hfs, hf, ?_, f3.trans hr, ?_, ?_, fun ft t t' k rs cols => ?_⟩
  · rw [f1, e]
    rfl
  · rw [f4, e]
    exact List.append_nil _
  · rw [f5, e]
    exact List.append_nil _
  · -- the flat list's layer and the driver's guard off
    have s1 : m.step ft t rs cols = .ok (t', k) ↔
        ((IM.marked b x.name).andThen x.name
          ((guardMark (IM.openedOf f).retype : Block S Cl).guarded sameReply fun _ => false)).step
            ft t rs cols = .ok (t', k) ∧
          (a.kind = KindName.K7 ∨ sameReply t t' = true) :=
      IM.step_iff (Q := fun t t' => a.kind = KindName.K7 ∨ sameReply t t' = true)
        (by rw [f3, e]; rfl)
        (fun s rs gs u => by
          rw [f6, e]
          exact guarded_decides sameReply _ s rs gs u) ft t t' k rs cols
    -- the two halves
    rw [s1, VerifiableInference.Desc.andThen_step_noRound _ _ _ rfl]
    have s2 : ∀ u, (IM.marked b x.name).step ft t rs cols = .ok (u, k) ↔
        b.step ft t rs cols = .ok (u, k) ∧ u.failed = none := fun u =>
      IM.step_iff (c := IM.marked b x.name) (d := b) (Q := fun _ u => u.failed = none) rfl
        (fun s rs gs v => IM.guardMark_yes b s v rs gs) ft t u k rs cols
    have s3 : ∀ u, ((guardMark (IM.openedOf f).retype : Block S Cl).guarded sameReply
        fun _ => false).decide u [] [] = .ok t' ↔
        (f.opened u = .ok t' ∧ t'.failed = none) ∧ sameReply u t' = true := fun u => by
      rw [VerifiableInference.Desc.guarded_yes sameReply (fun _ => false) _ rfl,
        IM.guardMark_yes]
      rfl
    constructor
    · rintro ⟨⟨u, a1, a2⟩, a3⟩
      exact ⟨u, ((s2 u).1 a1).1, ((s2 u).1 a1).2, ((s3 u).1 a2).1.1, ((s3 u).1 a2).1.2,
        ((s3 u).1 a2).2, a3⟩
    · rintro ⟨u, a1, a2, a3, a4, a5, a6⟩
      exact ⟨⟨u, (s2 u).2 ⟨a1, a2⟩, (s3 u).2 ⟨⟨a3, a4⟩, a5⟩⟩, a6⟩

/-- **`MemberLast`**: every member at the first chain's last place is the chain's last sub-protocol
as `Chain.blocksInOrder` lays it; that one is kind K13's third lot's, wrapped alone (`IM.seal_seated`). -/
theorem member_last : MemberLast := by
  intro o pol lay KL F Z Bs base c A B O m hm hp
  obtain ⟨b, _, rfl, hA⟩ := IM.seal_seated O
  obtain ⟨join, Fr, z, _, hfc, _, _⟩ := chainBy_first_fill O.chain
  exact ⟨Or.inr (last_member hfc hm (by rw [hp]) (by rw [hp]) (by rw [hp]; decide)), hA⟩

end ProofFile.Honest.AtPlace

#print axioms ProofFile.Honest.AtPlace.mem_all
#print axioms ProofFile.Honest.AtPlace.no_batch_at_block
#print axioms ProofFile.Honest.AtPlace.no_batch_at
#print axioms ProofFile.Honest.AtPlace.base_at_lot
#print axioms ProofFile.Honest.AtPlace.of_find
#print axioms ProofFile.Honest.AtPlace.member_laid
#print axioms ProofFile.Honest.AtPlace.name_of_laid
#print axioms ProofFile.Honest.AtPlace.member_alone
#print axioms ProofFile.Honest.AtPlace.first_kind
#print axioms ProofFile.Honest.AtPlace.member_first
#print axioms ProofFile.Honest.AtPlace.alone_gives
#print axioms ProofFile.Honest.AtPlace.joined_accepts
#print axioms ProofFile.Honest.AtPlace.guarded_decides
#print axioms ProofFile.Honest.AtPlace.joined_gives
#print axioms ProofFile.Honest.AtPlace.member_last
