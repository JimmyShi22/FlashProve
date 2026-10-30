-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/GroupArrays.lean:
WHAT A SENDING OF KIND K1 DOES TO THE TWO ARRAYS OF THE GROUP THAT ITS MESSAGES JOIN: THE
NEW MESSAGES' NUMBERS ARE LAID BEHIND THE MEMBERS, IN THE ORDER OF SENDING, AND THEIR FLAGS BEHIND
THE FLAGS "kept". Definitions, and statements with their proofs. It stands beside Joins
(Johnson/Desc/K1/Law/GroupAtRecord.lean), which says who the members are and nothing on their order.
Why. The joining lays a message "at the place of its number among the smaller numbers"
(OnBytes.Slice.withMessageInGroup). A new message's number is above every member's: so there it is an appending.
OBJECT. commitAtS (Johnson/Desc/K1/AtS.lean), so laterAt; firstSegmentOpening, where the group is new. (The
reads' place's joined sub-protocol k1Reads: Johnson/Desc/K1/Law/GroupArraysReads.lean.)
USER. The walk of K02_law.
  insert_end, filter_all: an entry laid at an array's end.
  Grown G G' ids fl   G'.members = G.members ++ ids; and, WHERE G HAS A FLAG A MEMBER, G'.kept =
                      G.kept ++ fl. Grown.refl, Grown.cons.
  joinP_grown, joinAll_grown, joinOwnP_grown: one message; a list; a moment's own messages.
  ids_list, ids_pairwise, ids_ge: the new numbers n₀, n₀ + 1, ...  flagsAt f: the moment's flags:
                      does the message live on (life > 0)?
  commitOwn_arrays    the kind's block. LaterArrays P B: the sentence, of a block at the chain's
                      state.
  laterArrays_commitAtS, _laterAt: **its members.** (_joined, _k1Reads: GroupArraysReads.lean.)
  newGroupP_new, firstOwn_arrays, firstAtS_arrays: **the first segment's opening.**
  Grown.nodup, Grown.nodup_ids: (A6) no number twice in front, none behind.
  newShape_of, commitAtS_newShape: (A5, at the new members) the i-th new message has the shape that
                      the sending announced.
PREMISES THAT STAY, at a later moment. Every member in front is below the statement's number of
messages. FOR THE FLAGS ONE MORE THAN WAS FIRST ASKED FOR: G.kept.size = G.members.size: the
joining lays the flag at THE MEMBERS' count: with fewer flags it lays none, with more it lays it in
their midst. (Grown keeps that equation: Grown.cons spends it so.) At the opening: none.
What is not claimed. That these two hold of any state. Nothing on soundness, on an honest prover or
on hiding.




-/
import Johnson.Desc.K1.Law.GroupAtLater
import Johnson.Desc.K1.Law.ShapesAtRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice _root_.Desc.Plain
open VerifiableInference.Desc.First.Send (joinOwnP joinAll)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Ground (shapesIn)

variable {L Cl : Type}

/-! ## Laying an entry at an array's end -/

theorem insert_end {α : Type} (xs : Array α) (a : α) :
    xs.insertIdxIfInBounds xs.size a = xs.push a := by
  unfold Array.insertIdxIfInBounds
  rw [dif_pos (Nat.le_refl _)]
  apply Array.toList_inj.1
  simp

theorem filter_all (xs : Array Nat) (o : Nat) (h : ∀ x ∈ xs, x < o) :
    (xs.filter (· < o)).size = xs.size := by
  rw [Array.filter_eq_self.2 fun a ha => by simpa using h a ha]

/-- **Group G' is group G with ids laid behind its members and fl behind its flags "kept"** (the
flags: where G has a flag a member). -/
def Grown (G G' : Group) (ids : List Nat) (fl : List Bool) : Prop :=
  G'.members = G.members ++ ids.toArray ∧
    (G.kept.size = G.members.size → G'.kept = G.kept ++ fl.toArray)

theorem Grown.refl (G : Group) : Grown G G [] [] := ⟨by simp, fun _ => by simp⟩

theorem Grown.cons {G G₁ G₂ : Group} {o : Nat} {k : Bool} {ids : List Nat} {fl : List Bool}
    (h : Grown G G₁ [o] [k]) (h' : Grown G₁ G₂ ids fl) : Grown G G₂ (o :: ids) (k :: fl) := by
  refine ⟨?_, fun hk => ?_⟩
  · rw [h'.1, h.1]
    apply Array.toList_inj.1
    simp
  · have e1 := h.2 hk
    have hk1 : G₁.kept.size = G₁.members.size := by
      rw [e1, h.1]
      simp [hk]
    rw [h'.2 hk1, e1]
    apply Array.toList_inj.1
    simp

/-- One message joins above every member. -/
theorem joinP_grown (d d' : DState L) (g o : Nat) (kept : Bool)
    (h : Ground.joinP d g o kept = some d') (G : Group) (hG : d.st.groups[g]? = some G)
    (hab : ∀ x ∈ G.members, x < o) :
    ∃ G', d'.st.groups[g]? = some G' ∧ Grown G G' [o] [kept] := by
  obtain ⟨G₀, hG₀, _, e⟩ := Later.joinP_inv d d' g o kept h
  obtain rfl : G₀ = G := Option.some.inj (hG₀.symm.trans hG)
  refine ⟨{ G₀ with
    members := G₀.members.insertIdxIfInBounds (G₀.members.filter (· < o)).size o
    kept := G₀.kept.insertIdxIfInBounds (G₀.members.filter (· < o)).size kept }, ?_, ?_, ?_⟩
  · rw [e]
    show (d.st.groups.modify g _)[g]? = _
    rw [Array.getElem?_modify, if_pos rfl, hG]
    rfl
  · show G₀.members.insertIdxIfInBounds (G₀.members.filter (· < o)).size o = _
    rw [filter_all _ _ hab, insert_end]
    apply Array.toList_inj.1
    simp
  · intro hk
    show G₀.kept.insertIdxIfInBounds (G₀.members.filter (· < o)).size kept = _
    rw [filter_all _ _ hab, ← hk, insert_end]
    apply Array.toList_inj.1
    simp

/-- A list of messages joins, each above all that stand there. -/
theorem joinAll_grown (p : GPar) (g : Nat) : ∀ (l : List (ReqMessage × Nat)) (d d' : DState L),
    joinAll groundG p g l d = some d' → ∀ G : Group, d.st.groups[g]? = some G →
    (∀ x ∈ G.members, ∀ y ∈ l.map Prod.snd, x < y) → (l.map Prod.snd).Pairwise (· < ·) →
    ∃ G', d'.st.groups[g]? = some G' ∧
      Grown G G' (l.map Prod.snd) (l.map fun x => decide (0 < x.1.life))
  | [], d, d', h, G, hG, _, _ => by
    obtain rfl := Option.some.inj h
    exact ⟨G, hG, Grown.refl G⟩
  | x :: l, d, d', h, G, hG, hab, hp => by
    obtain ⟨e, h1, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨G₁, hG₁, g1⟩ := joinP_grown d e g x.2 _ h1 G hG
      fun z hz => hab z hz x.2 (by simp)
    rw [List.map_cons, List.pairwise_cons] at hp
    obtain ⟨G₂, hG₂, g2⟩ := joinAll_grown p g l e d' h2 G₁ hG₁ (fun z hz y hy => by
      rw [g1.1] at hz
      rcases Array.mem_append.1 hz with hz | hz
      · exact hab z hz y (by rw [List.map_cons]; exact List.mem_cons_of_mem _ hy)
      · obtain rfl : z = x.2 := by simpa using hz
        exact hp.1 y hy) hp.2
    exact ⟨G₂, hG₂, g1.cons g2⟩

/-- A moment's own messages join the frame's group. -/
theorem joinOwnP_grown (p : GPar) (d : DState L) (f : ReqFrame) (sent : List ReqMessage)
    (ids : Array Nat) (y : ReqFrame × DState L) (h : joinOwnP groundG p d f sent ids = some y)
    (G : Group) (hG : d.st.groups[f.group]? = some G)
    (hab : ∀ x ∈ G.members, ∀ z ∈ ids.toList, x < z) (hp : ids.toList.Pairwise (· < ·)) :
    ∃ G', y.2.st.groups[f.group]? = some G' ∧
      Grown G G' ids.toList (sent.map fun x => decide (0 < x.life)) := by
  unfold joinOwnP at h
  split at h
  · rename_i hl
    obtain ⟨d', h1, rfl⟩ := Option.map_eq_some_iff.1 h
    have hlen : sent.length = ids.toList.length := by
      rw [Array.length_toList]
      exact eq_of_beq hl
    have e1 : (zipT sent ids.toList).map Prod.snd = ids.toList := by
      rw [zipT_eq, List.map_snd_zip (Nat.le_of_eq hlen.symm)]
    have e2 : ((zipT sent ids.toList).map fun x => decide (0 < x.1.life)) =
        sent.map fun x => decide (0 < x.life) := by
      have : ((zipT sent ids.toList).map fun x => decide (0 < x.1.life)) =
          ((zipT sent ids.toList).map Prod.fst).map fun x => decide (0 < x.life) := by
        rw [List.map_map]
        rfl
      rw [this, zipT_eq, List.map_fst_zip (Nat.le_of_eq hlen)]
    have hj := joinAll_grown p f.group _ d d' h1 G hG (by rw [e1]; exact hab) (by rw [e1]; exact hp)
    rw [e1, e2] at hj
    exact hj
  · cases h

/-! ## The new messages' numbers -/

theorem ids_list (P : Par) (n₀ : Nat) :
    (idsOf P n₀).toList = (List.range P.sent.size).map (· + n₀) := by
  unfold idsOf
  rw [Array.toList_map, Array.toList_range]

theorem ids_pairwise (P : Par) (n₀ : Nat) : (idsOf P n₀).toList.Pairwise (· < ·) := by
  rw [ids_list]
  exact List.pairwise_lt_range.map _ fun a b h => Nat.add_lt_add_right h n₀

theorem ids_ge (P : Par) (n₀ z : Nat) (h : z ∈ (idsOf P n₀).toList) : n₀ ≤ z := by
  rw [ids_list] at h
  obtain ⟨i, _, rfl⟩ := List.mem_map.1 h
  exact Nat.le_add_left _ _

/-- The flags "kept" of a moment's messages: does the message live on? -/
def flagsAt (f : ReqFrame) : List Bool := (f.atMoment f.moment).map fun x => decide (0 < x.life)

/-! ## A later moment's sending -/

/-- **The kind's block.** -/
theorem commitOwn_arrays (P : Par) (link moment : Nat) (arrays : Option (List Nat))
    (s s' : Owing (L3.St (DState Unit))) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitOwn P link moment arrays : Block _ Cl).decide s [r₁, r₂] gs = .ok s') (G : Group)
    (hG : s.held.w.st.groups[s.held.L.check.frame.group]? = some G)
    (hab : ∀ o ∈ G.members, o < s.held.w.st.oracles.size) :
    ∃ G', s'.held.w.st.groups[s.held.L.check.frame.group]? = some G' ∧
      Grown G G' (idsOf P s.held.w.st.oracles.size).toList (flagsAt s.held.L.check.frame) := by
  unfold commitOwn at h
  dsimp only at h
  split at h
  · split at h
    · cases h
    · obtain ⟨t, ht, rfl⟩ := (map_ok _ _ _).1 h
      unfold L3.commitStep at ht
      obtain ⟨_, _, ht⟩ := (bind_ok _ _ _).1 ht
      obtain ⟨⟨check, w⟩, h2, ht⟩ := (bind_ok _ _ _).1 ht
      obtain ⟨⟨Lk, F⟩, h3, ht⟩ := (bind_ok _ _ _).1 ht
      have e : ({ s.held with L := Lk, F := F, w := w } : L3.St (DState Unit)) = t := by
        simpa [pure, Except.pure] using ht
      obtain ⟨ids, d₁, f', a1, a2, a3⟩ := laterOwn_ok P s.owed _ _ _ _ _ h2
      obtain ⟨_, hids, _⟩ := (decideSend_iff P s.owed _ d₁ r₁ r₂ ids).1 a1
      have hk : d₁.st.groups = s.held.w.st.groups := (decideSend_kept P s.owed _ d₁ _ ids a1).2.1
      subst hids
      obtain ⟨G', g1, g2⟩ := joinOwnP_grown _ _ _ _ _ _ a2 G (by rw [hk]; exact hG)
        (fun x hx z hz => Nat.lt_of_lt_of_le (hab x hx) (ids_ge P _ z hz)) (ids_pairwise P _)
      rw [← e]
      exact ⟨G', g1, g2⟩
  · cases h

/-- **A block of a later moment's sending of the place P**: what an accepting run of it on two
rounds does to the open link's group's two arrays. -/
def LaterArrays (P : Par) (B : Block S Cl) : Prop :=
  ∀ s s' rs gs, rs.length = 2 → B.decide s rs gs = .ok s' →
    ∃ Lk, s.link? = some Lk ∧ ∀ G : Group, s.st.groups[Lk.check.frame.group]? = some G →
      (∀ o ∈ G.members, o < s.st.oracles.size) →
      ∃ G', s'.st.groups[Lk.check.frame.group]? = some G' ∧
        Grown G G' (idsOf P s.st.oracles.size).toList (flagsAt Lk.check.frame)

/-- The sending alone. -/
theorem laterArrays_commitAtS (P : Par) (link moment : Nat) (arrays : Option (List Nat)) :
    LaterArrays P (commitAtS P link moment arrays : Block S Cl) := by
  intro s s' rs gs h2 h
  obtain ⟨r₁, r₂, rfl⟩ := List.length_eq_two.1 h2
  unfold commitAtS at h
  dsimp only at h
  split at h
  · rename_i Lk F tl hL _ _
    obtain ⟨y, hy, rfl⟩ := (map_ok _ _ _).1 h
    refine ⟨Lk, hL, fun G hG hab => ?_⟩
    rw [st_put]
    exact commitOwn_arrays P link moment arrays _ y r₁ r₂ gs hy G hG hab
  · cases h

theorem laterArrays_laterAt (q : Params.First) (gp : GPar) (link piece moment : Nat)
    (arrays : Option (List Nat)) :
    LaterArrays (parLater q gp link piece moment)
      (laterAt q gp link piece moment arrays : Block S Cl) :=
  laterArrays_commitAtS _ _ _ _

/-! ## The first segment's opening: the group is new -/

theorem newGroupP_new (d d' : DState L) (code maskCode n : Nat)
    (h : Ground.newGroupP d code maskCode = some (n, d')) :
    ∃ G : Group, d'.st.groups[n]? = some G ∧ G.members = #[] ∧ G.kept = #[] := by
  unfold Ground.newGroupP at h
  split at h
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨{ code := code, maskCode := maskCode }, ?_, rfl, rfl⟩
    show (d.st.groups.push _)[d.st.groups.size]? = _
    rw [Array.getElem?_push_size]
  · cases h

/-- **The opening's decision**: the new group's members are the segment's own messages of the first
moment, in the order of sending, each with its flag. -/
theorem firstOwn_arrays (P : Par) (owed : Option Nat) (c c' : ChainCheck) (d d' : DState Unit)
    (r₁ r₂ : Fmt.RoundView) (h : firstOwn P owed c d [r₁, r₂] = .ok (c', d')) :
    ∃ G' : Group, d'.st.groups[d.st.groups.size]? = some G' ∧
      G'.members = (idsOf P d.st.oracles.size).extract 0 (c.frame.atMoment 0).length ∧
      G'.kept = ((c.frame.atMoment 0).map fun x => decide (0 < x.life)).toArray := by
  unfold firstOwn at h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨g, d₁⟩, h1, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨ids, d₂⟩, h2, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨mask, hmask, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨f₂, d₃⟩, h3, hfin⟩ := (bind_ok _ _ _).1 h
  obtain ⟨_, hids, _⟩ := (decideSend_iff P owed d₁ d₂ r₁ r₂ ids).1 h2
  have hg := (named_ok _ _ _).1 h1
  obtain ⟨rfl, _, _, _⟩ := newGroupP_group _ _ _ _ _ hg
  obtain ⟨G, n3, n6, n7⟩ := newGroupP_new _ _ _ _ _ hg
  have hn := (newGroupP_book _ _ _ _ _ hg).2
  have hk : d₂.st.groups = d₁.st.groups := (decideSend_kept P owed d₁ d₂ _ ids h2).2.1
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hfin)
  subst hids
  obtain ⟨G', g1, g2⟩ := joinOwnP_grown _ _ _ _ _ _ ((named_ok _ _ _).1 h3) G
    (by rw [hk]; exact n3) (fun x hx => by rw [n6] at hx; simp at hx) (by
      rw [Array.toList_extract, List.extract_eq_take_drop, List.drop_zero, Nat.sub_zero]
      exact (ids_pairwise P _).sublist (List.take_sublist _ _))
  refine ⟨G', g1, ?_, ?_⟩
  · rw [g2.1, n6, hn, Array.toArray_toList]
    rw [Array.empty_append]
    rfl
  · rw [g2.2 (by simp [n6, n7]), n7]
    simp

/-- **The block at the chain's state.** -/
theorem firstAtS_arrays (q : Params.First) (gp : GPar) (s s' : S) (r₁ r₂ : Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : (firstSegmentOpening q gp : Block S Cl).decide s [r₁, r₂] gs = .ok s') :
    ∃ G' : Group, s'.st.groups[s.st.groups.size]? = some G' ∧
      G'.members = (idsOf (firstPar q gp) s.st.oracles.size).extract 0
        (s.check.frame.atMoment 0).length ∧
      G'.kept = ((s.check.frame.atMoment 0).map fun x => decide (0 < x.life)).toArray := by
  unfold firstSegmentOpening at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
  obtain ⟨⟨c, d'⟩, h2, h⟩ := (bind_ok _ _ _).1 h
  obtain rfl := Except.ok.inj h
  exact firstOwn_arrays _ _ _ c _ d' r₁ r₂ h2

/-! ## Beside: no number twice; the new members' shapes -/

/-- (A6) Where no number stands twice among the members, none does behind. -/
theorem Grown.nodup {G G' : Group} {ids : List Nat} {fl : List Bool} (h : Grown G G' ids fl)
    (hn : G.members.toList.Nodup) (hab : ∀ x ∈ G.members, ∀ z ∈ ids, x < z)
    (hp : ids.Pairwise (· < ·)) : G'.members.toList.Nodup := by
  rw [h.1, Array.toList_append]
  refine List.Nodup.append hn (hp.imp fun h => Nat.ne_of_lt h) fun a h1 h2 => ?_
  exact Nat.lt_irrefl a (hab a (Array.mem_toList_iff.1 h1) a (by simpa using h2))

/-- (A6) at a sending's own numbers. -/
theorem Grown.nodup_ids {G G' : Group} {P : Par} {n₀ : Nat} {fl : List Bool}
    (h : Grown G G' (idsOf P n₀).toList fl) (hn : G.members.toList.Nodup)
    (hab : ∀ o ∈ G.members, o < n₀) : G'.members.toList.Nodup :=
  h.nodup hn (fun x hx z hz => Nat.lt_of_lt_of_le (hab x hx) (ids_ge P _ z hz)) (ids_pairwise P _)

/-- (A5, at the new members) The i-th new message has the shape that the sending announced. -/
theorem newShape_of {st st' : Statement} {x : List OracleShape}
    (e : shapesIn st' = shapesIn st ++ x) (i : Nat) :
    (st'.oracles[st.oracles.size + i]?).map (·.shape) = x[i]? := by
  have hl : (shapesIn st).length = st.oracles.size := by simp [shapesIn]
  have e1 : (shapesIn st')[st.oracles.size + i]? = x[i]? := by
    rw [e, List.getElem?_append_right (by rw [hl]; omega), hl, Nat.add_sub_cancel_left]
  unfold shapesIn at e1
  rw [List.getElem?_map, Array.getElem?_toList] at e1
  exact e1

theorem commitAtS_newShape (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (s s' : S)
    (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (h : (commitAtS P link moment arrays : Block S Cl).decide s [r₁, r₂] gs = .ok s') (i : Nat) :
    (s'.st.oracles[s.st.oracles.size + i]?).map (·.shape) = (shapesOf P)[i]? :=
  newShape_of (commitAtS_shapesIn P link moment arrays s s' r₁ r₂ gs h) i

end VerifiableInference.Desc.K1
