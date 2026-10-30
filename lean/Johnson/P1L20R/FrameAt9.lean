-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1L20R/FrameAt9.lean:
at the composed meaning mgAll Dm mgBase (Johnson/Desc/Sound/MgAll.lean, MgBase.lean),
whatever the parameters Dm: two of the fields of LettersRide (Johnson/Top/H0/Walk/FrameTied.lean) at
the link's frame's 51 sub-protocols: "inOrder" and "pub".

  our51             the numbers of the 51 in the flat list: the front, 25 "laid", 25 "cleared"
  idleB_full, door_idle9   at each of the 51 the public row of the table, joined with the list of
                    extra public tests (the closed term mgMore), makes no public item, and the
                    table's row opens no item: by Lean's kernel
  pubBehindB_full, pub_behind9   the public items that the promise asks at the border behind a
                    "cleared" (the open ones, and those tied to open items) are among three: "no
                    reply is heard yet", "the index-mask message's number is the listed one", "a
                    message of that number is there": by Lean's kernel
  cleared_out       an accepting "cleared" leaves s.out.reply and s.out.indexMasks; a message of
                    that number is there behind if it was in front
  inOrder9          "in order" reads the public part alone
  pub_clear9        LettersRide's field "pub" at an accepting "cleared"



Limits. The other fields of LettersRide (decodes, pubP, held, shown, noColl, items) are not touched
here. No soundness statement.

-/
import Johnson.P1L20R.FramePays
import Johnson.Desc.Sound.MgBase
import Johnson.Top.H0.Walk.FrameLedgerAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1L20

open VerifiableInference.Desc (Place KindName Strs)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers start openSets pubSets pubRowM
  pubOfItems rowOf flatPlacesOf)
open Johnson.Desc.First.Walk (clearWith LinkPub)
open Johnson.Desc.First.Walk.Tied

/-- The frame's 51 numbers. -/
def our51 : List ℕ :=
  0 :: ((List.range 25).map fun l => 14 * l + 1) ++ (List.range 25).map fun l => clearIx l

/-- A test with code: at these numbers the table's public row, joined with the list of extra public
tests, makes no public item, and the table's row opens no item. -/
def idleB : Bool :=
  our51.all fun k =>
    match (flatPlacesOf linksFull true)[k]? with
    | some p => (pubRowM mgMore linksFull p).makes.isEmpty && (rowOf linksFull p).outs.isEmpty
    | none => false

set_option maxRecDepth 1000000 in
theorem idleB_full : idleB = true := by decide +kernel

theorem idle_at {k : ℕ} (hk : k ∈ our51) :
    ∃ p, (flatPlacesOf linksFull true)[k]? = some p ∧ (pubRowM mgMore linksFull p).makes = [] ∧
      (rowOf linksFull p).outs = [] := by
  have h := List.all_eq_true.1 idleB_full k hk
  cases hp : (flatPlacesOf linksFull true)[k]? with
  | none => rw [hp] at h; cases h
  | some p =>
    rw [hp] at h
    simp only [Bool.and_eq_true, List.isEmpty_iff] at h
    exact ⟨p, rfl, h.1, h.2⟩

/-- A test with code: the two lists have a border behind each "cleared", and the public items that
the promise asks there are among three. -/
def pubBehindB : Bool :=
  (List.range 25).all fun l =>
    ((pubSets mgMore linksFull (flatPlacesOf linksFull true))[clearIx l + 1]?).isSome &&
    ((openSets linksFull (flatPlacesOf linksFull true) (start linksFull))[clearIx l + 1]?).isSome &&
    ((pubSets mgMore linksFull (flatPlacesOf linksFull true))[clearIx l + 1]?.getD [] ++
      pubOfItems ((openSets linksFull (flatPlacesOf linksFull true)
        (start linksFull))[clearIx l + 1]?.getD [])).all fun q =>
      q == Pub.unheard || q == Pub.indexIs || q == Pub.indexThere

set_option maxRecDepth 1000000 in
theorem pubBehindB_full : pubBehindB = true := by decide +kernel

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi P Tok rows cols nR X)

/-- **At the frame's 51 places no public item is made and no item is opened.** -/
theorem door_idle9 {k : ℕ} (hk : k ∈ our51) :
    ∃ p, (flatPlacesOf linksFull true)[k]? = some p ∧ DoorIdle (mgAll Dm mgBase) linksFull p ∧
      (rowOf linksFull p).outs = [] := by
  obtain ⟨p, h1, h2, h3⟩ := idle_at hk
  refine ⟨p, h1, ?_, h3⟩
  unfold DoorIdle
  rw [mgAll_more_base]
  exact h2

theorem pub_behind9 {l : ℕ} (hl : l < 25) {q : Pub}
    (hq : q ∈ (pubSets (mgAll Dm mgBase).more linksFull
        (flatPlacesOf linksFull true))[clearIx l + 1]?.getD [] ++
      pubOfItems ((openSets linksFull (flatPlacesOf linksFull true)
        (start linksFull))[clearIx l + 1]?.getD [])) :
    q = Pub.unheard ∨ q = Pub.indexIs ∨ q = Pub.indexThere := by
  rw [mgAll_more_base] at hq
  have h0 := List.all_eq_true.1 pubBehindB_full l (List.mem_range.2 hl)
  simp only [Bool.and_eq_true] at h0
  have h := List.all_eq_true.1 h0.2 q hq
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (h | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

/-- **"In order" reads the public part alone.** -/
theorem inOrder9 (p : P) (s t : S) (h : (mgAll Dm mgBase).inOrder (p, s) = true) :
    (mgAll Dm mgBase).inOrder (p, t) = true := by
  rw [mgAll_inOrder_base] at h ⊢
  exact h

end

/-- What an accepting "cleared" leaves of s.out. -/
theorem cleared_out {X : LinkPub} {counts : S → Except String Unit}
    {left : S → Option OnBytes.Model.WsForkOut} {lay : OnBytes.Model.WsLay}
    {lin : OnBytes.Params.LinShape} {s t : S}
    (h : clearWith X counts left
      (fun im w n os => VerifiableInference.Desc.First.Pend.pendingRowO lay im w n lin os) s =
        .ok t) :
    t.out.reply = s.out.reply ∧ t.out.indexMasks = s.out.indexMasks ∧
      ((s.st.oracles[s.out.indexMasks]?).isSome = true →
        (t.st.oracles[t.out.indexMasks]?).isSome = true) := by
  obtain ⟨C, F, _, _, _, _, _, _, _, _, _, h0, hrow⟩ := Johnson.Desc.First.Walk.Law.clearWith_ok h
  cases hv : X.fv with
  | false =>
    obtain ⟨e1, e2⟩ := h0 hv
    rw [e1, e2]
    exact ⟨rfl, rfl, id⟩
  | true =>
    obtain ⟨w, r, os, _, _, hout, _⟩ := hrow hv
    obtain ⟨l, c, l', r', β, _, _, hst, _, _, him⟩ := cleared_st h hv
    refine ⟨by rw [hout]; rfl, him, fun hs => ?_⟩
    rw [hst, him, lay_at]
    cases hx : s.st.oracles[s.out.indexMasks]? with
    | none => rw [hx] at hs; cases hs
    | some x => rfl

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi P Tok rows cols nR X)

/-- **LettersRide's field "pub" at "cleared"**, at the composed meaning, whatever Dm and N. -/
theorem pub_clear9 {N : Numbers} {l : ℕ} (hl : l < 25) {Xl : LinkPub}
    {counts : S → Except String Unit} {left : S → Option OnBytes.Model.WsForkOut}
    {lay : OnBytes.Model.WsLay} {lin : OnBytes.Params.LinShape} (p : P) (s t : S) (y : Strs)
    (q : Pub)
    (h : clearWith Xl counts left
      (fun im w n os => VerifiableInference.Desc.First.Pend.pendingRowO lay im w n lin os) s =
        .ok t)
    (hu : s.failed = none)
    (hF : FrontAt N (mgAll Dm mgBase) linksFull (flatPlacesOf linksFull true) (clearIx l) (p, s) y)
    (hq : q ∈ (pubSets (mgAll Dm mgBase).more linksFull
        (flatPlacesOf linksFull true))[clearIx l + 1]?.getD [] ++
      pubOfItems ((openSets linksFull (flatPlacesOf linksFull true)
        (start linksFull))[clearIx l + 1]?.getD [])) :
    (mgAll Dm mgBase).pub q (p, t) = true := by
  have hk : clearIx l ∈ our51 := by
    unfold our51
    exact List.mem_cons_of_mem _ (List.mem_append_right _
      (List.mem_map.2 ⟨l, List.mem_range.2 hl, rfl⟩))
  obtain ⟨pk, h1, h2, h3⟩ := door_idle9 Dm hk
  have hs : (mgAll Dm mgBase).pub q (p, s) = true := pub_of_kept h1 h3 h2 hu hF hq
  obtain ⟨g1, g2, g3⟩ := cleared_out h
  rw [mgAll_pub] at hs ⊢
  rcases pub_behind9 Dm hl hq with rfl | rfl | rfl
  · rw [VerifiableInference.Desc.First.pubAll_unheard] at hs ⊢
    unfold VerifiableInference.Desc.First.unheardB at hs ⊢
    rw [g1]
    exact hs
  · rw [VerifiableInference.Desc.First.pubAll_indexIs] at hs ⊢
    unfold VerifiableInference.Desc.K13.indexIsC at hs ⊢
    rw [g2]
    exact hs
  · rw [VerifiableInference.Desc.First.pubAll_indexThere] at hs ⊢
    unfold VerifiableInference.Desc.K13.indexThereC at hs ⊢
    exact g3 hs

end

end P1L20

#print axioms P1L20.idleB_full
#print axioms P1L20.pubBehindB_full
#print axioms P1L20.door_idle9
#print axioms P1L20.inOrder9
#print axioms P1L20.pub_clear9
