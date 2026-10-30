-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/Writes3.lean: what the sending's decision asks and what it writes, as one
equivalence on the carried record.

Main names: recvD, recvP_iff (the receiving); range_zip_tag, tag_pairwise, increasing_of_pairwise,
tag_get, cutSeeds_length; shapesOf, behind (the record behind the sending, one written term), asks
(what the decision asks); decideSend_iff.
Two of the decision's tests never refuse: that the sampled messages' numbers rise, and that none was
sampled before: the second half of decideSend_iff's proof makes both out of what the receiving
returns.
Plain records and pure functions of the verifier program are named, none that takes a context or
runs: layTrees, Slice.stSent, Slice.partsLaid, Slice.treesSent.

What is not claimed. The equivalence is of the decision bare, at two rounds; that a round holds and
draws what the kind's rounds say is asked in front of it (roundsFit). "No factor is 0" is judged on
the words as they are drawn, not on what they read as. Nothing on what a row means, on soundness, on
an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.Writes2
import Johnson.Desc.Own.TreesAgree
import Johnson.Desc.Own.RisingAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain

variable {L : Type}

/-! ## The statement's page receives the messages -/

/-- The record behind the receiving: the messages stand in the statement as received, their trees in
the book. -/
def recvD (ft : Nat) (d : DState L) (sent : Array OracleNotice) (lay : TreeLay) : DState L :=
  { d with
    st := Slice.stSent d.st sent
    book :=
      { trees := Slice.partsLaid sent lay d.st.oracles.size d.book.trees.size
          (Slice.treesSent ft lay.shapes.toList d.roots d.book.trees)
        place := d.book.place ++ (Array.range sent.size).map fun i =>
          (d.book.trees.size + lay.tree.getD i 0, lay.part.getD i 0) }
    roots := d.roots + lay.shapes.size }

theorem recvP_iff (ft : Nat) (d d₁ : DState L) (sent : Array OracleNotice) (ids : Array Nat) :
    Ground.recvP ft d sent = some (ids, d₁) ↔
      Ground.ok (Ground.recvL d.st d.book sent) = true ∧
        ∃ lay, layTrees d.st.codes sent = some lay ∧
        ids = (Array.range sent.size).map (· + d.st.oracles.size) ∧ d₁ = recvD ft d sent lay := by
  unfold Ground.recvP
  simp only [Own.treesMade_eq]
  by_cases hok : Ground.ok (Ground.recvL d.st d.book sent) = true
  · rw [if_pos hok]
    simp only [hok, true_and, Option.map_eq_some_iff, Prod.mk.injEq]
    constructor
    · rintro ⟨lay, h, rfl, rfl⟩
      exact ⟨lay, h, rfl, rfl⟩
    · rintro ⟨lay, h, rfl, rfl⟩
      exact ⟨lay, h, rfl, rfl⟩
  · simp [hok]

/-! ## The numbers -/

theorem range_zip_tag : ∀ (shapes : List OracleShape) (n0 : Nat),
    ((List.range shapes.length).map (· + n0)).zip shapes = tag n0 shapes
  | [], _ => by simp [tag]
  | s :: l, n0 => by
    have e : ((fun x => x + n0) ∘ Nat.succ) = (· + (n0 + 1)) := by
      funext x
      simp only [Function.comp]
      omega
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.zip_cons_cons,
      tag, e, range_zip_tag l (n0 + 1)]
    simp

theorem tag_ge : ∀ (shapes : List OracleShape) (o : Nat) (p : Nat × OracleShape),
    p ∈ tag o shapes → o ≤ p.1
  | [], _, _, h => by simp [tag] at h
  | s :: l, o, p, h => by
    simp only [tag, List.mem_cons] at h
    rcases h with rfl | h
    · exact Nat.le_refl _
    · exact Nat.le_of_succ_le (tag_ge l (o + 1) p h)

theorem tag_pairwise : ∀ (shapes : List OracleShape) (o : Nat),
    ((tag o shapes).map (·.1)).Pairwise (· < ·)
  | [], _ => by simp [tag]
  | s :: l, o => by
    simp only [tag, List.map_cons, List.pairwise_cons]
    refine ⟨fun b hb => ?_, tag_pairwise l (o + 1)⟩
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hb
    exact tag_ge l (o + 1) p hp

theorem increasing_of_pairwise : ∀ l : List Nat, l.Pairwise (· < ·) → Fmt.increasing l = true
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: l, h => by
    have h' := List.pairwise_cons.1 h
    rw [Fmt.increasing]
    simp [h'.1 b (by simp), increasing_of_pairwise (b :: l) h'.2]

theorem tag_get (A : Array OnBytes.Oracle) : ∀ (shapes : List OracleShape)
    (pre : List OnBytes.Oracle), A.toList = pre ++ shapes.map fresh →
    ∀ p ∈ tag pre.length shapes, A[p.1]? = some (fresh p.2)
  | [], _, _, p, hp => by simp [tag] at hp
  | s :: l, pre, h, p, hp => by
    have h' : A.toList = pre ++ fresh s :: l.map fresh := by simpa using h
    simp only [tag, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact get_mid _ _ _ _ h'
    · have := tag_get A l (pre ++ [fresh s]) (by simp [h']) p (by simpa using hp)
      exact this

theorem cutSeeds_length (v : Nat) : ∀ (n : Nat) (l : List E), (cutSeeds v n l).length = n
  | 0, _ => rfl
  | n + 1, l => by simp [cutSeeds, cutSeeds_length v n]

/-! ## The sending's decision -/

/-- The shapes of the place's messages, in the order of sending. -/
def shapesOf (P : Par) : List OracleShape := P.sent.toList.map (·.shape)

/-- **The record behind the sending**, as one written term. -/
def behind (P : Par) (d : DState L) (seeds : List (List E × E)) (ys : List E) : DState L :=
  put (recvD P.gp.firstTree d P.sent ((layTrees P.codes P.sent).getD {}))
    (d.st.oracles.toList ++ outs P.codes seeds d.st.oracles.size (shapesOf P) ys)

/-- What the sending's decision asks. -/
def asks (P : Par) (owed : Option Nat) (d : DState L) (r₁ r₂ : Fmt.RoundView) : Prop :=
  owed = none ∧ d.st.codes = P.codes ∧ (∀ s ∈ seedsOf P r₁, isZeroE s.2 = false) ∧
    Ground.ok (Ground.recvL d.st d.book P.sent) = true ∧
    fitB P.codes P.seeds (shapesOf P) (answersIn r₂) = true

theorem recvD_toList (ft : Nat) (d : DState L) (P : Par) (lay : TreeLay) :
    (recvD ft d P.sent lay).st.oracles.toList =
      d.st.oracles.toList ++ (shapesOf P).map fresh := by
  simp [recvD, Slice.stSent, shapesOf, fresh, Function.comp_def]

theorem ids_zip (P : Par) (n0 : Nat) :
    ((Array.range P.sent.size).map (· + n0)).toList.zip (P.sent.toList.map (·.shape)) =
      tag n0 (shapesOf P) := by
  have := range_zip_tag (shapesOf P) n0
  simpa [shapesOf] using this

/-- **What the sending's decision asks and writes.** -/
theorem decideSend_iff (P : Par) (owed : Option Nat) (d d' : DState L) (r₁ r₂ : Fmt.RoundView)
    (ids : Array Nat) :
    decideSend P owed d [r₁, r₂] = .ok (ids, d') ↔
      asks P owed d r₁ r₂ ∧ ids = (Array.range P.sent.size).map (· + d.st.oracles.size) ∧
        d' = behind P d (seedsOf P r₁) (answersIn r₂) := by
  have hlen : (seedsOf P r₁).length = P.seeds := cutSeeds_length _ _ _
  constructor
  · intro h
    unfold decideSend at h
    obtain ⟨_, h1, h⟩ := (bind_ok _ _ _).1 h
    obtain ⟨_, h2, h⟩ := (bind_ok _ _ _).1 h
    obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
    obtain ⟨_, h4, h⟩ := (bind_ok _ _ _).1 h
    obtain ⟨x, h5, h⟩ := (bind_ok _ _ _).1 h
    obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
    obtain ⟨_, _, h⟩ := (bind_ok _ _ _).1 h
    obtain ⟨e, h8, h⟩ := (bind_ok _ _ _).1 h
    have h1 := (need_ok _ _ _).1 h1
    have h2 := (need_ok _ _ _).1 h2
    have h4 := (need_ok _ _ _).1 h4
    have h5 := (named_ok _ _ _).1 h5
    have hp : (x.1, e) = (ids, d') := by simpa [pure, Except.pure] using h
    obtain ⟨hx, he⟩ := Prod.mk.inj hp
    subst he
    have hc : d.st.codes = P.codes := by simpa using h2
    obtain ⟨hok, lay, hlay, hids, hd₁⟩ := (recvP_iff _ d x.2 _ x.1).1 h5
    rw [hc] at hlay
    rw [hids, ids_zip, hd₁, ← Array.length_toList] at h8
    have key := (layRows_iff P.codes (seedsOf P r₁) (shapesOf P) d.st.oracles.toList (answersIn r₂)
      (recvD P.gp.firstTree d P.sent lay) e hc (recvD_toList _ d P lay)).1 h8
    rw [hlen] at key
    refine ⟨⟨by simpa using h1, hc, ?_, hok, key.1⟩, by rw [← hx, hids], ?_⟩
    · intro s hs
      have := (List.all_eq_true.1 h4) s hs
      simpa using this
    · rw [key.2]
      simp [behind, hlay]
  · rintro ⟨⟨rfl, hc, hz, hok, hf⟩, rfl, rfl⟩
    have hsome : (layTrees P.codes P.sent).isSome = true := by
      have := hok
      simp only [Ground.ok, Ground.recvL, Ground.sentL, List.cons_append, List.nil_append,
        List.all_cons, Bool.and_eq_true, Own.treesCan_eq] at this
      rw [← hc]
      exact this.2.1
    obtain ⟨lay, hlay⟩ := Option.isSome_iff_exists.1 hsome
    have h5 : Ground.recvP P.gp.firstTree d P.sent =
        some ((Array.range P.sent.size).map (· + d.st.oracles.size),
          recvD P.gp.firstTree d P.sent lay) :=
      (recvP_iff _ _ _ _ _).2 ⟨hok, lay, by rw [hc]; exact hlay, rfl, rfl⟩
    have hA := recvD_toList P.gp.firstTree d P lay
    unfold decideSend
    refine (bind_ok _ _ _).2 ⟨(), (need_ok _ _ _).2 rfl, ?_⟩
    refine (bind_ok _ _ _).2 ⟨(), (need_ok _ _ _).2 (by simpa using hc), ?_⟩
    refine (bind_ok _ _ _).2 ⟨(), (need_ok _ _ _).2 ((Own.treesCan_eq _ _).trans hsome), ?_⟩
    refine (bind_ok _ _ _).2 ⟨(), (need_ok _ _ _).2 (List.all_eq_true.2 fun s hs => by
      simpa using hz s hs), ?_⟩
    refine (bind_ok _ _ _).2 ⟨_, (named_ok _ _ _).2 h5, ?_⟩
    refine (bind_ok _ _ _).2 ⟨(), (need_ok _ _ _).2 ?_, ?_⟩
    · show Own.rising (((((Array.range P.sent.size).map (· + d.st.oracles.size)).toList.zip
        (P.sent.toList.map (·.shape))).filter fun y => y.2.answers != 0).map (·.1)) = true
      rw [ids_zip]
      exact (Own.rising_iff _).2 ((tag_pairwise _ _).sublist
        (List.Sublist.map _ List.filter_sublist))
    refine (bind_ok _ _ _).2 ⟨(), (need_ok _ _ _).2 ?_, ?_⟩
    · show (((((Array.range P.sent.size).map (· + d.st.oracles.size)).toList.zip
        (P.sent.toList.map (·.shape))).filter fun y => y.2.answers != 0).map (·.1)).all
          (fun o => (((recvD P.gp.firstTree d P.sent lay).st.oracles[o]?).map
            (!·.sampled)).getD false) = true
      rw [ids_zip, ← Array.length_toList]
      refine List.all_eq_true.2 fun o ho => ?_
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 ho
      rw [tag_get _ _ _ hA p (List.mem_filter.1 hp).1]
      rfl
    refine (bind_ok _ _ _).2 ⟨behind P d (seedsOf P r₁) (answersIn r₂), ?_, rfl⟩
    show layRows P.codes (seedsOf P r₁) (((Array.range P.sent.size).map
      (· + d.st.oracles.size)).toList.zip (P.sent.toList.map (·.shape))) (answersIn r₂)
      (recvD P.gp.firstTree d P.sent lay) = _
    rw [ids_zip, ← Array.length_toList]
    refine (layRows_iff P.codes (seedsOf P r₁) (shapesOf P) d.st.oracles.toList (answersIn r₂)
      (recvD P.gp.firstTree d P.sent lay) _ hc hA).2 ⟨by rw [hlen]; exact hf, ?_⟩
    simp [behind, hlay]

end VerifiableInference.Desc.K1
