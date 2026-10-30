-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/KeepsOrder.lean: the sending keeps the statement in order (every group in order,
every open row within its group's tables, every sample row on its own message).

Main names: layRows_keeps, decideSend_keeps.

What is not claimed. The sending's decision joins no group: the joining stands around it. Nothing on
soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.RowsOn
import Johnson.Desc.Means.Page

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice

variable {L : Type}

theorem layRows_keeps (codes : Codes) (seeds : List (List E × E)) :
    ∀ (shapes : List OracleShape) (pre : List OnBytes.Oracle) (ys : List E) (d d' : DState L),
      d.st.codes = codes → d.st.oracles.toList = pre ++ shapes.map fresh →
      (∀ s ∈ shapes, s.answers ≠ 0 →
        ((Msg.of codes s).K != 0 || (Msg.of codes s).Kzk != 0) = true ∧
          (Msg.of codes s).padFits = true ∧ ∀ sd ∈ seeds, (Msg.of codes s).v ≤ sd.1.length) →
      layRows codes seeds (tag pre.length shapes) ys d = .ok d' →
      Means.InOrder d.st → Means.InOrder d'.st
  | [], pre, ys, d, d', hc, hA, _, h, hI => by
    have := ((layRows_iff codes seeds [] pre ys d d' hc hA).1 h).2
    rw [this, put_self d _ (by simpa [outs] using hA)]
    exact hI
  | s :: l, pre, ys, d, d', hc, hA, hS, h, hI => by
    have hA' : d.st.oracles.toList = pre ++ fresh s :: l.map fresh := by simpa using hA
    have e : tag pre.length (s :: l) = (pre.length, s) :: tag (pre.length + 1) l := rfl
    rw [e] at h
    have hS' : ∀ t ∈ l, t.answers ≠ 0 →
        ((Msg.of codes t).K != 0 || (Msg.of codes t).Kzk != 0) = true ∧
          (Msg.of codes t).padFits = true ∧ ∀ sd ∈ seeds, (Msg.of codes t).v ≤ sd.1.length :=
      fun t ht => hS t (List.mem_cons_of_mem _ ht)
    by_cases h0 : s.answers = 0
    · have e1 : layRows codes seeds ((pre.length, s) :: tag (pre.length + 1) l) ys d =
          layRows codes seeds (tag (pre.length + 1) l) ys d := by
        rw [layRows]; simp [h0]
      rw [e1] at h
      have ih := layRows_keeps codes seeds l (pre ++ [fresh s]) ys d d' hc (by simp [hA']) hS'
      rw [List.length_append, List.length_singleton] at ih
      exact ih h hI
    · by_cases hs : s.answers ≤ seeds.length
      · by_cases hy : s.answers ≤ ys.length
        · have hx := get_mid _ _ _ _ hA'
          have hr := rowsOf_size codes seeds pre.length s ys hs hy
          have e1 : layRows codes seeds ((pre.length, s) :: tag (pre.length + 1) l) ys d =
              (named "K1: the statement does not admit the sample"
                (Ground.admitP d pre.length (rowsOf codes seeds pre.length s ys))).bind
                (layRows codes seeds (tag (pre.length + 1) l) (ys.drop s.answers)) := by
            rw [layRows]
            simp [h0, Nat.not_lt.2 hs, Nat.not_lt.2 hy, rowsOf]
          rw [e1] at h
          obtain ⟨d₁, h1, h2⟩ := (bind_ok _ _ _).1 h
          have h1 := (named_ok _ _ _).1 h1
          obtain ⟨c1, c2, c3⟩ := hS s List.mem_cons_self h0
          have hon := rowsOf_on d.st pre.length (fresh s) hx seeds ys
            (by rw [hc]; exact c1) (by rw [hc]; exact c2) (by rw [hc]; exact c3)
          rw [hc] at hon
          have hI₁ : Means.InOrder d₁.st := Means.admitP_keeps h1 hI hon
          obtain ⟨places, hp, rfl⟩ := (admitP_iff d d₁ _ s _ hx hr h0).1 h1
          rw [hc] at hp
          have ih := layRows_keeps codes seeds l (pre ++ [wr codes seeds pre.length s ys])
            (ys.drop s.answers) (admD d pre.length s places (rowsOf codes seeds pre.length s ys))
            d' hc (admD_toList codes seeds d pre l s ys places hc hA' h0 hp) hS'
          rw [List.length_append, List.length_singleton] at ih
          exact ih h2 hI₁
        · have e1 : layRows codes seeds ((pre.length, s) :: tag (pre.length + 1) l) ys d =
              .error "K1: an answer lacks for a row" := by
            rw [layRows]; simp [h0, Nat.not_lt.2 hs, Nat.lt_of_not_le hy]
          rw [e1] at h
          cases h
      · have e1 : layRows codes seeds ((pre.length, s) :: tag (pre.length + 1) l) ys d =
            .error "K1: a seed lacks for an answer" := by
          rw [layRows]; simp [h0, Nat.lt_of_not_le hs]
        rw [e1] at h
        cases h

/-- **The sending keeps the statement in order.** -/
theorem decideSend_keeps (P : Par) (owed : Option Nat) (d d' : DState L) (r₁ r₂ : Fmt.RoundView)
    (ids : Array Nat) (hB : planOkOwn P = true) (hfit : roundsFit (rounds P) [r₁, r₂] = true)
    (hyes : decideSend P owed d [r₁, r₂] = .ok (ids, d')) (hI : Means.InOrder d.st) :
    Means.InOrder d'.st := by
  obtain ⟨⟨_, hc, _, hok, hf⟩, _, hd'⟩ := (decideSend_iff P owed d d' r₁ r₂ ids).1 hyes
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
  have hI₁ : Means.InOrder (recvD P.gp.firstTree d P.sent lay).st := Means.recvP_keeps h5 hI
  have hA := recvD_toList P.gp.firstTree d P lay
  have hlen : (seedsOf P r₁).length = P.seeds := cutSeeds_length _ _ _
  have hlay' : layRows P.codes (seedsOf P r₁) (tag d.st.oracles.toList.length (shapesOf P))
      (answersIn r₂) (recvD P.gp.firstTree d P.sent lay) = .ok d' :=
    (layRows_iff P.codes (seedsOf P r₁) (shapesOf P) d.st.oracles.toList (answersIn r₂)
      (recvD P.gp.firstTree d P.sent lay) d' hc hA).2 ⟨by rw [hlen]; exact hf, by
        rw [hd']
        simp [behind, hlay]⟩
  have hdraw : (r₁.drawn.elems.map E.ofTriple).length = P.seeds * (P.coordinates + 1) :=
    draw_len P r₁ r₂ hfit
  refine layRows_keeps P.codes (seedsOf P r₁) (shapesOf P) d.st.oracles.toList (answersIn r₂)
    (recvD P.gp.firstTree d P.sent lay) d' hc hA (fun s hs h0 => ?_) hlay' hI₁
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hs
  obtain ⟨c1, c2⟩ := plan_msg P hB ⟨k, hk⟩ h0
  refine ⟨c1, c2, fun sd hsd => ?_⟩
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hsd
  rw [cutSeeds_get _ _ _ i sd hdraw hi]
  exact msgAt_v_le P ⟨k, hk⟩ h0

end VerifiableInference.Desc.K1
