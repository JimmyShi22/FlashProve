-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Quiet.lean: KIND K1's SENDING KEEPS EVERY RELATION R ON STATEMENTS that the ground's
eight plain functions keep which ask nothing of their caller (Johnson/Desc/GroundQuiet.lean) AND
THAT THE ADMITTING OF A SAMPLE KEEPS WHERE THE ROWS HANDED IN ARE ON THE MESSAGE: at a place that
passes the tests on the plan, and at rounds that fit. For the rows that the sending lays are on
their own message (Johnson/Desc/K1/Law/RowsOn.lean: rowsOf_on). So the sending is a calm step
(Johnson/Desc/Trail.lean). Theorems.

  AdmitOn R            the admitting keeps R where the rows are on the message.
  layRows_rel · decideSend_rel   the sending's decision keeps R. THE PROOFS FOLLOW, LINE BY LINE,
                       those of Johnson/Desc/K1/Law/KeepsOrder.lean (layRows_keeps,
                       decideSend_keeps), which show the same of one property, "the statement is in
                       order".
  fit_two · sendOwn_rel   the block of a sending by itself: a yes of its decision, at rounds that
                       fit and without the sealed digest, keeps R.
  admitOn_quiet · admitOn_calm   the admitting's condition is met at R := "a quiet step" and at
                       R := "a calm step".
What is not claimed. The sending's decision joins no group. Nothing on soundness as such, on an
honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.KeepsOrder
import Johnson.Desc.BlockKeeps
import Johnson.Desc.Trail

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice
open VerifiableInference.Desc.Ground (GroundQuiet)

/-- The admitting of a sample keeps R where the rows handed in are on the message. -/
def AdmitOn (R : Statement → Statement → Prop) : Prop :=
  ∀ {L : Type} (d d' : DState L) (o : Nat) (rows : Array OnBytes.Row),
    Ground.admitP d o rows = some d' → (∀ r ∈ rows.toList, Means.RowOn d.st o r) → R d.st d'.st

variable {L : Type} {R : Statement → Statement → Prop}

/-- The laying of the sample rows keeps R. -/
theorem layRows_rel (H : GroundQuiet R) (hA : AdmitOn R) (codes : Codes)
    (seeds : List (List E × E)) :
    ∀ (shapes : List OracleShape) (pre : List OnBytes.Oracle) (ys : List E) (d d' : DState L),
      d.st.codes = codes → d.st.oracles.toList = pre ++ shapes.map fresh →
      (∀ s ∈ shapes, s.answers ≠ 0 →
        ((Msg.of codes s).K != 0 || (Msg.of codes s).Kzk != 0) = true ∧
          (Msg.of codes s).padFits = true ∧ ∀ sd ∈ seeds, (Msg.of codes s).v ≤ sd.1.length) →
      layRows codes seeds (tag pre.length shapes) ys d = .ok d' → R d.st d'.st
  | [], pre, ys, d, d', hc, hA', _, h => by
    have := ((layRows_iff codes seeds [] pre ys d d' hc hA').1 h).2
    rw [this, put_self d _ (by simpa [outs] using hA')]
    exact H.refl _
  | s :: l, pre, ys, d, d', hc, hA0, hS, h => by
    have hA' : d.st.oracles.toList = pre ++ fresh s :: l.map fresh := by simpa using hA0
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
      have ih := layRows_rel H hA codes seeds l (pre ++ [fresh s]) ys d d' hc (by simp [hA']) hS'
      rw [List.length_append, List.length_singleton] at ih
      exact ih h
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
          have hR₁ : R d.st d₁.st := hA d d₁ _ _ h1 hon
          obtain ⟨places, hp, rfl⟩ := (admitP_iff d d₁ _ s _ hx hr h0).1 h1
          rw [hc] at hp
          have ih := layRows_rel H hA codes seeds l (pre ++ [wr codes seeds pre.length s ys])
            (ys.drop s.answers) (admD d pre.length s places (rowsOf codes seeds pre.length s ys))
            d' hc (admD_toList codes seeds d pre l s ys places hc hA' h0 hp) hS'
          rw [List.length_append, List.length_singleton] at ih
          exact H.trans hR₁ (ih h2)
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

/-- **The sending's decision keeps R.** -/
theorem decideSend_rel (H : GroundQuiet R) (hA : AdmitOn R) (P : Par) (owed : Option Nat)
    (d d' : DState L) (r₁ r₂ : Fmt.RoundView) (ids : Array Nat) (hB : planOkOwn P = true)
    (hfit : roundsFit (rounds P) [r₁, r₂] = true)
    (hyes : decideSend P owed d [r₁, r₂] = .ok (ids, d')) : R d.st d'.st := by
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
  have hR₁ : R d.st (recvD P.gp.firstTree d P.sent lay).st := H.recv _ _ _ _ _ h5
  have hA0 := recvD_toList P.gp.firstTree d P lay
  have hlen : (seedsOf P r₁).length = P.seeds := cutSeeds_length _ _ _
  have hlay' : layRows P.codes (seedsOf P r₁) (tag d.st.oracles.toList.length (shapesOf P))
      (answersIn r₂) (recvD P.gp.firstTree d P.sent lay) = .ok d' :=
    (layRows_iff P.codes (seedsOf P r₁) (shapesOf P) d.st.oracles.toList (answersIn r₂)
      (recvD P.gp.firstTree d P.sent lay) d' hc hA0).2 ⟨by rw [hlen]; exact hf, by
        rw [hd']
        simp [behind, hlay]⟩
  have hdraw : (r₁.drawn.elems.map E.ofTriple).length = P.seeds * (P.coordinates + 1) :=
    draw_len P r₁ r₂ hfit
  refine H.trans hR₁ (layRows_rel H hA P.codes (seedsOf P r₁) (shapesOf P) d.st.oracles.toList
    (answersIn r₂) (recvD P.gp.firstTree d P.sent lay) d' hc hA0 (fun s hs h0 => ?_) hlay')
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hs
  obtain ⟨c1, c2⟩ := plan_msg P hB ⟨k, hk⟩ h0
  refine ⟨c1, c2, fun sd hsd => ?_⟩
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hsd
  rw [cutSeeds_get _ _ _ i sd hdraw hi]
  exact msgAt_v_le P ⟨k, hk⟩ h0

/-- Two declared rounds fit two rounds alone. -/
theorem fit_two (a b : Fmt.DeclaredRound) (rs : List Fmt.RoundView) (h : roundsFit [a, b] rs = true) :
    ∃ r₁ r₂, rs = [r₁, r₂] := by
  match rs, h with
  | [r₁, r₂], _ => exact ⟨r₁, r₂, rfl⟩
  | [], h => simp [roundsFit] at h
  | [_], h => simp [roundsFit] at h
  | _ :: _ :: _ :: _, h => simp [roundsFit] at h

variable {Cl : Type}

/-- **What a yes of the sending's decision gives at rounds that fit and a plan that passes.** -/
theorem sendOwn_rel (H : GroundQuiet R) (hA : AdmitOn R) (P : Par) (hB : planOkOwn P = true)
    (s s' : Owing (DState (Array Nat))) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hfit : roundsFit (rounds P) rs = true)
    (h : (sendOwn (Cl := Cl) P).decide s (rs.map noDigest) gs = .ok s') :
    R s.held.st s'.held.st := by
  obtain ⟨r₁, r₂, rfl⟩ := fit_two _ _ rs hfit
  have h' : (decideSend P s.owed s.held [noDigest r₁, noDigest r₂]).map
      (fun x => ({ owed := none, held := { x.2 with loc := x.1 } } :
        Owing (DState (Array Nat)))) = .ok s' := h
  obtain ⟨x, h1, h2⟩ := Keeps.emap_ok h'
  subst h2
  exact decideSend_rel H hA P s.owed s.held x.2 (noDigest r₁) (noDigest r₂) x.1 hB hfit h1

/-- The admitting is a quiet step where the rows are on the message. -/
theorem admitOn_quiet {K : Type} [CommRing K] (ρ : OnBytes.Model.Reading K) :
    AdmitOn (Means.Quiet ρ) :=
  fun _ _ _ _ h hr => Means.quiet_admitP ρ h hr

/-- The admitting is a calm step where the rows are on the message. -/
theorem admitOn_calm {K : Type} [CommRing K] (ρ : OnBytes.Model.Reading K) :
    AdmitOn (Means.Calm ρ) :=
  fun d d' o rows h hr => ⟨Means.quiet_admitP ρ h hr, Ground.groundKeeps_grows.admit d d' o rows h⟩

end VerifiableInference.Desc.K1
