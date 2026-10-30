-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K5Shape.lean: kind K5, an attention segment's own rounds: small lemmas on its
own text (Att/K5AttentionKind.lean). Core Lean alone; no arithmetic of the field occurs.

Main names:
  `bind_some`, `pure_some`, `mapM_ran`: how a text typed in the kind's monad is taken apart where
    it returns.
  `take_spec`, `sum_spec`, `close_spec`, `batch_spec`: the four verbs, each where it returns.
  `hear_ran`: hear x, where it returns, taken apart into its verbs with the states between.
  `hear_walk`: where hear x returns, it has walked script x: the two texts, which are typed side by
    side, agree.
  `walk_fits`, `hear_rounds`: what a walk uses up is the stages' entries, entry for entry; so where
    hear returns, the rounds used up are `rounds p`, and no scalar waits behind.
  `left_over_nil`, `never_left_over`: with as many rounds as `rounds p` has, nothing is left over;
    inside Block.step the refusal "K5.left-over" never comes.
  `planOk_shape`: planOk gives, at each sumcheck of the script, the part's test on the plan.
  `decide_lays`: decide's yes is: nothing owed, a ledger, the hearing's return with all rounds used
    up, and the seat's lay of just that.

Limits: one direction, from a return.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K5AttentionKind
import Johnson.Desc.Part.MaskedSumShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes
open OnBytes.Model (Aff Fork)
open VerifiableInference.Desc (Block named need)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Var Ends Fit Fits)

/-- The monad's state. -/
abbrev St := Fork × List Fmt.RoundView × Nat

/-! ## The monad, where a text returns -/

theorem bind_some {α β : Type} (m : M α) (f : α → M β) (s s' : St) (b : β) :
    (m >>= f) s = some (b, s') ↔ ∃ a s1, m s = some (a, s1) ∧ f a s1 = some (b, s') := by
  show (StateT.bind m f) s = _ ↔ _
  unfold StateT.bind
  cases h : m s with
  | none => simp
  | some x =>
    obtain ⟨a, s1⟩ := x
    constructor
    · intro h'
      exact ⟨a, s1, rfl, h'⟩
    · rintro ⟨a', s1', e, h'⟩
      simp only [Option.some.injEq, Prod.mk.injEq] at e
      obtain ⟨e1, e2⟩ := e
      subst e1 e2
      exact h'

theorem pure_some {α : Type} (a b : α) (s s' : St) : (pure a : M α) s = some (b, s') ↔ a = b ∧ s = s' := by
  show (some (a, s) : Option (α × St)) = _ ↔ _
  simp

/-- A list of steps has run, one after the other. -/
def Ran {α β : Type} (f : α → M β) : List α → List β → St → St → Prop
  | [], [], s, s' => s' = s
  | a :: l, b :: bs, s, s' => ∃ s1, f a s = some (b, s1) ∧ Ran f l bs s1 s'
  | _, _, _, _ => False

theorem listMapM_ran {α β : Type} (f : α → M β) : ∀ (l : List α) (bs : List β) (s s' : St),
    l.mapM f s = some (bs, s') → Ran f l bs s s'
  | [], bs, s, s', h => by
    rw [List.mapM_nil] at h
    obtain ⟨e1, e2⟩ := (pure_some _ _ _ _).1 h
    subst e1 e2
    rfl
  | a :: l, bs, s, s', h => by
    rw [List.mapM_cons] at h
    obtain ⟨b, s1, h1, h2⟩ := (bind_some _ _ _ _ _).1 h
    obtain ⟨bs', s2, h3, h4⟩ := (bind_some _ _ _ _ _).1 h2
    obtain ⟨e1, e2⟩ := (pure_some _ _ _ _).1 h4
    subst e1 e2
    exact ⟨s1, h1, listMapM_ran f l bs' s1 s2 h3⟩

theorem mapM_ran {α β : Type} (f : α → M β) (a : Array α) (bs : Array β) (s s' : St)
    (h : a.mapM f s = some (bs, s')) : Ran f a.toList bs.toList s s' := by
  rw [Array.mapM_eq_mapM_toList] at h
  have h' : (a.toList.mapM f >>= fun l => pure l.toArray) s = some (bs, s') := by
    rw [← h, map_eq_pure_bind]
  obtain ⟨l, s1, h1, h2⟩ := (bind_some _ _ _ _ _).1 h'
  obtain ⟨e1, e2⟩ := (pure_some _ _ _ _).1 h2
  subst e1 e2
  exact listMapM_ran f _ _ _ _ h1

/-! ## The four verbs -/

theorem take_spec {n j lead lead' : Nat} {F G : Fork} {rs rs' : List Fmt.RoundView}
    (h : take n (F, rs, lead) = some (j, G, rs', lead')) :
    j = F.next ∧ rs' = rs ∧ lead' = lead + n ∧ ∃ r rest v, rs = r :: rest ∧
      MaskedSum.scalars ((r.vals.drop lead).take n) = some v ∧ v.length = n ∧
      ({ F with next := F.next + n } : Fork).hideRun F.next v.toArray oneE = some G := by
  unfold take at h
  cases rs with
  | nil => cases h
  | cons r rest =>
    simp only [Option.bind_eq_bind] at h
    obtain ⟨v, h1, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨_, h2, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨G', h3, h⟩ := Option.bind_eq_some_iff.1 h
    simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨e1, e2, e3, e4⟩ := h
    subst e2
    have hl : v.length = n := by
      by_cases hc : v.length = n
      · exact hc
      · simp [guard, hc, failure] at h2
    exact ⟨e1.symm, e3.symm, e4.symm, r, rest, v, rfl, h1, hl, h3⟩

theorem sum_spec {C : Aff} {vs : List Var} {e : Ends} {hh : MaskedSum.Heard} {lead lead' : Nat} {F G : Fork}
    {rs rs' : List Fmt.RoundView} (h : sum C (.sum vs e) (F, rs, lead) = some (hh, G, rs', lead')) :
    rs' = rs.drop (vs.length + 3) ∧ lead' = 0 ∧ ∃ (G1 : Fork) (f : Aff),
      MaskedSum.hear C ⟨lead, vs, some e⟩ F (rs.take (vs.length + 3)) = some (hh, G1) ∧
      MaskedSum.row hh zeroE {} G1 = some (f, G) := by
  unfold sum at h
  simp only [Option.bind_eq_bind] at h
  obtain ⟨⟨h1, G1⟩, a1, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨⟨f, G2⟩, a2, h⟩ := Option.bind_eq_some_iff.1 h
  simp only [Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨e1, e2, e3, e4⟩ := h
  subst e1 e2
  exact ⟨e3.symm, e4.symm, G1, f, a1, a2⟩

theorem close_spec {n lead lead' : Nat} {F G : Fork} {rs rs' : List Fmt.RoundView} {d : List E}
    (h : close n (F, rs, lead) = some (d, G, rs', lead')) :
    G = F ∧ lead' = 0 ∧ ∃ r, rs = r :: rs' ∧ r.vals.length = lead ∧ r.drawn.elems.length = n ∧
      d = r.drawn.elems.map E.ofTriple := by
  unfold close at h
  cases rs with
  | nil => cases h
  | cons r rest =>
    simp only at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨e1, e2, e3, e4⟩ := h
      subst e3
      exact ⟨e2.symm, e4.symm, r, rfl, hc.1, hc.2, e1.symm⟩
    · cases h

theorem batch_spec {rows lead lead' : Nat} {F G : Fork} {rs rs' : List Fmt.RoundView} {w : Array E}
    (h : batch rows (F, rs, lead) = some (w, G, rs', lead')) :
    G = F ∧ lead' = 0 ∧ ∃ r x, rs = r :: rs' ∧ r.vals.length = lead ∧ r.drawn.elems.map E.ofTriple = [x] ∧
      w = (MaskedSum.powersFrom x rows oneE).toArray := by
  unfold batch at h
  obtain ⟨d, ⟨F1, rs1, l1⟩, h1, h2⟩ := (bind_some _ _ _ _ _).1 h
  obtain ⟨a1, a2, r, a3, a4, a5, a6⟩ := close_spec h1
  match d, h2 with
  | [x], h2 =>
    obtain ⟨e1, e2⟩ := (pure_some _ _ _ _).1 h2
    simp only [Prod.mk.injEq] at e2
    obtain ⟨b1, b2, b3⟩ := e2
    subst b1 b2 b3 a1
    exact ⟨rfl, a2, r, x, a3, a4, a6.symm, e1.symm⟩
  | [], h2 => cases h2
  | _ :: _ :: _, h2 => cases h2

/-! ## The hearing, taken apart -/

/-- The stage of the key at the index. -/
def keyStage (x : Params.AttentionRounds) : Stage :=
  .sum ((List.replicate x.lt 3 ++ List.replicate x.lgk (x.lt + 3) ++ List.replicate x.lt (x.lt + 2)).map .plain)
    ⟨x.lt + 1, x.Lam + x.pairs * x.lt⟩

/-- A softmax-table unit has run. -/
def UnitRan (u : Nat × Nat) (o : Nat × MaskedSum.Heard) (s s' : St) : Prop :=
  ∃ s1, take 7 s = some (o.1, s1) ∧ sum (.slot (o.1 + 6)) (products u.1 u.2) s1 = some (o.2, s')

/-- The units have run, one after the other. -/
def UnitsRan : List (Nat × Nat) → List (Nat × MaskedSum.Heard) → St → St → Prop
  | [], [], s, s' => s' = s
  | u :: us, o :: os, s, s' => ∃ s1, UnitRan u o s s1 ∧ UnitsRan us os s1 s'
  | _, _, _, _ => False

/-- The remainder units' scalars have been taken. -/
def TakesRan (n : Nat) : Nat → List Nat → St → St → Prop
  | 0, [], s, s' => s' = s
  | k + 1, j :: js, s, s' => ∃ s1, take n s = some (j, s1) ∧ TakesRan n k js s1 s'
  | _, _, _, _ => False

theorem takes_of_ran (n : Nat) : ∀ (l : List Nat) (js : List Nat) (s s' : St),
    Ran (fun _ : Nat => take n) l js s s' → TakesRan n l.length js s s'
  | [], [], _, _, h => h
  | _ :: l, _ :: js, _, _, ⟨s1, h1, h2⟩ => ⟨s1, h1, takes_of_ran n l js _ _ h2⟩
  | [], _ :: _, _, _, h => h.elim
  | _ :: _, [], _, _, h => h.elim

theorem units_of_ran : ∀ (l : List (Nat × Nat)) (os : List (Nat × MaskedSum.Heard)) (s s' : St),
    Ran (fun u : Nat × Nat => (do
      let seven ← take 7
      pure (seven, ← sum (.slot (seven + 6)) (products u.1 u.2)) : M (Nat × MaskedSum.Heard))) l os s s' →
    UnitsRan l os s s'
  | [], [], _, _, h => h
  | u :: l, o :: os, s, s', ⟨s1, h1, h2⟩ => by
    obtain ⟨seven, sa, a1, a2⟩ := (bind_some _ _ _ _ _).1 h1
    obtain ⟨hh, sb, b1, b2⟩ := (bind_some _ _ _ _ _).1 a2
    obtain ⟨e1, e2⟩ := (pure_some _ _ _ _).1 b2
    subst e1 e2
    exact ⟨sb, ⟨sa, a1, b1⟩, units_of_ran l os _ _ h2⟩
  | [], _ :: _, _, _, h => h.elim
  | _ :: _, [], _, _, h => h.elim

/-- **The hearing has run**: verb by verb, with the states between. -/
structure HearRan (x : Params.AttentionRounds) (s0 : St) (h : Heard) (s' : St) : Prop where
  ran : ∃ sa sb s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 : St, ∃ pt : List E,
    TakesRan 3 x.planeMessages h.remainders.toList s0 sa ∧
    UnitsRan x.score h.scores.toList sa sb ∧
    take 5 sb = some (h.five, s1) ∧
    take x.lt s1 = some (h.bits, s2) ∧
    take 2 s2 = some (h.two, s3) ∧
    sum (.slot (h.five + 1)) (products x.e x.pairs) s3 = some (h.division, s4) ∧
    batch 2 s4 = some (h.gam, s5) ∧
    take 2 s5 = some (h.values, s6) ∧
    sum (.slot h.values) (products x.valueM x.pairs) s6 = some (h.below, s7) ∧
    sum (.slot (h.values + 1)) (products x.valueD x.pairs) s7 = some (h.on, s8) ∧
    close (2 * x.lgk + 2 * x.lt + 4) s8 = some (pt, s9) ∧ h.point = pt.toArray ∧
    take x.pairs s9 = some (h.maxima, s10) ∧
    batch x.pairs s10 = some (h.om, s11) ∧
    sum (batched x.pairs h.om h.maxima 1 0) (products x.attained x.pairs) s11 = some (h.atIndex, s12) ∧
    batch x.pairs s12 = some (h.om', s13) ∧
    sum (batched x.pairs h.om' h.atIndex.sEnd 2 1) (keyStage x) s13 = some (h.key, s14) ∧
    batch x.pairs s14 = some (h.om'', s15) ∧
    sum (.ofConst zeroE) (products x.bits x.pairs) s15 = some (h.cells, s')

theorem hear_ran {x : Params.AttentionRounds} {s0 s' : St} {h : Heard} (hh : hear x s0 = some (h, s')) :
    HearRan x s0 h s' := by
  unfold hear at hh
  simp only at hh
  obtain ⟨rem, sa, ha, hh⟩ := (bind_some _ _ _ _ _).1 hh
  obtain ⟨sco, sb, hb, hh⟩ := (bind_some _ _ _ _ _).1 hh
  obtain ⟨five, s1, h1, hh⟩ := (bind_some _ _ _ _ _).1 hh
  obtain ⟨bits, s2, h2, hh⟩ := (bind_some _ _ _ _ _).1 hh
  obtain ⟨two, s3, h3, hh⟩ := (bind_some _ _ _ _ _).1 hh
  obtain ⟨division, s4, h4, hh⟩ := (bind_some _ _ _ _ _).1 hh
  obtain ⟨gam, s5, h5, hh⟩ := (bind_some _ _ _ _ _).1 hh
  obtain ⟨values, s6, h6, hh⟩ := (bind_some _ _ _ _ _).1 hh
  obtain ⟨below, s7, h7, hh⟩ := (bind_some _ _ _ _ _).1 hh
  obtain ⟨on, s8, h8, hh⟩ := (bind_some _ _ _ _ _).1 hh
  obtain ⟨pt, s9, h9, hh⟩ := (bind_some _ _ _ _ _).1 hh
  obtain ⟨maxima, s10, h10, hh⟩ := (bind_some _ _ _ _ _).1 hh
  obtain ⟨om, s11, h11, hh⟩ := (bind_some _ _ _ _ _).1 hh
  obtain ⟨atIndex, s12, h12, hh⟩ := (bind_some _ _ _ _ _).1 hh
  obtain ⟨om', s13, h13, hh⟩ := (bind_some _ _ _ _ _).1 hh
  obtain ⟨key, s14, h14, hh⟩ := (bind_some _ _ _ _ _).1 hh
  obtain ⟨om'', s15, h15, hh⟩ := (bind_some _ _ _ _ _).1 hh
  obtain ⟨cells, s16, h16, hh⟩ := (bind_some _ _ _ _ _).1 hh
  obtain ⟨e1, e2⟩ := (pure_some _ _ _ _).1 hh
  subst e1 e2
  have ra := takes_of_ran 3 _ _ _ _ (mapM_ran _ _ _ _ _ ha)
  rw [Array.toList_range, List.length_range] at ra
  exact ⟨sa, sb, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, pt, ra,
    units_of_ran _ _ _ _ (mapM_ran _ _ _ _ _ hb), h1, h2, h3, h4, h5, h6, h7, h8, h9, rfl, h10, h11, h12, h13, h14,
    h15, h16⟩

/-! ## The walk -/

/-- Where the hearing stands: the rounds left, and the lead. -/
abbrev Pos := List Fmt.RoundView × Nat
def pos (s : St) : Pos := (s.2.1, s.2.2)

/-- The stages are walked. -/
def Walk : List Stage → Pos → Pos → Prop
  | [], a, b => b = a
  | .scalars n :: l, a, b =>
    (∃ r rest v, a.1 = r :: rest ∧ MaskedSum.scalars ((r.vals.drop a.2).take n) = some v ∧ v.length = n) ∧
      Walk l (a.1, a.2 + n) b
  | .sum vs e :: l, a, b =>
    ∃ used rest, a.1 = used ++ rest ∧ Fits (MaskedSum.entries ⟨a.2, vs, some e⟩) used ∧ Walk l (rest, 0) b
  | .batch _ :: l, a, b =>
    ∃ r rest, a.1 = r :: rest ∧ r.vals.length = a.2 ∧ r.drawn.elems.length = 1 ∧ Walk l (rest, 0) b
  | .point n :: l, a, b =>
    ∃ r rest, a.1 = r :: rest ∧ r.vals.length = a.2 ∧ r.drawn.elems.length = n ∧ Walk l (rest, 0) b

theorem Walk.append : ∀ {l l' : List Stage} {a m b : Pos}, Walk l a m → Walk l' m b → Walk (l ++ l') a b
  | [], _, _, _, _, h, h' => by
    rw [show _ = _ from h] at h'
    exact h'
  | .scalars _ :: _, _, _, _, _, h, h' => ⟨h.1, Walk.append h.2 h'⟩
  | .sum _ _ :: _, _, _, _, _, ⟨u, r, h1, h2, h3⟩, h' => ⟨u, r, h1, h2, Walk.append h3 h'⟩
  | .batch _ :: _, _, _, _, _, ⟨u, r, h1, h2, h3, h4⟩, h' => ⟨u, r, h1, h2, h3, Walk.append h4 h'⟩
  | .point _ :: _, _, _, _, _, ⟨u, r, h1, h2, h3, h4⟩, h' => ⟨u, r, h1, h2, h3, Walk.append h4 h'⟩

theorem Walk.cons {st : Stage} {l : List Stage} {a m b : Pos} (h : Walk [st] a m) (h' : Walk l m b) :
    Walk (st :: l) a b := Walk.append (l := [st]) h h'

theorem take_walk {n j : Nat} {s s' : St} (h : take n s = some (j, s')) : Walk [.scalars n] (pos s) (pos s') := by
  obtain ⟨F, rs, lead⟩ := s
  obtain ⟨G, rs', lead'⟩ := s'
  obtain ⟨_, e2, e3, r, rest, v, a1, a2, a3, _⟩ := take_spec h
  subst e2 e3
  exact ⟨⟨r, rest, v, a1, a2, a3⟩, rfl⟩

theorem sum_walk {C : Aff} {vs : List Var} {e : Ends} {hh : MaskedSum.Heard} {s s' : St}
    (h : sum C (.sum vs e) s = some (hh, s')) : Walk [.sum vs e] (pos s) (pos s') := by
  obtain ⟨F, rs, lead⟩ := s
  obtain ⟨G, rs', lead'⟩ := s'
  obtain ⟨e1, e2, G1, f, a1, _⟩ := sum_spec h
  obtain ⟨_, T, R, _, b2, _, _⟩ := MaskedSum.hear_spec a1
  subst e1 e2
  exact ⟨rs.take (vs.length + 3), rs.drop (vs.length + 3), (List.take_append_drop _ _).symm,
    MaskedSum.readAll_fits b2, rfl⟩

theorem close_walk {n : Nat} {d : List E} {s s' : St} (h : close n s = some (d, s')) :
    Walk [.point n] (pos s) (pos s') := by
  obtain ⟨F, rs, lead⟩ := s
  obtain ⟨G, rs', lead'⟩ := s'
  obtain ⟨_, e2, r, a1, a2, a3, _⟩ := close_spec h
  subst e2
  exact ⟨r, rs', a1, a2, a3, rfl⟩

theorem batch_walk {rows : Nat} {w : Array E} {s s' : St} (h : batch rows s = some (w, s')) :
    Walk [.batch rows] (pos s) (pos s') := by
  obtain ⟨F, rs, lead⟩ := s
  obtain ⟨G, rs', lead'⟩ := s'
  obtain ⟨_, e2, r, x, a1, a2, a3, _⟩ := batch_spec h
  subst e2
  have : r.drawn.elems.length = 1 := by
    have := congrArg List.length a3
    simpa using this
  exact ⟨r, rs', a1, a2, this, rfl⟩

theorem takes_walk (n : Nat) : ∀ (k : Nat) (js : List Nat) (s s' : St), TakesRan n k js s s' →
    Walk (List.replicate k (.scalars n)) (pos s) (pos s')
  | 0, [], _, _, h => by rw [show _ = _ from h]; rfl
  | k + 1, _ :: js, _, _, ⟨_, h1, h2⟩ => Walk.cons (take_walk h1) (takes_walk n k js _ _ h2)
  | 0, _ :: _, _, _, h => h.elim
  | _ + 1, [], _, _, h => h.elim

theorem units_walk : ∀ (us : List (Nat × Nat)) (os : List (Nat × MaskedSum.Heard)) (s s' : St),
    UnitsRan us os s s' → Walk (us.flatMap fun u => [.scalars 7, products u.1 u.2]) (pos s) (pos s')
  | [], [], _, _, h => by rw [show _ = _ from h]; rfl
  | u :: us, _ :: os, _, _, ⟨_, ⟨_, h1, h2⟩, h3⟩ => by
    rw [List.flatMap_cons]
    exact Walk.append (Walk.cons (take_walk h1) (sum_walk h2)) (units_walk us os _ _ h3)
  | [], _ :: _, _, _, h => h.elim
  | _ :: _, [], _, _, h => h.elim

/-- **Where the hearing returns, it has walked the script.** -/
theorem hear_walk {x : Params.AttentionRounds} {s0 s' : St} {h : Heard} (hh : hear x s0 = some (h, s')) :
    Walk (script x) (pos s0) (pos s') := by
  obtain ⟨sa, sb, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, pt, ha, hb, h1, h2, h3, h4, h5,
    h6, h7, h8, h9, _, h10, h11, h12, h13, h14, h15, h16⟩ := (hear_ran hh).ran
  exact Walk.append (Walk.append (takes_walk 3 _ _ _ _ ha) (units_walk _ _ _ _ hb))
    (Walk.cons (take_walk h1) <| Walk.cons (take_walk h2) <| Walk.cons (take_walk h3) <| Walk.cons (sum_walk h4) <|
     Walk.cons (batch_walk h5) <| Walk.cons (take_walk h6) <| Walk.cons (sum_walk h7) <| Walk.cons (sum_walk h8) <|
     Walk.cons (close_walk h9) <| Walk.cons (take_walk h10) <| Walk.cons (batch_walk h11) <|
     Walk.cons (sum_walk h12) <| Walk.cons (batch_walk h13) <| Walk.cons (sum_walk h14) <|
     Walk.cons (batch_walk h15) (sum_walk h16))

/-! ## What a walk uses up -/

theorem scalars_append : ∀ {a b : List Fmt.ItemValue} {x y : List E}, MaskedSum.scalars a = some x →
    MaskedSum.scalars b = some y → MaskedSum.scalars (a ++ b) = some (x ++ y)
  | [], _, _, _, h, h' => by
    simp only [MaskedSum.scalars, Option.some.injEq] at h
    subst h
    exact h'
  | .e u :: a, b, x, y, h, h' => by
    simp only [MaskedSum.scalars, Option.map_eq_some_iff] at h
    obtain ⟨x', h1, h2⟩ := h
    subst h2
    show (MaskedSum.scalars (a ++ b)).map _ = _
    rw [scalars_append h1 h']
    rfl
  | .f _ :: _, _, _, _, h, _ => by cases h
  | .word _ :: _, _, _, _, h, _ => by cases h
  | .root _ :: _, _, _, _, h, _ => by cases h
  | .answer _ :: _, _, _, _, h, _ => by cases h

/-- The first lead items of the first round left are scalars. -/
def LeadOk : List Fmt.RoundView → Nat → Prop
  | [], lead => lead = 0
  | r :: _, lead => ∃ s, MaskedSum.scalars (r.vals.take lead) = some s ∧ s.length = lead

theorem leadOk_zero : ∀ rs : List Fmt.RoundView, LeadOk rs 0
  | [] => rfl
  | _ :: _ => ⟨[], by simp [MaskedSum.scalars], rfl⟩

theorem LeadOk.whole {r : Fmt.RoundView} {rest : List Fmt.RoundView} {lead : Nat} (h : LeadOk (r :: rest) lead)
    (hl : r.vals.length = lead) : ∃ s, MaskedSum.scalars r.vals = some s ∧ s.length = lead := by
  obtain ⟨s, h1, h2⟩ := h
  rw [← hl, List.take_length] at h1
  exact ⟨s, h1, h2⟩

/-- **What a walk uses up is the stages' entries, entry for entry.** -/
theorem walk_fits : ∀ (st : List Stage) (rs : List Fmt.RoundView) (lead : Nat) (b : Pos), LeadOk rs lead →
    Walk st (rs, lead) b → ∃ used, rs = used ++ b.1 ∧ Fits (entriesOf lead st) used
  | [], rs, lead, b, _, h => by
    rw [show b = _ from h]
    exact ⟨[], rfl, trivial⟩
  | .scalars n :: l, rs, lead, b, hl, ⟨⟨r, rest, v, a1, a2, a3⟩, h⟩ => by
    refine walk_fits l rs (lead + n) b ?_ h
    simp only at a1
    subst a1
    obtain ⟨s, b1, b2⟩ := hl
    exact ⟨s ++ v, by rw [List.take_add]; exact scalars_append b1 a2, by rw [List.length_append, b2, a3]⟩
  | .sum vs e :: l, rs, lead, b, _, ⟨used, rest, a1, a2, h⟩ => by
    obtain ⟨u', c1, c2⟩ := walk_fits l rest 0 b (leadOk_zero _) h
    simp only at a1
    exact ⟨used ++ u', by rw [a1, c1, List.append_assoc], a2.append c2⟩
  | .batch rows :: l, rs, lead, b, hl, ⟨r, rest, a1, a2, a3, h⟩ => by
    obtain ⟨u', c1, c2⟩ := walk_fits l rest 0 b (leadOk_zero _) h
    simp only at a1 a2
    subst a1
    obtain ⟨s, b1, b2⟩ := hl.whole a2
    exact ⟨r :: u', by rw [c1]; rfl, ⟨⟨s, b1, by rw [b2]⟩, a3⟩, c2⟩
  | .point n :: l, rs, lead, b, hl, ⟨r, rest, a1, a2, a3, h⟩ => by
    obtain ⟨u', c1, c2⟩ := walk_fits l rest 0 b (leadOk_zero _) h
    simp only at a1 a2
    subst a1
    obtain ⟨s, b1, b2⟩ := hl.whole a2
    exact ⟨r :: u', by rw [c1]; rfl, ⟨⟨s, b1, by rw [b2]; rfl⟩, a3⟩, c2⟩

theorem Fits.map {g : Fmt.Entry → Fmt.Entry} (hm : ∀ e, (g e).msg = e.msg) (hd : ∀ e, (g e).drawE = e.drawE) :
    ∀ {es : List Fmt.Entry} {rs : List Fmt.RoundView}, Fits es rs → Fits (es.map g) rs
  | [], [], _ => trivial
  | e :: _, _ :: _, ⟨⟨⟨s, h1, h2⟩, h3⟩, h4⟩ => ⟨⟨⟨s, h1, by rw [hm, h2]⟩, by rw [hd, h3]⟩, Fits.map hm hd h4⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- The lead behind a walk of the script is 0: its last stage is a sumcheck. -/
theorem Walk.last_sum : ∀ {l : List Stage} {vs : List Var} {e : Ends} {a b : Pos}, Walk (l ++ [.sum vs e]) a b → b.2 = 0
  | [], _, _, _, _, ⟨_, _, _, _, h⟩ => by rw [show _ = _ from h]
  | .scalars _ :: _, _, _, _, _, h => Walk.last_sum h.2
  | .sum _ _ :: _, _, _, _, _, ⟨_, _, _, _, h⟩ => Walk.last_sum h
  | .batch _ :: _, _, _, _, _, ⟨_, _, _, _, _, h⟩ => Walk.last_sum h
  | .point _ :: _, _, _, _, _, ⟨_, _, _, _, _, h⟩ => Walk.last_sum h

/-- **Where the hearing returns, the rounds used up are ROUNDS, entry for entry.** -/
theorem hear_rounds (p : Par) {F G : Fork} {rs rest : List Fmt.RoundView} {lead : Nat} {h : Heard}
    (hh : hear p.own (F, rs, 0) = some (h, G, rest, lead)) :
    ∃ used, rs = used ++ rest ∧ Fits ((rounds p).map (·.entry)) used := by
  obtain ⟨used, a1, a2⟩ := walk_fits (script p.own) rs 0 (rest, lead) (leadOk_zero _) (hear_walk hh)
  refine ⟨used, a1, ?_⟩
  unfold rounds
  rw [List.map_map]
  refine Fits.map (g := _) (fun e => ?_) (fun e => ?_) a2
  · show (if e.drawE == 0 then e else { e with work := p.work }).msg = _
    split <;> rfl
  · show (if e.drawE == 0 then e else { e with work := p.work }).drawE = _
    split <;> rfl

/-- As many rounds as ROUNDS has: nothing is left over. -/
theorem left_over_nil (p : Par) {F G : Fork} {rs rest : List Fmt.RoundView} {lead : Nat} {h : Heard}
    (hl : rs.length = (rounds p).length) (hh : hear p.own (F, rs, 0) = some (h, G, rest, lead)) : rest = [] := by
  obtain ⟨used, a1, a2⟩ := hear_rounds p hh
  have := a2.length
  rw [List.length_map] at this
  have h2 := congrArg List.length a1
  rw [List.length_append] at h2
  exact List.eq_nil_of_length_eq_zero (by omega)

/-- The lead behind the hearing is 0. -/
theorem hear_lead {x : Params.AttentionRounds} {s0 s' : St} {h : Heard} (hh : hear x s0 = some (h, s')) :
    s'.2.2 = 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, s15, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    h16⟩ := (hear_ran hh).ran
  obtain ⟨F, rs, lead⟩ := s15
  obtain ⟨G, rs', lead'⟩ := s'
  exact (sum_spec h16).2.1

/-! ## The block -/

theorem roundsFit_length : ∀ (ds : List Fmt.DeclaredRound) (rs : List Fmt.RoundView), Desc.roundsFit ds rs = true →
    rs.length = ds.length
  | [], [], _ => rfl
  | _ :: ds, _ :: rs, h => by
    simp only [Desc.roundsFit, Bool.and_eq_true] at h
    simp [roundsFit_length ds rs h.2]
  | [], _ :: _, h => by simp [Desc.roundsFit] at h
  | _ :: _, [], h => by simp [Desc.roundsFit] at h

/-- **decide's yes is**: nothing owed; a ledger; the hearing's return, all rounds used up, no lead
behind; the seat's lay of
just what was heard and the ledger behind it. Of the state, decide turns what `lay` lays, and
nothing else. -/
theorem decide_lays {S : Type} (seat : Seat S) (p : Par) (s s' : S) (rs : List Fmt.RoundView) :
    decide seat p s rs = .ok s' ↔ seat.owed s = none ∧ ∃ F h G, seat.ledger s = some F ∧
      hear p.own (F, rs, 0) = some (h, G, [], 0) ∧ seat.lay s h G = some s' := by
  unfold decide
  cases h1 : seat.owed s with
  | some n => simp [need, bind, Except.bind]
  | none =>
    cases h2 : seat.ledger s with
    | none => simp [need, named, bind, Except.bind]
    | some F =>
      cases h3 : hear p.own (F, rs, 0) with
      | none => simp [need, named, bind, Except.bind, h3]
      | some y =>
        obtain ⟨h, G, rest, lead⟩ := y
        have hl : lead = 0 := hear_lead h3
        subst hl
        cases rest with
        | cons r rest => simp [need, named, bind, Except.bind, h3]
        | nil =>
          cases h4 : seat.lay s h G with
          | none => simp [need, named, bind, Except.bind, h3, h4]
          | some t =>
            simp only [need, named, bind, Except.bind, h3, h4, Option.isNone_none, List.isEmpty_nil, if_true,
              Except.ok.injEq, true_and, Option.some.injEq]
            constructor
            · intro e
              exact ⟨F, h, G, rfl, h3, by rw [h4, e]⟩
            · rintro ⟨F', h', G', e1, e2, e3⟩
              subst e1
              rw [h3] at e2
              simp only [Option.some.injEq, Prod.mk.injEq, and_true] at e2
              obtain ⟨e4, e5⟩ := e2
              subst e4 e5
              rw [h4] at e3
              exact Option.some.inj e3

/-- With as many rounds as ROUNDS has, decide never refuses under the name "K5.left-over". -/
theorem decide_not_left_over {S : Type} (seat : Seat S) (p : Par) (s : S) (rs : List Fmt.RoundView)
    (hl : rs.length = (rounds p).length) : decide seat p s rs ≠ .error "K5.left-over" := by
  unfold decide
  cases h1 : seat.owed s with
  | some n => simp [need, bind, Except.bind]
  | none =>
    cases h2 : seat.ledger s with
    | none => simp [need, named, bind, Except.bind]
    | some F =>
      cases h3 : hear p.own (F, rs, 0) with
      | none => simp [need, named, bind, Except.bind, h3]
      | some y =>
        obtain ⟨h, G, rest, lead⟩ := y
        have hr : rest = [] := left_over_nil p hl h3
        subst hr
        cases h4 : seat.lay s h G with
        | none => simp [need, named, bind, Except.bind, h3, h4]
        | some t => simp [need, named, bind, Except.bind, h3, h4]

/-- **In the general step the refusal "K5.left-over" never comes**: the test asks what roundsFit has
asked. -/
theorem never_left_over {S Cl : Type} (seat : Seat S)
    (claims : List (String × (Nat → S → Except String (List Cl × S)))) (p : Par) (firstTree : Nat) (s : S)
    (rs : List Fmt.RoundView) (cols : List Desc.OpenedColumn) :
    (attentionKind seat claims p).step firstTree s rs cols ≠ .error "K5.left-over" := by
  unfold Block.step
  cases h1 : Desc.roundsFit (attentionKind seat claims p).rounds rs with
  | false => simp [need, bind, Except.bind]
  | true =>
    have hl : (rs.map Desc.noDigest).length = (rounds p).length := by
      rw [List.length_map]; exact roundsFit_length _ _ h1
    have hd := decide_not_left_over seat p s (rs.map Desc.noDigest) hl
    simp only [need, bind, Except.bind, if_true]
    split
    · rename_i e he
      split at he
      · cases he
      · simp only [Except.error.injEq] at he
        subst he
        simp
    · split
      · rename_i e he
        intro hc
        simp only [Except.error.injEq] at hc
        subst hc
        exact hd he
      · simp [pure, Except.pure]

/-- planOk: at each sumcheck of the script the part's test on the plan says yes, at every lead. -/
theorem planOk_shape {p : Par} (h : planOk p = true) {vs : List Var} {e : Ends}
    (hm : Stage.sum vs e ∈ script p.own) (lead : Nat) : MaskedSum.shapeOk ⟨lead, vs, some e⟩ = true := by
  unfold planOk at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  exact h.2 _ hm

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.hear_ran
#print axioms VerifiableInference.Desc.First.Att.P.hear_walk
#print axioms VerifiableInference.Desc.First.Att.P.walk_fits
#print axioms VerifiableInference.Desc.First.Att.P.hear_rounds
#print axioms VerifiableInference.Desc.First.Att.P.left_over_nil
#print axioms VerifiableInference.Desc.First.Att.P.decide_lays
#print axioms VerifiableInference.Desc.First.Att.P.never_left_over
#print axioms VerifiableInference.Desc.First.Att.P.planOk_shape
