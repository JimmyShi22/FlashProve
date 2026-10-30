-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/Calls.lean: CONDITIONAL: THE CALLS THAT THE VERIFIER's HEARING LAYS ARE
THE ROW's. The verifier's hearing of an attention segment's own rounds (`hear`,
Johnson/Desc/First/Att/K5AttentionKind.lean) is typed beside its list of stages and does not read it; the honest
side's row of parts (`shapes`, Johnson/Desc/K5/Honest/Faces.lean) is folded from that list. Here:
where the hearing returns, each of its masked sumchecks was heard AT THE CALL OF THE ROW's PART, AS
DATA, on that part's own stretch of the rounds. Definitions of propositions, and statements with
their proofs.

  `StagesRan`, `StagesRan.append`, `takes_stages`, `units_stages`   a list of stages has run, verb
      by verb of the hearing's own four verbs, with each sumcheck's start form and what was heard
  `startsOf`, `hear_stages`   the hearing's start forms as its text lays them; **where the hearing
      returns, the script's stages have run** (off `hear_ran`, Johnson/Desc/First/Att/K5Shape.lean)
  `CallsAre`, `stages_calls`, `call_is`   **the calls are the parts'**: for each part that is a
      sumcheck, in order: `MaskedSum.hear` has returned at the part's own call, on the part's
      rounds; and so has the laying of the hiding polynomial's coefficients behind it
  `isSum`, `callsAre_at`, `firstOf_eq`, `call_at`   the same by the part's number: on the rounds
      from `firstOf x q` on

Every statement on a hearing is CONDITIONAL: the hearing has returned. Who is meant to show that:
whoever shows the verifier's yes at the place.

Limits. One direction: from a return. The ledgers in front of and behind a sumcheck are named by
"there is": what they hold is the matter of the lemmas on the hearing's verbs. Nothing is said of
the values heard. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K5.Honest.Faces
import Johnson.Desc.First.Att.K5Shape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Honest
open OnBytes (zeroE)
open OnBytes.Model (Aff Fork)
open VerifiableInference.Desc.Part (MaskedSum.Heard MaskedSum.hear MaskedSum.row)
open VerifiableInference.Desc.Part.MaskedSum (Call)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (Stage products script St Heard batched keyStage TakesRan
  UnitsRan hear_ran take_spec sum_spec close_spec batch_spec)

/-! ## 1 The stages have run -/

/-- **The stages have run**, verb by verb of the verifier's hearing, from a state of its monad to a
state. ev: for each masked sumcheck among them, in order: its start form, and what was heard. -/
def StagesRan : List Stage → St → St → List (Aff × MaskedSum.Heard) → Prop
  | [], s, s', ev => s' = s ∧ ev = []
  | .scalars n :: l, s, s', ev => ∃ j s1, P.take n s = some (j, s1) ∧ StagesRan l s1 s' ev
  | .sum vs e :: l, s, s', ev => ∃ C hh ev' s1, ev = (C, hh) :: ev' ∧
      P.sum C (.sum vs e) s = some (hh, s1) ∧ StagesRan l s1 s' ev'
  | .batch rows :: l, s, s', ev => ∃ w s1, P.batch rows s = some (w, s1) ∧ StagesRan l s1 s' ev
  | .point n :: l, s, s', ev => ∃ d s1, P.close n s = some (d, s1) ∧ StagesRan l s1 s' ev

theorem StagesRan.append : ∀ {l l' : List Stage} {a m b : St}
    {e₁ e₂ : List (Aff × MaskedSum.Heard)}, StagesRan l a m e₁ → StagesRan l' m b e₂ →
    StagesRan (l ++ l') a b (e₁ ++ e₂)
  | [], _, _, _, _, _, _, ⟨h1, h2⟩, h' => by
    rw [h2, ← h1]
    exact h'
  | .scalars _ :: _, _, _, _, _, _, _, ⟨j, s1, h1, h2⟩, h' => ⟨j, s1, h1, StagesRan.append h2 h'⟩
  | .sum _ _ :: _, _, _, _, _, _, _, ⟨C, hh, ev', s1, h0, h1, h2⟩, h' =>
    ⟨C, hh, _, s1, by rw [h0]; rfl, h1, StagesRan.append h2 h'⟩
  | .batch _ :: _, _, _, _, _, _, _, ⟨w, s1, h1, h2⟩, h' => ⟨w, s1, h1, StagesRan.append h2 h'⟩
  | .point _ :: _, _, _, _, _, _, _, ⟨d, s1, h1, h2⟩, h' => ⟨d, s1, h1, StagesRan.append h2 h'⟩

theorem takes_stages (n : Nat) : ∀ (k : Nat) (js : List Nat) (s s' : St), TakesRan n k js s s' →
    StagesRan (List.replicate k (.scalars n)) s s' []
  | 0, [], _, _, h => ⟨h, rfl⟩
  | k + 1, j :: js, _, _, ⟨s1, h1, h2⟩ => ⟨j, s1, h1, takes_stages n k js _ _ h2⟩
  | 0, _ :: _, _, _, h => h.elim
  | _ + 1, [], _, _, h => h.elim

theorem units_stages : ∀ (us : List (Nat × Nat)) (os : List (Nat × MaskedSum.Heard)) (s s' : St),
    UnitsRan us os s s' →
    StagesRan (us.flatMap fun u => [.scalars 7, products u.1 u.2]) s s'
      (os.map fun o => (Aff.slot (o.1 + 6), o.2))
  | [], [], _, _, h => ⟨h, rfl⟩
  | _ :: us, o :: os, _, _, ⟨s2, ⟨s1, h1, h2⟩, h3⟩ =>
    ⟨o.1, s1, h1, _, o.2, _, s2, rfl, h2, units_stages us os _ _ h3⟩
  | [], _ :: _, _, _, h => h.elim
  | _ :: _, [], _, _, h => h.elim

/-- The start forms of the hearing's masked sumchecks, each with what was heard, in the order of the
stages: as the verifier's text lays them. -/
def startsOf (x : OnBytes.Params.AttentionRounds) (h : Heard) : List (Aff × MaskedSum.Heard) :=
  (h.scores.toList.map fun o => (Aff.slot (o.1 + 6), o.2)) ++
    [(.slot (h.five + 1), h.division), (.slot h.values, h.below), (.slot (h.values + 1), h.on),
      (batched x.pairs h.om h.maxima 1 0, h.atIndex),
      (batched x.pairs h.om' h.atIndex.sEnd 2 1, h.key), (.ofConst zeroE, h.cells)]

/-- **Where the hearing returns, the script's stages have run**, with these start forms. -/
theorem hear_stages {x : OnBytes.Params.AttentionRounds} {s0 s' : St} {h : Heard}
    (hh : P.hear x s0 = some (h, s')) : StagesRan (script x) s0 s' (startsOf x h) := by
  obtain ⟨sa, sb, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, pt, ha, hb, h1,
    h2, h3, h4, h5, h6, h7, h8, h9, _, h10, h11, h12, h13, h14, h15, h16⟩ := (hear_ran hh).ran
  exact StagesRan.append
    (StagesRan.append (e₁ := []) (takes_stages 3 _ _ _ _ ha) (units_stages _ _ _ _ hb))
    ⟨_, s1, h1, _, s2, h2, _, s3, h3, _, _, _, s4, rfl, h4, _, s5, h5, _, s6, h6,
      _, _, _, s7, rfl, h7, _, _, _, s8, rfl, h8, _, s9, h9, _, s10, h10, _, s11, h11,
      _, _, _, s12, rfl, h12, _, s13, h13, _, _, _, s14, rfl, h14, _, s15, h15,
      _, _, _, s', rfl, h16, rfl, rfl⟩

/-! ## 2 The calls -/

/-- **The hearing's masked sumchecks are the parts' calls, each on the part's own stretch of the
rounds.** rs: the rounds from the first part on. ev: start forms and what was heard. -/
def CallsAre : List PartShape → List Fmt.RoundView → List (Aff × MaskedSum.Heard) → Prop
  | [], _, ev => ev = []
  | .sum k :: L, rs, ev => ∃ C hh ev' F G₁ f G, ev = (C, hh) :: ev' ∧
      MaskedSum.hear C k F (rs.take (k.vs.length + 3)) = some (hh, G₁) ∧
      MaskedSum.row hh zeroE {} G₁ = some (f, G) ∧ CallsAre L (rs.drop (k.vs.length + 3)) ev'
  | .one _ :: L, rs, ev => CallsAre L (rs.drop 1) ev

/-- Stages that have run have laid the parts' calls. General in the stages. -/
theorem stages_calls : ∀ (st : List Stage) (F : Fork) (rs : List Fmt.RoundView) (lead : Nat) (s' : St)
    (ev : List (Aff × MaskedSum.Heard)), StagesRan st (F, rs, lead) s' ev →
    CallsAre (shapesOf lead st) rs ev
  | [], _, _, _, _, _, h => h.2
  | .scalars n :: l, F, rs, lead, s', ev, ⟨j, ⟨G, rs', lead'⟩, h1, h2⟩ => by
    obtain ⟨_, e2, e3, _⟩ := take_spec h1
    subst e2 e3
    exact stages_calls l G rs' (lead + n) s' ev h2
  | .sum vs e :: l, F, rs, lead, s', _, ⟨C, hh, ev', ⟨G, rs', lead'⟩, rfl, h1, h2⟩ => by
    obtain ⟨e1, e2, G1, f, a1, a2⟩ := sum_spec h1
    subst e1 e2
    exact ⟨C, hh, ev', F, G1, f, G, rfl, a1, a2, stages_calls l G _ 0 s' ev' h2⟩
  | .batch rows :: l, F, rs, lead, s', ev, ⟨w, ⟨G, rs', lead'⟩, h1, h2⟩ => by
    obtain ⟨_, e2, r, x, a1, _⟩ := batch_spec h1
    subst e2 a1
    exact stages_calls l G rs' 0 s' ev h2
  | .point n :: l, F, rs, lead, s', ev, ⟨d, ⟨G, rs', lead'⟩, h1, h2⟩ => by
    obtain ⟨_, e2, r, a1, _⟩ := close_spec h1
    subst e2 a1
    exact stages_calls l G rs' 0 s' ev h2

/-- **THE CALLS THAT THE VERIFIER's HEARING LAYS ARE THE ROW's.** Conditional: the hearing has
returned. -/
theorem call_is {x : OnBytes.Params.AttentionRounds} {F : Fork} {rs : List Fmt.RoundView} {s' : St}
    {h : Heard} (hh : P.hear x (F, rs, 0) = some (h, s')) :
    CallsAre (shapes x) rs (startsOf x h) :=
  stages_calls _ F rs 0 s' _ (hear_stages hh)

/-! ## 3 By the part's number -/

/-- The part is a masked sumcheck. -/
def isSum : PartShape → Bool
  | .sum _ => true
  | .one _ => false

/-- The same by the part's number: the sumcheck that is part q is heard on the rounds from the
part's first on; it is the one among the start forms that has as many in front as there are
sumchecks among the parts in front. -/
theorem callsAre_at : ∀ (L : List PartShape) (rs : List Fmt.RoundView)
    (ev : List (Aff × MaskedSum.Heard)), CallsAre L rs ev → ∀ (q : Nat) (k : Call),
    L[q]? = some (.sum k) → ∃ C hh F G₁ f G,
      ev[((L.take q).filter isSum).length]? = some (C, hh) ∧
      MaskedSum.hear C k F ((rs.drop ((L.take q).map (·.rounds)).sum).take (k.vs.length + 3)) =
        some (hh, G₁) ∧ MaskedSum.row hh zeroE {} G₁ = some (f, G)
  | [], _, _, _, _, _, h => by cases h
  | .sum k' :: L, rs, _, ⟨C, hh, ev', F, G₁, f, G, rfl, a1, a2, a3⟩, 0, k, h => by
    obtain rfl : k' = k := by
      have := Option.some.inj h
      cases this
      rfl
    exact ⟨C, hh, F, G₁, f, G, rfl, a1, a2⟩
  | .sum k' :: L, rs, _, ⟨C, hh, ev', F, G₁, f, G, rfl, a1, a2, a3⟩, q + 1, k, h => by
    obtain ⟨C', hh', F', G', f', G'', b1, b2, b3⟩ := callsAre_at L _ ev' a3 q k h
    refine ⟨C', hh', F', G', f', G'', b1, ?_, b3⟩
    rw [List.drop_drop] at b2
    exact b2
  | .one _ :: L, rs, ev, a3, 0, k, h => by cases h
  | .one _ :: L, rs, ev, a3, q + 1, k, h => by
    obtain ⟨C', hh', F', G', f', G'', b1, b2, b3⟩ := callsAre_at L _ ev a3 q k h
    refine ⟨C', hh', F', G', f', G'', b1, ?_, b3⟩
    rw [List.drop_drop] at b2
    exact b2

/-- A part's first round, as a sum. -/
theorem firstOf_eq (x : OnBytes.Params.AttentionRounds) (q : Nat) :
    firstOf x q = (((shapes x).take q).map (·.rounds)).sum := by
  have hf : ∀ (l : List Nat) (a : Nat), l.foldl (· + ·) a = a + l.sum := by
    intro l
    induction l with
    | nil => intro a; rfl
    | cons b l ih =>
      intro a
      rw [List.foldl_cons, ih, List.sum_cons, Nat.add_assoc]
  unfold firstOf cut
  rw [hf, Nat.zero_add, List.map_take]

/-- **The call of the sumcheck that is part q**, on the rounds from `firstOf x q` on. Conditional:
the hearing has returned. -/
theorem call_at {x : OnBytes.Params.AttentionRounds} {F : Fork} {rs : List Fmt.RoundView} {s' : St}
    {h : Heard} (hh : P.hear x (F, rs, 0) = some (h, s')) (q : Nat) (k : Call)
    (hq : (shapes x)[q]? = some (.sum k)) : ∃ C hd F' G₁ f G,
      (startsOf x h)[(((shapes x).take q).filter isSum).length]? = some (C, hd) ∧
      MaskedSum.hear C k F' ((rs.drop (firstOf x q)).take (k.vs.length + 3)) =
        some (hd, G₁) ∧ MaskedSum.row hd zeroE {} G₁ = some (f, G) := by
  rw [firstOf_eq]
  exact callsAre_at _ rs _ (call_is hh) q k hq

end H2K5.Honest

#print axioms H2K5.Honest.StagesRan.append
#print axioms H2K5.Honest.takes_stages
#print axioms H2K5.Honest.units_stages
#print axioms H2K5.Honest.hear_stages
#print axioms H2K5.Honest.stages_calls
#print axioms H2K5.Honest.call_is
#print axioms H2K5.Honest.callsAre_at
#print axioms H2K5.Honest.firstOf_eq
#print axioms H2K5.Honest.call_at
