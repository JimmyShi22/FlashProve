-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K10/Honest/Fits.lean: THE CLOSING OF A SEGMENT (K10): FOUR STONES THAT CALLERS OF
Johnson/Desc/K10/Honest/Split.lean AND Returns.lean LACKED. Lemmas on the verifier's own text; no
honest side's frame in them; none of the library's goals. FOR TWO OF THE FOUR THE LIBRARY HOLDS
THE GENERAL STONE, not called here: rounds that fit, both ways, at any declared rounds:
`roundsFit_iff` (Johnson/Top/H0/StepLaws/RoundsFit.lean); what a yes of the closing leaves, from
the yes alone, in the library's words: `closing_inv2`
(Johnson/Desc/First/Close/Law/Whole.lean). For the number of rounds alone the library has
`roundsFit_length` (Johnson/Top/H0/StepLaws/StepLaws.lean) with `kind_rounds_length`
(First/Close/Law/RoundsOfPar.lean). OF WHAT FOLLOWS ONE SEARCH OF THE LIBRARY, WHICH DID NOT OPEN
EVERY FILE, FOUND NO LIKE: the first at the kind's own shape of rounds; the second in the words of
Returns.lean's `CloseLeft`, with the whole record behind.

  `rounds_back`, `rounds_fit_iff`   THE WAY BACK: rounds that fit the kind's declared rounds
                 (`roundsFit`, Johnson/Desc/Block.lean) are 2 + k rounds of the kind's shape; with
                 Step.lean's `rounds_fit`: just these
  `fits_iff`     the step's own tests in front of the decision (`Block.Fits`,
                 Johnson/Top/H0/StepLaws/StepLaws.lean) at the kind's block ARE: 2 + k rounds of
                 the kind's shape. No column is asked
    `vals_noDigest`   the second test of Split.lean does not see the rounds' sealed digest
  `step_split`   THE STEP SAYS YES JUST IF the rounds are 2 + k of the kind's shape and the two
                   tests of Split.lean say yes; `step_none`: it takes no column
  `yes_left`     WHAT A YES OF THE DECISION LEAVES (`CloseLeft`, Returns.lean), FROM THE YES
                 ALONE: at the data that the record names (`baseData`): Returns.lean's
                 `yes_behind` without its premise on the facts in front

Limits. Of the block at the kind's own record. It stands over files of this folder (YesFree,
Front, FrontToy, Base, BaseB, RowFits, Step, Returns, Split). Shown of no honest run. Nothing on
soundness, completeness or hiding of the protocol.

-/
import Johnson.Desc.K10.Honest.Split
import Johnson.Desc.K10.Honest.Step
import Johnson.Desc.K10.Honest.Returns
import Johnson.Top.H0.StepLaws.StepLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.YesFree
open OnBytes OnBytes.Means VerifiableInference.Desc VerifiableInference.Desc.First.Close

/-- Values that are all items "an element of the extension field" are such elements. -/
theorem vals_back : ∀ (n : Nat) (l : List Fmt.ItemValue), l.map itemOf = List.replicate n Fmt.Item.e →
    ∃ xs : List Fmt.Ext, l = xs.map Fmt.ItemValue.e ∧ xs.length = n
  | 0, [], _ => ⟨[], rfl, rfl⟩
  | 0, _ :: _, h => by cases h
  | _ + 1, [], h => by cases h
  | n + 1, v :: l, h => by
    rw [List.map_cons, List.replicate_succ] at h
    obtain ⟨h1, h2⟩ := List.cons.inj h
    obtain ⟨xs, rfl, hl⟩ := vals_back n l h2
    cases v with
    | e x => exact ⟨x :: xs, rfl, by rw [List.length_cons, hl]⟩
    | f _ => cases h1
    | word _ => cases h1
    | root _ => cases h1
    | answer _ => cases h1

/-- One round, the way back. -/
theorem round_back {e : Fmt.Entry} {n : Nat} {r : Fmt.RoundView} (h1 : e.answers = 0) (h2 : e.roots = 0)
    (h3 : e.msg = 24 * n) (h4 : e.drawE = 1) (h5 : e.poss = 0) (h6 : e.trits = 0)
    {ds : List Fmt.DeclaredRound} {rs : List Fmt.RoundView}
    (h : roundsFit ({ entry := e } :: ds) (r :: rs) = true) :
    Shaped n r ∧ roundsFit ds rs = true := by
  have i2 : (({ entry := e } : Fmt.DeclaredRound).items.filter (· != .root)) =
      List.replicate n Fmt.Item.e := by
    show (e.cut.filter (· != .root)) = _
    unfold Fmt.Entry.cut
    rw [h1, h2, h3]
    simp
  rw [roundsFit, i2] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, _⟩, _⟩, _⟩, a8⟩ := h
  have a2' : r.drawn.elems.length = 1 := a2.trans h4
  have a3' : r.drawn.poss.length = 0 := a3.trans h5
  have a4' : r.drawn.trits.length = 0 := a4.trans h6
  exact ⟨⟨vals_back n _ a1, List.length_eq_one_iff.1 a2', List.eq_nil_of_length_eq_zero a3',
    List.eq_nil_of_length_eq_zero a4'⟩, a8⟩

/-- The rounds "FOLD round", the way back. -/
theorem folds_back (e : Fmt.Entry) (h1 : e.answers = 0) (h2 : e.roots = 0) (h3 : e.msg = 24 * 2)
    (h4 : e.drawE = 1) (h5 : e.poss = 0) (h6 : e.trits = 0) : ∀ (k : Nat) (rs : List Fmt.RoundView),
    roundsFit (List.replicate k { entry := e }) rs = true →
      rs.length = k ∧ ∀ r ∈ rs, Shaped 2 r
  | 0, [], _ => ⟨rfl, fun _ h => nomatch h⟩
  | 0, _ :: _, h => by cases h
  | _ + 1, [], h => by cases h
  | k + 1, r :: rs, h => by
    rw [List.replicate_succ] at h
    obtain ⟨a, b⟩ := round_back h1 h2 h3 h4 h5 h6 h
    obtain ⟨c, d⟩ := folds_back e h1 h2 h3 h4 h5 h6 k rs b
    refine ⟨by rw [List.length_cons, c], fun q hq => ?_⟩
    rcases List.mem_cons.1 hq with rfl | hq
    · exact a
    · exact d q hq

/-- **THE WAY BACK**: rounds that fit the kind's declared rounds are 2 + k rounds of the kind's
shape. -/
theorem rounds_back {Cl : Type} (P : Par) (rs : List Fmt.RoundView)
    (h : roundsFit ((kind (Cl := Cl)) P).rounds rs = true) :
    rs.length = 2 + P.k ∧ ShapedAll rs := by
  have h' : roundsFit ((entries P).map fun e => ({ entry := e } : Fmt.DeclaredRound)) rs = true := h
  rw [entries_eq, List.map_cons, List.map_cons, List.map_replicate] at h'
  match rs, h' with
  | [], h' => cases h'
  | [_], h' =>
    obtain ⟨_, b⟩ := round_back (e := eBat P) (n := 0) rfl rfl rfl rfl rfl rfl h'
    cases b
  | rB :: rE :: rR, h' =>
    obtain ⟨a, b⟩ := round_back (e := eBat P) (n := 0) rfl rfl rfl rfl rfl rfl h'
    obtain ⟨c, d⟩ := round_back (e := eEps P) (n := 1) rfl rfl rfl rfl rfl rfl b
    obtain ⟨e, f⟩ := folds_back (eRound P) rfl rfl rfl rfl rfl rfl P.k rR d
    exact ⟨by rw [List.length_cons, List.length_cons, e]; omega, a, c, f⟩

/-- Rounds fit the kind's declared rounds just if they are 2 + k rounds of the kind's shape. -/
theorem rounds_fit_iff {Cl : Type} (P : Par) (rs : List Fmt.RoundView) :
    roundsFit ((kind (Cl := Cl)) P).rounds rs = true ↔ rs.length = 2 + P.k ∧ ShapedAll rs :=
  ⟨rounds_back P rs, fun h => rounds_fit P rs h.1 h.2⟩

/-- **The step's own tests at the kind's block** are: 2 + k rounds of the kind's shape; of the
columns nothing is asked. -/
theorem fits_iff {Cl : Type} (P : Par) (ft : Nat) (rs : List Fmt.RoundView) (cols : List OpenedColumn) :
    ((kind (Cl := Cl)) P).Fits ft rs cols ↔ rs.length = 2 + P.k ∧ ShapedAll rs := by
  have g : groupsOf ft ((kind (Cl := Cl)) P).rounds (rs.map (·.drawn)) = [] :=
    groups_nil ft (entries P) _
  unfold Block.Fits Block.want
  rw [g, rounds_fit_iff]
  simp

/-- The second test reads of the rounds what "BAT" drew alone: so it does not see the sealed
digest. -/
theorem vals_noDigest (s : Rec) (rs : List Fmt.RoundView) :
    closeValsB s (rs.map noDigest) = closeValsB s rs := by
  unfold closeValsB
  rw [batDraw_noDigest]

/-- The step takes no column. -/
theorem step_none {Cl : Type} {P : Par} {ft : Nat} {s s' : Rec} {rs : List Fmt.RoundView} {cols : List OpenedColumn}
    {n : Nat} (h : ((kind (Cl := Cl)) P).step ft s rs cols = .ok (s', n)) : n = 0 := by
  obtain ⟨_, _, h3⟩ := (step_iff ft _ s s' rs cols n).1 h
  have g : groupsOf ft ((kind (Cl := Cl)) P).rounds (rs.map (·.drawn)) = [] :=
    groups_nil ft (entries P) _
  rw [h3]
  unfold Block.want
  rw [g]
  rfl

/-- **THE STEP SAYS YES JUST IF** the rounds are 2 + k of the kind's shape and both tests say yes.
-/
theorem step_split {Cl : Type} (P : Par) (ft : Nat) (s : Rec) (rs : List Fmt.RoundView) (cols : List OpenedColumn) :
    (∃ s' n, ((kind (Cl := Cl)) P).step ft s rs cols = .ok (s', n)) ↔
      rs.length = 2 + P.k ∧ ShapedAll rs ∧ closeShapeB P s = true ∧ closeValsB s rs = true := by
  rw [← vals_noDigest s rs]
  constructor
  · rintro ⟨s', n, h⟩
    obtain ⟨h1, h2, _⟩ := (step_iff ft _ s s' rs cols n).1 h
    obtain ⟨a, b⟩ := (fits_iff P ft rs cols).1 h1
    obtain ⟨_, _, c, d⟩ := (close_yes_split (Cl := Cl) P s _ _).1 ⟨s', h2⟩
    exact ⟨a, b, c, d⟩
  · rintro ⟨a, b, c, d⟩
    obtain ⟨s', h2⟩ := (close_yes_split (Cl := Cl) P s (rs.map noDigest)
      (((kind (Cl := Cl)) P).shown ft rs cols)).2
      ⟨by rw [List.length_map, a], shapedAll_noDigest b, c, d⟩
    exact ⟨s', _, (step_iff ft _ s s' rs cols _).2 ⟨(fits_iff P ft rs cols).2 ⟨a, b⟩, h2, rfl⟩⟩

/-- **WHAT A YES OF THE DECISION LEAVES, FROM THE YES ALONE**: `CloseLeft` at the data that the
record names. -/
theorem yes_left {Cl : Type} {P : Par} {s s' : Rec} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : ((kind (Cl := Cl)) P).decide s rs gs = .ok s') :
    ∃ D, baseData s = some D ∧ CloseLeft P s D rs s' := by
  obtain ⟨y, hy, rfl⟩ := (kind_decide_iff P s s' rs gs).1 h
  obtain ⟨_, L, k2, G, k3, _, rows, hc, hf'⟩ := (closeFrame_iff _ _ _ _ _ y.1 y.2).1 hy
  obtain ⟨eB, es₁, rB, rs₁, e1, rfl, m, hm, row, Ly, S1, hbat, _, hfold⟩ := hc
  obtain ⟨b1, input, d, b2, xs, x, b3, _, b5, rfl, rfl⟩ := hbat
  obtain ⟨eE, eR, rE, rR, e2, rfl, _, _, _, _, _, d2, f6, sum, eps, f7, _, gam, cl, f9, f10,
    f11⟩ := hfold
  rw [entries_eq] at e1
  obtain ⟨rfl, rfl⟩ := List.cons.inj e1
  obtain ⟨rfl, rfl⟩ := List.cons.inj e2
  obtain ⟨t, ht, rfl⟩ := b3.2.2.2.2.2.2
  have hb : Ground.ok (Ground.beginRunL s.st s.frame.group) = true := List.all_eq_true.2 b1
  obtain ⟨Gs, hG⟩ : ∃ Gs, s.st.groups[s.frame.group]? = some Gs :=
    Option.isSome_iff_exists.1 (b1 _ (List.mem_cons_self ..))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj ((begin_at hb hG).symm.trans b2))
  have hd2 : d2.st = spent (Slice.begun s.st s.frame.group Gs) m := by
    unfold Ground.spendAsMaskP at f6
    split at f6
    · obtain rfl := Option.some.inj f6
      rfl
    · cases f6
  refine ⟨⟨L, G, m, Gs⟩, baseData_of k2 k3 hm hG, rB, rE, rR, t, row, sum, eps, gam, cl, rfl, ht,
    b5, f7, f9, ?_, ?_⟩
  · rw [rounds_len _ _ _ _ _ f9, List.length_replicate]
  · show (⟨none, y.1, y.2⟩ : Rec) = _
    unfold closeBehind
    rw [hf', f11, f10, hd2]
    rfl

end ProofFile.Honest.K10.YesFree

#print axioms ProofFile.Honest.K10.YesFree.rounds_fit_iff
#print axioms ProofFile.Honest.K10.YesFree.fits_iff
#print axioms ProofFile.Honest.K10.YesFree.vals_noDigest
#print axioms ProofFile.Honest.K10.YesFree.step_none
#print axioms ProofFile.Honest.K10.YesFree.step_split
#print axioms ProofFile.Honest.K10.YesFree.yes_left
