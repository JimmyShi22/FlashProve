-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/SecondOwed.lean: kind K14: "K14, second part" (⟨3, none, 0,
.K14⟩): OF THE TESTS OF secondList (Honest/K14/SecondYes.lean) FOURTEEN HOLD BY THE MAKE OF THE
LIBRARY's OWN FUNCTIONS WHEREVER THE TESTS IN FRONT OF THEM HOLD: here they are struck, and what is
left is one shorter list. No theorem says that each of its tests can be false: evaluations at turns
of one small synthetic state, in a file that is not part of this tree, are all that speaks for it. A
definition with code, and statements with their proofs.

  secondOwed p s  **THE SHORTER LIST**: five tests that something is there (each listed only where
                  it is false) and nineteen more: so its length is a function of the state. All but
                  the last three read the state in front itself; these three (that the row (Dot)
                  can be made, and the two clauses on laying it) read what takeOver returns: where
                  takeOver returns an error they are left out, and an earlier test is false there
  adopted_at, elsewhere_ok, join_ok   the message that adoptP lays is there, at the next free
                  number, with the notice's shape, not sampled; so the seven clauses of elsewhereL
                  come down to three, and the eight of joinL to five
  dot_bare        the row (Dot), where it can be made, is no sample row and has no single entry, no
                  run and no whole form: so the eight clauses of rowL come down to two
  owed_list       **all of secondOwed true: all of secondList true**
  second_owed     **so the member's decide function returns**

STRUCK, AS HOLDING BY MAKE: "Omega: its number here"; of elsewhereL: the message here is there, the
message there is there (asked in front), not sampled here, the same rows, degree and answers; of
joinL: the message is there, sampled, kept only with main rows; of rowL: the group is there and no
test has begun (asked in front, at the joining), no sample row, the single entries, the runs and the
forms fit their places.

What is not claimed. That the list is all true at any state. The converse (secondList's own
converse: second_only). Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.SecondYes
import Johnson.Desc.Third.Law.Says
import Johnson.Desc.Third.Law.Sharp
import Johnson.Desc.K14.Honest.YesCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (linDotRow linLayOmega linLayW OracleNotice)
open OnBytes.Slice (stSent)
open Desc.Plain (DState)
open VerifiableInference.Desc (Own.tensorInOrder Own.placeFits Own.allZero)
open VerifiableInference.Desc.Ground (Clauses ok has adoptL adoptP elsewhereL elsewhereP joinL joinP
  rowL addRowP)
open VerifiableInference.Desc.Later (adoptP_inv elsewhereP_inv)
open VerifiableInference.Desc.Third (S₃ P₁₄ Loc₃ SharedOut batchLinearConstraintsSecondPart takeOver plainArm firstStepB)
open VerifiableInference.Desc.Third.Law (takeOver_says linDotRow_plain modify_same)
open Desc.K14.Honest (units_addLaid runs_addLaid forms_addLaid)

/-- **THE SHORTER LIST**: five tests that something is there, each listed only where it is false,
and nineteen more. Where takeOver returns an error the last three tests are left out (the arm that
gives the empty list): an earlier test is false there, since takeOver returns wherever the tests in
front of it hold (so the proof of owed_list, by takeOver_of_list). -/
def secondOwed (p : P₁₄) (s : S₃) : Clauses :=
  match s.loc.border with
  | none => [("the two ends are at hand", false)]
  | some x =>
  match x.shared.book.place[x.shared.omega]? with
  | none => [("Omega: it has a place in the shared chain's book", false)]
  | some q =>
  match x.shared.book.trees[q.1]? with
  | none => [("Omega: its tree is in the shared chain's book", false)]
  | some t =>
  match x.shared.st.oracles[x.shared.omega]? with
  | none => [("Omega: it is in the shared chain's statement", false)]
  | some y =>
    ("the shape does not split the row (Dot)", plainArm p.S) ::
    ("no root is received yet, and the first own tree's number counts just one tree more",
      firstStepB s.roots s.loc.firstTree s.book) ::
    ("Omega: it has a tree to itself", t.parts.size == 1) ::
    ("Omega: it has the plan's shape", decide (y.shape = p.S.omega)) ::
    (adoptL s.st s.book #[{ shape := y.shape, leafClass := p.S.omegaLeafClass }]
      #[(t.number, t.src)] ++
    (("elsewhere: sampled there", y.sampled) ::
    ("elsewhere: the same main code", y.shape.mainRows == 0 ||
      has s.st.codes.base[y.shape.code]? fun c =>
        x.shared.st.codes.base[y.shape.code]? == some c) ::
    ("elsewhere: the same mask code", y.shape.maskRows == 0 ||
      has s.st.codes.mask[y.shape.maskCode]? fun z =>
        x.shared.st.codes.mask[y.shape.maskCode]? == some z) ::
    ("join: the group is there", (s.st.groups[s.loc.own]?).isSome) ::
    ("join: no test has begun", has s.st.groups[s.loc.own]? (!·.inRun)) ::
    ("join: the group's main code",
      has s.st.groups[s.loc.own]? fun G => y.shape.mainRows == 0 || y.shape.code == G.code) ::
    ("join: the group's mask code",
      has s.st.groups[s.loc.own]? fun G =>
        y.shape.maskRows == 0 || y.shape.maskCode == G.maskCode) ::
    ("join: no member twice",
      has s.st.groups[s.loc.own]? (!·.members.contains s.st.oracles.size)) ::
    match takeOver p.S s.loc.own x.shared (s.withCols []) with
    | .error _ => []
    | .ok a =>
      match linDotRow p.S x.g x.shared.psi a.1 (linLayOmega a.2.st.codes p.S) s.loc.w
          (linLayW a.2.st.codes p.S) with
      | none => [("the row (Dot) can be made", false)]
      | some dot =>
        [("addRow: the terms fit their places", has a.2.st.groups[s.loc.own]? fun G =>
            dot.terms.all fun t =>
              Own.tensorInOrder t.v && Own.placeFits a.2.st G t.oracle t.part t.v.vars 0),
         ("addRow: ON VALUES: no coefficient on a pad", has a.2.st.groups[s.loc.own]? fun G =>
            G.members.all fun o =>
              ((a.2.st.oracles[o]?).map (·.pad)).getD [] |>.all fun q =>
                Own.allZero (dot.coefficient o q.1 q.2))]))

variable {L : Type}

/-- The message that adoptP lays for one notice: at the next free number, with the notice's shape,
and every other field at the structure's default (so: not sampled); the codes and the groups
stay. -/
theorem adopted_at (d : DState L) (n : OracleNotice) (given : Array (Nat × Fmt.Src))
    (a : Array Nat × DState L) (h : adoptP d #[n] given = some a) :
    a.1[0]? = some d.st.oracles.size ∧
      a.2.st.oracles[d.st.oracles.size]? = some { shape := n.shape } ∧
      a.2.st.codes = d.st.codes ∧ a.2.st.groups = d.st.groups := by
  obtain ⟨e0, e1⟩ := adoptP_inv d #[n] given a h
  refine ⟨by rw [e1]; simp, by rw [e0]; simp [stSent], by rw [e0]; rfl, by rw [e0]; rfl⟩

/-- The seven clauses of elsewhereL at that message come down to three (h3, h6, h7), where the
message there is y (hy). -/
theorem elsewhere_ok (d : DState L) (y : OnBytes.Oracle) (lc : Nat)
    (given : Array (Nat × Fmt.Src)) (a : Array Nat × DState L)
    (h : adoptP d #[{ shape := y.shape, leafClass := lc }] given = some a)
    (other : OnBytes.Statement) (theirs : Nat) (hy : other.oracles[theirs]? = some y)
    (h3 : y.sampled = true)
    (h6 : (y.shape.mainRows == 0 || has d.st.codes.base[y.shape.code]? fun c =>
      other.codes.base[y.shape.code]? == some c) = true)
    (h7 : (y.shape.maskRows == 0 || has d.st.codes.mask[y.shape.maskCode]? fun z =>
      other.codes.mask[y.shape.maskCode]? == some z) = true) :
    ok (elsewhereL a.2.st d.st.oracles.size other theirs) = true := by
  obtain ⟨-, hx, hc, -⟩ := adopted_at d _ given a h
  simp only [ok, elsewhereL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  rw [hx, hy, hc]
  refine ⟨rfl, rfl, h3, rfl, ?_, h6, h7⟩
  show (y.shape.mainRows == y.shape.mainRows && y.shape.mainDeg == y.shape.mainDeg &&
    y.shape.maskRows == y.shape.maskRows && y.shape.answers == y.shape.answers) = true
  simp

/-- The eight clauses of joinL behind that come down to five. -/
theorem join_ok (d : DState L) (y : OnBytes.Oracle) (lc : Nat) (given : Array (Nat × Fmt.Src))
    (a : Array Nat × DState L)
    (h : adoptP d #[{ shape := y.shape, leafClass := lc }] given = some a)
    (other : OnBytes.Statement) (theirs : Nat) (d₁ : DState L)
    (h1 : elsewhereP a.2 d.st.oracles.size other theirs = some d₁) (own : Nat)
    (j1 : (d.st.groups[own]?).isSome = true) (j4 : has d.st.groups[own]? (!·.inRun) = true)
    (j5 : (has d.st.groups[own]? fun G => y.shape.mainRows == 0 || y.shape.code == G.code) = true)
    (j6 : (has d.st.groups[own]? fun G =>
      y.shape.maskRows == 0 || y.shape.maskCode == G.maskCode) = true)
    (j7 : has d.st.groups[own]? (!·.members.contains d.st.oracles.size) = true) :
    ok (joinL d₁.st own d.st.oracles.size false) = true := by
  obtain ⟨-, hx, -, hg⟩ := adopted_at d _ given a h
  obtain ⟨y', -, e1, -⟩ := elsewhereP_inv a.2 d₁ _ other theirs h1
  have hx1 : d₁.st.oracles[d.st.oracles.size]? = some
      { shape := y.shape, sampled := true
        sampleRows := y'.sampleRows.map (·.renamed d.st.oracles.size), pad := y'.pad } := by
    rw [e1]
    exact modify_same _ _ _ _ hx
  have hg1 : d₁.st.groups = d.st.groups := by rw [e1]; exact hg
  simp only [ok, joinL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
  rw [hx1, hg1]
  exact ⟨j1, rfl, rfl, j4, j5, j6, j7, rfl⟩

/-- The row (Dot), where it can be made, is no sample row and has no single entry, no run and no
whole form. -/
theorem dot_bare (S : OnBytes.Params.LinShape) (weights : List OnBytes.Tensor)
    (psi : List OnBytes.E) (omega : Nat) (omegaLay : OnBytes.VectorLay) (w : Nat)
    (wLay : OnBytes.VectorLay) (row : OnBytes.Row)
    (h : linDotRow S weights psi omega omegaLay w wLay = some row) :
    row.kind = .plain ∧ row.units = #[] ∧ row.runs = #[] ∧ row.forms = #[] := by
  refine ⟨linDotRow_plain S weights psi omega omegaLay w wLay row h, ?_⟩
  unfold linDotRow at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨_, _, cut, _, hrow⟩ := h
  rw [← hrow]
  exact ⟨by rw [units_addLaid, units_addLaid], by rw [runs_addLaid, runs_addLaid],
    by rw [forms_addLaid, forms_addLaid]⟩

/-- **All of secondOwed true: all of secondList true.** -/
theorem owed_list (p : P₁₄) (s : S₃) (h : ok (secondOwed p s) = true) :
    ok (secondList p s) = true := by
  unfold secondOwed at h
  cases hx : s.loc.border with
  | none => rw [hx] at h; cases h
  | some x =>
    rw [hx] at h
    dsimp only at h
    cases hq : x.shared.book.place[x.shared.omega]? with
    | none => rw [hq] at h; cases h
    | some q =>
      rw [hq] at h
      dsimp only at h
      cases ht : x.shared.book.trees[q.1]? with
      | none => rw [ht] at h; cases h
      | some t =>
        rw [ht] at h
        dsimp only at h
        cases hy : x.shared.st.oracles[x.shared.omega]? with
        | none => rw [hy] at h; cases h
        | some y =>
          rw [hy] at h
          dsimp only at h
          rw [ok_cons, ok_cons, ok_cons, ok_cons, ok_append, ok_cons, ok_cons, ok_cons, ok_cons,
            ok_cons, ok_cons, ok_cons, ok_cons] at h
          simp only [Bool.and_eq_true] at h
          obtain ⟨h2, h3, h6, h8, hA, e3, e6, e7, j1, j4, j5, j6, j7, h⟩ := h
          obtain ⟨a, ha⟩ := adoptP_of_ok (s.withCols []) _ _ hA
          obtain ⟨hm, -, -, -⟩ := adopted_at _ _ _ a ha
          have hE := elsewhere_ok (s.withCols []) y _ _ a ha x.shared.st x.shared.omega hy e3 e6 e7
          obtain ⟨d₁, hd₁⟩ := elsewhereP_of_ok a.2 _ _ _ hE
          have hJ := join_ok (s.withCols []) y _ _ a ha _ _ d₁ hd₁ s.loc.own j1 j4 j5 j6 j7
          have hT : ok (takeList p.S s.loc.own x.shared (s.withCols [])) = true := by
            unfold takeList
            rw [hq]
            dsimp only
            rw [ht]
            dsimp only
            rw [hy]
            dsimp only
            rw [ok_cons, ok_cons, ok_append, ha]
            dsimp only
            rw [hm]
            dsimp only
            rw [ok_append, hd₁]
            simp only [Bool.and_eq_true]
            exact ⟨h6, h8, hA, hE, hJ⟩
          obtain ⟨r, hr⟩ := takeOver_of_list _ _ _ _ hT
          rw [hr] at h
          dsimp only at h
          unfold secondList
          rw [hx]
          dsimp only
          rw [ok_cons, ok_cons, ok_append, hr]
          dsimp only
          cases hd : linDotRow p.S x.g x.shared.psi r.1 (linLayOmega r.2.st.codes p.S) s.loc.w
              (linLayW r.2.st.codes p.S) with
          | none => rw [hd] at h; cases h
          | some dot =>
            rw [hd] at h
            dsimp only at h
            simp only [Bool.and_eq_true]
            refine ⟨h2, h3, hT, ?_⟩
            obtain ⟨hk, hu, hrn, hf⟩ := dot_bare _ _ _ _ _ _ _ _ hd
            obtain ⟨_, G, -, -, -, -, -, -, hrun, hG', -⟩ := takeOver_says _ _ _ _ r hr
            simp only [ok, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
            simp only [ok, rowL, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
            refine ⟨?_, ?_, ?_, h.1, ?_, ?_, ?_, h.2⟩
            · rw [hG']
              rfl
            · rw [hG']
              show (!G.inRun) = true
              rw [hrun]
              rfl
            · rw [hk]
              rfl
            · rw [hG', hu]
              simp [has]
            · rw [hG', hrn]
              simp [has]
            · rw [hG', hf]
              simp [has]

/-- **So the member's decide function returns.** -/
theorem second_owed {Cl : Type} (p : P₁₄) (s : S₃) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : ok (secondOwed p s) = true) :
    ∃ s', (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s rs gs = .ok s' :=
  second_yes p s rs gs (owed_list p s h)

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.owed_list
#print axioms ProofFile.Honest.K14.second_owed
#print axioms ProofFile.Honest.K14.adopted_at
#print axioms ProofFile.Honest.K14.elsewhere_ok
#print axioms ProofFile.Honest.K14.join_ok
#print axioms ProofFile.Honest.K14.dot_bare
