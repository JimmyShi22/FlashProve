--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyDotRow.lean: THE ROW (Dot) PASSES SIX OF THE EIGHT CLAUSES THAT THE GROUND ASKS OF A NEW
OPEN ROW, at the statement behind the taking-over of Omega (E2E/KeyTakeOver.lean). So the first
sub-protocol of the key file's third chain accepts under the clause on the row's terms and a premise
on the pads in place of the eight. Statements and proofs. One step of the verifier's: NOTHING IS
SHOWN OF ANY PROVER: no completeness, nothing on what a view shows.

The row (Dot) is made of terms alone, all on main tables, of two messages: Omega's copy and W. It
has no single entry, no run and no form.

What is shown.
  `addLaid_units`, `addLaid_runs`, `addLaid_forms`, `addLaid_terms`: adding placed tensors to a row
    turns its terms alone; each new term lies on the main table of the message that is named.
  `DotForm`, **`dot_form`**: so of every row that `linDotRow` returns: plain; no single entry, run
    or form; every term on a main table.
  `stTaken_group`: the own group behind the taking-over: the group in front with Omega's copy
    entered.
  `PadsClear st G row`: A NAMED PREMISE: every entry that masks a sample's answers, of every member
    of G, lies in a mask table, OR the row's coefficient on it is the element 0, as words.
  **`dot_noPad`**: under it the ground's one clause on values ("no coefficient on a pad") holds of
    the row: in the first arm BY FORM: by E2E/RowsFit.lean's `coefficient_zero` and `noPad_of_zero`.
  `TermsFit st G row`: THE ONE CLAUSE THAT IS LEFT, to the letter of the ground's list: every term's
    tensor is in order and fits its place.
  **`dot_rowL`**: all eight clauses, from `Taken`, `PadsClear` and `TermsFit`.
  **`k14Second_passes'`**: "K14, second part" accepts, with these two in place of the eight clauses.

Limits.
- `PadsClear`'s SECOND ARM IS A DEBT ON VALUES, AND IT IS THE ARM THAT OMEGA's COPY NEEDS. A member
  without mask rows has its pad in its main table, where a term of the row does add. At the
  library's written value of the full size's sized key (`Lk6.AtPlan.keyFull`), by an evaluation: W's
  shape and the index-mask message's have one mask row; OMEGA's HAS NONE (twelve main rows). That
  the row's coefficient is 0 on Omega's pad (the vector ends in front of the pad): at all row
  weights without a written-out factor and all points: E2E/KeyPadClear.lean.
- `TermsFit`, and that `linDotRow` returns, are not shown.
- A member of all the premises together, at the full size's shapes and codes, at one point:
  E2E/KeySecondMember.lean: there the kernel finds the coefficient on Omega's pad to be 0.


-/
import E2E.KeyTakeOver
import E2E.RowsFit
import Johnson.Desc.Third.Law.Sharp

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.AtFiles
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open VerifiableInference.Desc.Ground
open VerifiableInference.Desc.Third (S₃ Border P₁₄ batchLinearConstraintsSecondPart plainArm firstStepB)

/-! ## What the row is made of -/

theorem addLaid_units (o : Nat) (lay : VectorLay) : ∀ (l : List Tensor) (row : OnBytes.Row),
    (addLaid row o lay l).units = row.units
  | [], _ => rfl
  | t :: l, row => addLaid_units o lay l (row.add o .main (lay.onTable t))

theorem addLaid_runs (o : Nat) (lay : VectorLay) : ∀ (l : List Tensor) (row : OnBytes.Row),
    (addLaid row o lay l).runs = row.runs
  | [], _ => rfl
  | t :: l, row => addLaid_runs o lay l (row.add o .main (lay.onTable t))

theorem addLaid_forms (o : Nat) (lay : VectorLay) : ∀ (l : List Tensor) (row : OnBytes.Row),
    (addLaid row o lay l).forms = row.forms
  | [], _ => rfl
  | t :: l, row => addLaid_forms o lay l (row.add o .main (lay.onTable t))

/-- Each new term lies on a main table. -/
theorem addLaid_terms (o : Nat) (lay : VectorLay) : ∀ (l : List Tensor) (row : OnBytes.Row),
    (∀ t ∈ row.terms.toList, t.part = .main) →
    ∀ t ∈ (addLaid row o lay l).terms.toList, t.part = .main
  | [], _, h => h
  | a :: l, row, h => addLaid_terms o lay l (row.add o .main (lay.onTable a)) fun t ht => by
      have ht' : t ∈ (row.terms.push ⟨o, .main, lay.onTable a⟩).toList := ht
      rw [Array.toList_push] at ht'
      rcases List.mem_append.1 ht' with c | c
      · exact h t c
      · obtain rfl := List.mem_singleton.1 c
        rfl

/-- The form of the row (Dot). -/
structure DotForm (row : OnBytes.Row) : Prop where
  plain : row.kind = .plain
  terms : ∀ t ∈ row.terms.toList, t.part = .main
  units : row.units = #[]
  runs : row.runs = #[]
  forms : row.forms = #[]

/-- **Every row that `linDotRow` returns has it.** -/
theorem dot_form (S : LinShape) (weights : List Tensor) (psi : List E) (omega : Nat)
    (omegaLay : VectorLay) (w : Nat) (wLay : VectorLay) (row : OnBytes.Row)
    (h : linDotRow S weights psi omega omegaLay w wLay = some row) : DotForm row := by
  have hp := VerifiableInference.Desc.Third.Law.linDotRow_plain S weights psi omega omegaLay w wLay
    row h
  unfold linDotRow at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨_, _, cut, _, hrow⟩ := h
  refine ⟨hp, ?_, ?_, ?_, ?_⟩
  · rw [← hrow]
    exact addLaid_terms _ _ _ _ (addLaid_terms _ _ _ _ fun t ht => by cases ht)
  · rw [← hrow, addLaid_units, addLaid_units]
  · rw [← hrow, addLaid_runs, addLaid_runs]
  · rw [← hrow, addLaid_forms, addLaid_forms]

/-! ## The clauses -/

/-- The own group behind the taking-over. -/
def groupTaken (s : S₃) (G : OnBytes.Group) : OnBytes.Group :=
  { G with
    members := G.members.insertIdxIfInBounds (G.members.filter (· < s.st.oracles.size)).size
      s.st.oracles.size
    kept := G.kept.insertIdxIfInBounds (G.members.filter (· < s.st.oracles.size)).size false }

theorem stTaken_group (S : LinShape) (s : S₃) (y : OnBytes.Oracle) (G : OnBytes.Group)
    (hG : s.st.groups[s.loc.own]? = some G) :
    (stTaken S s y G).groups[s.loc.own]? = some (groupTaken s G) := by
  show (s.st.groups.modify s.loc.own _)[s.loc.own]? = _
  rw [Array.getElem?_modify, if_pos rfl, hG]
  rfl

/-- **A named premise**: every entry that masks a sample's answers, of every member of G, lies in a
mask table, or the row's coefficient on it is the element 0, as words. -/
def PadsClear (st : Statement) (G : OnBytes.Group) (row : OnBytes.Row) : Prop :=
  ∀ o ∈ G.members.toList, ∀ x : OnBytes.Oracle, st.oracles[o]? = some x → ∀ q ∈ x.pad,
    q.1 = .mask ∨ row.coefficient o q.1 q.2 = zeroE

/-- **The clause on values holds of such a row by form.** -/
theorem dot_noPad {st : Statement} {G : OnBytes.Group} {row : OnBytes.Row} (hf : DotForm row)
    (hp : PadsClear st G row) :
    (G.members.all fun o =>
      ((st.oracles[o]?).map (·.pad)).getD [] |>.all fun q =>
        VerifiableInference.Desc.Own.allZero (row.coefficient o q.1 q.2)) = true :=
  AtPublicFiles.RowsFit.noPad_of_zero fun o ho x hx q hq => by
    rcases hp o ho x hx q hq with e | e
    swap
    · exact e
    refine AtPublicFiles.RowsFit.coefficient_zero (fun t ht => ?_) (fun u hu => ?_) (fun w hw => ?_)
      fun f hff => ?_
    · rw [hf.terms t ht, e]
      exact Bool.and_false _
    · rw [hf.units] at hu
      cases hu
    · rw [hf.runs] at hw
      cases hw
    · rw [hf.forms] at hff
      cases hff

/-- **The one clause that is left**: every term's tensor is in order and fits its place. -/
def TermsFit (st : Statement) (G : OnBytes.Group) (row : OnBytes.Row) : Prop :=
  (row.terms.all fun t => VerifiableInference.Desc.Own.tensorInOrder t.v &&
    VerifiableInference.Desc.Own.placeFits st G t.oracle t.part t.v.vars 0) = true

/-- **All eight clauses.** -/
theorem dot_rowL {S : LinShape} {s : S₃} {y : OnBytes.Oracle} {G : OnBytes.Group}
    {row : OnBytes.Row} (hG : s.st.groups[s.loc.own]? = some G) (hfresh : G.inRun = false)
    (hf : DotForm row) (hp : PadsClear (stTaken S s y G) (groupTaken s G) row)
    (ht : TermsFit (stTaken S s y G) (groupTaken s G) row) :
    ok (rowL (stTaken S s y G) s.loc.own row) = true := by
  refine ok_of_all _ fun c hc => ?_
  unfold rowL at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false, stTaken_group S s y G hG] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  · show (!(groupTaken s G).inRun) = true
    show (!G.inRun) = true
    rw [hfresh]
    rfl
  · show (row.kind != .sample) = true
    rw [hf.plain]
    rfl
  · exact ht
  · show (row.units.all _) = true
    rw [hf.units]
    exact Array.all_eq_true_iff_forall_mem.2 fun _ hm => absurd hm (Array.not_mem_empty _)
  · show (row.runs.all _) = true
    rw [hf.runs]
    exact Array.all_eq_true_iff_forall_mem.2 fun _ hm => absurd hm (Array.not_mem_empty _)
  · show (row.forms.all _) = true
    rw [hf.forms]
    exact Array.all_eq_true_iff_forall_mem.2 fun _ hm => absurd hm (Array.not_mem_empty _)
  · exact dot_noPad hf hp

/-- **"K14, second part" accepts**, with one clause on the row's terms and the premise on the pads
in place of the eight clauses. -/
theorem k14Second_passes' {Cl : Type} (p : P₁₄) (s : S₃) (x : Border) (q : Nat × Nat) (t : Tree)
    (y : OnBytes.Oracle) (G : OnBytes.Group) (lay : TreeLay) (dot : OnBytes.Row)
    (hb : s.loc.border = some x) (ha : plainArm p.S = true)
    (hf : firstStepB s.roots s.loc.firstTree s.book = true)
    (h : Taken p.S s x.shared q t y G lay) (hL : Listed s.st)
    (hd : linDotRow p.S x.g x.shared.psi s.st.oracles.size
      (linLayOmega (stTaken p.S s y G).codes p.S) s.loc.w
      (linLayW (stTaken p.S s y G).codes p.S) = some dot)
    (hp : PadsClear (stTaken p.S s y G) (groupTaken s G) dot)
    (ht : TermsFit (stTaken p.S s y G) (groupTaken s G) dot) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    ∃ s', (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s rs gs = .ok s' ∧
      s'.st = withRow (stTaken p.S s y G) s.loc.own dot ∧ s'.roots = s.roots ∧
      s'.loc = { s.loc with border := none, omega := s.st.oracles.size } :=
  k14Second_passes p s x q t y G lay dot hb ha hf h hL hd
    (dot_rowL h.group h.fresh (dot_form _ _ _ _ _ _ _ _ hd) hp ht) rs gs

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.addLaid_units
#print axioms AtPublicFiles.AtFiles.addLaid_runs
#print axioms AtPublicFiles.AtFiles.addLaid_forms
#print axioms AtPublicFiles.AtFiles.addLaid_terms
#print axioms AtPublicFiles.AtFiles.dot_form
#print axioms AtPublicFiles.AtFiles.stTaken_group
#print axioms AtPublicFiles.AtFiles.dot_noPad
#print axioms AtPublicFiles.AtFiles.dot_rowL
#print axioms AtPublicFiles.AtFiles.k14Second_passes'
