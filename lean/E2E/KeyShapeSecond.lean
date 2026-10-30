--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyShapeSecond.lean: "K14, SECOND PART", THE FIRST SUB-PROTOCOL OF THE KEY FILE's THIRD CHAIN,
CUT IN TWO: STRUCTURE | VALUES (the cut: Johnson/Desc/ProofFile/Honest/Thread/Shape.lean; the shape:
E2E/KeyShapeThird.lean). Its tests on the structure are written as one function `gSecond` of the
shape alone; ONE named test on values is left: "no coefficient on a pad". Definitions, statements
and proofs. NOTHING IS SHOWN OF ANY PROVER: no completeness.

The sub-protocol takes Omega over from the shared chain's end (the ground's functions for taking a
tree over, copying a sample, joining a group), makes the row (Dot) and adds it to the own group. On
shapes these four functions are Johnson/Desc/Ground/Shape/Ground.lean's. How many terms the row
has hangs on values: the shape holds no term and no row weight; that the row
can be made and that all its terms fit their places comes down to one mark on the row weights and
two tests on numbers (E2E/KeyDotFits.lean).

  (A table's index bits and "a summand fits its place" as functions of the shape: `tableBitsS`,
  `placeFitsS`, Johnson/Desc/Ground/Shape/More.lean.)
  `padB`: the ground's clause on values, as a test of statement, group and row. `dot_rest`: the five
    clauses on the row's summands, from the row's form, `TermsFit` and `padB`.
  **`gSecond`**: the sub-protocol on the shape. **`vSecond`**: its one named test on values.
  **`second_carries`**: (B1). **`second_returns`**: (B2).

Limits.
- `gSecond` asks more than the sub-protocol does: the mark of both statements' shapes; that each row
  weight is well-formed (a part of the mark on the weights). So it is sufficient, not necessary.
- THAT THE KEY FILE's ROW WEIGHTS HAVE THE MARK IS NOT SHOWN (E2E/KeyDotFits.lean's first limit).
- That `vSecond` passes is not shown here. It speaks of every member's pad. E2E/KeyPadClear.lean has
  it at Omega's copy, at the full size's shapes, at all well-formed row weights and all points; at a
  member whose pad lies in a mask table it holds by form (E2E/KeyDotRow.lean, `dot_noPad`); that the
  other members' pads lie there is a premise of both.


-/
import E2E.KeyShapeThird
import E2E.KeyDotFits
import Johnson.Desc.Ground.Shape.Marks
import Johnson.Desc.Ground.Shape.More
import OnBytes.Slice.BlkTensCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.AtFiles
open OnBytes OnBytes.Params Desc.Plain
open ProofFile.Honest (CarriesR ReturnsR)
open VerifiableInference.Desc.Ground.Sh
open VerifiableInference.Desc (named need)
open VerifiableInference.Desc.Ground
open VerifiableInference.Desc.Own (placeFits)
open VerifiableInference.Desc.Third (S₃ P₁₄ batchLinearConstraintsSecondPart takeOver plainArm firstStepB)
open VerifiableInference.Desc.Third.Law (ok_of_bind some_of_named true_of_need)

/-! ## The clauses on the row's summands -/

/-- The ground's clause on values, as a test of statement, group and row. -/
def padB (st : Statement) (g : Nat) (row : OnBytes.Row) : Bool :=
  has st.groups[g]? fun G => G.members.all fun o =>
    ((st.oracles[o]?).map (·.pad)).getD [] |>.all fun q =>
      VerifiableInference.Desc.Own.allZero (row.coefficient o q.1 q.2)

theorem dot_rest {st : Statement} {g : Nat} {G : OnBytes.Group} {row : OnBytes.Row}
    (hG : st.groups[g]? = some G) (hf : DotForm row) (ht : TermsFit st G row)
    (hp : padB st g row = true) : rowRestB st g row = true := by
  unfold rowRestB
  refine ok_of_all _ fun c hc => ?_
  unfold rowL at hc
  simp only [List.drop_succ_cons, List.drop_zero, List.mem_cons, List.not_mem_nil, or_false,
    hG] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
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
  · unfold padB at hp
    rw [hG] at hp
    exact hp

/-! ## The sub-protocol from its steps -/

/-- The taking-over returns where its nine steps do. -/
theorem takeOver_of_steps (S : LinShape) (own : Nat) (o : VerifiableInference.Desc.Third.SharedOut)
    (d : DState VerifiableInference.Desc.Third.Loc₃) (q : Nat × Nat) (T : Tree)
    (Y : OnBytes.Oracle) (X : Array Nat × DState VerifiableInference.Desc.Third.Loc₃) (mine : Nat)
    (d₁ d₂ : DState VerifiableInference.Desc.Third.Loc₃) (hq : o.book.place[o.omega]? = some q)
    (hT : o.book.trees[q.1]? = some T) (hal : (T.parts.size == 1) = true)
    (hY : o.st.oracles[o.omega]? = some Y) (hsh : decide (Y.shape = S.omega) = true)
    (h1 : adoptP d #[{ shape := Y.shape, leafClass := S.omegaLeafClass }] #[(T.number, T.src)] =
      some X) (hm : X.1[0]? = some mine) (h2 : elsewhereP X.2 mine o.st o.omega = some d₁)
    (h3 : joinP d₁ own mine false = some d₂) : takeOver S own o d = .ok (mine, d₂) := by
  unfold takeOver
  simp only [hq, hT, hY, named, need, hal, hsh, h1, hm, h2, h3, bind, Except.bind, pure,
    Except.pure, if_true]

/-! ## The sub-protocol on the shape -/

/-- The two places at which the row's terms lie fit; W's table's index bits are in range. -/
def dotFitsS (S : LinShape) (a : StSh) (own mine w : Nat) : Bool :=
  match a.groups[own]? with
  | some G =>
    placeFitsS a G mine .main (linLayOmega a.codes S).bits 0 &&
      placeFitsS a G w .main (linLayW a.codes S).bits 0 &&
      decide ((linLayW a.codes S).bits ≤ 63) && decide (S.kCol ≤ (linLayW a.codes S).bits)
  | none => false

/-- The row (Dot) can be made: on the shape. -/
def dotMadeS (S : LinShape) (x : BorderSh) : Bool := x.psi == S.kCol && x.weights

/-- **"K14, second part" on the shape.** -/
def gSecond (S : LinShape) (a : Sh₃) : Except String Sh₃ := do
  let x ← named "the two ends are at hand" a.2.border
  need "the marks of both statements" (a.2.tidy && x.tidy)
  need "the shape does not split the row (Dot)" (plainArm S)
  need "no root is received yet, and the first own tree's number counts just one tree more"
    (a.1.roots == 0 && a.1.book.trees.length + 1 == a.2.firstTree)
  let q ← named "Omega: it has a place in the shared chain's book" x.book.place[x.omega]?
  let t ← named "Omega: its tree is in the shared chain's book" x.book.trees[q.1]?
  need "Omega: it has a tree to itself" (t.parts.length == 1)
  let y ← named "Omega: it is in the shared chain's statement" x.st.oracles[x.omega]?
  need "Omega: it has the plan's shape" (decide (y.shape = S.omega))
  let r ← named "Omega: its tree comes in"
    (adoptS a.1 #[{ shape := y.shape, leafClass := S.omegaLeafClass }] [(t.number, t.src)])
  let mine ← named "Omega: its number here" r.1[0]?
  let a₁ ← named "Omega: it is sampled there, under the same shape and codes"
    (elsewhereS r.2 mine x.st x.omega)
  let a₂ ← named "Omega: it joins the own group" (joinS a₁ a.2.own mine false)
  need "the row (Dot) can be made" (dotMadeS S x)
  need "the row (Dot)'s two places fit" (dotFitsS S a₂.st a.2.own mine a.2.w)
  let a₃ ← named "the row (Dot) is laid" (addRowS a₂ a.2.own .plain)
  pure (a₃, { a.2 with border := none, omega := mine })

/-- **Its one named test on values**: no coefficient of the row (Dot) on a pad, at the statement
behind the taking-over. Where the taking-over or the making of the row does not return: true. -/
def vSecond (S : LinShape) (s : S₃) : Bool :=
  match s.loc.border with
  | none => true
  | some x =>
    match takeOver S s.loc.own x.shared (s.withCols []) with
    | .error _ => true
    | .ok a =>
      match linDotRow S x.g x.shared.psi a.1 (linLayOmega a.2.st.codes S) s.loc.w
          (linLayW a.2.st.codes S) with
      | none => true
      | some dot => padB a.2.st s.loc.own dot

/-- What the guards' return says of the state, step by step: the steps of the sub-protocol return,
and their shapes are the guards'. -/
theorem second_steps (S : LinShape) (s : S₃) (t : Sh₃) (hg : gSecond S (sh₃ S s) = .ok t) :
    ∃ x mine d₂ dot, s.loc.border = some x ∧ plainArm S = true ∧
      firstStepB s.roots s.loc.firstTree s.book = true ∧
      takeOver S s.loc.own x.shared (s.withCols []) = .ok (mine, d₂) ∧
      linDotRow S x.g x.shared.psi mine (linLayOmega d₂.st.codes S) s.loc.w
        (linLayW d₂.st.codes S) = some dot ∧ stTidyB s.st = true ∧ stTidyB d₂.st = true ∧
      d₂.st.codes = s.st.codes ∧
      dot.kind = .plain ∧
      (padB d₂.st s.loc.own dot = true → rowRestB d₂.st s.loc.own dot = true) ∧
      ∃ a₃, addRowS (shD d₂) s.loc.own .plain = some a₃ ∧
        t = (a₃, { locSh S s.st s.loc with border := none, omega := mine }) := by
  unfold gSecond at hg
  obtain ⟨x', hx, hg⟩ := ok_of_bind hg
  obtain ⟨_, hmk, hg⟩ := ok_of_bind hg
  obtain ⟨_, harm, hg⟩ := ok_of_bind hg
  obtain ⟨_, hfs, hg⟩ := ok_of_bind hg
  obtain ⟨q, hq, hg⟩ := ok_of_bind hg
  obtain ⟨t', ht, hg⟩ := ok_of_bind hg
  obtain ⟨_, hal, hg⟩ := ok_of_bind hg
  obtain ⟨y', hy, hg⟩ := ok_of_bind hg
  obtain ⟨_, hsh, hg⟩ := ok_of_bind hg
  obtain ⟨r, hr, hg⟩ := ok_of_bind hg
  obtain ⟨mine, hmine, hg⟩ := ok_of_bind hg
  obtain ⟨a₁, h1, hg⟩ := ok_of_bind hg
  obtain ⟨a₂, h2, hg⟩ := ok_of_bind hg
  obtain ⟨_, hmade, hg⟩ := ok_of_bind hg
  obtain ⟨_, hfit, hg⟩ := ok_of_bind hg
  obtain ⟨a₃, h3, hg⟩ := ok_of_bind hg
  have et := (Except.ok.inj hg).symm
  obtain ⟨x, hb, rfl⟩ := Option.map_eq_some_iff.1
    (show s.loc.border.map (borderSh S s.st.codes) = some x' from some_of_named hx)
  have hmk' := true_of_need hmk
  simp only [Bool.and_eq_true] at hmk'
  obtain ⟨m1, m3⟩ := hmk'
  have hq' : x.shared.book.place[x.shared.omega]? = some q :=
    (place_get _ _).symm.trans (some_of_named hq)
  obtain ⟨T, hT, rfl⟩ := Option.map_eq_some_iff.1
    ((tree_get x.shared.book q.1).symm.trans (some_of_named ht))
  obtain ⟨Y, hY, rfl⟩ := Option.map_eq_some_iff.1
    ((orc_get x.shared.st x.shared.omega).symm.trans (some_of_named hy))
  have hal' : (T.parts.size == 1) = true := by
    have := true_of_need hal
    rwa [show (treeSh T).parts.length = T.parts.size from Array.length_toList] at this
  have hr' : adoptS (shD (s.withCols [])) #[{ shape := Y.shape, leafClass := S.omegaLeafClass }]
      (givenSh #[(T.number, T.src)]) = some r := some_of_named hr
  obtain ⟨X, hX⟩ := adopt_returns _ _ _ _ hr'
  have cX := adopt_carries _ X.2 _ _ X.1 hX
  obtain rfl : (X.1, shD X.2) = r := Option.some.inj (cX.symm.trans hr')
  have hM1 := adopt_tidy _ X.2 _ _ X.1 hX m1
  have h1' : elsewhereS (shD X.2) mine (stSh x.shared.st) x.shared.omega = some a₁ :=
    some_of_named h1
  obtain ⟨d₁, hd1⟩ := elsewhere_returns _ _ _ _ _ h1'
  have c1 := elsewhere_carries _ _ _ _ _ hd1
  obtain rfl : shD d₁ = a₁ := Option.some.inj (c1.symm.trans h1')
  have hM2 := elsewhere_tidy _ _ _ _ _ hd1 hM1 m3
  have h2' : joinS (shD d₁) s.loc.own mine false = some a₂ := some_of_named h2
  obtain ⟨d₂, hd2⟩ := join_returns _ _ _ _ _ h2'
  have c2 := join_carries _ _ _ _ _ hd2
  obtain rfl : shD d₂ = a₂ := Option.some.inj (c2.symm.trans h2')
  have hM3 := join_tidy _ _ _ _ _ hd2 hM2
  have hmade' := true_of_need hmade
  unfold dotMadeS at hmade'
  simp only [Bool.and_eq_true, beq_iff_eq] at hmade'
  obtain ⟨p1, p2⟩ := hmade'
  have hcodes : d₂.st.codes = s.st.codes :=
    ((groundKeeps_grows.join _ _ _ _ _ hd2).1.trans
      (groundKeeps_grows.elsewhere _ _ _ _ _ hd1).1).trans (groundKeeps_grows.adopt _ _ _ _ _ hX).1
  have hw : weightsB S (linLayOmega d₂.st.codes S) x.g = true := by
    rw [hcodes]
    exact p2
  obtain ⟨dot, hdot⟩ := dot_returns S x.g x.shared.psi mine (linLayOmega d₂.st.codes S) s.loc.w
    (linLayW d₂.st.codes S) p1 hw
  have hfit' := true_of_need hfit
  unfold dotFitsS at hfit'
  have hgr : (shD d₂).st.groups[s.loc.own]? = (d₂.st.groups[s.loc.own]?).map grpSh :=
    grp_get d₂.st s.loc.own
  have hfit'' : (match (d₂.st.groups[s.loc.own]?).map grpSh with
    | some G =>
      placeFitsS (stSh d₂.st) G mine .main (linLayOmega d₂.st.codes S).bits 0 &&
        placeFitsS (stSh d₂.st) G s.loc.w .main (linLayW d₂.st.codes S).bits 0 &&
        decide ((linLayW d₂.st.codes S).bits ≤ 63) &&
        decide (S.kCol ≤ (linLayW d₂.st.codes S).bits)
    | none => false) = true := by
    rw [← hgr]
    exact hfit'
  cases hG : d₂.st.groups[s.loc.own]? with
  | none =>
    rw [hG] at hfit''
    cases hfit''
  | some G =>
    rw [hG] at hfit''
    simp only [Option.map_some, Bool.and_eq_true, decide_eq_true_eq, placeFitsS_eq] at hfit''
    obtain ⟨⟨⟨f1, f2⟩, f4⟩, f6⟩ := hfit''
    have hform := dot_form _ _ _ _ _ _ _ _ hdot
    have hterms := dot_terms_form S x.g x.shared.psi mine _ s.loc.w _ dot hdot hw f6 f4
    have hfs' : firstStepB s.roots s.loc.firstTree s.book = true := by
      have := true_of_need hfs
      unfold firstStepB
      rwa [show (sh₃ S s).1.book.trees.length = s.book.trees.size from tree_size s.book] at this
    exact ⟨x, mine, d₂, dot, hb, true_of_need harm, hfs',
      takeOver_of_steps S s.loc.own x.shared _ q T Y X mine d₁ d₂ hq' hT hal' hY
        (true_of_need hsh) hX (some_of_named hmine) hd1 hd2,
      hdot, m1, hM3, hcodes, hform.plain,
      fun hp => dot_rest hG hform (dot_termsFit hterms d₂.st G f1 f2) hp,
      a₃, some_of_named h3, et⟩

/-- **(B2)**: the guards return and the one test on values passes: the sub-protocol's decision
returns. -/
theorem second_returns {Cl : Type} (p : P₁₄) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    ReturnsR (sh₃ p.S) (fun s => (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s rs gs) (gSecond p.S)
      (vSecond p.S) := by
  intro s t hg hv
  obtain ⟨x, mine, d₂, dot, hb, ha, hf, hto, hdot, -, -, -, hk, hrest, a₃, h3, -⟩ :=
    second_steps p.S s t hg
  have hp : padB d₂.st s.loc.own dot = true := by
    unfold vSecond at hv
    simp only [hb, hto, hdot] at hv
    exact hv
  obtain ⟨b, hbb⟩ := addRow_returns d₂ s.loc.own dot a₃ (by rw [hk]; exact h3) (hrest hp)
  refine ⟨{ st := b.st, book := b.book, roots := b.roots
            loc := { s.loc with border := none, omega := mine } }, ?_⟩
  simp only [batchLinearConstraintsSecondPart, hb, ha, hf, hto, hdot, hbb, named, need, bind, Except.bind, pure,
    Except.pure, if_true]

/-- **(B1)**: where the sub-protocol's decision returns and the guards return, they return the shape
behind. -/
theorem second_carries {Cl : Type} (p : P₁₄) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    CarriesR (sh₃ p.S) (fun s => (batchLinearConstraintsSecondPart (Cl := Cl) p).decide s rs gs) (gSecond p.S) := by
  intro s s' t hf hg
  obtain ⟨x, mine, d₂, dot, hb, -, -, hto, hdot, hT, hM, hcd, hk, -, a₃, h3, rfl⟩ :=
    second_steps p.S s t hg
  obtain ⟨x', a, dot', b, hb', hto', hdot', hbb, rfl⟩ :=
    VerifiableInference.Desc.Third.Law.k14Second_inv p s s' rs gs hf
  obtain rfl : x = x' := Option.some.inj (hb.symm.trans hb')
  obtain rfl : (mine, d₂) = a := Except.ok.inj (hto.symm.trans hto')
  obtain rfl : dot = dot' := Option.some.inj (hdot.symm.trans hdot')
  have c := addRow_carries d₂ b s.loc.own dot hbb
  rw [hk] at c
  obtain rfl : shD b = a₃ := Option.some.inj (c.symm.trans h3)
  have hTb : stTidyB b.st = true := addRow_tidy d₂ b s.loc.own dot hbb hM
  show (shD b, (⟨stTidyB s.st, _, _, _, none, _, _⟩ : LocSh)) =
    (shD b, ⟨stTidyB b.st, _, _, _, none, _, _⟩)
  rw [hT, hTb]
  rfl

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.dot_rest
#print axioms AtPublicFiles.AtFiles.takeOver_of_steps
#print axioms AtPublicFiles.AtFiles.second_steps
#print axioms AtPublicFiles.AtFiles.second_returns
#print axioms AtPublicFiles.AtFiles.second_carries
