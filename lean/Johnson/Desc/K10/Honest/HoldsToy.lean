-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K10/Honest/HoldsToy.lean: A MEMBER OF THE PREMISES OF THE VALUES' HALF of the closing of a
segment (`closeBase_holds`, Johnson/Desc/K10/Honest/Holds.lean; `close_plays`, Leaves.lean; beneath them
`close_holds`, `groupValue_kept`, Values.lean, and the shared fold's `fold_holds_kept`,
Johnson/Prover/Link/FoldKept.lean): so that these theorems are not empty, at a group WITH A KEPT MEMBER.

The record is that of the kind's first toy (its data: Johnson/Desc/K10/Honest/ToyData.lean): three
members, one kept; four open rows, with structured vectors, whose targets are true of the toy's tables. The
words are the members' tables, read in the field.

  `valueE`, `saysB`, `says_of`   a row applied to words of the program's elements, with code; where
                    that value is the row's target the row holds of the words read in the field
  `wordFor`, `read_wordFor`       an element of the program that is read as a given field element (the
                    library's `ofE`, OnBytes/Slice/Field.lean)
  `exists_shows`    for all round polynomials and every point there are rounds that show them
  `toy_says`        the toy's four rows hold of the toy's words, in the library's reading of a row
                    (`Row.coefficient`, `tableSize`): by `decide +kernel`. (The rows' targets are made
                    by the toy's own reckoning from the same tables.) With it the layout's two
                    logarithms of the message lengths, 3 and 3, and the number of rows, 4
  `HoldsMember`     ALL PREMISES OF `closeBase_holds`, at the toy's record, stage and words, and the
                    rounds' shape, as one proposition
  `toy_member`      IT HAS A MEMBER AT EVERY element x that "BAT" may draw, ALL coefficients W of the
                    hiding polynomial, EVERY drawn coefficient eps and EVERY point γ
  `toy_holds`, `toy_plays`   `closeBase_holds` and `close_plays`, each called at a member
  `toy_all`         `toy_member` and `toy_plays` joined
  `toy_kept`        at x = 3 the batched row has a separate form on the kept member, and its value on
                    the words, in the program's arithmetic, is not the word 0: by `decide +kernel`

Limits. THE ROUNDS AND THE DRAWS ARE MADE to show the honest round polynomials: no prover's text sends
them, no transcript draws them; that an honest prover's part of this kind, or `Fmt.M1.FoldOwn`, sends
just these words, or could in time, is not shown. φ is the library's packing of the letter W: it is tied
neither to the words at the fresh mask's oracle message (which are 0 here) nor to the toy's coins. The
record is written by hand: no pad, no ledger, no sampled member and so no sample row. That the kept
forms' value is not 0 IN THE FIELD is not shown (`toy_kept` is on words; at x = 0 it is 0). One size;
h = 0. Of the block's decision, not its step. Nothing on soundness, completeness or hiding of the
protocol.

-/
import Johnson.Desc.K10.Honest.Leaves
import Johnson.Desc.K10.Honest.BaseToys

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.Values
open OnBytes OnBytes.Means OnBytes.Slice Johnson.Prover.Link H2K.ClaimSays Cb
open VerifiableInference.Desc
open ProofFile.Honest.K10.YesFree (BaseData CloseBase closeBase_of Shaped ShapedAll)

/-! ## 1 A row applied to words of the program's elements -/

/-- The sum of f 0 .. f (n - 1), in the program's arithmetic. -/
def sumE (n : Nat) (f : Nat → E) : E := (List.range n).foldl (fun a i => addE a (f i)) zeroE

theorem read_sumE (f : Nat → E) : ∀ n, readE (sumE n f) = ∑ i ∈ Finset.range n, readE (f i)
  | 0 => rdE.zero
  | n + 1 => by
    have ih := read_sumE f n
    unfold sumE at ih ⊢
    rw [List.range_succ, List.foldl_append, Finset.sum_range_succ, ← ih]
    exact readE_add _ _

/-- A row applied to words of the program's elements. -/
def valueE (S : Statement) (r : Row) (w : Nat → OnBytes.Part → Nat → E) : E :=
  sumE S.oracles.size fun o =>
    addE (sumE (tableSize S o .main) fun i => mulE (r.coefficient o .main i) (w o .main i))
      (sumE (tableSize S o .mask) fun i => mulE (r.coefficient o .mask i) (w o .mask i))

theorem read_valueE (S : Statement) (r : Row) (w : Nat → OnBytes.Part → Nat → E) :
    readE (valueE S r w) = value rdE S r fun o p i => readE (w o p i) := by
  unfold valueE value onTable
  rw [read_sumE]
  refine Finset.sum_congr rfl fun o _ => ?_
  rw [readE_add, read_sumE, read_sumE]
  simp only [readE_mul]
  rfl

/-- The row's value on the words is its target. -/
def saysB (S : Statement) (r : Row) (w : Nat → OnBytes.Part → Nat → E) : Bool := valueE S r w == r.target

theorem says_of {S : Statement} {r : Row} {w : Nat → OnBytes.Part → Nat → E} (h : saysB S r w = true) :
    Says rdE S r fun o p i => readE (w o p i) := by
  unfold Says
  rw [← read_valueE]
  exact readE_of_beq _ _ h

/-! ## 2 Rounds that show given polynomials -/

/-- An element of the program that is read as x. -/
def wordFor (x : GE) : Fmt.Ext3 := ofE x

theorem read_wordFor (x : GE) : readE (E.ofTriple (wordFor x)) = x := by
  rw [readE_ofTriple]
  exact toE_ofE x

/-- For all round polynomials and every point there are rounds of the kind's shape that show them. -/
theorem exists_shows : ∀ (k : ℕ) (q : RIdx (sVars GE 2 k) → GE) (γ : HPt (sVars GE 2 k)),
    ∃ rs, Shows k rs q γ ∧ ∀ r ∈ rs, Shaped 2 r
  | 0, _, _ => ⟨[], trivial, fun _ h => (List.not_mem_nil h).elim⟩
  | k + 1, q, γ => by
    obtain ⟨rs, h, hs⟩ := exists_shows k (fun i => q (Sum.inr i)) γ.2
    refine ⟨⟨[.e (wordFor (q (Sum.inl (0 : Fin 3)))), .e (wordFor (q (Sum.inl (2 : Fin 3))))],
      ⟨[wordFor γ.1], [], [], none⟩⟩ :: rs, ⟨read_wordFor _, read_wordFor _, read_wordFor _, h⟩,
      fun r hr => ?_⟩
    rcases List.mem_cons.1 hr with rfl | c
    · exact ⟨⟨[_, _], rfl, rfl⟩, ⟨_, rfl⟩, rfl, rfl⟩
    · exact hs r c

/-! ## 3 The member -/

namespace Toy
open ProofFile.Honest.K10.Toy (P fr ask₀ coin₀ entryT)
open ProofFile.Honest.K10.Toy.Base (St₀ kept_member)

/-- The stage of the library with the toy's numbers: both codes have messages of eight entries; no
row variable of the mask rows; three of the main rows. -/
def st : Sg := ⟨⟨4, 8, 3⟩, ⟨4, 8, 3⟩, 0, 3, 1⟩

/-- The toy's words, read in the field. -/
def words : Words GE := fun o p i => readE (entryT ask₀ coin₀ o p i)

/-- The toy's record in front of the block. -/
def sT : First.Close.Rec := ⟨none, fr, St₀⟩

theorem sT_member : ProofFile.Honest.K10.YesFree.closeBaseB P sT = true := kept_member

/-- The toy's rows hold of the toy's words, and the group's numbers are the stage's: evaluated by
Lean's kernel at the group that the statement has. -/
theorem toy_says : (sT.st.groups[sT.frame.group]?).map (fun G =>
    ((runRows sT.st G).toList.all fun r => saysB sT.st r (entryT ask₀ coin₀),
      (Own.layoutOf sT.st G).logEll, (Own.layoutOf sT.st G).logEllZk, (runRows sT.st G).size)) =
    some (true, 3, 3, 4) := by decide +kernel

/-- The frame's record of the group has the stage's k and h. -/
theorem toy_group : (sT.frame.groups[sT.frame.link]?).map (fun G => (G.k, G.h)) = some (3, 0) := by
  decide +kernel

/-- **ALL PREMISES OF `closeBase_holds`, at the toy's record, stage and words**: the facts on the record; the
four numbers; the rows hold of the words; the batching at x returns row; the fresh table φ pairs with
W; "FOLD epsilon" shows the sum of W's polynomial over the cube and drew eps; the rounds "FOLD round"
show the honest round polynomials and drew γ; the rounds have the kind's shape. -/
structure HoldsMember (D : BaseData) (x : E) (W : HIdx (sVars GE 2 (st.h + st.g)) → GE) (eps : GE)
    (γ : HPt (sVars GE 2 (st.h + st.g))) (row : GroupRow) (rE : Fmt.RoundView) (rR : List Fmt.RoundView)
    (φ : st.cFr.J → GE) : Prop where
  base : CloseBase P sT D
  nk : D.Gq.k = st.h + st.g
  nh : D.Gq.h = st.h
  nl : 2 ^ (Own.layoutOf sT.st D.G).logEll = st.C.l
  nz : 2 ^ (Own.layoutOf sT.st D.G).logEllZk = st.Z.l
  hold : AllSay rdE sT.st (runRows sT.st D.G).toList words
  batch : Own.batch (D.S1 sT) sT.frame.group ⟨Own.layoutOf sT.st D.G, runRows sT.st D.G⟩ x = some row
  pairs : Pairs st st.Z.l W φ
  first : readE ((sentOf rE).getD 0 zeroE) = hMu (sVars GE 2 (st.h + st.g)) W
  drew : readE (drawnOf rE) = eps
  shows : Shows (st.h + st.g) rR (foldQK st (vecG st row)
    (msgOf st (Means.tablesOf (D.S1 sT) (Own.layoutOf sT.st D.G) words)) W (readE (drawnOf rE))
    (keptVal (keptLen (D.S1 sT))
      (Means.tablesOf (D.S1 sT) (Own.layoutOf sT.st D.G) words).kept row.kept) γ) γ
  shapeE : Shaped 1 rE
  shapeR : ∀ r ∈ rR, Shaped 2 r

/-- **THE PREMISES HAVE A MEMBER**, at every element x, all coefficients W, every eps and every point
γ. -/
theorem toy_member (x : E) (W : HIdx (sVars GE 2 (st.h + st.g)) → GE) (eps : GE)
    (γ : HPt (sVars GE 2 (st.h + st.g))) : ∃ D row rE rR φ, HoldsMember D x W eps γ row rE rR φ := by
  obtain ⟨D, H⟩ := closeBase_of sT_member
  have h1 := toy_says
  rw [H.there] at h1
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
  obtain ⟨a1, a2, a3, _⟩ := h1
  have h2 := toy_group
  rw [H.group] at h2
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
  have hsay : AllSay rdE sT.st (runRows sT.st D.G).toList words :=
    fun r hr => says_of (List.all_eq_true.1 a1 r hr)
  have nl : 2 ^ (Own.layoutOf sT.st D.G).logEll = st.C.l := by rw [a2]; rfl
  have nz : 2 ^ (Own.layoutOf sT.st D.G).logEllZk = st.Z.l := by rw [a3]; rfl
  obtain ⟨row, hrow, _⟩ := closeBase_holds H st h2.1 h2.2 nl nz words hsay x
  let rE : Fmt.RoundView :=
    ⟨[.e (wordFor (hMu (sVars GE 2 (st.h + st.g)) W))], ⟨[wordFor eps], [], [], none⟩⟩
  obtain ⟨rR, hR, hS⟩ := exists_shows (st.h + st.g) (foldQK st (vecG st row)
    (msgOf st (Means.tablesOf (D.S1 sT) (Own.layoutOf sT.st D.G) words)) W (readE (drawnOf rE))
    (keptVal (keptLen (D.S1 sT))
      (Means.tablesOf (D.S1 sT) (Own.layoutOf sT.st D.G) words).kept row.kept) γ) γ
  exact ⟨D, row, rE, rR, packed st (by decide) W, H, h2.1, h2.2, nl, nz, hsay, hrow,
    pairs_packed st (by decide) W, read_wordFor _, read_wordFor eps, hR,
    ⟨⟨[_], rfl, rfl⟩, ⟨_, rfl⟩, rfl, rfl⟩, hS⟩

/-- **`closeBase_holds`, CALLED AT A MEMBER**: the single rows that the fold returns are true. -/
theorem toy_holds {D : BaseData} {x : E} {W : HIdx (sVars GE 2 (st.h + st.g)) → GE} {eps : GE}
    {γ : HPt (sVars GE 2 (st.h + st.g))} {row : GroupRow} {rE : Fmt.RoundView} {rR : List Fmt.RoundView}
    {φ : st.cFr.J → GE} (M : HoldsMember D x W eps γ row rE rR φ) :
    ∑ j, vecS st (foldOutAt (D.S1 sT) (D.F sT) row D.m (rE :: rR)) j *
          foldMsg st (msgOf st (Means.tablesOf (D.S1 sT) (Own.layoutOf sT.st D.G) words)) φ
            (sPt 2 (st.h + st.g) γ) j +
        keptVal (keptLen (D.S1 sT))
          (Means.tablesOf (D.S1 sT) (Own.layoutOf sT.st D.G) words).kept
          (foldOutAt (D.S1 sT) (D.F sT) row D.m (rE :: rR)).kept =
      readE (foldOutAt (D.S1 sT) (D.F sT) row D.m (rE :: rR)).target := by
  obtain ⟨row', hrow', hall⟩ := closeBase_holds M.base st M.nk M.nh M.nl M.nz words M.hold x
  obtain rfl : row' = row := Option.some.inj (hrow'.symm.trans M.batch)
  exact hall rE rR φ W γ M.pairs M.first M.shows

/-- **`close_plays`, CALLED AT A MEMBER**: with a round "BAT" that drew t in front, THE BLOCK's DECISION
SAYS YES AND THE SINGLE ROWS THAT IT LAYS INTO THE FRAME ARE TRUE. -/
theorem toy_plays {D : BaseData} {t : Fmt.Ext3} {W : HIdx (sVars GE 2 (st.h + st.g)) → GE} {eps : GE}
    {γ : HPt (sVars GE 2 (st.h + st.g))} {row : GroupRow} {rE : Fmt.RoundView} {rR : List Fmt.RoundView}
    {φ : st.cFr.J → GE} (M : HoldsMember D (E.ofTriple t) W eps γ row rE rR φ) :
    ∃ s', ((First.Close.kind (Cl := Unit)) P).decide sT (⟨[], ⟨[t], [], [], none⟩⟩ :: rE :: rR) [] =
        .ok s' ∧
      ∑ j, vecS st s'.frame.rows j *
            foldMsg st (msgOf st (Means.tablesOf (D.S1 sT) (Own.layoutOf sT.st D.G) words)) φ
              (sPt 2 (st.h + st.g) γ) j +
          keptVal (keptLen (D.S1 sT))
            (Means.tablesOf (D.S1 sT) (Own.layoutOf sT.st D.G) words).kept s'.frame.rows.kept =
        readE s'.frame.rows.target := by
  have hlen : rR.length = 3 := (claimOf_shows _ rR _ γ zeroE M.shows).2.2
  exact close_plays (Cl := Unit) M.base st M.nk M.nh M.nl M.nz words M.hold
    ⟨[], ⟨[t], [], [], none⟩⟩ rE rR [] (by rw [List.length_cons, List.length_cons, hlen]; rfl)
    ⟨⟨⟨[], rfl, rfl⟩, ⟨t, rfl⟩, rfl, rfl⟩, M.shapeE, M.shapeR⟩ φ W γ M.pairs M.first
    (fun row' h' => by
      obtain rfl : row = row' := Option.some.inj (M.batch.symm.trans h')
      exact M.shows)

/-- **THE TWO JOINED**: at every element t that "BAT" may draw, all W, every eps and every point γ there
are rounds, with all premises beside, at which the block's decision says yes and the single rows that
it lays into the frame are true. -/
theorem toy_all (t : Fmt.Ext3) (W : HIdx (sVars GE 2 (st.h + st.g)) → GE) (eps : GE)
    (γ : HPt (sVars GE 2 (st.h + st.g))) :
    ∃ D row rE rR φ s', HoldsMember D (E.ofTriple t) W eps γ row rE rR φ ∧
      ((First.Close.kind (Cl := Unit)) P).decide sT (⟨[], ⟨[t], [], [], none⟩⟩ :: rE :: rR) [] =
        .ok s' ∧
      ∑ j, vecS st s'.frame.rows j *
            foldMsg st (msgOf st (Means.tablesOf (D.S1 sT) (Own.layoutOf sT.st D.G) words)) φ
              (sPt 2 (st.h + st.g) γ) j +
          keptVal (keptLen (D.S1 sT))
            (Means.tablesOf (D.S1 sT) (Own.layoutOf sT.st D.G) words).kept s'.frame.rows.kept =
        readE s'.frame.rows.target := by
  obtain ⟨D, row, rE, rR, φ, M⟩ := toy_member (E.ofTriple t) W eps γ
  obtain ⟨s', h1, h2⟩ := toy_plays M
  exact ⟨D, row, rE, rR, φ, s', M, h1, h2⟩

/-- THE KEPT FORMS ARE THERE: at the element 3 the batched row has one separate form, on the oracle
message number 3, and its value on the toy's words, reckoned in the program's arithmetic, is not the
word 0: evaluated by Lean's kernel. -/
theorem toy_kept : (sT.st.groups[sT.frame.group]?).bind (fun G =>
    (Own.batch (begun sT.st sT.frame.group G) sT.frame.group
      ⟨Own.layoutOf sT.st G, runRows sT.st G⟩ (ProofFile.Honest.K10.Toy.e 3)).map fun row =>
        (row.kept.toList.map (·.oracle), row.kept.toList.map fun f =>
          isZeroE (sumE 16 fun i => mulE (f.c.entry i) (entryT ask₀ coin₀ f.oracle .main i)))) =
    some ([3], [false]) := by decide +kernel

end Toy

end ProofFile.Honest.K10.Values

#print axioms ProofFile.Honest.K10.Values.says_of
#print axioms ProofFile.Honest.K10.Values.exists_shows
#print axioms ProofFile.Honest.K10.Values.Toy.toy_says
#print axioms ProofFile.Honest.K10.Values.Toy.toy_member
#print axioms ProofFile.Honest.K10.Values.Toy.toy_kept
#print axioms ProofFile.Honest.K10.Values.Toy.toy_holds
#print axioms ProofFile.Honest.K10.Values.Toy.toy_plays
#print axioms ProofFile.Honest.K10.Values.Toy.toy_all
