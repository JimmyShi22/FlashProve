-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/ChecksAtO.lean: **THE LAW's FORM BITES AT A NAMED STATEMENT WITH A GROUP.**
Statements and proofs, over the literals of Johnson/Desc/K12/Law/LitO.lean.

ChecksAt.lean shows: wherever the promise is met, the record fixes its data and N fails of them, a
verifier that says yes to all has not the law's form. That such a statement exists was its premise.
Here is one, for the second arm (`k12_lawRecFreeO`, FreeOff.lean) at N := `NTuple`:

  `tOx`: the record tO of the smaller stored proof's own-mask place, with the one open row of the
    group under test replaced by THE ROW THAT NOTHING CAN MEET: no summand, target 1 ("0 = 1").
  `says_bare`: a row without a summand and with target 1 says its claim of no words.
  `promise_Ox`: the whole promise holds at tOx (the record's count of roots; `FirstOpensOwn`;
    `PayRec`): these read places, sizes and shapes, no field element. By Lean's kernel on the
    literals.
  `not_ntuple_Ox`: `NTuple` is false at tOx, whatever the frame, the letters and the oracles.
  `yesAll_bites_Ox`: **so a piece that puts out at every transcript from (tOx, y), at errors below
    its rounds' numbers of challenges, has not the form of `k12_lawRecFreeO`'s law.**
Limits. Nothing on soundness: a check of a statement's form. tOx is no record that a verifier
reaches. The first arm's form is tried at no statement with a group. That the piece `pieceT` itself
refuses at tOx is not shown.

-/
import Johnson.Desc.K12.Coin.MemberProm
import Johnson.Desc.K12.Coin.ChecksAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Slice OnBytes.Means OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open H2K.First (gpOf Plain)
open H2K.Member (piO tO rO memberB member_of_B payRec_of)
open H2K.Pin (NTuple PayRec)

/-- The row that nothing can meet. -/
def rBare : OnBytes.Row := { target := oneE }

/-- The stored proof's record with the group's one open row replaced by it. -/
def tOx : T12 :=
  { tO with st := { tO.st with groups := tO.st.groups.modify tO.g fun G =>
      { G with rows := G.rows.setIfInBounds 0 rBare } } }

/-- A row without a summand and with target 1 says its claim of no words. -/
theorem says_bare {K : Type} [CommRing K] [Nontrivial K] (ρ : Model.Reading K) (S : Statement)
    (r : OnBytes.Row) (m : Words K) (h1 : r.terms = #[]) (h2 : r.units = #[]) (h3 : r.runs = #[])
    (h4 : r.forms = #[]) (h5 : r.target = oneE) : ¬ Says ρ S r m := by
  have hc : ∀ o part i, r.coefficient o part i = zeroE := by
    intro o part i
    unfold OnBytes.Row.coefficient
    rw [h1, h2, h3, h4]
    rfl
  intro h
  unfold Says value onTable at h
  simp only [hc, ρ.zero, zero_mul, Finset.sum_const_zero, add_zero, h5, ρ.one] at h
  exact zero_ne_one h

/-- Some row that the test takes in is bare. -/
def bareB (t : T12) : Bool :=
  match t.st.groups[t.g]? with
  | some G => (runRows t.st G).toList.any fun r =>
      r.terms.isEmpty && r.units.isEmpty && r.runs.isEmpty && r.forms.isEmpty &&
        decide (r.target = oneE)
  | none => false

theorem bareB_x : bareB tOx = true := by decide +kernel
theorem memberB_x : memberB piO rO tOx = true := by decide +kernel

/-- The plain data that a record fixes at piO. -/
def dAt (t : T12) : Option Plain :=
  match piO.nums.stages, t.st.groups[t.g]?, t.st.layout t.g with
  | a :: _, some G0, some Ly => gpOf piO { t with st := begun t.st t.g G0, pass := .nothing } a Ly
  | _, _, _ => none

theorem dAt_x :
    ((dAt tOx).map fun D => (D.ts, D.opens.map (·.2), D.mems.map (·.t), D.fresh.t)) =
      some ([1, 2, 5], [.own 1, .own 2, .own 5], [1, 2], 5) := by
  decide +kernel

theorem firstOpensOwn_Ox (t₁ t₂ : ℕ) :
    FirstOpensOwn piO (numAt t₁ t₂ 1) (fun z => t₁ + z) (t₁ + 5) tOx := by
  intro a rest G0 Ly D hf
  obtain ⟨f1, f2, f3, f4⟩ := hf
  have f5 : gpOf piO { tOx with st := begun tOx.st tOx.g G0, pass := .nothing } a Ly = some D :=
    f4 default
  have hD : dAt tOx = some D := by
    unfold dAt
    rw [f1, f2, f3]
    exact f5
  have h := dAt_x
  rw [hD] at h
  have h' := Option.some.inj h
  have e1 : D.ts = [1, 2, 5] := congrArg (·.1) h'
  have e2 : D.opens.map (·.2) = [.own 1, .own 2, .own 5] := congrArg (·.2.1) h'
  have e3 : D.mems.map (·.t) = [1, 2] := congrArg (·.2.2.1) h'
  have e4 : D.fresh.t = 5 := congrArg (·.2.2.2) h'
  refine ⟨?_, fun i => ?_, ?_⟩
  · have hm : D.opens.map (fun o => numAt t₁ t₂ 1 o.2) =
        (D.opens.map (·.2)).map (numAt t₁ t₂ 1) := by
      rw [List.map_map]
      rfl
    rw [hm, e2, e1]
    simp [numAt]
  · have hm : (D.mems.get i).t ∈ D.mems.map (·.t) :=
      List.mem_map.2 ⟨_, List.get_mem _ i, rfl⟩
    rw [e3] at hm
    show t₁ + (D.mems.get i).t < t₁ + 5
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    omega
  · show t₁ + D.fresh.t = t₁ + 5
    rw [e4]

/-- What the record fixes is there. -/
theorem fixes_Ox : ∃ a rest G0 Ly D, Fixes piO tOx a rest G0 Ly D :=
  (member_of_B piO rO tOx memberB_x).1

/-- **The whole promise holds at tOx.** -/
theorem promise_Ox (t₁ t₂ : ℕ) :
    tOx.roots = 5 ∧ (FirstOpensOwn piO (numAt t₁ t₂ 1) (fun z => t₁ + z) (t₁ + 5) tOx ∧
      PayRec piO tOx) :=
  ⟨rfl, firstOpensOwn_Ox t₁ t₂, payRec_of (member_of_B piO rO tOx memberB_x).2⟩

/-- **`NTuple` is false at tOx.** -/
theorem not_ntuple_Ox (F : Frame) (no : ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (y : F.E.Str)
    {a : Fmt.M1.Stage} {rest : List Fmt.M1.Stage} {G0 : Group} {Ly : GroupLayout} {D : Plain}
    (hF : Fixes piO tOx a rest G0 Ly D) : ¬ NTuple F piO no rad rd (tOx, y) a rest G0 Ly D := by
  rintro ⟨row₀, hok, hT⟩
  unfold H2K.Pin.TupleAt at hT
  obtain ⟨w, _, hall, _⟩ := hT
  have hb := bareB_x
  unfold bareB at hb
  rw [hF.2.1] at hb
  obtain ⟨r, hr, hq⟩ := List.any_eq_true.1 hb
  simp only [Bool.and_eq_true, Array.isEmpty_iff, decide_eq_true_eq] at hq
  obtain ⟨⟨⟨⟨q1, q2⟩, q3⟩, q4⟩, q5⟩ := hq
  exact says_bare _ _ r _ q1 q2 q3 q4 q5 (hall r hr)

/-- **The form of the second arm's law bites at (tOx, y).** -/
theorem yesAll_bites_Ox {W : Type} (F : Frame) (t₁ t₂ : ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ)
    (p : Piece (ckP .two) F T12 Unit W) (y : F.E.Str)
    (hyes : ∀ τ, ∃ b, p.ior.red.out (tOx, y) τ = some b) (hs : Small p.err) :
    ¬ p.ior.red.Leads
      (fun x => x.1.roots = 5 ∧
        (FirstOpensOwn piO (numAt t₁ t₂ 1) (fun z => t₁ + z) (t₁ + 5) x.1 ∧ PayRec piO x.1))
      (fun x _ => QN piO (NTuple F piO (fun z => t₁ + z) rad rd) x) p.err := by
  obtain ⟨a, rest, G0, Ly, D, hF⟩ := fixes_Ox
  exact yesAll_failsAt F piO _ _ p (tOx, y) (promise_Ox t₁ t₂) hF
    (not_ntuple_Ox F _ rad rd y hF) hyes hs

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.says_bare
#print axioms VerifiableInference.Desc.K12.Coin.promise_Ox
#print axioms VerifiableInference.Desc.K12.Coin.not_ntuple_Ox
#print axioms VerifiableInference.Desc.K12.Coin.yesAll_bites_Ox
