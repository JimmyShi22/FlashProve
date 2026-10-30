-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/DotPads.lean: kind K14: "K14, second part" (⟨3, none, 0, .K14⟩):
THE ROW (Dot) READS AS 0 ON EVERY PLACE OF A MEMBER's PAD, ALSO WHERE ITS WEIGHTS HAVE A WRITTEN-OUT
FACTOR, UNDER PREMISES ON WHERE THE PADS LIE AND ON THE WEIGHTS' FORM: so the test "addRow: ON
VALUES: no coefficient on a pad", the last of secondRest (Honest/K14/OmegaDoor.lean), at the
member's own state, where the taking-over and linDotRow return. Statements with their proofs; three
definitions, one with code.

  laid_cut_zeroG  **the summands of a cut, laid on a table, add up to 0 at the index of an entry
                  beyond the cut, WITH OR WITHOUT A WRITTEN-OUT FACTOR**: laid_cut_zero
                  (Johnson/Desc/K14/Honest/YesCut.lean) asks that there is none. Asked here: no
                  written-out variable is named twice, and each is one of the vector's variables. By
                  the library's tensorBelow_valG, tensorBelow_memG
                  (Johnson/Desc/K14/Law/TensorsDense.lean) and onTable_entryG (LayDense.lean)
  dot_inv         what linDotRow is made of, where it returns
  dot_coefficient the row's coefficient on an entry: the cut weights on Omega's table, and the
                  equality vector of the shared point, times -1, on W's
  cuts_zero       the cut weights, all of them, laid on a table, add up to 0 at the index of an
                  entry beyond the cut: by induction on the list
  WeightsFit g    the facts on the weights: each names no written-out variable twice, and names only
                  its own variables. weightsFitB: a test with code that gives them (weightsFit_of:
                  one way alone). weightsFit_of_ok: well-formed weights (the library's Tensor.ok)
                  have them: the library's dense_of_ok (LayDense.lean)
  dot_far         **the row reads as 0 behind the matrix's rows in Omega's table, behind the columns
                  in W's table, and on every other table**. (At an index beyond a main table's size
                  nothing is said)
  PadsBehind T o lay n each place of the message's pad in its main table lies inside the table and
                  holds an entry numbered at least n: the one field of Sits (YesCut.lean) that is
                  spent here. Where the statement T has no message number o it holds of itself and
                  says nothing
  dot_pads        so, under PadsBehind at Omega from the matrix's rows on and at W from 2 ^ kCol on:
                  THE TEST's BODY at every group G: for each member and each place of its pad the
                  coefficient's words are 0
  sizes_of_linOk  the two sizes that dot_far asks, from linOk: by the library's placedDot_of_seated
                  (Johnson/Desc/K14/Law/PlacedDot.lean), called at a statement of two messages
  rest24          **THE TEST's OWN Bool AT THE MEMBER's OWN STATE**: where takeOver returns a and
                  linDotRow returns dot at the member's own arguments, and under four more premises:
                  WeightsFit of the border's weights; linOk at the state's codes; PadsBehind at
                  Omega's copy from the matrix's rows on; PadsBehind at W from 2 ^ kCol on
  omega_padsBehind **OMEGA's HALF OF THE PREMISE**: PadsBehind at Omega's copy in the state that
                  takeOver returns, from: Omega's pad at the shared end lies where the plan's shape
                  gives (omegaPadB: Honest/K14/OmegaEnd.lean); both statements have one table of
                  codes; linOk. That Omega has the plan's shape there: takeOver's own test (the
                  library's takeOver_shape)

WHICH PREMISE READS A VALUE (all of this paragraph is by reading: no statement bears it). PadsBehind
and the two sizes read none. WeightsFit reads how many pairs a vector has and which of its variables
are written out: not the weights' scalars, their written-out values or what their pairs hold, nor
the shared point's coordinates. Tensor.ok, from which weightsFit_of_ok has it, reads beside that the
pairs of the written-out variables are (1, 1), how many values there are and where the vector's
stretch of them begins, and that it has at most 63 variables. That takeOver returns (ha of rest24)
tests sizes, shapes, marks, codes and members: by reading. THAT THE ROW CAN BE MADE (linDotRow
returns: the test "the row (Dot) can be made") DOES READ SOMETHING OF WHAT THE WEIGHTS' PAIRS HOLD:
the library's tensorBelow asks which halves of the pairs that are not written out are 0.

What is not claimed. PadsBehind at W: the first chain's end. WeightsFit at the pending row of any
run (from the book-keeping at the last chain's border 0: weights_of_form,
Honest/K14/OmegaJoin.lean). That the row can be made. The test "the terms fit their places" for
weights with a written-out factor (that test, under premises of its own: dot_terms_fit,
Honest/K14/DotTermsFit.lean). Nothing on any property of the protocol: nothing on completeness, on
soundness or on hiding.
-/
import Johnson.Desc.ProofFile.Honest.K14.OmegaDoor
import Johnson.Desc.K14.Law.LayDense
import Johnson.Desc.K14.Honest.YesFold
import Johnson.Desc.Means.Forth.YesWords
import Johnson.Desc.K14.Law.PlacedDot
import Johnson.Desc.Own.LinAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (Tensor VectorLay Row E addLaid linDotRow tensorBelow distinctNats negE oneE)
open OnBytes.Model (Reading)
open OnBytes.Slice (entryAt_lt index_entryAt)
open VerifiableInference.Desc (Own.allZero)
open VerifiableInference.Desc.Ground (has)
open VerifiableInference.Desc.Third (S₃ P₁₄ takeOver)
open VerifiableInference.Desc.Third.Law (takeOver_says takeOver_shape carries_takeOver)
open Desc.K14.Law (tensorBelow_valG tensorBelow_memG onTable_entryG dense_of_ok coefficient_addLaid
  coefficient_empty sum_map_zero)
open Desc.K14.Honest (vars_eq)

section reading
variable {K : Type} [Field K] (ρ : Reading K)

/-- **The summands of a cut, laid on a table, add up to 0 at the index of an entry beyond the cut,
with or without a written-out factor.** k: the entry's number. Asked: no written-out variable is
named twice (hdist); each is one of the vector's variables (hdv); the cut returns (hL); the vector's
variables are at most the table's bits (hn); k lies below the table's size (hk); hz: k lies beyond
the cut. -/
theorem laid_cut_zeroG (lay : VectorLay) (v : Tensor) (hdist : distinctNats v.denseVars = true)
    (hdv : ∀ d ∈ v.denseVars, d < v.vars) (start count len : Nat) (L : List Tensor)
    (hL : tensorBelow v start count len = some L) (hn : v.vars ≤ lay.bits) (k : Nat)
    (hk : k < 2 ^ lay.bits) (hz : k < 2 ^ v.vars → len ≤ k / 2 ^ start % 2 ^ count) :
    (L.map fun t => ρ.val ((lay.onTable t).entry (lay.index k))).sum = 0 := by
  have each : ∀ t ∈ L, ρ.val ((lay.onTable t).entry (lay.index k)) =
      if k < 2 ^ v.vars then ρ.val (t.entry k) else 0 := by
    intro t ht
    obtain ⟨h1, h2⟩ := tensorBelow_memG v start count len L hL t ht
    have h0 := onTable_entryG ρ lay t (by rw [h1, h2]; exact hdv) (by rw [h2]; exact hn) k hk
    rwa [h2] at h0
  rw [List.map_congr_left each]
  by_cases hk2 : k < 2 ^ v.vars
  · simp only [if_pos hk2]
    rw [tensorBelow_valG ρ v hdist start count len L hL k, if_neg (Nat.not_lt.2 (hz hk2))]
  · simp only [if_neg hk2]
    exact sum_map_zero L _ fun _ _ => rfl

/-- What linDotRow is made of, where it returns. -/
theorem dot_inv (S : OnBytes.Params.LinShape) (weights : List Tensor) (psi : List E) (omega : Nat)
    (omegaLay : VectorLay) (w : Nat) (wLay : VectorLay) (row : Row)
    (h : linDotRow S weights psi omega omegaLay w wLay = some row) :
    ∃ cut, psi.length = S.kCol ∧ (∀ g ∈ weights, g.vars = S.kRow) ∧
      (weights.mapM fun g => tensorBelow g 0 S.kRow S.matrixRows) = some cut ∧
      row = addLaid (addLaid {} omega omegaLay cut.flatten) w wLay [Tensor.eq psi (negE oneE)] := by
  unfold linDotRow at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨_, hg, cut, hc, hrow⟩ := h
  have hb : (psi.length == S.kCol && weights.all (·.vars == S.kRow)) = true := by
    by_contra hne
    simp [guard, hne] at hg
  rw [Bool.and_eq_true] at hb
  exact ⟨cut, eq_of_beq hb.1, fun g hg => eq_of_beq (List.all_eq_true.1 hb.2 g hg), hc, hrow.symm⟩

/-- The row's coefficient on an entry. -/
theorem dot_coefficient (omega : Nat) (omegaLay : VectorLay) (w : Nat) (wLay : VectorLay)
    (A : List Tensor) (psi : List E) (o : Nat) (pt : OnBytes.Part) (i : Nat) :
    ρ.val ((addLaid (addLaid {} omega omegaLay A) w wLay
      [Tensor.eq psi (negE oneE)]).coefficient o pt i) =
      (if omega = o ∧ OnBytes.Part.main = pt then
        (A.map fun t => ρ.val ((omegaLay.onTable t).entry i)).sum else 0) +
      (if w = o ∧ OnBytes.Part.main = pt then
        ρ.val ((wLay.onTable (Tensor.eq psi (negE oneE))).entry i) else 0) := by
  rw [coefficient_addLaid, coefficient_addLaid, coefficient_empty, zero_add]
  simp

/-- The cuts of a list of vectors, all laid on one table, add up to 0 at the index of an entry k
that is at least len. Asked: k lies below the table's size (hk); count is at most the table's bits
(hc); each vector has count variables and the two facts of WeightsFit; every cut returns. -/
theorem cuts_zero (lay : VectorLay) (count len : Nat) (k : Nat) (hk : k < 2 ^ lay.bits)
    (hc : count ≤ lay.bits) (hlen : len ≤ k) :
    ∀ (ws : List Tensor) (cut : List (List Tensor)),
      (∀ g ∈ ws, g.vars = count ∧ distinctNats g.denseVars = true ∧
        ∀ d ∈ g.denseVars, d < g.vars) →
      (ws.mapM fun g => tensorBelow g 0 count len) = some cut →
      (cut.flatten.map fun t => ρ.val ((lay.onTable t).entry (lay.index k))).sum = 0
  | [], cut, _, h => by
    obtain rfl : [] = cut := by simpa using h
    rfl
  | g :: ws, cut, hw, h => by
    rw [List.mapM_cons] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨L, hL, rest, hr, rfl⟩ := h
    obtain ⟨h1, h2, h3⟩ := hw g List.mem_cons_self
    rw [List.flatten_cons, List.map_append, List.sum_append,
      laid_cut_zeroG ρ lay g h2 h3 0 count len L hL (by rw [h1]; exact hc) k hk (by
        intro hlt
        rw [h1] at hlt
        rw [Nat.pow_zero, Nat.div_one, Nat.mod_eq_of_lt hlt]
        exact hlen),
      cuts_zero lay count len k hk hc hlen ws rest
        (fun x hx => hw x (List.mem_cons_of_mem _ hx)) hr, zero_add]

end reading

/-- **The facts on the weights**: each vector names no written-out variable twice, and each
written-out variable is one of its own variables. -/
def WeightsFit (g : List Tensor) : Prop :=
  ∀ v ∈ g, distinctNats v.denseVars = true ∧ ∀ d ∈ v.denseVars, d < v.vars

/-- A test with code that gives them. -/
def weightsFitB (g : List Tensor) : Bool :=
  g.all fun v => distinctNats v.denseVars && v.denseVars.all (· < v.vars)

/-- The test gives the facts. -/
theorem weightsFit_of {g : List Tensor} (h : weightsFitB g = true) : WeightsFit g := by
  intro v hv
  have := List.all_eq_true.1 h v hv
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at this
  exact this

/-- Well-formed weights (the library's Tensor.ok) have them: the library's dense_of_ok. -/
theorem weightsFit_of_ok {g : List Tensor} (h : ∀ v ∈ g, v.ok = true) : WeightsFit g :=
  fun v hv => ⟨(dense_of_ok v (h v hv)).2, (dense_of_ok v (h v hv)).1⟩

/-- Each place of the message's pad in its main table lies inside the table and holds an entry
numbered at least n. WHERE THE STATEMENT HAS NO MESSAGE NUMBER o IT HOLDS OF ITSELF AND SAYS
NOTHING. Of a place of the pad outside the main table nothing is said. -/
def PadsBehind (T : OnBytes.Statement) (o : Nat) (lay : VectorLay) (n : Nat) : Prop :=
  ∀ x, T.oracles[o]? = some x → ∀ q ∈ x.pad, q.1 = OnBytes.Part.main →
    q.2 < 2 ^ lay.bits ∧ n ≤ lay.entryAt q.2

section reading
variable {K : Type} [Field K] (ρ : Reading K)

/-- **The row (Dot) reads as 0 behind the matrix's rows in Omega's table, behind the columns in W's
table, and on every other table**: where linDotRow returns the row (h), under WeightsFit (hW), and
where kRow and kCol are at most the two tables' bits (hrO, hrW). In the two tables the index is
asked to lie below the table's size (hO, hV). -/
theorem dot_far (S : OnBytes.Params.LinShape) (weights : List Tensor) (psi : List E) (omega : Nat)
    (omegaLay : VectorLay) (w : Nat) (wLay : VectorLay) (row : Row)
    (h : linDotRow S weights psi omega omegaLay w wLay = some row) (hW : WeightsFit weights)
    (hrO : S.kRow ≤ omegaLay.bits) (hrW : S.kCol ≤ wLay.bits) (o : Nat) (pt : OnBytes.Part)
    (idx : Nat)
    (hO : omega = o → OnBytes.Part.main = pt →
      idx < 2 ^ omegaLay.bits ∧ S.matrixRows ≤ omegaLay.entryAt idx)
    (hV : w = o → OnBytes.Part.main = pt → idx < 2 ^ wLay.bits ∧ 2 ^ S.kCol ≤ wLay.entryAt idx) :
    ρ.val (row.coefficient o pt idx) = 0 := by
  obtain ⟨cut, hpsi, hv, hc, rfl⟩ := dot_inv S weights psi omega omegaLay w wLay row h
  rw [dot_coefficient]
  have z1 : (if omega = o ∧ OnBytes.Part.main = pt then
      (cut.flatten.map fun t => ρ.val ((omegaLay.onTable t).entry idx)).sum else 0) = 0 := by
    by_cases hh : omega = o ∧ OnBytes.Part.main = pt
    · rw [if_pos hh]
      obtain ⟨hi, hk⟩ := hO hh.1 hh.2
      have z := cuts_zero ρ omegaLay S.kRow S.matrixRows (omegaLay.entryAt idx)
        (entryAt_lt omegaLay idx hi) hrO hk weights cut
        (fun g hg => ⟨hv g hg, (hW g hg).1, (hW g hg).2⟩) hc
      rw [index_entryAt omegaLay idx hi] at z
      exact z
    · rw [if_neg hh]
  have z2 : (if w = o ∧ OnBytes.Part.main = pt then
      ρ.val ((wLay.onTable (Tensor.eq psi (negE oneE))).entry idx) else 0) = 0 := by
    by_cases hh : w = o ∧ OnBytes.Part.main = pt
    · rw [if_pos hh]
      obtain ⟨hi, hk⟩ := hV hh.1 hh.2
      have hv : (Tensor.eq psi (negE oneE)).vars = S.kCol := by rw [vars_eq, hpsi]
      have z := onTable_entryG ρ wLay (Tensor.eq psi (negE oneE)) (fun d hd => by cases hd)
        (by rw [hv]; exact hrW) (wLay.entryAt idx) (entryAt_lt wLay idx hi)
      rw [index_entryAt wLay idx hi, hv, if_neg (Nat.not_lt.2 hk)] at z
      exact z
    · rw [if_neg hh]
  rw [z1, z2, add_zero]

end reading

/-- **The test's body at every group G**: under PadsBehind at Omega from the matrix's rows on and at
W from 2 ^ kCol on. T: the statement at which the row is laid. -/
theorem dot_pads (S : OnBytes.Params.LinShape) (weights : List Tensor) (psi : List E) (omega : Nat)
    (omegaLay : VectorLay) (w : Nat) (wLay : VectorLay) (row : Row)
    (h : linDotRow S weights psi omega omegaLay w wLay = some row) (hW : WeightsFit weights)
    (hrO : S.kRow ≤ omegaLay.bits) (hrW : S.kCol ≤ wLay.bits) (T : OnBytes.Statement)
    (G : OnBytes.Group) (sO : PadsBehind T omega omegaLay S.matrixRows)
    (sW : PadsBehind T w wLay (2 ^ S.kCol)) :
    (G.members.all fun o =>
      ((T.oracles[o]?).map (·.pad)).getD [] |>.all fun q =>
        Own.allZero (row.coefficient o q.1 q.2)) = true := by
  rw [Array.all_eq_true_iff_forall_mem]
  intro o _
  cases hx : T.oracles[o]? with
  | none => rfl
  | some x =>
    show (x.pad.all fun q => Own.allZero (row.coefficient o q.1 q.2)) = true
    rw [List.all_eq_true]
    intro q hq
    refine OnBytes.Means.allZero_coefficient row o q.1 q.2
      (dot_far Reading.gl S weights psi omega omegaLay w wLay row h hW hrO hrW o q.1 q.2 ?_ ?_)
    · rintro rfl hm
      exact sO x hx q hq hm.symm
    · rintro rfl hm
      exact sW x hx q hq hm.symm

/-- The two sizes, from linOk: the library's placedDot_of_seated at a statement of two messages. -/
theorem sizes_of_linOk (codes : OnBytes.Codes) (S : OnBytes.Params.LinShape)
    (h : OnBytes.linOk codes S = true) :
    S.kRow ≤ (OnBytes.linLayOmega codes S).bits ∧ S.kCol ≤ (OnBytes.linLayW codes S).bits := by
  have P := Desc.K14.Law.placedDot_of_seated
    (T := { codes := codes, oracles := #[{ shape := S.omega }, { shape := S.w }], groups := #[] })
    (omega := 0) (w := 1) ⟨rfl, by decide, ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩⟩ h
  exact ⟨P.roomOmega, P.roomW⟩

/-- **The test's own Bool at the member's own state**, where takeOver returns a (ha) and linDotRow
returns dot at the member's own arguments (hd), under four more premises: WeightsFit of the border's
weights (hW); linOk at the state's codes (hlin); PadsBehind at Omega's copy from the matrix's rows
on (sO); PadsBehind at W from 2 ^ kCol on (sW). -/
theorem rest24 (p : P₁₄) (s : S₃) (x : VerifiableInference.Desc.Third.Border)
    (a : Nat × Desc.Plain.DState VerifiableInference.Desc.Third.Loc₃) (dot : Row)
    (ha : takeOver p.S s.loc.own x.shared (s.withCols []) = .ok a)
    (hd : linDotRow p.S x.g x.shared.psi a.1 (OnBytes.linLayOmega a.2.st.codes p.S) s.loc.w
      (OnBytes.linLayW a.2.st.codes p.S) = some dot)
    (hW : WeightsFit x.g) (hlin : OnBytes.linOk s.st.codes p.S = true)
    (sO : PadsBehind a.2.st a.1 (OnBytes.linLayOmega a.2.st.codes p.S) p.S.matrixRows)
    (sW : PadsBehind a.2.st s.loc.w (OnBytes.linLayW a.2.st.codes p.S) (2 ^ p.S.kCol)) :
    (has a.2.st.groups[s.loc.own]? fun G =>
      G.members.all fun o =>
        ((a.2.st.oracles[o]?).map (·.pad)).getD [] |>.all fun q =>
          Own.allZero (dot.coefficient o q.1 q.2)) = true := by
  have hc : a.2.st.codes = s.st.codes := (carries_takeOver _ _ _ _ a ha).1.1.codes
  obtain ⟨_, G, -, -, -, -, -, -, -, hG', -⟩ := takeOver_says _ _ _ _ a ha
  obtain ⟨z1, z2⟩ := sizes_of_linOk a.2.st.codes p.S (by rw [hc]; exact hlin)
  rw [hG']
  exact dot_pads p.S x.g x.shared.psi a.1 _ s.loc.w _ dot hd hW z1 z2 a.2.st _ sO sW

/-- **Omega's half of the premise.** y: Omega's entry at the shared end. -/
theorem omega_padsBehind (p : P₁₄) (s : S₃) (x : VerifiableInference.Desc.Third.Border)
    (a : Nat × Desc.Plain.DState VerifiableInference.Desc.Third.Loc₃)
    (ha : takeOver p.S s.loc.own x.shared (s.withCols []) = .ok a) (y : OnBytes.Oracle)
    (hy : x.shared.st.oracles[x.shared.omega]? = some y)
    (hpad : y.pad = ((OnBytes.Send.pad x.shared.st.codes p.S.omega).getD []).map fun q =>
      (q.part, q.index))
    (hcs : x.shared.st.codes = s.st.codes) (hlin : OnBytes.linOk s.st.codes p.S = true) :
    PadsBehind a.2.st a.1 (OnBytes.linLayOmega a.2.st.codes p.S) p.S.matrixRows := by
  have hc : a.2.st.codes = s.st.codes := (carries_takeOver _ _ _ _ a ha).1.1.codes
  obtain ⟨y', _, e1, hy', -, -, hx, -⟩ := takeOver_says _ _ _ _ a ha
  obtain rfl : y = y' := Option.some.inj (hy.symm.trans hy')
  obtain ⟨y₁, hy₁, hsh⟩ := takeOver_shape _ _ _ _ a ha
  obtain rfl : y = y₁ := Option.some.inj (hy.symm.trans hy₁)
  rw [← e1] at hx
  have M : Desc.K14.Honest.MsgIs a.2.st a.1 p.S.omega :=
    ⟨_, hx, hsh, rfl, by rw [hc, ← hcs]; exact hpad⟩
  have hf : VerifiableInference.Desc.Own.linFits a.2.st.codes p.S = true := by
    rw [VerifiableInference.Desc.Own.linFits_eq, hc]
    exact hlin
  exact (Desc.K14.Honest.sits_omega hf M { code := 0, maskCode := 0, members := #[a.1] }
    (by simp)).pad

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.laid_cut_zeroG
#print axioms ProofFile.Honest.K14.dot_inv
#print axioms ProofFile.Honest.K14.dot_coefficient
#print axioms ProofFile.Honest.K14.cuts_zero
#print axioms ProofFile.Honest.K14.weightsFit_of
#print axioms ProofFile.Honest.K14.weightsFit_of_ok
#print axioms ProofFile.Honest.K14.dot_far
#print axioms ProofFile.Honest.K14.dot_pads
#print axioms ProofFile.Honest.K14.sizes_of_linOk
#print axioms ProofFile.Honest.K14.rest24
#print axioms ProofFile.Honest.K14.omega_padsBehind
