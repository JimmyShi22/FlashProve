-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/NamesOnly.lean: CONDITIONAL: WHICH ARRAYS THE CLAIMS OF AN ATTENTION
SEGMENT's OWN ROUNDS NAME: a claim of the runs "first" and "second" has no run of entries, and every
entry of its form lies in one array, the array of the reads (number `iU3` of the plan); the run
"keys" states no claim; the key forms that are handed to the lookup's run "join", and the forms of
the two readers that are handed to its run "planes", name entries of that array alone. So none of
them names an entry or a run of the array of the smallness test's digits, or of a matrix's array of
symbols. On the verifier's own runs; no prover in it. IT IMPORTS FILES OF THE LIBRARY ALONE.

Why. A law that computes a weight of the ledger behind the batching as a sum over all gathered
claims wants to know which claims bear on which array.

How. NEARLY ALL OF IT IS THE LIBRARY's, CALLED. Which entries the forms name: `Cov`,
`first_cov_K05`, `second_cov_K05` (Johnson/Desc/First/Att/Claims/Covered.lean, CoveredApart.lean),
`keysRun_covered` (CoveredKeys.lean), their two premises at what a state holds: `cov_parts`
(HeardPlain.lean); with the array's width also the row and the place: `first_named`, `second_named`
(the same file), and from one public test on the state `plain_named_first`, `plain_named_second`
(Johnson/Desc/First/Att/Door/Law/PlainThereTie.lean); the readers: `readers_rowsIn`
(Johnson/Desc/First/Att/K05PlanesEnts.lean), over `readers_rows` (K05ReadersRows.lean beside it).
That a claim of the three runs is a bare form: `runOfForms_hands` (Claims/RunsHand.lean). That the
array of the reads is another than the digits' and the symbols': `ApartAt`
(Johnson/Desc/First/Link/Law/OkJoin.lean). The road from a run's yes to the forms is that of
`first_state` (Johnson/Desc/K5/Honest/Law/LiveState.lean, which is not imported).

Main names:
  `NamesOnly` t cl: the claim has no run, and every entry of its form lies in array t.
  `off_of_only`, `off_apart`: such a claim names nothing of another array; so under `ApartAt`.
  `firstAt_tree`, `secondAt_tree`: the forms, at what was heard and a ledger.
  `first_forms`, `second_forms`: what a yes of the two runs is made of.
  `first_namesOnly`, `second_namesOnly`, `keys_none`: **the three runs at a state.**
  `first_row0`, `second_row0`: with the array's width: row 0, below the tables' length.
  `keys_tree`, `readers_tree`: **the key forms; the two readers' forms.**
  `first_off`, `second_off`: **the two runs name nothing of the digits' array or a matrix's.**

Limits. Two premises on the state. hp (`HeardPlain`): the start form of each sumcheck that the state
holds as heard names no entry; a `Heard` that no hearing has made could start at a form that names
any array (the library's control `heardPlain_bites`). ha (`ApartAt`) at the structure of the
smallness test. Who pays the two under the library's head on the public input:
Johnson/Desc/K5/Honest/Law/NamesReads.lean. Of the one claim of "join" and the claims of "planes"
the key forms' and the readers' share alone is spoken of: what else these runs' texts lay into a
claim is the lookup's (the library's `cov_joinW`; all claims of "planes" at these readers:
`hents_of_run`; "first", "second" and the one claim of "join" together: `ents_of_returns`,
Johnson/Desc/First/Att/K05EntsOf.lean). The runs are the kind's own at its seat on the first chain's
state (`runFirst`, `runKeys`, `runSecond`, Johnson/Desc/First/Att/Claims/K5Still.lean); that an
entry of a link's order is such a run is not drawn here.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Att.Claims.HeardPlain
import Johnson.Desc.First.Att.Claims.CoveredKeys
import Johnson.Desc.First.Att.Claims.K5Still
import Johnson.Desc.First.Att.K05PlanesEnts
import Johnson.Desc.First.Link.Law.OkJoin
import Johnson.Desc.FoldKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes (E)
open OnBytes.Model (Aff Fork HTree HTailF2)
open VerifiableInference.Desc (Claim First.S First.AttOwn named)
open VerifiableInference.Desc.First.Att.P (ParC parCOf Heard keysOfO keysOfK readersOfO U3At
  plannedK readers_rowsIn)
open VerifiableInference.Desc.LinkJoin (ApartAt)
open K5Law (inAt firstAt secondAt inOf_isAt firstK_isAt secondK_isAt runFirst runKeys runSecond
  rFirst_mem rKeys_mem rSecond_mem runOfForms_hands HeardPlain cov_parts first_cov_K05
  second_cov_K05 keysRun_covered first_named second_named)

/-- **All that the claim names of arrays lies in array t**: it has no run of entries, and every
entry of its form lies in array t. -/
def NamesOnly (t : ℕ) (cl : Claim) : Prop := cl.runs = #[] ∧ ∀ x ∈ cl.form.ents.toList, x.tree = t

/-- Such a claim names no entry and no run of another array. -/
theorem off_of_only {t t' : ℕ} {cl : Claim} (h : NamesOnly t cl) (hne : t' ≠ t) :
    (∀ x ∈ cl.form.ents, x.tree ≠ t') ∧ ∀ u ∈ cl.runs, u.tree ≠ t' := by
  refine ⟨fun x hx e => hne (e.symm.trans (h.2 x (Array.mem_toList_iff.2 hx))), fun u hu => ?_⟩
  rw [h.1] at hu
  exact absurd hu (Array.not_mem_empty u)

/-- **So it names nothing of the digits' array, nor of a matrix's array of symbols.** Conditional:
h; ha: array t is another than these, at the structure tl. -/
theorem off_apart {tl : HTailF2} {t : ℕ} {cl : Claim} (h : NamesOnly t cl) (ha : ApartAt tl t) :
    ((∀ x ∈ cl.form.ents, x.tree ≠ tl.ix.ZZ) ∧ ∀ u ∈ cl.runs, u.tree ≠ tl.ix.ZZ) ∧
      ∀ mu, mu < tl.NM → (∀ x ∈ cl.form.ents, x.tree ≠ tl.gtTree.getD mu 0) ∧
        ∀ u ∈ cl.runs, u.tree ≠ tl.gtTree.getD mu 0 := by
  obtain ⟨_, _, _, hZ, _, hG, _⟩ := ha
  exact ⟨off_of_only h hZ, fun mu hmu => off_of_only h (hG mu hmu)⟩

section At
variable {c : ParC} {g : OnBytes.Model.Forest.Heard} {h : Heard} {U : Fork} {l : List Aff}

/-- The forms of "first", at what was heard and a ledger. It is the library's `first_named` without
the array's width, and so without the row and the place. Conditional: e: they are made; hc. -/
theorem firstAt_tree (e : firstAt c g h U = some l) (hc : HeardPlain h) :
    ∀ f ∈ l, ∀ x ∈ f.ents.toList, x.tree = c.iU3 := by
  unfold firstAt at e
  obtain ⟨y, hy, e1⟩ := Option.bind_eq_some_iff.1 e
  obtain ⟨z, hz, rfl⟩ := Option.map_eq_some_iff.1 e1
  have eu := (K5Law.inAt_parts hy).2.1
  obtain ⟨hL, hR⟩ := cov_parts hy hc
  intro f hf x hx
  obtain ⟨_, _, et, _⟩ := first_cov_K05 hL hR (j := z.2) hz f hf x hx
  exact et.trans eu

/-- The forms of "second", likewise. -/
theorem secondAt_tree (e : secondAt c g h U = some l) (hc : HeardPlain h) :
    ∀ f ∈ l, ∀ x ∈ f.ents.toList, x.tree = c.iU3 := by
  unfold secondAt at e
  obtain ⟨y, hy, e1⟩ := Option.bind_eq_some_iff.1 e
  have eu := (K5Law.inAt_parts hy).2.1
  obtain ⟨hL, hR⟩ := cov_parts hy hc
  intro f hf x hx
  obtain ⟨_, _, et, _⟩ := second_cov_K05 hL hR e1 f hf x hx
  exact et.trans eu

end At

section State
variable (A : OnBytes.Attention.Plan)

/-- What a yes of "first" is made of, at a state that holds hd as heard. -/
theorem first_forms {m : ℕ} {u : First.S} {z : List Claim × First.S} {hd : Heard}
    (h5 : u.heard5? = some hd) (hr : runFirst (parCOf A) m u = .ok z) :
    ∃ (a : First.AttOwn) (g : OnBytes.Model.Forest.Heard) (l : List Aff), u.here = .att a ∧
      firstAt (parCOf A) g hd a.F = some l ∧ z.1 = l.map fun f => ({ form := f } : Claim) := by
  obtain ⟨_, l, hl, e2⟩ := runOfForms_hands _ (parCOf A) _ (rFirst_mem (parCOf A)) m u z.1 z.2 hr
  have hk := VerifiableInference.Desc.Keeps.named_ok (show named "K5.first" _ = .ok (l, u) from hl)
  cases he : u.here with
  | att a =>
    rw [firstK_isAt he] at hk
    have h5' : a.heard5 = some hd := by
      unfold First.S.heard5? at h5
      rw [he] at h5
      exact h5
    obtain ⟨l', hl', e3⟩ := Option.map_eq_some_iff.1 hk
    obtain rfl : l' = l := (Prod.mk.inj e3).1
    obtain ⟨g, _, hl'⟩ := Option.bind_eq_some_iff.1 hl'
    rw [h5'] at hl'
    exact ⟨a, g, l', rfl, hl', e2⟩
  | _ =>
    unfold First.S.heard5? at h5
    rw [he] at h5
    exact nomatch h5

/-- What a yes of "second" is made of, likewise. -/
theorem second_forms {m : ℕ} {u : First.S} {z : List Claim × First.S} {hd : Heard}
    (h5 : u.heard5? = some hd) (hr : runSecond (parCOf A) m u = .ok z) :
    ∃ (a : First.AttOwn) (g : OnBytes.Model.Forest.Heard) (l : List Aff), u.here = .att a ∧
      secondAt (parCOf A) g hd a.F = some l ∧ z.1 = l.map fun f => ({ form := f } : Claim) := by
  obtain ⟨_, l, hl, e2⟩ := runOfForms_hands _ (parCOf A) _ (rSecond_mem (parCOf A)) m u z.1 z.2 hr
  have hk := VerifiableInference.Desc.Keeps.named_ok (show named "K5.second" _ = .ok (l, u) from hl)
  cases he : u.here with
  | att a =>
    rw [secondK_isAt he] at hk
    have h5' : a.heard5 = some hd := by
      unfold First.S.heard5? at h5
      rw [he] at h5
      exact h5
    obtain ⟨l', hl', e3⟩ := Option.map_eq_some_iff.1 hk
    obtain rfl : l' = l := (Prod.mk.inj e3).1
    obtain ⟨g, _, hl'⟩ := Option.bind_eq_some_iff.1 hl'
    rw [h5'] at hl'
    exact ⟨a, g, l', rfl, hl', e2⟩
  | _ =>
    unfold First.S.heard5? at h5
    rw [he] at h5
    exact nomatch h5

/-- **THE RUN "first" AT A STATE: EACH CLAIM HAS NO RUN, AND EVERY ENTRY OF ITS FORM LIES IN THE
ARRAY OF THE READS.** Conditional: h5, hp: what the state holds as heard starts at forms without
entries; hr: the run's yes. -/
theorem first_namesOnly {m : ℕ} {u : First.S} {z : List Claim × First.S} {hd : Heard}
    (h5 : u.heard5? = some hd) (hp : HeardPlain hd) (hr : runFirst (parCOf A) m u = .ok z) :
    ∀ cl ∈ z.1, NamesOnly A.iU3 cl := by
  obtain ⟨a, g, l, _, hl, e⟩ := first_forms A h5 hr
  rw [e]
  intro cl hcl
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hcl
  exact ⟨rfl, firstAt_tree hl hp f hf⟩

/-- **THE RUN "second" AT A STATE**, likewise. -/
theorem second_namesOnly {m : ℕ} {u : First.S} {z : List Claim × First.S} {hd : Heard}
    (h5 : u.heard5? = some hd) (hp : HeardPlain hd) (hr : runSecond (parCOf A) m u = .ok z) :
    ∀ cl ∈ z.1, NamesOnly A.iU3 cl := by
  obtain ⟨a, g, l, _, hl, e⟩ := second_forms A h5 hr
  rw [e]
  intro cl hcl
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hcl
  exact ⟨rfl, secondAt_tree hl hp f hf⟩

/-- **THE RUN "keys" STATES NO CLAIM.** It is the first clause of `keys_state` (LiveState.lean),
without that law's premise on the state. Conditional: the run's yes. -/
theorem keys_none {m : ℕ} {u : First.S} {z : List Claim × First.S}
    (hr : runKeys (parCOf A) m u = .ok z) : z.1 = [] := by
  obtain ⟨_, l, hl, e2⟩ := runOfForms_hands _ (parCOf A) _ (rKeys_mem (parCOf A)) m u z.1 z.2 hr
  have hk := VerifiableInference.Desc.Keeps.named_ok (show named "K5.keys" _ = .ok (l, u) from hl)
  unfold VerifiableInference.Desc.First.Att.P.keysK at hk
  obtain ⟨_, _, e3⟩ := Option.map_eq_some_iff.1 hk
  obtain rfl : [] = l := (Prod.mk.inj e3).1
  rw [e2]
  rfl

/-- With the array's width: row 0, and a place below the tables' length: the library's
`first_named` at the run. Conditional: as `first_namesOnly`; he: the open segment; hT, hW: its
ledger has the array, with at least as many columns as the tables have entries. -/
theorem first_row0 {m : ℕ} {u : First.S} {z : List Claim × First.S} {hd : Heard}
    (h5 : u.heard5? = some hd) (hp : HeardPlain hd) (hr : runFirst (parCOf A) m u = .ok z)
    {a : First.AttOwn} (he : u.here = .att a) {T : HTree} (hT : a.F.trees[A.iU3]? = some T)
    (hW : A.nW ≤ T.K) :
    ∀ cl ∈ z.1, ∀ x ∈ cl.form.ents.toList, x.tree = A.iU3 ∧ x.row = 0 ∧ x.idx < A.nW := by
  obtain ⟨a', g, l, he', hl, e⟩ := first_forms A h5 hr
  obtain rfl : a = a' := by
    rw [he] at he'
    cases he'
    rfl
  rw [e]
  intro cl hcl
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hcl
  exact first_named hl hp hT hW f hf

/-- The like of "second". -/
theorem second_row0 {m : ℕ} {u : First.S} {z : List Claim × First.S} {hd : Heard}
    (h5 : u.heard5? = some hd) (hp : HeardPlain hd) (hr : runSecond (parCOf A) m u = .ok z)
    {a : First.AttOwn} (he : u.here = .att a) {T : HTree} (hT : a.F.trees[A.iU3]? = some T)
    (hW : A.nW ≤ T.K) :
    ∀ cl ∈ z.1, ∀ x ∈ cl.form.ents.toList, x.tree = A.iU3 ∧ x.row = 0 ∧ x.idx < A.nW := by
  obtain ⟨a', g, l, he', hl, e⟩ := second_forms A h5 hr
  obtain rfl : a = a' := by
    rw [he] at he'
    cases he'
    rfl
  rw [e]
  intro cl hcl
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hcl
  exact second_named hl hp hT hW f hf

/-- **THE KEY FORMS THAT ARE HANDED TO THE LOOKUP's RUN "join" NAME ENTRIES OF THE ARRAY OF THE
READS ALONE.** Conditional: h5, hp; hk: the function of the key forms returns. -/
theorem keys_tree {u : First.S} {KF : Array Aff} {hd : Heard} (h5 : u.heard5? = some hd)
    (hp : HeardPlain hd) (hk : keysOfO A u = some KF) :
    ∀ f ∈ KF.toList, ∀ x ∈ f.ents.toList, x.tree = A.iU3 := by
  unfold keysOfO keysOfK at hk
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hk
  obtain ⟨⟨i, K⟩, hin, pad, _, w, hw, hkr⟩ := hk
  cases he : u.here with
  | att a =>
    rw [inOf_isAt he] at hin
    have h5' : a.heard5 = some hd := by
      unfold First.S.heard5? at h5
      rw [he] at h5
      exact h5
    obtain ⟨g, _, hin⟩ := Option.bind_eq_some_iff.1 hin
    rw [h5'] at hin
    have hy : inAt (parCOf A) g hd a.F = some (i, K) := hin
    have eu := (K5Law.inAt_parts hy).2.1
    obtain ⟨hL, hR⟩ := cov_parts hy hp
    intro f hf x hx
    obtain ⟨_, _, et, _⟩ := keysRun_covered hL hR (l₁ := w.1) (j := w.2) hw hkr f hf x hx
    exact et.trans eu
  | _ =>
    unfold First.S.heard5? at h5
    rw [he] at h5
    exact nomatch h5

/-- **THE FORMS OF THE TWO READERS THAT ARE HANDED TO THE LOOKUP's RUN "planes" NAME ENTRIES OF ROW
0 OF THE ARRAY OF THE READS ALONE**: the library's `readers_rowsIn`, its word `RowsIn` unfolded: the
end of the library's `readers_rows`, without that law's premise on what the runs read.
Conditional: hs: the open segment; hU: its ledger has the plan's array of the reads, of one row, at
the planned width; hr: the readers return. -/
theorem readers_tree {u : First.S} {a₀ : First.AttOwn}
    {r : (ℕ → ℕ → Option Aff) × (ℕ → Option Aff)} (hs : u.here = .att a₀)
    (hU : U3At A (plannedK A) a₀.F) (hr : readersOfO A u = some r) :
    (∀ e col f, r.1 e col = some f → ∀ y ∈ f.ents.toList, y.tree = A.iU3 ∧ y.row = 0) ∧
      ∀ col f, r.2 col = some f → ∀ y ∈ f.ents.toList, y.tree = A.iU3 ∧ y.row = 0 :=
  readers_rowsIn A hs hU hr

/-- **THE RUN "first" NAMES NO ENTRY AND NO RUN OF THE DIGITS' ARRAY, NOR OF A MATRIX's ARRAY OF
SYMBOLS.** Conditional: h5, hp; hr; ha: the array of the reads is another than these at tl. -/
theorem first_off {m : ℕ} {u : First.S} {z : List Claim × First.S} {hd : Heard}
    (h5 : u.heard5? = some hd) (hp : HeardPlain hd) (hr : runFirst (parCOf A) m u = .ok z)
    {tl : HTailF2} (ha : ApartAt tl A.iU3) : ∀ cl ∈ z.1,
    ((∀ x ∈ cl.form.ents, x.tree ≠ tl.ix.ZZ) ∧ ∀ v ∈ cl.runs, v.tree ≠ tl.ix.ZZ) ∧
      ∀ mu, mu < tl.NM → (∀ x ∈ cl.form.ents, x.tree ≠ tl.gtTree.getD mu 0) ∧
        ∀ v ∈ cl.runs, v.tree ≠ tl.gtTree.getD mu 0 :=
  fun cl hcl => off_apart (first_namesOnly A h5 hp hr cl hcl) ha

/-- **THE RUN "second"**, likewise. -/
theorem second_off {m : ℕ} {u : First.S} {z : List Claim × First.S} {hd : Heard}
    (h5 : u.heard5? = some hd) (hp : HeardPlain hd) (hr : runSecond (parCOf A) m u = .ok z)
    {tl : HTailF2} (ha : ApartAt tl A.iU3) : ∀ cl ∈ z.1,
    ((∀ x ∈ cl.form.ents, x.tree ≠ tl.ix.ZZ) ∧ ∀ v ∈ cl.runs, v.tree ≠ tl.ix.ZZ) ∧
      ∀ mu, mu < tl.NM → (∀ x ∈ cl.form.ents, x.tree ≠ tl.gtTree.getD mu 0) ∧
        ∀ v ∈ cl.runs, v.tree ≠ tl.gtTree.getD mu 0 :=
  fun cl hcl => off_apart (second_namesOnly A h5 hp hr cl hcl) ha

end State

end H2K5.Honest

#print axioms H2K5.Honest.off_of_only
#print axioms H2K5.Honest.off_apart
#print axioms H2K5.Honest.firstAt_tree
#print axioms H2K5.Honest.secondAt_tree
#print axioms H2K5.Honest.first_forms
#print axioms H2K5.Honest.second_forms
#print axioms H2K5.Honest.first_namesOnly
#print axioms H2K5.Honest.second_namesOnly
#print axioms H2K5.Honest.keys_none
#print axioms H2K5.Honest.first_row0
#print axioms H2K5.Honest.second_row0
#print axioms H2K5.Honest.keys_tree
#print axioms H2K5.Honest.readers_tree
#print axioms H2K5.Honest.first_off
#print axioms H2K5.Honest.second_off
