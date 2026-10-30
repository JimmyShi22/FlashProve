-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Claims/FunsAtTl.lean: kind K5: THE LIST OF TABLES THAT THE BLOCK AT PIECE 4 OF AN ATTENTION SEGMENT CLOSES IS funsAt A AT THE RECORD IN FRONT OF THAT BLOCK (Claims/FunsAt.lean: the tables that the claims' seat makes at a
record): "the yes of the block at piece 4 from a to b: b's smallness test's record's list of tables is funsAt A a".

Why. In front of that block the record's list of tables is still open: whoever must say there what the array of the reads will hold says it by funsAt A, which answers already behind the kind's own block; the block's last step makes the same
tables at the same arguments and closes the list with them.

Main names:
  shown_same: ledgers with the same slots show the same. left_same, leftKey_same, leftP_same, ptsFrom_same: the kind's road reads a ledger through Fork.shown alone. inAt_same: and the width of the array of the reads.
  funsAt_one: one answer at two records of an attention segment that agree in what the lookup returned, what the kind heard, the slots and that width.
  funsAt_tl: the step (readsAtSO, Att/ReadsO.lean). block4_funs: **the block's own decision.**
PREMISE: the open ledger in front has the array A.iU3: funsAt reads its width and answers [] without it; the step reads no array.
IS IT EMPTY HERE? Where the step or the block refuses nothing is said.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K1.KeepsSlots
import Johnson.Desc.K1.KeepsShapes
import Johnson.Desc.K1.Places
import Johnson.Desc.First.Att.ReadsO
import Johnson.Desc.First.Att.Claims.ReadsLays
import Johnson.Desc.First.Att.Claims.FunsAt

set_option autoImplicit false

namespace K5Law
open OnBytes OnBytes.Model
open VerifiableInference.Desc (First.S First.AttOwn Block named need)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (ParC Heard Geo)

theorem shown_same {F G : Fork} (h : PscRun.SlotsSame F G) (j : ℕ) : G.shown j = F.shown j := by
  unfold Fork.shown
  rw [h.ns, h.gotF, h.vp]

section Same
variable {F G : Fork} (e : ∀ j, G.shown j = F.shown j)
include e

theorem left_same (hh : VerifiableInference.Desc.Part.MaskedSum.Heard) (W : Array E) : P.left G hh W = P.left F hh W := by
  unfold P.left
  simp only [e]

theorem leftKey_same (g : Geo) (hh : VerifiableInference.Desc.Part.MaskedSum.Heard) (rho om' : Array E) :
    P.leftKey g G hh rho om' = P.leftKey g F hh rho om' := by
  unfold P.leftKey
  simp only [e]

theorem leftP_same (g : Geo) (zk : Array (Array E)) (h : Heard) : P.leftP g zk h G = P.leftP g zk h F := by
  unfold P.leftP
  simp only [left_same e, leftKey_same e]

theorem ptsFrom_same (g : Geo) (zk : Array (Array E)) (h : Heard) : P.ptsFrom g zk h G = P.ptsFrom g zk h F := by
  unfold P.ptsFrom
  rw [leftP_same e]

theorem inAt_same (c : ParC) (g : Forest.Heard) (h : Heard)
    (hK : (G.trees[c.iU3]?).map (·.K) = (F.trees[c.iU3]?).map (·.K)) : inAt c g h G = inAt c g h F := by
  unfold inAt
  rw [ptsFrom_same e, hK]

end Same

/-- One answer at two records that agree in what is read. -/
theorem funsAt_one (A : Attention.Plan) {s s' : First.S} {a a' : First.AttOwn} (hs : s.here = .att a)
    (hs' : s'.here = .att a') (hg : a'.g = a.g) (h5 : a'.heard5 = a.heard5) (e : ∀ j, a'.F.shown j = a.F.shown j)
    (hK : (a'.F.trees[A.iU3]?).map (·.K) = (a.F.trees[A.iU3]?).map (·.K)) : funsAt A s' = funsAt A s := by
  unfold funsAt
  rw [inOf_isAt hs, inOf_isAt hs', hg, h5]
  cases a.g with
  | none => rfl
  | some g =>
    cases a.heard5 with
    | none => rfl
    | some h =>
      show ((inAt (P.parCOf A) g h a'.F).map _).getD [] = ((inAt (P.parCOf A) g h a.F).map _).getD []
      rw [inAt_same e (P.parCOf A) g h hK]

/-- **The step closes the list with funsAt A at the record in front.** -/
theorem funsAt_tl (A : Attention.Plan) {s s' : First.S} {a : First.AttOwn} (h : readsAtSO A s = .ok s')
    (hs : s.here = .att a) (hT : (a.F.trees[A.iU3]?).isSome = true) :
    (s'.tl?).map (·.funs.toList) = some (funsAt A s) := by
  unfold readsAtSO at h
  simp only [hs] at h
  obtain ⟨hh, e5, h⟩ := except_bind_ok h
  obtain ⟨g, eg, h⟩ := except_bind_ok h
  obtain ⟨r, hr, h⟩ := except_bind_ok h
  have es : s' = { s with here := .att { a with t := some r.1, tl := r.2.1 } } := by cases h; rfl
  subst es
  unfold readsStepO at hr
  obtain ⟨_, _, hr⟩ := except_bind_ok hr
  obtain ⟨p, hp, hr⟩ := except_bind_ok hr
  obtain ⟨t, ht, hr⟩ := except_bind_ok hr
  obtain ⟨tl', hc, hr⟩ := except_bind_ok hr
  obtain ⟨_, _, hr⟩ := except_bind_ok hr
  have er : r = (tabsBack t, tl', a.F.next) := by cases hr; rfl
  subst er
  have e5' : a.heard5 = some hh := by
    have : s.heard5? = some hh := by
      cases x : s.heard5? with
      | none => rw [x] at e5; cases e5
      | some y => rw [x] at e5; cases e5; rfl
    unfold First.S.heard5? at this
    rw [hs] at this
    exact this
  have eg' : a.g = some g := by
    cases x : a.g with
    | none => rw [x] at eg; cases eg
    | some y => rw [x] at eg; cases eg; rfl
  have hp' : P.ptsFrom (P.parCOf A).geo g.zk hh a.F = some p := by
    cases x : P.ptsFrom (P.parCOf A).geo g.zk hh a.F with
    | none => rw [x] at hp; cases hp
    | some y => rw [x] at hp; cases hp; rfl
  have ht' : P.tablesP (P.parCOf A).geo (P.parCOf A).mats (P.parCOf A).nW (P.lookOfO (P.parCOf A).geo.lmb g) p = some t := by
    cases x : P.tablesP (P.parCOf A).geo (P.parCOf A).mats (P.parCOf A).nW (P.lookOfO (P.parCOf A).geo.lmb g) p with
    | none => rw [x] at ht; cases ht
    | some y => rw [x] at ht; cases ht; rfl
  have etl : tl'.funs = (tabsBack t).funs := by
    unfold VerifiableInference.Desc.First.K8.Order.close at hc
    split at hc
    · cases hc
    · cases hc; rfl
  obtain ⟨T, hT'⟩ := Option.isSome_iff_exists.1 hT
  have ein : inAt (P.parCOf A) g hh a.F =
      some ({ g := (P.parCOf A).geo, p := p, t := t, zk := g.zk, iU3 := (P.parCOf A).iU3 }, T.K) := by
    have hT'' : a.F.trees[(P.parCOf A).iU3]? = some T := hT'
    unfold inAt
    simp only [Option.bind_eq_bind, hp', Option.bind_some, ht', hT'', Option.map_some]
    rfl
  show some tl'.funs.toList = some (funsAt A s)
  unfold funsAt
  rw [inOf_isAt hs, eg', e5']
  show _ = some (((inAt (P.parCOf A) g hh a.F).map _).getD [])
  rw [ein, etl]
  rfl

/-- The record behind a commitment of K1's, at an attention segment. -/
theorem here_commit {Lt : Type} {s : First.S} {a₀ : First.AttOwn} (hs : s.here = .att a₀)
    (d : _root_.Desc.Plain.DState Lt) (L : LinkCtx) (F : Fork) :
    (((VerifiableInference.Desc.K1.laid s d).putLink L).putFork F).here = .att { a₀ with L := L, F := F } := by
  have e1 : (VerifiableInference.Desc.K1.laid s d).here = .att a₀ := hs
  have e2 : ((VerifiableInference.Desc.K1.laid s d).putLink L).here = .att { a₀ with L := L } := by
    unfold First.S.putLink
    rw [e1]
  unfold First.S.putFork
  rw [e2]

/-- **THE BLOCK AT PIECE 4, FROM a TO b.** -/
theorem block4_funs {Cl : Type} (q : Params.First) (gp : Desc.Plain.GPar) (link piece moment : ℕ) (arrays : Option (List ℕ))
    (name : String) (W : Verify.Public) (l g : ℕ) (z : Block First.S Cl) (hz : readsAtO W l g = some z) {A : Attention.Plan}
    (hA : W.A[g]? = some A) {a b : First.S} {a₀ : First.AttOwn} {rs : List Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    (h : ((VerifiableInference.Desc.K1.laterAt (Cl := Cl) q gp link piece moment arrays).andThen name z).decide a rs gs = .ok b)
    (ha : a.here = .att a₀) (hT : (a₀.F.trees[A.iU3]?).isSome = true) :
    (b.tl?).map (·.funs.toList) = some (funsAt A a) := by
  obtain ⟨m, h1, h2⟩ := except_bind_ok h
  unfold readsAtO at hz
  rw [hA] at hz
  obtain rfl := Option.some.inj hz
  have h2' : readsAtSO A m = .ok b := h2
  have hf : a.fork? = some a₀.F := by
    unfold First.S.fork?
    rw [ha]
  obtain ⟨_, F, _, y, _, hF, _, em, ss⟩ := VerifiableInference.Desc.K1.commitAtS_slots h1
  obtain ⟨_, F', _, y', _, hF', _, em', sh⟩ := VerifiableInference.Desc.K1.commitAtS_shapes h1
  obtain rfl : a₀.F = F := Option.some.inj (hf.symm.trans hF)
  obtain rfl : a₀.F = F' := Option.some.inj (hf.symm.trans hF')
  have hm := here_commit ha y.w y.L y.F
  rw [← em] at hm
  have hm' := here_commit ha y'.w y'.L y'.F
  rw [← em'] at hm'
  have eF : y'.F = y.F :=
    congrArg (fun v : First.AttOwn => v.F) (VerifiableInference.Desc.First.Here.att.inj (hm'.symm.trans hm))
  rw [eF] at sh
  have hsh : ∀ t : ℕ, (y.F.trees[t]?).map (fun T : HTree => (T.R, T.K)) = (a₀.F.trees[t]?).map fun T : HTree => (T.R, T.K) := by
    intro t
    have := congrArg (fun v => v[t]?) sh
    simpa [Array.getElem?_map] using this
  have hK : (y.F.trees[A.iU3]?).map (·.K) = (a₀.F.trees[A.iU3]?).map (·.K) := by
    have := congrArg (Option.map Prod.snd) (hsh A.iU3)
    simpa [Option.map_map, Function.comp_def] using this
  have hTm : (y.F.trees[A.iU3]?).isSome = true := by
    obtain ⟨T, eT⟩ := Option.isSome_iff_exists.1 hT
    rw [eT] at hK
    obtain ⟨T', eT', _⟩ := Option.map_eq_some_iff.1 hK
    rw [eT']
    rfl
  rw [funsAt_tl A h2' hm hTm]
  exact congrArg some (funsAt_one A ha hm rfl rfl (shown_same ss) hK)

end K5Law

#print axioms K5Law.funsAt_one
#print axioms K5Law.funsAt_tl
#print axioms K5Law.block4_funs
