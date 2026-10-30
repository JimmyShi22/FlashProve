-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/G6/Rider/Psc.lean: a second zero test on the challenges of a sumcheck.

Definitions, statements and proofs. No protocol of its own.

The block is the sumcheck for a polynomial summand of Cb/Ld/LdPsc.lean (`PscPar.psc`, `PscOur`; the
theorem for `PscOur`, `psc_our_goodAt`: Cb/Ld/LdLineAt.lean). The rider (Cb/G6/Rider/Both.lean) is:
before the block, every array f i of a family is 0 on the cube of dimension g (`OnCube`); behind it,
the multilinear extension of every f i is 0 at the coordinates pl 0, .., pl (g - 1) of the block's
own point (`AtPoint`). The arrays read the block's state and the tuple of messages.

Main statements.
  `psc_rider_any`: for any two joints between which the sumcheck is `GoodAt`.
  `psc_rider`, `psc_our_rider`: over the library's `psc_goodAt`, `psc_our_goodAt`; the larger count
  in each round.
  `psc_our_rider_same`: no number changed, if each placed variable has degree at least 1.
  `psc_our_two_riders`, `psc_our_rider_in`, `psc_our_rider_sig`: two riders; the safe form; over a
  signature.
  `ptTrue`, `ptTrue_eq`, `psc_our_rider_run`: a reader of the point that compiles, and the rule
  through it.
  `psc_max_counts`: the list of counts, round by round.
  `hollow_source_kept`, `hollow_semantic`: empty uses.

Under: the library's own conditions (`VarsOK`, `DegOK` or `DegX` and `DegY`, `ValInj`); the places
different and in range. An empty family makes source and target both true; g = 0 means one vertex
and no challenge.

An empty use. A0 (A, B in `psc_rider_any`) is a free letter. If A0, or any other part of the input's
`relR` without the rider, gives the source, the statement follows from the library's theorem alone,
at any places, and says nothing (`hollow_own`, `hollow_out`, `hollow_semantic`). The safe form is
`psc_our_rider_in`. A use should prove the two sentences that stand at `hollow_own`
(Cb/G6/Rider/Both.lean).

It does not say: more than `GoodAt` at the joints with the rider; anything on a coordinate that
another block draws; that the target is a claim that a later stage takes up; anything on a form that
reads an array which is sent after the sumcheck (by type the rider reads the tuple and the input
statement alone). Nothing is extracted for the rider: its half is soundness at the fixed tuple.

Computable? `ptAt`, `selPl`, `placed`, `ptT`, `ptTrue` are plain definitions. `ptAt` recurses on the
list of formats, so that list is a value at run time; at `T.par.fmt`, where the targets read it, it
does not compile, because the format of the added last variable is noncomputable in the library
(Cb/Ld/LdPsc.lean). `ptTrue` is the reader that compiles; see its docstring for where it runs.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLineAt
import Cb.G6.Rider.Both

set_option autoImplicit false

namespace Cb.Rider
open Iop Prob Cb Blocks
open scoped ENNReal

/-! ## 1. The places, the source and the target -/

section Psc
variable {E : Type}

/-- Coordinate i of a point of the sumcheck's variables (0 beyond the last). It recurses on the list
of formats. -/
def ptAt [Zero E] : (l : List (PFmt E)) → PPt l → ℕ → E
  | [], _, _ => 0
  | _ :: _, γ, 0 => γ.1
  | _ :: l, γ, i + 1 => ptAt l γ.2 i

/-- Which coordinate of the rider's point, if any, the round of variable i draws: t if i = pl t for
some t < g. -/
def selPl (g : ℕ) (pl : ℕ → ℕ) (i : ℕ) : Option ℕ := (List.range g).find? fun t => pl t = i

variable [Field E]

/-- The rounds of the variables l, numbered from i: the round of variable j binds what sel j names,
read through the format's own map `val`. -/
def bindsV (sel : ℕ → Option ℕ) : (i : ℕ) → (l : List (PFmt E)) → Binds ℕ E (pRounds l)
  | _, [] => ()
  | i, f :: l => ((sel i).map fun k => (k, f.val), bindsV sel (i + 1) l)

variable [Fintype E]

/-- The whole sumcheck `Y.psc Ex`: its first round and its last bind nothing; the rounds of the
variables bind by sel. -/
noncomputable def pscBinds (Y : PscPar E) (Ex : ExtSpec) (sel : ℕ → Option ℕ) :
    Binds ℕ E (Y.psc Ex).shape :=
  Binds.app (s := (Y.core Ex).shape) (t := (Y.ends Ex).shape)
    ((none, bindsV sel 0 Y.fmt) : Binds ℕ E (pRound0 E :: pRounds Y.fmt))
    ((none, ()) : Binds ℕ E [pRoundV E Y.A])

/-- The rider's list of counts on the sumcheck: 1 in the round of a placed variable, 0 elsewhere. -/
noncomputable def pscRiderErr (Y : PscPar E) (Ex : ExtSpec) (g : ℕ) (pl : ℕ → ℕ) :
    Err (Y.psc Ex).shape :=
  (pscBinds Y Ex (selPl g pl)).err fun _ => 1

/-- The source: every array of the family is 0 at every vertex of the cube of dimension g. -/
def OnCube {St M ι : Type} (g : ℕ) (f : ι → St → M → ℕ → E) (st : St) (m : M) : Prop :=
  ∀ i, ∀ X < 2 ^ g, f i st m X = 0

/-- The target: the multilinear extension of every array is 0 at the coordinates pl 0, .., pl (g -
1) of the sumcheck's point. -/
def AtPoint {St M ι : Type} (g : ℕ) (pl : ℕ → ℕ) (f : ι → St → M → ℕ → E) (l : List (PFmt E))
    (st : St) (γ : PPt l) (m : M) : Prop :=
  ∀ i, ext g (f i st m) (fun t => ptAt l γ (pl t)) = 0

/-! ## 2. Lemmas on the places and on the rounds of the variables; the rule -/

theorem selPl_some {g : ℕ} {pl : ℕ → ℕ} {i t : ℕ} (h : selPl g pl i = some t) :
    t < g ∧ pl t = i := by
  refine ⟨List.mem_range.mp (List.mem_of_find?_eq_some h), ?_⟩
  have := List.find?_some h
  simpa using this

theorem selPl_apply {g : ℕ} {pl : ℕ → ℕ} (hpl : ∀ t < g, ∀ t' < g, pl t = pl t' → t = t') {t : ℕ}
    (ht : t < g) : selPl g pl (pl t) = some t := by
  cases h : selPl g pl (pl t) with
  | none =>
    have := List.find?_eq_none.1 h t (List.mem_range.mpr ht)
    simp at this
  | some t' =>
    obtain ⟨h1, h2⟩ := selPl_some h
    rw [hpl t' h1 t ht h2]

theorem selPl_inj {g : ℕ} {pl : ℕ → ℕ} {i i' k : ℕ} (h : selPl g pl i = some k)
    (h' : selPl g pl i' = some k) : i = i' :=
  (selPl_some h).2.symm.trans (selPl_some h').2

omit [Fintype E] in
theorem mem_vars_bindsV (sel : ℕ → Option ℕ) {k : ℕ} : ∀ (l : List (PFmt E)) (i : ℕ),
    k ∈ (bindsV sel i l).vars ↔ ∃ j < l.length, sel (i + j) = some k
  | [], _ => ⟨fun h => absurd h List.not_mem_nil, fun ⟨_, hj, _⟩ => absurd hj (Nat.not_lt_zero _)⟩
  | f :: l, i => by
      have ih := mem_vars_bindsV sel (k := k) l (i + 1)
      have hstep : (∃ j < l.length, sel (i + 1 + j) = some k) ↔
          ∃ j < (f :: l).length, 0 < j ∧ sel (i + j) = some k := by
        constructor
        · rintro ⟨j, hj, hs⟩
          exact ⟨j + 1, Nat.succ_lt_succ hj, Nat.succ_pos _, by rw [← hs]; congr 1; omega⟩
        · rintro ⟨j, hj, h0, hs⟩
          obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
          exact ⟨j', Nat.lt_of_succ_lt_succ hj, by rw [← hs]; congr 1; omega⟩
      show k ∈ Binds.vars (s := pRound f :: pRounds l)
        ((sel i).map fun k => (k, f.val), bindsV sel (i + 1) l) ↔ _
      cases hs : sel i with
      | none =>
        show k ∈ (bindsV sel (i + 1) l).vars ↔ _
        rw [ih, hstep]
        constructor
        · rintro ⟨j, hj, _, h⟩
          exact ⟨j, hj, h⟩
        · rintro ⟨j, hj, h⟩
          refine ⟨j, hj, Nat.pos_of_ne_zero fun h0 => ?_, h⟩
          subst h0
          rw [Nat.add_zero, hs] at h
          cases h
      | some k₀ =>
        show k ∈ k₀ :: (bindsV sel (i + 1) l).vars ↔ _
        rw [List.mem_cons, ih, hstep]
        constructor
        · rintro (rfl | ⟨j, hj, _, h⟩)
          · exact ⟨0, Nat.succ_pos _, hs⟩
          · exact ⟨j, hj, h⟩
        · rintro ⟨j, hj, h⟩
          rcases Nat.eq_zero_or_pos j with rfl | h0
          · rw [Nat.add_zero, hs] at h
            exact Or.inl (Option.some.inj h).symm
          · exact Or.inr ⟨j, hj, h0, h⟩

omit [Fintype E] in
theorem inj_bindsV (sel : ℕ → Option ℕ) : ∀ (l : List (PFmt E)) (i : ℕ),
    (∀ φ ∈ l, Function.Injective φ.val) → (bindsV sel i l).Inj
  | [], _, _ => trivial
  | f :: l, i, h => by
      have ih := inj_bindsV sel l (i + 1) fun φ hφ => h φ (List.mem_cons_of_mem _ hφ)
      show Binds.Inj (s := pRound f :: pRounds l)
        ((sel i).map fun k => (k, f.val), bindsV sel (i + 1) l)
      cases sel i with
      | none => exact ih
      | some k => exact ⟨h f List.mem_cons_self, ih⟩

omit [Fintype E] in
/-- The point that the analysis reads off the challenges is the point of the variables, at each
placed coordinate. -/
theorem pt_bindsV (sel : ℕ → Option ℕ)
    (hsel : ∀ i i' k, sel i = some k → sel i' = some k → i = i') :
    ∀ (l : List (PFmt E)) (i : ℕ) (ρ : Rho (pRounds l)) (z : ℕ → E) (j k : ℕ), j < l.length →
      sel (i + j) = some k → (bindsV sel i l).pt ρ z k = ptAt l (pG l ρ) j
  | [], _, _, _, _, _, hj, _ => absurd hj (Nat.not_lt_zero _)
  | f :: l, i, (c, ρ), z, j, k, hj, hk => by
      show Binds.pt (s := pRound f :: pRounds l)
        ((sel i).map fun k => (k, f.val), bindsV sel (i + 1) l) (c, ρ) z k = _
      cases j with
      | zero =>
        rw [Nat.add_zero] at hk
        rw [hk]
        show (bindsV sel (i + 1) l).pt ρ (Function.update z k (f.val c)) k = f.val c
        have hnot : k ∉ (bindsV sel (i + 1) l).vars := by
          rw [mem_vars_bindsV]
          rintro ⟨j', _, h'⟩
          have := hsel _ _ k hk h'
          omega
        rw [Binds.pt_of_notMem _ _ _ hnot, Function.update_self]
      | succ j =>
        have hk' : sel (i + 1 + j) = some k := by rw [← hk]; congr 1; omega
        have ih := fun z' => pt_bindsV sel hsel l (i + 1) ρ z' j k (Nat.lt_of_succ_lt_succ hj) hk'
        show _ = ptAt l (pG l ρ) j
        cases sel i with
        | none => exact ih z
        | some k₀ => exact ih _

omit [Fintype E] in
theorem err_bindsV_le (sel : ℕ → Option ℕ) : ∀ (l : List (PFmt E)) (i : ℕ),
    (∀ j φ k, l[j]? = some φ → sel (i + j) = some k → 1 ≤ φ.n) →
    Err.le ((bindsV sel i l).err fun _ => 1) (pErr l)
  | [], _, _ => trivial
  | f :: l, i, h => by
      have ih := err_bindsV_le sel l (i + 1) fun j φ k hφ hk =>
        h (j + 1) φ k (by simpa using hφ) (by rw [← hk]; congr 1; omega)
      show Err.le (s := pRound f :: pRounds l)
        (Binds.err (fun _ => 1) (s := pRound f :: pRounds l)
          ((sel i).map fun k => (k, f.val), bindsV sel (i + 1) l)) (f.n, pErr l)
      cases hs : sel i with
      | none => exact ⟨Nat.zero_le _, ih⟩
      | some k => exact ⟨h 0 f k (by simp) hs, ih⟩

omit [Fintype E] in
theorem below_bindsV (sel : ℕ → Option ℕ) (c : ℝ≥0∞) : ∀ (l : List (PFmt E)) (i : ℕ),
    (∀ j φ k, l[j]? = some φ → sel (i + j) = some k →
      (1 : ℝ≥0∞) ≤ c * (Fintype.card φ.Ch : ℝ≥0∞)) →
    Err.Below ((bindsV sel i l).err fun _ => 1) c
  | [], _, _ => trivial
  | f :: l, i, h => by
      have ih := below_bindsV sel c l (i + 1) fun j φ k hφ hk =>
        h (j + 1) φ k (by simpa using hφ) (by rw [← hk]; congr 1; omega)
      show Err.Below (s := pRound f :: pRounds l)
        (Binds.err (fun _ => 1) (s := pRound f :: pRounds l)
          ((sel i).map fun k => (k, f.val), bindsV sel (i + 1) l)) c
      cases hs : sel i with
      | none => exact ⟨by simp, ih⟩
      | some k => exact ⟨by simpa using h 0 f k (by simp) hs, ih⟩

theorem vars_pscBinds (Y : PscPar E) (Ex : ExtSpec) (sel : ℕ → Option ℕ) :
    (pscBinds Y Ex sel).vars = (bindsV sel 0 Y.fmt).vars :=
  (Binds.vars_app (s := (Y.core Ex).shape) (t := (Y.ends Ex).shape)
    ((none, bindsV sel 0 Y.fmt) : Binds ℕ E (pRound0 E :: pRounds Y.fmt))
    ((none, ()) : Binds ℕ E [pRoundV E Y.A])).trans (List.append_nil _)

theorem inj_pscBinds (Y : PscPar E) (Ex : ExtSpec) (sel : ℕ → Option ℕ) (hI : Y.ValInj) :
    (pscBinds Y Ex sel).Inj :=
  Binds.Inj.app (s := (Y.core Ex).shape) (t := (Y.ends Ex).shape)
    (a := ((none, bindsV sel 0 Y.fmt) : Binds ℕ E (pRound0 E :: pRounds Y.fmt)))
    (b := ((none, ()) : Binds ℕ E [pRoundV E Y.A])) (inj_bindsV sel Y.fmt 0 hI) trivial

theorem pt_pscBinds (Y : PscPar E) (Ex : ExtSpec) (sel : ℕ → Option ℕ) (τ : Tr (Y.psc Ex).shape)
    (z : ℕ → E) :
    (pscBinds Y Ex sel).pt τ.rho z =
      (bindsV sel 0 Y.fmt).pt
        (Tr.fst (s := (Y.core Ex).shape) (t := (Y.ends Ex).shape) τ).rho.2 z := by
  have h := Binds.pt_app (s := (Y.core Ex).shape) (t := (Y.ends Ex).shape)
    ((none, bindsV sel 0 Y.fmt) : Binds ℕ E (pRound0 E :: pRounds Y.fmt))
    ((none, ()) : Binds ℕ E [pRoundV E Y.A]) τ.rho z
  rw [Tr.rho_fst]
  exact h

/-- Whatever the sumcheck's verifier outputs: the state is the input's, and the point is made of the
challenges of the variables' rounds. -/
theorem psc_out_pt (Y : PscPar E) (Ex : ExtSpec) (x : E × Y.St) (y : Ex.Str)
    (τ : Tr (Y.psc Ex).shape) (o : Y.Out) (h : (Y.psc Ex).out x y τ = some o) :
    o.st = x.2 ∧ o.pt = pG Y.fmt (Tr.fst (s := (Y.core Ex).shape) (t := (Y.ends Ex).shape)
        τ).rho.2 := by
  have h' : ((Y.outC x (Tr.fst (s := (Y.core Ex).shape) (t := (Y.ends Ex).shape) τ)).bind fun z =>
      (Y.ends Ex).out z y (Tr.snd (s := (Y.core Ex).shape) τ)) = some o := h
  obtain ⟨z, hz, ho⟩ := Option.bind_eq_some_iff.mp h'
  unfold PscPar.outC at hz
  split at hz
  · have hz' := Option.some.inj hz
    have ho' := Option.some.inj ho
    subst hz'
    subst ho'
    exact ⟨rfl, rfl⟩
  · exact absurd hz (by simp)

omit [Fintype E] in
/-- `ptAt` on the point of challenges, by recursion. -/
theorem ptAt_pG (φ : PFmt E) (l : List (PFmt E)) (c : φ.Ch) (ρ : Rho (pRounds l)) (i : ℕ) :
    ptAt (φ :: l) (pG (φ :: l) (c, ρ)) 0 = φ.val c ∧
      ptAt (φ :: l) (pG (φ :: l) (c, ρ)) (i + 1) = ptAt l (pG l ρ) i :=
  ⟨rfl, rfl⟩

/-- The rule at the sumcheck `Y.psc Ex`, for any two joints between which it is `GoodAt`: the same
term is `GoodAt` from (A and the source) to (B and the target), with the larger count in each round.
The places pl t are different and in range. It applies to its own result. Warning: A and B are free.
Wherever the input joint's `relR` without the rider (a relation that rides along, or the block's own
claim) or the output joint's `relR` already gives the source, this says nothing (`hollow_own`,
`hollow_out`, Cb/G6/Rider/Both.lean; the test of a use stands at `hollow_own`). -/
theorem psc_rider_any (Y : PscPar E) (Ex : ExtSpec) {M Wi Wo Kc ι : Type}
    {H : (Y.psc Ex).Honest (M × Wi) (M × Wo)} {A : IOR.Rels Kc (E × Y.St) Ex (M × Wi)}
    {B : IOR.Rels Kc Y.Out Ex (M × Wo)}
    {xt : M → (E × Y.St) × Ex.Str → Tr (Y.psc Ex).shape → Wo → Wi} {P : IOR.Nums Kc (Y.psc Ex)}
    (h : GoodAt (Y.psc Ex) H A B xt P) (hI : Y.ValInj)
    (g : ℕ) (pl : ℕ → ℕ) (hpl : ∀ t < g, ∀ t' < g, pl t = pl t' → t = t')
    (hlt : ∀ t < g, pl t < Y.fmt.length) (f : ι → Y.St → M → ℕ → E) :
    GoodAt (Y.psc Ex) H (withRider A fun m a => OnCube g f a.1.2 m)
      (withRider B fun m o => AtPoint g pl f Y.fmt o.1.st o.1.pt m) xt
      (numsMax P (pscRiderErr Y Ex g pl)) :=
  goodAt_cube h (pscBinds Y Ex (selPl g pl)) (inj_pscBinds Y Ex _ hI) g id (fun _ _ _ _ e => e)
    (fun t ht => by
      rw [vars_pscBinds, mem_vars_bindsV]
      exact ⟨pl t, hlt t ht, by rw [Nat.zero_add]; exact selPl_apply hpl ht⟩)
    (fun i m a => f i a.1.2 m) (fun i m o => f i o.1.st m) (fun o t => ptAt Y.fmt o.1.pt (pl t))
    (fun i m a τ o ho X _ => by
      obtain ⟨xo, hxo, rfl⟩ := Option.map_eq_some_iff.mp ho
      show f i xo.st m X = f i a.1.2 m X
      rw [(psc_out_pt Y Ex a.1 a.2 τ xo hxo).1])
    (fun a τ o ho t ht => by
      obtain ⟨xo, hxo, rfl⟩ := Option.map_eq_some_iff.mp ho
      show ptAt Y.fmt xo.pt (pl t) = _
      rw [pt_pscBinds, (psc_out_pt Y Ex a.1 a.2 τ xo hxo).2]
      exact (pt_bindsV _ (fun _ _ _ h h' => selPl_inj h h') Y.fmt 0 _ _ (pl t) t (hlt t ht)
        (by rw [Nat.zero_add]; exact selPl_apply hpl ht)).symm)

/-- The rule over the library's `psc_goodAt`. Warning: A0 is free. Wherever the input joint's `relR`
without the rider (a relation that rides along, or the block's own claim) or the output joint's
`relR` already gives the source, this says nothing (`hollow_own`, `hollow_out`,
Cb/G6/Rider/Both.lean; the test of a use stands at `hollow_own`). -/
theorem psc_rider (Y : PscPar E) (Ex : ExtSpec) (M Wp Kc ι : Type)
    (A0 : IOR.Rels Kc Y.St Ex (M × Wp)) (msg : M → Y.J → E)
    (hV : Y.VarsOK) (hD : Y.DegOK) (hI : Y.ValInj)
    (g : ℕ) (pl : ℕ → ℕ) (hpl : ∀ t < g, ∀ t' < g, pl t = pl t' → t = t')
    (hlt : ∀ t < g, pl t < Y.fmt.length) (f : ι → Y.St → M → ℕ → E) :
    GoodAt (Y.psc Ex) (Y.hon Ex fun w => msg w.1)
      (withRider (Y.baseIn A0 fun w => msg w.1) fun m a => OnCube g f a.1.2 m)
      (withRider (Y.baseOut A0 fun w => msg w.1) fun m o => AtPoint g pl f Y.fmt o.1.st o.1.pt m)
      (fun _ _ _ wp => wp) (numsMax (Y.nums Ex Kc) (pscRiderErr Y Ex g pl)) :=
  psc_rider_any Y Ex (psc_goodAt E Y Ex M Wp Kc A0 msg hV hD hI) hI g pl hpl hlt f

/-- The rule for every `PscOur`, from the sum claim `T.baseIn`: reduction, honest prover and
extractor are those of the library's `psc_our_goodAt`, letter for letter. The places pl t are rounds
of the variables of `T.fmt` (not of the added last variable). Counts: the larger in each round.
Warning: A0 is free. Wherever the input joint's `relR` without the rider (a relation that rides
along, or the block's own claim) or the output joint's `relR` already gives the source, this says
nothing (`hollow_own`, `hollow_out`, Cb/G6/Rider/Both.lean; the test of a use stands at
`hollow_own`). -/
theorem psc_our_rider (T : PscOur E) (Ex : ExtSpec) (M Wp Kc ι : Type)
    (A0 : IOR.Rels Kc T.St Ex (M × Wp)) (msg : M → T.J → E)
    (hV : T.VarsOK) (hX : T.DegX) (hY : T.DegY) (hI : T.ValInj)
    (g : ℕ) (pl : ℕ → ℕ) (hpl : ∀ t < g, ∀ t' < g, pl t = pl t' → t = t')
    (hlt : ∀ t < g, pl t < T.fmt.length) (f : ι → T.St → M → ℕ → E) :
    GoodAt (T.par.psc Ex) (T.par.hon Ex fun w => msg w.1)
      (withRider (T.baseIn A0 fun w => msg w.1) fun m a => OnCube g f a.1.2 m)
      (withRider (T.par.baseOut A0 fun w => msg w.1)
        fun m o => AtPoint g pl f T.par.fmt o.1.st o.1.pt m)
      (fun _ _ _ wp => wp) (numsMax (T.par.nums Ex Kc) (pscRiderErr T.par Ex g pl)) := by
  have e : T.SumHolds = T.par.SumHolds :=
    funext fun x => funext fun m => propext (psc_our_sum E T x m).symm
  unfold PscOur.baseIn
  rw [e]
  exact psc_rider T.par Ex M Wp Kc ι A0 msg ((psc_our_ok E T).1 hV) (psc_our_deg E T hX hY)
    ((psc_our_ok E T).2 hI) g pl hpl
    (fun t ht => lt_of_lt_of_le (hlt t ht) (by
      show T.fmt.length ≤ (T.fmt ++ [pDummy E T.DY]).length
      rw [List.length_append]
      exact Nat.le_add_right _ _)) f

/-- If each placed variable has degree at least 1, the rider's list lies below the sumcheck's own.
-/
theorem psc_rider_err_le (Y : PscPar E) (Ex : ExtSpec) (g : ℕ) (pl : ℕ → ℕ)
    (hn : ∀ t < g, ∀ φ, Y.fmt[pl t]? = some φ → 1 ≤ φ.n) :
    Err.le (pscRiderErr Y Ex g pl) (Y.err Ex) := by
  have e1 : pscRiderErr Y Ex g pl =
      Err.app (s := (Y.core Ex).shape) (t := (Y.ends Ex).shape)
        (Binds.err (fun _ => 1)
          ((none, bindsV (selPl g pl) 0 Y.fmt) : Binds ℕ E (pRound0 E :: pRounds Y.fmt)))
        (Binds.err (fun _ => 1) ((none, ()) : Binds ℕ E [pRoundV E Y.A])) :=
    Binds.err_app (s := (Y.core Ex).shape) (t := (Y.ends Ex).shape) (fun _ => 1) _ _
  rw [e1]
  refine Iop.Err.le_app (s := (Y.core Ex).shape) (t := (Y.ends Ex).shape) (a' := Y.errC Ex)
    (b' := (0, ())) ⟨Nat.zero_le _, ?_⟩ ⟨Nat.le_refl _, trivial⟩
  refine err_bindsV_le _ Y.fmt 0 fun j φ k hφ hk => ?_
  rw [Nat.zero_add] at hk
  obtain ⟨hk1, hk2⟩ := selPl_some hk
  exact hn k hk1 φ (by rw [hk2]; exact hφ)

/-- The same for a `PscOur`. -/
theorem psc_our_rider_err_le (T : PscOur E) (Ex : ExtSpec) (g : ℕ) (pl : ℕ → ℕ)
    (hlt : ∀ t < g, pl t < T.fmt.length) (hn : ∀ t < g, ∀ φ, T.fmt[pl t]? = some φ → 1 ≤ φ.n) :
    Err.le (pscRiderErr T.par Ex g pl) (T.par.err Ex) :=
  psc_rider_err_le T.par Ex g pl fun t ht φ hφ => by
    have hφ' : (T.fmt ++ [pDummy E T.DY])[pl t]? = some φ := hφ
    rw [List.getElem?_append_left (hlt t ht)] at hφ'
    exact hn t ht φ hφ'

/-- The rule with no number changed: `T.par.nums Ex Kc` itself, if each placed variable has degree
at least 1. Each count is over that round's own set of challenges: in the round of a placed variable
with format φ at most max (φ.n, 1) = φ.n values are bad (`psc_max_counts` writes the list out). The
condition on degrees cannot be dropped (`same_needs_hn`, Cb/G6/Rider/PscTest.lean): where a placed
variable has degree 0 the larger count of its round is 1, not the block's own 0; `psc_our_rider` has
that count. Warning: A0 is free. Wherever the input joint's `relR` without the rider (a relation
that rides along, or the block's own claim) or the output joint's `relR` already gives the source,
this says nothing (`hollow_own`, `hollow_out`, Cb/G6/Rider/Both.lean; the test of a use stands at
`hollow_own`). -/
theorem psc_our_rider_same (T : PscOur E) (Ex : ExtSpec) (M Wp Kc ι : Type)
    (A0 : IOR.Rels Kc T.St Ex (M × Wp)) (msg : M → T.J → E)
    (hV : T.VarsOK) (hX : T.DegX) (hY : T.DegY) (hI : T.ValInj)
    (g : ℕ) (pl : ℕ → ℕ) (hpl : ∀ t < g, ∀ t' < g, pl t = pl t' → t = t')
    (hlt : ∀ t < g, pl t < T.fmt.length) (hn : ∀ t < g, ∀ φ, T.fmt[pl t]? = some φ → 1 ≤ φ.n)
    (f : ι → T.St → M → ℕ → E) :
    GoodAt (T.par.psc Ex) (T.par.hon Ex fun w => msg w.1)
      (withRider (T.baseIn A0 fun w => msg w.1) fun m a => OnCube g f a.1.2 m)
      (withRider (T.par.baseOut A0 fun w => msg w.1)
        fun m o => AtPoint g pl f T.par.fmt o.1.st o.1.pt m)
      (fun _ _ _ wp => wp) (T.par.nums Ex Kc) := by
  have h := psc_our_rider T Ex M Wp Kc ι A0 msg hV hX hY hI g pl hpl hlt f
  rwa [numsMax_eq _ (psc_our_rider_err_le T Ex g pl hlt hn)] at h

/-! ## 3. The counts, written out round by round -/

/-- Is variable i placed? -/
def placed (g : ℕ) (pl : ℕ → ℕ) (i : ℕ) : Bool := (selPl g pl i).isSome

theorem placed_iff {g : ℕ} {pl : ℕ → ℕ} (hpl : ∀ t < g, ∀ t' < g, pl t = pl t' → t = t') (i : ℕ) :
    placed g pl i = true ↔ ∃ t < g, pl t = i := by
  unfold placed
  rw [Option.isSome_iff_exists]
  exact ⟨fun ⟨t, ht⟩ => ⟨t, selPl_some ht⟩, fun ⟨t, ht, e⟩ => ⟨t, e ▸ selPl_apply hpl ht⟩⟩

/-- The rider's counts on the variables' rounds, as a list: 1 if placed, else 0. -/
def riderCounts (nm : ℕ → Bool) : (i : ℕ) → (l : List (PFmt E)) → Err (pRounds l)
  | _, [] => ()
  | i, _ :: l => (if nm i then 1 else 0, riderCounts nm (i + 1) l)

/-- The larger counts on the variables' rounds: max (φ.n, 1) if placed, else φ.n. -/
def maxCounts (nm : ℕ → Bool) : (i : ℕ) → (l : List (PFmt E)) → Err (pRounds l)
  | _, [] => ()
  | i, φ :: l => (Nat.max φ.n (if nm i then 1 else 0), maxCounts nm (i + 1) l)

omit [Fintype E] in
theorem err_bindsV_eq (sel : ℕ → Option ℕ) : ∀ (l : List (PFmt E)) (i : ℕ),
    (bindsV sel i l).err (fun _ => 1) = riderCounts (fun j => (sel j).isSome) i l
  | [], _ => rfl
  | f :: l, i => by
      have ih := err_bindsV_eq sel l (i + 1)
      show Binds.err (fun _ => 1) (s := pRound f :: pRounds l)
        ((sel i).map fun k => (k, f.val), bindsV sel (i + 1) l) =
          (if (sel i).isSome = true then 1 else 0, riderCounts (fun j => (sel j).isSome) (i + 1) l)
      cases sel i with
      | none => exact Prod.ext rfl ih
      | some k => exact Prod.ext rfl ih

omit [Fintype E] in
theorem max_pErr_riderCounts (nm : ℕ → Bool) : ∀ (l : List (PFmt E)) (i : ℕ),
    Err.max (pErr l) (riderCounts nm i l) = maxCounts nm i l
  | [], _ => rfl
  | _ :: l, i => Prod.ext rfl (max_pErr_riderCounts nm l (i + 1))

/-- The rider's list, written out round by round. -/
theorem pscRiderErr_eq (Y : PscPar E) (Ex : ExtSpec) (g : ℕ) (pl : ℕ → ℕ) :
    pscRiderErr Y Ex g pl =
      Err.app (s := (Y.core Ex).shape) (t := (Y.ends Ex).shape)
        ((0, riderCounts (placed g pl) 0 Y.fmt) : Err (pRound0 E :: pRounds Y.fmt))
        ((0, ()) : Err [pRoundV E Y.A]) := by
  refine (Binds.err_app (s := (Y.core Ex).shape) (t := (Y.ends Ex).shape) (fun _ => 1)
    ((none, bindsV (selPl g pl) 0 Y.fmt) : Binds ℕ E (pRound0 E :: pRounds Y.fmt))
    ((none, ()) : Binds ℕ E [pRoundV E Y.A])).trans ?_
  show Err.app (s := (Y.core Ex).shape) (t := (Y.ends Ex).shape)
    ((0, (bindsV (selPl g pl) 0 Y.fmt).err fun _ => 1) : Err (pRound0 E :: pRounds Y.fmt))
    ((0, ()) : Err [pRoundV E Y.A]) = _
  rw [err_bindsV_eq]
  rfl

/-- The list of the larger counts, written out: 1 | for each variable max (φ.n, 1 if placed) | 0. -/
theorem psc_max_counts (Y : PscPar E) (Ex : ExtSpec) (g : ℕ) (pl : ℕ → ℕ) :
    Err.max (Y.err Ex) (pscRiderErr Y Ex g pl) =
      Err.app (s := (Y.core Ex).shape) (t := (Y.ends Ex).shape)
        ((1, maxCounts (placed g pl) 0 Y.fmt) : Err (pRound0 E :: pRounds Y.fmt))
        ((0, ()) : Err [pRoundV E Y.A]) := by
  rw [pscRiderErr_eq]
  refine (Iop.Err.max_app (s := (Y.core Ex).shape) (t := (Y.ends Ex).shape) (Y.errC Ex)
    ((0, riderCounts (placed g pl) 0 Y.fmt) : Err (pRound0 E :: pRounds Y.fmt))
    ((0, ()) : Err [pRoundV E Y.A]) ((0, ()) : Err [pRoundV E Y.A])).trans ?_
  show Err.app (s := (Y.core Ex).shape) (t := (Y.ends Ex).shape)
    ((Nat.max 1 0, Err.max (pErr Y.fmt) (riderCounts (placed g pl) 0 Y.fmt)) :
      Err (pRound0 E :: pRounds Y.fmt)) ((Nat.max 0 0, ()) : Err [pRoundV E Y.A]) = _
  rw [max_pErr_riderCounts]
  rfl

/-! ## 4. Two riders; the safe form; over a signature -/

/-- Two riders on one sumcheck, which may share rounds: the rule on its own result; no number
changed. Warning: A0 is free. Wherever the input joint's `relR` without the rider (a relation that
rides along, or the block's own claim) or the output joint's `relR` already gives the source, this
says nothing (`hollow_own`, `hollow_out`, Cb/G6/Rider/Both.lean; the test of a use stands at
`hollow_own`). -/
theorem psc_our_two_riders (T : PscOur E) (Ex : ExtSpec) (M Wp Kc ι₁ ι₂ : Type)
    (A0 : IOR.Rels Kc T.St Ex (M × Wp)) (msg : M → T.J → E)
    (hV : T.VarsOK) (hX : T.DegX) (hY : T.DegY) (hI : T.ValInj)
    (g₁ : ℕ) (pl₁ : ℕ → ℕ) (hpl₁ : ∀ t < g₁, ∀ t' < g₁, pl₁ t = pl₁ t' → t = t')
    (hlt₁ : ∀ t < g₁, pl₁ t < T.fmt.length)
    (hn₁ : ∀ t < g₁, ∀ φ, T.fmt[pl₁ t]? = some φ → 1 ≤ φ.n) (f₁ : ι₁ → T.St → M → ℕ → E)
    (g₂ : ℕ) (pl₂ : ℕ → ℕ) (hpl₂ : ∀ t < g₂, ∀ t' < g₂, pl₂ t = pl₂ t' → t = t')
    (hlt₂ : ∀ t < g₂, pl₂ t < T.fmt.length)
    (hn₂ : ∀ t < g₂, ∀ φ, T.fmt[pl₂ t]? = some φ → 1 ≤ φ.n) (f₂ : ι₂ → T.St → M → ℕ → E) :
    GoodAt (T.par.psc Ex) (T.par.hon Ex fun w => msg w.1)
      (withRider (withRider (T.baseIn A0 fun w => msg w.1) fun m a => OnCube g₁ f₁ a.1.2 m)
        fun m a => OnCube g₂ f₂ a.1.2 m)
      (withRider (withRider (T.par.baseOut A0 fun w => msg w.1)
        fun m o => AtPoint g₁ pl₁ f₁ T.par.fmt o.1.st o.1.pt m)
        fun m o => AtPoint g₂ pl₂ f₂ T.par.fmt o.1.st o.1.pt m)
      (fun _ _ _ wp => wp) (T.par.nums Ex Kc) := by
  have h1 := psc_our_rider_same T Ex M Wp Kc ι₁ A0 msg hV hX hY hI g₁ pl₁ hpl₁ hlt₁ hn₁ f₁
  have hlen : ∀ t < g₂, pl₂ t < T.par.fmt.length := fun t ht => lt_of_lt_of_le (hlt₂ t ht) (by
    show T.fmt.length ≤ (T.fmt ++ [pDummy E T.DY]).length
    rw [List.length_append]
    exact Nat.le_add_right _ _)
  have h2 := psc_rider_any T.par Ex h1 ((psc_our_ok E T).2 hI) g₂ pl₂ hpl₂ hlen f₂
  rwa [numsMax_eq _ (psc_our_rider_err_le T Ex g₂ pl₂ hlt₂ hn₂)] at h2

/-- The safe form of `psc_our_rider_same`. The source comes in inside the relation A0 that rides
along, and does not come out: the output joint rides over A0 alone and has the target. It is still
an empty use if A0 itself, or the block's own claim, gives the source (`hollow_own`). -/
theorem psc_our_rider_in (T : PscOur E) (Ex : ExtSpec) (M Wp Kc ι : Type)
    (A0 : IOR.Rels Kc T.St Ex (M × Wp)) (msg : M → T.J → E)
    (hV : T.VarsOK) (hX : T.DegX) (hY : T.DegY) (hI : T.ValInj)
    (g : ℕ) (pl : ℕ → ℕ) (hpl : ∀ t < g, ∀ t' < g, pl t = pl t' → t = t')
    (hlt : ∀ t < g, pl t < T.fmt.length) (hn : ∀ t < g, ∀ φ, T.fmt[pl t]? = some φ → 1 ≤ φ.n)
    (f : ι → T.St → M → ℕ → E) :
    GoodAt (T.par.psc Ex) (T.par.hon Ex fun w => msg w.1)
      (T.baseIn (withRider A0 fun m s => OnCube g f s.1 m) fun w => msg w.1)
      (withRider (T.par.baseOut A0 fun w => msg w.1)
        fun m o => AtPoint g pl f T.par.fmt o.1.st o.1.pt m)
      (fun _ _ _ wp => wp) (T.par.nums Ex Kc) :=
  goodAt_conseq (psc_our_rider_same T Ex M Wp Kc ι A0 msg hV hX hY hI g pl hpl hlt hn f)
    (fun _ _ _ h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩) (fun _ _ _ h => h) (fun _ h => h) (fun _ h => h)
    (fun _ _ _ h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩) (fun _ _ h => h) (fun _ => rfl) (fun _ => rfl)

/-- Over a signature of oracle messages, through the library's `sigLift_goodB`: the joints with the
rider go through that lift, and the rider then reads the messages that the statement's oracles
decode to. Nothing is said of any other way to lift. Warning: A0 is free. Wherever the input joint's
`relR` without the rider (a relation that rides along, or the block's own claim) or the output
joint's `relR` already gives the source, this says nothing (`hollow_own`, `hollow_out`,
Cb/G6/Rider/Both.lean; the test of a use stands at `hollow_own`). -/
theorem psc_our_rider_sig (S : Sig E) (T : PscOur E) (E₀ : ExtSpec) (Wp Kc ι : Type)
    (A0 : IOR.Rels Kc T.St E₀ (S.Msg × Wp)) (msg : S.Msg → T.J → E)
    (hV : T.VarsOK) (hX : T.DegX) (hY : T.DegY) (hI : T.ValInj)
    (g : ℕ) (pl : ℕ → ℕ) (hpl : ∀ t < g, ∀ t' < g, pl t = pl t' → t = t')
    (hlt : ∀ t < g, pl t < T.fmt.length) (hn : ∀ t < g, ∀ φ, T.fmt[pl t]? = some φ → 1 ≤ φ.n)
    (f : ι → T.St → S.Msg → ℕ → E) :
    IOR.GoodB ((T.par.psc E₀).keep S.Smp S.ext) (S.liftH (T.par.hon E₀ fun w => msg w.1))
      (S.over (withRider (T.baseIn A0 fun w => msg w.1) fun m a => OnCube g f a.1.2 m))
      (S.over (withRider (T.par.baseOut A0 fun w => msg w.1)
        fun m o => AtPoint g pl f T.par.fmt o.1.st o.1.pt m))
      (fun _ _ w => w) ((T.par.nums E₀ Kc).keep S.Smp S.ext) :=
  sigLift_goodB E S Kc _ _ Wp Wp E₀ E₀ (T.par.psc E₀) _ _ _ _ _
    (psc_our_rider_same T E₀ S.Msg Wp Kc ι A0 msg hV hX hY hI g pl hpl hlt hn f)

/-! ## 5. A reader of the point that compiles -/

section Reader
omit [Field E] [Fintype E]

/-- A point of the variables l, with something of type Tl behind it. -/
def PPtT : List (PFmt E) → Type → Type
  | [], Tl => Tl
  | _ :: l, Tl => E × PPtT l Tl

theorem ppt_app : ∀ (l l' : List (PFmt E)), PPt (l ++ l') = PPtT l (PPt l')
  | [], _ => rfl
  | _ :: l, l' => congrArg (fun A => E × A) (ppt_app l l')

/-- Coordinate i of the first part (0 beyond it). It recurses on l alone; what stands behind is a
type, so it is no value at run time. -/
def ptT [Zero E] : (l : List (PFmt E)) → {Tl : Type} → PPtT l Tl → ℕ → E
  | [], _, _, _ => 0
  | _ :: _, _, γ, 0 => γ.1
  | _ :: l, _, γ, i + 1 => ptT l γ.2 i

theorem cast_pair {A B : Type} (h : A = B) (h2 : (E × A) = (E × B)) (p : E × A) :
    cast h2 p = (p.1, cast h p.2) := by
  subst h
  rfl

theorem ptT_cast [Zero E] : ∀ (l l' : List (PFmt E)) (γ : PPt (l ++ l')) (i : ℕ), i < l.length →
    ptT l (cast (ppt_app l l') γ) i = ptAt (l ++ l') γ i
  | [], _, _, i, h => absurd h (Nat.not_lt_zero i)
  | f :: l, l', γ, 0, _ => congrArg Prod.fst (cast_pair (ppt_app l l') (ppt_app (f :: l) l') γ)
  | f :: l, l', γ, i + 1, h =>
      (congrArg (fun p : E × PPtT l (PPt l') => ptT l p.2 i)
        (cast_pair (ppt_app l l') (ppt_app (f :: l) l') γ)).trans
        (ptT_cast l l' γ.2 i (Nat.lt_of_succ_lt_succ h))

end Reader

/-- A reader of the coordinates of the variables of `T.fmt` in the output statement's point (0 from
`T.fmt.length` on). It is a plain definition: the format of the added last variable, which is
noncomputable in the library, stands in a type and in a proof alone. For a variable record T it
compiles; at a record whose own definition has no compiled code it does not. -/
def ptTrue (T : PscOur E) (o : T.par.Out) (i : ℕ) : E :=
  ptT T.fmt (cast (ppt_app T.fmt [pDummy E T.DY]) o.pt) i

/-- At the rule's places it is `ptAt`. -/
theorem ptTrue_eq (T : PscOur E) (o : T.par.Out) {i : ℕ} (h : i < T.fmt.length) :
    ptTrue T o i = ptAt T.par.fmt o.pt i :=
  ptT_cast T.fmt [pDummy E T.DY] o.pt i h

/-- `psc_our_rider_same` with the target written through `ptTrue`. Warning: A0 is free. Wherever the
input joint's `relR` without the rider (a relation that rides along, or the block's own claim) or
the output joint's `relR` already gives the source, this says nothing (`hollow_own`, `hollow_out`,
Cb/G6/Rider/Both.lean; the test of a use stands at `hollow_own`). -/
theorem psc_our_rider_run (T : PscOur E) (Ex : ExtSpec) (M Wp Kc ι : Type)
    (A0 : IOR.Rels Kc T.St Ex (M × Wp)) (msg : M → T.J → E)
    (hV : T.VarsOK) (hX : T.DegX) (hY : T.DegY) (hI : T.ValInj)
    (g : ℕ) (pl : ℕ → ℕ) (hpl : ∀ t < g, ∀ t' < g, pl t = pl t' → t = t')
    (hlt : ∀ t < g, pl t < T.fmt.length) (hn : ∀ t < g, ∀ φ, T.fmt[pl t]? = some φ → 1 ≤ φ.n)
    (f : ι → T.St → M → ℕ → E) :
    GoodAt (T.par.psc Ex) (T.par.hon Ex fun w => msg w.1)
      (withRider (T.baseIn A0 fun w => msg w.1) fun m a => OnCube g f a.1.2 m)
      (withRider (T.par.baseOut A0 fun w => msg w.1)
        fun m o => ∀ i, ext g (f i o.1.st m) (fun t => ptTrue T o.1 (pl t)) = 0)
      (fun _ _ _ wp => wp) (T.par.nums Ex Kc) :=
  goodAt_congr_rider (fun _ _ => Iff.rfl)
    (fun m o => forall_congr' fun i => by
      rw [ext_congr_point (z := fun t => ptAt T.par.fmt o.1.pt (pl t))
        (z' := fun t => ptTrue T o.1 (pl t)) fun t ht => (ptTrue_eq T o.1 (hlt t ht)).symm])
    (psc_our_rider_same T Ex M Wp Kc ι A0 msg hV hX hY hI g pl hpl hlt hn f)

/-! ## 6. Empty uses at the sumcheck -/

/-- An empty use, written out. If the source rides inside A0, the output joint still holds it, and
the target beside it comes for nothing: at any places pl (they need not be different, nor in range),
with no condition on degrees, from `psc_our_goodAt` alone. Nothing is reduced to the point. -/
theorem hollow_source_kept (T : PscOur E) (Ex : ExtSpec) (M Wp Kc ι : Type)
    (A0 : IOR.Rels Kc T.St Ex (M × Wp)) (msg : M → T.J → E)
    (hV : T.VarsOK) (hX : T.DegX) (hY : T.DegY) (hI : T.ValInj)
    (g : ℕ) (pl : ℕ → ℕ) (f : ι → T.St → M → ℕ → E) :
    GoodAt (T.par.psc Ex) (T.par.hon Ex fun w => msg w.1)
      (T.baseIn (withRider A0 fun m a => OnCube g f a.1 m) fun w => msg w.1)
      (withRider (T.par.baseOut (withRider A0 fun m a => OnCube g f a.1 m) fun w => msg w.1)
        fun m o => AtPoint g pl f T.par.fmt o.1.st o.1.pt m)
      (fun _ _ _ wp => wp) (T.par.nums Ex Kc) :=
  hollow_add (psc_our_goodAt E T Ex M Wp Kc (withRider A0 fun m a => OnCube g f a.1 m) msg
    hV hX hY hI) _ fun _ _ _ hw i => ext_zero_of_forall (hw.1.2 i) _

/-- An empty use. For any A0 whose `rel` and `relR` give the source, however it is written, the very
conclusion of `psc_our_rider_same` follows from `psc_our_goodAt` alone, at any places. (`relR` alone
is enough: `hollow_own`.) -/
theorem hollow_semantic (T : PscOur E) (Ex : ExtSpec) (M Wp Kc ι : Type)
    (A0 : IOR.Rels Kc T.St Ex (M × Wp)) (msg : M → T.J → E)
    (hV : T.VarsOK) (hX : T.DegX) (hY : T.DegY) (hI : T.ValInj)
    (g : ℕ) (pl : ℕ → ℕ) (f : ι → T.St → M → ℕ → E)
    (h1 : ∀ st y w, A0.rel st y w → OnCube g f st w.1)
    (h2 : ∀ a w, A0.relR a w → OnCube g f a.1 w.1) :
    GoodAt (T.par.psc Ex) (T.par.hon Ex fun w => msg w.1)
      (withRider (T.baseIn A0 fun w => msg w.1) fun m a => OnCube g f a.1.2 m)
      (withRider (T.par.baseOut A0 fun w => msg w.1)
        fun m o => AtPoint g pl f T.par.fmt o.1.st o.1.pt m)
      (fun _ _ _ wp => wp) (T.par.nums Ex Kc) :=
  goodAt_conseq
    (hollow_add (psc_our_goodAt E T Ex M Wp Kc A0 msg hV hX hY hI)
      (fun m o => AtPoint g pl f T.par.fmt o.1.st o.1.pt m)
      fun _ _ _ hw i => ext_zero_of_forall (h1 _ _ _ hw.1 i) _)
    (fun _ _ _ h => h.1) (fun _ _ _ h => h) (fun _ h => h) (fun _ h => h)
    (fun _ _ _ h => ⟨h, h2 _ _ h.1⟩) (fun _ _ h => h) (fun _ => rfl) (fun _ => rfl)

end Psc

end Cb.Rider

#print axioms Cb.Rider.psc_out_pt
#print axioms Cb.Rider.ptAt_pG
#print axioms Cb.Rider.psc_rider_any
#print axioms Cb.Rider.psc_rider
#print axioms Cb.Rider.psc_our_rider
#print axioms Cb.Rider.psc_rider_err_le
#print axioms Cb.Rider.psc_our_rider_same
#print axioms Cb.Rider.pscRiderErr_eq
#print axioms Cb.Rider.psc_max_counts
#print axioms Cb.Rider.psc_our_two_riders
#print axioms Cb.Rider.psc_our_rider_in
#print axioms Cb.Rider.psc_our_rider_sig
#print axioms Cb.Rider.ptTrue_eq
#print axioms Cb.Rider.psc_our_rider_run
#print axioms Cb.Rider.hollow_source_kept
#print axioms Cb.Rider.hollow_semantic
