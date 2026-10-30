-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K06Bears.lean: the errors that the law of the output head's own rounds asks a
piece to bear (ErrBears at the ceiling priceAt: Johnson/Desc/Sound/RuleAtKit.lean) are borne by a
row that is below 2^-128 a round; and so by the cap's own row.

It holds at every list ds of written rounds (TypedOracleCompiler.Run.PQ.RD) whose entries are the planner's
for the head's own rounds (OnBytes.Tie.Pv.Head.headOwnList w (recAt lt lPd)), for 1 <= lt <= 2 ^ 60,
at every number w of bits of work.

What the file holds.
  nElems_dsOf      a round whose kind is neither seeds nor sealed draws drawE elements, where
                   drawNZ <= drawE.
  tail_small       behind the first round, at every pair of k6Priced: logN <= 64; drawNZ <= drawE
                   <= 1; no position and no matrix entry is drawn; the count is at most 8.
  k6Names, name_mem, names_all_fit, kinds_fit, kinds_of_names   every round has one of seven names;
                   each of the seven has a kind that is neither seeds nor sealed. So the premise on
                   the kinds follows where each round's kind is the kind of its entry's name.
  needK6           the numbers asked: kitK ds j * (priceAt p j * kitFs .two ds j).
  k06Bears         **the row errOf (Johnson/Desc/Kinds/Law/BearsBelow.lean) bears them; it is below
                   2^-128 a round; and it is nowhere above Err.cap 128 _.**
  k06BearsCap      **the cap's own row, Err.cap 128 (uL (ckP .two) ds), bears them.**
  k06BearsCapNames the same, with the premise on the kinds traded for "each round's kind is its
                   name's".
  Cond.spends_bears, Cond.spends_bearsCap   the same from the condition on public numbers K06Cond
                   (Johnson/Desc/Kinds/Law/K06Condition.lean), at the parameters parOf h work.
Who calls it. Johnson/Desc/Kinds/Law/K6PiecePays.lean, at ds := toRDs p.ds of a piece p.

The letters. No statement has a "there is": the row is a function of ds and of the numbers asked. w
is read by the premise on ds's entries alone: it is the entries' work; nothing is asked of it.

What it does not show. (1) That a piece's own err is this row: p.err is the piece's maker's: whoever
builds the piece lays errOf there, or a row that is nowhere smaller (BearsBelow.lean: bears_mono).
(2) No sum over the rounds: 128 bits a round; nothing on 124 for the whole. (3) The pin of the cells
and the mask row in front of the draws: owed elsewhere. (4) It holds for 1 <= lt <= 2 ^ 60, at every
work. (5) That ds's entries are the planner's is a premise; so is that no round's kind is seeds or
sealed, which follows from the first where each round's kind is that of its entry's name
(kinds_of_names). K6PiecePays.lean pays the first for written rounds that are the seated block's
declared rounds; THAT A REAL PIECE's ds MEETS IT (and lays its kinds so) IS SHOWN NOWHERE YET. The
field is .two alone. Nothing on soundness by itself.

-/
import Johnson.Desc.Kinds.Law.BearsBelow
import Johnson.Desc.Kinds.Law.K06BelowSpent

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law.Bears

open VerifiableInference.Desc.Sound (ErrBears kitK kitFs kitF nElems isElem)
open TypedOracleCompiler.Run.PQ (uL RD)
open _root_.Iop (Err)
open Johnson.Bridge (KindFits)
open OnBytes.Tie.Pv.Lay (eDraw eBat)
open Below (k6Priced sumPriced k6Priced_entries k6Priced_counts q)
open Prices (prices recAt)
open Norm (lt lPd)
open scoped ENNReal

theorem nElems_append : ∀ a b : List Fmt.Draw, nElems (a ++ b) = nElems a + nElems b
  | [], b => by simp [nElems]
  | d :: a, b => by
    show (if isElem d then 1 else 0) + nElems (a ++ b) =
      (if isElem d then 1 else 0) + nElems a + nElems b
    rw [nElems_append a b, Nat.add_assoc]

theorem nElems_replicate (n : ℕ) (d : Fmt.Draw) :
    nElems (List.replicate n d) = if isElem d then n else 0 := by
  induction n with
  | zero => simp [nElems]
  | succ n ih =>
    rw [List.replicate_succ]
    show (if isElem d then 1 else 0) + nElems (List.replicate n d) = _
    rw [ih]
    split <;> omega

/-- A round whose kind is neither seeds nor sealed draws drawE elements. -/
theorem nElems_dsOf (e : Fmt.Entry) (k : Fmt.Kind) (hk : KindFits false k)
    (hnz : e.drawNZ ≤ e.drawE) : nElems (Fmt.dsOf e k) = e.drawE := by
  unfold Fmt.dsOf Fmt.dsElems
  rw [if_neg hk.1, if_neg hk.2, nElems_append, nElems_append, nElems_append, nElems_replicate,
    nElems_replicate, nElems_replicate]
  simp [nElems, isElem]
  omega

/-- What is asked of an entry with its count. -/
structure Small (w : ℕ) (x : Fmt.Entry × ℕ) : Prop where
  log : x.1.logN ≤ 64
  nz : x.1.drawNZ ≤ x.1.drawE
  poss : x.1.poss = 0
  trits : x.1.trits = 0
  one : x.1.drawE ≤ 1
  cnt : x.2 ≤ 8

theorem sum_small (b m ends w : ℕ) (x : Fmt.Entry × ℕ) (hx : x ∈ sumPriced b m ends w) :
    Small w x := by
  simp only [sumPriced, List.mem_cons, List.mem_append, List.mem_replicate, List.not_mem_nil,
    or_false] at hx
  rcases hx with rfl | ⟨_, rfl⟩ | rfl | rfl <;>
    exact ⟨by simp [eDraw], by simp [eDraw], by simp [eDraw], by simp [eDraw], by simp [eDraw],
      by norm_num⟩

/-- Behind the point every pair is small. -/
theorem tail_small (lt lPd w : ℕ) (x : Fmt.Entry × ℕ) (hx : x ∈ (k6Priced lt lPd w).tail) :
    Small w x := by
  simp only [k6Priced, List.tail_cons, List.mem_cons, List.mem_append] at hx
  rcases hx with rfl | hx | rfl | rfl | hx | hx | hx
  · exact ⟨by simp [eBat], by simp [eBat], by simp [eBat], by simp [eBat], by simp [eBat],
      by norm_num⟩
  · exact sum_small _ _ _ w x hx
  · exact ⟨by simp [eDraw], by simp [eDraw], by simp [eDraw], by simp [eDraw], by simp [eDraw],
      by norm_num⟩
  · exact ⟨by simp [eBat], by simp [eBat], by simp [eBat], by simp [eBat], by simp [eBat],
      by norm_num⟩
  · exact sum_small _ _ _ w x hx
  · exact sum_small _ _ _ w x hx
  · exact sum_small _ _ _ w x hx

/-- The kind of a name, if it has one, is neither seeds nor sealed: as a test with code. -/
def fitB (n : String) : Bool := (Fmt.kindOf n).all fun k => k != .seeds && k != .sealed

theorem fit_of {n : String} {k : Fmt.Kind} (h : fitB n = true) (hk : Fmt.kindOf n = some k) :
    KindFits false k := by
  unfold fitB at h
  rw [hk] at h
  simpa using h

/-- The seven names of the head's own rounds. -/
def k6Names : List String :=
  ["ZERO", "BAT-sigma", "PSC epsilon", "PSC round", "PSC Y", "PSC values", "LINE"]

theorem names_all_fit : ∀ n ∈ k6Names, fitB n = true := by decide

theorem sum_name (b m ends w : ℕ) (x : Fmt.Entry × ℕ) (hx : x ∈ sumPriced b m ends w) :
    x.1.name ∈ k6Names := by
  simp only [sumPriced, List.mem_cons, List.mem_append, List.mem_replicate, List.not_mem_nil,
    or_false] at hx
  rcases hx with rfl | ⟨_, rfl⟩ | rfl | rfl <;> simp [k6Names, eDraw]

/-- **Every round has one of the seven names.** -/
theorem name_mem (lt lPd w : ℕ) (x : Fmt.Entry × ℕ) (hx : x ∈ k6Priced lt lPd w) :
    x.1.name ∈ k6Names := by
  simp only [k6Priced, List.mem_cons, List.mem_append] at hx
  rcases hx with rfl | rfl | hx | rfl | rfl | hx | hx | hx
  · simp [k6Names, eDraw]
  · simp [k6Names, eBat]
  · exact sum_name _ _ _ w x hx
  · simp [k6Names, eDraw]
  · simp [k6Names, eBat]
  · exact sum_name _ _ _ w x hx
  · exact sum_name _ _ _ w x hx
  · exact sum_name _ _ _ w x hx

/-- **The rounds' names have fitting kinds.** -/
theorem kinds_fit (lt lPd w : ℕ) (x : Fmt.Entry × ℕ) (hx : x ∈ k6Priced lt lPd w) :
    fitB x.1.name = true :=
  names_all_fit _ (name_mem lt lPd w x hx)

/-- So the premise on the kinds follows where each round's kind is the kind of its entry's name. -/
theorem kinds_of_names (lt lPd w : ℕ) (ds : List RD)
    (hE : ds.map (·.entry) = OnBytes.Tie.Pv.Head.headOwnList w (recAt lt lPd))
    (hn : ∀ d ∈ ds, Fmt.kindOf d.entry.name = some d.kind) : ∀ d ∈ ds, KindFits false d.kind := by
  intro d hd
  have h1 : d.entry ∈ (k6Priced lt lPd w).map (·.1) := by
    rw [k6Priced_entries, ← hE]
    exact List.mem_map_of_mem hd
  obtain ⟨x, hx, hxe⟩ := List.mem_map.1 h1
  exact fit_of (by rw [← hxe]; exact kinds_fit lt lPd w x hx) (hn d hd)

theorem room (n : ℕ) (hn : n ≤ 2 ^ 60) : n * 2 ^ 129 ≤ Fmt.Fld.two.p ^ 3 - 1 := by
  have h1 : n * 2 ^ 129 ≤ 2 ^ 60 * 2 ^ 129 := Nat.mul_le_mul_right _ hn
  have h2 : (2 : ℕ) ^ 60 * 2 ^ 129 ≤ Fmt.Fld.two.p ^ 3 - 1 := by decide
  exact le_trans h1 h2

/-- The numbers that the rule at the kit asks the piece to bear, at the ceiling priceAt p. -/
def needK6 (p : Par) (ds : List RD) (j : ℕ) : ℕ := kitK ds j * (priceAt p j * kitFs .two ds j)

/-- **The row bears the numbers asked, and is below 2^-128 a round.** -/
def K06Bears : Prop :=
  ∀ (p : Par) (w : ℕ) (ds : List RD),
    (letI := p.sizes; 1 ≤ lt) → (letI := p.sizes; lt ≤ 2 ^ 60) →
    (letI := p.sizes; ds.map (·.entry) = OnBytes.Tie.Pv.Head.headOwnList w (recAt lt lPd)) →
    (∀ d ∈ ds, KindFits false d.kind) →
    ErrBears (_root_.Run.ckP .two) (fun j => kitK ds j * (priceAt p j * kitFs .two ds j)) ds 0
        (errOf (_root_.Run.ckP .two) (needK6 p ds) ds 0) ∧
      Err.Below (errOf (_root_.Run.ckP .two) (needK6 p ds) ds 0) ((2 : ℝ≥0∞)⁻¹ ^ 128) ∧
      Err.le (errOf (_root_.Run.ckP .two) (needK6 p ds) ds 0) (Err.cap 128 _)

theorem k06Bears : K06Bears := by
  intro p w ds h1 h2 hE hk
  letI := p.sizes
  have hb : Err.Below (errOf (_root_.Run.ckP .two) (needK6 p ds) ds 0) ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
    refine errOf_below _ _ _ ds 0 fun i d hd => ?_
    rw [Nat.zero_add]
    have e : needK6 p ds i = nElems (Fmt.dsOf d.entry d.kind) * priceAt p i * kitF .two d := by
      unfold needK6 kitK kitFs
      rw [hd]
      exact (Nat.mul_assoc _ _ _).symm
    rw [e]
    have hkd := hk d (List.mem_of_getElem? hd)
    have hent : (OnBytes.Tie.Pv.Head.headOwnList w (recAt lt lPd))[i]? = some d.entry := by
      rw [← hE, List.getElem?_map, hd]
      rfl
    rw [← k6Priced_entries, List.getElem?_map] at hent
    obtain ⟨x, hx, hxe⟩ := Option.map_eq_some_iff.1 hent
    cases i with
    | zero =>
      have hx0 : x = (eDraw "ZERO" w 0 lt, lt * q ^ (lt - 1)) := by
        simpa [k6Priced] using hx.symm
      have hde : d.entry = eDraw "ZERO" w 0 lt := by rw [← hxe, hx0]
      have hp : priceAt p 0 ≤ 1 := by
        refine le_trans (Nat.min_le_right _ _) ?_
        unfold Came.tightAt
        rw [if_pos rfl]
      have hnz : d.entry.drawNZ ≤ d.entry.drawE := by rw [hde]; simp [eDraw]
      have hlog : d.entry.logN ≤ 64 := by rw [hde]; simp [eDraw]
      refine kit_below d _ hlog (blocks_small d.entry d.kind hlog (by rw [hde]; simp [eDraw])
        (by rw [hde]; simp [eDraw]; exact h2) hnz (by rw [hde]; simp [eDraw])) ?_
      refine room _ ?_
      rw [nElems_dsOf _ _ hkd hnz, hde]
      calc (eDraw "ZERO" w 0 lt).drawE * priceAt p 0 ≤ lt * 1 := Nat.mul_le_mul (by simp [eDraw]) hp
        _ ≤ 2 ^ 60 := by rw [Nat.mul_one]; exact h2
    | succ i =>
      have hxt : x ∈ (k6Priced lt lPd w).tail := by
        refine List.mem_of_getElem? (i := i) ?_
        rw [List.getElem?_tail]
        exact hx
      have S := tail_small lt lPd w x hxt
      have hcnt : ((k6Priced lt lPd w).map (·.2))[i + 1]? = some x.2 := by
        rw [List.getElem?_map, hx]
        rfl
      rw [k6Priced_counts, List.getElem?_cons_succ, List.getElem?_tail] at hcnt
      have hv : (prices lt lPd).getD (i + 1) 0 = x.2 := by
        rw [List.getD_eq_getElem?_getD, hcnt]
        rfl
      have hp : priceAt p (i + 1) ≤ 8 :=
        le_trans (priceAt_le p p.policy ⟨fun _ => 0, 0, 0⟩ ⟨0⟩ h1 (i + 1)) (hv ▸ S.cnt)
      have hnz : d.entry.drawNZ ≤ d.entry.drawE := by rw [← hxe]; exact S.nz
      have hone : d.entry.drawE ≤ 1 := by rw [← hxe]; exact S.one
      have hlog : d.entry.logN ≤ 64 := by rw [← hxe]; exact S.log
      refine kit_below d _ hlog (blocks_small d.entry d.kind hlog
        (by rw [← hxe, S.poss]; exact Nat.zero_le _)
        (le_trans hone (by norm_num)) hnz (by rw [← hxe, S.trits]; exact Nat.zero_le _)) ?_
      refine room _ ?_
      rw [nElems_dsOf _ _ hkd hnz]
      calc d.entry.drawE * priceAt p (i + 1) ≤ 1 * 8 := Nat.mul_le_mul hone hp
        _ ≤ 2 ^ 60 := by norm_num
  exact ⟨errOf_bears _ _ ds 0, hb, Err.le_cap_of_below_inv 128 _ hb⟩

/-- **The cap's own row bears them.** -/
theorem k06BearsCap (p : Par) (w : ℕ) (ds : List RD) (h1 : letI := p.sizes; 1 ≤ lt)
    (h2 : letI := p.sizes; lt ≤ 2 ^ 60)
    (hE : letI := p.sizes; ds.map (·.entry) = OnBytes.Tie.Pv.Head.headOwnList w (recAt lt lPd))
    (hk : ∀ d ∈ ds, KindFits false d.kind) :
    ErrBears (_root_.Run.ckP .two) (fun j => kitK ds j * (priceAt p j * kitFs .two ds j)) ds 0
      (Err.cap 128 (uL (_root_.Run.ckP .two) ds)) :=
  have H := k06Bears p w ds h1 h2 hE hk
  bears_mono _ _ ds 0 _ _ H.2.2 H.1

/-- The same, each round's kind being its entry's name's. -/
theorem k06BearsCapNames (p : Par) (w : ℕ) (ds : List RD) (h1 : letI := p.sizes; 1 ≤ lt)
    (h2 : letI := p.sizes; lt ≤ 2 ^ 60)
    (hE : letI := p.sizes; ds.map (·.entry) = OnBytes.Tie.Pv.Head.headOwnList w (recAt lt lPd))
    (hn : ∀ d ∈ ds, Fmt.kindOf d.entry.name = some d.kind) :
    ErrBears (_root_.Run.ckP .two) (fun j => kitK ds j * (priceAt p j * kitFs .two ds j)) ds 0
      (Err.cap 128 (uL (_root_.Run.ckP .two) ds)) :=
  letI := p.sizes
  k06BearsCap p w ds h1 h2 hE (kinds_of_names lt lPd w ds hE hn)

end VerifiableInference.Desc.Kinds.Head.Law.Bears

namespace VerifiableInference.Desc.Kinds.Head.Law.Cond

open VerifiableInference.Desc.Sound (ErrBears kitK kitFs)
open TypedOracleCompiler.Run.PQ (RD)
open OnBytes.Model.Head (Shape Border)
open _root_.Iop (Err)
open Johnson.Bridge (KindFits)
open Prices (recAt)
open Norm (lt lPd)
open scoped ENNReal

/-- **From the condition on public numbers**, at the place's own parameters parOf h work. -/
theorem spends_bears {h : Shape} {b : Border} {work inst : Nat} {reads : Option Nat}
    (C : K06Cond h b work inst reads) (ds : List RD)
    (hE : letI := sizesOf h; ds.map (·.entry) = OnBytes.Tie.Pv.Head.headOwnList work (recAt lt lPd))
    (hk : ∀ d ∈ ds, KindFits false d.kind) :
    ErrBears (_root_.Run.ckP .two)
        (fun j => kitK ds j * (priceAt (parOf h work) j * kitFs .two ds j)) ds 0
        (Bears.errOf (_root_.Run.ckP .two) (Bears.needK6 (parOf h work) ds) ds 0) ∧
      Err.Below (Bears.errOf (_root_.Run.ckP .two) (Bears.needK6 (parOf h work) ds) ds 0)
        ((2 : ℝ≥0∞)⁻¹ ^ 128) ∧
      Err.le (Bears.errOf (_root_.Run.ckP .two) (Bears.needK6 (parOf h work) ds) ds 0)
        (Err.cap 128 _) :=
  Bears.k06Bears (parOf h work) work ds C.point
    (le_trans (admitted_lt h C.admitted) (by norm_num)) hE hk

theorem spends_bearsCap {h : Shape} {b : Border} {work inst : Nat} {reads : Option Nat}
    (C : K06Cond h b work inst reads) (ds : List RD)
    (hE : letI := sizesOf h; ds.map (·.entry) = OnBytes.Tie.Pv.Head.headOwnList work (recAt lt lPd))
    (hk : ∀ d ∈ ds, KindFits false d.kind) :
    ErrBears (_root_.Run.ckP .two)
        (fun j => kitK ds j * (priceAt (parOf h work) j * kitFs .two ds j)) ds 0
      (Err.cap 128 (TypedOracleCompiler.Run.PQ.uL (_root_.Run.ckP .two) ds)) :=
  Bears.k06BearsCap (parOf h work) work ds C.point
    (le_trans (admitted_lt h C.admitted) (by norm_num)) hE hk

end VerifiableInference.Desc.Kinds.Head.Law.Cond

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Bears.k06Bears
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Cond.spends_bears
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Bears.k06BearsCap
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Bears.k06BearsCapNames
