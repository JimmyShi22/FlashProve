-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/FourRunsCell.lean: THE HEAD's HALF OF THE EXCHANGE AT THE SENDING OF THE
HEAD's READS, AT THE HEAD's FOUR RUNS "norm", "policy", "logits", "join": the form ArmCellIn
(Johnson/Desc/Sound/StatedCellIn.lean): at every entry that a form of the run names, the committed
cell, read behind the sending, is the head's stated function at the verifier's state in front.
Statements and proofs. The like at the run "planes": Law/PlanesCell.lean, whose pattern and tools
(EntsAt and its rules) are used here.

WHAT IT IS NOT. Implications. Nothing on soundness. No values are shown at which the premises hold
together. armCellIn_four's premise hOurs (the twelve tables' entries in the world of the committed
data are the reads in truth of some cells c1 that agree with the arm's cells inside the ranges) is
near its conclusion: what that theorem pays is the walk over the 35 forms and the six key vectors,
the unfolding of the stated function, and the step from c1 to the arm's cells. armCellIn_K6 moves
the content into three NAMED premises, none shown here (Law/FourRunsTie.lean has the second and the
third from the tie of the approximate range proof):
  hRun   the run's points and vectors are the kind's letters (Law/TwelveOurs.lean: RunIs), at the
         verifier's state with the tables laid;
  hTw    the twelve tables' entries in the world of the committed data behind the sending are the
         sums at the run's own weights over the cells c1 (Law/TieReads.lean: TwelveTrue);
  hSame  c1 agrees with the integer cells made of the data in front, inside the ranges that the
         head's relation names (Law/CellsAlike.lean: SameCells).
WHY c1. The arm's cells (Law/CellsOfData.lean) are cut to four ranges; the integers of which the
tie speaks are not: see Law/FourRunsTie.lean's head.
The other premises: K6States (which runs stand under the four names) · hRd (the reader is k6Silent:
Law/K6Silent.lean's readers_silent has it where no tables are laid) · hok (the tests on the list of
rounds' numbers) · hT (K6HeardAt: Law/K6RecordPaid.lean's heardAt_of_below has it behind the
sub-protocol's accept) · hbare (the lookup's last claim names no entry) · harr (the two parts have
one list of arrays: a premise of the exchange itself) · hwide (the reads' array is as wide as
planned) · hla (a public number).

  nameN_is, nameH_is   two spellings of a read's table's name are one.
  kept2_ents, kept_ents   EntsAt Q is kept by the forms' arithmetic.
  entsAt_entry     the form at a position below the width names that one place in row 0.
  long_congr, short_congr, readAt_same, readAtN_same   below its length a read in truth reads no
                   cell beyond the ranges: two structures of cells that agree there give one read.
  EntriesAt Q N R  below each read's length the filling's entry names places of which Q holds.
  claims_ents, keyVector_ents   so do the 35 forms and the key vectors (Law/AlikeWorth.lean's walk).
  armCellIn_four   general in the stated function's letters: see its docstring.
  armCellIn_K6     MAIN: at uHeadK6 X 24 (Law/StatedHeadArm.lean): see its docstring.

LETTERS. No letter stands under "there is" in the two tops' conclusions. In hOurs: Rn: pinned by
Rn.t = tt and Rn.iU3 = readsOf W (OursTrue reads these two fields alone); c1: tied by OursTrue and
SameCells. In hRun: o, cov, x, t: pinned by the five equations. l, piece: read by K6States alone.
In armCellIn_K6 c1 is the caller's letter: read by hTw and hSame.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.PlanesCell
import Johnson.Desc.Kinds.Law.TwelveOurs
import Johnson.Desc.Kinds.Law.StatedHeadArm
import Johnson.Desc.Kinds.Law.K6RecordPaid
import Johnson.Desc.Kinds.Law.CellsAlike
import Johnson.Desc.Kinds.Law.FromLookup

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE oneE)
open OnBytes.Model (Fork Aff Ent World Reading HTree)
open OnBytes.Model.Verify (borderOf)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.K9 (Readers readerOf segAt? RunOf)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (worldOwn dataQ)
open Norm (lt ls d lPd T S2)

theorem nameN_is (r : FinalNorm.Read) : nameN r = nameOfN r := by cases r <;> rfl

theorem nameH_is (r : Read) : nameH r = nameOf r := by cases r <;> rfl

theorem kept2_ents (Q : Nat → Nat → Nat → Prop) : Kept2 fun _ f' => EntsAt Q f' :=
  { addMul := fun k ha hb => entsAt_addMul ha hb k
    bare := fun _ h => entsAt_of_empty Q h }

theorem kept_ents (Q : Nat → Nat → Nat → Prop) : Kept (EntsAt Q) :=
  { addMul := fun k ha hb => entsAt_addMul ha hb k
    bare := fun _ h _ => entsAt_of_empty Q h }

/-- The form at a position below the width names that one place in row 0. -/
theorem entsAt_entry {Q : Nat → Nat → Nat → Prop} {iU3 K3 pos : Nat} (hlt : pos < K3)
    (h : Q iU3 0 pos) : EntsAt Q (entryAt iU3 K3 pos) := by
  intro y hy
  unfold entryAt at hy
  rw [Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt] at hy
  obtain rfl : y = { tree := iU3, row := 0, idx := pos, coef := oneE } := by
    simpa [Aff.ent] using hy
  exact h

section Same

variable [Sizes]

/-- An entry of a read under long weights reads its S2 features, at the positions below T. -/
theorem long_congr (f g : Nat → E) (x x' : Nat → Nat → Int) (i : Nat)
    (h : ∀ j t, j < S2 → t < T → x (S2 * i + j) t = x' (S2 * i + j) t) :
    (sumTo S2 fun j => sumTo T fun t => f j * g t * ofInt (x (S2 * i + j) t)) =
      sumTo S2 fun j => sumTo T fun t => f j * g t * ofInt (x' (S2 * i + j) t) :=
  Came.sumTo_congr S2 fun j hj => Came.sumTo_congr T fun t ht => by rw [h j t hj ht]

/-- A read under short weights reads its feature, at the positions below T. -/
theorem short_congr (g : Nat → E) (x x' : Nat → Nat → Int) (i : Nat)
    (h : ∀ t, t < T → x i t = x' i t) :
    (sumTo T fun t => g t * ofInt (x i t)) = sumTo T fun t => g t * ofInt (x' i t) :=
  Came.sumTo_congr T fun t ht => by rw [h t ht]

end Same

section SameReads

variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In] [Norm.Heard] [FinalNorm.Heard]
  [Heard]

/-- **Below its length a read of the head's five reads no cell beyond the ranges.** -/
theorem readAt_same {c c' : NCells} (h : SameCells c c') (r : Read) (i : Nat)
    (hi : i < readLen r) : readAt c.toCells r.of i = readAt c'.toCells r.of i := by
  cases r with
  | wideAtKeys => exact long_congr _ _ _ _ i fun j t hj ht => h.wide _ t (block_lt hi hj) ht
  | wideAtCosts => exact long_congr _ _ _ _ i fun j t hj ht => h.wide _ t (block_lt hi hj) ht
  | actAtLogits => exact short_congr _ _ _ i fun t ht => h.act i t hi ht
  | rowAtCosts => exact short_congr _ _ _ i fun t ht => h.row i t hi ht
  | rowCount => exact short_congr _ _ _ i fun t ht => h.row i t hi ht

/-- **The like for the normalization's seven.** -/
theorem readAtN_same {c c' : NCells} (h : SameCells c c') (r : FinalNorm.Read) (i : Nat)
    (hi : i < readLenN r) : readAtN c r.of i = readAtN c' r.of i := by
  cases r with
  | streamAtSquares =>
    exact long_congr _ _ _ _ i fun j t hj ht => h.stream _ t (block_lt hi hj) ht
  | streamAtNormed =>
    exact long_congr _ _ _ _ i fun j t hj ht => h.stream _ t (block_lt hi hj) ht
  | actAtKeys => exact short_congr _ _ _ i fun t ht => h.act i t hi ht
  | rowAtKeys => exact short_congr _ _ _ i fun t ht => h.row i t hi ht
  | rowAtPV =>
    exact short_congr _ _ _ i fun t ht =>
      h.row i t (Nat.lt_of_lt_of_le hi (Nat.le_add_right _ _)) ht
  | rowAtProducts =>
    exact short_congr _ _ _ i fun t ht =>
      h.row i t (Nat.lt_of_lt_of_le hi (Nat.le_add_right _ _)) ht
  | rowAtNormed =>
    exact short_congr _ _ _ i fun t ht =>
      h.row i t (Nat.lt_of_lt_of_le hi (Nat.le_add_right _ _)) ht

end SameReads

section Walk

variable [Sizes] [Policy] [Request] [Token] [FinalNorm.In] [In] [Norm.Heard] [FinalNorm.Heard]
  [Heard]

/-- **Below each read's length the filling's entry names places of which Q holds.** -/
structure EntriesAt (Q : Nat → Nat → Nat → Prop) (N : FinalNorm.Reads) (R : Reads) : Prop where
  norm : ∀ r i, i < readLenN r → EntsAt Q (N.entry r i)
  wide : ∀ i, i < wideLenN → EntsAt Q (N.wide i)
  head : ∀ r i, i < readLen r → EntsAt Q (R.entry r i)

variable {Q : Nat → Nat → Nat → Prop} {N : FinalNorm.Reads} {R : Reads}

/-- The 35 forms. -/
theorem claims_ents (A : EntriesAt Q N R) (B : HeardBare) (hd : S2 ∣ d) :
    ∀ name fs, (claimsAt N R).lookup name = some fs → ∀ f, f ∈ fs → EntsAt Q f := by
  intro name fs hl f hf
  obtain ⟨_, _, _, _, h⟩ := alike_claims (kept2_ents Q) N N R R A.norm A.head hd
    (heardAlike_of_bare (kept2_ents Q) B) (fun S0 => entsAt_of_empty Q (B.lgLeft S0))
    (entsAt_of_empty Q B.lgEnd) name fs hl f hf
  exact h

/-- A call's key vector. -/
theorem keyVector_ents (A : EntriesAt Q N R) (B : HeardBare) (hd : S2 ∣ d) (hJ : JVa ≤ JV)
    (padding : E) (keys : List PlaceKey) :
    EntsAt Q (letI := N; letI := R; keyVector key padding keys) := by
  unfold keyVector
  have step : ∀ (l : List Form) (a : Form), EntsAt Q a → (∀ f ∈ l, EntsAt Q f) →
      EntsAt Q (l.foldl (· + ·) a) := by
    intro l
    induction l with
    | nil => intro a ha _; exact ha
    | cons x xs ih =>
      intro a ha hl
      exact ih _ (entsAt_addMul ha (hl x List.mem_cons_self) _)
        fun f hf => hl f (List.mem_cons_of_mem _ hf)
  refine step _ _ (entsAt_of_empty Q rfl) fun f hf => ?_
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hf
  cases k with
  | inl k =>
    exact alikeN_key (kept2_ents Q) N N A.norm A.wide hd
      (heardAlike_of_bare (kept2_ents Q) B) k
  | inr k => exact rel_key (kept2_ents Q) R R A.head hJ (entsAt_of_empty Q B.lgClaimed) k

end Walk

/-- **THE HEAD's HALF OF THE EXCHANGE AT THE HEAD's FOUR RUNS, general in the stated function's
letters.** s, a: the verifier's state in front of the sending of the reads, and its part; b: the
part behind it. Where the twelve tables' entries in the world of the committed data behind the
sending are the reads in truth of cells that agree, inside the ranges, with the cells made of the
data in front (hOurs): at every entry that a form of the run names the committed cell is statedAll
at the state in front. -/
theorem armCellIn_four (W : OnBytes.Model.Verify.Public) (P : K8.ReadsQuiet.PH) (l piece blk : Nat)
    (states : Nat → List (RunOf S))
    (KS : K6States W.hS (readsOf W) (parOf W.hS (workOf W)) l piece states blk)
    (Rd : Readers) (own own' : List (Nat × Nat)) (s : S) (a b : K9.Part)
    (rdW : Nat × Nat → Sound.MsgQ)
    (hRd : ∀ name, K6Name name → Rd.forms blk name s = k6Silent P states blk name s)
    (hok : (parOf W.hS (workOf W)).ok = true)
    (hT : K6HeardAt W.hS (readsOf W) (parOf W.hS (workOf W)) s)
    (hbare : ∀ gk, s.lookHeard? = some gk → gk.cEnd.ents = #[])
    (cells : S → Bound K → NCells) (lm : Nat) (nuL : S → Bound K → _root_.Fo.Pl → K)
    (harr : b.L.arrayOf = a.L.arrayOf)
    (hwide : ∀ e F tr, withTables P s = some e → e.fork? = some F →
      F.trees[readsOf W]? = some tr → P.hp.nU.getD 2 0 ≤ tr.K)
    (hOurs : ∀ e v o tt F tr, withTables P s = some e →
      lettersAt (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) e = .ok v →
      e.here = .head o → o.t = some tt → e.fork? = some F → F.trees[readsOf W]? = some tr →
      ∃ (Rn : OnBytes.Model.Head.Run) (c1 : NCells), Rn.t = tt ∧ Rn.iU3 = readsOf W ∧
        (letI := v.1
         letI := v.2.1
         OursTrue (worldOwn b [] (dataQ own' b rdW)) Rn tr.K c1 ∧
           SameCells c1 (cells s (dataQ own a rdW))))
    (name : String) (hn : K6Name name) :
    Sound.ArmCellIn Rd own own' blk name s a b rdW (statedAll W P cells lm nuL) := by
  intro R hR f hf x hx _ c hc _
  obtain ⟨g, H, F0, G, rs, hg, hH, hW0, hh, hLt⟩ := hT
  have hB := heardBare_of_hear hW0 hh
  rw [hRd name hn] at hR
  obtain ⟨e, he, hRe⟩ := Option.bind_eq_some_iff.mp hR
  have hse := front_withTables he
  -- the equation, as a property of a place
  let Q : Nat → Nat → Nat → Prop := fun tree row idx =>
    ∀ c : Nat × String, a.L.arrayOf[tree]? = some c →
      (dataQ own' b rdW).cell c.1 c.2 row idx =
        statedAll W P cells lm nuL s (dataQ own a rdW) c row idx
  -- the entries of the thirteen readers
  have entries : ∀ v, lettersAt (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) e = .ok v →
      (letI := v.1
       letI := v.2.1
       EntriesAt Q v.2.2.final v.2.2.head) := by
    intro v hv
    obtain ⟨g', bh, pl⟩ := v
    obtain ⟨H', y, k1, _, k3, k4⟩ := lettersAt_ok W.hS (readsOf W) (parOf W.hS (workOf W)) hv
    obtain ⟨o, F, tt, tr, ho, hF, ht, htr, _, a1, a2, a3⟩ := reads_are W.hS (readsOf W) e y k3
    obtain ⟨w1, w2⟩ := reads_within W.hS (readsOf W) e y k3 tt o ho ht
    have hAp := tabsApart_at P s e o tt he ho ht
    have hBe := below_of_width P s (readsOf W) hwide e o tt F tr he ho ht hF htr
    obtain ⟨Rn, c1, hRt, hRi, HO, hSm⟩ := hOurs e (g', bh, pl) o tt F tr he hv ho ht hF htr
    have k1' : given (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) e = .ok g' := k1
    have epl : pl = ⟨y.1, y.2⟩ := by
      have := congrArg (fun w : Given × Behind × Places => w.2.2) k4
      exact this
    -- one entry
    have one : ∀ (nm : String) (t : String × Nat × Nat) (i : Nat) (val : Nat → E),
        NoPlane nm → tt.tab.find? (fun e => e.1 == nm) = some t → firstOf tt nm = t.2.1 →
        i < t.2.2 → EntryIs (worldOwn b [] (dataQ own' b rdW)) Rn tr.K nm val →
        truthOf (g', bh, pl) (cells s (dataQ own a rdW)) nm i = val i →
        EntsAt Q (entryAt (readsOf W) tr.K (firstOf tt nm + i)) := by
      intro nm t i val hnp hfind hfirst hi hE htv
      have hm : t ∈ tt.tab := List.mem_of_find?_eq_some hfind
      have hlt : t.2.1 + i < tr.K := by
        have := hBe t hm
        omega
      have hname : t.1 = nm := by
        have := List.find?_some hfind
        simpa using this
      rw [hfirst]
      refine entsAt_entry hlt ?_
      intro c' hc'
      have hS : OnBytes.Road.Hd.Starts Rn nm t.2.1 := by
        unfold OnBytes.Road.Hd.Starts
        rw [hRt, hfind]
        rfl
      have hV : OnBytes.Road.Hd.Valid Rn t.2.1 i := by
        unfold OnBytes.Road.Hd.Valid
        rw [hRt]
        exact List.any_eq_true.2 ⟨t, hm, by simp [hi]⟩
      have h1 := hE t.2.1 hS i hV
      unfold OnBytes.Road.Hd.rdW at h1
      rw [hRi, Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt] at h1
      have h2 : (match b.L.arrayOf[readsOf W]? with
        | some q => (dataQ own' b rdW).cell q.1 q.2 0 (t.2.1 + i)
        | none => 0) = rd (val i) := h1
      rw [harr, hc'] at h2
      have h3 : (dataQ own' b rdW).cell c'.1 c'.2 0 (t.2.1 + i) = rd (val i) := h2
      rw [h3, statedAll_other W P cells lm nuL s e _ c' 0 _ he o ho tt ht t
        (tabAtCol_of hAp hfind i hi) (hname ▸ hnp)]
      unfold statedReads
      simp only [he, ho, hv, ht, Option.bind_some, tabAtCol_of hAp hfind i hi]
      rw [hname, Nat.add_sub_cancel_left, htv]
    -- the sizes at the letters are the seat's
    obtain ⟨z, y', hgf⟩ := given_form k1'
    have hsz : g'.sizes = (parOf W.hS (workOf W)).sizes := by rw [hgf]
    subst epl
    apply EntriesAt.mk
    · intro r i hi0
      have hi : i < @readLenN (parOf W.hS (workOf W)).sizes r := hsz ▸ hi0
      obtain ⟨t, h1, h2, h3⟩ := w1 r
      show EntsAt Q (y.1.entry r i)
      rw [a1 r i]
      exact one (nameOfN r) t i _ (noPlane_norm r) h1 h2 (Nat.lt_of_lt_of_le hi h3)
        (nameN_is r ▸ HO.norm r) ((truthOf_norm _ _ r i).trans (readAtN_same hSm r i hi0).symm)
    · intro i hi0
      have hi : i < @wideLenN (parOf W.hS (workOf W)).sizes := hsz ▸ hi0
      obtain ⟨t, h1, h2, h3⟩ := w2 .wideAtKeys
      have hi' : i < t.2.2 := by
        refine Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hi ?_) h3
        exact Nat.div_le_div_right (Nat.le_add_right _ _)
      have hi2 : i < readLen .wideAtKeys :=
        Nat.lt_of_lt_of_le hi0 (Nat.div_le_div_right (Nat.le_add_right _ _))
      show EntsAt Q (y.1.wide i)
      rw [a2 i]
      exact one "hf@Z" t i _ (noPlane_head .wideAtKeys) h1 h2 hi' (HO.head .wideAtKeys)
        ((truthOf_head _ _ .wideAtKeys i).trans (readAt_same hSm .wideAtKeys i hi2).symm)
    · intro r i hi0
      have hi : i < @readLen (parOf W.hS (workOf W)).sizes r := hsz ▸ hi0
      obtain ⟨t, h1, h2, h3⟩ := w2 r
      show EntsAt Q (y.2.entry r i)
      rw [a3 r i]
      exact one (nameOf r) t i _ (noPlane_head r) h1 h2 (Nat.lt_of_lt_of_le hi h3)
        (nameH_is r ▸ HO.head r) ((truthOf_head _ _ r i).trans (readAt_same hSm r i hi0).symm)
  -- the letters at e are the state's own
  have letters : ∀ v, lettersAt (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) e = .ok v →
      v.1 = g ∧ (v.2.1.norm, v.2.1.final, v.2.1.head) = H := by
    intro v hv
    obtain ⟨H', y, k1, k2, _, k4⟩ := lettersAt_ok W.hS (readsOf W) (parOf W.hS (workOf W)) hv
    have e1 : (Except.ok v.1 : Except String Given) = .ok g := by
      rw [← k1, given_front W.hS (readsOf W) _ hse, hg]
    have e2 := heard_front W.hS (readsOf W) hse H hH
    rw [k2] at e2
    refine ⟨Except.ok.inj e1, ?_⟩
    rw [k4]
    exact Option.some.inj e2
  suffices hQ : EntsAt Q f from hQ x hx c hc
  by_cases hjn : name = "join"
  · subst hjn
    obtain ⟨v, gk, hv, hgke, ej, _⟩ := reader_join KS e R hRe
    obtain ⟨rfl, rfl⟩ := letters v hv
    have hgk : s.lookHeard? = some gk := by rw [← (fork_withTables he).2]; exact hgke
    obtain ⟨_, _, k1, _⟩ := lettersAt_ok W.hS (readsOf W) (parOf W.hS (workOf W)) hv
    obtain ⟨hd, hJ⟩ := sizes_of_plan _ _ e v.1 hok k1
    rw [ej] at hf
    obtain rfl := List.mem_singleton.mp hf
    refine joinForm_has (kept_ents Q) gk (keyVectorsAt v) (fun q hq => ?_)
      (entsAt_of_empty Q (hbare gk hgk))
    have hlen : q < v.1.calls.length := by
      simpa [keyVectorsAt] using hq
    letI := v.1
    letI := v.2.1
    letI := v.2.2
    unfold keyVectorsAt
    rw [Came.getD_map_toArray v.1.calls _ q hlen (Aff.ofConst zeroE) (0, [])]
    exact keyVector_ents (entries v hv) hB hd hJ _ _
  · have hn' : name = "norm" ∨ name = "policy" ∨ name = "logits" := by
      rcases hn with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact absurd h hjn
    obtain ⟨v, fs, hv, lk, ef, _⟩ := reader_own KS name hn' e R hRe
    obtain ⟨rfl, rfl⟩ := letters v hv
    obtain ⟨_, _, k1, _⟩ := lettersAt_ok W.hS (readsOf W) (parOf W.hS (workOf W)) hv
    obtain ⟨hd, _⟩ := sizes_of_plan _ _ e v.1 hok k1
    rw [ef] at hf
    letI := v.1
    letI := v.2.1
    letI := v.2.2
    exact claims_ents (entries v hv) hB hd name fs lk f hf

/-- **THE HEAD's HALF OF THE EXCHANGE AT THE HEAD's FOUR RUNS, AT THE HEAD's ARM OF THE STATED
DATA.** s, a: the verifier's state in front of the sending of the reads, and its part; b: the part
behind it. Where, at the state with the tables laid, the run's points and vectors are the kind's
letters (hRun), the twelve tables' entries in the world of the committed data behind the sending
are the sums at the run's own weights over cells c1 (hTw), and c1 agrees inside the ranges with the
integer cells made of the data in front (hSame): at every entry that a form of one of the four runs
names, the committed cell is uHeadK6 X 24 at the state in front. -/
theorem armCellIn_K6 (X : OnBytes.Model.Verify.Public) (l piece blk : Nat)
    (states : Nat → List (RunOf S))
    (KS : K6States X.hS (readsOf X) (parOf X.hS (workOf X)) l piece states blk)
    (Rd : Readers) (own own' : List (Nat × Nat)) (s : S) (a b : K9.Part)
    (rdW : Nat × Nat → Sound.MsgQ)
    (hRd : ∀ name, K6Name name → Rd.forms blk name s = k6Silent (p8K6 X 24) states blk name s)
    (hok : (parOf X.hS (workOf X)).ok = true)
    (hT : K6HeardAt X.hS (readsOf X) (parOf X.hS (workOf X)) s)
    (hbare : ∀ gk, s.lookHeard? = some gk → gk.cEnd.ents = #[])
    (harr : b.L.arrayOf = a.L.arrayOf)
    (hwide : ∀ e F tr, withTables (p8K6 X 24) s = some e → e.fork? = some F →
      F.trees[readsOf X]? = some tr → X.H.nU.getD 2 0 ≤ tr.K)
    (hla : X.hS.la = X.hS.ls + X.hS.lt) (c1 : NCells)
    (hRun : ∀ e v, withTables (p8K6 X 24) s = some e →
      lettersAt (parOf X.hS (workOf X)) (seatAt X.hS (readsOf X)) e = .ok v →
      ∃ o cov x t, e.here = .head o ∧ e.covered X.hS.T X.hS.V = .ok cov ∧ o.x = some x ∧
        o.t = some t ∧ K8.ReadsQuiet.tables X.hS X.HLy X.H cov x = .ok t ∧
        (letI := v.1
         letI := v.2.1
         RunIs ⟨X.hS, X.HLy, borderOf X.y, X.H, cov, x, t, readsOf X⟩))
    (hTw : ∀ e v o cov x t F tr, withTables (p8K6 X 24) s = some e →
      lettersAt (parOf X.hS (workOf X)) (seatAt X.hS (readsOf X)) e = .ok v →
      e.here = .head o → e.covered X.hS.T X.hS.V = .ok cov → o.x = some x → o.t = some t →
      K8.ReadsQuiet.tables X.hS X.HLy X.H cov x = .ok t →
      e.fork? = some F → F.trees[readsOf X]? = some tr →
      (letI := v.1
       TwelveTrue (worldOwn b [] (dataQ own' b rdW))
         ⟨X.hS, X.HLy, borderOf X.y, X.H, cov, x, t, readsOf X⟩ tr.K c1))
    (hSame : ∀ e v, withTables (p8K6 X 24) s = some e →
      lettersAt (parOf X.hS (workOf X)) (seatAt X.hS (readsOf X)) e = .ok v →
      (letI := v.1
       SameCells c1 (cellsOfData X (Meaning.sizesOf X) (dataQ own a rdW))))
    (name : String) (hn : K6Name name) :
    Sound.ArmCellIn Rd own own' blk name s a b rdW (uHeadK6 X 24) :=
  armCellIn_four X (p8K6 X 24) l piece blk states KS Rd own own' s a b rdW hRd hok hT hbare
    (fun _ D => cellsOfData X (Meaning.sizesOf X) D) X.hS.lmbH (nuK6 X) harr hwide
    (fun e v o tt F tr he hv ho ht hF htr => by
      obtain ⟨o', cov, x, t, ho', hc, hx, ht', hmd, I⟩ := hRun e v he hv
      obtain rfl : o = o' := by
        rw [ho] at ho'
        injection ho'
      obtain rfl : tt = t := Option.some.inj (ht.symm.trans ht')
      obtain ⟨_, _, k1, _⟩ := lettersAt_ok X.hS (readsOf X) (parOf X.hS (workOf X)) hv
      obtain ⟨z, y', hgf⟩ := given_form k1
      have hsz : v.1.sizes = (parOf X.hS (workOf X)).sizes := by rw [hgf]
      refine ⟨⟨X.hS, X.HLy, borderOf X.y, X.H, cov, x, tt, readsOf X⟩, c1, rfl, rfl, ?_,
        hSame e v he hv⟩
      letI := v.1
      letI := v.2.1
      refine Came.ours_of_twelve I ?_ (hTw e v o cov x tt F tr he hv ho hc hx ht hmd hF htr)
      show X.hS.la = v.1.sizes.ls + v.1.sizes.lt
      rw [hsz]
      exact hla) name hn

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.readAt_same
#print axioms VerifiableInference.Desc.Kinds.Head.Law.readAtN_same
#print axioms VerifiableInference.Desc.Kinds.Head.Law.claims_ents
#print axioms VerifiableInference.Desc.Kinds.Head.Law.keyVector_ents
#print axioms VerifiableInference.Desc.Kinds.Head.Law.armCellIn_four
#print axioms VerifiableInference.Desc.Kinds.Head.Law.armCellIn_K6
