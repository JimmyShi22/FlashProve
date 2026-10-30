-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6StatedPlanes.lean: THE STATED FUNCTION OF THE WHOLE ARRAY OF THE HEAD's
READS: Law/K6Stated.lean's statedReads (the twelve tables' reads in truth; 0 at the lookup's planes'
three tables) WITH THE THREE PLANES' READS IN TRUTH LAID IN; and what the calling kind owes its
lookup on the planes (the three clauses K3HostPlanes) AT THAT STATED DATA, BY UNFOLDING: no tie of
the proximity test's equations and no law of the reads is asked. Definitions, statements and proofs.

  planesTruth gk lm nu name i   at "bH-bits-0" | "bH-bits-1": the library's sum over the rows of the
                   planes' matrix of the weight at the lookup's first | second point times the cell
                   (colsK) at column i; at "bH-pin": pinColK; nothing at another name.
  planesRead       the same by the column of the array: the table in whose stretch the column lies,
                   at the verifier's state with the tables laid.
  statedAll        THE FUNCTION: planesRead where it answers; statedReads elsewhere.
  statedAll_other  at a column of a table that bears none of the three names it IS statedReads.
  statedAll_at     at column i of one of the three tables it is planesTruth's value.
  hostPlanes_stated   MAIN: in every world whose entries are those of the world of the forms at data
                   whose cells of the reads' array are statedAll: K3HostPlanes at the seat's own
                   readers of the planes.
  entriesAlike_of_statedAll, k6Out_of_items_statedAll   Law/K6Stated.lean's two tops, carried: the
                   proofs are these tops' own, with one step more (statedAll_other): THEY OVERTAKE
                   THEM wherever the stated function is statedAll.

nu: A LETTER: the reading of the lookup's places (the planes' matrix's cells; the masks) off the
verifier's state and the data.
WHAT IT IS NOT. Definitions and an unfolding. That the sums are what the proximity test's equations
enforce is said nowhere here. TabsApart, "each table ends below the array's width", the three
tables' lengths: premises. Nothing on soundness.
LETTERS. r stands under "there is": tied by callerReaders.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.K6Stated
import Johnson.Desc.Kinds.Law.HeadPlanes

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E zeroE)
open OnBytes.Model (Fork Aff World Reading HTree)
open VerifiableInference.Desc.First (S HeadOwn)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (worldOwn)
open Norm (lt ls d lPd T S2)

/-- The three planes' reads in truth, by the table's name. -/
def planesTruth (gk : OnBytes.Model.Forest.Heard) (lm : Nat) (nu : _root_.Fo.Pl → K)
    (name : String) (i : Nat) : Option K :=
  if name = "bH-bits-0" then
    some (_root_.Fo.colsK gk.shape lm (_root_.Fo.rdL Reading.gl gk.zb0) nu i)
  else if name = "bH-bits-1" then
    some (_root_.Fo.colsK gk.shape lm (_root_.Fo.rdL Reading.gl gk.zb1) nu i)
  else if name = "bH-pin" then some (Cb.Fo.Pin.pinColK lm nu i)
  else none

/-- The same by the column of the array of the reads. -/
def planesRead (P : K8.ReadsQuiet.PH) (lm : Nat) (nu : _root_.Fo.Pl → K) (s : S) (pos : Nat) :
    Option K :=
  (withTables P s).bind fun e =>
    match e.here with
    | .head o =>
      e.lookHeard?.bind fun gk =>
        (o.t.bind fun tt => tabAtCol tt pos).bind fun x => planesTruth gk lm nu x.1 (pos - x.2.1)
    | _ => none

/-- **THE STATED FUNCTION OF THE WHOLE ARRAY OF THE READS.** -/
def statedAll (W : OnBytes.Model.Verify.Public) (P : K8.ReadsQuiet.PH)
    (cells : S → Bound K → NCells) (lm : Nat) (nu : S → Bound K → _root_.Fo.Pl → K) :
    S → Bound K → Nat × String → Nat → Nat → K :=
  fun s D c r pos =>
    match planesRead P lm (nu s D) s pos with
    | some v => v
    | none => statedReads W P cells s D c r pos

/-- None of the three names. -/
def NoPlane (name : String) : Prop :=
  name ≠ "bH-bits-0" ∧ name ≠ "bH-bits-1" ∧ name ≠ "bH-pin"

theorem planesTruth_none (gk : OnBytes.Model.Forest.Heard) (lm : Nat) (nu : _root_.Fo.Pl → K)
    {name : String} (h : NoPlane name) (i : Nat) : planesTruth gk lm nu name i = none := by
  unfold planesTruth
  rw [if_neg h.1, if_neg h.2.1, if_neg h.2.2]

/-- At a column of a table that bears none of the three names it is statedReads. -/
theorem statedAll_other (W : OnBytes.Model.Verify.Public) (P : K8.ReadsQuiet.PH)
    (cells : S → Bound K → NCells) (lm : Nat) (nu : S → Bound K → _root_.Fo.Pl → K) (s e : S)
    (D : Bound K) (c : Nat × String) (r pos : Nat) (he : withTables P s = some e) (o : HeadOwn)
    (ho : e.here = .head o) (tt : OnBytes.Model.Head.Tables) (ht : o.t = some tt)
    (x : String × Nat × Nat) (hx : tabAtCol tt pos = some x) (hn : NoPlane x.1) :
    statedAll W P cells lm nu s D c r pos = statedReads W P cells s D c r pos := by
  have h0 : planesRead P lm (nu s D) s pos = none := by
    unfold planesRead
    rw [he]
    simp only [Option.bind_some, ho, ht, hx]
    cases e.lookHeard? with
    | none => rfl
    | some gk => exact planesTruth_none gk lm _ hn _
  unfold statedAll
  rw [h0]

/-- At column i of a table found under its name it is planesTruth's value, where that answers. -/
theorem statedAll_at (W : OnBytes.Model.Verify.Public) (P : K8.ReadsQuiet.PH)
    (cells : S → Bound K → NCells) (lm : Nat) (nu : S → Bound K → _root_.Fo.Pl → K) (s e : S)
    (D : Bound K) (c : Nat × String) (r : Nat) (he : withTables P s = some e) (o : HeadOwn)
    (ho : e.here = .head o) (tt : OnBytes.Model.Head.Tables) (ht : o.t = some tt)
    (hA : TabsApart tt) (gk : OnBytes.Model.Forest.Heard) (hg : e.lookHeard? = some gk)
    (name : String) (x : String × Nat × Nat)
    (hx : tt.tab.find? (fun e => e.1 == name) = some x) (i : Nat) (hi : i < x.2.2) (v : K)
    (hv : planesTruth gk lm (nu s D) name i = some v) :
    statedAll W P cells lm nu s D c r (x.2.1 + i) = v := by
  have hname : x.1 = name := by
    have := List.find?_some hx
    simpa using this
  have h0 : planesRead P lm (nu s D) s (x.2.1 + i) = some v := by
    unfold planesRead
    rw [he]
    simp only [Option.bind_some, ho, ht, hg, tabAtCol_of hA hx i hi]
    rw [hname, Nat.add_sub_cancel_left]
    exact hv
  unfold statedAll
  rw [h0]

/-- **WHAT THE HEAD OWES ITS LOOKUP ON THE PLANES, AT THE STATED DATA, BY UNFOLDING.** -/
theorem hostPlanes_stated (W : OnBytes.Model.Verify.Public) (P : K8.ReadsQuiet.PH)
    (cells : S → Bound K → NCells) (lm : Nat) (nu : S → Bound K → _root_.Fo.Pl → K) (s e : S)
    (a : K9.Part) (D D' : Bound K) (Wd : World K) (hWd : Wd.entry = (worldOwn a [] D').entry)
    (he : withTables P s = some e) (o : HeadOwn) (ho : e.here = .head o)
    (tt : OnBytes.Model.Head.Tables) (ht : o.t = some tt) (hA : TabsApart tt) (F : Fork)
    (hF : e.fork? = some F) (tr : HTree) (htr : F.trees[readsOf W]? = some tr) (hK : tr.K ≠ 0)
    (hB : ∀ x ∈ tt.tab, x.2.1 + x.2.2 ≤ tr.K) (gk : OnBytes.Model.Forest.Heard)
    (hg : e.lookHeard? = some gk) (cU : Nat × String)
    (hArr : a.L.arrayOf[readsOf W]? = some cU)
    (hcell : ∀ pos, D'.cell cU.1 cU.2 0 pos = statedAll W P cells lm nu s D cU 0 pos)
    {e0 e1 eP : String × Nat × Nat}
    (h0 : (tt.tab.find? fun e => e.1 == "bH-bits-0") = some e0)
    (h1 : (tt.tab.find? fun e => e.1 == "bH-bits-1") = some e1)
    (hP : (tt.tab.find? fun e => e.1 == "bH-pin") = some eP)
    (l0 : gk.shape.NC * 2 ^ (gk.shape.kT + 5 - lm) ≤ e0.2.2)
    (l1 : gk.shape.NC * 2 ^ (gk.shape.kT + 5 - lm) ≤ e1.2.2)
    (lP : gk.shape.NC * 2 ^ (gk.shape.kT + 5 - lm) ≤ eP.2.2) :
    ∃ r, callerReaders (planesAt (readsOf W)) e = some r ∧
      Meaning.Planes.K3HostPlanes gk.shape lm (_root_.Fo.rdL Reading.gl gk.zb0)
        (_root_.Fo.rdL Reading.gl gk.zb1) (nu s D) (fun f => f.value Reading.gl Wd)
        (fun e col => (r.1 e col).getD {}) (fun col => (r.2 col).getD {}) := by
  refine ⟨_, planesAt_readers (readsOf W) ho hF ht htr hK, ?_⟩
  have hcols : ((F.trees[readsOf W]?).map (·.K)).getD 1 = tr.K := by
    rw [htr]
    rfl
  -- one entry
  have one : ∀ (xr : PlaneRead) (name : String) (t : String × Nat × Nat) (i : Nat) (v : K),
      (match xr with
        | .bits0 => "bH-bits-0" | .bits1 => "bH-bits-1" | .pin => "bH-pin") = name →
      tt.tab.find? (fun e => e.1 == name) = some t → i < t.2.2 →
      planesTruth gk lm (nu s D) name i = some v →
      ((planeEntry tt.tab (readsOf W) (((F.trees[readsOf W]?).map (·.K)).getD 1) xr i).getD
        {}).value Reading.gl Wd = v := by
    intro xr name t i v hnm hfind hi hv
    subst hnm
    have hm : t ∈ tt.tab := List.mem_of_find?_eq_some hfind
    have hlt : t.2.1 + i < tr.K := by
      have := hB t hm
      omega
    rw [hcols, planeEntry_at (x := xr) hfind hi]
    show (Aff.ent (readsOf W) ((t.2.1 + i) / tr.K) ((t.2.1 + i) % tr.K)).value Reading.gl _ = v
    rw [Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt, Aff.value_ent, hWd]
    show (match a.L.arrayOf[readsOf W]? with
      | some b => D'.cell b.1 b.2 0 (t.2.1 + i)
      | none => 0) = _
    rw [hArr]
    show D'.cell cU.1 cU.2 0 (t.2.1 + i) = _
    rw [hcell]
    exact statedAll_at W P cells lm nu s e D cU 0 he o ho tt ht hA gk hg _ t hfind i hi v hv
  refine ⟨fun col hc => ?_, fun col hc => ?_, fun col hc => ?_⟩
  · exact one .bits0 _ e0 col _ rfl h0 (lt_of_lt_of_le hc l0) rfl
  · exact one .bits1 _ e1 col _ rfl h1 (lt_of_lt_of_le hc l1) rfl
  · exact one .pin _ eP col _ rfl hP (lt_of_lt_of_le hc lP) rfl

/-! ## The twelve tables: Law/K6Stated.lean's two tops, carried to statedAll -/

theorem noPlane_head (r : Read) : NoPlane (nameOf r) := by
  cases r <;> exact ⟨by decide, by decide, by decide⟩

theorem noPlane_norm (r : FinalNorm.Read) : NoPlane (nameOfN r) := by
  cases r <;> exact ⟨by decide, by decide, by decide⟩

/-- **AT DATA WHOSE CELLS OF THE READS' ARRAY ARE THE STATED FUNCTION: THE SEAT's ENTRIES ARE WORTH
THE READS IN TRUTH.** D': the stated data; cU: the reads' array's name in the link's list. -/
theorem entriesAlike_of_statedAll (W : OnBytes.Model.Verify.Public) (P : K8.ReadsQuiet.PH)
    (cells : S → Bound K → NCells) (lm : Nat) (nu : S → Bound K → _root_.Fo.Pl → K) (s e : S)
    (a : K9.Part) (D D' : Bound K) (d : Pinned)
    (v : Given × Behind × Places) (he : withTables P s = some e)
    (hv : lettersAt (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) e = .ok v)
    (cU : Nat × String) (hArr : a.L.arrayOf[readsOf W]? = some cU)
    (hcell : ∀ pos, D'.cell cU.1 cU.2 0 pos = statedAll W P cells lm nu s D cU 0 pos)
    (hd1 : d.1.cell = (cells s D).cell) (hd2 : d.1.stream = (cells s D).stream)
    (hApart : ∀ o tt, e.here = .head o → o.t = some tt → TabsApart tt)
    (hBelow : ∀ o tt F tr, e.here = .head o → o.t = some tt → e.fork? = some F →
      F.trees[readsOf W]? = some tr → ∀ x ∈ tt.tab, x.2.1 + x.2.2 ≤ tr.K)
    (W₂ : World K) :
    letI := v.1
    letI := v.2.1
    EntriesAlike (worldOwn a [] D') W₂ v.2.2.final (normReadsAtCells d.1) v.2.2.head
      (readsAt d.1.toCells) := by
  obtain ⟨g, bh, pl⟩ := v
  obtain ⟨H, x, k1, _, k3, k4⟩ := lettersAt_ok W.hS (readsOf W) (parOf W.hS (workOf W)) hv
  obtain ⟨o, F, tt, tr, ho, hF, ht, htr, _, a1, a2, a3⟩ := reads_are W.hS (readsOf W) e x k3
  obtain ⟨w1, w2⟩ := reads_within W.hS (readsOf W) e x k3 tt o ho ht
  have hAp := hApart o tt ho ht
  have hBe := hBelow o tt F tr ho ht hF htr
  have k1' : given (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) e = .ok g := k1
  have epl : pl = ⟨x.1, x.2⟩ := by
    have := congrArg (fun w : Given × Behind × Places => w.2.2) k4
    exact this
  -- one entry
  have one : ∀ (name : String) (t : String × Nat × Nat) (i : Nat),
      NoPlane name →
      tt.tab.find? (fun e => e.1 == name) = some t → firstOf tt name = t.2.1 → i < t.2.2 →
      vW (worldOwn a [] D') (entryAt (readsOf W) tr.K (firstOf tt name + i)) =
        rd (truthOf (g, bh, pl) d.1 name i) := by
    intro name t i hnp hfind hfirst hi
    have hm : t ∈ tt.tab := List.mem_of_find?_eq_some hfind
    have hlt : t.2.1 + i < tr.K := by
      have := hBe t hm
      omega
    have hname : t.1 = name := by
      have := List.find?_some hfind
      simpa using this
    rw [hfirst]
    unfold entryAt vW
    rw [Nat.div_eq_of_lt hlt, Nat.mod_eq_of_lt hlt, Aff.value_ent]
    show (match a.L.arrayOf[readsOf W]? with
      | some b => D'.cell b.1 b.2 0 (t.2.1 + i)
      | none => 0) = _
    rw [hArr]
    show D'.cell cU.1 cU.2 0 (t.2.1 + i) = _
    rw [hcell, statedAll_other W P cells lm nu s e D cU 0 _ he o ho tt ht t
      (tabAtCol_of hAp hfind i hi) (hname ▸ hnp)]
    unfold statedReads
    simp only [he, ho, hv, ht, Option.bind_some, tabAtCol_of hAp hfind i hi]
    rw [hname, Nat.add_sub_cancel_left, truthOf_congr _ d.1 (cells s D) hd1 hd2]
  -- the sizes at the letters are the seat's
  obtain ⟨z, y, hgf⟩ := given_form k1'
  have hsz : g.sizes = (parOf W.hS (workOf W)).sizes := by rw [hgf]
  subst epl
  apply EntriesAlike.mk
  · intro r i hi
    have hi : i < @readLenN (parOf W.hS (workOf W)).sizes r := hsz ▸ hi
    obtain ⟨t, h1, h2, h3⟩ := w1 r
    show vW _ (x.1.entry r i) = _
    rw [a1 r i, one (nameOfN r) t i (noPlane_norm r) h1 h2 (Nat.lt_of_lt_of_le hi h3),
      truthOf_norm]
    unfold vW
    exact (Aff.value_ofConst _ _ _).symm
  · intro i hi
    have hi : i < @wideLenN (parOf W.hS (workOf W)).sizes := hsz ▸ hi
    obtain ⟨t, h1, h2, h3⟩ := w2 .wideAtKeys
    have hi' : i < t.2.2 := by
      refine Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hi ?_) h3
      exact Nat.div_le_div_right (Nat.le_add_right _ _)
    show vW _ (x.1.wide i) = _
    rw [a2 i, one "hf@Z" t i (noPlane_head .wideAtKeys) h1 h2 hi',
      show ("hf@Z" : String) = nameOf .wideAtKeys from rfl,
      truthOf_head]
    unfold vW
    exact (Aff.value_ofConst _ _ _).symm
  · intro r i hi
    have hi : i < @readLen (parOf W.hS (workOf W)).sizes r := hsz ▸ hi
    obtain ⟨t, h1, h2, h3⟩ := w2 r
    show vW _ (x.2.entry r i) = _
    rw [a3 r i, one (nameOf r) t i (noPlane_head r) h1 h2 (Nat.lt_of_lt_of_le hi h3),
      truthOf_head]
    unfold vW
    exact (Aff.value_ofConst _ _ _).symm

/-- **k6Out_of_items AT STATED DATA WHOSE CELLS OF THE READS' ARRAY ARE statedAll**: the premise
hA is gone; in its place: the array's name in the link's list; the cells' equation (at the table's
term for the stated data: its own unfolding); the tie of the components to the letter cells; two
facts on the tables. -/
theorem k6Out_of_items_statedAll (W : OnBytes.Model.Verify.Public) (P : K8.ReadsQuiet.PH)
    (l piece b : Nat) (states : Nat → List (K9.RunOf S))
    (KS : K6States W.hS (readsOf W) (parOf W.hS (workOf W)) l piece states b)
    (Rd : K9.Readers) (St : Sound.Stated) (own : List (Nat × Nat)) (s : S)
    (rdW : Nat × Nat → Sound.MsgQ) (d : Pinned) (a : K9.Part) (ha : K9.segAt? s = some a)
    (hRd : ∀ name, K6Name name → Rd.forms b name s = k6Silent P states b name s)
    (hok : (parOf W.hS (workOf W)).ok = true)
    (hT : K6HeardAt W.hS (readsOf W) (parOf W.hS (workOf W)) s)
    (hmask : ∀ j, j < a.F.mf.size → (St.at1 s (Sound.dataQ own a rdW)).mask j = rd (d.2 j))
    (cells : S → Bound K → NCells) (lm : Nat) (nu : S → Bound K → _root_.Fo.Pl → K)
    (cU : Nat × String) (hArr : a.L.arrayOf[readsOf W]? = some cU)
    (hcell : ∀ pos, (St.at1 s (Sound.dataQ own a rdW)).cell cU.1 cU.2 0 pos =
      statedAll W P cells lm nu s (Sound.dataQ own a rdW) cU 0 pos)
    (hd1 : d.1.cell = (cells s (Sound.dataQ own a rdW)).cell)
    (hd2 : d.1.stream = (cells s (Sound.dataQ own a rdW)).stream)
    (hApart : ∀ e o tt, withTables P s = some e → e.here = .head o → o.t = some tt →
      TabsApart tt)
    (hBelow : ∀ e o tt F tr, withTables P s = some e → e.here = .head o → o.t = some tt →
      e.fork? = some F → F.trees[readsOf W]? = some tr → ∀ x ∈ tt.tab, x.2.1 + x.2.2 ≤ tr.K)
    (hWt : WeightAt W s d.1.toCells d.2)
    (hbare : ∀ gk, s.lookHeard? = some gk → gk.cEnd.ents = #[])
    (hn : Sound.formsTQ Rd St own b "norm" s rdW) (hp : Sound.formsTQ Rd St own b "policy" s rdW)
    (hl : Sound.formsTQ Rd St own b "logits" s rdW)
    (hj : Sound.formsTQ Rd St own b "join" s rdW) : K6Out W s d :=
  k6Out_of_items W P l piece b states KS Rd St own s rdW d a ha hRd hok hT hmask
    (fun e v he hv => entriesAlike_of_statedAll W P cells lm nu s e a (Sound.dataQ own a rdW) _ d v
      he hv cU hArr hcell hd1 hd2 (fun o tt => hApart e o tt he)
      (fun o tt F tr => hBelow e o tt F tr he) _)
    hWt hbare hn hp hl hj

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.entriesAlike_of_statedAll
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k6Out_of_items_statedAll
#print axioms VerifiableInference.Desc.Kinds.Head.Law.statedAll_other
#print axioms VerifiableInference.Desc.Kinds.Head.Law.statedAll_at
#print axioms VerifiableInference.Desc.Kinds.Head.Law.hostPlanes_stated
