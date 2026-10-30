-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Head/PubAtFull.lean: THE NINE COUNTS OF PADDING KEYS OF THE OUTPUT HEAD's LOOKUP AT
THE FULL SIZE, and an opening law for tests on the head's whole layout. What `Head.layout` returns
at the full size is known by `LaidW` (Johnson/AtFull/Head/LayoutAtFull.lean), in which the counts
stand as a letter `pub` with its size alone. Here they are nine written numbers. No sub-protocol
imports this file.

Definitions.
  `pubNine`: the nine. Whence: typed off a note of another writer of this project, which has them
    as the written value `pubW 3 false` of its own file; held here by Lean's kernel in `form_W`.
    Their tie to that name is left to whoever calls them.
  `formB`: with code: the closed form (`formAt`, Johnson/AtFull/Head/PubValue.lean) gives the nine,
    and each segment's length is below 2 ^ 41.
  `laidOf L calls fs kb`: the very structure of `LaidW`'s last conjunct, with the nine for `pub`.
  `withLaid f`: with code: the head's numbers, calls, lookup's shape (the twin without the tests on
    tables) and planes' columns are made, and f is asked at `laidOf` of these; false where a maker
    refuses.
Statements.
  `form_W`: [Lean's kernel] `withFs formB = true`. It reads of a call its number of columns and its
    segments' lengths.
  `form_tree_no`, `form_taken_no`: negative tests, each with one input bent: with trees of twice the
    columns, and with one column more taken in each call, the closed form does not give the nine.
  `facts_W`: what `allW` gives at whatever letters the three makers return: the lookup's shape by
    the true routine, and the two premises of `pubOf_eq`.
  `laid_pub`: LaidW x ⊢ x = .ok HLy with HLy.fs.pub = pubNine.
  `withLaid_true`: withLaid f = true ⊢ for every x with LaidW x: x = .ok HLy and f HLy = true.

Limits. The full size, at the stored free numbers alone. No soundness is claimed. On hiding nothing.

-/
import Johnson.AtFull.Head.LayoutAtFull
import Johnson.AtFull.Head.PubValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtFull.Head
open OnBytes OnBytes.Model OnBytes.Model.Head
open OnBytes.Road.Hd (tauFCw)
open Johnson.Unfolds (shape_eq ask_eq)
open VerifiableInference.Desc.Kinds.Head.Law (Cond.hFull)

/-- The nine counts. -/
def pubNine : Array Nat :=
  #[0, 51052544, 0, 61538304, 0, 61415424, 0, 61538304, 128974848]

/-- The closed form gives the nine, and the lengths are small. -/
def formB (_ : HL) (calls : List CallD) (fs : Forest.Shape) : Bool :=
  decide (((List.range fs.NT).map (formAt Cond.hFull.T (csW fs) fs calls)).toArray = pubNine) &&
    calls.all fun cd => cd.segs.all fun s => decide (s.n < 2 ^ (topBit + 1))

/-- **By the kernel.** -/
theorem form_W : withFs formB = true := by decide +kernel

/-- A negative test: with trees of twice the columns. (withFs is false also where a maker refuses:
that the three makers return is form_W's: it is the control.) -/
theorem form_tree_no : withFs (fun _ calls fs =>
    decide (((List.range fs.NT).map (formAt Cond.hFull.T (csW fs + 1) fs calls)).toArray =
      pubNine)) = false := by decide +kernel

/-- A negative test: with one column more taken in each call (a segment of length 1 more). The
control: form_W. -/
theorem form_taken_no : withFs (fun _ calls fs =>
    decide (((List.range fs.NT).map (formAt Cond.hFull.T (csW fs) fs
      (calls.map fun cd => { cd with segs := { name := "", n := 1, pos := #[], moe := false } ::
        cd.segs }))).toArray = pubNine)) = false := by decide +kernel

/-- What allW gives, at whatever letters the three makers return. -/
theorem facts_W {L : HL} {calls : List CallD} {fs : Forest.Shape}
    (hL : numbers Cond.hFull = .ok L) (hc : callsOf Cond.hFull L = .ok calls)
    (hf : Forest.shapeNoAsk (clW calls) Cond.hFull.LIDB = .ok fs) :
    Forest.shape (clW calls) Cond.hFull.LIDB = .ok fs ∧
    (∀ x ∈ calls.zipIdx,
      (x.1.J / 2 ^ (fs.dT - Cond.hFull.lt) == 2 ^ fs.iota.getD x.2 0) = true) ∧
    (∀ x ∈ calls.zipIdx, ∀ g ∈ x.1.segs, perEntry g.name = true →
      g.n - (Cond.hFull.V - firstEntry L g.name) = 0) := by
  obtain ⟨L', calls', fs', hL', hc', hf', hT⟩ := withFs_true allW
  obtain rfl : L' = L := Except.ok.inj (hL'.symm.trans hL)
  obtain rfl : calls' = calls := Except.ok.inj (hc'.symm.trans hc)
  obtain rfl : fs' = fs := Except.ok.inj (hf'.symm.trans hf)
  unfold bigTest at hT
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at hT
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨t1, t2⟩, t3⟩, t4⟩, t5⟩, t6⟩, t7⟩, t8⟩, t9⟩, t10⟩, t11⟩, t12⟩ := hT
  have asks : ∀ c ∈ (clW calls').toList, Forest.callAsk c = .ok () := by
    intro c hcm
    have r := rec_ok Cond.hFull tauFCw tauFEw calls' fc_ok fe_ok hcm
    rw [ask_eq c r.1 r.2]
    exact ok_unit (t4 c hcm)
  refine ⟨(shape_eq _ _ asks).trans hf, fun x hx => beq_iff_eq.2 (t9 x hx).1.1.1, ?_⟩
  intro x hx g hg hp
  have k := (t9 x hx).1.1.2 g hg
  rw [hp] at k
  simpa using k

/-- The counts at whatever letters the makers return. -/
theorem pub_nine {L : HL} {calls : List CallD} {fs : Forest.Shape} {pub : Array Nat}
    (hL : numbers Cond.hFull = .ok L) (hc : callsOf Cond.hFull L = .ok calls)
    (hf : Forest.shapeNoAsk (clW calls) Cond.hFull.LIDB = .ok fs)
    (hp : pubOf Cond.hFull L fs calls = .ok pub) : pub = pubNine := by
  obtain ⟨-, H1, H2⟩ := facts_W hL hc hf
  obtain ⟨L', calls', fs', hL', hc', hf', hT⟩ := withFs_true form_W
  obtain rfl : L' = L := Except.ok.inj (hL'.symm.trans hL)
  obtain rfl : calls' = calls := Except.ok.inj (hc'.symm.trans hc)
  obtain rfl : fs' = fs := Except.ok.inj (hf'.symm.trans hf)
  unfold formB at hT
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hT
  have e := Except.ok.inj (hp.symm.trans (pubOf_eq Cond.hFull L' fs' calls' H1 H2))
  rw [e, pub_value Cond.hFull.T (fs'.dT - Cond.hFull.lt) fs' calls'
    (fun cd hcd => by
      obtain ⟨name, kind, asks, fl, e1, -⟩ := (OnBytes.Road.Hd.callsOf_spec hc).1 cd hcd
      exact ⟨name, kind, asks, fl, e1⟩) hT.2]
  exact hT.1

/-- The structure of LaidW's last conjunct, with the nine. -/
def laidOf (L : HL) (calls : List CallD) (fs : Forest.Shape) (kb : Nat) : HL :=
  { L with
    kb := kb, calls := calls.toArray,
    cl := (clW calls).mapIdx fun q c => { c with iota := fs.iota.getD q 0 },
    fs := { fs with
      calls := (clW calls).mapIdx fun q c => { c with iota := fs.iota.getD q 0 },
      pub := pubNine } }

/-- A test at the head's whole layout. -/
def withLaid (f : HL → Bool) : Bool :=
  withFs fun L calls fs =>
    match Forest.planeCols fs Cond.hFull.lmbH with
    | .ok kb => f (laidOf L calls fs kb)
    | .error _ => false

/-- What LaidW says, with the makers' twin and the nine. -/
theorem LaidW.opens {x : Except String HL} (h : LaidW x) :
    ∃ L calls fs kb, numbers Cond.hFull = .ok L ∧ callsOf Cond.hFull L = .ok calls ∧
      Forest.shapeNoAsk (clW calls) Cond.hFull.LIDB = .ok fs ∧
      Forest.planeCols fs Cond.hFull.lmbH = .ok kb ∧ x = .ok (laidOf L calls fs kb) := by
  obtain ⟨L, calls, fs, kb, pub, hL, hc, hs, hk, hp, -, -, hx⟩ := h
  obtain ⟨L', calls', fs', hL', hc', hf', -⟩ := withFs_true allW
  obtain rfl : L' = L := Except.ok.inj (hL'.symm.trans hL)
  obtain rfl : calls' = calls := Except.ok.inj (hc'.symm.trans hc)
  obtain rfl : fs' = fs := Except.ok.inj ((facts_W hL hc hf').1.symm.trans hs)
  obtain rfl := pub_nine hL hc hf' hp
  exact ⟨L', calls', fs', kb, hL, hc, hf', hk, hx⟩

/-- **The counts in what the head's layout returns are the nine.** -/
theorem laid_pub {x : Except String HL} (h : LaidW x) :
    ∃ HLy, x = .ok HLy ∧ HLy.fs.pub = pubNine := by
  obtain ⟨L, calls, fs, kb, -, -, -, -, hx⟩ := h.opens
  exact ⟨_, hx, rfl⟩

/-- **The opening law.** -/
theorem withLaid_true {f : HL → Bool} (h : withLaid f = true) :
    ∀ x, LaidW x → ∃ HLy, x = .ok HLy ∧ f HLy = true := by
  intro x hx
  obtain ⟨L, calls, fs, kb, hL, hc, hf, hk, e⟩ := hx.opens
  obtain ⟨L', calls', fs', hL', hc', hf', hT⟩ := withFs_true h
  obtain rfl : L' = L := Except.ok.inj (hL'.symm.trans hL)
  obtain rfl : calls' = calls := Except.ok.inj (hc'.symm.trans hc)
  obtain rfl : fs' = fs := Except.ok.inj (hf'.symm.trans hf)
  rw [hk] at hT
  exact ⟨_, e, hT⟩

end AtFull.Head

#print axioms AtFull.Head.form_W
#print axioms AtFull.Head.form_tree_no
#print axioms AtFull.Head.form_taken_no
#print axioms AtFull.Head.facts_W
#print axioms AtFull.Head.pub_nine
#print axioms AtFull.Head.LaidW.opens
#print axioms AtFull.Head.laid_pub
#print axioms AtFull.Head.withLaid_true
