-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/K4Fit.lean: THE LAYERS' OWN ROUNDS (K4) IN THE FRAME's OWN FORM, WITH THE FIT
OF THE MEMBER's DECLARED ROUNDS SPENT: what is left among the tests on values are tests on values.
Under the head P5J.AtMgA; nothing is evaluated.

Why. K4's block tests three things in front of its hearing (stretchB,
Johnson/Desc/First/K4/Returns/AtChain.lean): no count of rows waits; the stretch fits K4's table;
the strict reading. Johnson/AtFull/Shape/K4Frame.lean leaves all three among the tests on values and
rounds. The first is seen on the chain's shape. The other two follow from the frame's own test on
the rounds' form (roundsFit, Johnson/Desc/Block.lean) at the member's declared rounds.

  all_e, cut_entryOf   a message whose items are n elements of the field; the cut of a row's entry.
  **k4_fit**      rounds that fit the declared rounds of K4's table, shown without the sealed
                  digest, pass both of K4's tests on the stretch.
  noneWaitsSh, noneWaits_sh   "no count of rows waits", on the chain's shape.
  k4StepW         THE STEP: no count of rows waits, on the shape; then the step at the seat
                  (k4StepS, Johnson/AtFull/Shape/K4AtHead.lean).
  k4ValsV         THE TESTS ON VALUES: the request's tokens; the merged point; the coin.
  k4StepW_reads, k4ValsV_reads   both read three fields of a place's record alone.
  vals_join       the whole Bool of K4AtHead.lean from its three parts: the shape's, the fit's, the
                  values'.
  k4_rounds_at    the member's declared rounds are those of K4's table.
  **k4_at_fit**   the seat, as k4_at, with "returns" at rounds that fit.
  **k4_frame_fit**   Carries and Returns at K4's twelve members, at G (28 g + 4) = liftO (k4StepW
                  ...) and vals (28 g + 4) = k4ValsV ....

Limits. As in K4Frame.lean, but for the fit: TWO PREMISES OF THE RULE AT TWELVE MEMBERS; G and vals
are letters; NO STATE IS SHOWN AT WHICH THE STEP RETURNS; who pays k4ValsV is not said. k4_frame_fit
does not say that a member stands at 28 g + 4 (k4_at_fit has it): where none stood, Carries and
Returns would say nothing: both begin "for every member at that number". K4Frame.lean's k4_frame
speaks at the same twelve numbers with another G and vals: a table takes one of the two. The head is
taken at OnBytes.secondHashFunction, its first letter, alone. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.K4Frame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain roundsFit noDigest itemOf)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape
open OnBytes.Maker (WholeD)
open P5J (AtMgA)
open OnBytes.K.Kc (paired)
open OnBytes.Desc.First (Kit.plainStretchWith Kit.plainRoundWith Kit.rowsOk)
open OnBytes.Desc.First.K4 (Par Rd entryOf entries rounds fitsAll rowsTabled blockAtC)
open OnBytes.Desc.First.K4.Rt (stretchB coinB decide_lays k4Step_carries)
open OnBytes.Desc.First.K4.RtPub (tokensFit)
open ProofFile.Honest (Carries Returns)

/-! ## 1 Rounds that fit the declared rounds of K4's table -/

/-- A message whose items are n elements of the field. -/
theorem all_e : ∀ (l : List Fmt.ItemValue) (n : Nat), l.map itemOf = List.replicate n .e →
    l.length = n ∧ (l.all fun x => match x with | .e _ => true | _ => false) = true
  | [], n, h => by
    cases n with
    | zero => exact ⟨rfl, rfl⟩
    | succ n => cases h
  | x :: l, n, h => by
    cases n with
    | zero => cases h
    | succ n =>
      rw [List.map_cons, List.replicate_succ] at h
      obtain ⟨h1, h2⟩ := List.cons.inj h
      obtain ⟨i1, i2⟩ := all_e l n h2
      refine ⟨by rw [List.length_cons, i1], ?_⟩
      rw [List.all_cons, i2, Bool.and_true]
      cases x <;> first | rfl | cases h1

/-- The cut of a row's entry: as many elements of the field as the row says are sent. -/
theorem cut_entryOf (d : Rd) :
    ({ entry := entryOf d } : Fmt.DeclaredRound).items.filter (· != .root) =
      List.replicate d.sent .e := by
  show ((List.replicate 0 Fmt.Item.answer ++ List.replicate 0 Fmt.Item.root ++
    List.replicate ((24 * d.sent - 24 * 0 - 32 * 0) / 24) Fmt.Item.e).filter
      (· != Fmt.Item.root)) = _
  have e : (24 * d.sent - 24 * 0 - 32 * 0) / 24 = d.sent := by omega
  rw [e]
  simp

/-- **Rounds that fit the declared rounds of K4's table pass K4's two tests on the stretch.** -/
theorem k4_fit : ∀ (ds : List Rd) (rs : List Fmt.RoundView),
    roundsFit ((ds.map entryOf).map fun e => { entry := e }) rs = true →
      fitsAll ds (ds.map entryOf) (rs.map noDigest) = true ∧
        Kit.plainStretchWith rowsTabled (ds.map entryOf) (rs.map noDigest) = true
  | [], [], _ => ⟨rfl, rfl⟩
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | d :: ds, r :: rs, h => by
    have h' : (r.vals.map itemOf ==
          ({ entry := entryOf d } : Fmt.DeclaredRound).items.filter (· != .root) &&
        r.drawn.elems.length == (entryOf d).drawE && r.drawn.poss.length == (entryOf d).poss &&
        r.drawn.trits.length == (entryOf d).trits &&
        r.drawn.poss.all (· < 2 ^ (entryOf d).logN) &&
        r.drawn.trits.all (fun t => t == -1 || t == 0 || t == 1) &&
        VerifiableInference.Desc.drawsMarkedNonzeroHaveNonzeroWords { entry := entryOf d } r &&
        roundsFit ((ds.map entryOf).map fun e => { entry := e }) rs) = true := h
    simp only [Bool.and_eq_true, beq_iff_eq] at h'
    obtain ⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, -⟩, -⟩, -⟩, a8⟩ := h'
    rw [cut_entryOf] at a1
    obtain ⟨b1, b2⟩ := all_e r.vals d.sent a1
    obtain ⟨i1, i2⟩ := k4_fit ds rs a8
    have a2' : r.drawn.elems.length = d.drawn := a2
    have a3' : r.drawn.poss.length = 0 := a3
    have a4' : r.drawn.trits.length = 0 := a4
    refine ⟨?_, ?_⟩
    · show (Rd.fits d (entryOf d) (noDigest r) &&
        fitsAll ds (ds.map entryOf) (rs.map noDigest)) = true
      rw [i1, Bool.and_true]
      show (d.name.name == d.name.name && r.vals.length == d.sent && d.drawn == d.drawn &&
        r.drawn.elems.length == d.drawn && d.notZero == d.notZero && d.rows == d.rows) = true
      simp [b1, a2']
    · show (Kit.plainRoundWith rowsTabled (ds.map entryOf).isEmpty (entryOf d) (noDigest r) &&
        Kit.plainStretchWith rowsTabled (ds.map entryOf) (rs.map noDigest)) = true
      rw [i2, Bool.and_true]
      show ((0 : Nat) == 0 && (0 : Nat) == 0 && r.drawn.elems.length == d.drawn &&
        r.drawn.poss.length == 0 && r.drawn.trits.length == 0 &&
        Kit.rowsOk rowsTabled (ds.map entryOf).isEmpty (entryOf d) &&
        r.vals.all fun x => match x with | .e _ => true | _ => false) = true
      have hr : Kit.rowsOk rowsTabled (ds.map entryOf).isEmpty (entryOf d) = true := by
        unfold Kit.rowsOk rowsTabled
        by_cases h0 : ((entryOf d).rows == 0) = true
        · simp [h0]
        · simp [h0]
      rw [a2', a3', a4', hr, b2]
      simp only [beq_self_eq_true, Bool.and_self]

/-! ## 2 The step and the tests on values -/

/-- No count of rows waits, on the shape. -/
def noneWaitsSh (a : ChainSh) : Bool :=
  match a.rowsOwed with
  | none => true
  | some r => r == 0

theorem noneWaits_sh (s : S) : noneWaitsSh (chainSh s) = s.noneWaits := rfl

/-- **The step**: no count of rows waits; then the step at the seat. -/
def k4StepW (p : Par) (a : ChainSh) : Option ChainSh :=
  if noneWaitsSh a then k4StepS p a else none

/-- **The tests on values**: the request's tokens; the merged point; the coin. Where the state has
no lookup's record (s.look? = none) the clause on the merged point says yes in silence; the two
others still decide. (Under the step's return that case does not arise: k4FrontB asks that the
record be there.) mergedB (K4AtHead.lean) says yes where either reading of the points fails. The
first clause tests the request, no sent or drawn value. -/
def k4ValsV (p : Par) (s : S) (rs : List Fmt.RoundView) : Bool :=
  tokensFit { p.P with tokv := s.tokv } p.g && (s.look?.all fun fo => mergedB p.P fo) &&
    coinB p.P p.g (paired rs (entries p.P p.hp p.g))

theorem k4StepW_reads {p q : Par} (h1 : p.P = q.P) (h2 : p.hp = q.hp) (h3 : p.g = q.g) :
    k4StepW p = k4StepW q := by
  funext a
  unfold k4StepW
  rw [k4StepS_reads h1 h2 h3]

theorem k4ValsV_reads {p q : Par} (h1 : p.P = q.P) (h2 : p.hp = q.hp) (h3 : p.g = q.g) :
    k4ValsV p = k4ValsV q := by
  funext s rs
  unfold k4ValsV
  rw [h1, h2, h3]

/-- The whole Bool of K4AtHead.lean, from its three parts: the shape's, the fit's, the values'. -/
theorem vals_join {p : Par} {s : S} {rs : List Fmt.RoundView} (hw : s.noneWaits = true)
    (hf : roundsFit ((entries p.P p.hp p.g).map fun e => { entry := e }) rs = true)
    (hv : k4ValsV p s (rs.map noDigest) = true) : k4ValsB p s (rs.map noDigest) = true := by
  obtain ⟨f1, f2⟩ := k4_fit (rounds p.P p.hp p.g) rs hf
  have f1' : fitsAll (rounds p.P p.hp p.g) (entries p.P p.hp p.g) (rs.map noDigest) = true := f1
  have f2' : Kit.plainStretchWith rowsTabled (entries p.P p.hp p.g) (rs.map noDigest) = true := f2
  unfold k4ValsV at hv
  simp only [Bool.and_eq_true] at hv
  unfold k4ValsB stretchB
  rw [hw, f1', f2', hv.1.1, hv.1.2, hv.2]
  rfl

/-! ## 3 The seat and the frame, with the fit spent -/

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The member's declared rounds are those of K4's table. -/
theorem k4_rounds_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (g : Nat) (hg : g < 12) :
    ∃ (Bs : ProofFile.PureBase) (y : Bool × Par) (b : Block S ProofFile.Cl),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      y.2.P = Bs.G₀.W.layers ∧ y.2.g = g ∧ Bs.G₀.W.G[g]? = some y.2.hp ∧
      cF.blocksInOrder[28 * g + 4]? = some b ∧
      b.rounds = (entries y.2.P y.2.hp y.2.g).map fun e => { entry := e } := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, b, y, eL, eb, -, la, -, eg, eP, ehp, -, -⟩ := IM.k4_of h.scope h.reads O g hg
  have q := IM.hear_at_flat eL eb
  rw [IM.flatIx_scope h.scope h.reads O (by omega : 2 * g ≤ 24) 2] at q
  have en : 14 * (2 * g) + 2 + 2 = 28 * g + 4 := by omega
  rw [en] at q
  exact ⟨Bs, y, b, O.made, eP, eg, ehp, q, IM.alone_rounds la⟩

theorem k4_at_fit (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (g : Nat) (hg : g < 12) :
    ∃ (Bs : ProofFile.PureBase) (y : Bool × Par) (b : Block S ProofFile.Cl),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      y ∈ ProofFile.k4From Zp Bs.G₀ Bs.G₀.built.toList 0 none ∧
      y.2.P = Bs.G₀.W.layers ∧ y.2.g = g ∧ Bs.G₀.W.G[g]? = some y.2.hp ∧
      cF.blocksInOrder[28 * g + 4]? = some b ∧
      (∀ s rs gs t u, b.decide s rs gs = .ok t →
        k4StepW { y.2 with k3Runs := true } (chainSh s) = some u → u = chainSh t ∧ t.st = s.st) ∧
      ∀ s rs gs u, roundsFit b.rounds rs = true →
        k4StepW { y.2 with k3Runs := true } (chainSh s) = some u →
        k4ValsV { y.2 with k3Runs := true } s (rs.map noDigest) = true →
        ∃ t, b.decide s (rs.map noDigest) gs = .ok t := by
  obtain ⟨Bs, y, b, e1, e2, e3, e4, e5, q, hc, hr⟩ := k4_at h g hg
  obtain ⟨Bs', y', b', e1', e3', e4', e5', q', hrd⟩ := k4_rounds_at h g hg
  obtain rfl : Bs = Bs' := Except.ok.inj (e1.symm.trans e1')
  obtain rfl : b = b' := Option.some.inj (q.symm.trans q')
  have kP : y'.2.P = y.2.P := e3'.trans e3.symm
  have kg : y'.2.g = y.2.g := e4'.trans e4.symm
  have kh : y'.2.hp = y.2.hp := Option.some.inj (e5'.symm.trans e5)
  rw [kP, kh, kg] at hrd
  refine ⟨Bs, y, b, e1, e2, e3, e4, e5, q, fun s rs gs t u hd hu => ?_,
    fun s rs gs u hf hu hv => ?_⟩
  · unfold k4StepW at hu
    split at hu
    · exact hc s rs gs t u hd hu
    · cases hu
  · unfold k4StepW at hu
    split at hu
    · rename_i hw
      rw [hrd] at hf
      exact hr s _ gs u hu (vals_join (p := { y.2 with k3Runs := true })
        ((noneWaits_sh s).symm.trans hw) hf hv)
    · cases hu

theorem k4_frame_fit (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (g : Nat) (hg : g < 12) :
    ∃ (Bs : ProofFile.PureBase) (y : Bool × Par),
      ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs ∧
      y ∈ ProofFile.k4From Zp Bs.G₀ Bs.G₀.built.toList 0 none ∧
      y.2.P = Bs.G₀.W.layers ∧ y.2.g = g ∧ Bs.G₀.W.G[g]? = some y.2.hp ∧
      ∀ (ft : Nat) G vals,
        G (28 * g + 4) = liftO (k4StepW { y.2 with k3Runs := true }) →
        (∀ s rs gs, vals (28 * g + 4) s rs gs = k4ValsV { y.2 with k3Runs := true } s rs) →
        Carries cF.blocksInOrder ft (firstZA G vals) (28 * g + 4) ∧
          Returns cF.blocksInOrder ft (firstZA G vals) (28 * g + 4) := by
  obtain ⟨Bs, y, b, e1, e2, e3, e4, e5, q, hc, hr⟩ := k4_at_fit h g hg
  refine ⟨Bs, y, e1, e2, e3, e4, e5, fun ft G vals hG hv => ⟨?_, ?_⟩⟩
  · refine carries_of_seat q fun s rs gs t u _ hd hu => ?_
    rw [hG] at hu
    obtain ⟨w, hw, rfl⟩ := liftO_ok.1 hu
    obtain ⟨k1, k2⟩ := hc s _ gs t w hd hw
    subst k1
    show (chainSh t, formsOf s.st) = (chainSh t, formsOf t.st)
    rw [k2]
  · refine returns_of_seat q fun s rs gs u hf hu hvv => ?_
    rw [hG] at hu
    rw [hv] at hvv
    obtain ⟨w, hw, -⟩ := liftO_ok.1 hu
    exact hr s rs gs w hf hw hvv

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.all_e
#print axioms Johnson.AtFull.Shape.cut_entryOf
#print axioms Johnson.AtFull.Shape.k4_fit
#print axioms Johnson.AtFull.Shape.noneWaits_sh
#print axioms Johnson.AtFull.Shape.k4StepW_reads
#print axioms Johnson.AtFull.Shape.k4ValsV_reads
#print axioms Johnson.AtFull.Shape.vals_join
#print axioms Johnson.AtFull.Shape.k4_rounds_at
#print axioms Johnson.AtFull.Shape.k4_at_fit
#print axioms Johnson.AtFull.Shape.k4_frame_fit
#print axioms Johnson.AtFull.Shape.noneWaitsSh
#print axioms Johnson.AtFull.Shape.k4StepW
#print axioms Johnson.AtFull.Shape.k4ValsV
