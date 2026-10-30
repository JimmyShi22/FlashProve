-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Att/PlanOwn.lean: the entries of the rounds that the planner adds for an attention
sub-proof's own part, as a closed list that is cut into named stretches.

The planner's routine is planAttentionOwn (OnBytes/Params/SubRounds.lean). What is said of a round
here is its whole Fmt.Entry: the name and eleven numbers (count, work, msg, roots, answers, drawE,
drawNZ, poss, logN, trits, rows). The list is a function of w, the work of a round of the kind field
in a request's scope, and of the record x : AttentionRounds. A round's six other fields are in
OnBytes/Tie/Pv/Att/PlanOwnW.lean, from which the statements here follow.

The cut has one rule. A stretch is either one whole planPsc, from its round PSC epsilon to its round
PSC values, or one single round BAT-sigma or ZERO. There is no round for scalars alone: planScalars
adds no entry, and its 24 n bytes are counted in the msg of the next round that is closed. The table
calls these scalars riders. It gives the first message in scalars, and then the rest.
  unitL, first  3 planeMessages + 7 riders + 1   u.1 rounds of 3; Y: 2; values: 2 u.2
  unitL, later  7 riders + 1                     the same, for its own u
  aE            5 + lt + 2 riders + 1            e rounds of 3; Y: 2; values: 2 pairs
                (and 3 planeMessages riders if x.score is empty)
  batV          0                                rows 2
  aVM           2 riders + 1                     valueM rounds of 3; Y: 2; values: 2 pairs
  aVD           1                                valueD rounds of 3; Y: 2; values: 2 pairs
  zeroFH        0                                draws 2 lgk + 2 lt + 4
  batF          pairs riders                     rows pairs
  aF            1                                attained rounds of 3; Y: 2; values: 2 pairs
  batD          0                                rows pairs
  aD            1                                lt rounds of 2, lgk of lt + 2, lt of lt + 1;
                                                 Y: lt + 1; values: Lam + pairs lt
  batH          0                                rows pairs
  aH            1                                bits rounds of 3; Y: 2; values: 2 pairs

Main names:
  `Adds s b b' r L`: from a state with At s b the routine r ends well only in a state with
    At s b', and it has then added just rounds whose entries are L.
  `att_adds`: Adds s 0 0 (planAttentionOwn x) (attList (s.workOf .field .request) x).
  `att_entries`: the part of att_adds on the list, written out. `att_finish`: the same of finish.
  `lPsc_sc3`, `lPsc_scd`: a sumcheck's entries in closed form.
  `attCuts`, `attCuts_join`: the stretches under their names; joined, they are attList. The names
    are strings: "A1", "A2" and so on for the score units, then "AE", "batV", "AVM", "AVD",
    "zeroFH", "batF", "AF", "batD", "AD", "batH", "AH".
  `sc3_length`, `scd_length`, `attList_length`: the numbers of rounds.
  `firsts`, `attList_at`: the first index of each stretch behind the score units, for every x.

Limits: att_adds stands under At s 0 p and under the premise that the routine ends well from p. No
statement says that it does end well, or that the state behind the lookup has At s 0. att_finish
speaks of the routine run alone from an empty plan; the planner itself runs the lookup first
(attentionRounds). To end well is less than to pass the plan's verdict (Planned.holds). The list is
the plan of the verifier on bytes; no text of the C++ programs is compared with it here.

The list has names, bytes and numbers of draws. A statement on a block must not take more from it.
It is silent, or looks alike, where the verifier's routines differ. What is said of the routines
below is by reading OnBytes/Model/AttentionScores.lean, AttentionDivide.lean, AttentionClaimsB.lean,
AttentionSums.lean, AttentionShape.lean, Psc.lean, Hide.lean, Rounds.lean and OnBytes/Iop/Psc.lean;
no theorem says it.
 1. The order of the variables. All variables of a sum of the size attentionSc3 have the same entry.
    Which variable a round binds is the routine's. The order is not the same everywhere: aE's point
    has the head's bits first and then the token's; aF's and aH's have the token's first. In aD the
    numbers of scalars tell three runs of rounds apart; at lt = 1 the first run's entry and the
    third's would be the same (the verifier's shape refuses lt below 2 and above 16).
 2. Which coefficient is left out. A round sends g - 1 scalars for a polynomial of a degree below g.
    The plan does not say which of the g is not sent, or from which equation the verifier restores
    it. The variables' rounds use Weight.plain, the sum g(0) + g(1), with the linear coefficient not
    sent. Y's round uses Weight.atZero, the sum g(0), with the constant coefficient not sent.
 3. The order inside a message. The plan has one number for a message. In the routines the riders
    come first and the sumcheck's own scalar last. The end values of a sum of products come as
    A_0, B_0, A_1, B_1 and so on; aD's are Lam key values and then lt bits for each pair.
 4. What the riders are, and whose. Of a score unit's 7 riders the seventh is the unit's start. The
    3 planeMessages riders belong to no sumcheck of this list. Of aE's riders the second is aE's
    start. Of aVM's two riders the first is aVM's start and the second is aVD's: a block for aVD
    names a scalar of another block's message. batF's riders are the pairs' row maxima, from which
    aF starts.
 5. The routines' cut is not this cut.
      batF, aF   one routine (scoreAtIndexIn). The element enters aF's start and aF's weights.
      batD, aD   one routine (keyAtIndexIn). The element enters aD's start and aD's summand.
      batH, aH   one routine (bitsIn). The element enters aH's weights alone; aH starts from 0.
      batV       drawn by divide, in no sumcheck's routine. Its element enters no start form. It
                 enters the second map of every pair in both aVM and aVD, and one linear claim.
      zeroFH     drawn by attain. Its first lgk + lt elements are aF's point, its last 4 + lgk + lt
                 are aH's. The plan has one bound for all 2 lgk + 2 lt + 4 elements together.
    aD starts from the batch of aF's second end values, which get no claim of their own, and its
    summand reads aF's point.
 6. No stretch tests an equation. A run leaves one affine form that must be 0, and end values that
    must be tied down. These become linear claims, which are batched by an element that is drawn
    later: in the plan, the round BAT-sigma on x.rows rows of attentionRounds. It is in no stretch
    (no round of attList reads x.rows). A block's list of errors from a stretch's numbers alone does
    not count that round or what follows it in the chain.
 7. Points that are drawn before the list begins. The weights of the score units, aE, aVM and aVD
    are taken at points that the lookup has drawn, before index 0 of attList. Only aF and aH have a
    point's round in the list.
 8. What is tested without a round: that the denominator is the sum of the weights has no round of
    its own (the comment on planAttentionOwn).
 9. Which stretch is which, where sizes meet. aVD, aF and aH are the same list as soon as their
    numbers of variables agree; so are aE, aVM and a score unit of pairs pieces, but for the riders.
    In every shape that the verifier makes, aE and aVD have the same number of variables. batD and
    batH are always the same list, and batV too where pairs = 2. A test that compares a list with
    the plan cannot notice that two of them were taken for each other.
 10. That the record's numbers are the routines' numbers. OnBytes/Model/AttentionPlan.lean fills x;
    no statement here ties x to a run. The routine of aD takes degrees (2, lt + 2, lt + 1); the
    plan's PscSize.degree says one more.
 11. That a list has a run. pscEnds asks for at least one end value, so pairs = 0 has a list and no
    run.
 12. drawNZ is 0 at PSC epsilon: the plan lets that element be 0.
-/
import OnBytes.Tie.Pv.Att.PlanOwnW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Att.Plan

open OnBytes OnBytes.Params

/-! ### The closed lists -/

/-- A round that draws n elements of E, none of them barred from 0, with b bytes sent. -/
def eDraw (name : String) (w b n : Nat) : Fmt.Entry :=
  { name := name, work := w, msg := b, drawE := n }

/-- A batch of rows, with b bytes sent in its own round. -/
def eBat (w b rows : Nat) : Fmt.Entry :=
  { name := "BAT-sigma", work := w, msg := b, drawE := 1, rows := rows }

/-- The round in the further variable Y, with dy scalars. -/
def eY (w dy : Nat) : Fmt.Entry :=
  { name := "PSC Y", work := w, msg := 24 * dy, drawE := 1, drawNZ := 1 }

/-- The round of n end values. -/
def eValues (n : Nat) : Fmt.Entry := { name := "PSC values", msg := 24 * n }

/-- A sumcheck of the size x, with b more bytes in the first message. -/
def lPsc (w b : Nat) (x : PscSize) : List Fmt.Entry :=
  [eDraw "PSC epsilon" w (b + 24) 1] ++
    x.degree.map (fun g => eDraw "PSC round" w (24 * (g - 1)) 1) ++
    (if x.withY then [eY w x.degreeY, eValues x.values] else [])

/-- One score unit. -/
def unitL (w b : Nat) (u : Nat × Nat) : List Fmt.Entry :=
  lPsc w (b + 24 * 7) (attentionSc3 u.1 u.2)
def unitsL (w : Nat) : Nat → List (Nat × Nat) → List Fmt.Entry
  | _, [] => []
  | b, u :: t => unitL w b u ++ unitsL w 0 t
def scoreL (w : Nat) (x : AttentionRounds) : List Fmt.Entry := unitsL w (planeBytes x) x.score
def aE (w : Nat) (x : AttentionRounds) : List Fmt.Entry :=
  lPsc w (leftOpen (planeBytes x) x.score + 24 * (5 + x.lt + 2)) (attentionSc3 x.e x.pairs)
def batV (w : Nat) (_x : AttentionRounds) : List Fmt.Entry := [eBat w 0 2]
def aVM (w : Nat) (x : AttentionRounds) : List Fmt.Entry :=
  lPsc w (24 * 2) (attentionSc3 x.valueM x.pairs)
def aVD (w : Nat) (x : AttentionRounds) : List Fmt.Entry :=
  lPsc w 0 (attentionSc3 x.valueD x.pairs)
def zeroFH (w : Nat) (x : AttentionRounds) : List Fmt.Entry :=
  [eDraw "ZERO" w 0 (2 * x.lgk + 2 * x.lt + 4)]
def batF (w : Nat) (x : AttentionRounds) : List Fmt.Entry := [eBat w (24 * x.pairs) x.pairs]
def aF (w : Nat) (x : AttentionRounds) : List Fmt.Entry :=
  lPsc w 0 (attentionSc3 x.attained x.pairs)
def batD (w : Nat) (x : AttentionRounds) : List Fmt.Entry := [eBat w 0 x.pairs]
def aD (w : Nat) (x : AttentionRounds) : List Fmt.Entry :=
  lPsc w 0 (attentionScd x.lt x.lgk x.pairs x.Lam)
def batH (w : Nat) (x : AttentionRounds) : List Fmt.Entry := [eBat w 0 x.pairs]
def aH (w : Nat) (x : AttentionRounds) : List Fmt.Entry :=
  lPsc w 0 (attentionSc3 x.bits x.pairs)

/-- The whole list. -/
def attList (w : Nat) (x : AttentionRounds) : List Fmt.Entry :=
  scoreL w x ++ aE w x ++ batV w x ++ aVM w x ++ aVD w x ++ zeroFH w x ++ batF w x ++ aF w x ++
    batD w x ++ aD w x ++ batH w x ++ aH w x

/-! ### The entries of the whole rounds -/

theorem wPsc_entries (s : Setting) (b : Nat) (x : PscSize) :
    (wPsc s b x).map (·.entry) = lPsc (s.workOf .field .request) b x := by
  cases h : x.withY <;>
    simp [wPsc, lPsc, h, rEps, rVar, rY, roundOf, quietOf, entryOf, eDraw, eY, eValues,
      Function.comp_def]

theorem unitsW_entries (s : Setting) : ∀ (b : Nat) (l : List (Nat × Nat)),
    (unitsW s b l).map (·.entry) = unitsL (s.workOf .field .request) b l
  | _, [] => rfl
  | b, u :: t => by
    simp only [unitsW, unitW, unitsL, unitL, List.map_append, wPsc_entries, unitsW_entries s 0 t]

theorem attRounds_entries (s : Setting) (x : AttentionRounds) :
    (attRounds s x).map (·.entry) = attList (s.workOf .field .request) x := by
  simp only [attRounds, attList, scoreW, aEW, batVW, aVMW, aVDW, zeroFHW, batFW, aFW, batDW, aDW,
    batHW, aHW, scoreL, aE, batV, aVM, aVD, zeroFH, batF, aF, batD, aD, batH, aH, List.map_append,
    wPsc_entries, unitsW_entries]
  simp [rZero, rBat, roundOf, entryOf, eDraw, eBat]

/-- From b open bytes the routine r ends well only with b' open bytes, and it has then added just
rounds with the entries L. -/
def Adds (s : Setting) (b b' : Nat) (r : Planning Unit) (L : List Fmt.Entry) : Prop :=
  ∀ p q, At s b p → r p = .ok ((), q) →
    At s b' q ∧ ∃ l : List PlanRound, q.rounds = p.rounds ++ l.toArray ∧ l.map (·.entry) = L

/-- planAttentionOwn adds just attList. -/
theorem att_adds (s : Setting) (x : AttentionRounds) :
    Adds s 0 0 (planAttentionOwn x) (attList (s.workOf .field .request) x) := fun p q hp h =>
  ⟨(att_addsW s x p q hp h).1, attRounds s x, (att_addsW s x p q hp h).2, attRounds_entries s x⟩

/-- The part of att_adds on the list, written out. -/
theorem att_entries (s : Setting) (x : AttentionRounds) (p q : PlanState) (hp : At s 0 p)
    (h : planAttentionOwn x p = .ok ((), q)) :
    ∃ l : List PlanRound, q.rounds = p.rounds ++ l.toArray ∧
      l.map (·.entry) = attList (s.workOf .field .request) x :=
  (att_adds s x p q hp h).2

/-- The same of the planner's finish. -/
theorem att_finish (s : Setting) (x : AttentionRounds) (P : Planned)
    (h : finish s .request (planAttentionOwn x) = .ok P) :
    P.set = s ∧ P.rounds.map (·.entry) = attList (s.workOf .field .request) x := by
  obtain ⟨h1, h2⟩ := att_finishW s x P h
  exact ⟨h1, by rw [h2, attRounds_entries]⟩

/-! ### Closed forms -/

/-- A sumcheck of the size attentionSc3. -/
theorem lPsc_sc3 (w b nv pairs : Nat) : lPsc w b (attentionSc3 nv pairs) =
    [eDraw "PSC epsilon" w (b + 24) 1] ++ List.replicate nv (eDraw "PSC round" w 72 1) ++
      [eY w 2, eValues (2 * pairs)] := by
  simp [lPsc, attentionSc3]

/-- The sumcheck of the size attentionScd. -/
theorem lPsc_scd (w b lt lgk pairs Lam : Nat) : lPsc w b (attentionScd lt lgk pairs Lam) =
    [eDraw "PSC epsilon" w (b + 24) 1] ++ List.replicate lt (eDraw "PSC round" w 48 1) ++
      List.replicate lgk (eDraw "PSC round" w (24 * (lt + 2)) 1) ++
      List.replicate lt (eDraw "PSC round" w (24 * (lt + 1)) 1) ++
      [eY w (lt + 1), eValues (Lam + pairs * lt)] := by
  simp [lPsc, attentionScd]

theorem lPsc_length (w b : Nat) (x : PscSize) (h : x.withY = true) :
    (lPsc w b x).length = x.degree.length + 3 := by
  simp [lPsc, h]

theorem sc3_length (w b nv pairs : Nat) : (lPsc w b (attentionSc3 nv pairs)).length = nv + 3 := by
  simp [lPsc, attentionSc3]

theorem scd_length (w b lt lgk pairs Lam : Nat) :
    (lPsc w b (attentionScd lt lgk pairs Lam)).length = 2 * lt + lgk + 3 := by
  simp [lPsc, attentionScd] <;> omega

/-! ### The named stretches -/

/-- The score units under the names A1, A2 and so on, from the number k. -/
def unitCuts (w : Nat) : Nat → Nat → List (Nat × Nat) → List (String × List Fmt.Entry)
  | _, _, [] => []
  | k, b, u :: t => (s!"A{k}", unitL w b u) :: unitCuts w (k + 1) 0 t

/-- The stretches, each under its name, in the plan's order. -/
def attCuts (w : Nat) (x : AttentionRounds) : List (String × List Fmt.Entry) :=
  unitCuts w 1 (planeBytes x) x.score ++
  [("AE", aE w x), ("batV", batV w x), ("AVM", aVM w x), ("AVD", aVD w x), ("zeroFH", zeroFH w x),
   ("batF", batF w x), ("AF", aF w x), ("batD", batD w x), ("AD", aD w x), ("batH", batH w x),
   ("AH", aH w x)]

theorem unitCuts_join (w : Nat) : ∀ (k b : Nat) (l : List (Nat × Nat)),
    ((unitCuts w k b l).map (·.2)).flatten = unitsL w b l
  | _, _, [] => rfl
  | k, b, u :: t => by
    simp only [unitCuts, unitsL, List.map_cons, List.flatten_cons, unitCuts_join w (k + 1) 0 t]

/-- Joined, the stretches are the list. -/
theorem attCuts_join (w : Nat) (x : AttentionRounds) :
    ((attCuts w x).map (·.2)).flatten = attList w x := by
  simp only [attCuts, attList, scoreL, List.map_append, List.flatten_append, unitCuts_join,
    List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.append_assoc]

/-- The number of rounds of the score units. -/
def scoreLen (l : List (Nat × Nat)) : Nat := (l.map fun u => u.1 + 3).sum

theorem unitsL_length (w : Nat) :
    ∀ (b : Nat) (l : List (Nat × Nat)), (unitsL w b l).length = scoreLen l
  | _, [] => rfl
  | b, u :: t => by
    simp only [unitsL, unitL, List.length_append, sc3_length, unitsL_length w 0 t, scoreLen,
      List.map_cons, List.sum_cons]

/-- The first index in attList of each stretch behind the score units, and the number of all
rounds. -/
structure Firsts where
  aE : Nat
  batV : Nat
  aVM : Nat
  aVD : Nat
  zeroFH : Nat
  batF : Nat
  aF : Nat
  batD : Nat
  aD : Nat
  batH : Nat
  aH : Nat
  all : Nat
  deriving DecidableEq, Repr

def firsts (x : AttentionRounds) : Firsts :=
  let a := scoreLen x.score
  let b := a + (x.e + 3)
  let c := b + 1
  let d := c + (x.valueM + 3)
  let e := d + (x.valueD + 3)
  let f := e + 1
  let g := f + 1
  let h := g + (x.attained + 3)
  let i := h + 1
  let j := i + (2 * x.lt + x.lgk + 3)
  let k := j + 1
  { aE := a, batV := b, aVM := c, aVD := d, zeroFH := e, batF := f, aF := g, batD := h, aD := i,
    batH := j, aH := k, all := k + (x.bits + 3) }

theorem attList_length (w : Nat) (x : AttentionRounds) :
    (attList w x).length = (firsts x).all := by
  simp only [attList, scoreL, aE, batV, aVM, aVD, zeroFH, batF, aF, batD, aD, batH, aH,
    List.length_append, unitsL_length, sc3_length, scd_length, List.length_cons, List.length_nil,
    firsts] <;> omega

/-- If L is A and then R, then R stands behind the first A.length members of L. -/
theorem drop_first {α : Type} {L A R : List α} (h : L = A ++ R) : L.drop A.length = R := by
  rw [h, List.drop_left]

/-- If B and then R stand behind the first n members of L, then R stands behind the first
n + B.length. -/
theorem drop_step {α : Type} {L B R : List α} {n : Nat} (h : L.drop n = B ++ R) :
    L.drop (n + B.length) = R := by
  rw [← List.drop_drop, h, List.drop_left]

/-- Each stretch stands at its first index: what is left of attList there begins with the stretch,
and goes on with what is left at the next stretch's first index. -/
theorem attList_at (w : Nat) (x : AttentionRounds) :
    (attList w x).drop (firsts x).aE = aE w x ++ (attList w x).drop (firsts x).batV ∧
    (attList w x).drop (firsts x).batV = batV w x ++ (attList w x).drop (firsts x).aVM ∧
    (attList w x).drop (firsts x).aVM = aVM w x ++ (attList w x).drop (firsts x).aVD ∧
    (attList w x).drop (firsts x).aVD = aVD w x ++ (attList w x).drop (firsts x).zeroFH ∧
    (attList w x).drop (firsts x).zeroFH = zeroFH w x ++ (attList w x).drop (firsts x).batF ∧
    (attList w x).drop (firsts x).batF = batF w x ++ (attList w x).drop (firsts x).aF ∧
    (attList w x).drop (firsts x).aF = aF w x ++ (attList w x).drop (firsts x).batD ∧
    (attList w x).drop (firsts x).batD = batD w x ++ (attList w x).drop (firsts x).aD ∧
    (attList w x).drop (firsts x).aD = aD w x ++ (attList w x).drop (firsts x).batH ∧
    (attList w x).drop (firsts x).batH = batH w x ++ (attList w x).drop (firsts x).aH ∧
    (attList w x).drop (firsts x).aH = aH w x := by
  have l0 : (scoreL w x).length = scoreLen x.score := unitsL_length w _ _
  have l1 : (aE w x).length = x.e + 3 := sc3_length _ _ _ _
  have l2 : (batV w x).length = 1 := rfl
  have l3 : (aVM w x).length = x.valueM + 3 := sc3_length _ _ _ _
  have l4 : (aVD w x).length = x.valueD + 3 := sc3_length _ _ _ _
  have l5 : (zeroFH w x).length = 1 := rfl
  have l6 : (batF w x).length = 1 := rfl
  have l7 : (aF w x).length = x.attained + 3 := sc3_length _ _ _ _
  have l8 : (batD w x).length = 1 := rfl
  have l9 : (aD w x).length = 2 * x.lt + x.lgk + 3 := scd_length _ _ _ _ _ _
  have l10 : (batH w x).length = 1 := rfl
  have e0 : attList w x = attList w x := rfl
  conv at e0 => rhs; simp only [attList, List.append_assoc]
  have d1 : (attList w x).drop (firsts x).aE = _ := l0 ▸ drop_first e0
  have d2 : (attList w x).drop (firsts x).batV = _ := l1 ▸ drop_step d1
  have d3 : (attList w x).drop (firsts x).aVM = _ := l2 ▸ drop_step d2
  have d4 : (attList w x).drop (firsts x).aVD = _ := l3 ▸ drop_step d3
  have d5 : (attList w x).drop (firsts x).zeroFH = _ := l4 ▸ drop_step d4
  have d6 : (attList w x).drop (firsts x).batF = _ := l5 ▸ drop_step d5
  have d7 : (attList w x).drop (firsts x).aF = _ := l6 ▸ drop_step d6
  have d8 : (attList w x).drop (firsts x).batD = _ := l7 ▸ drop_step d7
  have d9 : (attList w x).drop (firsts x).aD = _ := l8 ▸ drop_step d8
  have d10 : (attList w x).drop (firsts x).batH = _ := l9 ▸ drop_step d9
  have d11 : (attList w x).drop (firsts x).aH = _ := l10 ▸ drop_step d10
  rw [d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end OnBytes.Tie.Pv.Att.Plan

#print axioms OnBytes.Tie.Pv.Att.Plan.att_adds
#print axioms OnBytes.Tie.Pv.Att.Plan.att_entries
#print axioms OnBytes.Tie.Pv.Att.Plan.att_finish
#print axioms OnBytes.Tie.Pv.Att.Plan.attRounds_entries
#print axioms OnBytes.Tie.Pv.Att.Plan.lPsc_sc3
#print axioms OnBytes.Tie.Pv.Att.Plan.lPsc_scd
#print axioms OnBytes.Tie.Pv.Att.Plan.lPsc_length
#print axioms OnBytes.Tie.Pv.Att.Plan.sc3_length
#print axioms OnBytes.Tie.Pv.Att.Plan.scd_length
#print axioms OnBytes.Tie.Pv.Att.Plan.attCuts_join
#print axioms OnBytes.Tie.Pv.Att.Plan.attList_length
#print axioms OnBytes.Tie.Pv.Att.Plan.attList_at
