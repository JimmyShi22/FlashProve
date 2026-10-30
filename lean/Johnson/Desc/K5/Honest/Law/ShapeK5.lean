-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/ShapeK5.lean: CONDITIONAL: THE DECISION OF THE KIND "AN ATTENTION
SEGMENT's OWN ROUNDS" (K5; Johnson/Desc/First/Att/K5AttentionKind.lean, at the seat seatSO, Att/SeatO.lean) AS
ONE BOOL AND ONE UPDATE ON A SHAPE OF THE STATE THAT HOLDS NO FIELD ELEMENT. Over the library and
the shapes of Johnson/Desc/First/Shape/ alone: no prover's text is read. Definitions, and statements
with their proofs.

Why. A verifier's step says yes where its guards on the structure pass and its tests on values pass.
This kind's decision has no test on values (`hear_iff`, Att/K5Returns.lean). Here its guards are one
Bool, what it lays is one update, and two laws tie them to the decision's own text.

Main names:
  `batchedSh`, `affSh_batched`   the shape of a batched start form
  `sumShAt`, `prodAt`, `takesAt`, `unitsAt`, `unitsEnd`, `nFive` .. `nCells`, `heard5At`
    what the hearing hands on, as a function of the plan's numbers and the next free number in front
  `powers_len`, `take_sh`, `sum_sh`, `takes_sh`, `units_sh`, `heard5_sh`
    **the shape of what the hearing hands on is that function**
  `K5Sh`, `k5Sh`   what the decision reads and lays, as a shape: five readers
  `noneWaitsB`, `k5G`   **the guards as one Bool**
  `ledStep`, `k5Step`   **the step as one update**
  `k5Sh_att`, `readyO_of_G`, `k5_shape_returns`
    **returns**: the Bool's yes in front gives the decision's yes
  `eq_of_bare`, `ledSh_behind`, `k5_shape_carries`
    **carries**: the shape behind a yes is the update of the shape in front
  `k5G_bites`   seven controls: the Bool can say no (that it can say yes: Law/ShapeK5Yes.lean)

EVERY STATEMENT ON THE HEARING OR THE DECISION IS CONDITIONAL. `heard5_sh`, `ledSh_behind`: the
hearing returns; the three arrays on slots of the ledger in front have their length; the second
also: the slots that the rounds take are there and free. `k5_shape_returns`: the test on the plan;
the Bool's yes; the rounds have the plan's shape. `k5_shape_carries`: the decision's yes and the
Bool's yes.
By `k5_returns`, `k5_yes_is` (Johnson/Desc/K5/Honest/Law/Returns.lean), `filled_behind`
(Law/FilledBehind.lean), `hear_below` (Att/K05HearBelow.lean), `hear_ran` and the four verbs'
statements (Att/K5Shape.lean), `free_of_B`, `fillB_zip`, `affSh_addMul`
(Johnson/Desc/First/Shape/Parts.lean).
Limits. THE KIND's OWN DECISION ALONE: in the first chain's blocksInOrder list the block stands inside two
wrappers (a refusal at a mark behind the decision; a test that the reply is as it was), of which
nothing is said here; nor of the kind's runs of claims. The Bool is sufficient, not necessary: it
asks two sizes that the decision's text does not test. `K5Sh` is a reader of five components, typed
here; that they are components of the chain's shape is not shown. Nothing shows that the Bool says
yes at any state that is reached.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Shape.AttOwn
import Johnson.Desc.K5.Honest.Law.Returns
import Johnson.Desc.K5.Honest.Law.FilledBehind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Honest
open OnBytes OnBytes.Model OnBytes.Model.Road
open VerifiableInference.Desc (First.S First.AttOwn)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Var Ends Free Fits)
open VerifiableInference.Desc.First.Att.P
open VerifiableInference.Desc.First.Shape (AffSh affSh affSh_addMul affSh_slot affSh_ofConst SumSh
  sumSh Heard5Sh heard5Sh AttOwnSh attOwnSh attOf LedSh ledSh treeSh freeB fillB fillB_zip
  free_of_B)

/-! ## 1 The start forms' shapes -/

/-- The shape of the form Σ_b w_b · (scalar number first + step · b + off), over n members. -/
def batchedSh (n first step off : Nat) : AffSh :=
  AffSh.mk [] ((List.range n).map fun b => first + (step * b + off))

theorem affSh_batched (n : Nat) (w : Array E) (first step off : Nat) :
    affSh (batched n w first step off) = batchedSh n first step off := by
  have key : ∀ (l : List Nat) (a : Aff),
      affSh (l.foldl (fun a b => a.addMul (.slot (first + (step * b + off))) (w.getD b zeroE)) a) =
        (affSh a).append (AffSh.mk [] (l.map fun b => first + (step * b + off))) := by
    intro l
    induction l with
    | nil =>
      intro a
      simp [AffSh.append, AffSh.mk, AffSh.ents, AffSh.slots]
    | cons b l ih =>
      intro a
      rw [List.foldl_cons, ih, affSh_addMul, affSh_slot]
      simp [AffSh.append, AffSh.mk, AffSh.ents, AffSh.slots]
  unfold batched batchedSh
  rw [key, affSh_ofConst]
  simp [AffSh.append, AffSh.mk, AffSh.ents, AffSh.slots]

/-! ## 2 What the hearing hands on, as a function of the plan's numbers and the next free number -/

/-- A sumcheck that is heard from the next free number n on. C: the start form's shape. -/
def sumShAt (C : AffSh) (vs : List Var) (e : Ends) (n : Nat) : SumSh :=
  { start := C, first := n, degrees := vs.map (·.d) ++ [e.dY + 1], r := vs.length + 1
    sEnd := n + MaskedSum.ownSlots (vs ++ [.point zeroE (e.dY + 1)]) }

/-- A sumcheck of products of two maps: k variables, m pairs of maps. -/
def prodAt (C : AffSh) (k m n : Nat) : SumSh := sumShAt C (List.replicate k (.plain 4)) ⟨2, 2 * m⟩ n

/-- k times three scalars. -/
def takesAt : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, n => n :: takesAt k (n + 3)

/-- The softmax-table units. -/
def unitsAt : List (Nat × Nat) → Nat → List (Nat × SumSh)
  | [], _ => []
  | u :: us, n => (n, prodAt (AffSh.mk [] [n + 6]) u.1 u.2 (n + 7)) ::
      unitsAt us (n + 7 + (products u.1 u.2).slots)

/-- The next free number behind them. -/
def unitsEnd : List (Nat × Nat) → Nat → Nat
  | [], n => n
  | u :: us, n => unitsEnd us (n + 7 + (products u.1 u.2).slots)

/-- The next free number in front of: the division's five scalars; the division's sumcheck; the
value product's two scalars; its sumcheck on the diagonal; the maxima; the score at the index; the
key at the index; the index's cells. -/
def nFive (x : Params.AttentionRounds) (n : Nat) : Nat := unitsEnd x.score (n + 3 * x.planeMessages)
def nDiv (x : Params.AttentionRounds) (n : Nat) : Nat := nFive x n + 5 + x.lt + 2
def nVal (x : Params.AttentionRounds) (n : Nat) : Nat := nDiv x n + (products x.e x.pairs).slots
def nOn (x : Params.AttentionRounds) (n : Nat) : Nat :=
  nVal x n + 2 + (products x.valueM x.pairs).slots
def nMax (x : Params.AttentionRounds) (n : Nat) : Nat := nOn x n + (products x.valueD x.pairs).slots
def nIdx (x : Params.AttentionRounds) (n : Nat) : Nat := nMax x n + x.pairs
def nKey (x : Params.AttentionRounds) (n : Nat) : Nat :=
  nIdx x n + (products x.attained x.pairs).slots
def nCells (x : Params.AttentionRounds) (n : Nat) : Nat := nKey x n + (keyStage x).slots

/-- **The shape of what the hearing hands on**, of the plan's numbers x and the next free number n
in front. -/
def heard5At (x : Params.AttentionRounds) (n : Nat) : Heard5Sh :=
  { remainders := takesAt x.planeMessages n
    scores := unitsAt x.score (n + 3 * x.planeMessages)
    five := nFive x n
    bits := nFive x n + 5
    two := nFive x n + 5 + x.lt
    division := prodAt (AffSh.mk [] [nFive x n + 1]) x.e x.pairs (nDiv x n)
    gam := 2
    values := nVal x n
    below := prodAt (AffSh.mk [] [nVal x n]) x.valueM x.pairs (nVal x n + 2)
    on := prodAt (AffSh.mk [] [nVal x n + 1]) x.valueD x.pairs (nOn x n)
    point := 2 * x.lgk + 2 * x.lt + 4
    maxima := nMax x n
    om := x.pairs
    atIndex := prodAt (batchedSh x.pairs (nMax x n) 1 0) x.attained x.pairs (nIdx x n)
    om' := x.pairs
    key := sumShAt
      (batchedSh x.pairs
        (prodAt (batchedSh x.pairs (nMax x n) 1 0) x.attained x.pairs (nIdx x n)).sEnd 2 1)
      ((List.replicate x.lt 3 ++ List.replicate x.lgk (x.lt + 3) ++
        List.replicate x.lt (x.lt + 2)).map .plain) ⟨x.lt + 1, x.Lam + x.pairs * x.lt⟩ (nKey x n)
    om'' := x.pairs
    cells := prodAt (AffSh.mk [] []) x.bits x.pairs (nCells x n) }

/-- So many powers. The library has it too (`powersFrom_len`,
Johnson/Desc/Part/MaskedSumLedger.lean), in a file that this one does not import. -/
theorem powers_len (y : E) : ∀ (n : Nat) (a : E), (MaskedSum.powersFrom y n a).length = n
  | 0, _ => rfl
  | n + 1, a => by
    show (MaskedSum.powersFrom y n (mulE a y)).length + 1 = n + 1
    rw [powers_len y n]

/-- n scalars are taken. -/
theorem take_sh {n j lead lead' : Nat} {F G : Fork} {rs rs' : List Fmt.RoundView}
    (h : take n (F, rs, lead) = some (j, G, rs', lead')) (hz : Sized F) :
    j = F.next ∧ G.next = F.next + n := by
  obtain ⟨e1, _, _, r, rest, v, _, _, _, hG⟩ := take_spec h
  exact ⟨e1, (hideRun_ok _ _ _ _ _ hG ⟨hz.vp, hz.mf, hz.got⟩).next⟩

/-- A sumcheck is heard. -/
theorem sum_sh {C : Aff} {vs : List Var} {e : Ends} {hh : MaskedSum.Heard} {lead lead' : Nat}
    {F G : Fork} {rs rs' : List Fmt.RoundView}
    (h : sum C (.sum vs e) (F, rs, lead) = some (hh, G, rs', lead')) (hz : Sized F) :
    sumSh hh = sumShAt (affSh C) vs e F.next ∧ G.next = F.next + (Stage.sum vs e).slots := by
  obtain ⟨_, _, G1, f, a1, a2⟩ := sum_spec h
  obtain ⟨hsh, T, Rd, b1, b2, b3, b4⟩ := MaskedSum.hear_spec a1
  obtain ⟨r0, used, rv, front, c1, c2, c3, c4, c5⟩ := MaskedSum.readAll_spec b2
  have hall : (⟨lead, vs, some e⟩ : MaskedSum.Call).all = vs ++ [.point zeroE (e.dY + 1)] := rfl
  rw [hall] at b3 b4
  have F1 := hideRun_ok _ _ _ _ _ b4 ⟨hz.vp, hz.mf, hz.got⟩
  have F2 := hideRun_ok _ _ _ _ _ (row_write a2) F1.sized
  have hr : (Rd.rounds.map (·.2)).length = vs.length + 1 := by
    rw [List.length_map, c4.length.2]
    show (vs ++ [Var.point zeroE (e.dY + 1)]).length = vs.length + 1
    rw [List.length_append]
    rfl
  refine ⟨?_, ?_⟩
  · rw [b3]
    unfold sumSh sumShAt
    simp only [List.map_append, List.map_cons, List.map_nil, hr]
    rfl
  · rw [F2.next, F1.next]
    show F.next + MaskedSum.ownSlots (vs ++ [.point zeroE (e.dY + 1)]) + Rd.values.length =
      F.next + (MaskedSum.ownSlots (vs ++ [.point zeroE (e.dY + 1)]) + e.n)
    rw [c5.2.1, Nat.add_assoc]

/-- The plane messages' scalars are taken (`TakesRan`, Johnson/Desc/First/Att/K5Shape.lean). -/
theorem takes_sh : ∀ (k : Nat) (js : List Nat) (s s' : St), TakesRan 3 k js s s' → Sized s.1 →
    js = takesAt k s.1.next ∧ s'.1.next = s.1.next + 3 * k
  | 0, [], _, _, h, _ => by
    have e : _ = _ := h
    rw [e]
    exact ⟨rfl, rfl⟩
  | k + 1, _ :: js, ⟨F, rs, lead⟩, s', ⟨⟨F1, rs1, l1⟩, h1, h2⟩, hz => by
    obtain ⟨z1, _⟩ := take_below h1 hz
    obtain ⟨a1, a2⟩ := take_sh h1 hz
    obtain ⟨b1, b2⟩ := takes_sh k js _ s' h2 z1
    refine ⟨?_, ?_⟩
    · rw [a1, b1]
      show F.next :: takesAt k F1.next = F.next :: takesAt k (F.next + 3)
      rw [a2]
    · rw [b2]
      show F1.next + 3 * k = F.next + 3 * (k + 1)
      rw [a2]
      omega
  | 0, _ :: _, _, _, h, _ => h.elim
  | _ + 1, [], _, _, h, _ => h.elim

/-- The units of the scores are heard (`UnitsRan`, Att/K5Shape.lean). -/
theorem units_sh : ∀ (us : List (Nat × Nat)) (os : List (Nat × MaskedSum.Heard)) (s s' : St),
    UnitsRan us os s s' → Sized s.1 →
    (os.map fun o => (o.1, sumSh o.2)) = unitsAt us s.1.next ∧ s'.1.next = unitsEnd us s.1.next
  | [], [], _, _, h, _ => by
    have e : _ = _ := h
    rw [e]
    exact ⟨rfl, rfl⟩
  | u :: us, o :: os, ⟨F, rs, lead⟩, s', ⟨s2, ⟨⟨F1, rs1, l1⟩, h1, h2⟩, h3⟩, hz => by
    obtain ⟨F2, rs2, l2⟩ := s2
    obtain ⟨z1, _⟩ := take_below h1 hz
    obtain ⟨z2, _⟩ := sum_below h2 z1
    obtain ⟨a1, a2⟩ := take_sh h1 hz
    obtain ⟨b1, b2⟩ := sum_sh h2 z1
    obtain ⟨c1, c2⟩ := units_sh us os _ s' h3 z2
    have n2 : F2.next = F.next + 7 + (products u.1 u.2).slots := by rw [b2, a2]; rfl
    refine ⟨?_, ?_⟩
    · rw [List.map_cons, c1, b1, affSh_slot, a1, a2]
      show _ :: unitsAt us F2.next = _
      rw [n2]
      rfl
    · rw [c2]
      show unitsEnd us F2.next = _
      rw [n2]
      rfl
  | [], _ :: _, _, _, h, _ => h.elim
  | _ :: _, [], _, _, h, _ => h.elim

/-- **THE SHAPE OF WHAT THE HEARING HANDS ON IS THAT FUNCTION OF THE PLAN's NUMBERS AND OF THE NEXT
FREE NUMBER IN FRONT.** CONDITIONAL on: the hearing returns; the three arrays on slots of the ledger
in front have their length. -/
theorem heard5_sh {x : Params.AttentionRounds} {F G : Fork} {rs rs' : List Fmt.RoundView}
    {lead lead' : Nat} {h : Heard} (hh : hear x (F, rs, lead) = some (h, G, rs', lead'))
    (hz : Sized F) : heard5Sh h = heard5At x F.next := by
  obtain ⟨sa, sb, ⟨F1, r1, l1⟩, ⟨F2, r2, l2⟩, ⟨F3, r3, l3⟩, ⟨F4, r4, l4⟩, ⟨F5, r5, l5⟩,
    ⟨F6, r6, l6⟩, ⟨F7, r7, l7⟩, ⟨F8, r8, l8⟩, ⟨F9, r9, l9⟩, ⟨F10, r10, l10⟩, ⟨F11, r11, l11⟩,
    ⟨F12, r12, l12⟩, ⟨F13, r13, l13⟩, ⟨F14, r14, l14⟩, ⟨F15, r15, l15⟩, pt, ha, hb, h1, h2, h3,
    h4, h5, h6, h7, h8, h9, hpt, h10, h11, h12, h13, h14, h15, h16⟩ := (hear_ran hh).ran
  obtain ⟨Fb, rb, lb⟩ := sb
  obtain ⟨e5, _, _, y5, _, _, _, w5⟩ := batch_spec h5
  obtain ⟨e9, _, _, _, _, q9, d9⟩ := close_spec h9
  obtain ⟨e11, _, _, y11, _, _, _, w11⟩ := batch_spec h11
  obtain ⟨e13, _, _, y13, _, _, _, w13⟩ := batch_spec h13
  obtain ⟨e15, _, _, y15, _, _, _, w15⟩ := batch_spec h15
  subst e5 e9 e11 e13 e15
  obtain ⟨za, _⟩ := takes_below _ _ _ sa ha hz
  obtain ⟨zb, _⟩ := units_below _ _ _ _ hb za
  obtain ⟨z1, _⟩ := take_below h1 zb
  obtain ⟨z2, _⟩ := take_below h2 z1
  obtain ⟨z3, _⟩ := take_below h3 z2
  obtain ⟨z4, _⟩ := sum_below h4 z3
  obtain ⟨z6, _⟩ := take_below h6 z4
  obtain ⟨z7, _⟩ := sum_below h7 z6
  obtain ⟨z8, _⟩ := sum_below h8 z7
  obtain ⟨z10, _⟩ := take_below h10 z8
  obtain ⟨z12, _⟩ := sum_below h12 z10
  obtain ⟨z14, _⟩ := sum_below h14 z12
  obtain ⟨ta, na⟩ := takes_sh _ _ _ sa ha hz
  obtain ⟨ub, nb⟩ := units_sh _ _ _ _ hb za
  have na' : sa.1.next = F.next + 3 * x.planeMessages := na
  have nb' : Fb.next = nFive x F.next := by
    have e : Fb.next = unitsEnd x.score sa.1.next := nb
    rw [e, na']
    rfl
  obtain ⟨t1, n1⟩ := take_sh h1 zb
  obtain ⟨t2, n2⟩ := take_sh h2 z1
  obtain ⟨t3, n3⟩ := take_sh h3 z2
  obtain ⟨s4, n4⟩ := sum_sh h4 z3
  obtain ⟨t6, n6⟩ := take_sh h6 z4
  obtain ⟨s7, n7⟩ := sum_sh h7 z6
  obtain ⟨s8, n8⟩ := sum_sh h8 z7
  obtain ⟨t10, n10⟩ := take_sh h10 z8
  obtain ⟨s12, n12⟩ := sum_sh h12 z10
  obtain ⟨s14, n14⟩ := sum_sh h14 z12
  obtain ⟨s16, _⟩ := sum_sh h16 z14
  have E5 : h.five = nFive x F.next := by rw [t1, nb']
  have Eb : h.bits = nFive x F.next + 5 := by rw [t2, n1, nb']
  have Et : h.two = nFive x F.next + 5 + x.lt := by rw [t3, n2, n1, nb']
  have N3 : F3.next = nDiv x F.next := by rw [n3, n2, n1, nb']; rfl
  have N4 : F5.next = nVal x F.next := by rw [n4, N3]; rfl
  have Ev : h.values = nVal x F.next := by rw [t6, N4]
  have N6 : F6.next = nVal x F.next + 2 := by rw [n6, N4]
  have N7 : F7.next = nOn x F.next := by rw [n7, N6]; rfl
  have N8 : F9.next = nMax x F.next := by rw [n8, N7]; rfl
  have Em : h.maxima = nMax x F.next := by rw [t10, N8]
  have N10 : F11.next = nIdx x F.next := by rw [n10, N8]; rfl
  have N12 : F13.next = nKey x F.next := by rw [n12, N10]; rfl
  have N14 : F15.next = nCells x F.next := by rw [n14, N12]; rfl
  have Ed : sumSh h.division =
      prodAt (AffSh.mk [] [nFive x F.next + 1]) x.e x.pairs (nDiv x F.next) := by
    rw [s4, affSh_slot, E5, N3]
    rfl
  have Ebl : sumSh h.below =
      prodAt (AffSh.mk [] [nVal x F.next]) x.valueM x.pairs (nVal x F.next + 2) := by
    rw [s7, affSh_slot, Ev, N6]
    rfl
  have Eon : sumSh h.on =
      prodAt (AffSh.mk [] [nVal x F.next + 1]) x.valueD x.pairs (nOn x F.next) := by
    rw [s8, affSh_slot, Ev, N7]
    rfl
  have Eat : sumSh h.atIndex =
      prodAt (batchedSh x.pairs (nMax x F.next) 1 0) x.attained x.pairs (nIdx x F.next) := by
    rw [s12, affSh_batched, Em, N10]
    rfl
  have Ese : h.atIndex.sEnd =
      (prodAt (batchedSh x.pairs (nMax x F.next) 1 0) x.attained x.pairs (nIdx x F.next)).sEnd :=
    congrArg SumSh.sEnd Eat
  have Ek : sumSh h.key = sumShAt
      (batchedSh x.pairs
        (prodAt (batchedSh x.pairs (nMax x F.next) 1 0) x.attained x.pairs (nIdx x F.next)).sEnd
        2 1)
      ((List.replicate x.lt 3 ++ List.replicate x.lgk (x.lt + 3) ++
        List.replicate x.lt (x.lt + 2)).map .plain) ⟨x.lt + 1, x.Lam + x.pairs * x.lt⟩
      (nKey x F.next) := by
    rw [s14, affSh_batched, Ese, N12]
  have Ec : sumSh h.cells = prodAt (AffSh.mk [] []) x.bits x.pairs (nCells x F.next) := by
    rw [s16, affSh_ofConst, N14]
    rfl
  have Eg : h.gam.size = 2 := by rw [w5, List.size_toArray, powers_len]
  have Eo : h.om.size = x.pairs := by rw [w11, List.size_toArray, powers_len]
  have Eo' : h.om'.size = x.pairs := by rw [w13, List.size_toArray, powers_len]
  have Eo'' : h.om''.size = x.pairs := by rw [w15, List.size_toArray, powers_len]
  have Ep : h.point.size = 2 * x.lgk + 2 * x.lt + 4 := by
    rw [hpt, List.size_toArray, d9, List.length_map, q9]
  have Eu : (h.scores.toList.map fun o => (o.1, sumSh o.2)) =
      unitsAt x.score (F.next + 3 * x.planeMessages) := by
    rw [ub, na']
  unfold heard5Sh heard5At
  rw [ta, Eu, E5, Eb, Et, Ed, Eg, Ev, Ebl, Eon, Ep, Em, Eo, Eat, Eo', Ek, Eo'', Ec]

/-! ## 3 The kind's shape, its one Bool and its one update -/

/-- **What the kind's decision reads and lays of the state, as a shape**: five readers OF THE STATE.
Four bear the names of the components of the first chain's shape that are made of the same fields
(Johnson/Desc/First/Shape/Chain.lean, which this file does not import: marked, rowsOwed, look, led);
the fifth: the attention link's own fields (Shape/AttOwn.lean). -/
structure K5Sh where
  marked : Bool
  rowsOwed : Option Nat
  look : Bool
  led : Option LedSh
  att : Option AttOwnSh

def k5Sh (s : First.S) : K5Sh :=
  { marked := s.failed.isSome, rowsOwed := s.rowsOwed, look := s.look?.isSome
    led := s.fork?.map ledSh, att := attOf s.here }

/-- No count of rows waits (S.noneWaits, Johnson/Desc/First/State.lean). -/
def noneWaitsB : Option Nat → Bool
  | none => true
  | some r => r == 0

/-- **THE KIND's GUARDS AS ONE BOOL.** x: the plan's numbers of the segment's rounds. No mark; no
count of rows waits; the lookup on the calls has laid its return; an attention link stands open
whose own rounds have not been heard; the ledger's arrays have their size and the slots that the
rounds take are there and free. -/
def k5G (x : Params.AttentionRounds) (a : K5Sh) : Bool :=
  !a.marked && noneWaitsB a.rowsOwed && a.look &&
    match a.att, a.led with
    | some t, some L => t.heard5.isNone && freeB L L.next (slotsOf (script x))
    | _, _ => false

/-- The ledger's shape behind: n slots from the next free number on are filled, and that number
moves by n. -/
def ledStep (n : Nat) (L : LedSh) : LedSh :=
  LedSh.mk L.ns L.shown L.factors (fillB L.got L.next n) L.owed L.planClaims L.trees (L.next + n)
    L.coefs L.claims L.drawn L.handed L.shut

/-- **THE KIND's STEP AS ONE UPDATE.** -/
def k5Step (x : Params.AttentionRounds) (a : K5Sh) : K5Sh :=
  { a with
    rowsOwed := none
    led := a.led.map (ledStep (slotsOf (script x)))
    att := match a.att, a.led with
      | some t, some L => some { t with heard5 := some (heard5At x L.next) }
      | t, _ => t }

/-- The shape at a state that stands in an attention link. -/
theorem k5Sh_att {s : First.S} {a : First.AttOwn} (h : s.here = .att a) :
    k5Sh s = { marked := s.failed.isSome, rowsOwed := s.rowsOwed, look := a.g.isSome
               led := some (ledSh a.F), att := some (attOwnSh a) } := by
  unfold k5Sh First.S.look? First.S.fork?
  rw [h]
  rfl

/-- **Where the Bool says yes the state is ready** (`ReadyO`,
Johnson/Desc/First/Att/K05SeatAccepts.lean). -/
theorem readyO_of_G (p : Par) {s : First.S} (h : k5G p.own (k5Sh s) = true) : ReadyO p s := by
  obtain ⟨a, ha⟩ : ∃ a, s.here = .att a := by
    cases e : s.here with
    | att a => exact ⟨a, rfl⟩
    | _ => simp [k5G, k5Sh, attOf, e] at h
  rw [k5Sh_att ha] at h
  simp only [k5G, Bool.and_eq_true, Bool.not_eq_true', Option.isSome_eq_false_iff,
    Option.isNone_iff_eq_none] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4, h5⟩ := h
  obtain ⟨g, hg⟩ := Option.isSome_iff_exists.1 h3
  have h4' : a.heard5 = none := by
    cases e : a.heard5 with
    | none => rfl
    | some y =>
      have : (attOwnSh a).heard5 = some (heard5Sh y) := by
        show a.heard5.map heard5Sh = _
        rw [e]
        rfl
      rw [this] at h4
      cases h4
  obtain ⟨f1, f2, f3⟩ := free_of_B h5
  have f2' : a.F.next + slotsOf (script p.own) ≤ a.F.ns := f2
  refine ⟨⟨a, g, ha, hg, h4', ⟨f1.1, f1.2.1, f1.2.2⟩, f1.2.2, f2', fun j j1 j2 => ?_⟩, h1, h2⟩
  have k := f3 (j - a.F.next) (by omega)
  have e : (ledSh a.F).next + (j - a.F.next) = j := by
    show a.F.next + (j - a.F.next) = j
    omega
  rw [e] at k
  have hs : j < a.F.gotF.size := by
    rw [f1.2.2]
    omega
  unfold OnBytes.PscRun.Filled at k
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hs] at k ⊢
  simpa using k

/-- **RETURNS: where the Bool says yes at the shape in front, the kind's decision returns**, at
rounds of the plan's shape. CONDITIONAL on: the test on the plan; the rounds' shape. No premise
speaks of a value. One way alone: the Bool asks two sizes that the decision's text does not test. -/
theorem k5_shape_returns (p : Par) (hp : planOk p = true) {s : First.S}
    (h : k5G p.own (k5Sh s) = true) {rs : List Fmt.RoundView}
    (hfit : Fits ((rounds p).map (·.entry)) rs) : ∃ s', decide seatSO p s rs = .ok s' := by
  obtain ⟨a, hd, G, _, _, e⟩ := k5_returns p hp (readyO_of_G p h) hfit
  exact ⟨_, e⟩

/-- The ledger but for its next free number and its three arrays on slots. -/
theorem eq_of_bare {F G : Fork} (h : bare G = bare F) :
    G = { F with next := G.next, gotF := G.gotF, vp := G.vp, mf := G.mf } := by
  cases F
  cases G
  simp [bare] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
  rfl

/-- **The ledger's shape behind the hearing is the update of the shape in front.** CONDITIONAL on:
the hearing returns; the arrays' lengths; the stretch's slots are there and free in front. -/
theorem ledSh_behind {x : Params.AttentionRounds} {F G : Fork} {rs rs' : List Fmt.RoundView}
    {lead lead' : Nat} {h : Heard} (hh : hear x (F, rs, lead) = some (h, G, rs', lead'))
    (hz : Sized F) (hfree : Free F F.next (slotsOf (script x))) :
    ledSh G = ledStep (slotsOf (script x)) (ledSh F) := by
  obtain ⟨hn, hs, hg⟩ := filled_behind hh hz hfree
  obtain ⟨zG, bl⟩ := hear_below hh hz
  have hns : G.ns = F.ns := bl.ns
  have eg : G.gotF.toList = fillB F.gotF.toList F.next (slotsOf (script x)) := by
    rw [fillB_zip _ _ _ (by rw [Array.length_toList, hz.got]; exact hfree.2.1)]
    refine List.ext_getElem (by simp [hs]) fun i i1 i2 => ?_
    have iG : i < G.gotF.size := by simpa using i1
    have iF : i < F.gotF.size := by rw [← hs]; exact iG
    have e := hg i false
    rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem iG,
      Array.getElem?_eq_getElem iF] at e
    simp only [Option.getD_some] at e
    simp only [List.getElem_map, List.getElem_zipIdx, Array.getElem_toList, Nat.zero_add]
    rw [e]
    by_cases hin : F.next ≤ i ∧ i < F.next + slotsOf (script x)
    · simp [hin.1, hin.2]
    · rw [if_neg hin]
      have hb : (Decidable.decide (F.next ≤ i) &&
          Decidable.decide (i < F.next + slotsOf (script x))) = false := by
        simpa using fun a => by omega
      rw [hb, Bool.or_false]
  have e2 := congrArg ledSh (eq_of_bare bl.2.1)
  rw [e2]
  show LedSh.mk F.ns G.vp.size G.mf.size G.gotF.toList (F.owed.toList.map (·.added))
      F.planClaimsF (F.trees.toList.map treeSh) G.next F.LS.size F.nClaim F.thetaDrawnF
      F.kapMapF.toList F.doorShutF =
    LedSh.mk F.ns F.vp.size F.mf.size (fillB F.gotF.toList F.next (slotsOf (script x)))
      (F.owed.toList.map (·.added)) F.planClaimsF (F.trees.toList.map treeSh)
      (F.next + slotsOf (script x)) F.LS.size F.nClaim F.thetaDrawnF F.kapMapF.toList F.doorShutF
  rw [eg, hn, zG.vp, zG.mf, hz.vp, hz.mf, hns]

/-- **CARRIES: where the kind's decision says yes and the Bool says yes at the shape in front, the
shape behind is the update of the shape in front.** CONDITIONAL on these two. -/
theorem k5_shape_carries (p : Par) {s s' : First.S} {rs : List Fmt.RoundView}
    (h : decide seatSO p s rs = .ok s') (hG : k5G p.own (k5Sh s) = true) :
    k5Sh s' = k5Step p.own (k5Sh s) := by
  obtain ⟨a, hd, G, ha, hh, rfl⟩ := k5_yes_is p h
  obtain ⟨a', _, ha', _, _, hz, hfree⟩ := (readyO_of_G p hG).open_
  rw [ha] at ha'
  cases ha'
  have hb : (behind s a hd G).here = .att { a with F := G, heard5 := some hd } := rfl
  rw [k5Sh_att hb, k5Sh_att ha]
  unfold k5Step
  simp only [Option.map_some]
  rw [ledSh_behind hh hz hfree]
  have e1 : attOwnSh { a with F := G, heard5 := some hd } =
      { attOwnSh a with heard5 := some (heard5Sh hd) } := rfl
  rw [e1, heard5_sh hh hz]
  rfl

/-- Seven controls: the Bool says no at a mark; where a count of rows waits; where the lookup has
laid nothing; where no attention link stands open; where no ledger is there; where the link's own
rounds have been heard; where the slots are not there and free. -/
theorem k5G_bites (x : Params.AttentionRounds) (a : K5Sh) :
    (a.marked = true → k5G x a = false) ∧ (noneWaitsB a.rowsOwed = false → k5G x a = false) ∧
      (a.look = false → k5G x a = false) ∧ (a.att = none → k5G x a = false) ∧
      (a.led = none → k5G x a = false) ∧
      (∀ t y, a.att = some t → t.heard5 = some y → k5G x a = false) ∧
      (∀ L, a.led = some L → freeB L L.next (slotsOf (script x)) = false → k5G x a = false) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun t y h1 h2 => ?_,
    fun L h1 h2 => ?_⟩
  · simp [k5G, h]
  · simp [k5G, h]
  · simp [k5G, h]
  · simp [k5G, h]
  · cases e : a.att <;> simp [k5G, h, e]
  · cases e : a.led <;> simp [k5G, h1, h2, e]
  · cases e : a.att <;> simp [k5G, h1, h2, e]

end H2K5.Honest

#print axioms H2K5.Honest.affSh_batched
#print axioms H2K5.Honest.powers_len
#print axioms H2K5.Honest.take_sh
#print axioms H2K5.Honest.sum_sh
#print axioms H2K5.Honest.takes_sh
#print axioms H2K5.Honest.units_sh
#print axioms H2K5.Honest.heard5_sh
#print axioms H2K5.Honest.k5Sh_att
#print axioms H2K5.Honest.readyO_of_G
#print axioms H2K5.Honest.k5_shape_returns
#print axioms H2K5.Honest.eq_of_bare
#print axioms H2K5.Honest.ledSh_behind
#print axioms H2K5.Honest.k5_shape_carries
#print axioms H2K5.Honest.k5G_bites
