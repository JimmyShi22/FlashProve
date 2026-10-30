-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/Numbers.lean: CONDITIONAL: the numbers of scalars that the verifier's
hearing of an attention segment's own rounds hands on (the fields of type Nat of Heard,
Johnson/Desc/First/Att/K5Heard.lean, and each sumcheck's first own slot), counted from the first
slot that the hearing takes; and what lies in the ledger under the slots of each part, BY THE
FIELD's NAME. A definition of a proposition, and statements with their proofs. No frame of a prover
is imported, and no value of the honest side is spoken of.

Under the name Numbers stand the tools: takes_num, units_num, sums_units, sums_unit, sums_tail,
tailStarts, start_unit, start_tail, tail_put.
  names_are      CONDITIONAL: the named numbers against each other: a remainder unit's three scalars
                 stand at three times its number; a softmax-table unit's seven, the division's
                 5 + lt + 2, the value product's two and the maxima stand right in front of the
                 own slots of the sumcheck behind them
  Laid x n rs h G   each of the hearing's sumchecks, by its field's name, is laid as the row's part
                 of its number (SumPut, Johnson/Desc/K5/Honest/Law/Puts.lean), with the slots from
                 n + slotsTo x q on; the maxima's round likewise; and the named numbers
  laid_of_hear   CONDITIONAL: **where the hearing returns from a ledger F whose arrays have their
                 length: Laid x F.next rs h G**, G the ledger behind

Limits. One direction, from a return. Nothing is said of what a slot hides.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.Puts
import Johnson.Desc.K5.Honest.Law.Named
import Johnson.Desc.First.Att.K5SaidAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Honest
open OnBytes (E zeroE oneE)
open OnBytes.Model (Aff Fork)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Call)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (St Heard Open open_zero take_said sum_said close_said
  batch_said TakesRan UnitsRan hear_ran takes_said units_said batched)

namespace Numbers

/-- The remainder units' scalars stand three by three. -/
theorem takes_num : ∀ (k : Nat) (js : List Nat) (F G : Fork) (rs rs' : List Fmt.RoundView)
    (lead lead' : Nat) (pre : List E), TakesRan 3 k js (F, rs, lead) (G, rs', lead') →
    OnBytes.Model.Road.Sized F → Open rs lead pre → ∀ i r, js[i]? = some r → r = F.next + 3 * i
  | 0, [], _, _, _, _, _, _, _, _, _, _ => fun i r h => by cases h
  | k + 1, j :: js, F, G, rs, rs', lead, lead', pre, ⟨⟨F1, rs1, l1⟩, h1, h2⟩, hz, ho => by
    obtain ⟨v, _, _, a3, a4, a5, _, _, a8⟩ := take_said h1 hz ho
    intro i r hi
    cases i with
    | zero =>
      obtain rfl := Option.some.inj hi
      exact a4
    | succ i =>
      rw [takes_num k js F1 G rs1 rs' l1 lead' (pre ++ v) h2 a5 a3 i r hi, a8]
      omega
  | 0, _ :: _, _, _, _, _, _, _, _, h, _, _ => h.elim
  | _ + 1, [], _, _, _, _, _, _, _, h, _, _ => h.elim

/-- A softmax-table unit's seven scalars stand right in front of its sumcheck's own slots. -/
theorem units_num : ∀ (us : List (Nat × Nat)) (os : List (Nat × MaskedSum.Heard)) (F G : Fork)
    (rs rs' : List Fmt.RoundView) (lead lead' : Nat) (pre : List E),
    UnitsRan us os (F, rs, lead) (G, rs', lead') → OnBytes.Model.Road.Sized F → Open rs lead pre →
    os.length = us.length ∧ ∀ o ∈ os, o.1 + 7 = o.2.first
  | [], [], _, _, _, _, _, _, _, _, _, _ => ⟨rfl, fun o h => by cases h⟩
  | u :: us, o :: os, F, G, rs, rs', lead, lead', pre,
      ⟨⟨F2, rs2, l2⟩, ⟨⟨F1, rs1, l1⟩, h1, h2⟩, h3⟩, hz, ho => by
    obtain ⟨v7, _, _, a3, a4, a5, _, _, a8⟩ := take_said h1 hz ho
    obtain ⟨b1, H, used, _, b3⟩ := sum_said h2 a5 a3
    subst b1
    obtain ⟨c1, c2⟩ := units_num us os F2 G rs2 rs' 0 lead' [] h3 b3.sized (open_zero _)
    refine ⟨congrArg (· + 1) c1, fun o' ho' => ?_⟩
    rcases List.mem_cons.1 ho' with rfl | h'
    · rw [b3.first, a8, a4]
    · exact c2 o' h'
  | [], _ :: _, _, _, _, _, _, _, _, h, _, _ => h.elim
  | _ :: _, [], _, _, _, _, _, _, _, h, _, _ => h.elim

/-- All of the softmax-table units' parts are masked sumchecks. -/
theorem sums_units : ∀ (us : List (Nat × Nat)) (lead i : Nat), i ≤ us.length →
    (((unitsShapes lead us).take i).filter isSum).length = i
  | [], _, i, h => by
    obtain rfl : i = 0 := Nat.le_zero.1 h
    rfl
  | _ :: _, _, 0, _ => rfl
  | u :: us, lead, i + 1, h => by
    have e : ((unitsShapes lead (u :: us)).take (i + 1)).filter isSum =
        productsShape (lead + 7) u.1 u.2 :: ((unitsShapes 0 us).take i).filter isSum := rfl
    rw [e, List.length_cons, sums_units us 0 i (Nat.le_of_succ_le_succ h)]

/-- In front of the unit number i stand i masked sumchecks. -/
theorem sums_unit (x : OnBytes.Params.AttentionRounds) {i : Nat} (hi : i ≤ x.score.length) :
    (((shapes x).take i).filter isSum).length = i := by
  rw [shapes_eq, List.take_append_of_le_length (by rw [unitsShapes_length]; exact hi),
    sums_units _ _ _ hi]

/-- In front of the part number j behind the units stand the units' and those of the parts behind
them. -/
theorem sums_tail (x : OnBytes.Params.AttentionRounds) (j : Nat) :
    (((shapes x).take (x.score.length + j)).filter isSum).length =
      x.score.length + (((tailShapes x (leadBehind x)).take j).filter isSum).length := by
  have h0 := sums_units x.score (x.planeMessages * 3) x.score.length (Nat.le_refl _)
  rw [List.take_of_length_le (by rw [unitsShapes_length])] at h0
  rw [shapes_eq, List.take_append, List.take_of_length_le (by rw [unitsShapes_length]; omega),
    unitsShapes_length, Nat.add_sub_cancel_left, List.filter_append, List.length_append, h0]

/-- The start forms and what was heard of the six sumchecks behind the units'. -/
def tailStarts (x : OnBytes.Params.AttentionRounds) (h : Heard) : List (Aff × MaskedSum.Heard) :=
  [(.slot (h.five + 1), h.division), (.slot h.values, h.below), (.slot (h.values + 1), h.on),
    (batched x.pairs h.om h.maxima 1 0, h.atIndex),
    (batched x.pairs h.om' h.atIndex.sEnd 2 1, h.key), (.ofConst zeroE, h.cells)]

theorem start_unit (x : OnBytes.Params.AttentionRounds) (h : Heard) {i : Nat}
    {o : Nat × MaskedSum.Heard} (ho : h.scores[i]? = some o) :
    (startsOf x h)[i]? = some (Aff.slot (o.1 + 6), o.2) := by
  have hi : i < h.scores.size := by
    rcases Nat.lt_or_ge i h.scores.size with h1 | h1
    · exact h1
    · rw [Array.getElem?_eq_none h1] at ho
      cases ho
  unfold startsOf
  rw [List.getElem?_append_left (by rw [List.length_map, Array.length_toList]; exact hi),
    List.getElem?_map, Array.getElem?_toList, ho]
  rfl

theorem start_tail (x : OnBytes.Params.AttentionRounds) (h : Heard)
    (hs : h.scores.size = x.score.length) (t : Nat) :
    (startsOf x h)[x.score.length + t]? = (tailStarts x h)[t]? := by
  show ((h.scores.toList.map fun o => (Aff.slot (o.1 + 6), o.2)) ++ tailStarts x h)[_]? = _
  rw [List.getElem?_append_right (by rw [List.length_map, Array.length_toList, hs]; omega),
    List.length_map, Array.length_toList, hs, Nat.add_sub_cancel_left]

end Numbers

open Numbers

/-! ## 1 The named numbers against each other -/

/-- **The named numbers against each other.** CONDITIONAL: the hearing's return; the ledger's arrays
have their length. -/
theorem names_are {x : OnBytes.Params.AttentionRounds} {F G : Fork} {rs rest : List Fmt.RoundView}
    {lead : Nat} {h : Heard} (hh : P.hear x (F, rs, 0) = some (h, G, rest, lead))
    (hz : OnBytes.Model.Road.Sized F) :
    (∀ i r, h.remainders[i]? = some r → r = F.next + 3 * i) ∧
      h.scores.size = x.score.length ∧ (∀ o ∈ h.scores.toList, o.1 + 7 = o.2.first) ∧
      h.bits = h.five + 5 ∧ h.two = h.five + 5 + x.lt ∧
      h.five + (5 + x.lt + 2) = h.division.first ∧ h.values + 2 = h.below.first ∧
      h.maxima + x.pairs = h.atIndex.first := by
  obtain ⟨⟨Fa, rsa, la⟩, ⟨Fb, rsb, lb⟩, ⟨F1, rs1, l1⟩, ⟨F2, rs2, l2⟩, ⟨F3, rs3, l3⟩,
    ⟨F4, rs4, l4⟩, ⟨F5, rs5, l5⟩, ⟨F6, rs6, l6⟩, ⟨F7, rs7, l7⟩, ⟨F8, rs8, l8⟩, ⟨F9, rs9, l9⟩,
    ⟨F10, rs10, l10⟩, ⟨F11, rs11, l11⟩, ⟨F12, rs12, l12⟩, s13, s14, s15, pt, ha, hb, h1, h2, h3,
    h4, h5, h6, h7, h8, h9, hpt, h10, h11, h12, _⟩ := (hear_ran hh).ran
  have n1 := takes_num _ _ _ _ _ _ _ _ [] ha hz (open_zero _)
  obtain ⟨planes, _, _, pa3, pa4, _, _⟩ := takes_said _ _ _ _ _ _ _ _ [] ha hz (open_zero _)
  obtain ⟨n2, n3⟩ := units_num _ _ _ _ _ _ _ _ _ hb pa4 pa3
  obtain ⟨units, usedU, _, _, ub3, ub4, _, _⟩ := units_said _ _ _ _ _ _ _ _ _ hb pa4 pa3
  obtain ⟨v5, _, _, a3, a4, a5, _, _, a8⟩ := take_said h1 ub4 ub3
  obtain ⟨vI, _, _, b3, b4, b5, _, _, b8⟩ := take_said h2 a5 a3
  obtain ⟨v2, _, _, c3, c4, c5, _, _, c8⟩ := take_said h3 b5 b3
  obtain ⟨d0, HE, usedE, _, d2⟩ := sum_said h4 c5 c3
  subst d0
  obtain ⟨e1, e0, r5, xV, _, _, _⟩ := batch_said h5 (open_zero _)
  subst e0 e1
  obtain ⟨vC, _, _, f3, f4, f5, _, _, f8⟩ := take_said h6 d2.sized (open_zero _)
  obtain ⟨g0, HM, usedM, _, g2⟩ := sum_said h7 f5 f3
  subst g0
  obtain ⟨i0, HVD, usedVD, _, i2⟩ := sum_said h8 g2.sized (open_zero _)
  subst i0
  obtain ⟨j1, j0, _, r9, _, _⟩ := close_said h9 (open_zero _)
  subst j0 j1
  obtain ⟨vM, _, _, k3, k4, k5, _, _, k8⟩ := take_said h10 i2.sized (open_zero _)
  obtain ⟨m1, m0, r11, xF, _, _, _⟩ := batch_said h11 k3
  subst m0 m1
  obtain ⟨_, HF, usedF, _, q2⟩ := sum_said h12 k5 (open_zero _)
  refine ⟨fun i r hr => n1 i r (by rw [Array.getElem?_toList]; exact hr), ?_, n3, ?_, ?_, ?_, ?_,
    ?_⟩
  · rw [← n2, Array.length_toList]
  · rw [b4, a8, a4]
  · rw [c4, b8, a8, a4]
  · rw [d2.first, c8, b8, a8, a4]
    omega
  · rw [g2.first, f8, f4]
  · rw [q2.first, k8, k4]

/-! ## 2 By the field's name -/

/-- **The hearing's sumchecks and numbers, laid as the row's parts.** n: the first slot that the
hearing takes; rs: its rounds; G: the ledger behind. It is a definition. -/
structure Laid (x : OnBytes.Params.AttentionRounds) (n : Nat) (rs : List Fmt.RoundView) (h : Heard)
    (G : Fork) : Prop where
  size : h.scores.size = x.score.length
  unit : ∀ i o k, h.scores[i]? = some o → (shapes x)[i]? = some (.sum k) →
    SumPut k (n + slotsTo x i) (rs.drop (firstOf x i)) o.2 G ∧ o.1 + 7 = o.2.first
  division : ∀ k, (shapes x)[iSE x]? = some (.sum k) →
    SumPut k (n + slotsTo x (iSE x)) (rs.drop (firstOf x (iSE x))) h.division G
  below : ∀ k, (shapes x)[iVM x]? = some (.sum k) →
    SumPut k (n + slotsTo x (iVM x)) (rs.drop (firstOf x (iVM x))) h.below G
  on : ∀ k, (shapes x)[iVD x]? = some (.sum k) →
    SumPut k (n + slotsTo x (iVD x)) (rs.drop (firstOf x (iVD x))) h.on G
  atIndex : ∀ k, (shapes x)[iSF x]? = some (.sum k) →
    SumPut k (n + slotsTo x (iSF x)) (rs.drop (firstOf x (iSF x))) h.atIndex G
  key : ∀ k, (shapes x)[iSD x]? = some (.sum k) →
    SumPut k (n + slotsTo x (iSD x)) (rs.drop (firstOf x (iSD x))) h.key G
  cells : ∀ k, (shapes x)[iHB x]? = some (.sum k) →
    SumPut k (n + slotsTo x (iHB x)) (rs.drop (firstOf x (iHB x))) h.cells G
  maxima : LeadPut x.pairs (n + slotsTo x (iM6 x)) (rs.drop (firstOf x (iM6 x))) G
  rem : ∀ i r, h.remainders[i]? = some r → r = n + 3 * i
  bits : h.bits = h.five + 5
  two : h.two = h.five + 5 + x.lt
  five : h.five + (5 + x.lt + 2) = h.division.first
  values : h.values + 2 = h.below.first
  max : h.maxima = n + slotsTo x (iM6 x)

namespace Numbers

/-- One of the six sumchecks behind the units', as part number (the units' number) + j. -/
theorem tail_put {x : OnBytes.Params.AttentionRounds} {F : Fork} {rs : List Fmt.RoundView} {s' : St}
    {h : Heard} (hh : P.hear x (F, rs, 0) = some (h, s')) (hz : OnBytes.Model.Road.Sized F)
    (hs : h.scores.size = x.score.length) (j t : Nat)
    (ht : (((tailShapes x (leadBehind x)).take j).filter isSum).length = t)
    {C0 : Aff} {hd0 : MaskedSum.Heard} (h0 : (tailStarts x h)[t]? = some (C0, hd0)) (k : Call)
    (hk : (shapes x)[x.score.length + j]? = some (.sum k)) :
    SumPut k (F.next + slotsTo x (x.score.length + j)) (rs.drop (firstOf x (x.score.length + j)))
      hd0 s'.1 := by
  obtain ⟨C, hd, e, S⟩ := sum_put hh hz _ k hk
  rw [sums_tail, ht, start_tail x h hs, h0] at e
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj e)
  exact S

end Numbers

/-- **Where the hearing returns: all is laid as the row's parts.** CONDITIONAL: the hearing's
return; the ledger's arrays have their length. -/
theorem laid_of_hear {x : OnBytes.Params.AttentionRounds} {F G : Fork} {rs rest : List Fmt.RoundView}
    {lead : Nat} {h : Heard} (hh : P.hear x (F, rs, 0) = some (h, G, rest, lead))
    (hz : OnBytes.Model.Road.Sized F) : Laid x F.next rs h G := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩ := names_are hh hz
  have T := fun j t ht C0 hd0 h0 k hk =>
    tail_put hh hz n2 j t ht (C0 := C0) (hd0 := hd0) h0 k hk
  have hF := T 6 3 rfl _ _ rfl _ (shape_iSF x)
  exact
    { size := n2
      unit := fun i o k ho hk => by
        obtain ⟨C, hd, e, S⟩ := sum_put hh hz i k hk
        have hi : i ≤ x.score.length := by
          rcases Nat.lt_or_ge i h.scores.size with h1 | h1
          · omega
          · rw [Array.getElem?_eq_none h1] at ho
            cases ho
        rw [sums_unit x hi, start_unit x h ho] at e
        obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj e)
        exact ⟨S, n3 o (Array.mem_toList_iff.2 (Array.mem_of_getElem? ho))⟩
      division := fun k hk => T 0 0 rfl _ _ rfl k hk
      below := fun k hk => T 2 1 rfl _ _ rfl k hk
      on := fun k hk => T 3 2 rfl _ _ rfl k hk
      atIndex := fun k hk => T 6 3 rfl _ _ rfl k hk
      key := fun k hk => T 8 4 rfl _ _ rfl k hk
      cells := fun k hk => T 10 5 rfl _ _ rfl k hk
      maxima := one_put hh hz (iM6 x) x.pairs (shape_iM6 x)
      rem := n1
      bits := n4
      two := n5
      five := n6
      values := n7
      max := by
        have h1 := hF.first
        have h2 := slotsTo_next x (shape_iM6 x)
        have h3 : (PartShape.one x.pairs).scalars = x.pairs := rfl
        have h4 : (productsShape 0 x.attained x.pairs) = .sum ⟨0, _, _⟩ := rfl
        have h5 : slotsTo x (x.score.length + 6) = slotsTo x (iM6 x + 1) := rfl
        rw [h3] at h2
        rw [h5, h2] at h1
        have h6 : h.atIndex.first = F.next + (slotsTo x (iM6 x) + x.pairs) + 0 := h1
        omega }

end H2K5.Honest

#print axioms H2K5.Honest.Numbers.takes_num
#print axioms H2K5.Honest.Numbers.units_num
#print axioms H2K5.Honest.Numbers.sums_units
#print axioms H2K5.Honest.Numbers.sums_unit
#print axioms H2K5.Honest.Numbers.sums_tail
#print axioms H2K5.Honest.Numbers.start_unit
#print axioms H2K5.Honest.Numbers.start_tail
#print axioms H2K5.Honest.names_are
#print axioms H2K5.Honest.Numbers.tail_put
#print axioms H2K5.Honest.laid_of_hear
