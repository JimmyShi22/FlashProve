-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/HeardIs.lean: CONDITIONAL: the honest prover's side of an attention
segment's own rounds: the challenges that the verifier's hearing holds (hear,
Johnson/Desc/First/Att/K5AttentionKind.lean) are those that the prover's side lays into the same type (heardAt,
Johnson/Desc/K5/Honest/Points.lean), field by field, word for word, BUT FOR each sumcheck's eps and
the challenge of its further variable: there the prover's side lays 0, and nothing is compared.
Definitions of propositions, and statements with their proofs. No frame of a prover is imported.

Under the name HeardIs stand the tools:
  cutOf, shapesOf_cut, tailCut, cut_eq, cut_unit, cut_at
                 the numbers of rounds of the row's parts, written out
  firstOf_next, firstOf_mono   a part's first round stands behind the part in front of it
  many_at, one_at   a round's elements, and its first, off challenges that hold them
  sum_part, batch_part, close_part, units_part   one verb of the hearing at the part number p
The statements:
  Reads c rs     the challenges c hold, round by round, the elements that the rounds rs drew; more
                 may follow
  SameTo x q a b    two values of the verifier's type for what was heard hold the same challenges in
                 all parts of the row in front of part number q: a sumcheck's variables'
                 challenges, a batching element's powers, the point; and they have as many
                 remainder units and softmax-table units. Numbers of scalars, starts, targets,
                 running claims, eps and the challenge of the further variable are NOT compared
  heard_is_ours  CONDITIONAL: **where the verifier's hearing returns at rounds whose challenges the
                 prover's side holds, SameTo holds of the two at every q, so in all parts**
  Agree n c c', heardAt_agree   two lists of challenges that are one in the first n rounds give
                 the same in all parts that end within these rounds

Who is meant to pay the premises. The hearing's return: whoever has the member's yes. Reads:
whoever ties the rounds as played to the challenges heard.

Limits. One direction, from a return. Nothing is said of a value that is sent. The key points of
the lookup's calls are not spoken of. No property is claimed by a definition.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K5.Honest.Law.Cells
import Johnson.Desc.First.Att.K5Shape

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes (E zeroE oneE)
open OnBytes.Model (Aff Fork)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Var Ends VarsRead Sent hear_spec readAll_spec)
open VerifiableInference.Desc.First.Att.P (Heard Stage script products hear take sum close batch
  chal St keyStage HearRan hear_ran TakesRan UnitsRan UnitRan take_spec sum_spec close_spec
  batch_spec)

/-! ## 1 The parts' numbers of rounds, written out -/

namespace HeardIs

/-- The numbers of rounds of the parts that a list of stages is folded into. -/
def cutOf : List Stage → List Nat
  | [] => []
  | .scalars _ :: l => cutOf l
  | .sum vs _ :: l => (vs.length + 3) :: cutOf l
  | .batch _ :: l => 1 :: cutOf l
  | .point _ :: l => 1 :: cutOf l

/-- The numbers of rounds of the eleven parts behind the softmax-table units' sumchecks. -/
def tailCut (x : OnBytes.Params.AttentionRounds) : List Nat :=
  [x.e + 3, 1, x.valueM + 3, x.valueD + 3, 1, 1, x.attained + 3, 1, x.lt + x.lgk + x.lt + 3, 1,
    x.bits + 3]

theorem shapesOf_cut : ∀ (st : List Stage) (lead : Nat),
    (shapesOf lead st).map (·.rounds) = cutOf st
  | [], _ => rfl
  | .scalars n :: l, lead => shapesOf_cut l (lead + n)
  | .sum vs _ :: l, _ => congrArg (List.cons (vs.length + 3)) (shapesOf_cut l 0)
  | .batch _ :: l, _ => congrArg (List.cons 1) (shapesOf_cut l 0)
  | .point _ :: l, _ => congrArg (List.cons 1) (shapesOf_cut l 0)

theorem cutOf_append : ∀ a b : List Stage, cutOf (a ++ b) = cutOf a ++ cutOf b
  | [], _ => rfl
  | .scalars _ :: l, b => cutOf_append l b
  | .sum vs _ :: l, b => congrArg (List.cons (vs.length + 3)) (cutOf_append l b)
  | .batch _ :: l, b => congrArg (List.cons 1) (cutOf_append l b)
  | .point _ :: l, b => congrArg (List.cons 1) (cutOf_append l b)

theorem cutOf_scalars (k : Nat) : ∀ n : Nat, cutOf (List.replicate n (.scalars k)) = []
  | 0 => rfl
  | n + 1 => cutOf_scalars k n

theorem cutOf_units : ∀ us : List (Nat × Nat),
    cutOf (us.flatMap fun u => [.scalars 7, products u.1 u.2]) = us.map fun u => u.1 + 3
  | [] => rfl
  | u :: us => by
    rw [List.flatMap_cons, cutOf_append, cutOf_units us, List.map_cons]
    show [(List.replicate u.1 (Var.plain 4)).length + 3] ++ _ = _
    rw [List.length_replicate]
    rfl

/-- **The parts' numbers of rounds**: a softmax-table unit's sumcheck has its variables' number and
three more; then the eleven parts behind. No premise. -/
theorem cut_eq (x : OnBytes.Params.AttentionRounds) :
    cut x = x.score.map (fun u => u.1 + 3) ++ tailCut x := by
  unfold cut shapes
  rw [shapesOf_cut]
  show cutOf (List.replicate x.planeMessages (.scalars 3) ++
    x.score.flatMap (fun u => [.scalars 7, products u.1 u.2]) ++ _) = _
  rw [cutOf_append, cutOf_append, cutOf_scalars, cutOf_units, List.nil_append]
  congr 1
  simp only [cutOf, tailCut, products, List.length_replicate, List.length_map, List.length_append]

theorem cut_unit (x : OnBytes.Params.AttentionRounds) {i : Nat} {u : Nat × Nat}
    (h : x.score[i]? = some u) : (cut x)[i]? = some (u.1 + 3) := by
  have hi : i < x.score.length := (List.getElem?_eq_some_iff.1 h).1
  rw [cut_eq, List.getElem?_append_left (by rw [List.length_map]; exact hi), List.getElem?_map, h]
  rfl

theorem cut_at (x : OnBytes.Params.AttentionRounds) (j : Nat) :
    (cut x)[x.score.length + j]? = (tailCut x)[j]? := by
  rw [cut_eq, List.getElem?_append_right (by rw [List.length_map]; omega), List.length_map,
    Nat.add_sub_cancel_left]

/-- A part's first round stands behind the part in front of it. -/
theorem firstOf_next (x : OnBytes.Params.AttentionRounds) {p v : Nat} (h : (cut x)[p]? = some v) :
    firstOf x (p + 1) = firstOf x p + v := by
  unfold firstOf
  rw [List.take_add_one, List.foldl_append, h]
  rfl

theorem firstOf_step (x : OnBytes.Params.AttentionRounds) (p : Nat) :
    firstOf x p ≤ firstOf x (p + 1) := by
  cases h : (cut x)[p]? with
  | some v => rw [firstOf_next x h]; omega
  | none =>
    unfold firstOf
    rw [List.take_add_one, List.foldl_append, h]
    exact Nat.le_refl _

theorem firstOf_mono (x : OnBytes.Params.AttentionRounds) {p q : Nat} (h : p ≤ q) :
    firstOf x p ≤ firstOf x q := by
  induction q with
  | zero => rw [Nat.le_zero.1 h]
  | succ q ih =>
    rcases Nat.lt_or_ge p (q + 1) with h1 | h1
    · exact Nat.le_trans (ih (by omega)) (firstOf_step x q)
    · rw [show p = q + 1 by omega]

end HeardIs

open HeardIs

/-! ## 2 Challenges that hold what rounds drew -/

/-- **The challenges hold, round by round, the elements that the rounds drew.** More may follow
behind. Of a round's challenge the elements alone are compared: the verifier's decision is shown its
rounds without the sealed digest. -/
def Reads (c : Chal) (rs : List Fmt.RoundView) : Prop :=
  ∀ (i : Nat) (r : Fmt.RoundView), rs[i]? = some r → (c.own[i]?).map (·.elems) = some r.drawn.elems

/-- Two lists of challenges are one in the first n rounds. -/
def Agree (n : Nat) (c c' : Chal) : Prop := ∀ i, i < n → c.own[i]? = c'.own[i]?

/-- **The same challenges in all parts in front of part number q.** It is a definition. -/
structure SameTo (x : OnBytes.Params.AttentionRounds) (q : Nat) (a b : Heard) : Prop where
  nR : a.remainders.size = b.remainders.size
  nS : a.scores.size = b.scores.size
  scores : ∀ i, i < q → ∀ u v, a.scores[i]? = some u → b.scores[i]? = some v → chal u.2 = chal v.2
  division : iSE x < q → chal a.division = chal b.division
  gam : iGam x < q → a.gam = b.gam
  below : iVM x < q → chal a.below = chal b.below
  on : iVD x < q → chal a.on = chal b.on
  point : iZero x < q → a.point = b.point
  om : iM6 x < q → a.om = b.om
  atIndex : iSF x < q → chal a.atIndex = chal b.atIndex
  om' : iOm4 x < q → a.om' = b.om'
  key : iSD x < q → chal a.key = chal b.key
  om'' : iOm5 x < q → a.om'' = b.om''
  cells : iHB x < q → chal a.cells = chal b.cells

namespace HeardIs

section
variable (c : Chal) {rs : List Fmt.RoundView} (hc : Reads c rs)
include hc

theorem many_at {n : Nat} {r : Fmt.RoundView} (hr : rs[n]? = some r) :
    c.many n = (r.drawn.elems.map E.ofTriple).toArray := by
  unfold Chal.many
  rw [hc n r hr]
  simp only [Option.getD_some, List.map_toArray]

theorem one_at {n : Nat} {r : Fmt.RoundView} (hr : rs[n]? = some r) {g : E}
    (hg : r.drawn.elems.map E.ofTriple = [g]) : c.one n = g := by
  unfold Chal.one
  rw [many_at c hc hr, hg]
  rfl

end

/-! ## 3 The hearing's verbs, each at its place among the rounds -/

theorem drop_cons {α : Type} {l t : List α} {n : Nat} {a : α} (h : l.drop n = a :: t) :
    l[n]? = some a ∧ t = l.drop (n + 1) := by
  constructor
  · have h0 := congrArg (fun z => z[0]?) h
    simp only [List.getElem?_drop, Nat.add_zero, List.getElem?_cons_zero] at h0
    exact h0
  · have h1 := congrArg List.tail h
    rw [List.tail_drop, List.tail_cons] at h1
    exact h1.symm

theorem drop_add {α : Type} (l : List α) (a b : Nat) : (l.drop a).drop b = l.drop (a + b) := by
  apply List.ext_getElem?
  intro i
  simp only [List.getElem?_drop, Nat.add_assoc]

theorem take_pos {n j : Nat} {s s' : St} (h : take n s = some (j, s')) : s'.2.1 = s.2.1 := by
  obtain ⟨F, rs, lead⟩ := s
  obtain ⟨G, rs', lead'⟩ := s'
  exact (take_spec h).2.1

theorem takes_pos (n : Nat) : ∀ (k : Nat) (js : List Nat) (s s' : St), TakesRan n k js s s' →
    s'.2.1 = s.2.1 ∧ js.length = k
  | 0, [], s, s', h => ⟨by rw [show s' = s from h], rfl⟩
  | k + 1, _ :: js, _, s', ⟨s1, h1, h2⟩ =>
    ⟨(takes_pos n k js s1 s' h2).1.trans (take_pos h1),
      congrArg (· + 1) (takes_pos n k js s1 s' h2).2⟩
  | 0, _ :: _, _, _, h => h.elim
  | _ + 1, [], _, _, h => h.elim

/-- A variable's round drew just the challenge that was read of it. -/
theorem varsRead_at : ∀ {vs : List Var} {used : List Fmt.RoundView} {l : List (List E × E)},
    VarsRead vs used l → ∀ (i : Nat) (r : Fmt.RoundView), used[i]? = some r →
      ∃ y, l[i]? = some y ∧ r.drawn.elems.map E.ofTriple = [y.2]
  | [], [], [], _, _, _, h => by cases h
  | _ :: _, _ :: _, (s, g) :: _, h, 0, r, hr => by
    obtain rfl := Option.some.inj hr
    exact ⟨(s, g), rfl, h.1.2.2.2.symm⟩
  | _ :: _, _ :: _, (_, _) :: _, h, i + 1, r, hr => varsRead_at h.2 i r hr
  | [], [], _ :: _, h, _, _, _ => h.elim
  | [], _ :: _, _, h, _, _, _ => h.elim
  | _ :: _, [], _, h, _, _, _ => h.elim
  | _ :: _, _ :: _, [], h, _, _, _ => h.elim

/-- Where a masked sumcheck's hearing returns: as many challenges as variables, the further one
among them; number i is what round number i + 1 drew. -/
theorem hear_r {C : Aff} {lead : Nat} {vs : List Var} {e : Ends} {F G : Fork}
    {rs : List Fmt.RoundView} {hh : MaskedSum.Heard}
    (h : MaskedSum.hear C ⟨lead, vs, some e⟩ F rs = some (hh, G)) :
    hh.r.length = vs.length + 1 ∧ ∀ i, i < vs.length + 1 →
      ∃ r g, rs[i + 1]? = some r ∧ hh.r[i]? = some g ∧ r.drawn.elems.map E.ofTriple = [g] := by
  obtain ⟨_, T, R, _, hR, hEq, _⟩ := hear_spec h
  obtain ⟨r0, used, rv, front, hrs, _, _, hV, _⟩ := readAll_spec hR
  obtain ⟨l1, l2⟩ := VarsRead.length hV
  rw [List.length_append, List.length_singleton] at l1 l2
  have hr : hh.r = R.rounds.map (·.2) := by rw [hEq]
  refine ⟨by rw [hr, List.length_map, l2], fun i hi => ?_⟩
  obtain ⟨r, hu⟩ : ∃ r, used[i]? = some r := ⟨used[i]'(by omega), List.getElem?_eq_getElem _⟩
  obtain ⟨y, hy, hg⟩ := varsRead_at hV i r hu
  refine ⟨r, y.2, ?_, ?_, hg⟩
  · rw [hrs, List.getElem?_cons_succ, List.getElem?_append_left (by omega), hu]
  · rw [hr, List.getElem?_map, hy]
    rfl

section
variable (x : OnBytes.Params.AttentionRounds) (c : Chal) {rs : List Fmt.RoundView} (hc : Reads c rs)
include hc

/-- **A masked sumcheck that is part number p.** CONDITIONAL: the verb returns, from a state whose
rounds left are those from the part's first on. -/
theorem sum_part {p : Nat} {C : Aff} {vs : List Var} {e : Ends} {hh : MaskedSum.Heard} {s s' : St}
    (hcut : (cut x)[p]? = some (vs.length + 3)) (h : sum C (.sum vs e) s = some (hh, s'))
    (hs : s.2.1 = rs.drop (firstOf x p)) :
    s'.2.1 = rs.drop (firstOf x (p + 1)) ∧ chal hh = c.r x p := by
  obtain ⟨F, rs0, lead⟩ := s
  obtain ⟨G, rs', lead'⟩ := s'
  have hs' : rs0 = rs.drop (firstOf x p) := hs
  subst hs'
  obtain ⟨e1, _, G1, f, h1, _⟩ := sum_spec h
  refine ⟨?_, ?_⟩
  · show rs' = _
    rw [e1, drop_add, firstOf_next x hcut]
  · obtain ⟨hl, hr⟩ := hear_r h1
    unfold chal Chal.r
    rw [List.getD_eq_getElem?_getD, hcut, Option.getD_some, Nat.add_sub_cancel]
    apply Array.toList_inj.1
    rw [Array.toList_map, Array.toList_range]
    show hh.r.dropLast = _
    apply List.ext_getElem?
    intro i
    rw [List.getElem?_dropLast, hl, Nat.add_sub_cancel, List.getElem?_map]
    by_cases hi : i < vs.length
    · obtain ⟨r, g, a1, a2, a3⟩ := hr i (by omega)
      rw [if_pos hi, a2, List.getElem?_range hi, Option.map_some]
      rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop] at a1
      rw [one_at c hc (n := firstOf x p + 1 + i) (by rw [← a1]; congr 1; omega) a3]
    · rw [if_neg hi, List.getElem?_eq_none (by rw [List.length_range]; omega)]
      rfl

/-- **A batching element's round that is part number p.** -/
theorem batch_part {p rows : Nat} {w : Array E} {s s' : St} (hcut : (cut x)[p]? = some 1)
    (h : batch rows s = some (w, s')) (hs : s.2.1 = rs.drop (firstOf x p)) :
    s'.2.1 = rs.drop (firstOf x (p + 1)) ∧ w = powers (c.one (firstOf x p)) rows := by
  obtain ⟨F, rs0, lead⟩ := s
  obtain ⟨G, rs', lead'⟩ := s'
  have hs' : rs0 = rs.drop (firstOf x p) := hs
  subst hs'
  obtain ⟨_, _, r, y, h1, _, h2, h3⟩ := batch_spec h
  obtain ⟨a, b⟩ := drop_cons h1
  refine ⟨?_, ?_⟩
  · show rs' = _
    rw [b, firstOf_next x hcut]
  · unfold powers
    rw [h3, one_at c hc a h2]

/-- **The point's round, as part number p.** -/
theorem close_part {p n : Nat} {d : List E} {s s' : St} (hcut : (cut x)[p]? = some 1)
    (h : close n s = some (d, s')) (hs : s.2.1 = rs.drop (firstOf x p)) :
    s'.2.1 = rs.drop (firstOf x (p + 1)) ∧ d.toArray = c.many (firstOf x p) := by
  obtain ⟨F, rs0, lead⟩ := s
  obtain ⟨G, rs', lead'⟩ := s'
  have hs' : rs0 = rs.drop (firstOf x p) := hs
  subst hs'
  obtain ⟨_, _, r, h1, _, _, h2⟩ := close_spec h
  obtain ⟨a, b⟩ := drop_cons h1
  refine ⟨?_, ?_⟩
  · show rs' = _
    rw [b, firstOf_next x hcut]
  · rw [h2, many_at c hc a]

/-- The softmax-table units' sumchecks, from unit number i on. -/
theorem units_part : ∀ (us : List (Nat × Nat)) (os : List (Nat × MaskedSum.Heard)) (i : Nat)
    (s s' : St), x.score.drop i = us → s.2.1 = rs.drop (firstOf x i) → UnitsRan us os s s' →
    s'.2.1 = rs.drop (firstOf x (i + us.length)) ∧ os.length = us.length ∧
      ∀ j o, os[j]? = some o → chal o.2 = c.r x (i + j)
  | [], [], i, s, s', _, hs, h =>
    ⟨by rw [show s' = s from h]; exact hs, rfl, fun j o hj => by cases hj⟩
  | u :: us, o :: os, i, s, s', hu, hs, ⟨s1, ⟨s0, h1, h2⟩, h3⟩ => by
    obtain ⟨hi, hu'⟩ := drop_cons hu
    have hcut : (cut x)[i]? = some ((List.replicate u.1 (Var.plain 4)).length + 3) := by
      rw [List.length_replicate]
      exact cut_unit x hi
    obtain ⟨p1, p2⟩ := sum_part x c hc hcut h2 ((take_pos h1).trans hs)
    obtain ⟨q1, q2, q3⟩ := units_part us os (i + 1) s1 s' hu'.symm p1 h3
    refine ⟨?_, congrArg (· + 1) q2, ?_⟩
    · rw [q1, List.length_cons, show i + 1 + us.length = i + (us.length + 1) by omega]
    · intro j o' hj
      cases j with
      | zero =>
        obtain rfl := Option.some.inj hj
        exact p2
      | succ j =>
        rw [q3 j o' hj, show i + 1 + j = i + (j + 1) by omega]
  | [], _ :: _, _, _, _, _, _, h => h.elim
  | _ :: _, [], _, _, _, _, _, h => h.elim

end

end HeardIs

/-! ## 4 The hearing's challenges are the prover's -/

/-- **Where the verifier's hearing returns at rounds whose challenges the prover's side holds, the
two hold the same challenges, in all parts**, as `SameTo` compares them: not eps, not the further
variable's challenge. CONDITIONAL: hh: the hearing's return, from any ledger and with no scalar
waiting; hc: the challenges c hold what the rounds drew. -/
theorem heard_is_ours (P : Pub5) (c : Chal) {F : Fork} {rs : List Fmt.RoundView} {hd : Heard} {s' : St}
    (hh : hear P.x (F, rs, 0) = some (hd, s')) (hc : Reads c rs) (q : Nat) :
    SameTo P.x q hd (heardAt P c fun _ => none) := by
  obtain ⟨sa, sb, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, pt, ra, rb, t1,
    t2, t3, u4, b5, t6, u7, u8, c9, ept, t10, b11, u12, b13, u14, b15, u16⟩ := (hear_ran hh).ran
  have L : ∀ j v, (tailCut P.x)[j]? = some v → (cut P.x)[P.x.score.length + j]? = some v :=
    fun j v h => (cut_at P.x j).trans h
  have R4 : ∀ n : Nat, (List.replicate n (Var.plain 4)).length + 3 = n + 3 := fun n => by
    rw [List.length_replicate]
  obtain ⟨pa, na⟩ := takes_pos 3 _ _ _ _ ra
  obtain ⟨pb, nb, cb⟩ := units_part P.x c hc P.x.score hd.scores.toList 0 sa sb rfl
    (by rw [pa]; rfl) rb
  rw [Nat.zero_add] at pb
  obtain ⟨p4, e4⟩ := sum_part P.x c hc (p := P.x.score.length) (by rw [R4]; exact L 0 _ rfl) u4
    ((take_pos t3).trans ((take_pos t2).trans ((take_pos t1).trans pb)))
  obtain ⟨p5, e5⟩ := batch_part P.x c hc (p := P.x.score.length + 1) (L 1 _ rfl) b5 p4
  obtain ⟨p7, e7⟩ := sum_part P.x c hc (p := P.x.score.length + 2) (by rw [R4]; exact L 2 _ rfl) u7
    ((take_pos t6).trans p5)
  obtain ⟨p8, e8⟩ := sum_part P.x c hc (p := P.x.score.length + 3) (by rw [R4]; exact L 3 _ rfl) u8
    p7
  obtain ⟨p9, e9⟩ := close_part P.x c hc (p := P.x.score.length + 4) (L 4 _ rfl) c9 p8
  obtain ⟨p11, e11⟩ := batch_part P.x c hc (p := P.x.score.length + 5) (L 5 _ rfl) b11
    ((take_pos t10).trans p9)
  obtain ⟨p12, e12⟩ := sum_part P.x c hc (p := P.x.score.length + 6)
    (by rw [R4]; exact L 6 _ rfl) u12 p11
  obtain ⟨p13, e13⟩ := batch_part P.x c hc (p := P.x.score.length + 7) (L 7 _ rfl) b13 p12
  obtain ⟨p14, e14⟩ := sum_part P.x c hc (p := P.x.score.length + 8)
    (by
      simp only [List.length_map, List.length_append, List.length_replicate]
      exact L 8 _ rfl) u14 p13
  obtain ⟨p15, e15⟩ := batch_part P.x c hc (p := P.x.score.length + 9) (L 9 _ rfl) b15 p14
  obtain ⟨_, e16⟩ := sum_part P.x c hc (p := P.x.score.length + 10)
    (by rw [R4]; exact L 10 _ rfl) u16 p15
  exact
    { nR := by
        show hd.remainders.size = (Array.replicate P.x.planeMessages 0).size
        rw [Array.size_replicate, ← na, Array.length_toList]
      nS := by
        show hd.scores.size = ((Array.range P.x.score.length).map _).size
        rw [Array.size_map, Array.size_range, ← nb, Array.length_toList]
      scores := fun i _ u v hu hv => by
        have h1 := cb i u (by rw [Array.getElem?_toList]; exact hu)
        rw [Nat.zero_add] at h1
        have hv' : ((Array.range P.x.score.length).map fun p =>
            ((0 : Nat), sumAt (c.r P.x p)))[i]? = some v := hv
        rw [Array.getElem?_map, Array.getElem?_range] at hv'
        by_cases hi : i < P.x.score.length
        · rw [if_pos hi] at hv'
          obtain rfl := Option.some.inj hv'
          rw [h1]
          exact (chal_sumAt _).symm
        · rw [if_neg hi] at hv'
          cases hv'
      division := fun _ => e4.trans (chal_sumAt _).symm
      gam := fun _ => e5
      below := fun _ => e7.trans (chal_sumAt _).symm
      on := fun _ => e8.trans (chal_sumAt _).symm
      point := fun _ => ept.trans e9
      om := fun _ => e11
      atIndex := fun _ => e12.trans (chal_sumAt _).symm
      om' := fun _ => e13
      key := fun _ => e14.trans (chal_sumAt _).symm
      om'' := fun _ => e15
      cells := fun _ => e16.trans (chal_sumAt _).symm }

/-! ## 5 Challenges that are one in the first rounds -/

theorem many_agree {n : Nat} {c c' : Chal} (h : Agree n c c') {i : Nat} (hi : i < n) :
    c.many i = c'.many i := by
  unfold Chal.many
  rw [h i hi]

theorem one_agree {n : Nat} {c c' : Chal} (h : Agree n c c') {i : Nat} (hi : i < n) :
    c.one i = c'.one i := by
  unfold Chal.one
  rw [many_agree h hi]

/-- The challenges of the variables' rounds of part p, where the part ends within the first n
rounds. -/
theorem r_agree (x : OnBytes.Params.AttentionRounds) {n : Nat} {c c' : Chal} (h : Agree n c c')
    {p : Nat} (hp : firstOf x (p + 1) ≤ n) : c.r x p = c'.r x p := by
  unfold Chal.r
  apply Array.toList_inj.1
  rw [Array.toList_map, Array.toList_map, Array.toList_range]
  refine List.map_congr_left fun l hl => one_agree h ?_
  have hl' := List.mem_range.1 hl
  rw [List.getD_eq_getElem?_getD] at hl'
  cases hc : (cut x)[p]? with
  | none =>
    rw [hc] at hl'
    exact absurd hl' (by simp)
  | some v =>
    rw [hc, Option.getD_some] at hl'
    rw [firstOf_next x hc] at hp
    omega

/-- **Challenges that are one in the rounds of the parts in front of part q give the same
challenges in these parts.** CONDITIONAL: Agree. -/
theorem heardAt_agree (P : Pub5) {c c' : Chal} {q : Nat} (h : Agree (firstOf P.x q) c c') :
    SameTo P.x q (heardAt P c fun _ => none) (heardAt P c' fun _ => none) := by
  have R : ∀ p, p < q → c.r P.x p = c'.r P.x p := fun p hp =>
    r_agree P.x h (firstOf_mono P.x hp)
  have O : ∀ p v, (cut P.x)[p]? = some (v + 1) → p < q →
      c.one (firstOf P.x p) = c'.one (firstOf P.x p) := fun p v hv hp =>
    one_agree h (Nat.lt_of_lt_of_le (by rw [firstOf_next P.x hv]; omega)
      (firstOf_mono P.x (show p + 1 ≤ q from hp)))
  have L : ∀ j v, (tailCut P.x)[j]? = some v → (cut P.x)[P.x.score.length + j]? = some v :=
    fun j v h => (cut_at P.x j).trans h
  exact
    { nR := rfl
      nS := by
        show ((Array.range P.x.score.length).map _).size =
          ((Array.range P.x.score.length).map _).size
        rw [Array.size_map, Array.size_map]
      scores := fun i hi u v hu hv => by
        have hu' : ((Array.range P.x.score.length).map fun p =>
            ((0 : Nat), sumAt (c.r P.x p)))[i]? = some u := hu
        have hv' : ((Array.range P.x.score.length).map fun p =>
            ((0 : Nat), sumAt (c'.r P.x p)))[i]? = some v := hv
        rw [Array.getElem?_map, Array.getElem?_range] at hu' hv'
        by_cases hl : i < P.x.score.length
        · rw [if_pos hl] at hu' hv'
          obtain rfl := Option.some.inj hu'
          obtain rfl := Option.some.inj hv'
          show chal (sumAt (c.r P.x i)) = chal (sumAt (c'.r P.x i))
          rw [R i hi]
        · rw [if_neg hl] at hu'
          cases hu'
      division := fun hq => congrArg (fun r => chal (sumAt r)) (R _ hq)
      gam := fun hq => congrArg (fun y => powers y 2) (O _ 0 (L 1 _ rfl) hq)
      below := fun hq => congrArg (fun r => chal (sumAt r)) (R _ hq)
      on := fun hq => congrArg (fun r => chal (sumAt r)) (R _ hq)
      point := fun hq => many_agree h (Nat.lt_of_lt_of_le
        (by rw [firstOf_next P.x (p := iZero P.x) (v := 1) (L 4 _ rfl)]; omega)
        (firstOf_mono P.x (show iZero P.x + 1 ≤ q from hq)))
      om := fun hq => congrArg (fun y => powers y P.x.pairs) (O _ 0 (L 5 _ rfl) hq)
      atIndex := fun hq => congrArg (fun r => chal (sumAt r)) (R _ hq)
      om' := fun hq => congrArg (fun y => powers y P.x.pairs) (O _ 0 (L 7 _ rfl) hq)
      key := fun hq => congrArg (fun r => chal (sumAt r)) (R _ hq)
      om'' := fun hq => congrArg (fun y => powers y P.x.pairs) (O _ 0 (L 9 _ rfl) hq)
      cells := fun hq => congrArg (fun r => chal (sumAt r)) (R _ hq) }

end H2K5.Honest

#print axioms H2K5.Honest.HeardIs.shapesOf_cut
#print axioms H2K5.Honest.HeardIs.cutOf_append
#print axioms H2K5.Honest.HeardIs.cutOf_scalars
#print axioms H2K5.Honest.HeardIs.cutOf_units
#print axioms H2K5.Honest.HeardIs.cut_eq
#print axioms H2K5.Honest.HeardIs.cut_unit
#print axioms H2K5.Honest.HeardIs.cut_at
#print axioms H2K5.Honest.HeardIs.firstOf_next
#print axioms H2K5.Honest.HeardIs.firstOf_step
#print axioms H2K5.Honest.HeardIs.firstOf_mono
#print axioms H2K5.Honest.HeardIs.many_at
#print axioms H2K5.Honest.HeardIs.one_at
#print axioms H2K5.Honest.HeardIs.drop_cons
#print axioms H2K5.Honest.HeardIs.drop_add
#print axioms H2K5.Honest.HeardIs.take_pos
#print axioms H2K5.Honest.HeardIs.takes_pos
#print axioms H2K5.Honest.HeardIs.varsRead_at
#print axioms H2K5.Honest.HeardIs.hear_r
#print axioms H2K5.Honest.HeardIs.sum_part
#print axioms H2K5.Honest.HeardIs.batch_part
#print axioms H2K5.Honest.HeardIs.close_part
#print axioms H2K5.Honest.HeardIs.units_part
#print axioms H2K5.Honest.heard_is_ours
#print axioms H2K5.Honest.many_agree
#print axioms H2K5.Honest.one_agree
#print axioms H2K5.Honest.r_agree
#print axioms H2K5.Honest.heardAt_agree
