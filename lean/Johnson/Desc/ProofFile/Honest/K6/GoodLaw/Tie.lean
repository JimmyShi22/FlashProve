-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/GoodLaw/Tie.lean: the tests of Honest/K6/Good.lean on the draws of
the output head's own rounds, tied to what the verifier's text hears of these rounds. Definitions
with code, statements and proofs ON THE VERIFIER's TEXT; no prover is in this file.

  `drawsOk own`     every word of every drawn element is below the prime
  `goodAll p own`   `drawsOk`, `goodK6` and `goodK6Nz` together
  `read_draws`      what the part reads of a masked sumcheck's rounds, in the rounds' draws: the
                    stretch has as many rounds as variables and three more; the element at the
                    beginning is the first round's; every challenge that is kept is the draw of one
                    of the next rounds
  `goodK6_at`, `goodK6Nz_at`   the two tests, clause by clause
  `drawPoint_len`, `batch_len`, `level_len`   how many rounds each stretch has
  `good_heard`      **THE TIE: where the head's hearing returns on the rounds rs and `goodAll` says
                    yes of their draws: no challenge that the four sumchecks keep reads as 0, nor
                    the element at the beginning of the third and of the fourth**: every challenge
                    that is kept is the draw of ONE OF the rounds that Good.lean's clauses name by
                    number (which of them, and the converse, are not shown)
  `forms_live`      **so every slot of the window but the last is live** (`forms_live_heard`,
                    GoodLaw/Forms.lean)

Limits. The tie covers the four sumchecks' challenges and the elements at the beginnings of the
third and the fourth: not the
point on the positions, the two batching elements or the element of the round that ends the first
sumcheck. NOTHING IS TIED OF `linkedK6`. The premises: the ledger in front is well laid; the hearing
returns and uses the rounds up; the lookup's point on the positions has lt coordinates; for
`forms_live` also: the reads' entries name no slot. Two more, headLt p = lt and headLPd p = lPd, say
that
the public numbers p are those of the letters; GoodLaw/Runs.lean pays them at the verifier's own
letters. The ground of GoodLaw/Coef.lean is this file's ground too.
Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.K6.Good
import Johnson.Desc.ProofFile.Honest.K6.GoodLaw.Forms

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace ProofFile.Honest.K6.GoodLaw

section
open OnBytes (E zeroE okE isZeroE)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head.Law (rd callOf)
open VerifiableInference.Desc.Part.MaskedSum (Var Sent VarsRead readAll Read)

/-- Every word of every drawn element is below the prime. -/
def drawsOk (own : List Fmt.Drawn) : Bool := own.all fun d => (elemsOf d).all okE

/-- The three tests on a list of challenges. -/
def goodAll (p : Head.Par) (own : List Fmt.Drawn) : Bool :=
  drawsOk own && goodK6 p own && goodK6Nz p own

/-! ## The first element of a round's draw -/

theorem elemOf_cons_succ (d : Fmt.Drawn) (l : List Fmt.Drawn) (n : Nat) :
    elemOf (d :: l) (n + 1) = elemOf l n := by
  unfold elemOf
  simp

theorem elemOf_append_right : ∀ (A B : List Fmt.Drawn) (k : Nat),
    elemOf (A ++ B) (A.length + k) = elemOf B k
  | [], B, k => by simp
  | a :: A, B, k => by
    rw [List.cons_append, List.length_cons, show A.length + 1 + k = (A.length + k) + 1 by omega,
      elemOf_cons_succ]
    exact elemOf_append_right A B k

theorem elemOf_append_left : ∀ (A B : List Fmt.Drawn) (k : Nat), k < A.length →
    elemOf (A ++ B) k = elemOf A k
  | [], _, k, h => by simp at h
  | a :: A, B, 0, _ => rfl
  | a :: A, B, k + 1, h => by
    rw [List.cons_append, elemOf_cons_succ, elemOf_cons_succ]
    exact elemOf_append_left A B k (by simpa using h)

theorem elemOf_ok (own : List Fmt.Drawn) (h : drawsOk own = true) (n : Nat) :
    okE (elemOf own n) = true := by
  unfold elemOf
  cases hd : own[n]? with
  | none => rfl
  | some d =>
    have hm : d ∈ own := List.mem_of_getElem? hd
    have h1 : (elemsOf d).all okE = true := (List.all_eq_true.1 h) d hm
    show okE (((elemsOf d).head?).getD zeroE) = true
    cases he : (elemsOf d).head? with
    | none => rfl
    | some x => exact (List.all_eq_true.1 h1) x (List.mem_of_mem_head? he)

/-- Words below the prime, not all 0: the reading is not 0. -/
theorem rd_ne (x : E) (h1 : okE x = true) (h2 : isZeroE x = false) : rd x ≠ 0 :=
  VerifiableInference.Desc.K9H.notZero_val x (by
    unfold VerifiableInference.Desc.K9H.notZero
    rw [h1, h2]
    rfl)

/-! ## One masked sumcheck's reading against its rounds' draws -/

theorem sent_one {r : Fmt.RoundView} {n : Nat} {s : List E} {g : E} (h : Sent r n 1 s [g])
    (l : List Fmt.Drawn) :
    elemOf (r.drawn :: l) 0 = g := by
  have e : [g] = r.drawn.elems.map E.ofTriple := h.2.2.2
  have e2 : (r.drawn.elems.map E.ofTriple).head? = some g := by
    rw [← e]
    rfl
  show ((r.drawn.elems.map E.ofTriple).head?).getD zeroE = g
  rw [e2]
  rfl

theorem varsRead_draws : ∀ (vs : List Var) (used : List Fmt.RoundView) (l : List (List E × E)),
    VarsRead vs used l → ∀ x ∈ l.map (·.2), ∃ k, k < used.length ∧ x = elemOf (used.map (·.drawn)) k
  | [], [], [], _, x, hx => by simp at hx
  | v :: vs, r :: rs, (s, g) :: l, h, x, hx => by
    rw [List.map_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨0, by simp, (sent_one h.1 _).symm⟩
    · obtain ⟨k, hk, e⟩ := varsRead_draws vs rs l h.2 x hx
      exact ⟨k + 1, by simpa using hk, by rw [List.map_cons, elemOf_cons_succ]; exact e⟩
  | [], [], _ :: _, h, _, _ => h.elim
  | [], _ :: _, _, h, _, _ => h.elim
  | _ :: _, [], _, h, _, _ => h.elim
  | _ :: _, _ :: _, [], h, _, _ => h.elim

/-- **What was read of a sumcheck's rounds, in the rounds' draws**: the stretch has z.size + 3
rounds; the element at the beginning is round 0's; every challenge that is kept is that of one of
the rounds 1 to z.size + 1. -/
theorem read_draws {lead : Nat} {z : Point} {e : Nat} {t : List Fmt.RoundView} {R : Read}
    (hR : readAll (callOf lead z e) t = some R) :
    t.length = z.size + 3 ∧ R.eps = elemOf (t.map (·.drawn)) 0 ∧
      ∀ x ∈ R.rounds.map (·.2), ∃ k, k ≤ z.size ∧ x = elemOf (t.map (·.drawn)) (1 + k) := by
  obtain ⟨r0, used, rv, front, ht, s0, _, hv, _⟩ :=
    VerifiableInference.Desc.Part.MaskedSum.readAll_spec
      (show readAll ⟨lead, z.toList.map (Var.point · 3), some ⟨2, e⟩⟩ t = some R from hR)
  have hl : used.length = z.size + 1 := by
    rw [hv.length.1]
    simp
  subst ht
  refine ⟨by simp [hl], ?_, fun x hx => ?_⟩
  · rw [List.map_cons]
    exact (sent_one s0 _).symm
  · obtain ⟨k, hk, ex⟩ := varsRead_draws _ _ _ hv x hx
    refine ⟨k, by omega, ?_⟩
    rw [List.map_cons, show 1 + k = k + 1 by omega, elemOf_cons_succ, List.map_append,
      elemOf_append_left _ _ k (by simpa using hk)]
    exact ex

end

section
open OnBytes (E isZeroE)
open OnBytes.Model (Fork)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head.Law (rd callOf heardRec bind_some pure_some
  need_some hide_some)
open VerifiableInference.Desc.Part.MaskedSum (readAll Read)

/-! ## The two Bools, unpacked -/

theorem all_zipIdx {α : Type} (ok : α → Bool) : ∀ (l : List α) (k : Nat),
    (l.zipIdx k).all (fun x => ok x.1) = l.all ok
  | [], _ => rfl
  | a :: l, k => by
    rw [List.zipIdx_cons, List.all_cons, List.all_cons, all_zipIdx ok l (k + 1)]

theorem clauses_all (what ask : String) (ok : E → Bool) (z : Point) :
    (headClausesOn what ask ok z).all (·.2) = z.toList.all ok := by
  unfold headClausesOn
  rw [List.all_map]
  exact all_zipIdx ok z.toList 0

theorem sumR_all (p : Head.Par) (i n : Nat) (own : List Fmt.Drawn)
    (h : (headSumR p i n own).toList.all (!isZeroE ·) = true) (j : Nat) (hj : j < n) :
    isZeroE (elemOf own (headInFront p i + 1 + j)) = false := by
  have hm : elemOf own (headInFront p i + 1 + j) ∈ (headSumR p i n own).toList := by
    unfold headSumR
    simp only [List.mem_map, List.mem_range]
    exact ⟨j, hj, rfl⟩
  have := (List.all_eq_true.1 h) _ hm
  simpa using this

/-- `goodK6`, clause by clause. -/
theorem goodK6_at (p : Head.Par) (own : List Fmt.Drawn) (h : goodK6 p own = true) :
    (∀ j, j < headLPd p + headLt p → isZeroE (elemOf own (headInFront p 2 + 1 + j)) = false) ∧
    (∀ j, j < headLt p → isZeroE (elemOf own (headInFront p 5 + 1 + j)) = false) ∧
    (∀ j, j < headLt p → isZeroE (elemOf own (headInFront p 6 + 1 + j)) = false) ∧
    (∀ j, j < headLPd p + headLt p → isZeroE (elemOf own (headInFront p 7 + 1 + j)) = false) ∧
    isZeroE (elemOf own (headInFront p 6)) = false ∧
    isZeroE (elemOf own (headInFront p 7)) = false := by
  unfold goodK6 goodK6Clauses at h
  simp only [List.all_append, Bool.and_eq_true, clauses_all, List.all_cons, List.all_nil,
    Bool.and_true] at h
  obtain ⟨⟨⟨⟨a2, a5⟩, a6⟩, a7⟩, e6, e7⟩ := h
  exact ⟨sumR_all p 2 _ own a2, sumR_all p 5 _ own a5, sumR_all p 6 _ own a6,
    sumR_all p 7 _ own a7, by simpa using e6, by simpa using e7⟩

/-- `goodK6Nz`, clause by clause. -/
theorem goodK6Nz_at (p : Head.Par) (own : List Fmt.Drawn) (h : goodK6Nz p own = true) :
    isZeroE (elemOf own (headInFront p 2 + 1 + (headLPd p + headLt p))) = false ∧
    isZeroE (elemOf own (headInFront p 5 + 1 + headLt p)) = false ∧
    isZeroE (elemOf own (headInFront p 6 + 1 + headLt p)) = false ∧
    isZeroE (elemOf own (headInFront p 7 + 1 + (headLPd p + headLt p))) = false := by
  unfold goodK6Nz goodK6NzClauses at h
  simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨b2, b5, b6, b7⟩ := h
  exact ⟨by simpa using b2, by simpa using b5, by simpa using b6, by simpa using b7⟩

theorem inFront (p : Head.Par) :
    headInFront p 2 = 2 ∧ headInFront p 5 = headLPd p + headLt p + 7 ∧
    headInFront p 6 = headLPd p + 2 * headLt p + 10 ∧
    headInFront p 7 = headLPd p + 3 * headLt p + 13 := by
  have e2 : headInFront p 2 = 0 + 1 + 1 := rfl
  have e5 : headInFront p 5 = 0 + 1 + 1 + (headLPd p + headLt p + 3) + 1 + 1 := rfl
  have e6 : headInFront p 6 = 0 + 1 + 1 + (headLPd p + headLt p + 3) + 1 + 1 + (headLt p + 3) := rfl
  have e7 : headInFront p 7 =
      0 + 1 + 1 + (headLPd p + headLt p + 3) + 1 + 1 + (headLt p + 3) + (headLt p + 3) := rfl
  exact ⟨by omega, by omega, by omega, by omega⟩

/-! ## How many rounds each stretch has -/

theorem round_cons {n k : Nat} {F G : Fork} {rs left : List Fmt.RoundView} {x : List E × List E}
    (h : Hear.round n k F rs = some (x, G, left)) : rs.length = left.length + 1 := by
  unfold Hear.round at h
  cases rs with
  | nil => cases h
  | cons r l =>
    dsimp only at h
    cases hr : VerifiableInference.Desc.Part.MaskedSum.roundOf n k r with
    | none => rw [hr] at h; cases h
    | some y =>
      rw [hr] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2.2]
      rfl

theorem drawPoint_len {n : Nat} {F G : Fork} {p : List Fmt.RoundView} {z : Point}
    (h : drawPoint n F p = some (z, G, [])) : p.length = 1 := by
  unfold drawPoint at h
  obtain ⟨x, Fx, lx, a, b⟩ := bind_some h
  obtain ⟨_, _, e⟩ := pure_some b
  rw [round_cons a, e]
  rfl

theorem batch_len {n rows : Nat} {F G : Fork} {p : List Fmt.RoundView} {x : Array Hid × E}
    (h : sendThenBatch n rows F p = some (x, G, [])) : p.length = 1 := by
  unfold sendThenBatch at h
  obtain ⟨vg, F1, l1, h1, k1⟩ := bind_some h
  obtain ⟨v, gs⟩ := vg
  dsimp only at k1
  obtain ⟨A', F2, l2, h2, k2⟩ := bind_some k1
  obtain ⟨g', F3, l3, h3, k3⟩ := bind_some k2
  obtain ⟨_, _, e3⟩ := need_some h3
  obtain ⟨_, _, e4⟩ := pure_some k3
  have e2 := (hide_some h2).1
  rw [round_cons h1, e2, e3, e4]
  rfl

theorem level_len {z : Point} {start : Form} {F G : Fork} {t : List Fmt.RoundView} {S : Sum}
    (h : level z start F t = some (S, G, [])) : t.length = z.size + 4 := by
  unfold level at h
  obtain ⟨cs, G1, l1, h1, k1⟩ := bind_some h
  obtain ⟨c, s⟩ := cs
  dsimp only at k1
  obtain ⟨ag, G2, l2, h2, k2⟩ := bind_some k1
  obtain ⟨a, g⟩ := ag
  dsimp only at k2
  obtain ⟨dn, G3, l3, h3, k3⟩ := bind_some k2
  obtain ⟨_, _, e3⟩ := need_some h3
  obtain ⟨_, _, e4⟩ := pure_some k3
  obtain ⟨_, e1, e0⟩ := Head.Law.Came.heardBy_cut h1
  have hl := round_cons h2
  rw [e3, e4, e1, List.length_drop] at hl
  simp only [List.length_nil] at hl
  omega

theorem elemOf_mid (A t B : List Fmt.RoundView) (k : Nat) (hk : k < t.length) :
    elemOf ((A ++ (t ++ B)).map (·.drawn)) (A.length + k) = elemOf (t.map (·.drawn)) k := by
  rw [List.map_append, List.map_append]
  have e : A.length = (A.map (·.drawn)).length := by simp
  rw [e, elemOf_append_right, elemOf_append_left _ _ k (by simpa using hk)]

/-- One sumcheck: where its stretch t lies in the rounds behind a rounds, and the draws at the
places a + 1 .. a + 1 + z.size are not 0: no challenge that it keeps reads as 0. -/
theorem sum_good {S : Sum} {C : Form} {T : E} {R : Read} {lead : Nat} {z : Point} {e first : Nat}
    {t A B : List Fmt.RoundView} (hR : readAll (callOf lead z e) t = some R)
    (hpsc : S.psc = some (heardRec C T R (callOf lead z e) first))
    (ok : drawsOk ((A ++ (t ++ B)).map (·.drawn)) = true)
    (hz : ∀ k, k ≤ z.size →
      isZeroE (elemOf ((A ++ (t ++ B)).map (·.drawn)) (A.length + (1 + k))) = false) :
    SumGood S := by
  intro hd hhd x hx
  rw [hpsc] at hhd
  obtain rfl := Option.some.inj hhd
  obtain ⟨hl, _, hr⟩ := read_draws hR
  obtain ⟨k, hk, rfl⟩ := hr x hx
  rw [← elemOf_mid A t B (1 + k) (by omega)]
  exact rd_ne _ (elemOf_ok _ ok _) (hz k hk)

theorem sum_goodEps {S : Sum} {C : Form} {T : E} {R : Read} {lead : Nat} {z : Point} {e first : Nat}
    {t A B : List Fmt.RoundView} (hR : readAll (callOf lead z e) t = some R)
    (hpsc : S.psc = some (heardRec C T R (callOf lead z e) first))
    (ok : drawsOk ((A ++ (t ++ B)).map (·.drawn)) = true)
    (hz : isZeroE (elemOf ((A ++ (t ++ B)).map (·.drawn)) (A.length + 0)) = false) :
    SumGoodEps S := by
  intro hd hhd
  rw [hpsc] at hhd
  obtain rfl := Option.some.inj hhd
  obtain ⟨hl, he, _⟩ := read_draws hR
  show rd R.eps ≠ 0
  rw [he, ← elemOf_mid A t B 0 (by omega)]
  exact rd_ne _ (elemOf_ok _ ok _) hz

end

section
open OnBytes (E zeroE isZeroE)
open OnBytes.Model (Fork)
open VerifiableInference.Desc.Kinds
open VerifiableInference.Desc.Kinds.Head (asClaim HeardAll)
open VerifiableInference.Desc.Kinds.Head.Law (WellLaid callOf heardRec)
open VerifiableInference.Desc.Part.MaskedSum (readAll Read)
open VerifiableInference.Desc.K9H (liveAt)

theorem stretch_good {S : Sum} {C : Form} {T : E} {R : Read} {lead : Nat} {z : Point}
    {e first : Nat} {t A B : List Fmt.RoundView} (rs : List Fmt.RoundView) (D : rs = A ++ (t ++ B))
    (hR : readAll (callOf lead z e) t = some R)
    (hpsc : S.psc = some (heardRec C T R (callOf lead z e) first))
    (ok : drawsOk (rs.map (·.drawn)) = true) (off : Nat) (hoff : A.length = off)
    (hz : ∀ k, k ≤ z.size → isZeroE (elemOf (rs.map (·.drawn)) (off + 1 + k)) = false) :
    SumGood S := by
  subst D
  subst hoff
  exact sum_good hR hpsc ok fun k hk => by
    rw [show A.length + (1 + k) = A.length + 1 + k by omega]
    exact hz k hk

theorem stretch_goodEps {S : Sum} {C : Form} {T : E} {R : Read} {lead : Nat} {z : Point}
    {e first : Nat} {t A B : List Fmt.RoundView} (rs : List Fmt.RoundView) (D : rs = A ++ (t ++ B))
    (hR : readAll (callOf lead z e) t = some R)
    (hpsc : S.psc = some (heardRec C T R (callOf lead z e) first))
    (ok : drawsOk (rs.map (·.drawn)) = true) (off : Nat) (hoff : A.length = off)
    (hz : isZeroE (elemOf (rs.map (·.drawn)) off) = false) : SumGoodEps S := by
  subst D
  subst hoff
  exact sum_goodEps hR hpsc ok hz

theorem ar5 (a b : Nat) : 1 + (1 + (a + b + 4 + 1)) = a + b + 7 := by omega
theorem ar6 (a b : Nat) : 1 + (1 + (a + b + 4 + (1 + (b + 3)))) = a + 2 * b + 10 := by omega
theorem ar7 (a b : Nat) : 1 + (1 + (a + b + 4 + (1 + (b + 3 + (b + 3))))) = a + 3 * b + 13 := by
  omega

section Whole
variable [Head.Sizes] [Head.Policy] [Head.Request] [Head.Token] [FinalNorm.In] [Head.In]

/-- **THE TIE**: the three tests on the rounds' draws give what `forms_live_heard` asks of what was
heard. -/
theorem good_heard (p : Head.Par) (hlt : headLt p = Norm.lt) (hlPd : headLPd p = Norm.lPd)
    {F G : Fork} {rs : List Fmt.RoundView} {H : HeardAll} (hW : WellLaid F)
    (h : Head.hear F rs = some (H, G, [])) (hzt : (FinalNorm.zt).size = Norm.lt)
    (good : goodAll p (rs.map (·.drawn)) = true) :
    SumGood H.1.squares ∧ SumGood H.1.products ∧ SumGood H.2.1.normed ∧ SumGood H.2.2.logits ∧
      SumGoodEps H.2.1.normed ∧ SumGoodEps H.2.2.logits := by
  unfold goodAll at good
  simp only [Bool.and_eq_true] at good
  obtain ⟨⟨ok, gd⟩, nz⟩ := good
  obtain ⟨a2, a5, a6, a7, e6, e7⟩ := goodK6_at p _ gd
  obtain ⟨b2, b5, b6, b7⟩ := goodK6Nz_at p _ nz
  obtain ⟨f2, f5, f6, f7⟩ := inFront p
  obtain ⟨G1, G2, l1, hNorm, wG1, wG2, hsN, hsL, _⟩ := Head.Law.Came.hear_parts hW h
  obtain ⟨p0, p1, tS, p2, tP, Fa, Fb, Fc, hrs, h0, h1, _, h3, h4, h5, wa, wb, wc⟩ :=
    Head.Law.norm_parts hW hNorm
  have hpV : (H.1.pV).size = Norm.lt := Head.Law.drawPoint_size h0
  have hzS : (Head.Law.zS H.1.pV).size = Norm.lPd + Norm.lt := by
    simp [Head.Law.zS, halves, hpV]
  have hzL : (FinalNorm.zt ++ halves Norm.lPd).size = Norm.lt + Norm.lPd := by
    simp [halves, hzt]
  have n0 := drawPoint_len h0
  have n1 := batch_len h1
  have nS := level_len h3
  have n2 := batch_len h4
  obtain ⟨R4, T4, r4, _, q4, _⟩ := Head.Law.level_ends wa h3 (fun _ => zeroE)
  obtain ⟨c6, R6, T6, _, r6, _, _, q6, _⟩ := Head.Law.sumcheck_ends wc h5 (fun _ => zeroE)
  obtain ⟨c7, R7, T7, _, r7, _, _, q7, _⟩ := Head.Law.sumcheck_ends wG1 hsN (fun _ => zeroE)
  obtain ⟨c8, R8, T8, _, r8, _, _, q8, _⟩ := Head.Law.sumcheck_ends wG2 hsL (fun _ => zeroE)
  have nP := (read_draws r6).1
  have nN := (read_draws r7).1
  have D4 : rs = (p0 ++ p1) ++ (tS.take ((Head.Law.zS H.1.pV).size + 3) ++
      (tS.drop ((Head.Law.zS H.1.pV).size + 3) ++ (p2 ++ (tP ++ l1)))) := by
    rw [← List.append_assoc (tS.take _), List.take_append_drop, hrs]
    simp only [List.append_assoc]
  have D5 : rs = (p0 ++ (p1 ++ (tS ++ p2))) ++ (tP ++ l1) := by
    rw [hrs]
    simp only [List.append_assoc]
  have D6 : rs = (p0 ++ (p1 ++ (tS ++ (p2 ++ tP)))) ++
      (l1.take ((FinalNorm.zt).size + 3) ++ l1.drop ((FinalNorm.zt).size + 3)) := by
    rw [List.take_append_drop, hrs]
    simp only [List.append_assoc]
  have D7 : rs = (p0 ++ (p1 ++ (tS ++ (p2 ++ (tP ++ l1.take ((FinalNorm.zt).size + 3)))))) ++
      ((l1.drop ((FinalNorm.zt).size + 3)).take ((FinalNorm.zt ++ halves Norm.lPd).size + 3) ++
        (l1.drop ((FinalNorm.zt).size + 3)).drop ((FinalNorm.zt ++ halves Norm.lPd).size + 3)) := by
    rw [List.take_append_drop]
    simp only [List.append_assoc]
    rw [List.take_append_drop, hrs]
  have L4 : (p0 ++ p1).length = headInFront p 2 := by
    simp only [List.length_append, n0, n1, f2]
  have L5 : (p0 ++ (p1 ++ (tS ++ p2))).length = headInFront p 5 := by
    simp only [List.length_append, n0, n1, nS, n2]
    rw [f5, hlPd, hlt, hzS]
    exact ar5 _ _
  have L6 : (p0 ++ (p1 ++ (tS ++ (p2 ++ tP)))).length = headInFront p 6 := by
    simp only [List.length_append, n0, n1, nS, n2, nP]
    rw [f6, hlPd, hlt, hzS, hpV]
    exact ar6 _ _
  have L7 : (p0 ++ (p1 ++ (tS ++ (p2 ++ (tP ++ l1.take ((FinalNorm.zt).size + 3)))))).length =
      headInFront p 7 := by
    simp only [List.length_append, n0, n1, nS, n2, nP, nN]
    rw [f7, hlPd, hlt, hzS, hpV, hzt]
    exact ar7 _ _
  refine ⟨stretch_good rs D4 r4 q4 ok _ L4 fun k hk => ?_,
    stretch_good rs D5 r6 q6 ok _ L5 fun k hk => ?_,
    stretch_good rs D6 r7 q7 ok _ L6 fun k hk => ?_,
    stretch_good rs D7 r8 q8 ok _ L7 fun k hk => ?_,
    stretch_goodEps rs D6 r7 q7 ok _ L6 e6, stretch_goodEps rs D7 r8 q8 ok _ L7 e7⟩
  · rcases Nat.lt_or_ge k (headLPd p + headLt p) with c | c
    · exact a2 k c
    · obtain rfl : k = headLPd p + headLt p :=
        Nat.le_antisymm (by rw [hlPd, hlt, ← hzS]; exact hk) c
      exact b2
  · rcases Nat.lt_or_ge k (headLt p) with c | c
    · exact a5 k c
    · obtain rfl : k = headLt p := Nat.le_antisymm (by rw [hlt, ← hpV]; exact hk) c
      exact b5
  · rcases Nat.lt_or_ge k (headLt p) with c | c
    · exact a6 k c
    · obtain rfl : k = headLt p := Nat.le_antisymm (by rw [hlt, ← hzt]; exact hk) c
      exact b6
  · rcases Nat.lt_or_ge k (headLPd p + headLt p) with c | c
    · exact a7 k c
    · obtain rfl : k = headLPd p + headLt p :=
        Nat.le_antisymm (by rw [hlPd, hlt, Nat.add_comm, ← hzL]; exact hk) c
      exact b7

/-- **THE SAME ON THE DRAWS**: every slot of the window but the last is live where the three tests
on the rounds' draws say yes. -/
theorem forms_live [FinalNorm.Reads] [Head.Reads] (p : Head.Par) (hlt : headLt p = Norm.lt)
    (hlPd : headLPd p = Norm.lPd) {F G : Fork} {rs : List Fmt.RoundView} {H : HeardAll} (hW : WellLaid F)
    (h : Head.hear F rs = some (H, G, []))
    (hN : ∀ r i, (FinalNorm.entry r i).slots = #[]) (hR : ∀ r i, (Head.entry r i).slots = #[])
    (hzt : (FinalNorm.zt).size = Norm.lt) (good : goodAll p (rs.map (·.drawn)) = true) :
    letI : Norm.Heard := H.1
    letI : FinalNorm.Heard := H.2.1
    letI : Head.Heard := H.2.2
    (∀ j, F.next ≤ j → j < F.next + (35 + 6 * headLt p + 2 * headLPd p) →
      liveAt (FinalNorm.forms.map asClaim) j = true) ∧
    (∀ j, F.next + (35 + 6 * headLt p + 2 * headLPd p) ≤ j → j + 1 < G.next →
      liveAt (Head.logitForms.map asClaim) j = true) := by
  obtain ⟨g1, g2, g3, g4, e3, e4⟩ := good_heard p hlt hlPd hW h hzt good
  rw [hlt, hlPd]
  exact forms_live_heard hW h hN hR hzt g1 g2 g3 g4 e3 e4

end Whole

end

#print axioms elemOf_cons_succ
#print axioms elemOf_append_right
#print axioms elemOf_append_left
#print axioms elemOf_ok
#print axioms rd_ne
#print axioms sent_one
#print axioms varsRead_draws
#print axioms read_draws
#print axioms all_zipIdx
#print axioms clauses_all
#print axioms sumR_all
#print axioms goodK6_at
#print axioms goodK6Nz_at
#print axioms inFront
#print axioms round_cons
#print axioms drawPoint_len
#print axioms batch_len
#print axioms level_len
#print axioms elemOf_mid
#print axioms sum_good
#print axioms sum_goodEps
#print axioms stretch_good
#print axioms stretch_goodEps
#print axioms ar5
#print axioms ar6
#print axioms ar7
#print axioms good_heard
#print axioms forms_live

end ProofFile.Honest.K6.GoodLaw
