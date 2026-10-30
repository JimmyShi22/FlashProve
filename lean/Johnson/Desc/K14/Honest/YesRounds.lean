--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Honest/YesRounds.lean: the premises on a view's rounds under which the decide
functions of the eight sub-protocols of the linear claim's shared rounds return .ok
(Johnson/Desc/K14/Honest/YesChain.lean: Rounds8) follow from the format's own test on the rounds.

Before a sub-protocol's decide function is called, the format's step tests the form of its rounds
(roundsFit: Johnson/Desc/Block.lean): which items a round shows, how many elements and locations
were sampled, and that the elements that the plan marks as never 0 are not 0 as machine words.

Main names:
  ofTriple_nz         three words that are not all 0 are not the element whose words are all 0
  cut_nz              the factors of the seeds that are cut off a list of sampled elements stand
                      just where the format's list of a round of seeds marks "never 0"
  seeds_nz            **no sampled seed of a sending has the factor 0 as machine words**
  fitB_of_rounds      **the counts of seeds, answers and pads fit**, where the sending passes its
                      test on the plan and every code's message length is a power of two
  scalar_of_rounds    the round of "SPLIT" holds one scalar
  rounds8_of_fits     **Rounds8**, from the test on the rounds of the five sub-protocols that have
                      rounds and are not "LOC", and the columns

What stays a premise here: each sampled location has its column, of as many words as the committed
table has rows. It follows from the format's own test on the columns: cols_of_step
(Johnson/Desc/K14/Honest/ChainSteps.lean).
What is not claimed. Nothing on the values shown. Nothing on soundness, on completeness or on
hiding.

-/
import Johnson.Desc.K14.Honest.YesChain
import Johnson.Desc.K14.Law.LocFits
import Johnson.Desc.K1.Law.When

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Honest
open OnBytes OnBytes.Params Desc.Plain
open VerifiableInference.Desc (Block roundsFit drawsMarkedNonzeroHaveNonzeroWords itemOf)
open VerifiableInference.Desc.K1 (cutSeeds seedsOf answersIn shapesOf fitB planOkOwn)
open Desc.K14.Law (parU parO)

/-- Three words that are not all 0 are not the element whose words are all 0. -/
theorem ofTriple_nz (t : Fmt.Ext) (h : t ≠ (0, 0, 0)) : isZeroE (E.ofTriple t) = false := by
  obtain ⟨a, b, c⟩ := t
  cases hz : isZeroE (E.ofTriple (a, b, c)) with
  | false => rfl
  | true =>
    exfalso
    have hz' : (a == 0 && b == 0 && c == 0) = true := hz
    simp only [Bool.and_eq_true, beq_iff_eq] at hz'
    exact h (by rw [hz'.1.1, hz'.1.2, hz'.2])

/-- The format's list of a round of n + 1 seeds: one seed's, then that of n seeds. -/
theorem dsSeeds_succ (n v : Nat) :
    Fmt.dsSeeds (n + 1) v = (List.replicate v Fmt.Draw.elem ++ [Fmt.Draw.elemNZ]) ++
      Fmt.dsSeeds n v := by
  unfold Fmt.dsSeeds
  rw [List.replicate_succ, List.flatten_cons]

/-- **The factors of the seeds that are cut off a list of sampled elements stand just where the
format's list marks "never 0".** -/
theorem cut_nz (v : Nat) : ∀ (n : Nat) (l : List Fmt.Ext), l.length = n * (v + 1) →
    (((Fmt.dsSeeds n v).zip l).all fun x => x.1 != .elemNZ || x.2 != (0, 0, 0)) = true →
    ∀ s ∈ cutSeeds v n (l.map E.ofTriple), isZeroE s.2 = false
  | 0, _, _, _ => by
    intro s hs
    cases hs
  | n + 1, l, hl, h => by
    have hlen : v + 1 ≤ l.length := by
      rw [hl, Nat.succ_mul]
      omega
    -- the list: one seed's stretch, then the rest
    obtain ⟨t, ht⟩ : ∃ t, l[v]? = some t := ⟨l[v], List.getElem?_eq_getElem (by omega)⟩
    have e1 : l = (l.take v ++ [t]) ++ l.drop (v + 1) := by
      have a := List.take_append_drop v l
      have b : l.drop v = t :: l.drop (v + 1) := by
        rw [List.drop_eq_getElem_cons (by omega)]
        congr 1
        have := List.getElem?_eq_getElem (l := l) (i := v) (by omega)
        rw [ht] at this
        exact (Option.some.inj this).symm
      rw [List.append_assoc, List.singleton_append, ← b]
      exact a.symm
    have hz : (Fmt.dsSeeds (n + 1) v).zip l =
        ((List.replicate v Fmt.Draw.elem ++ [Fmt.Draw.elemNZ]).zip (l.take v ++ [t])) ++
          (Fmt.dsSeeds n v).zip (l.drop (v + 1)) := by
      rw [dsSeeds_succ]
      conv_lhs => rw [e1]
      exact List.zip_append (by simp; omega)
    rw [hz, List.all_append, Bool.and_eq_true] at h
    have hz2 : (List.replicate v Fmt.Draw.elem ++ [Fmt.Draw.elemNZ]).zip (l.take v ++ [t]) =
        (List.replicate v Fmt.Draw.elem).zip (l.take v) ++ [(Fmt.Draw.elemNZ, t)] := by
      rw [List.zip_append (by simp; omega)]
      rfl
    have ht0 : t ≠ (0, 0, 0) := by
      have h1 := h.1
      rw [hz2, List.all_append, Bool.and_eq_true] at h1
      have h2 := h1.2
      simpa using h2
    intro s hs
    have hs' : s ∈ ((l.map E.ofTriple).take v, ((l.map E.ofTriple).drop v).headD zeroE) ::
        cutSeeds v n ((l.map E.ofTriple).drop (v + 1)) := hs
    rcases List.mem_cons.1 hs' with rfl | hs''
    · show isZeroE (((l.map E.ofTriple).drop v).headD zeroE) = false
      have e3 : ((l.map E.ofTriple).drop v).headD zeroE = E.ofTriple t := by
        rw [← List.map_drop, List.drop_eq_getElem_cons (by omega)]
        have := List.getElem?_eq_getElem (l := l) (i := v) (by omega)
        rw [ht] at this
        rw [← Option.some.inj this]
        rfl
      rw [e3]
      exact ofTriple_nz t ht0
    · rw [← List.map_drop] at hs''
      refine cut_nz v n (l.drop (v + 1)) ?_ h.2 s hs''
      rw [List.length_drop, hl, Nat.succ_mul]
      omega

/-- **No sampled seed of a sending has the factor 0 as machine words.** -/
theorem seeds_nz (Q : VerifiableInference.Desc.K1.Par) (r₁ r₂ : Fmt.RoundView)
    (h : roundsFit (VerifiableInference.Desc.K1.rounds Q) [r₁, r₂] = true) :
    ∀ s ∈ seedsOf Q r₁, isZeroE s.2 = false := by
  have hlen := (VerifiableInference.Desc.K1.fit_facts Q r₁ r₂ h).1
  have hnz : drawsMarkedNonzeroHaveNonzeroWords { entry := VerifiableInference.Desc.K1.seedEntry Q } r₁ = true := by
    simp only [VerifiableInference.Desc.K1.rounds, roundsFit, Bool.and_eq_true] at h
    exact h.1.2
  have hk : Fmt.kindOf (VerifiableInference.Desc.K1.seedEntry Q).name = some .seeds := by
    show Fmt.kindOf "SEND seed" = some .seeds
    decide
  unfold drawsMarkedNonzeroHaveNonzeroWords at hnz
  rw [hk, Option.any_some] at hnz
  by_cases h0 : Q.seeds = 0
  · intro s hs
    unfold seedsOf at hs
    rw [h0] at hs
    cases hs
  · have hpos : 0 < Q.seeds := Nat.pos_of_ne_zero h0
    have a1 : (VerifiableInference.Desc.K1.seedEntry Q).drawE -
        (VerifiableInference.Desc.K1.seedEntry Q).drawNZ = Q.seeds * Q.coordinates := by
      show Q.seeds * (Q.coordinates + 1) - Q.seeds = _
      rw [Nat.mul_succ, Nat.add_sub_cancel]
    have e : Fmt.dsElems (VerifiableInference.Desc.K1.seedEntry Q) .seeds =
        Fmt.dsSeeds Q.seeds Q.coordinates := by
      unfold Fmt.dsElems
      rw [if_pos rfl, a1]
      show Fmt.dsSeeds Q.seeds (Q.seeds * Q.coordinates / Q.seeds) ++
        List.replicate (Q.seeds * Q.coordinates % Q.seeds) Fmt.Draw.elem = _
      rw [Nat.mul_div_cancel_left _ hpos, Nat.mul_mod_right, List.replicate_zero, List.append_nil]
    rw [e] at hnz
    exact cut_nz Q.coordinates Q.seeds r₁.drawn.elems hlen hnz

/-- **The counts of seeds, answers and pads fit.** -/
theorem fitB_of_rounds (Q : VerifiableInference.Desc.K1.Par) (r₁ r₂ : Fmt.RoundView)
    (hplan : planOkOwn Q = true) (hlen : Q.codes.lengthsOk = true)
    (hfit : roundsFit (VerifiableInference.Desc.K1.rounds Q) [r₁, r₂] = true) :
    fitB Q.codes Q.seeds (shapesOf Q) (answersIn r₂) = true := by
  simp only [planOkOwn, VerifiableInference.Desc.K1.planOk, Bool.and_eq_true] at hplan
  obtain ⟨⟨⟨hsh, _⟩, _⟩, hpad⟩ := hplan
  refine VerifiableInference.Desc.K1.fitB_true _ _ _ _
    (fun s hs h0 => ⟨VerifiableInference.Desc.K1.le_seeds Q s hs, ?_⟩)
    (by rw [VerifiableInference.Desc.K1.answers_len Q r₁ r₂ hfit,
      VerifiableInference.Desc.K1.answers_sum])
  obtain ⟨n, hn, rfl⟩ := List.mem_map.1 hs
  refine VerifiableInference.Desc.K1.pad_isSome _ _ hlen
    (Array.all_eq_true_iff_forall_mem.1 hsh n (Array.mem_toList_iff.1 hn)) ?_
  refine List.all_eq_true.1 hpad n.shape ?_
  simp only [VerifiableInference.Desc.K1.Par.tuple, List.mem_filter]
  exact ⟨hs, by simpa using h0⟩

/-- A round that shows one item, an element, shows one scalar. -/
theorem one_scalar (vals : List Fmt.ItemValue) (h : vals.map itemOf = [.e]) : ∃ x, vals = [.e x] := by
  rcases vals with _ | ⟨g, _ | ⟨g', t⟩⟩
  · simp at h
  · cases g <;> simp [itemOf] at h
    exact ⟨_, rfl⟩
  · simp at h

/-- **The round of "SPLIT" holds one scalar.** -/
theorem scalar_of_rounds (P : P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (hS : P.S.sharedSplitNeeded = true)
    (r8 : Fmt.RoundView) (h : roundsFit b8.rounds [r8] = true) : ∃ x, r8.vals = [.e x] := by
  unfold blocks at hb
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq,
    List.cons.injEq, and_true] at hb
  obtain ⟨sentU, hU, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := hb
  have hr : (((entries P).drop 3).take (if P.S.sharedSplitNeeded then 1 else 0)).map
      (fun e => ({ entry := e } : Fmt.DeclaredRound)) =
      [{ entry := { name := "SPLIT", work := 0, msg := 24 } }] := by
    unfold entries rounds whys
    rw [if_pos hS, if_pos hS]
    rfl
  have h' : roundsFit ((((entries P).drop 3).take (if P.S.sharedSplitNeeded then 1 else 0)).map
      (fun e => ({ entry := e } : Fmt.DeclaredRound))) [r8] = true := h
  rw [hr] at h'
  simp only [roundsFit, Bool.and_eq_true, beq_iff_eq] at h'
  exact one_scalar r8.vals h'.1.1.1.1.1.1.1

/-- **Rounds8, from the format's test on the rounds, and the columns.** -/
theorem rounds8_of_fits (P : P14) (sentU : Array OracleNotice) (layO : TreeLay)
    (hP : PlanFacts P.par P.codes sentU layO) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (hBU : planOkOwn (parU P sentU) = true)
    (hBO : planOkOwn (parO P) = true)
    (r1 r2a r2b r4 r5a r5b r7 r8 : Fmt.RoundView) (cols : List (Nat × List UInt64))
    (f1 : roundsFit b1.rounds [r1] = true)
    (f2 : roundsFit (VerifiableInference.Desc.K1.rounds (parU P sentU)) [r2a, r2b] =
      true)
    (f5 : roundsFit (VerifiableInference.Desc.K1.rounds (parO P)) [r5a, r5b] = true)
    (f7 : roundsFit b7.rounds [r7] = true) (f8 : roundsFit b8.rounds [r8] = true)
    (hcols : ∀ x ∈ r4.drawn.poss, ∃ col,
      cols.lookup (x % 2 ^ P.par.S.fold.index.code.logN) = some col ∧
        col.length = P.par.S.fold.index.rows) :
    Rounds8 P.par (parU P sentU) (parO P) r1 r2a r2b r4 r5a r5b r7 r8 cols := by
  have hlen : P.codes.lengthsOk = true := hP.lengths
  obtain ⟨r, hr, a1, _⟩ := Law.point_fits P b1 b2 b3 b4 b5 b6 b7 b8 hb [r1] f1
  obtain rfl : r1 = r := by simpa using hr
  obtain ⟨r, hr, a7, _⟩ := Law.zeta_fits P b1 b2 b3 b4 b5 b6 b7 b8 hb [r7] f7
  obtain rfl : r7 = r := by simpa using hr
  exact ⟨by unfold drawn; rw [List.length_map]; exact a1, seeds_nz _ r2a r2b f2,
    fitB_of_rounds _ r2a r2b hBU hlen f2, hcols, seeds_nz _ r5a r5b f5,
    fitB_of_rounds _ r5a r5b hBO hlen f5, by unfold drawn; rw [List.length_map]; exact a7,
    scalar_of_rounds P b1 b2 b3 b4 b5 b6 b7 b8 hb hP.two r8 f8⟩

end Desc.K14.Honest

#print axioms Desc.K14.Honest.ofTriple_nz
#print axioms Desc.K14.Honest.dsSeeds_succ
#print axioms Desc.K14.Honest.cut_nz
#print axioms Desc.K14.Honest.seeds_nz
#print axioms Desc.K14.Honest.fitB_of_rounds
#print axioms Desc.K14.Honest.one_scalar
#print axioms Desc.K14.Honest.scalar_of_rounds
#print axioms Desc.K14.Honest.rounds8_of_fits
