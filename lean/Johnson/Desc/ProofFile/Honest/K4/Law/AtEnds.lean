-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/AtEnds.lean: WHERE THE SECOND TOKEN SUMCHECK's JOB AND THE
BATCHED SUMCHECK's JOB ARE MADE AND FIT THEIR CALLS, THEIR SUMMANDS ON GIVEN END VALUES ARE THERE AT
EVERY POINT AND AT ALL END VALUES (`Sides.summand`, Johnson/Desc/K4/Honest/Sides.lean;
`StackData.summandOn`, Johnson/Desc/K4/Honest/Stack.lean). Statements and proofs.

Limits. NO JOB IS SHOWN TO BE MADE ANYWHERE: each statement starts from a return. THAT THERE IS A
TOKEN (0 < T) IS A PREMISE for the second token sumcheck. Nothing on what a summand is worth. It
stands over the text of `Reads.has` as a test on names, lengths and public numbers (`wtsFit`,
Johnson/Desc/K4/Honest/Cells.lean). No property is claimed.

Why. A job's `atEnds` takes 0 where one of these two functions yields nothing, and the public test
on a job's shape (`k4JobFits`, Honest/K4/Part.lean) does not call `atEnds`. By these statements the
two functions yield something wherever the jobs' own clauses of the test hold.

  `sidesSkel_refl`, `sideKeys_refl`, `blkKeys_refl`   each relation holds of a thing and itself
     (`lookSkel_refl`: LookSkel.lean).
  `dataSkel_refl`   likewise, of what the batched sumcheck's job reads.
  `amapM_size`, `bind_isSome`, `bitsOf_size`   small laws.
  `summand_of_rows`, `jobTermsOn_summand`   from the tokens' rows; from the job.
  `summandOn_of_ends`, `jobStackOn_summandOn`   from the true end values; from the job.
  `stack_ends_len`   the batched sumcheck's job has as many end values at any two lists of as many
     challenges: so the number that `k4JobFits` counts at challenges 0 is the number at a run's.
  `sidesOf_pub`   what the shared data hold of the place's public data.
  `terms_atEnds`, `stack_atEnds`   **of a place, an input and sampled values.**
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SkelStack
import Johnson.Desc.First.K4.RunsLength

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (Forest.Heard eqTab)
open OnBytes.Model.Layer (SBlk)
open OnBytes.Flat (All2 OptRel)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Desc.First.K4.RtPub

/-! ## Each relation holds of a thing and itself -/

theorem sidesSkel_refl (S : Sides) : SidesSkel S S :=
  ⟨rfl, lookSkel_refl _, ⟨⟨rfl, rfl, rfl, rfl⟩, rfl, rfl, fun _ => rfl⟩, rfl, rfl, rfl, rfl,
    All2.refl (R := FormKeys) (fun _ => rfl) _⟩

theorem sideKeys_refl (A : OnBytes.Desc.First.K4.RtPub.Side) : SideKeys A A := by
  cases A
  · trivial
  · exact fun i yv => OptRel.refl (R := FormKeys) (fun _ => rfl) _

theorem blkKeys_refl (W : Prop) (b : SBlk) : BlkKeys W b b :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, sideKeys_refl _, sideKeys_refl _, fun _ => rfl,
    fun _ => rfl, fun _ => rfl⟩

/-- The relation holds of what the batched sumcheck's job reads and itself. -/
theorem dataSkel_refl (D : StackData) : DataSkel D D :=
  ⟨sidesSkel_refl _, fun _ => rfl, All2.refl (blkKeys_refl False) _, rfl, rfl⟩

/-! ## Small laws -/

theorem amapM_size {α β : Type} {f : α → Option β} {xs : Array α} {ys : Array β}
    (h : xs.mapM f = some ys) : ys.size = xs.size := by
  rw [Array.mapM_eq_mapM_toList] at h
  cases hl : xs.toList.mapM f with
  | none =>
    rw [hl] at h
    cases h
  | some zs =>
    rw [hl] at h
    obtain rfl : zs.toArray = ys := Option.some.inj h
    exact OnBytes.Desc.First.K4.mapM_length _ zs hl

theorem bind_isSome {α β : Type} {x : Option α} {f : α → Option β} {a : α} (hx : x = some a)
    (hf : (f a).isSome = true) : (x >>= f).isSome = true := by
  subst hx
  exact hf

theorem bitsOf_size (n x : Nat) : (bitsOf n x).size = n := by
  unfold bitsOf
  rw [Array.size_map, Array.size_range]

/-! ## The second token sumcheck -/

/-- **Where the tokens' rows are made and there is a token, the summand is there at every point of
lt coordinates and at all values of the shown factors.** -/
theorem summand_of_rows {S : Sides} {rows : Array (Array E × Array Trip)}
    (h : tokenRows S = some rows) (hT : 0 < S.v.y.T) (sh z : Array E)
    (hz : z.size = S.v.y.h.lt) : (S.summand sh z).isSome = true := by
  have hs : rows.size = S.v.y.T := by
    have e := amapM_size h
    rwa [Array.size_range] at e
  have hpos : 0 < rows.size := hs ▸ hT
  obtain ⟨t, ht⟩ := amapM_mem h _ (Array.getElem_mem_toList hpos)
  obtain ⟨R, hR, h1⟩ := Option.bind_eq_some_iff.mp ht
  obtain ⟨sh', _, h2⟩ := Option.bind_eq_some_iff.mp h1
  obtain ⟨tr, h3, _⟩ := Option.bind_eq_some_iff.mp h2
  have K := sidesSkel_refl S
  obtain ⟨R', e1, k1⟩ := OptRel.of_right
    (readsTok_has K (z := z) (z₀ := bitsOf S.v.y.h.lt t) (hz.trans (bitsOf_size _ _).symm)) hR
  obtain ⟨l, e2, _⟩ := OptRel.of_right
    (trips_rel K k1 (eqTab z) _
      (fun lm yv => (S.gatedUnder (eqTab z)).getD (S.routedAt lm yv) zeroE) _ sh sh') h3
  unfold Sides.summand
  refine bind_isSome e1 ?_
  dsimp only
  exact bind_isSome e2 rfl

theorem jobTermsOn_summand {S : Sides} {j : Job} (h : jobTermsOn S = some j) (hT : 0 < S.v.y.T)
    (sh z : Array E) (hz : z.size = S.v.y.h.lt) : (S.summand sh z).isSome = true := by
  unfold jobTermsOn at h
  obtain ⟨rows, hr, _⟩ := Option.bind_eq_some_iff.mp h
  exact summand_of_rows hr hT sh z hz

/-! ## The batched sumcheck -/

/-- **Where the true end values are made at one list of challenges, the summand is there at every
list of as many challenges and at all end values.** -/
theorem summandOn_of_ends {D : StackData} {rs₀ : Array E} {l : List E}
    (h : D.endsAt rs₀ = some l) (rs e : Array E) (hr : rs.size = rs₀.size) :
    (D.summandOn rs e).isSome = true := by
  unfold StackData.endsAt at h
  dsimp only at h
  obtain ⟨fin, hf, _⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨fin', e1, _⟩ := OptRel.of_right
    (stackEnd_keys (W := False) D.S.v.y D.S.Q.hp.lamS D.om (e.extract 1 (1 + D.nVirt))
      (e.extract (2 + D.nVirt) e.size) D.om (Array.replicate D.nVirt zeroE)
      (Array.replicate D.S.opens.size zeroE) (e.getD 0 zeroE) (e.getD (1 + D.nVirt) zeroE) zeroE
      zeroE (All2.refl (blkKeys_refl False) D.bl.toList) hr) hf
  unfold StackData.summandOn StackData.sidesOn
  rw [Option.isSome_map]
  exact bind_isSome e1 rfl

theorem jobStackOn_summandOn {D : StackData} {rs₀ : List E} (h : (jobStackOn D).ends rs₀ ≠ [])
    (rs e : Array E) (hr : rs.size = rs₀.length) : (D.summandOn rs e).isSome = true := by
  have h' : (D.endsAt rs₀.toArray.reverse).getD [] ≠ [] := h
  cases hE : D.endsAt rs₀.toArray.reverse with
  | none =>
    rw [hE] at h'
    exact absurd rfl h'
  | some l =>
    refine summandOn_of_ends hE rs e ?_
    rw [Array.size_reverse, List.size_toArray]
    exact hr

/-- **As many end values at any two lists of as many challenges.** -/
theorem stack_ends_len (D : StackData) {rs rs₀ : List E} (h : rs.length = rs₀.length) :
    ((jobStackOn D).ends rs).length = ((jobStackOn D).ends rs₀).length := by
  show ((D.endsAt rs.toArray.reverse).getD []).length =
    ((D.endsAt rs₀.toArray.reverse).getD []).length
  have r := endsAt_rel (dataSkel_refl D) (rs := rs.toArray.reverse) (rs₀ := rs₀.toArray.reverse)
    (by rw [Array.size_reverse, Array.size_reverse, List.size_toArray, List.size_toArray, h])
  revert r
  cases D.endsAt rs.toArray.reverse <;> cases D.endsAt rs₀.toArray.reverse <;> intro r
  · rfl
  · exact False.elim r
  · exact False.elim r
  · exact r

/-! ## Of a place, an input and sampled values -/

theorem sidesOf_pub {Q : K4Pub} {w : K4In} {p : Pts} {S : Sides} (h : Sides.of Q w p = some S) :
    S.Q = Q ∧ S.v.y = Q.P.y := by
  unfold Sides.of at h
  dsimp only at h
  obtain ⟨v, hv, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨TS, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨Z, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨cls, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨a, lfc⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨opens, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨⟨gl, gr⟩, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨ends, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain rfl := Option.some.inj h
  have r := envOf_rel Q (p := p) (p₀ := p) (lookSkel_refl _)
  rw [hv] at r
  exact ⟨rfl, r.2.1⟩

/-- **The second token sumcheck**: where its job is made, and there is a token. -/
theorem terms_atEnds {Q : K4Pub} {w : K4In} {p : Pts} (h : (jobTerms Q w p).isSome = true)
    (hT : 0 < Q.P.y.T) :
    ∃ S, Sides.of Q w p = some S ∧
      ∀ sh z : Array E, z.size = Q.P.y.h.lt → (S.summand sh z).isSome = true := by
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp h
  unfold jobTerms at hj
  obtain ⟨S, hS, hj⟩ := Option.bind_eq_some_iff.mp hj
  have e := (sidesOf_pub hS).2
  exact ⟨S, hS, fun sh z hz => jobTermsOn_summand hj (e ▸ hT) sh z (e ▸ hz)⟩

/-- **The batched sumcheck**: where its job is made and fits its call. -/
theorem stack_atEnds {Q : K4Pub} {w : K4In} {p : Pts} {sh : Array E}
    (h : (jobStack Q w p sh).any (k4JobFits ((k4Shapes Q).getD 3 ⟨0, [], none⟩)) = true) :
    ∃ D, stackData Q w p sh = some D ∧
      ∀ rs e : Array E, rs.size = Q.hp.lamS → (D.summandOn rs e).isSome = true := by
  unfold jobStack at h
  cases hD : stackData Q w p sh with
  | none =>
    rw [hD] at h
    cases h
  | some D =>
    rw [hD] at h
    have hf : k4JobFits (k4PlainShape Q.hp.lamS 2
        (2 + (1 + Q.P.y.LamM) + (Q.hp.NCL - if Q.g == 0 then 1 else 0))) (jobStackOn D) = true := h
    refine ⟨D, rfl, fun rs e hr => ?_⟩
    unfold k4JobFits k4PlainShape at hf
    simp only [Bool.and_eq_true, beq_iff_eq, List.length_replicate] at hf
    refine jobStackOn_summandOn (rs₀ := List.replicate Q.hp.lamS zeroE) (fun hn => ?_) rs e
      (by rw [List.length_replicate, hr])
    have hl := hf.2.2
    rw [hn] at hl
    simp only [List.length_nil] at hl
    omega

end ProofFile.Honest.K4




#print axioms ProofFile.Honest.K4.sidesSkel_refl
#print axioms ProofFile.Honest.K4.sideKeys_refl
#print axioms ProofFile.Honest.K4.blkKeys_refl
#print axioms ProofFile.Honest.K4.dataSkel_refl
#print axioms ProofFile.Honest.K4.amapM_size
#print axioms ProofFile.Honest.K4.bind_isSome
#print axioms ProofFile.Honest.K4.bitsOf_size
#print axioms ProofFile.Honest.K4.summand_of_rows
#print axioms ProofFile.Honest.K4.jobTermsOn_summand
#print axioms ProofFile.Honest.K4.summandOn_of_ends
#print axioms ProofFile.Honest.K4.jobStackOn_summandOn
#print axioms ProofFile.Honest.K4.stack_ends_len
#print axioms ProofFile.Honest.K4.sidesOf_pub
#print axioms ProofFile.Honest.K4.terms_atEnds
#print axioms ProofFile.Honest.K4.stack_atEnds
