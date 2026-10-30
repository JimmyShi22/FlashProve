-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Inner/Passes.lean: the proof of `HeadMergeInner`
(Honest/K11/Inner/Statement.lean), to the letter, FROM FOUR STATEMENTS OF THE LAW OF THE MASKED
SUMCHECK's HONEST PART FOR ALL CALLERS (Honest/SumLaw/Statement.lean), which stand here as premises:
`SumHeard`, `SumClaim`, `SumLeft`, `SumLast`. Of that folder's proved lemmas one small one is
called: `alone_drawn` (Honest/SumLaw/More.lean): the rounds bear the challenges that were handed in.

How. `SumHeard`: the part's text of the verifier's sumcheck hears the rounds. `SumClaim`: of it one
clause alone is spent: the challenges that were heard are those that were handed in.
`headMergeHears` (Honest/K11/Inner/Hears.lean): so the kind's own maker of the tape and its hearing
return, with the same ledger and the same letters. (1): the part's row returns at the ledger behind
(the library's `row_returns_later`), and is worth eps (S0 + kept - cf) by `SumLeft` at
`headMergeSumsTo` (Honest/K11/Inner/Chain.lean) with the library's `merge_start`; what is shown is
cf by `SumLast` and `headMergeSummand`; `flatRowLaid` and `flatRowTie`
(Johnson/Desc/Part/MaskedSumFlatProofs.lean) carry both over to the flat text's row. (2): the fold
returns (`gammaFold_returns`, Honest/K11/Inner/Helps.lean), and the library's `pending_gamma` reads
it.

Limits. Those of the statement. A THEOREM WITH FOUR PREMISES THAT ARE OTHERS' STATEMENTS: it says
nothing until these are theorems. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Inner.Hears
import Johnson.Desc.ProofFile.Honest.K11.Inner.Chain
import Johnson.Desc.ProofFile.Honest.K11.Inner.Helps
import Johnson.Desc.ProofFile.Honest.SumLaw.More

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes (E mulE zeroE oneE)
open OnBytes.Slice (GE)
open OnBytes.Model (Reading Aff World Fork Psc WsLay WsClaim WsForkOut wsClaimShape wsForkStart
  wsGammaAdd wsRowPart wsEpsT powers)
open OnBytes.PscRun (Sized Filled Later)
open OnBytes.Road (Wm UnitOK claimVal rowAt fmAt bitsOf gl_numerals)
open OnBytes.K.Kc (Fl Tape)
open VerifiableInference.Desc.First.MergeLaw (claimFits_eq)
open VerifiableInference.Desc.Part.MaskedSum (Var Heard hear row rowForm rowLaid scalars Sent
  VarsRead hear_spec readAll_spec LedgerReady ownSlots SameLetters flatRowTie flatRowLaid
  heard_lenK hear_keeps row_keeps row_write row_of_laid row_returns_later)
open Johnson.Desc.First.ForkMerge (mergeHear mergeTapeE mergeEntries claimFits)
open Johnson.Desc.First.ForkMerge.Honest (termsOf endAt summand_ends)
open ProofFile.Honest.SumLaw (alone SumCoins firstRun endRun frontOf drawsOk varsOf jobPoly SumsTo
  hidingCoin SumHeard SumClaim SumLeft SumLast)

/-- What lies under a slot that is filled is kept in every later ledger's world. -/
theorem slot_kept {F H : Fork} (hl : Later F H) (mask : Nat → GE) (ent : Nat → Nat → Nat → GE)
    (j : Nat) (hj : Filled F j) :
    (H.worldOf Reading.gl mask ent).slot j = (F.worldOf Reading.gl mask ent).slot j := by
  obtain ⟨_, a, b⟩ := hl.keep j hj
  show Reading.gl.val (H.vp.getD j zeroE) - Reading.gl.val (H.mf.getD j zeroE) * mask j =
    Reading.gl.val (F.vp.getD j zeroE) - Reading.gl.val (F.mf.getD j zeroE) * mask j
  rw [a, b]

/-- Writing the plan's number of claims keeps all that lies under slots. -/
theorem headMerge_later_plan (G : Fork) (n : Nat) : Later G { G with planClaimsF := n } :=
  ⟨Nat.le_refl _, rfl, id, fun _ h => ⟨h, rfl, rfl⟩⟩

theorem empty_aff_value (Wd : World GE) : ({} : Aff).value Reading.gl Wd = 0 := by
  show (0 : GE) + 0 + Reading.gl.val zeroE = 0
  rw [Reading.gl.zero]
  simp

theorem list_getD_zero_headD (l : List E) : l.getD 0 zeroE = l.headD zeroE := by
  cases l <;> rfl

theorem headMergeInner_of (hHeard : SumHeard) (hClaim : SumClaim) (hLeft : SumLeft)
    (hLast : SumLast) : HeadMergeInner := by
  intro n₁ n₂ lay c t seen ds rounds r₀ x work cl sv F W mask ent hv0 he0 hp0 ht0 hlastH hds hdp
    hal hcl h1 h2 h3 hq hW hL hfill hmask htrue
  have hk : (headMergeJob lay).callAt t.input (frontOf t seen) = headMergeShape lay.lk :=
    headMergeCall lay t.input (frontOf t seen)
  have hds' : drawsOk ((headMergeJob lay).callAt t.input (frontOf t seen)) ds = true := by
    rw [hk]
    exact hds
  -- the part's text hears the rounds
  obtain ⟨h, G, hh0⟩ := hHeard Unit HeadMergeAsk Unit n₁ n₂ (headMergeJob lay) c t seen ds rounds
    (wsForkStart sv (powers (E.ofTriple x) sv.size)) F
    (by rw [hk]; exact shapeOk_headMerge lay.lk) hds' hal (by rw [hk]; exact hL)
  have hh : hear (wsForkStart sv (powers (E.ofTriple x) sv.size)) (headMergeShape lay.lk) F rounds =
      some (h, G) := by
    rw [← hk]
    exact hh0
  have hdr : rounds.map (·.drawn) = ds :=
    SumLaw.alone_drawn (sumPart (V := Unit) n₁ n₂ (headMergeJob lay)) c t seen ds rounds hal
  have hrs : ∀ r ∈ rounds, r.drawn.poss = [] ∧ r.drawn.trits = [] := fun r hr =>
    hdp r.drawn (by rw [← hdr]; exact List.mem_map_of_mem hr)
  have h4 : ∀ q ∈ cl, q.ui < lay.U.size ∧ claimFits lay q = true := fun q hqm => by
    obtain ⟨un, hu, hs, _, _⟩ := hq q hqm
    refine ⟨?_, by rw [claimFits_eq, hs]; rfl⟩
    by_contra hn
    rw [Array.getElem?_eq_none (by omega)] at hu
    cases hu
  have hq3 : ∀ q ∈ cl, ∃ u, lay.U[q.ui]? = some u ∧ wsClaimShape lay q = .ok () ∧
      UnitOK lay.lk u := fun q hqm => by
    obtain ⟨un, a1, a2, a3, _⟩ := hq q hqm
    exact ⟨un, a1, a2, a3⟩
  -- so the kind's own text
  obtain ⟨tp, wo, htp, hmh, hSL, f1, f2, f3, f4, wsf, wrm, wbe, wsh, wre⟩ :=
    headMergeHears lay cl sv F G work r₀ rounds x h h1 h2 h3 h4 hL.1 hv0 he0 hp0 ht0 hrs hh
  obtain ⟨_, hr0, _⟩ := hClaim Unit HeadMergeAsk Unit n₁ n₂ (headMergeJob lay) c t seen ds rounds _
    F G h hds' hal hh0
  have hr : h.r = varsOf (headMergeShape lay.lk) ds := by
    rw [← hk]
    exact hr0
  -- what was read, written out
  obtain ⟨_, T, R, hT, hR, hhe, hG⟩ := hear_spec hh
  obtain ⟨r1, used, rv, front, ers, _, _, hvr, sV⟩ :=
    readAll_spec (lead := 0) (vs := List.replicate lay.lk (Var.plain 3)) (e := ⟨1, 1⟩) hR
  obtain ⟨u1, u2, l1, l2, _, el, hv1, hv2⟩ := VarsRead.split hvr
  obtain ⟨_, sY, beta, _, el2, _⟩ := VarsRead.one hv2
  subst el2
  obtain ⟨v, hv⟩ : ∃ v, R.values = [v] := List.length_eq_one_iff.1 sV.2.1
  have hlen : (l1.map (·.2)).length = lay.lk := by
    have a := (VarsRead.length hv1).2
    rw [List.length_replicate] at a
    rw [List.length_map, a]
  have hrl : h.r = l1.map (·.2) ++ [beta] := by
    rw [hhe]
    show R.rounds.map (·.2) = _
    rw [el, List.map_append]
    rfl
  have hrm : wo.rm.toList = l1.map (·.2) := by
    rw [wrm, hrl, List.take_left' hlen]
  have hrmA : wo.rm = (l1.map (·.2)).toArray := by
    rw [← hrm, Array.toArray_toList]
  have hbe : wo.beta = beta := by
    rw [wbe, hrl]
    simp
  obtain ⟨e1, e2, e3⟩ := heard_lenK hh
  have hall : (headMergeShape lay.lk).all =
      List.replicate lay.lk (Var.plain 3) ++ [Var.point zeroE (1 + 1)] := rfl
  have hown : ownSlots (headMergeShape lay.lk).all = 2 * lay.lk + 2 := by
    rw [hall, ownSlots_headMerge]
  -- the ledger behind the hearing
  have hS2 : Sized ({ F with next := F.next + ownSlots (headMergeShape lay.lk).all +
      R.values.length } : Fork) := hL.1
  obtain ⟨hsame, hSG, hrun, hout⟩ := OnBytes.PscRun.hideRun_ok _ G _ _ _ hS2 hG
  have hnext : G.next = F.next + 2 * lay.lk + 3 := by
    rw [hsame.next]
    show F.next + ownSlots (headMergeShape lay.lk).all + R.values.length = _
    rw [hown, hv]
    show F.next + (2 * lay.lk + 2) + 1 = _
    omega
  have hFG : Later F G := hear_keeps hh
  -- what is shown is the last message's scalar
  have hfv : wo.fvp = v := by
    have a := hrun 0 (by rw [hv]; simp)
    have b : G.shown h.sEnd = some (G.vp.getD h.sEnd zeroE) :=
      OnBytes.Desc.First.P1.shown_returns (by rw [hsame.ns, e2]; exact a.1)
        (by rw [e2]; exact a.2.2.1)
    rw [wsh] at b
    rw [Option.some.inj b, e2]
    have d := a.2.2.2.1
    rw [hv] at d
    exact d
  -- the session's letters
  have hx : E.ofTriple x = (drawnE (frontOf t seen).heard).getLastD zeroE :=
    (drawnE_last t.heard r₀.drawn x hlastH he0).symm
  have hends := summand_ends Reading.gl lay t.input.entry (E.ofTriple x) cl hq3
  have hterms : headMergeTerms lay t.input (frontOf t seen) =
      termsOf lay t.input.entry (E.ofTriple x) cl.toList := by
    unfold headMergeTerms
    rw [← hx, hcl]
    rfl
  have hsums := headMergeSumsTo GE Reading.gl lay t.input (frontOf t seen) cl (E.ofTriple x) beta
    (endRun c) (l1.map (·.2)) hcl hx hq3 hlen
  -- the last message
  obtain ⟨rl, s, hl1, hl2, _, hl4⟩ := hLast Unit HeadMergeAsk Unit n₁ n₂ (headMergeJob lay) c t seen
    ds rounds ⟨1, 1⟩ rfl hds' hal
  have hrl' : rl = rv := by
    have e : (r1 :: (used ++ [rv])).getLast? = some rv := by
      rw [← List.cons_append, List.getLast?_concat]
    rw [ers, e] at hl1
    exact (Option.some.inj hl1).symm
  have hs : s = [v] := by
    rw [hrl', sV.1, hv] at hl2
    exact (Option.some.inj hl2).symm
  have hval : Reading.gl.val wo.fvp =
      fmAt Reading.gl lay (fun r k => Reading.gl.val (t.input.entry r k))
          (cl.zip (powers (E.ofTriple x) cl.size)).toList (l1.map (·.2)).toArray +
        Reading.gl.val beta * Reading.gl.val ((endRun c).headD zeroE) := by
    have a := hl4 0 (by decide)
    rw [hk, ← hr, hrl, hs, list_getD_zero_headD (endRun c)] at a
    have b : ((headMergeJob lay).ends t.input (frontOf t seen)
        ((l1.map (·.2) ++ [beta]).take (headMergeJob lay).shape.vs.length)).getD 0 zeroE =
        endAt (termsOf lay t.input.entry (E.ofTriple x) cl.toList) (l1.map (·.2)) := by
      show endAt (headMergeTerms lay t.input (frontOf t seen))
        ((l1.map (·.2) ++ [beta]).take (List.replicate lay.lk (Var.plain 3)).length) = _
      rw [List.length_replicate, List.take_left' hlen, hterms]
    rw [b, hends.2 _ hlen] at a
    rw [hfv]
    have e : (l1.map (·.2) ++ [beta]).getLastD zeroE = beta := by simp
    rw [e] at a
    exact a
  refine ⟨tp, wo, G, htp, hmh, hnext, by rw [wrm, hr], by rw [wbe, hr], ?_, ?_⟩
  · -- (1)
    intro n
    have hSn : Sized ({ G with planClaimsF := n } : Fork) := hSG
    have hroom : F.next + ownSlots (headMergeShape lay.lk).all ≤
        ({ G with planClaimsF := n } : Fork).ns := by
      show _ ≤ G.ns
      rw [hsame.ns]
      have a := (hrun 0 (by rw [hv]; simp)).1
      exact Nat.le_of_lt a
    have hfree : ∀ j, F.next ≤ j → j < F.next + ownSlots (headMergeShape lay.lk).all →
        ¬ Filled ({ G with planClaimsF := n } : Fork) j := fun j a b hf =>
      hL.2.2.2 j a (by
        have := hown
        show j < F.next + ownSlots (headMergeShape lay.lk).all + _
        omega) ((hout j (Or.inl b)).2.2.1 hf)
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1
      (row_returns_later hh hSn hroom hfree wo.fvp {})
    have hrow : row h wo.fvp {} { G with planClaimsF := n } = some (rowForm h wo.fvp {}, y.2) :=
      row_of_laid wo.fvp {} (row_write (f := y.1) (G := y.2) hy)
    have hLat : Later F y.2 := (hFG.trans (headMerge_later_plan G n)).trans (row_keeps hrow)
    -- the claimed form's worth in the world behind
    have hslot : List.Forall₂ (fun s q => (y.2.worldOf Reading.gl mask ent).slot s =
        claimVal Reading.gl lay (fun r k => Reading.gl.val (t.input.entry r k)) q)
        sv.toList cl.toList :=
      forall2_getD _ 0 default sv.toList cl.toList
        (by rw [Array.length_toList, Array.length_toList, h3]) fun a ha => by
          rw [Array.length_toList] at ha
          rw [arr_getD_toList, arr_getD_toList]
          have hmem : cl.getD a default ∈ cl := by
            rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem ha]
            exact Array.getElem_mem ha
          have hsm : sv.getD a 0 ∈ sv := by
            have ha' : a < sv.size := by omega
            rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem ha']
            exact Array.getElem_mem ha'
          obtain ⟨un, a1, a2, a3, a4⟩ := hq _ hmem
          rw [slot_kept hLat mask ent _ (hfill _ hsm), htrue a ha]
          exact claimVal_inside gl_numerals a1 a2 a3 a4 _ _ fun r k b1 b2 => (hW r k b1 b2).symm
    have hstart := OnBytes.Road.merge_start gl_numerals
      (fun r k => Reading.gl.val (t.input.entry r k)) (y.2.worldOf Reading.gl mask ent) cl sv
      (powers (E.ofTriple x) sv.size) hq3 hslot
    have hleft := hLeft Unit HeadMergeAsk Unit n₁ n₂ (headMergeJob lay) c t seen ds rounds
      (wsForkStart sv (powers (E.ofTriple x) sv.size)) F G { G with planClaimsF := n } y.2 y.2 h
      wo.fvp {} (rowForm h wo.fvp {}) mask ent _ hds' hal hh0 hSn hrow (Later.refl _)
      (by
        intro i hi
        rw [hk, hown] at hi
        rw [hmask i hi]
        show _ = Reading.gl.val ((firstRun c).getD (0 + i) zeroE)
        rw [Nat.zero_add])
      (by
        rw [hk, hrl, hstart, h3]
        exact hsums)
    refine ⟨y.2, _, (flatRowLaid wo.p h wo.fvp {} _ y.2 [] hSL f1 f2 f3 f4).mpr hrow, ?_⟩
    rw [flatRowTie GE Reading.gl _ wo.p h wo.fvp {} hSL, hleft, empty_aff_value, hval]
    ring
  · -- (2)
    obtain ⟨Gam, hGam⟩ := gammaFold_returns lay (cl.zip (powers (E.ofTriple x) sv.size)).toList
      (fun y => mulE y.2 (wsEpsT lay y.1 wo.rm)) (Array.replicate lay.m0 zeroE) fun y hy => by
        rw [Array.toList_zip] at hy
        obtain ⟨un, a1, a2, a3, a4⟩ :=
          hq y.1 (Array.mem_def.mpr (List.of_mem_zip (a := y.1) (b := y.2) hy).1)
        exact ⟨un, a1, a2, a3, by rw [Array.size_replicate]; exact a4⟩
    refine ⟨Gam, by rw [wre]; exact hGam, ?_⟩
    have hp := OnBytes.Road.pending_gamma gl_numerals lay
      (fun r k => Reading.gl.val (t.input.entry r k)) wo.rm
      (cl.zip (powers (E.ofTriple x) sv.size)).toList hGam
    have hsw : ∑ y ∈ Finset.range lay.m0, Reading.gl.val (Gam.getD y zeroE) *
          rowAt Reading.gl lay.lk wo.rm W y =
        ∑ y ∈ Finset.range lay.m0, Reading.gl.val (Gam.getD y zeroE) *
          rowAt Reading.gl lay.lk wo.rm (fun r k => Reading.gl.val (t.input.entry r k)) y :=
      Finset.sum_congr rfl fun y hy => by
        rw [rowAt_inside Reading.gl lay.lk lay.m0 wo.rm W _
          (fun r k b1 b2 => (hW r k b1 b2).symm) y (Finset.mem_range.1 hy)]
    rw [hsw, ← hp, hval, hbe, hrmA, h3]

end ProofFile.Honest.K11

#print axioms ProofFile.Honest.K11.headMergeInner_of
