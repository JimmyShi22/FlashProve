-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/Stack.lean: THE LAYERS' OWN ROUNDS (K4): joinStart AND hearStack
RETURN (OnBytes/Desc/First/K4/Hear.lean: the element that joins two claims; the batched sumcheck;
its end). General laws: nothing is evaluated.

  mapM_shown_returns, shownRun_returns   K4's run of shown values.
  JoinPub         the readings of pure functions in joinStart, AS PREMISES: weighedOf, joinPart (AT
                  THE LOOKUP's TWO DRAWN ELEMENTS alpha AND theta), the two lengths, laidOf against
                  the lookup's padding counts; and that no part names a slot.
  joinStart_returns   it returns, and every slot of its form has been shown.
  rowsStack, slotsStack   the rows of K4's table that hearStack hears; the slots that it takes.
  StackPub        the readings of pure functions in hearStack, AS PREMISES, each asked for all
                  arrays that are drawn or shown later, of the lengths that the table of rounds
                  fixes: callsTS; panelsT over panelsA; the places' number against the plan's
                  rounds; the next claim's number; stackEnd.
  stackEnd_wD     what stackEnd's own last test gives.
  StackLeft       what hearStack leaves: the number of challenges; slots by number; every slot of
                  the claim has been shown; every slot that it takes is filled.
  **hearStack_returns**   room, a tape of its rows' shape, StackPub, the second token sumcheck is
                  there, the slot of its claimed sum and those of its end values have been shown,
                  and so has every slot of the lookup's end form and of the form KT: it returns,
                  with the room behind, nothing below turned, the next slot by number, and
                  StackLeft.

Limits. Conditional laws. JoinPub AND StackPub ARE PREMISES ON PURE FUNCTIONS' RETURNS: that they
hold at any plan is not shown in this file, nor that these returns hang on sizes and the layout
alone. "No part names a slot" rests on a reading: OnBytes/Model/LayerForms.lean holds no use of
Aff.slot; no law of this file says it. Beside these premises the two laws name no test on values.
Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.First.K4.Returns.Terms
import OnBytes.Desc.First.K4.StackTape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Rt
open OnBytes OnBytes.K.Kc D6.Ret
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.PscRun (Sized Filled)
open VerifiableInference.Desc.First.Shape (affSh AffSh)

/-! ## A run of shown values -/

/-- A list of shown values, one after the other. -/
theorem mapM_shown_returns (first : Nat) (G : Fork) (t : Tape) : ∀ (l : List Nat),
    (∀ i ∈ l, first + i < G.ns ∧ Filled G (first + i)) →
    ∃ a, (l.mapM fun i => Fl.shown (first + i)) G t = some (a, G, t) ∧ a.length = l.length
  | [], _ => ⟨[], by rw [List.mapM_nil]; rfl, rfl⟩
  | i :: l, h => by
    obtain ⟨a, e, hl⟩ := mapM_shown_returns first G t l fun j hj => h j (List.mem_cons_of_mem _ hj)
    have hi := h i (List.mem_cons_self ..)
    refine ⟨G.vp.getD (first + i) zeroE :: a, ?_, by rw [List.length_cons, List.length_cons, hl]⟩
    rw [List.mapM_cons]
    refine bindR (shownR hi.1 hi.2 t) ?_
    exact bindR e rfl

/-- **K4's run of shown values returns** where the slots are there and filled. -/
theorem shownRun_returns (first n : Nat) (G : Fork) (t : Tape)
    (h : ∀ i, i < n → first + i < G.ns ∧ Filled G (first + i)) :
    ∃ a, shownRun engFl first n G t = some (a, G, t) ∧ a.size = n := by
  obtain ⟨a, e, hl⟩ := mapM_shown_returns first G t (Array.range n).toList fun i hi =>
    h i (by simpa using hi)
  refine ⟨a.toArray, ?_, by simpa using hl⟩
  show ((Array.range n).mapM fun i => Fl.shown (first + i)) G t = _
  rw [Array.mapM_eq_mapM_toList, map_eq_pure_bind]
  exact bindR e rfl

/-! ## The start form of the batched sumcheck -/

/-- The readings of pure functions in joinStart, and that its parts name no slot. -/
structure JoinPub (v : Env) (fo : Forest.Heard) : Prop where
  weighed : ∃ weighed parts laid, v.y.calls.mapM v.weighedOf = some weighed ∧
    ((v.y.calls.zip weighed).toList.zipIdx.mapM fun x =>
      v.joinPart fo.alpha fo.theta x.2 x.1.1 x.1.2) = some parts ∧
    (parts.length == fo.shape.calls.size && fo.e.size == fo.shape.calls.size) = true ∧
    weighed.toList.zipIdx.foldlM (fun laid x => v.laidOf x.2 x.1 laid) (Forest.noPub fo.shape) =
      some laid ∧
    (laid == fo.shape.pub) = true ∧ ∀ a ∈ parts, (affSh a).slots = []

/-- **joinStart returns**, and every slot of its form has been shown. -/
theorem joinStart_returns {v : Env} {H : Heard} {tT : Tsc} (om : Array E) {F : Fork} (t : Tape)
    (hp : JoinPub v H.fo) (hT : H.tT = some tT) (h1 : tT.sCl < F.next) (h2 : Filled F tT.sCl)
    (hc : Shown F H.fo.cEnd) (hk : Shown F H.KT) :
    ∃ C, joinStart engFl v H om F t = some (C, F, t) ∧ Shown F C := by
  obtain ⟨weighed, parts, laid, a1, a2, a3, a4, a5, a6⟩ := hp.weighed
  have key : ∃ C pad, joinStart engFl v H om F t = some (C, F, t) ∧
      C = ((parts.zipIdx.foldl (fun (a : Aff) x => a.addMul x.1 (H.fo.e.getD x.2 zeroE)) aff0 +
        Aff.ofConst pad) - Aff.slot tT.sCl - H.fo.cEnd).addMul H.KT (om.getD 1 zeroE) := by
    refine ⟨_, (List.range (2 ^ H.fo.shape.rK - H.fo.shape.NT)).foldl
      (fun a t => addE a (mulE ((eqTab H.fo.zy).getD (H.fo.shape.NT + t) zeroE)
        (subE H.fo.alpha (H.fo.padKey 0)))) zeroE, ?_, rfl⟩
    unfold joinStart
    refine bindR (needR a1 _ _) ?_
    refine bindR (needR a2 _ _) ?_
    refine bindR (mustR a3 _ _) ?_
    refine bindR (needR a4 _ _) ?_
    refine bindR (mustR a5 _ _) ?_
    refine bindR (needR hT _ _) ?_
    rfl
  obtain ⟨C, pad, e, rfl⟩ := key
  refine ⟨_, e, ?_⟩
  refine Shown.addMul (Shown.sub (Shown.sub (Shown.add ?_ (shown_const F _)) (shown_slot h1 h2)) hc)
    hk _
  refine shown_foldl (fun x : Aff × Nat => x.1) _ _ _ (shown_const F _) fun x hx j hj => ?_
  have hm : x.1 ∈ parts := (List.mem_zipIdx' hx).2 ▸ List.getElem_mem _
  rw [a6 x.1 hm] at hj
  cases hj

/-! ## The batched sumcheck -/

/-- The rows of K4's table that hearStack hears: the end of its number 4, and its number 5. -/
def rowsStack (P : Pub) (lamS NCLp : Nat) : List Rd :=
  [batchRd 0 2] ++ masked lamS 1 2 (2 + (1 + P.y.LamM) + NCLp)

/-- The slots that hearStack takes. -/
def slotsStack (P : Pub) (lamS NCLp : Nat) : Nat :=
  1 + (2 * lamS + (2 + (2 + (1 + P.y.LamM) + NCLp)))

/-- The readings of pure functions in hearStack, each asked for all arrays that are drawn or shown
later, of the lengths that the table of rounds fixes. -/
structure StackPub (P : Pub) (v : Env) (H : Heard) (lamS NCLp : Nat) : Prop where
  pans : ∃ TS, callsTS P = some TS ∧ ∀ shownT : Array E, shownT.size = nEndT P.y →
    ∃ pans, panelsT ⟨v, H.fo.e, shownT, H.ztF, stubO P.y⟩ TS
        (panelsA ⟨v, H.fo.e, shownT, H.ztF, stubO P.y⟩ {}) = some pans ∧
      (ceilLog2 (placePanels pans.bl).2 == lamS) = true ∧ (pans.nextV == NCLp) = true ∧
      ∀ (rs om H1 V : Array E) (a b : E), rs.size = lamS → om.size = 2 →
        H1.size = 1 + P.y.LamM → V.size = NCLp →
        ∃ fin, stackEnd P.y (placePanels pans.bl).1 rs lamS om H1 V a b = some fin
  join : JoinPub v H.fo

/-- What stackEnd's own last test gives: the bits of the down product's panel. -/
theorem stackEnd_wD {y : Lay} {bl : Array SBlk} {rs om H1 V : Array E} {lam : Nat} {a b : E}
    {fin : StackEnd} (h : stackEnd y bl rs lam om H1 V a b = some fin) :
    fin.wD = y.h.ll + y.lPf := by
  unfold stackEnd at h
  cases hs : bl.foldlM (stackEndOf y rs lam om H1 V) { As := a, Bs := b } with
  | none =>
    rw [hs] at h
    cases h
  | some s =>
    rw [hs] at h
    have h' : (if (s.wD != y.h.ll + y.lPf) = true then none else some s) = some fin := h
    by_cases hc : (s.wD != y.h.ll + y.lPf) = true
    · rw [if_pos hc] at h'
      cases h'
    · rw [if_neg hc] at h'
      obtain rfl := Option.some.inj h'
      simpa using hc

/-- What hearStack leaves. F: the ledger in front; G: behind. -/
structure StackLeft (P : Pub) (lamS NCLp : Nat) (F G : Fork) (K : HeardStack) : Prop where
  rs : K.rs.size = lamS
  sA0 : K.sA0 = F.next + (1 + (2 * lamS + 2))
  sH1 : K.sH1 = K.sA0 + 1
  sB0 : K.sB0 = K.sH1 + (1 + P.y.LamM)
  sV : K.sV = K.sB0 + 1
  ends : ∀ i, i < 2 + (1 + P.y.LamM) + NCLp → Filled G (K.sA0 + i)
  wD : K.fin.wD = P.y.h.ll + P.y.lPf
  row : Shown G K.rowS
  /-- every slot that it takes is filled -/
  marks : ∀ j, F.next ≤ j → j < G.next → Filled G j

/-- **hearStack returns.** -/
theorem hearStack_returns (P : Pub) (v : Env) (H : Heard) (lamS NCLp : Nat) {tT : Tsc} {F : Fork}
    {k : Nat} (hR : Room F (slotsStack P lamS NCLp + k)) {t : Tape}
    (hT : TapeOf (rowsStack P lamS NCLp) t) (u : Tape) (hp : StackPub P v H lamS NCLp)
    (htT : H.tT = some tT) (h1 : tT.sCl < F.next) (h2 : Filled F tT.sCl)
    (h3 : ∀ i, i < nEndT P.y → tT.sEnd + i < F.next ∧ Filled F (tT.sEnd + i))
    (hc : Shown F H.fo.cEnd) (hk : Shown F H.KT) :
    ∃ K G, hearStack engFl P v H lamS NCLp F (t ++ u) = some (K, G, u) ∧ Room G k ∧ Below F G ∧
      G.next = F.next + slotsStack P lamS NCLp ∧ StackLeft P lamS NCLp F G K := by
  unfold rowsStack at hT
  unfold slotsStack at hR
  obtain ⟨t1, t2, rfl, ht1, ht2⟩ := tape_append hT
  obtain ⟨s, d, t', rfl, a1, a2, a3⟩ := tape_cons ht1
  obtain rfl := tape_nil a3
  obtain rfl := len_zero a1
  obtain ⟨x, rfl⟩ := len_one a2
  obtain ⟨s0, eps, rs, sY, beta, vals, rfl, b1, b2, b3, b4, b5⟩ := tape_masked ht2
  obtain ⟨mu0, rfl⟩ := len_one b1
  have hns : F.next ≤ F.ns := by have := hR.fits; omega
  obtain ⟨TS, hTS, hpan⟩ := hp.pans
  obtain ⟨shownT, c1, c1s⟩ := shownRun_returns tT.sEnd (nEndT P.y) F
    (⟨some RoundName.pscEpsilon.name, 0, 0, [mu0], [eps]⟩ ::
      (rs ++ ⟨some RoundName.pscY.name, 1, 0, sY, [beta]⟩ ::
        ⟨some RoundName.pscValues.name, 0, 0, vals, []⟩ :: u))
    fun i hi => ⟨by have := (h3 i hi).1; omega, (h3 i hi).2⟩
  obtain ⟨pans, hpans, hplaces, hnext, hend⟩ := hpan shownT c1s
  obtain ⟨C, c2, c2s⟩ := joinStart_returns (powers x 2)
    (⟨some RoundName.pscEpsilon.name, 0, 0, [mu0], [eps]⟩ ::
      (rs ++ ⟨some RoundName.pscY.name, 1, 0, sY, [beta]⟩ ::
        ⟨some RoundName.pscValues.name, 0, 0, vals, []⟩ :: u)) hp.join htT h1 h2 hc hk
  obtain ⟨T, hTC⟩ := c2s.public hns
  obtain ⟨p0, d1, d2, d3⟩ := pscBeginR (n := 2 * lamS + (2 + (2 + (1 + P.y.LamM) + NCLp) + k))
    (by refine hR.mono ?_; omega) hTC mu0 eps 0
    (rs ++ ⟨some RoundName.pscY.name, 1, 0, sY, [beta]⟩ ::
      ⟨some RoundName.pscValues.name, 0, 0, vals, []⟩ :: u)
  obtain ⟨-, d4⟩ := pscBegin_head d1
  obtain ⟨st, G1, e1, e2, e3, e4, e5, e6, e7, e8⟩ := plainRounds_returns { lam := lamS, p := p0 } rs
    _ (2 + (2 + (1 + P.y.LamM) + NCLp) + k)
    (⟨some RoundName.pscY.name, 1, 0, sY, [beta]⟩ ::
      ⟨some RoundName.pscValues.name, 0, 0, vals, []⟩ :: u) b2 b3 d2
  obtain ⟨p2, G2, f1, f2, f3, f4, f5⟩ := pscEndsR e2 (by omega) (by omega) 0 0 sY vals beta u b4 b5
  have hnx := f2.next
  have hft := f2.fits
  have hfi := f2.first
  have e4' : G1.next = F.next + 1 + 2 * lamS := e4
  have hfill : ∀ i, i < 2 + (1 + P.y.LamM) + NCLp →
      G1.next + 2 + i < G2.ns ∧ Filled G2 (G1.next + 2 + i) := fun i hi =>
    ⟨by omega, f2.ends i hi⟩
  obtain ⟨H1, g1, g1s⟩ := shownRun_returns (G1.next + 2 + 1) (1 + P.y.LamM) G2 u fun i hi => by
    have := hfill (1 + i) (by omega)
    rwa [← Nat.add_assoc] at this
  obtain ⟨V, g2, g2s⟩ := shownRun_returns (G1.next + 2 + 1 + (1 + P.y.LamM) + 1) NCLp G2 u
    fun i hi => by
      have := hfill (1 + (1 + P.y.LamM) + 1 + i) (by omega)
      have e : G1.next + 2 + (1 + (1 + P.y.LamM) + 1 + i) =
        G1.next + 2 + 1 + (1 + P.y.LamM) + 1 + i := by omega
      rwa [e] at this
  have hA := hfill 0 (by omega)
  have hB := hfill (1 + (1 + P.y.LamM)) (by omega)
  rw [Nat.add_zero] at hA
  have eB : G1.next + 2 + (1 + (1 + P.y.LamM)) = G1.next + 2 + 1 + (1 + P.y.LamM) := by omega
  rw [eB] at hB
  obtain ⟨fin, hfin⟩ := hend st.rs (powers x 2) H1 V (G2.vp.getD (G1.next + 2) zeroE)
    (G2.vp.getD (G1.next + 2 + 1 + (1 + P.y.LamM)) zeroE) e7
    (OnBytes.Tie.Pv.Tail.Port.powers_size _ _) g1s g2s
  have hstart : p2.start = C := ((pscEnds_head f1).start.trans e3.start).trans d4
  have hfirst : p2.first = F.next := (f3.trans e3.first).trans d3
  have BF2 : Below F G2 := ⟨f4.trans e5, fun _ => f2.sized, by omega, fun j hj =>
    (f5 j (by omega)).trans ((e8 j).trans filled_next)⟩
  obtain ⟨G3, r1, r2, r3, r4, r5, r6, r7, r8⟩ := row_tape f2.isOpen f2.room (by omega)
    (mulE fin.As fin.Bs) (kept := {}) (by rw [hstart]; exact c2s.below BF2)
    (fun _ hj => by cases hj)
    (fun j hj => by
      rw [hstart] at hj
      have hj' : j ∈ (affSh C).slots ++ ([] : List Nat) := hj
      rw [List.append_nil] at hj'
      rw [hfirst]
      exact (c2s j hj').1) u
  have etape : ([⟨some RoundName.batSigma.name, 0, 2, [], [x]⟩] ++
      ⟨some RoundName.pscEpsilon.name, 0, 0, [mu0], [eps]⟩ ::
        (rs ++ [⟨some RoundName.pscY.name, 1, 0, sY, [beta]⟩,
          ⟨some RoundName.pscValues.name, 0, 0, vals, []⟩]) ++ u : Tape) =
      ⟨some RoundName.batSigma.name, 0, 2, [], [x]⟩ ::
        ⟨some RoundName.pscEpsilon.name, 0, 0, [mu0], [eps]⟩ ::
        (rs ++ ⟨some RoundName.pscY.name, 1, 0, sY, [beta]⟩ ::
          ⟨some RoundName.pscValues.name, 0, 0, vals, []⟩ :: u) := by simp
  refine ⟨{ rs := st.rs, sA0 := G1.next + 2, sH1 := G1.next + 2 + 1,
            sB0 := G1.next + 2 + 1 + (1 + P.y.LamM), sV := G1.next + 2 + 1 + (1 + P.y.LamM) + 1,
            fin := fin, rowS := p2.rowForm (mulE fin.As fin.Bs) {} }, G3, ?_, r2,
    ⟨r4.trans BF2.ns, fun _ => r5, by omega, fun j hj =>
      (r7 j (Or.inl (by omega))).trans (BF2.same j hj)⟩, by unfold slotsStack; omega, ?_⟩
  · refine etape ▸ ?_
    unfold hearStack
    refine bindR (batchR 2 (by decide) x F _) ?_
    refine bindR (needR htT _ _) ?_
    refine bindR c1 ?_
    refine bindR (needR hTS _ _) ?_
    refine bindR (needR hpans _ _) ?_
    refine bindR (mustR hplaces _ _) ?_
    refine bindR c2 ?_
    refine bindR d1 ?_
    refine bindR e1 ?_
    refine bindR (mustR hnext _ _) ?_
    refine bindR f1 ?_
    refine bindR g1 ?_
    refine bindR g2 ?_
    refine bindR (shownR hA.1 hA.2 u) ?_
    refine bindR (shownR hB.1 hB.2 u) ?_
    refine bindR (needR hfin _ _) ?_
    refine bindR r1 ?_
    rfl
  · exact
      { rs := e7, sA0 := by show G1.next + 2 = _; omega, sH1 := rfl, sB0 := rfl, sV := rfl
        ends := fun i hi => (r7 _ (Or.inr (by show _ ≤ G1.next + 2 + i; omega))).2 (f2.ends i hi)
        wD := stackEnd_wD hfin, row := r8
        marks := fun j h1 h2 => by
          by_cases q : j < G1.next + 2
          · exact r6 j (by omega) (by omega)
          · have e : G1.next + 2 + (j - (G1.next + 2)) = j := by omega
            have hf := f2.ends (j - (G1.next + 2)) (by omega)
            rw [e] at hf
            exact (r7 j (Or.inr (by omega))).2 hf }

end OnBytes.Desc.First.K4.Rt

#print axioms OnBytes.Desc.First.K4.Rt.mapM_shown_returns
#print axioms OnBytes.Desc.First.K4.Rt.shownRun_returns
#print axioms OnBytes.Desc.First.K4.Rt.joinStart_returns
#print axioms OnBytes.Desc.First.K4.Rt.stackEnd_wD
#print axioms OnBytes.Desc.First.K4.Rt.hearStack_returns
