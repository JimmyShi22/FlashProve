-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K10/Honest/Leaves.lean: WHAT A YES OF THE CLOSING OF A SEGMENT LEAVES: the record behind the
block's decision, written out; and with it THE TWO HALVES OF THE KIND's LAW JOINED. Theorems on the
verifier's own text; no prover's moves are named (`foldQK`: the other house's honest round polynomials).

  `heard_reads`, `rounds_read`   what the verifier's text hears of a round is what another house's
                    readers of a round return (`sentOf`, `drawnOf`, `claimOf`,
                    Johnson/Prover/Link/FormFold.lean)
  `yes_leaves`      EACH YES OF THE DECISION, at a list of two rounds or more, LEAVES: nothing owed; the
                    frame with the single rows `foldOutAt S1 F row m (rE :: rR)`, no mask, the link's
                    number moved on, the next call "first"; the statement `spent S1 m`: S1, F, row, m as in
                    the facts `CloseFront` at the element that "BAT" drew
  `close_plays`     THE TWO HALVES: from `CloseBase`, rows that hold of words, a fresh table that pairs
                    and rounds of the kind's shape that show the honest polynomials: THE DECISION
                    SAYS YES, AND THE SINGLE ROWS THAT IT LAYS INTO THE FRAME ARE TRUE of the folded
                    message, their kept forms with them

By: `kind_decide_iff`, `closeFrame_iff` (Johnson/Desc/First/Close/Law/KindDecide.lean, CloseMeans.lean),
whose proposition is opened as in Johnson/Desc/K10/Honest/Front.lean; `claimOf_cons`
(Johnson/Prover/Link/FormFoldLaws.lean); `close_yes_all` (Base.lean); `closeBase_holds` (Holds.lean).

Limits. Over five files of another house (Holds.lean's Limits). Of the block's decision at the kind's
own record (the step, lifted, wrapped and guarded: Step.lean, AtS.lean). "True" is said of the message
`foldMsg` of the words' tables and the fresh table φ: φ IS A LETTER: that it is the table of the oracle
message number m is not asked; that the words are 0 where nobody sent anything is not asked. That the
rounds show the honest round polynomials is a premise. Behind the fold the kept forms' value stays in
the other house's letters (`keptVal`; Values.lean's Limits). That a list of fewer than two rounds gets
no yes is shown in Front.lean (`front_of_yes`). Nothing on soundness, completeness or hiding of the
protocol.

-/
import Johnson.Desc.K10.Honest.Holds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.Values
open OnBytes OnBytes.Means OnBytes.Slice Johnson.Prover.Link H2K.ClaimSays Cb
open VerifiableInference.Desc
open VerifiableInference.Desc.First.Close (Par Rec kind entries HeardMeans RoundsMeans onSt)
open ProofFile.Honest.K10.YesFree (BaseData CloseBase CloseFront CloseData ShapedAll batDraw)

/-- The items that the verifier's text takes as elements are those that `sentOf` returns. -/
theorem elems_sent : ∀ (vs : List Fmt.ItemValue) (xs : List E), First.Close.elemsOf vs = some xs →
    (vs.filterMap fun v => match v with
      | .e x => some (E.ofTriple x)
      | _ => none) = xs
  | [], xs, h => by
    obtain rfl : [] = xs := Option.some.inj h
    rfl
  | v :: vs, xs, h => by
    unfold First.Close.elemsOf at h
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨bs, hbs, h3⟩ := Option.bind_eq_some_iff.1 h2
    obtain rfl : b :: bs = xs := Option.some.inj h3
    have ih := elems_sent vs bs hbs
    cases v with
    | e y =>
      obtain rfl : E.ofTriple y = b := Option.some.inj hb
      simp only [List.filterMap_cons, ih]
    | _ => cases hb

/-- What the verifier's text hears of a round. -/
theorem heard_reads {name : String} {items : Nat} {e : Fmt.Entry} {r : Fmt.RoundView} {xs : List E} {x : E}
    (h : HeardMeans name items e r 0 xs x) : sentOf r = xs ∧ drawnOf r = x := by
  obtain ⟨_, _, _, _, _, h6, t, ht, rfl⟩ := h
  refine ⟨elems_sent _ _ h6, ?_⟩
  unfold drawnOf
  rw [ht]
  rfl

/-- What it hears of the rounds "FOLD round". -/
theorem rounds_read : ∀ (es : List Fmt.Entry) (rs : List Fmt.RoundView) (claim : E) (gs : List E) (cl : E),
    RoundsMeans es rs claim gs cl → gs = rs.map drawnOf ∧ cl = claimOf rs claim
  | [], [], _, _, _, h => ⟨h.1, h.2⟩
  | e :: es, r :: rs, claim, gs, cl, h => by
    obtain ⟨c0, c2, g, gs', hh, hr, rfl⟩ := h
    obtain ⟨a, b⟩ := heard_reads hh
    obtain ⟨i1, i2⟩ := rounds_read es rs _ gs' cl hr
    refine ⟨by rw [List.map_cons, b, i1], ?_⟩
    have e0 : ([c0, c2] : List E).getD 0 zeroE = c0 := rfl
    have e1 : ([c0, c2] : List E).getD 1 zeroE = c2 := rfl
    rw [i2, Johnson.Prover.Link.claimOf_cons, a, b, e0, e1]
  | [], _ :: _, _, _, _, h => h.elim
  | _ :: _, [], _, _, _, h => h.elim

/-- **WHAT EACH YES OF THE DECISION LEAVES.** -/
theorem yes_leaves {Cl : Type} {P : Par} {s s' : Rec} {rB rE : Fmt.RoundView} {rR : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (h : ((kind (Cl := Cl)) P).decide s (rB :: rE :: rR) gs = .ok s') :
    ∃ t D, rB.drawn.elems = [t] ∧ CloseFront P s (E.ofTriple t) D ∧
      s' = ⟨none, { s.frame with
          rows := foldOutAt D.d.st (D.F s) D.row D.m (rE :: rR), mask := none
          link := s.frame.link + 1, next := .first }, spent D.d.st D.m⟩ := by
  obtain ⟨y, hy, rfl⟩ := (First.Close.kind_decide_iff P s s' (rB :: rE :: rR) gs).1 h
  obtain ⟨k1, L, k2, G, k3, k4, rows, hc, hf'⟩ := (First.Close.closeFrame_iff _ _ _ _ _ y.1 y.2).1 hy
  obtain ⟨eB, es₁, rB', rs₁, e1, e1', m, hm, row, Ly, S1, hbat, hkh, hfold⟩ := hc
  obtain ⟨b1, input, d, b2, xs, x, b3, b4, b5, rfl, rfl⟩ := hbat
  obtain ⟨eE, eR, rE', rR', e2, e2', ⟨s1, _⟩, _, f3, f4, f5, d2, f6, sum, eps, f7, f8, gam, cl, f9,
    f10, f11⟩ := hfold
  obtain ⟨rfl, rfl⟩ := List.cons.inj e1
  obtain ⟨rfl, rfl⟩ := List.cons.inj e1'
  obtain ⟨rfl, rfl⟩ := List.cons.inj e2
  obtain ⟨rfl, rfl⟩ := List.cons.inj e2'
  obtain ⟨t, ht, rfl⟩ := b3.2.2.2.2.2.2
  obtain ⟨a1, a2⟩ := heard_reads f7
  obtain ⟨g1, g2⟩ := rounds_read _ _ _ _ _ f9
  have hd2 : d2.st = spent d.st m := by
    unfold Ground.spendAsMaskP at f6
    split at f6
    · obtain rfl := Option.some.inj f6
      rfl
    · cases f6
  refine ⟨t, ⟨L, G, m, input, d, d2, row⟩, ht, ⟨k1, k2, k3, k4, hm, b1, b2, b4, b5, hkh,
    (List.length_replicate ..).symm.trans s1, f3, f4, f5, f6, f8⟩, ?_⟩
  have hrows : rows = foldOutAt d.st
      (ioppFoldShape { code := s.frame.shape.code, maskCode := s.frame.shape.maskCode, k := G.k,
                       h := G.h } input.layout) row m (rE :: rR) := by
    rw [f10, hd2, g1, g2]
    show _ = foldOutput (spent d.st m) _ row m (drawnOf rE) (rR.map drawnOf)
      (claimOf rR (maddE ((sentOf rE).getD 0 zeroE) (drawnOf rE) row.target))
    rw [a1, a2]
    rfl
  show (⟨none, y.1, y.2⟩ : Rec) = _
  rw [hf', f11, hd2, hrows]
  rfl

/-- **THE TWO HALVES OF THE KIND's LAW, JOINED.** st: a stage of the library with the group's four
numbers. m: words of which every row that the test takes in holds. φ: a fresh table that pairs with the
coefficients W. rB, rE, rR: rounds of the kind's shape; rE shows the sum of W's polynomial over the
cube; rR show the honest round polynomials at the point γ. -/
theorem close_plays {Cl : Type} {P : Par} {s : Rec} {D : BaseData} (H : CloseBase P s D) (st : Sg)
    (nk : D.Gq.k = st.h + st.g) (nh : D.Gq.h = st.h)
    (nl : 2 ^ (Own.layoutOf s.st D.G).logEll = st.C.l)
    (nz : 2 ^ (Own.layoutOf s.st D.G).logEllZk = st.Z.l) (m : Words GE)
    (hs : AllSay rdE s.st (runRows s.st D.G).toList m) (rB rE : Fmt.RoundView) (rR : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (hl : (rB :: rE :: rR).length = 2 + P.k)
    (hsh : ShapedAll (rB :: rE :: rR)) (φ : st.cFr.J → GE)
    (W : HIdx (sVars GE 2 (st.h + st.g)) → GE) (γ : HPt (sVars GE 2 (st.h + st.g)))
    (hP : Pairs st st.Z.l W φ)
    (hσ : readE ((sentOf rE).getD 0 zeroE) = hMu (sVars GE 2 (st.h + st.g)) W)
    (hR : ∀ row, Own.batch (D.S1 s) s.frame.group ⟨Own.layoutOf s.st D.G, runRows s.st D.G⟩
        (drawnOf rB) = some row →
      Shows (st.h + st.g) rR (foldQK st (vecG st row)
        (msgOf st (tablesOf (D.S1 s) (Own.layoutOf s.st D.G) m)) W (readE (drawnOf rE))
        (keptVal (keptLen (D.S1 s)) (tablesOf (D.S1 s) (Own.layoutOf s.st D.G) m).kept row.kept)
        γ) γ) :
    ∃ s', ((kind (Cl := Cl)) P).decide s (rB :: rE :: rR) gs = .ok s' ∧
      ∑ j, vecS st s'.frame.rows j *
            foldMsg st (msgOf st (tablesOf (D.S1 s) (Own.layoutOf s.st D.G) m)) φ
              (sPt 2 (st.h + st.g) γ) j +
          keptVal (keptLen (D.S1 s)) (tablesOf (D.S1 s) (Own.layoutOf s.st D.G) m).kept
            s'.frame.rows.kept = readE s'.frame.rows.target := by
  obtain ⟨s', hy⟩ := ProofFile.Honest.K10.YesFree.close_yes_all (Cl := Cl) H (rB :: rE :: rR) gs hl hsh
  obtain ⟨t, D', ht, H', rfl⟩ := yes_leaves hy
  have hx : drawnOf rB = E.ofTriple t := by
    unfold drawnOf
    rw [ht]
    rfl
  obtain ⟨row, hrow, hall⟩ := closeBase_holds H st nk nh nl nz m hs (drawnOf rB)
  -- the data of the yes are the base's
  have eG : D'.G = D.Gq := Option.some.inj (H'.group.symm.trans H.group)
  have em : D'.m = D.m := Option.some.inj (H'.mask.symm.trans H.mask)
  have eb : (D'.input, D'.d) = (⟨Own.layoutOf s.st D.G, runRows s.st D.G⟩,
      { onSt s.st with st := D.S1 s }) := by
    have h1 := H'.layout
    unfold Ground.beginRunP at h1
    have hb : Ground.ok (Ground.beginRunL (onSt s.st).st s.frame.group) = true := H.beginRun
    have ht' : (onSt s.st).st.groups[s.frame.group]? = some D.G := H.there
    rw [if_pos hb, ht'] at h1
    exact (Option.some.inj h1).symm
  obtain ⟨ei, ed⟩ := Prod.mk.inj eb
  have er : D'.row = row := by
    have h2 := H'.combine
    rw [ei, ed, ← hx] at h2
    exact Option.some.inj (h2.symm.trans hrow)
  refine ⟨_, hy, ?_⟩
  have hfin := hall rE rR φ W γ hP hσ (hR row hrow)
  have eF : D'.F s = D.F s := by
    show ioppFoldShape _ D'.input.layout = ioppFoldShape _ (Own.layoutOf s.st D.G)
    rw [ei, eG]
  show ∑ j, vecS st (foldOutAt D'.d.st (D'.F s) D'.row D'.m (rE :: rR)) j * _ +
    keptVal _ _ (foldOutAt D'.d.st (D'.F s) D'.row D'.m (rE :: rR)).kept =
      readE (foldOutAt D'.d.st (D'.F s) D'.row D'.m (rE :: rR)).target
  rw [ed, eF, er, em]
  exact hfin

end ProofFile.Honest.K10.Values

#print axioms ProofFile.Honest.K10.Values.heard_reads
#print axioms ProofFile.Honest.K10.Values.rounds_read
#print axioms ProofFile.Honest.K10.Values.yes_leaves
#print axioms ProofFile.Honest.K10.Values.close_plays
