-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/PointsIs.lean: CONDITIONAL: the verifier's function for the named points
and weights of an attention segment's own rounds (pointsOf, Johnson/Desc/First/Att/Points.lean),
called at two values of what was heard: which fields of its two results are the same, word for word.
Definitions of propositions, and statements with their proofs. No frame of a prover is imported.

Why. The prover's side calls that function on challenges laid into a value whose numbers of
scalars and rows are blank (ptsOf, Johnson/Desc/K5/Honest/Points.lean), and it calls it early, when
some challenges are still to come. So an equation of the two results is false. What holds is an
equation field by field, for the fields that are made of the key points alone, and for those that
are made of challenges which both values hold.

  remKey, unitKey, divKey   of a plane claim's unit, a softmax-table unit, and the division: the
                  fields that are made of the place's numbers and the key points alone
  KeySame p p'    these are the same in p and p'
  points_congr    CONDITIONAL: where the function returns at one value heard and one list of rows,
                  it returns at every other with the same three lengths, and KeySame holds: so
                  whether it returns hangs on the place's numbers, the key points and three
                  lengths alone
  points_chal     three fields as they are made of challenges
  PtsTo x q p p'  KeySame, and the fields made of the challenges of the parts in front of part
                  number q are the same
  points_to       CONDITIONAL: from SameTo (Johnson/Desc/K5/Honest/Law/HeardIs.lean) and two returns
  points_same     CONDITIONAL: PtsTo of the prover's named points and the verifier's: KeySame, and
                  the fields that the parts in front of part q make; no other field
  ptsOf_agree, ptsOf_none   the prover's own call at two lists of challenges that are one in the
                  rounds in front of part q, at the same key points

Not compared: every number of a scalar, every first number of end values, every row.

Limits. Every statement is conditional. Nothing is said of a value that is sent. No property is
claimed by a definition. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K5.Honest.Law.HeardIs
import Johnson.Desc.First.Att.Claims.PointsRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes (E zeroE)
open VerifiableInference.Desc.First.Att.P (Geo Heard Left Pts RemP ScoreP DivP W1 pointsOf chal
  tileSums eqTab)

/-! ## 1 The fields that are made of the key points alone -/

def remKey (u : RemP) : Nat × Array E × Bool × Array W1 × Nat := (u.call, u.z, u.isD, u.pw, u.np)

def unitKey (k : ScoreP) :
    Nat × Nat × Bool × Array W1 × Array E × Array E × Array E × Array E × Array E :=
  (k.call, k.claim, k.below, k.pw, k.zg, k.zs, k.zi, k.zj, k.wI)

def divKey (d : DivP) : Array W1 × Array W1 × Array W1 × Nat × E × Array E × Array E × Array E ×
    Array E × Array E × Array E × Array E × Array E :=
  (d.pwW, d.pwX, d.pwH, d.qWH, d.zsl, d.zgW, d.ziW, d.zcW, d.zgX, d.ziX, d.zgH, d.ziH, d.zcH)

/-- **The fields that are made of the key points alone are the same.** It is a definition. -/
structure KeySame (p p' : Pts) : Prop where
  planes : p.planes.toList.map remKey = p'.planes.toList.map remKey
  scores : p.scores.toList.map unitKey = p'.scores.toList.map unitKey
  d : divKey p.d = divKey p'.d

namespace PointsIs

/-- A fold that may refuse, at two lists that are related member by member. -/
theorem foldlM_rel {α β : Type} {step : β → α → Option β} {Rx : α → α → Prop}
    {Rb : β → β → Prop} : ∀ (xs xs' : List α), List.Forall₂ Rx xs xs' → ∀ b b' r, Rb b b' →
    xs.foldlM step b = some r →
    (∀ b b' x x' r, Rb b b' → Rx x x' → step b x = some r → ∃ r', step b' x' = some r' ∧ Rb r r') →
    ∃ r', xs'.foldlM step b' = some r' ∧ Rb r r'
  | _, _, .nil, b, b', r, hb, h, _ => by
    simp only [List.foldlM_nil, Option.pure_def, Option.some.injEq] at h
    subst h
    exact ⟨b', rfl, hb⟩
  | x :: xs, x' :: xs', .cons hx ht, b, b', r, hb, h, hs => by
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨b1, h1, h2⟩ := h
    obtain ⟨b1', h1', hb1⟩ := hs b b' x x' b1 hb hx h1
    obtain ⟨r', h2', hr⟩ := foldlM_rel xs xs' ht b1 b1' r hb1 h2 hs
    refine ⟨r', ?_, hr⟩
    simp only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff]
    exact ⟨b1', h1', h2'⟩

/-- A map over a zipped list that reads the first members alone. -/
theorem map_zip_congr {α β γ : Type} (f : α × β → γ) (hf : ∀ u b b', f (u, b) = f (u, b')) :
    ∀ (l : List α) (a a' : List β), a.length = a'.length → (l.zip a).map f = (l.zip a').map f
  | [], _, _, _ => by simp
  | _ :: _, [], [], _ => rfl
  | u :: l, b :: a, b' :: a', h => by
    simp only [List.zip_cons_cons, List.map_cons]
    rw [hf u b b', map_zip_congr f hf l a a' (Nat.succ.inj h)]
  | _ :: _, [], _ :: _, h => by cases h
  | _ :: _, _ :: _, [], h => by cases h

/-- Two lists zipped twice, with one list of first members. -/
theorem zip2_rel {α β γ : Type} : ∀ (l : List α) (a a' : List β) (b b' : List γ),
    a.length = a'.length → b.length = b'.length →
    List.Forall₂ (fun (x x' : (α × β) × γ) => x.1.1 = x'.1.1) ((l.zip a).zip b) ((l.zip a').zip b')
  | [], _, _, _, _, _, _ => by simp
  | _ :: _, [], [], _, _, _, _ => by simp
  | _ :: _, _ :: _, _ :: _, [], [], _, _ => by simp
  | u :: l, x :: a, x' :: a', y :: b, y' :: b', h1, h2 => by
    simp only [List.zip_cons_cons]
    exact .cons rfl (zip2_rel l a a' b b' (Nat.succ.inj h1) (Nat.succ.inj h2))
  | _ :: _, [], _ :: _, _, _, h, _ => by cases h
  | _ :: _, _ :: _, [], _, _, h, _ => by cases h
  | _ :: _, _ :: _, _ :: _, [], _ :: _, _, h => by cases h
  | _ :: _, _ :: _, _ :: _, _ :: _, [], _, h => by cases h

/-- What the fold over the softmax-table units has laid so far, compared. -/
def AccSame (b b' : Array RemP × Array ScoreP) : Prop :=
  b.1.toList.map remKey = b'.1.toList.map remKey ∧ b.2.toList.map unitKey = b'.2.toList.map unitKey

/-- The fold over the softmax-table units, from the remainder units' plane claims, at two lists of
numbers of scalars and two related lists of units. -/
theorem fold_two {α β : Type} {F : α × Nat → RemP}
    {step : Array RemP × Array ScoreP → β → Option (Array RemP × Array ScoreP)}
    {Rx : β → β → Prop} {kr : Array α} {rem rem' : Array Nat} {xs xs' : List β}
    {a : Array RemP × Array ScoreP} (hf : xs.foldlM step ((kr.zip rem).map F, #[]) = some a)
    (hx : List.Forall₂ Rx xs xs') (hr : rem.size = rem'.size)
    (hF : ∀ u b b', remKey (F (u, b)) = remKey (F (u, b')))
    (hs : ∀ b b' x x' r, AccSame b b' → Rx x x' → step b x = some r →
      ∃ r', step b' x' = some r' ∧ AccSame r r') :
    ∃ a', xs'.foldlM step ((kr.zip rem').map F, #[]) = some a' ∧ AccSame a a' := by
  have h0 : AccSame ((kr.zip rem).map F, #[]) ((kr.zip rem').map F, #[]) := by
    refine ⟨?_, rfl⟩
    show ((kr.zip rem).map F).toList.map remKey = ((kr.zip rem').map F).toList.map remKey
    rw [Array.toList_map, Array.toList_map, Array.toList_zip, Array.toList_zip, List.map_map,
      List.map_map]
    exact map_zip_congr _ (fun u b b' => hF u b b') _ _ _ (by simpa using hr)
  exact foldlM_rel xs xs' hx _ _ a h0 hf hs

end PointsIs

open PointsIs

/-- **Whether the function returns hangs on the place's numbers, the key points and three lengths
alone; and what it makes of the key points alone is the same at every value heard.** CONDITIONAL:
the three lengths are the same; the function returns at (h, L). -/
theorem points_congr {g : Geo} {zk : Array (Array E)} {h h' : Heard} {L L' : Left} {p : Pts}
    (nR : h.remainders.size = h'.remainders.size) (nS : h.scores.size = h'.scores.size)
    (nL : L.scores.size = L'.scores.size) (hp : pointsOf g zk h L = some p) :
    ∃ p', pointsOf g zk h' L' = some p' ∧ KeySame p p' := by
  unfold pointsOf at hp ⊢
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, K5Law.guard_some, Option.pure_def,
    Option.some.injEq] at hp ⊢
  obtain ⟨_, g1, _, g2, a, hf, uW, hW, uX, hX, uH, hH, _, g3, _, g4, e⟩ := hp
  rw [← Array.foldlM_toList, Array.toList_zip, Array.toList_zip] at hf
  obtain ⟨a', hf', Ra⟩ := fold_two (rem' := h'.remainders) hf
    (zip2_rel g.scores.toArray.toList h.scores.toList h'.scores.toList L.scores.toList
      L'.scores.toList (by simpa using nS) (by simpa using nL)) nR (fun _ _ _ => rfl)
    (by
      rintro ⟨b1, b2⟩ ⟨b1', b2'⟩ ⟨⟨u, s0, sc⟩, row⟩ ⟨⟨u', s0', sc'⟩, row'⟩ r ⟨hb1, hb2⟩ hx h1
      have hx' : u = u' := hx
      subst hx'
      have hsz : b1.size = b1'.size := by
        have := congrArg List.length hb1
        simpa using this
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, K5Law.guard_some, Option.pure_def,
        Option.some.injEq] at h1 ⊢
      obtain ⟨_, hg, e1⟩ := h1
      subst e1
      refine ⟨_, ⟨(), hg, rfl⟩, ?_, ?_⟩
      · simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil]
        rw [hb1]
        rfl
      · simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil]
        rw [hb2]
        simp only [unitKey, hsz])
  subst e
  refine ⟨_, ⟨(), by rw [← nR]; exact g1, (), by rw [← nS, ← nL]; exact g2, a', ?_, uW, hW, uX, hX,
    uH, hH, (), g3, (), g4, rfl⟩, Ra.1, Ra.2, rfl⟩
  rw [← Array.foldlM_toList, Array.toList_zip, Array.toList_zip]
  exact hf'

/-- Three fields as they are made of challenges. CONDITIONAL: the return. -/
theorem points_chal {g : Geo} {zk : Array (Array E)} {h : Heard} {L : Left} {p : Pts}
    (hp : pointsOf g zk h L = some p) :
    p.d.wJv = (tileSums g (eqTab ((chal h.below).extract g.lgk (g.lgk + (g.lnT - 1))))
        (eqTab ((chal h.below).extract (g.lgk + (g.lnT - 1)) (g.lgk + (g.lnT - 1) + g.lnT)))).2 ∧
      p.x.tg = h.point.extract 0 g.lgk ∧ p.x.ti = h.point.extract g.lgk (g.lgk + g.lt) := by
  unfold pointsOf at hp
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, K5Law.guard_some, Option.pure_def,
    Option.some.injEq] at hp
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, e⟩ := hp
  subst e
  exact ⟨rfl, rfl, rfl⟩

/-! ## 2 The fields that are made of challenges -/

/-- **The same named points and weights, as far as the parts in front of part number q make
them.** It is a definition. -/
structure PtsTo (x : OnBytes.Params.AttentionRounds) (q : Nat) (p p' : Pts) : Prop where
  key : KeySame p p'
  scR : ∀ i, i < q → ∀ k k', p.scores[i]? = some k → p'.scores[i]? = some k' → k.sc.r = k'.sc.r
  scE : iSE x < q → p.d.scE.r = p'.d.scE.r
  gam : iGam x < q → p.d.gam = p'.d.gam
  vpm : iVM x < q → p.d.vpm.r = p'.d.vpm.r
  wJv : iVM x < q → p.d.wJv = p'.d.wJv
  vpd : iVD x < q → p.d.vpd.r = p'.d.vpd.r
  tg : iZero x < q → p.x.tg = p'.x.tg
  ti : iZero x < q → p.x.ti = p'.x.ti
  scF : iSF x < q → p.x.scF.r = p'.x.scF.r
  scd : iSD x < q → p.x.scd.r = p'.x.scd.r
  scH : iHB x < q → p.x.scH.r = p'.x.scH.r

/-- A softmax-table unit's challenges, off what was heard. -/
theorem unit_chal {g : Geo} {zk : Array (Array E)} {h : Heard} {L : Left} {p : Pts}
    (hp : pointsOf g zk h L = some p) {i : Nat} {k : ScoreP} (hk : p.scores[i]? = some k) :
    ∃ u, h.scores[i]? = some u ∧ k.sc.r = chal u.2 := by
  have h1 := congrArg (fun l => l[i]?) (K5Law.chal_are (K5Law.points_are hp))
  simp only [List.getElem?_map, Array.getElem?_toList, hk, Option.map_some] at h1
  cases hu : h.scores[i]? with
  | none =>
    rw [hu] at h1
    cases h1
  | some u =>
    rw [hu] at h1
    exact ⟨u, rfl, Option.some.inj h1⟩

/-- **From the same challenges to the same named points and weights.** CONDITIONAL: the two values
heard hold the same challenges in front of part q; the lists of rows have one length; the function
returns at both. -/
theorem points_to {x : OnBytes.Params.AttentionRounds} {q : Nat} {g : Geo} {zk : Array (Array E)}
    {h h' : Heard} {L L' : Left} {p p' : Pts} (S : SameTo x q h h')
    (nL : L.scores.size = L'.scores.size) (hp : pointsOf g zk h L = some p)
    (hp' : pointsOf g zk h' L' = some p') : PtsTo x q p p' := by
  obtain ⟨p'', e, K⟩ := points_congr (L' := L') S.nR S.nS nL hp
  obtain rfl := Option.some.inj (e.symm.trans hp')
  have A := K5Law.points_are hp
  have A' := K5Law.points_are hp'
  obtain ⟨w, tg, ti⟩ := points_chal hp
  obtain ⟨w', tg', ti'⟩ := points_chal hp'
  exact
    { key := K
      scR := fun i hi k k' hk hk' => by
        obtain ⟨u, hu, e1⟩ := unit_chal hp hk
        obtain ⟨u', hu', e2⟩ := unit_chal hp' hk'
        rw [e1, e2, S.scores i hi u u' hu hu']
      scE := fun hq => by
        rw [A.scE, A'.scE]
        exact S.division hq
      gam := fun hq => by rw [A.gam, A'.gam, S.gam hq]
      vpm := fun hq => by
        rw [A.vpm, A'.vpm]
        exact S.below hq
      wJv := fun hq => by rw [w, w', S.below hq]
      vpd := fun hq => by
        rw [A.vpd, A'.vpd]
        exact S.on hq
      tg := fun hq => by rw [tg, tg', S.point hq]
      ti := fun hq => by rw [ti, ti', S.point hq]
      scF := fun hq => by
        rw [A.scF, A'.scF]
        exact S.atIndex hq
      scd := fun hq => by
        rw [A.scd, A'.scd]
        exact S.key hq
      scH := fun hq => by
        rw [A.scH, A'.scH]
        exact S.cells hq }

/-- The relation on what was heard, turned round. -/
theorem SameTo.symm {x : OnBytes.Params.AttentionRounds} {q : Nat} {a b : Heard}
    (S : SameTo x q a b) : SameTo x q b a :=
  { nR := S.nR.symm
    nS := S.nS.symm
    scores := fun i hi u v hu hv => (S.scores i hi v u hv hu).symm
    division := fun h => (S.division h).symm
    gam := fun h => (S.gam h).symm
    below := fun h => (S.below h).symm
    on := fun h => (S.on h).symm
    point := fun h => (S.point h).symm
    om := fun h => (S.om h).symm
    atIndex := fun h => (S.atIndex h).symm
    om' := fun h => (S.om' h).symm
    key := fun h => (S.key h).symm
    om'' := fun h => (S.om'' h).symm
    cells := fun h => (S.cells h).symm }

/-- **The prover's named points and weights are the verifier's**, field by field, as far as the
parts in front of part q make them. CONDITIONAL: hd, what the verifier heard, holds the prover's
challenges in these parts; both calls return: the prover's at its blank rows, the verifier's at its
own rows L and at the prover's key points. -/
theorem points_same (P : Pub5) {c : Chal} {q : Nat} {hd : Heard} {L : Left} {p₀ p : Pts}
    (S : SameTo P.x q hd (heardAt P c fun _ => none)) (hp₀ : ptsOf P c = some p₀)
    (hp : pointsOf P.g c.zk hd L = some p) : PtsTo P.x q p₀ p :=
  points_to S.symm
    ((K5Law.points_are (show pointsOf P.g c.zk _ _ = some p₀ from hp₀)).nL.symm.trans
      (K5Law.points_are hp).nL) hp₀ hp

/-! ## 3 The prover's own call, early and late -/

/-- **The prover's named points, early and late.** CONDITIONAL: the key points are the same words;
the challenges are one in the rounds in front of part q; the function returns at c. -/
theorem ptsOf_agree (P : Pub5) {c c' : Chal} {q : Nat} (hz : c.zk = c'.zk)
    (h : Agree (firstOf P.x q) c c') {p : Pts} (hp : ptsOf P c = some p) :
    ∃ p', ptsOf P c' = some p' ∧ PtsTo P.x q p p' := by
  have S := heardAt_agree P h
  unfold ptsOf ptsAt at hp ⊢
  rw [← hz]
  obtain ⟨p', e, _⟩ := points_congr (L' := blankLeft P.x.score.length) S.nR S.nS rfl hp
  exact ⟨p', e, points_to S rfl hp e⟩

/-- Where it refuses early it refuses late. -/
theorem ptsOf_none (P : Pub5) {c c' : Chal} (hz : c.zk = c'.zk) (hp : ptsOf P c = none) :
    ptsOf P c' = none := by
  cases h' : ptsOf P c' with
  | none => rfl
  | some p' =>
    obtain ⟨p, e, _⟩ :=
      ptsOf_agree P (q := 0) hz.symm (fun i hi => absurd hi (Nat.not_lt_zero i)) h'
    rw [hp] at e
    cases e

end H2K5.Honest

#print axioms H2K5.Honest.PointsIs.foldlM_rel
#print axioms H2K5.Honest.PointsIs.map_zip_congr
#print axioms H2K5.Honest.PointsIs.zip2_rel
#print axioms H2K5.Honest.PointsIs.fold_two
#print axioms H2K5.Honest.points_congr
#print axioms H2K5.Honest.points_chal
#print axioms H2K5.Honest.unit_chal
#print axioms H2K5.Honest.points_to
#print axioms H2K5.Honest.SameTo.symm
#print axioms H2K5.Honest.points_same
#print axioms H2K5.Honest.ptsOf_agree
#print axioms H2K5.Honest.ptsOf_none
