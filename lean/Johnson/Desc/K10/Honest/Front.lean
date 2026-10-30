-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K10/Honest/Front.lean: THE CLOSING OF A SEGMENT SAYS YES, FROM NAMED FACTS ON THE RECORD
IN FRONT OF IT. Theorems on the verifier's own text (the kind's block, `Close.kind`,
Johnson/Desc/First/Close/Kind.lean). It names no frame of an honest side.

What is said. `CloseFront P s x D` lists, one field for each guard that reads the record in front or
the plan (but for those that hold of the kind's entries at every plan), what must hold of the record
s at the element x that "BAT" draws; D holds the things of which the fields speak. From these facts,
at every list of 2 + k rounds of the kind's shape in which "BAT" drew x, the block's decision says
yes (`close_yes`). And each yes gives these facts at the element that "BAT" drew, and that there are
2 + k rounds of the kind's shape (`front_of_yes`). So the decision says yes JUST IF all this holds
(`close_yes_iff`): together they are enough, and each yes gives them all. (That no fact follows from
the others is not said.)

  `CloseData`      the link's shape and the group's record; the mask's number; what the beginning of
                   the test hands over and leaves; the record behind the spending of the mask; the
                   batched row
  `CloseFront`     the facts, each under its guard's name in Close/Closing.lean's head (`beginRun` and
                   `spendAsMask`: four clauses of the ground each; `spent`: that effect's result)
  `heard_made`, `rounds_made`   a round's guards, from its entry and its shape
  `close_yes`, `front_of_yes`, `close_yes_iff`   the theorems

By: `closeFrame_iff` (Johnson/Desc/First/Close/Law/CloseMeans.lean), whose proposition is opened;
`kind_decide_iff` (Law/KindDecide.lean).

Limits. OF THE BLOCK's DECISION (`Block.decide`) ALONE: a block's step (`Block.step`,
Johnson/Desc/Block.lean) asks two tests in front of it, on the rounds' format and on the columns:
Johnson/Desc/K10/Honest/Step.lean. TWO FIELDS READ x: `combine` and, through the batched row,
`rowfits`: that they hold at every element: Johnson/Desc/K10/Honest/RowFits.lean, Base.lean. Whether a
record that an honest run leaves meets the facts is not said. What the decision hands on is not said.
Nothing on soundness, completeness or hiding of the protocol.

-/
import Johnson.Desc.K10.Honest.YesFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.YesFree
open OnBytes VerifiableInference.Desc VerifiableInference.Desc.First.Close

/-- What the facts speak of. -/
structure CloseData where
  L : Params.ReqLink
  G : ReqGroup
  /-- the fresh mask's number -/
  m : Nat
  /-- the layout and the rows in their fixed order -/
  input : RunInput
  /-- the record behind the beginning of the test -/
  d : _root_.Desc.Plain.DState Unit
  /-- the record behind the spending of the mask -/
  d2 : _root_.Desc.Plain.DState Unit
  /-- the batched row -/
  row : GroupRow

/-- The shape of the fold, as `closeFrame` makes it. -/
def CloseData.F (D : CloseData) (s : Rec) : FoldShape :=
  ioppFoldShape { code := s.frame.shape.code, maskCode := s.frame.shape.maskCode, k := D.G.k,
                  h := D.G.h } D.input.layout

/-- **The facts in front of the closing**, at the element x that "BAT" draws. -/
structure CloseFront (P : Par) (s : Rec) (x : E) (D : CloseData) : Prop where
  owed : s.owed = none
  link : s.frame.shape.link[s.frame.link]? = some D.L
  group : s.frame.groups[s.frame.link]? = some D.G
  due : s.frame.next = .laterOrClose ∧ s.frame.moment = reqMoments D.L
  mask : s.frame.mask = some D.m
  beginRun : ∀ c ∈ Ground.beginRunL s.st s.frame.group, c.2 = true
  layout : Ground.beginRunP (onSt s.st) s.frame.group = some (D.input, D.d)
  rows : P.rows = D.input.rows.size
  combine : Own.batch D.d.st s.frame.group D.input x = some D.row
  kh : D.input.layout.k = D.G.k ∧ D.input.layout.h = D.G.h
  /-- the plan's side of K10.stretch: the block has as many rounds "FOLD round" as the group has row
  variables -/
  stretch : P.k = D.G.k
  shape : Own.foldShapeFits D.d.st (D.F s) = true
  maskfits : Own.foldMaskFits D.d.st (D.F s) D.m = true
  spendAsMask : ∀ c ∈ Ground.spendAsMaskL D.d.st D.m, c.2 = true
  spent : Ground.spendAsMaskP (onSt D.d.st) D.m = some D.d2
  rowfits : Own.foldRowFits D.d2.st (D.F s) D.row = true

/-- A round's guards, from its entry and its shape. -/
theorem heard_made {name : String} {items : Nat} {e : Fmt.Entry} {r : Fmt.RoundView} (h1 : e.name = name)
    (h2 : e.drawNZ = 0)
    (h3 : e.count = 1 ∧ e.msg = 24 * items + 32 * 0 ∧ e.roots = 0 ∧ e.answers = 0 ∧ e.poss = 0 ∧
      e.trits = 0) (h4 : e.drawE = 1) (hs : Shaped items r) :
    ∃ xs x, HeardMeans name items e r 0 xs x ∧ xs.length = items ∧
      ∀ t, r.drawn.elems = [t] → x = E.ofTriple t := by
  obtain ⟨⟨ys, hv, hl⟩, ⟨t', ht'⟩, hp, hq⟩ := hs
  refine ⟨ys.map E.ofTriple, E.ofTriple t', ⟨h1, h2, h3, ?_, ⟨?_, ?_, ?_⟩, ?_, t', ht', rfl⟩, ?_, ?_⟩
  · rw [hv, List.length_map, hl]
  · rw [ht', h4]; rfl
  · rw [hp, h3.2.2.2.2.1]; rfl
  · rw [hq, h3.2.2.2.2.2]; rfl
  · rw [hv, elemsOf_map]
  · rw [List.length_map, hl]
  · intro t ht
    rw [ht'] at ht
    rw [(List.cons.inj ht).1]

/-- The rounds "FOLD round", from their shape. -/
theorem rounds_made (e : Fmt.Entry) (h1 : e.name = "FOLD round") (h2 : e.drawNZ = 0)
    (h3 : e.count = 1 ∧ e.msg = 24 * 2 + 32 * 0 ∧ e.roots = 0 ∧ e.answers = 0 ∧ e.poss = 0 ∧
      e.trits = 0) (h4 : e.drawE = 1) : ∀ (n : Nat) (rs : List Fmt.RoundView) (claim : E),
    rs.length = n → (∀ r ∈ rs, Shaped 2 r) →
    ∃ gs cl, RoundsMeans (List.replicate n e) rs claim gs cl
  | 0, [], claim, _, _ => ⟨[], claim, rfl, rfl⟩
  | 0, _ :: _, _, hl, _ => by simp at hl
  | _ + 1, [], _, hl, _ => by simp at hl
  | n + 1, r :: rs, claim, hl, hs => by
    obtain ⟨xs, g, hh, hlen, _⟩ := heard_made h1 h2 h3 h4 (hs r (List.mem_cons_self ..))
    obtain ⟨a, b, rfl⟩ : ∃ a b, xs = [a, b] := List.length_eq_two.1 hlen
    obtain ⟨gs, cl, h⟩ := rounds_made e h1 h2 h3 h4 n rs (foldClaimRound claim a b g)
      (Nat.succ.inj hl) fun q hq => hs q (List.mem_cons_of_mem _ hq)
    exact ⟨g :: gs, cl, a, b, g, gs, hh, h, rfl⟩

/-- The first of the kind's three entries (`entries`, Johnson/Desc/First/Close/Kind.lean). -/
def eBat (P : Par) : Fmt.Entry :=
  { name := "BAT", work := P.workField, drawE := 1, rows := P.rows }
/-- The second. -/
def eEps (P : Par) : Fmt.Entry :=
  { name := "FOLD epsilon", work := P.workField, msg := 24, drawE := 1 }
/-- The third, k times. -/
def eRound (P : Par) : Fmt.Entry :=
  { name := "FOLD round", work := P.workClose, msg := 48, drawE := 1 }

theorem entries_eq (P : Par) : entries P = eBat P :: eEps P :: List.replicate P.k (eRound P) := rfl

/-- **FROM THE FACTS IN FRONT THE BLOCK's DECISION SAYS YES**, at every list of 2 + k rounds of the kind's
shape in which "BAT" drew x. -/
theorem close_yes {Cl : Type} {P : Par} {s : Rec} {x : E} {D : CloseData}
    (H : CloseFront P s x D) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64)))
    (hl : rs.length = 2 + P.k) (hs : ShapedAll rs) (t : Fmt.Ext) (hb : batDraw rs = [t])
    (hx : x = E.ofTriple t) : ∃ s', ((kind (Cl := Cl)) P).decide s rs gs = .ok s' := by
  match rs, hl, hs, hb with
  | rB :: rE :: rR, hl, ⟨t1, t2, t3⟩, hb =>
    obtain ⟨xs, x', u1, _, u3⟩ :=
      heard_made (e := eBat P) rfl rfl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl t1
    have hx' : x' = x := (u3 t (by simpa [batDraw] using hb)).trans hx.symm
    subst hx'
    obtain ⟨ys, eps, v1, vl, _⟩ :=
      heard_made (e := eEps P) rfl rfl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl t2
    obtain ⟨sum, rfl⟩ : ∃ a, ys = [a] := List.length_eq_one_iff.1 vl
    have hlen : rR.length = P.k := by simp at hl; omega
    obtain ⟨gamma, claim, w⟩ := rounds_made (eRound P) rfl rfl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl
      P.k rR (maddE sum eps D.row.target) hlen t3
    refine ⟨_, (kind_decide_iff P s _ _ gs).2 ⟨(_, _), (closeFrame_iff _ _ _ _ _ _ _).2
      ⟨H.owed, D.L, H.link, D.G, H.group, H.due, _, ⟨eBat P, _, rB, _, entries_eq P, rfl, D.m,
        H.mask, D.row,
        D.input.layout, D.d.st, ⟨H.beginRun, D.input, D.d, H.layout, xs, x', u1, H.rows, H.combine,
          rfl, rfl⟩, H.kh, eEps P, _, rE, rR, rfl, rfl, ⟨?_, ?_⟩, ?_, H.shape, H.maskfits,
        H.spendAsMask, D.d2, H.spent, sum, eps, v1, H.rowfits, gamma, claim, w, rfl, rfl⟩, rfl⟩,
      rfl⟩⟩
    · rw [List.length_replicate]; exact H.stretch
    · exact hlen.trans H.stretch
    · intro e he
      rcases List.mem_cons.1 he with rfl | he
      · rfl
      · rw [List.eq_of_mem_replicate he]; rfl

/-- Items that are all elements of the extension field. -/
theorem elems_shape : ∀ (vs : List Fmt.ItemValue) (xs : List E), First.Close.elemsOf vs = some xs →
    ∃ ys : List Fmt.Ext, vs = ys.map Fmt.ItemValue.e
  | [], _, _ => ⟨[], rfl⟩
  | v :: vs, xs, h => by
    unfold First.Close.elemsOf at h
    rw [List.mapM_cons] at h
    obtain ⟨b, hb, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨bs, hbs, _⟩ := Option.bind_eq_some_iff.1 h2
    obtain ⟨ys, hy⟩ := elems_shape vs bs hbs
    cases v with
    | e y => exact ⟨y :: ys, by rw [hy]; rfl⟩
    | _ => cases hb

/-- A round that passes its guards has the shape. -/
theorem shaped_of_heard {name : String} {items : Nat} {e : Fmt.Entry} {r : Fmt.RoundView} {xs : List E}
    {x : E} (h : HeardMeans name items e r 0 xs x) : Shaped items r := by
  obtain ⟨_, _, h3, h4, ⟨_, d2, d3⟩, h6, t, ht, _⟩ := h
  obtain ⟨ys, hy⟩ := elems_shape _ _ h6
  refine ⟨⟨ys, hy, ?_⟩, ⟨t, ht⟩, List.eq_nil_of_length_eq_zero (d2.trans h3.2.2.2.2.1),
    List.eq_nil_of_length_eq_zero (d3.trans h3.2.2.2.2.2)⟩
  rw [hy, List.length_map] at h4
  exact h4

/-- The rounds "FOLD round" that pass their guards have the shape, and are as many as the entries. -/
theorem rounds_shape : ∀ (es : List Fmt.Entry) (rs : List Fmt.RoundView) (claim : E) (gs : List E)
    (cl : E), RoundsMeans es rs claim gs cl → (∀ r ∈ rs, Shaped 2 r) ∧ rs.length = es.length
  | [], [], _, _, _, _ => ⟨fun _ h => (List.not_mem_nil h).elim, rfl⟩
  | e :: es, r :: rs, claim, gs, cl, h => by
    obtain ⟨c0, c2, g, gs', hh, hr, _⟩ := h
    obtain ⟨i1, i2⟩ := rounds_shape es rs _ gs' cl hr
    refine ⟨fun q hq => ?_, by rw [List.length_cons, List.length_cons, i2]⟩
    rcases List.mem_cons.1 hq with rfl | c
    · exact shaped_of_heard hh
    · exact i1 q c
  | [], _ :: _, _, _, _, h => h.elim
  | _ :: _, [], _, _, _, h => h.elim

/-- **EACH YES GIVES THE FACTS, AT THE ELEMENT THAT "BAT" DREW, AND THE ROUNDS' SHAPE AND NUMBER.** -/
theorem front_of_yes {Cl : Type} {P : Par} {s s' : Rec} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : ((kind (Cl := Cl)) P).decide s rs gs = .ok s') :
    ∃ t D, batDraw rs = [t] ∧ CloseFront P s (E.ofTriple t) D ∧ rs.length = 2 + P.k ∧
      ShapedAll rs := by
  obtain ⟨y, hy, _⟩ := (kind_decide_iff P s s' rs gs).1 h
  obtain ⟨k1, L, k2, G, k3, k4, rows, hc, _⟩ := (closeFrame_iff _ _ _ _ _ y.1 y.2).1 hy
  obtain ⟨eB, es₁, rB, rs₁, e1, rfl, m, hm, row, Ly, S1, hbat, hkh, hfold⟩ := hc
  obtain ⟨b1, input, d, b2, xs, x, b3, b4, b5, rfl, rfl⟩ := hbat
  obtain ⟨eE, eR, rE, rR, e2, rfl, ⟨s1, _⟩, _, f3, f4, f5, d2, f6, _, _, f7, f8, _, _, f9, _⟩ := hfold
  obtain ⟨rfl, rfl⟩ := List.cons.inj e1
  obtain ⟨rfl, rfl⟩ := List.cons.inj e2
  obtain ⟨t, ht, rfl⟩ := b3.2.2.2.2.2.2
  obtain ⟨r1, r2⟩ := rounds_shape _ _ _ _ _ f9
  refine ⟨t, ⟨L, G, m, input, d, d2, row⟩, by simp [batDraw, ht], ⟨k1, k2, k3, k4, hm, b1, b2, b4, b5,
    hkh, (List.length_replicate ..).symm.trans s1, f3, f4, f5, f6, f8⟩, ?_,
    shaped_of_heard b3, shaped_of_heard f7, r1⟩
  rw [List.length_cons, List.length_cons, r2, List.length_replicate]
  omega

/-- **THE BLOCK's DECISION SAYS YES JUST IF** there are 2 + k rounds of the kind's shape and the facts
hold at the element that "BAT" drew. -/
theorem close_yes_iff {Cl : Type} (P : Par) (s : Rec) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) :
    (∃ s', ((kind (Cl := Cl)) P).decide s rs gs = .ok s') ↔
      rs.length = 2 + P.k ∧ ShapedAll rs ∧
        ∃ t D, batDraw rs = [t] ∧ CloseFront P s (E.ofTriple t) D :=
  ⟨fun ⟨_, h⟩ => by
    obtain ⟨t, D, a, b, c, d⟩ := front_of_yes h
    exact ⟨c, d, t, D, a, b⟩,
   fun ⟨hl, hs, t, _, hb, H⟩ => close_yes H rs gs hl hs t hb rfl⟩

end ProofFile.Honest.K10.YesFree

#print axioms ProofFile.Honest.K10.YesFree.entries_eq
#print axioms ProofFile.Honest.K10.YesFree.heard_made
#print axioms ProofFile.Honest.K10.YesFree.rounds_made
#print axioms ProofFile.Honest.K10.YesFree.close_yes
#print axioms ProofFile.Honest.K10.YesFree.front_of_yes
#print axioms ProofFile.Honest.K10.YesFree.close_yes_iff
