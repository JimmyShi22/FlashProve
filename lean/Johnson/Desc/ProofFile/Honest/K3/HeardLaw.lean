-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/HeardLaw.lean: the honest side of the kind "lookup" (K3):
conditional (at a lookup with one part of keys): where the verifier's hearing of a lookup's rounds
returns, the points that it hands back are those that Honest/K3/Heard.lean makes of the same rounds'
challenges, found by number. Theorems. Of the definitions `PointsAgree` is the statement; the others
serve the proofs here, and many of them stand in other files of this folder too: the readers `one`,
`seg`, `many` and `e1`; `lastPt`, `allOf`; the row's stretches (`blkA`, `ties`, `preKey` and their
like) and the numbers of rounds in front (`oAlpha` to `oEnd`).

Terms. Honest/K3/GLOSSARY.md ("points", "key point", "base"). In this file: the verifier's hearing
is `hearV`, over `messagesV` (both Johnson/Desc/First/Look/Via/Rounds.lean); what it hands back is
the structure `HeardV`. "JOIN" and "ZERO" are the plan's names of rounds of a lookup.

What is shown.
  `PointsAgree f g base heard`: what is said: six equations between the fields of `HeardV` and four
    definitions of Heard.lean: `ptsOf`, `leavesR`, `bitsR`, `varsAt`.
  `pointsAgree_of_hearV`: `PointsAgree` from `hearV f F rs = some (g, G)`, at f.parts = [v], at the
    list front ++ (the rounds' challenges) ++ back and base := the length of front: any rounds in
    front and behind.
  `keyPtsAt_of_hearVia`: at a proof file's link: the structure that `hearVia`
    (Johnson/Desc/First/Look/Via/Via.lean) makes has the zx, zy and zk of `keyPtsAt`.
  `withPoints_varsAt`: at every face that passes the verifier's tests, whatever its parts: at every
    sumcheck of the row the stage's shape with
    `pointsAt` laid in is `varsAt`: the list of variables that the verifier's text makes at these
    points.
  `varsAt_prefix`: at f.parts = [v]: `varsAt` at a stage reads the challenges in front of the stage
    alone.

Hypotheses that remain.
  `hp`: f.parts = [v]: one part of keys (in all but `withPoints_varsAt`).
  `h`: the return of the hearing (`hearV`, or `hearVia` in `keyPtsAt_of_hearVia`, where `hs` says
    that the place has a shape).
  `hok`, `hs`, `hk`: (in `withPoints_varsAt`, and in `blank_varsAt` beneath it; `hok` in
    `order_len`) the face passes the verifier's tests (`Face.ok`); the stage is one of the row's (so
    in `varsAt_prefix` too); its call is k.
  `hlen`: (in `keyPt_all`, `tabPt_all`, `rhoT_all`, `zeroPt_all`; it comes in, with `hp`, through a
    `variable`) there are as many rounds as the lookup takes: oEnd f v ≤ rs.length. Beside it there:
    `hm`, `hl` (the level is in range: m ≤ v, l ≤ f.d), `hj`, `hz` (the rounds "JOIN" and "ZERO"
    sample as many elements as are read).
  `hpl`: (in `walk`) two planes at least.
  The helpers' hypotheses, as listed from their statements: ranges and small equations on numbers
    and lists; that the piece of the verifier's text in question returns; `Cuts` of a text's parts;
    that a stage is none of certain others.
Can the hypothesis on the return be met? Honest/K3/HeardGuards.lean [not in this library]: `hearV`
returns at two synthetic faces with one part, one of them `faceOf` at a shape (`heardV.isSome`,
`(recordOf dr₁).isSome`), by evaluation.

How the proof goes. 1: three readers on rounds (`one`, `seg`, `many`) and what `elemAt`, `varChals`,
`drawsAt` are in them. 2: each piece of the verifier's text cuts just its rounds and hands back just
these samples, over the library's `hear_spec` and `readAll_spec`
(Johnson/Desc/Part/MaskedSumShape.lean), `whole_parts` (Johnson/Desc/Part/MaskedSumKeeps.lean),
`level_spec` (Johnson/Desc/First/ProdV/LevelKit.lean), `turn_spec` and `run_succ_spec`
(Johnson/Desc/First/ProdV/Facts.lean). 3: the walk through `messagesV`. 4: `firstRound` at the
stages that are read, as sums. 5: the two together. 6: the two theorems on `varsAt`.

Users. `pointsAgree_of_hearV` is called in Honest/K3/Law/HeardWholeLaw.lean,
Honest/K3/Law/LookLeftOf.lean and Honest/K3/Law/Top.lean; `withPoints_varsAt` and `varsAt_prefix` in
Honest/K3/Law/Walk.lean. `keyPt_all`, `tabPt_all`, `rhoT_all` and `zeroPt_all` are called in
Honest/K3/Law/LookHeard.lean, `level_seg` in Honest/K3/Parts/NamesMarks.lean; the head of
Honest/K3/Law/Forward.lean names `level_seg` as what its theorems mirror. The readers `one`, `seg`
and `many` stand in statements of files under Honest/K3/Law/ and Honest/K3/Good/.

Limits. One part of keys: all lookups of a proof file's links are such (`faceOf`); a key file's are
not. Not said: anything of the point of "JOIN" or of "ZERO" (`rhoT`, `zeroPt`) by itself, or of the
points between the levels: `HeardV` holds none of these. That the verifier's text hears each
sumcheck at `varsAt` of these points is not shown here: `varsAt` calls the verifier's makers of
variables by name, and `level_seg`, `keyPt_all`, `tabPt_all`, `rhoT_all` and `zeroPt_all` are there
for whoever walks the course. Shown in part: Honest/K3/Law/LookHeard.lean (`lookHeard_of_steps`):
the verifier's hearing returns on a course's rounds, and what it heard is the run's; at one part of
keys, and conditional on `StageStep`, `LeavesStep`, `Cut`, `Fit` and the invariant in front. By that
file's head, not by the theorem's statement: along the way of the proof each piece of `messagesV` is
heard at the stage's call in the run, which is the stage's shape with `varsAt` at these points
(`walk_call_eq`, Honest/K3/Law/Walk.lean). Nothing is said of what was sent.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Heard
import Johnson.Desc.First.Look.Via.Via
import Johnson.Desc.First.Link.Law.LooksVia
import Johnson.Desc.First.ProdV.Facts
import Johnson.Desc.Part.MaskedSumShape
import Johnson.Desc.Part.MaskedSumKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes (E zeroE)
open OnBytes.Model (Fork Aff orderDefault)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.K3 (HeardV hearV messagesV Hr drawsV drawV sumV openV tieV partsV
  keysV
  noVar leafVars bitsCall)
open VerifiableInference.Desc.First.ProdV (layBack levelVars stepDown LevelOut level turn Carried
  level_spec turn_spec run_zero run_succ_spec levelEnds)
open VerifiableInference.Desc.LinkJoin.ViaL (bindHr_some)

/-- **The points that the verifier's hearing hands back are those made of the challenges by
number.** Here g is what was heard; base and heard are as `ptsOf` takes them. -/
structure PointsAgree (f : LFace) (g : HeardV) (base : Nat) (heard : List Fmt.Drawn) : Prop where
  theta : g.theta = (ptsOf f base heard).theta
  alpha : g.alpha = (ptsOf f base heard).alpha
  /-- each part's key tree's last point -/
  keys : g.keys.map (·.1) = f.parts.zipIdx.map fun x => (ptsOf f base heard).keyPt x.2 x.1
  zb0 : g.zb0 = leavesR f base heard
  zb1 : g.zb1 = bitsR f base heard
  /-- the leaves' variables, as the masked sumcheck's own structure keeps them -/
  leaves : g.leaves.vars = varsAt f .leaves (ptsOf f base heard)

/-! ## 1 Three readers on rounds -/

/-- The first element that a round sampled; 0 where it sampled none. -/
def e1 (r : Fmt.RoundView) : E := (r.drawn.elems.map E.ofTriple).headD zeroE

/-- The first element that round number a sampled. -/
def one (rs : List Fmt.RoundView) (a : Nat) : E := (rs.map e1).getD a zeroE

/-- The first elements of the n rounds from number a on. -/
def seg (rs : List Fmt.RoundView) (a n : Nat) : List E := ((rs.map e1).drop a).take n

/-- All elements that round number a sampled. -/
def many (rs : List Fmt.RoundView) (a : Nat) : List E :=
  ((rs[a]?).map fun r => r.drawn.elems.map E.ofTriple).getD []

theorem one_drop (rs : List Fmt.RoundView) (k a : Nat) : one (rs.drop k) a = one rs (k + a) := by
  simp [one, List.getD_eq_getElem?_getD, List.getElem?_drop]

theorem seg_drop (rs : List Fmt.RoundView) (k a n : Nat) : seg (rs.drop k) a n = seg rs (k + a) n := by
  simp [seg, List.map_drop, List.drop_drop]

theorem many_drop (rs : List Fmt.RoundView) (k a : Nat) : many (rs.drop k) a = many rs (k + a) := by
  simp [many, List.getElem?_drop]

theorem seg_take (rs : List Fmt.RoundView) (m a n : Nat) (h : a + n ≤ m) :
    seg (rs.take m) a n = seg rs a n := by
  simp only [seg, List.map_take, List.drop_take, List.take_take]
  congr 1
  omega

theorem drop_cons {α : Type} : ∀ {l : List α} {k : Nat} {x : α} {rest : List α},
    l.drop k = x :: rest → rest = l.drop (k + 1) ∧ k < l.length ∧ l[k]? = some x
  | [], k, x, rest, h => by simp at h
  | y :: l, 0, x, rest, h => by
    simp only [List.drop_zero, List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | y :: l, k + 1, x, rest, h => by
    simp only [List.drop_succ_cons] at h
    obtain ⟨a, b, c⟩ := drop_cons h
    refine ⟨by simpa using a, by simpa using b, by simpa using c⟩

theorem one_of_get {rs : List Fmt.RoundView} {a : Nat} {r : Fmt.RoundView} (h : rs[a]? = some r) :
    one rs a = e1 r := by
  simp [one, List.getD_eq_getElem?_getD, h]

theorem range_getD (l : List E) : (List.range l.length).map (fun j => l.getD j zeroE) = l := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]

theorem seg_eq_range (rs : List Fmt.RoundView) (a n : Nat) (h : a + n ≤ rs.length) :
    (List.range n).map (fun l => one rs (a + l)) = seg rs a n := by
  have hL : a + n ≤ (rs.map e1).length := by simpa using h
  simp only [seg, one]
  generalize rs.map e1 = L at hL
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_take, List.length_drop]
    omega
  · intro i h1 h2
    have hi : i < n := by simpa using h1
    have hb : a + i < L.length := by omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb]

/-- The list of all challenges: some in front, the rounds', some behind. -/
def allOf (front : List Fmt.Drawn) (rs : List Fmt.RoundView) (back : List Fmt.Drawn) : List Fmt.Drawn :=
  front ++ rs.map (·.drawn) ++ back

theorem allOf_get (front back : List Fmt.Drawn) (rs : List Fmt.RoundView) (a : Nat) (h : a < rs.length) :
    (allOf front rs back)[front.length + a]? = (rs[a]?).map (·.drawn) := by
  unfold allOf
  rw [List.append_assoc, List.getElem?_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left, List.getElem?_append_left (by simpa using h), List.getElem?_map]

theorem elemsAt_all (front back : List Fmt.Drawn) (rs : List Fmt.RoundView) (a : Nat)
    (h : a < rs.length) : elemsAt (allOf front rs back) (front.length + a) = many rs a := by
  unfold elemsAt many
  rw [allOf_get front back rs a h]
  cases rs[a]? <;> rfl

theorem elemAt_all (front back : List Fmt.Drawn) (rs : List Fmt.RoundView) (a : Nat)
    (h : a < rs.length) : elemAt (allOf front rs back) (front.length + a) = one rs a := by
  unfold elemAt
  rw [elemsAt_all front back rs a h, one_of_get (List.getElem?_eq_getElem h)]
  simp [many, e1, List.getElem?_eq_getElem h]

theorem varChals_all (f : LFace) (front back : List Fmt.Drawn) (rs : List Fmt.RoundView) (s : Stage)
    (k n : Nat) (hk : firstRound f s = k) (h : k + 1 + n ≤ rs.length) :
    varChals f front.length (allOf front rs back) s n = seg rs (k + 1) n := by
  rw [← seg_eq_range rs (k + 1) n h]
  unfold varChals roundAt
  apply List.map_congr_left
  intro l hl
  have hl' : l < n := by simpa using hl
  rw [hk, Nat.add_assoc, Nat.add_assoc, elemAt_all front back rs _ (by omega), Nat.add_assoc]

theorem drawsAt_all (front back : List Fmt.Drawn) (rs : List Fmt.RoundView) (a n : Nat)
    (h : a < rs.length) (hn : (many rs a).length = n) :
    drawsAt (allOf front rs back) (front.length + a) n = many rs a := by
  unfold drawsAt
  rw [elemsAt_all front back rs a h, ← hn]
  exact range_getD _

/-! ## 2 Each piece cuts just its rounds and hands back just these samples -/

variable {α β γ : Type}

local notation "vRoundsOf" => VerifiableInference.Desc.K3.roundsOf
local notation "vRun" => VerifiableInference.Desc.First.ProdV.run

/-- Wherever x returns it has taken just n rounds off the front. -/
structure Cuts (x : Hr α) (n : Nat) : Prop where
  cut : ∀ {F G : Fork} {rs rest : List Fmt.RoundView} {a : α}, x F rs = some (a, G, rest) →
    rest = rs.drop n ∧ n ≤ rs.length

theorem Cuts.bind {x : Hr α} {f : α → Hr β} {n m : Nat} (hx : Cuts x n) (hf : ∀ a, Cuts (f a) m) :
    Cuts (x >>= f) (n + m) := by
  refine ⟨?_⟩
  intro F G rs rest b h
  obtain ⟨a, G1, r1, h1, h2⟩ := bindHr_some h
  obtain ⟨q1, l1⟩ := hx.cut h1
  obtain ⟨q2, l2⟩ := (hf a).cut h2
  subst q1
  rw [List.length_drop] at l2
  refine ⟨?_, by omega⟩
  rw [q2]
  simp [List.drop_drop]

theorem cuts_pure (a : α) : Cuts (pure a : Hr α) 0 := by
  refine ⟨?_⟩
  intro F G rs rest b h
  have h' : some (a, F, rs) = some (b, G, rest) := h
  cases h'
  simp

theorem cuts_slot : Cuts Hr.slot 0 := by
  refine ⟨?_⟩
  intro F G rs rest b h
  have h' : some (F.next, F, rs) = some (b, G, rest) := h
  cases h'
  simp

theorem cuts_owe (what : String) : Cuts (Hr.owe what) 0 := by
  refine ⟨?_⟩
  intro F G rs rest b h
  have h' : some ((F.owe what).1, (F.owe what).2, rs) = some (b, G, rest) := h
  cases h'
  simp

theorem cuts_must (c : Bool) : Cuts (Hr.must c) 0 := by
  refine ⟨?_⟩
  intro F G rs rest b h
  unfold Hr.must at h
  split at h
  · cases h
    simp
  · exact nomatch h

theorem cuts_foldlM {f : β → γ → Hr β} {c : Nat} (hf : ∀ s a, Cuts (f s a) c) :
    ∀ (l : List γ) (s : β), Cuts (l.foldlM f s) (c * l.length)
  | [], s => by
    show Cuts (pure s : Hr β) (c * 0)
    exact cuts_pure s
  | a :: l, s => by
    show Cuts (f s a >>= fun s' => l.foldlM f s') (c * (l.length + 1))
    rw [Nat.mul_succ, Nat.add_comm]
    exact Cuts.bind (hf s a) fun s' => cuts_foldlM hf l s'

/-- A round of samples. -/
theorem drawsV_spec {n : Nat} {F G : Fork} {rs rest : List Fmt.RoundView} {x : Array E}
    (h : drawsV n F rs = some (x, G, rest)) :
    rest = rs.drop 1 ∧ 1 ≤ rs.length ∧ x.toList = many rs 0 ∧ x.size = n := by
  unfold drawsV at h
  cases rs with
  | nil => exact nomatch h
  | cons r rs' =>
    dsimp only at h
    split at h
    · obtain ⟨y, hy, e⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨y1, y2⟩ := y
      obtain ⟨_, _, s3, s4⟩ := MaskedSum.roundOf_spec hy
      simp only [Prod.mk.injEq] at e
      obtain ⟨e1', e2', e3'⟩ := e
      subst e1' e2' e3'
      refine ⟨by simp, by simp, ?_, ?_⟩
      · simp [many, s4]
      · simp [s4, s3]
    · exact nomatch h

theorem drawV_spec {F G : Fork} {rs rest : List Fmt.RoundView} {x : E}
    (h : drawV F rs = some (x, G, rest)) :
    rest = rs.drop 1 ∧ 1 ≤ rs.length ∧ x = one rs 0 := by
  unfold drawV at h
  split at h
  · rename_i y G' rest' hy
    obtain ⟨q, l, t, _⟩ := drawsV_spec hy
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨a1, a2, a3⟩ := h
      subst a1 a2 a3
      refine ⟨q, l, ?_⟩
      have hr : rs[0]? = some rs[0] := List.getElem?_eq_getElem (by omega)
      rw [one_of_get hr]
      have t' : y.toList = rs[0].drawn.elems.map E.ofTriple := by
        rw [t]
        simp [many, hr]
      unfold e1
      rw [← t']
      obtain ⟨l'⟩ := y
      cases l' <;> simp
    · exact nomatch h
  · exact nomatch h

/-- The challenges that were read are the rounds' first samples. -/
theorem varsRead_firsts : ∀ {vs : List MaskedSum.Var} {used : List Fmt.RoundView} {l : List (List E × E)},
    MaskedSum.VarsRead vs used l → l.map (·.2) = used.map e1
  | [], [], [], _ => rfl
  | _ :: _, r :: _, (_, g) :: _, h => by
    have ih := varsRead_firsts h.2
    have hg : [g] = r.drawn.elems.map E.ofTriple := h.1.2.2.2
    simp only [List.map_cons, ih, e1, ← hg, List.headD_cons]
  | [], [], _ :: _, h => h.elim
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim
  | _ :: _, _ :: _, [], h => h.elim

/-- A masked sumcheck with ends, on just its own rounds. -/
theorem whole_seg {C : Aff} {lead : Nat} {vs : List MaskedSum.Var} {e : MaskedSum.Ends}
    {endTerm : List E → List E → E} {F G : Fork} {rs : List Fmt.RoundView} {h : MaskedSum.Heard}
      {row : Aff}
    (hw : MaskedSum.whole C ⟨lead, vs, some e⟩ endTerm F rs = some (h, row, G)) :
    rs.length = vs.length + 3 ∧ h.r.take vs.length = seg rs 1 vs.length := by
  obtain ⟨_, G0, sh, _, hh, _, _⟩ := MaskedSum.whole_parts hw
  obtain ⟨_, T, R, _, hR, hrec, _⟩ := MaskedSum.hear_spec hh
  obtain ⟨r0, used, rv, front, a1, _, _, a4, _⟩ := MaskedSum.readAll_spec hR
  have hl : used.length = vs.length + 1 := by simpa using (MaskedSum.VarsRead.length a4).1
  have hf := varsRead_firsts a4
  subst a1
  refine ⟨by simp [hl], ?_⟩
  rw [hrec]
  show (R.rounds.map (·.2)).take vs.length = _
  rw [hf]
  simp only [seg, List.map_cons, List.map_append, List.drop_succ_cons, List.drop_zero]
  rw [List.take_append_of_le_length (by simp [hl])]

/-- A call without ends: what is read. -/
theorem readAll_none_spec {lead : Nat} {vs : List MaskedSum.Var} {rs : List Fmt.RoundView}
    {R : MaskedSum.Read} (h : MaskedSum.readAll ⟨lead, vs, none⟩ rs = some R) :
    ∃ r0 used, rs = r0 :: used ∧ MaskedSum.VarsRead vs used R.rounds := by
  unfold MaskedSum.readAll at h
  cases rs with
  | nil => cases h
  | cons r rest =>
    simp only at h
    split at h
    · rename_i x mu eps l h1 h2 h3
      have e := Option.some.inj h
      subst e
      obtain ⟨used, a1, a2⟩ := MaskedSum.varRounds_spec _ _ _ _ h2
      exact ⟨r, used, by rw [a1]; simp, a2⟩
    · rename_i h3
      cases h3
    · cases h

/-- A masked sumcheck without ends, on just its own rounds. -/
theorem hear_none_seg {C : Aff} {lead : Nat} {vs : List MaskedSum.Var} {F G : Fork}
    {rs : List Fmt.RoundView} {h : MaskedSum.Heard}
    (hh : MaskedSum.hear C ⟨lead, vs, none⟩ F rs = some (h, G)) :
    rs.length = vs.length + 1 ∧ h.r = seg rs 1 vs.length ∧ h.vars = vs := by
  obtain ⟨_, T, R, _, hR, hrec, _⟩ := MaskedSum.hear_spec hh
  obtain ⟨r0, used, a1, a4⟩ := readAll_none_spec hR
  have hl : used.length = vs.length := (MaskedSum.VarsRead.length a4).1
  have hf := varsRead_firsts a4
  subst a1
  refine ⟨by simp [hl], ?_, by rw [hrec]; rfl⟩
  rw [hrec]
  show R.rounds.map (·.2) = _
  rw [hf]
  simp only [seg, List.map_cons, List.drop_succ_cons, List.drop_zero]
  rw [← hl, ← List.length_map (f := e1), List.take_length]

theorem sumV_spec {C : Aff} {k : MaskedSum.Call} {endTerm : List E → List E → E} {F G : Fork}
    {rs rest : List Fmt.RoundView} {x : MaskedSum.Heard × Aff}
    (h : sumV C k endTerm F rs = some (x, G, rest)) :
    rest = rs.drop (vRoundsOf k) ∧ vRoundsOf k ≤ rs.length ∧
      x.1.r.take k.vs.length = seg rs 1 k.vs.length := by
  unfold sumV at h
  split at h
  · exact nomatch h
  · split at h
    · rename_i hd row G' hw
      split at h
      · exact nomatch h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨a1, a2, a3⟩ := h
        subst a1 a2 a3
        obtain ⟨e, _, _, he, _, _, _⟩ := MaskedSum.whole_parts hw
        obtain ⟨lead, vs, ends⟩ := k
        simp only at he
        subst he
        obtain ⟨b1, b2⟩ := whole_seg hw
        have hro : vRoundsOf ⟨lead, vs, some e⟩ = vs.length + 3 := by
          simp [VerifiableInference.Desc.K3.roundsOf]
        rw [hro] at b1 b2 ⊢
        rw [List.length_take] at b1
        refine ⟨rfl, by omega, ?_⟩
        rw [b2, seg_take _ _ _ _ (by omega)]
    · exact nomatch h

theorem cuts_sumV (C : Aff) (k : MaskedSum.Call) (endTerm : List E → List E → E) :
    Cuts (sumV C k endTerm) (vRoundsOf k) := ⟨fun h => ⟨(sumV_spec h).1, (sumV_spec h).2.1⟩⟩

theorem openV_spec {C : Aff} {vs : List MaskedSum.Var} {F G : Fork} {rs rest : List Fmt.RoundView}
    {x : MaskedSum.Heard} (h : openV C vs F rs = some (x, G, rest)) :
    rest = rs.drop (vs.length + 1) ∧ vs.length + 1 ≤ rs.length ∧ x.r = seg rs 1 vs.length ∧
      x.vars = vs := by
  unfold openV at h
  split at h
  · exact nomatch h
  · obtain ⟨y, hy, e⟩ := Option.map_eq_some_iff.1 h
    obtain ⟨hd, G'⟩ := y
    simp only [Prod.mk.injEq] at e
    obtain ⟨a1, a2, a3⟩ := e
    subst a1 a2 a3
    obtain ⟨b1, b2, b3⟩ := hear_none_seg hy
    rw [List.length_take] at b1
    refine ⟨rfl, by omega, ?_, b3⟩
    rw [b2, seg_take _ _ _ _ (by omega)]

/-- The tie: w - 1 sumchecks of three rounds. -/
theorem cuts_tieV (w : Nat) (a : E) (hw : 2 ≤ w) : Cuts (tieV w a) (3 * (w - 1)) := by
  have e : 3 * (w - 1) = 3 + (3 * (List.range (w - 2)).length + 0) := by
    rw [List.length_range]
    omega
  rw [e]
  unfold tieV
  refine Cuts.bind (cuts_sumV _ _ _) fun x => ?_
  refine Cuts.bind (cuts_foldlM (c := 3) (fun s _ => ?_) _ _) fun _ => cuts_pure _
  exact Cuts.bind (n := 3) (m := 0) (cuts_sumV _ _ _) fun _ => cuts_pure _

/-- How many rounds n levels take, from m0 variables up. -/
def K (m0 : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => K m0 n + (m0 + n + 4)

/-- One level. -/
theorem level_seg {m : Nat} {z : Array E} {order : List Nat} {C : Aff} {F G : Fork}
    {rs rest : List Fmt.RoundView} {o : LevelOut} (h : level m z order C F rs = some (o, G, rest)) :
    rest = rs.drop (m + 4) ∧ m + 4 ≤ rs.length ∧ o.r = layBack m order (seg rs 1 m) ∧
      o.xi = one rs (m + 3) := by
  obtain ⟨hd, line, s, hw, hdrop, hr, ho, _, _⟩ := level_spec h
  obtain ⟨d1, d2, d3⟩ := drop_cons hdrop
  obtain ⟨b1, b2⟩ := whole_seg (lead := 0) (vs := levelVars m z order) (e := levelEnds) hw
  have hlen : (levelVars m z order).length = order.length := by simp [levelVars]
  rw [hlen, List.length_take] at b1
  rw [hlen] at b2
  have hm : order.length = m := by omega
  rw [hm] at b2
  refine ⟨d1, by omega, ?_, ?_⟩
  · rw [ho, b2, seg_take _ _ _ _ (by omega)]
  · rw [one_of_get d3]
    have hx : [o.xi] = line.drawn.elems.map E.ofTriple := (MaskedSum.roundOf_spec hr).2.2.2
    simp [e1, ← hx]

/-- The point behind n levels that are heard from round number a on; z where there is none. -/
def lastPt (m0 : Nat) (orders : Nat → List Nat) (z : Array E) (rs : List Fmt.RoundView) (a : Nat) :
    Nat → Array E
  | 0 => z
  | n + 1 =>
    behind (m0 + n) (orders (m0 + n)) (seg rs (a + K m0 n + 1) (m0 + n))
      (one rs (a + K m0 n + (m0 + n + 3)))

/-- A run of levels. -/
theorem run_cuts {m0 : Nat} {orders : Nat → List Nat} {s : Carried} {F : Fork}
    {rs : List Fmt.RoundView} : ∀ {n : Nat} {c : Carried} {G : Fork} {rest : List Fmt.RoundView},
    vRun m0 n orders s F rs = some (c, G, rest) → rest = rs.drop (K m0 n) ∧ K m0 n ≤ rs.length
  | 0, c, G, rest, h => by
    rw [run_zero] at h
    cases h
    simp [K]
  | n + 1, c, G, rest, h => by
    obtain ⟨s1, F1, r1, h1, h2⟩ := run_succ_spec h
    obtain ⟨q, l⟩ := run_cuts h1
    obtain ⟨o, hl, _⟩ := turn_spec h2
    obtain ⟨a1, a2, _, _⟩ := level_seg hl
    subst q
    rw [List.length_drop] at a2
    refine ⟨?_, by simp only [K]; omega⟩
    rw [a1]
    simp [List.drop_drop, K]

theorem run_point {m0 : Nat} {orders : Nat → List Nat} {s : Carried} {F : Fork}
    {rs : List Fmt.RoundView} {n : Nat} {c : Carried} {G : Fork} {rest : List Fmt.RoundView}
    (h : vRun m0 n orders s F rs = some (c, G, rest)) :
    c.point = lastPt m0 orders s.point rs 0 n := by
  cases n with
  | zero =>
    rw [run_zero] at h
    cases h
    rfl
  | succ n =>
    obtain ⟨s1, F1, r1, h1, h2⟩ := run_succ_spec h
    obtain ⟨q, _⟩ := run_cuts h1
    obtain ⟨o, hl, hc⟩ := turn_spec h2
    obtain ⟨_, _, a3, a4⟩ := level_seg hl
    subst q
    rw [hc]
    show (stepDown o).1 = _
    rw [← behind_eq_stepDown _ _ _ o a3, a4, seg_drop, one_drop]
    simp [lastPt]

theorem lastPt_drop (m0 : Nat) (orders : Nat → List Nat) (z : Array E) (rs : List Fmt.RoundView)
    (a n : Nat) : lastPt m0 orders z (rs.drop a) 0 n = lastPt m0 orders z rs a n := by
  cases n with
  | zero => rfl
  | succ n => simp [lastPt, seg_drop, one_drop, Nat.add_assoc]

/-- One part's key tree. -/
theorem keysV_one {f : LFace} {v i : Nat} {C : Aff} {rows : Array Aff} {F G : Fork}
    {rs rest : List Fmt.RoundView} {a : Array Aff × List (Array E × Aff)}
    (h : keysV f [(v, i)] [C] rows F rs = some (a, G, rest)) :
    ∃ c, vRun 0 v (f.orders i) { rows := rows, point := #[], form := C } F rs = some (c, G, rest) ∧
      a.2 = [(c.point, c.form)] := by
  unfold keysV at h
  obtain ⟨k, G1, r1, h1, h⟩ := bindHr_some h
  obtain ⟨y, G2, r2, h2, h⟩ := bindHr_some h
  unfold keysV at h2
  have h2' : some ((k.rows, []), G1, r1) = some (y, G2, r2) := h2
  cases h2'
  have h' : some ((k.rows, [(k.point, k.form)]), G1, r1) = some (a, G, rest) := h
  cases h'
  exact ⟨k, h1, rfl⟩

/-! ## 4 `firstRound` at the stages of a lookup with one part, as sums -/

def ties (n : Nat) : List Stage := (List.range n).map Stage.tie
def keysL (n : Nat) : List Stage :=
  (List.range n).flatMap fun m => [Stage.key 0 m, Stage.keyLine 0 m]
def tabsL (n : Nat) : List Stage := (List.range n).flatMap fun l => [Stage.tab l, Stage.tabLine l]
def blkA (f : LFace) : List Stage := if f.shifted then [Stage.shift] else []
/-- The stages in front of JOIN; of the key level m; of the table's level l. -/
def preJoin (f : LFace) : List Stage := blkA f ++ (Stage.alpha :: ties (f.planes - 1))
def preKey (f : LFace) (m : Nat) : List Stage := preJoin f ++ (Stage.join :: keysL m)
def preTab (f : LFace) (v l : Nat) : List Stage := preKey f v ++ tabsL l

/-- The numbers of rounds in front. -/
def oAlpha (f : LFace) : Nat := if f.shifted then 1 else 0
def oJoin (f : LFace) : Nat := oAlpha f + 1 + 3 * (f.planes - 1)
def oKey (f : LFace) : Nat := oJoin f + 1
def oTab (f : LFace) (v : Nat) : Nat := oKey f + K 0 v
def oLeaves (f : LFace) (v : Nat) : Nat := oTab f v + K f.mu f.d
def oZero (f : LFace) (v : Nat) : Nat := oLeaves f v + (f.mu + f.d + 1)
def oBits (f : LFace) (v : Nat) : Nat := oZero f v + 1
def oEnd (f : LFace) (v : Nat) : Nat := oBits f v + (f.mu + f.d + 3)

theorem stages_one (f : LFace) (v : Nat) (hp : f.parts = [v]) :
    stages f = preTab f v f.d ++ [Stage.leaves, Stage.zero, Stage.bits] := by
  unfold stages
  rw [hp]
  simp [preTab, preKey, preJoin, blkA, ties, keysL, tabsL]

theorem ties_succ (n : Nat) : ties (n + 1) = ties n ++ [Stage.tie n] := by
  simp [ties, List.range_succ]

theorem keysL_succ (n : Nat) : keysL (n + 1) = keysL n ++ [Stage.key 0 n, Stage.keyLine 0 n] := by
  simp [keysL, List.range_succ, List.flatMap_append]

theorem tabsL_succ (n : Nat) : tabsL (n + 1) = tabsL n ++ [Stage.tab n, Stage.tabLine n] := by
  simp [tabsL, List.range_succ, List.flatMap_append]

theorem keysL_split {m v : Nat} (h : m < v) :
    ∃ post, keysL v = keysL m ++ (Stage.key 0 m :: Stage.keyLine 0 m :: post) := by
  induction v with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h1 | h1
    · obtain ⟨post, e⟩ := ih h1
      exact ⟨post ++ [Stage.key 0 n, Stage.keyLine 0 n], by rw [keysL_succ, e]; simp⟩
    · subst h1
      exact ⟨[], by rw [keysL_succ]⟩

theorem tabsL_split {l d : Nat} (h : l < d) :
    ∃ post, tabsL d = tabsL l ++ (Stage.tab l :: Stage.tabLine l :: post) := by
  induction d with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h1 | h1
    · obtain ⟨post, e⟩ := ih h1
      exact ⟨post ++ [Stage.tab n, Stage.tabLine n], by rw [tabsL_succ, e]; simp⟩
    · subst h1
      exact ⟨[], by rw [tabsL_succ]⟩

theorem rounds_tie (f : LFace) (s : Nat) : Stage.rounds f (.tie s) = 3 := by cases s <;> rfl

theorem rounds_key (f : LFace) (i m : Nat) : Stage.rounds f (.key i m) = m + 3 := by
  simp [Stage.rounds, Stage.call, levelCall, levelVars, VerifiableInference.Desc.K3.roundsOf]

theorem rounds_tab (f : LFace) (l : Nat) : Stage.rounds f (.tab l) = f.mu + l + 3 := by
  simp [Stage.rounds, Stage.call, levelCall, levelVars, VerifiableInference.Desc.K3.roundsOf]

theorem rounds_leaves (f : LFace) : Stage.rounds f .leaves = f.mu + f.d + 1 := by
  simp [Stage.rounds, Stage.call, leafVars, VerifiableInference.Desc.K3.roundsOf]

theorem rounds_bits (f : LFace) : Stage.rounds f .bits = f.mu + f.d + 3 := by
  simp [Stage.rounds, Stage.call, bitsCall, VerifiableInference.Desc.K3.roundsOf]

theorem sum_blkA (f : LFace) : ((blkA f).map (Stage.rounds f)).sum = oAlpha f := by
  unfold blkA oAlpha
  split <;> rfl

theorem sum_ties (f : LFace) : ∀ n, ((ties n).map (Stage.rounds f)).sum = 3 * n
  | 0 => rfl
  | n + 1 => by
    rw [ties_succ, List.map_append, List.sum_append, sum_ties f n]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, rounds_tie]
    omega

theorem sum_keysL (f : LFace) : ∀ n, ((keysL n).map (Stage.rounds f)).sum = K 0 n
  | 0 => rfl
  | n + 1 => by
    have e : Stage.rounds f (.keyLine 0 n) = 1 := rfl
    rw [keysL_succ, List.map_append, List.sum_append, sum_keysL f n]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, rounds_key, e, K]
    omega

theorem sum_tabsL (f : LFace) : ∀ n, ((tabsL n).map (Stage.rounds f)).sum = K f.mu n
  | 0 => rfl
  | n + 1 => by
    have e : Stage.rounds f (.tabLine n) = 1 := rfl
    rw [tabsL_succ, List.map_append, List.sum_append, sum_tabsL f n]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, rounds_tab, e, K]
    omega

theorem sum_preJoin (f : LFace) : ((preJoin f).map (Stage.rounds f)).sum = oJoin f := by
  have e : Stage.rounds f .alpha = 1 := rfl
  unfold preJoin oJoin
  rw [List.map_append, List.sum_append, sum_blkA, List.map_cons, List.sum_cons, sum_ties, e]
  omega

theorem sum_preKey (f : LFace) (m : Nat) :
    ((preKey f m).map (Stage.rounds f)).sum = oKey f + K 0 m := by
  have e : Stage.rounds f .join = 1 := rfl
  unfold preKey oKey
  rw [List.map_append, List.sum_append, sum_preJoin, List.map_cons, List.sum_cons, sum_keysL, e]
  omega

theorem sum_preTab (f : LFace) (v l : Nat) :
    ((preTab f v l).map (Stage.rounds f)).sum = oTab f v + K f.mu l := by
  unfold preTab oTab
  rw [List.map_append, List.sum_append, sum_preKey, sum_tabsL]

theorem firstRound_split (f : LFace) (s : Stage) (pre post : List Stage)
    (h : stages f = pre ++ s :: post) (hn : s ∉ pre) :
    firstRound f s = (pre.map (Stage.rounds f)).sum := by
  have hi : (pre ++ s :: post).idxOf s = pre.length := by simp [List.idxOf_append, hn]
  unfold firstRound indexOf
  rw [h, hi, List.take_left']
  rfl

theorem notMem_blkA {f : LFace} {s : Stage} (h : s ≠ .shift) : s ∉ blkA f := by
  unfold blkA
  split <;> simp [h]

theorem notMem_ties {s : Stage} {n : Nat} (h : ∀ j, s ≠ .tie j) : s ∉ ties n := by
  intro hm
  obtain ⟨j, _, e⟩ := List.mem_map.1 hm
  exact h j e.symm

theorem notMem_keysL {s : Stage} {n : Nat} (h1 : ∀ j, j < n → s ≠ .key 0 j)
    (h2 : ∀ j, j < n → s ≠ .keyLine 0 j) : s ∉ keysL n := by
  intro hm
  obtain ⟨x, hx, hh⟩ := List.mem_flatMap.1 hm
  have hx' := List.mem_range.1 hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with e | e
  · exact h1 x hx' e
  · exact h2 x hx' e

theorem notMem_tabsL {s : Stage} {n : Nat} (h1 : ∀ j, j < n → s ≠ .tab j)
    (h2 : ∀ j, j < n → s ≠ .tabLine j) : s ∉ tabsL n := by
  intro hm
  obtain ⟨x, hx, hh⟩ := List.mem_flatMap.1 hm
  have hx' := List.mem_range.1 hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with e | e
  · exact h1 x hx' e
  · exact h2 x hx' e

theorem notMem_preJoin {f : LFace} {s : Stage} (h0 : s ≠ .shift) (h1 : s ≠ .alpha)
    (h2 : ∀ j, s ≠ .tie j) : s ∉ preJoin f := by
  unfold preJoin
  simp only [List.mem_append, List.mem_cons, not_or]
  exact ⟨notMem_blkA h0, h1, notMem_ties h2⟩

theorem notMem_preKey {f : LFace} {s : Stage} {m : Nat} (h0 : s ≠ .shift) (h1 : s ≠ .alpha)
    (h2 : ∀ j, s ≠ .tie j) (h3 : s ≠ .join) (h4 : ∀ j, j < m → s ≠ .key 0 j)
    (h5 : ∀ j, j < m → s ≠ .keyLine 0 j) : s ∉ preKey f m := by
  unfold preKey
  simp only [List.mem_append, List.mem_cons, not_or]
  exact ⟨notMem_preJoin h0 h1 h2, h3, notMem_keysL h4 h5⟩

theorem notMem_preTab {f : LFace} {s : Stage} {v l : Nat} (h0 : s ≠ .shift) (h1 : s ≠ .alpha)
    (h2 : ∀ j, s ≠ .tie j) (h3 : s ≠ .join) (h4 : ∀ j, j < v → s ≠ .key 0 j)
    (h5 : ∀ j, j < v → s ≠ .keyLine 0 j) (h6 : ∀ j, j < l → s ≠ .tab j)
    (h7 : ∀ j, j < l → s ≠ .tabLine j) : s ∉ preTab f v l := by
  unfold preTab
  simp only [List.mem_append, not_or]
  exact ⟨notMem_preKey h0 h1 h2 h3 h4 h5, notMem_tabsL h6 h7⟩

section One
variable (f : LFace) (v : Nat) (hp : f.parts = [v])
include hp

theorem fr_shift (hs : f.shifted = true) : firstRound f .shift = 0 := by
  rw [firstRound_split f .shift []
    (Stage.alpha :: ties (f.planes - 1) ++ (Stage.join :: keysL v) ++ tabsL f.d ++
      [Stage.leaves, Stage.zero, Stage.bits]) (by
    rw [stages_one f v hp]
    simp [preTab, preKey, preJoin, blkA, hs]) (by simp)]
  rfl

theorem fr_alpha : firstRound f .alpha = oAlpha f := by
  rw [firstRound_split f .alpha (blkA f)
    (ties (f.planes - 1) ++ (Stage.join :: keysL v) ++ tabsL f.d ++
      [Stage.leaves, Stage.zero, Stage.bits]) (by
    rw [stages_one f v hp]
    simp [preTab, preKey, preJoin]) (notMem_blkA (by nofun)), sum_blkA]

theorem fr_join : firstRound f .join = oJoin f := by
  rw [firstRound_split f .join (preJoin f)
    (keysL v ++ tabsL f.d ++ [Stage.leaves, Stage.zero, Stage.bits]) (by
    rw [stages_one f v hp]
    simp [preTab, preKey]) (notMem_preJoin (by nofun) (by nofun) (fun _ => by nofun)),
    sum_preJoin]

theorem fr_key {m : Nat} (hm : m < v) : firstRound f (.key 0 m) = oKey f + K 0 m := by
  obtain ⟨post, e⟩ := keysL_split hm
  rw [firstRound_split f (.key 0 m) (preKey f m)
    ((Stage.keyLine 0 m :: post) ++ tabsL f.d ++ [Stage.leaves, Stage.zero, Stage.bits]) (by
    rw [stages_one f v hp]
    simp [preTab, preKey, e])
    (notMem_preKey (by nofun) (by nofun) (fun _ => by nofun) (by nofun)
      (fun j hj e => by have := Stage.key.inj e; omega) (fun _ _ => by nofun)), sum_preKey]

theorem fr_keyLine {m : Nat} (hm : m < v) :
    firstRound f (.keyLine 0 m) = oKey f + K 0 m + (m + 3) := by
  obtain ⟨post, e⟩ := keysL_split hm
  rw [firstRound_split f (.keyLine 0 m) (preKey f m ++ [.key 0 m])
    (post ++ tabsL f.d ++ [Stage.leaves, Stage.zero, Stage.bits]) (by
    rw [stages_one f v hp]
    simp [preTab, preKey, e])
    (by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨notMem_preKey (by nofun) (by nofun) (fun _ => by nofun) (by nofun)
        (fun _ _ => by nofun) (fun j hj e => by have := Stage.keyLine.inj e; omega), by nofun⟩),
    List.map_append, List.sum_append, sum_preKey]
  simp [rounds_key]

theorem fr_tab {l : Nat} (hl : l < f.d) : firstRound f (.tab l) = oTab f v + K f.mu l := by
  obtain ⟨post, e⟩ := tabsL_split hl
  rw [firstRound_split f (.tab l) (preTab f v l)
    ((Stage.tabLine l :: post) ++ [Stage.leaves, Stage.zero, Stage.bits]) (by
    rw [stages_one f v hp]
    simp [preTab, e])
    (notMem_preTab (by nofun) (by nofun) (fun _ => by nofun) (by nofun) (fun _ _ => by nofun)
      (fun _ _ => by nofun) (fun j hj e => by have := Stage.tab.inj e; omega)
      (fun _ _ => by nofun)), sum_preTab]

theorem fr_tabLine {l : Nat} (hl : l < f.d) :
    firstRound f (.tabLine l) = oTab f v + K f.mu l + (f.mu + l + 3) := by
  obtain ⟨post, e⟩ := tabsL_split hl
  rw [firstRound_split f (.tabLine l) (preTab f v l ++ [.tab l])
    (post ++ [Stage.leaves, Stage.zero, Stage.bits]) (by
    rw [stages_one f v hp]
    simp [preTab, e])
    (by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨notMem_preTab (by nofun) (by nofun) (fun _ => by nofun) (by nofun)
        (fun _ _ => by nofun) (fun _ _ => by nofun) (fun _ _ => by nofun)
        (fun j hj e => by have := Stage.tabLine.inj e; omega), by nofun⟩),
    List.map_append, List.sum_append, sum_preTab]
  simp [rounds_tab]

theorem fr_leaves : firstRound f .leaves = oLeaves f v := by
  rw [firstRound_split f .leaves (preTab f v f.d) [.zero, .bits] (stages_one f v hp)
    (notMem_preTab (by nofun) (by nofun) (fun _ => by nofun) (by nofun) (fun _ _ => by nofun)
      (fun _ _ => by nofun) (fun _ _ => by nofun) (fun _ _ => by nofun)), sum_preTab]
  rfl

theorem fr_zero : firstRound f .zero = oZero f v := by
  rw [firstRound_split f .zero (preTab f v f.d ++ [.leaves]) [.bits] (by
    rw [stages_one f v hp]; simp)
    (by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨notMem_preTab (by nofun) (by nofun) (fun _ => by nofun) (by nofun)
        (fun _ _ => by nofun) (fun _ _ => by nofun) (fun _ _ => by nofun) (fun _ _ => by nofun),
        by nofun⟩),
    List.map_append, List.sum_append, sum_preTab]
  simp [rounds_leaves, oZero, oLeaves]

theorem fr_bits : firstRound f .bits = oBits f v := by
  have e : Stage.rounds f .zero = 1 := rfl
  rw [firstRound_split f .bits (preTab f v f.d ++ [.leaves, .zero]) [] (by
    rw [stages_one f v hp]; simp)
    (by
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨notMem_preTab (by nofun) (by nofun) (fun _ => by nofun) (by nofun)
        (fun _ _ => by nofun) (fun _ _ => by nofun) (fun _ _ => by nofun) (fun _ _ => by nofun),
        by nofun, by nofun⟩),
    List.map_append, List.sum_append, sum_preTab]
  simp [rounds_leaves, e, oBits, oZero, oLeaves]
  omega

end One

/-! ## 3 The walk through `messagesV` -/

theorem pure_spec {a b : α} {F G : Fork} {rs rest : List Fmt.RoundView}
    (h : (pure a : Hr α) F rs = some (b, G, rest)) : b = a ∧ G = F ∧ rest = rs := by
  have h' : some (a, F, rs) = some (b, G, rest) := h
  cases h'
  exact ⟨rfl, rfl, rfl⟩

theorem ite_bind_some {c : Prop} [Decidable c] {x y : Hr α} {k : α → Hr β} {F : Fork}
    {rs : List Fmt.RoundView} {r : β × Fork × List Fmt.RoundView}
    (h : (if c then x >>= k else y >>= k) F rs = some r) :
    ∃ a G rest, (if c then x else y) F rs = some (a, G, rest) ∧ k a G rest = some r := by
  by_cases hc : c
  · rw [if_pos hc] at h
    obtain ⟨a, G, rest, h1, h2⟩ := bindHr_some h
    exact ⟨a, G, rest, by rw [if_pos hc]; exact h1, h2⟩
  · rw [if_neg hc] at h
    obtain ⟨a, G, rest, h1, h2⟩ := bindHr_some h
    exact ⟨a, G, rest, by rw [if_neg hc]; exact h1, h2⟩

theorem dd {δ : Type} (l : List δ) (a b : Nat) : (l.drop a).drop b = l.drop (a + b) := by
  simp [List.drop_drop]

/-- What the walk yields: the fields of what was heard, in the three readers on the rounds. -/
structure Walk (f : LFace) (v : Nat) (rs : List Fmt.RoundView) (g : HeardV) : Prop where
  len : oEnd f v ≤ rs.length
  theta : g.theta = if f.shifted then one rs 0 else zeroE
  alpha : g.alpha = one rs (oAlpha f)
  joinLen : (many rs (oJoin f)).length = f.mu
  keys : g.keys.map (·.1) = [lastPt 0 (f.orders 0) #[] rs (oKey f) v]
  leaves : g.leaves.vars =
    leafVars f (lastPt f.mu orderDefault (many rs (oJoin f)).toArray.reverse rs (oTab f v) f.d)
  zb0 : g.zb0 = (seg rs (oLeaves f v + 1) (f.mu + f.d)).toArray
  zb1 : g.zb1 = (seg rs (oBits f v + 1) (f.mu + f.d)).toArray

theorem walk (f : LFace) (v : Nat) (hp : f.parts = [v]) (hpl : 2 ≤ f.planes) {F G : Fork}
    {rs rest : List Fmt.RoundView} {g : HeardV} (h : messagesV f F rs = some (g, G, rest)) :
    Walk f v rs g := by
  have dJ : oJoin f = oAlpha f + 1 + 3 * (f.planes - 1) := rfl
  have dK : oKey f = oJoin f + 1 := rfl
  have dT : oTab f v = oKey f + K 0 v := rfl
  have dL : oLeaves f v = oTab f v + K f.mu f.d := rfl
  have dZ : oZero f v = oLeaves f v + (f.mu + f.d + 1) := rfl
  have dB : oBits f v = oZero f v + 1 := rfl
  have dE : oEnd f v = oBits f v + (f.mu + f.d + 3) := rfl
  unfold messagesV at h
  obtain ⟨slot0, F1, r1, e1, h⟩ := bindHr_some h
  obtain ⟨o1, F2, r2, e2, h⟩ := bindHr_some h
  obtain ⟨o2, F3, r3, e3, h⟩ := bindHr_some h
  obtain ⟨o3, F4, r4, e4, h⟩ := bindHr_some h
  dsimp only at h
  obtain ⟨theta, F5, r5, e5, h⟩ := ite_bind_some h
  obtain ⟨alpha, F6, r6, e6, h⟩ := bindHr_some h
  obtain ⟨⟨rows, sZ, sG⟩, F7, r7, e7, h⟩ := bindHr_some h
  obtain ⟨⟨rows2, roots⟩, F8, r8, e8, h⟩ := bindHr_some h
  obtain ⟨jo, F9, r9, e9, h⟩ := bindHr_some h
  obtain ⟨⟨rows3, keys⟩, F10, r10, e10, h⟩ := bindHr_some h
  obtain ⟨u1, F11, r11, e11, h⟩ := bindHr_some h
  obtain ⟨table, F12, r12, e12, h⟩ := bindHr_some h
  obtain ⟨u2, F13, r13, e13, h⟩ := bindHr_some h
  obtain ⟨leaves, F14, r14, e14, h⟩ := bindHr_some h
  obtain ⟨ze, F15, r15, e15, h⟩ := bindHr_some h
  obtain ⟨bits, F16, r16, e16, h⟩ := bindHr_some h
  obtain ⟨sl, F17, r17, e17, h⟩ := bindHr_some h
  obtain ⟨u3, F18, r18, e18, h⟩ := bindHr_some h
  obtain ⟨hg, _, _⟩ := pure_spec h
  -- the rounds that are left, piece by piece
  have c1 : r1 = rs := by simpa using (cuts_slot.cut e1).1
  subst c1
  have c2 : r2 = r1 := by simpa using ((cuts_owe _).cut e2).1
  subst c2
  have c3 : r3 = r2 := by simpa using ((cuts_owe _).cut e3).1
  subst c3
  have c4 : r4 = r3 := by simpa using ((cuts_owe _).cut e4).1
  subst c4
  have t5 : r5 = r4.drop (oAlpha f) ∧ oAlpha f ≤ r4.length ∧
      theta = (if f.shifted then one r4 0 else zeroE) := by
    unfold oAlpha
    by_cases hs : f.shifted = true
    · simp only [if_pos hs] at e5 ⊢
      exact drawV_spec e5
    · simp only [if_neg hs] at e5 ⊢
      obtain ⟨a, _, c⟩ := pure_spec e5
      exact ⟨by simp [c], by omega, a⟩
  obtain ⟨hr5, l5, ht⟩ := t5
  obtain ⟨q6, l6, ha⟩ := drawV_spec e6
  obtain ⟨q7, l7⟩ := (cuts_tieV _ _ hpl).cut e7
  rw [hp] at e8 e10
  obtain ⟨p8, _, q8⟩ :=
    pure_spec (show (pure (rows, [Aff.slot sZ]) : Hr _) F7 r7 =
      some ((rows2, roots), F8, r8) from e8)
  obtain ⟨q9, l9, t9, s9⟩ := drawsV_spec e9
  have hroots : roots = [Aff.slot sZ] := congrArg (·.2) p8
  rw [hroots] at e10
  obtain ⟨c, hc, hkeys⟩ := keysV_one (v := v) (i := 0) e10
  obtain ⟨q10, l10⟩ := run_cuts hc
  have pc := run_point hc
  have q11 : r11 = r10 := by simpa using ((cuts_must _).cut e11).1
  obtain ⟨q12, l12⟩ := run_cuts e12
  have pt := run_point e12
  have q13 : r13 = r12 := by simpa using ((cuts_must _).cut e13).1
  obtain ⟨q14, l14, t14, v14⟩ := openV_spec e14
  obtain ⟨q15, l15, t15, s15⟩ := drawsV_spec e15
  obtain ⟨q16, l16, t16⟩ := sumV_spec e16
  have hlv : (leafVars f table.point).length = f.mu + f.d := by simp [leafVars]
  have hbv : (bitsCall ze.reverse.toList).vs.length = f.mu + f.d := by simp [bitsCall, s15]
  have hbr : vRoundsOf (bitsCall ze.reverse.toList) = f.mu + f.d + 3 := by
    simp [VerifiableInference.Desc.K3.roundsOf, bitsCall, s15]
  rw [hlv] at q14 l14 t14
  rw [hbv] at t16
  rw [hbr] at q16 l16
  have hr6 : r6 = r4.drop (oAlpha f + 1) := by rw [q6, hr5, dd]
  have hr7 : r7 = r4.drop (oJoin f) := by rw [q7, hr6, dd, dJ]
  have hr8 : r8 = r4.drop (oJoin f) := by rw [q8, hr7]
  have hr9 : r9 = r4.drop (oKey f) := by rw [q9, hr8, dd, dK]
  have hr10 : r10 = r4.drop (oTab f v) := by rw [q10, hr9, dd, dT]
  have hr11 : r11 = r4.drop (oTab f v) := by rw [q11, hr10]
  have hr12 : r12 = r4.drop (oLeaves f v) := by rw [q12, hr11, dd, dL]
  have hr13 : r13 = r4.drop (oLeaves f v) := by rw [q13, hr12]
  have hr14 : r14 = r4.drop (oZero f v) := by rw [q14, hr13, dd, dZ]
  have hr15 : r15 = r4.drop (oBits f v) := by rw [q15, hr14, dd, dB]
  rw [hr15, List.length_drop] at l16
  rw [hr5] at ha
  rw [one_drop, Nat.add_zero] at ha
  rw [hr8, many_drop, Nat.add_zero] at t9
  have hjo : jo = (many r4 (oJoin f)).toArray := by
    rw [← t9]
  rw [hr9, lastPt_drop] at pc
  rw [hr11, lastPt_drop] at pt
  rw [hr13, seg_drop] at t14
  rw [hr15, seg_drop] at t16
  subst hg
  refine ⟨by omega, ht, ha, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← t9]
    simpa using s9
  · show keys.map (·.1) = _
    have hk : keys = [(c.point, c.form)] := hkeys
    rw [hk, ← pc]
    rfl
  · show leaves.vars = _
    rw [v14, pt, hjo]
  · show leaves.r.toArray = _
    rw [t14]
  · show (bits.1.r.take (f.mu + f.d)).toArray = _
    rw [t16]

/-! ## 5 `ptsOf` at the whole list, in the three readers; the two theorems -/

theorem K_succ (m0 n : Nat) : K m0 (n + 1) = K m0 n + (m0 + n + 4) := rfl

theorem K_mono (m0 : Nat) {a b : Nat} (h : a ≤ b) : K m0 a ≤ K m0 b := by
  induction b with
  | zero =>
    have : a = 0 := by omega
    subst this
    exact Nat.le_refl _
  | succ n ih =>
    rcases Nat.le_succ_iff.1 h with h1 | h1
    · have := ih h1
      rw [K_succ]
      omega
    · subst h1
      exact Nat.le_refl _

/-- The numbers of rounds in front, one after the other. -/
theorem o_chain (f : LFace) (v : Nat) :
    oAlpha f ≤ 1 ∧ oJoin f = oAlpha f + 1 + 3 * (f.planes - 1) ∧ oKey f = oJoin f + 1 ∧
      oTab f v = oKey f + K 0 v ∧ oLeaves f v = oTab f v + K f.mu f.d ∧
      oZero f v = oLeaves f v + (f.mu + f.d + 1) ∧ oBits f v = oZero f v + 1 ∧
      oEnd f v = oBits f v + (f.mu + f.d + 3) := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  unfold oAlpha
  split <;> omega

section All
variable (f : LFace) (v : Nat) (hp : f.parts = [v]) (front back : List Fmt.Drawn)
  (rs : List Fmt.RoundView) (hlen : oEnd f v ≤ rs.length)
include hp hlen

theorem theta_all : (ptsOf f front.length (allOf front rs back)).theta =
    if f.shifted then one rs 0 else zeroE := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := o_chain f v
  show (if f.shifted then elemAt (allOf front rs back) (roundAt f front.length .shift) else zeroE) =
    _
  by_cases hs : f.shifted = true
  · simp only [if_pos hs]
    unfold roundAt
    rw [fr_shift f v hp hs, elemAt_all front back rs 0 (by omega)]
  · simp only [if_neg hs]

theorem alpha_all : (ptsOf f front.length (allOf front rs back)).alpha = one rs (oAlpha f) := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := o_chain f v
  show elemAt (allOf front rs back) (roundAt f front.length .alpha) = _
  unfold roundAt
  rw [fr_alpha f v hp, elemAt_all front back rs _ (by omega)]

theorem rhoT_all (hj : (many rs (oJoin f)).length = f.mu) :
    (ptsOf f front.length (allOf front rs back)).rhoT = (many rs (oJoin f)).toArray.reverse := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := o_chain f v
  show (drawsAt (allOf front rs back) (roundAt f front.length .join) f.mu).toArray.reverse = _
  unfold roundAt
  rw [fr_join f v hp, drawsAt_all front back rs _ _ (by omega) hj]

theorem zeroPt_all (hz : (many rs (oZero f v)).length = f.mu + f.d) :
    (ptsOf f front.length (allOf front rs back)).zeroPt = (many rs (oZero f v)).toArray.reverse :=
      by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := o_chain f v
  show (drawsAt (allOf front rs back) (roundAt f front.length .zero) (f.mu + f.d)).toArray.reverse =
    _
  unfold roundAt
  rw [fr_zero f v hp, drawsAt_all front back rs _ _ (by omega) hz]

theorem keyPt_all {m : Nat} (hm : m ≤ v) :
    (ptsOf f front.length (allOf front rs back)).keyPt 0 m =
      lastPt 0 (f.orders 0) #[] rs (oKey f) m := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := o_chain f v
  cases m with
  | zero => rfl
  | succ m =>
    have hk := K_mono 0 hm
    rw [K_succ] at hk
    show behind m (f.orders 0 m) (varChals f front.length (allOf front rs back) (.key 0 m) m)
      (elemAt (allOf front rs back) (roundAt f front.length (.keyLine 0 m))) = _
    unfold roundAt
    rw [varChals_all f front back rs _ _ m (fr_key f v hp (by omega)) (by omega),
      fr_keyLine f v hp (by omega), elemAt_all front back rs _ (by omega)]
    simp [lastPt]

theorem tabPt_all (hj : (many rs (oJoin f)).length = f.mu) {l : Nat} (hl : l ≤ f.d) :
    (ptsOf f front.length (allOf front rs back)).tabPt l =
      lastPt f.mu orderDefault (many rs (oJoin f)).toArray.reverse rs (oTab f v) l := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := o_chain f v
  cases l with
  | zero => exact rhoT_all f v hp front back rs hlen hj
  | succ l =>
    have hk := K_mono f.mu hl
    rw [K_succ] at hk
    show behind (f.mu + l) (orderDefault (f.mu + l))
      (varChals f front.length (allOf front rs back) (.tab l) (f.mu + l))
      (elemAt (allOf front rs back) (roundAt f front.length (.tabLine l))) = _
    unfold roundAt
    rw [varChals_all f front back rs _ _ _ (fr_tab f v hp (by omega)) (by omega),
      fr_tabLine f v hp (by omega), elemAt_all front back rs _ (by omega)]
    rfl

theorem leavesR_all : leavesR f front.length (allOf front rs back) =
    (seg rs (oLeaves f v + 1) (f.mu + f.d)).toArray := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := o_chain f v
  unfold leavesR
  rw [varChals_all f front back rs _ _ _ (fr_leaves f v hp) (by omega)]

theorem bitsR_all : bitsR f front.length (allOf front rs back) =
    (seg rs (oBits f v + 1) (f.mu + f.d)).toArray := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := o_chain f v
  unfold bitsR
  rw [varChals_all f front back rs _ _ _ (fr_bits f v hp) (by omega)]

end All

/-- **Conditional: at one part of keys.** Where the hearing returns on the rounds rs, its points are
those of the challenges of rs, whatever stands in front and behind. -/
theorem pointsAgree_of_hearV (f : LFace) (v : Nat) (hp : f.parts = [v]) (F G : Fork)
    (rs : List Fmt.RoundView) (g : HeardV) (front back : List Fmt.Drawn)
    (h : hearV f F rs = some (g, G)) :
    PointsAgree f g front.length (front ++ rs.map (·.drawn) ++ back) := by
  unfold hearV at h
  split at h
  · rename_i hok
    have hpl : 2 ≤ f.planes := by
      simp only [VerifiableInference.Desc.K3.Face.ok, Bool.and_eq_true, decide_eq_true_eq] at hok
      omega
    split at h
    · rename_i g' G' hm
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨a1, a2⟩ := h
      subst a1 a2
      have W := walk f v hp hpl hm
      show PointsAgree f g' front.length (allOf front rs back)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [W.theta, theta_all f v hp front back rs W.len]
      · rw [W.alpha, alpha_all f v hp front back rs W.len]
      · rw [W.keys, hp, ← keyPt_all f v hp front back rs W.len (Nat.le_refl v)]
        rfl
      · rw [W.zb0, leavesR_all f v hp front back rs W.len]
      · rw [W.zb1, bitsR_all f v hp front back rs W.len]
      · rw [W.leaves, ← tabPt_all f v hp front back rs W.len W.joinLen (Nat.le_refl _)]
        rfl
    · exact nomatch h
  · exact nomatch h

/-- **At a proof file's link**: the verifier program's structure, as `hearVia` makes it, has the
calls' key points of `keyPtsAt`. -/
theorem keyPtsAt_of_hearVia (p : VerifiableInference.Desc.First.Look.P)
    (s : OnBytes.Model.Forest.Shape) (hs : p.shape = some s) (F G : Fork) (rs : List Fmt.RoundView)
    (H : OnBytes.Model.Forest.Heard) (front back : List Fmt.Drawn)
    (h : VerifiableInference.Desc.K3.Law.hearVia p F rs = some (H, G)) :
    H.zx = (keyPtsAt s front.length (front ++ rs.map (·.drawn) ++ back)).zx ∧
      H.zy = (keyPtsAt s front.length (front ++ rs.map (·.drawn) ++ back)).zy ∧
      H.zk = (keyPtsAt s front.length (front ++ rs.map (·.drawn) ++ back)).zk := by
  unfold VerifiableInference.Desc.K3.Law.hearVia at h
  rw [hs] at h
  simp only at h
  split at h
  · obtain ⟨x, hx, h2⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨gV, G'⟩ := x
    obtain ⟨H', hH, e⟩ := Option.map_eq_some_iff.1 h2
    simp only [Prod.mk.injEq] at e
    obtain ⟨e1', _⟩ := e
    subst e1'
    have P := pointsAgree_of_hearV (VerifiableInference.Desc.K3.faceOf s) s.v rfl F G' rs gV front
      back hx
    have hk : gV.keys.map (·.1) =
        [(ptsOf (VerifiableInference.Desc.K3.faceOf s) front.length
          (front ++ rs.map (·.drawn) ++ back)).keyPt 0 s.v] := P.keys
    obtain ⟨a, ha, hpt⟩ : ∃ a, gV.keys = [a] ∧ a.1 =
        (ptsOf (VerifiableInference.Desc.K3.faceOf s) front.length
          (front ++ rs.map (·.drawn) ++ back)).keyPt 0 s.v := by
      cases hq : gV.keys with
      | nil => simp [hq] at hk
      | cons a l =>
        cases l with
        | nil => exact ⟨a, rfl, by simpa [hq] using hk⟩
        | cons b l' => simp [hq] at hk
    obtain ⟨pt, form⟩ := a
    simp only at hpt
    have R := keyPtsOf_toHeard s (VerifiableInference.Desc.K3.toHeardG gV) H' pt form ha hH
    rw [hpt] at R
    exact R
  · exact nomatch h


/-! ## 6 The call at which a stage's sumcheck is heard: the shape with the run's points -/

/-- Where a key level stands in the row: in some part's tree. -/
theorem mem_key {f : LFace} {i m : Nat} (hs : Stage.key i m ∈ stages f) :
    ∃ x ∈ f.parts.zipIdx, i = x.2 ∧ m < x.1 := by
  unfold stages at hs
  rcases List.mem_append.1 hs with h | h
  · rcases List.mem_append.1 h with h | h
    · rcases List.mem_append.1 h with h | h
      · exfalso
        by_cases hc : f.shifted = true <;> simp [hc] at h
      · obtain ⟨x, hx, h2⟩ := List.mem_flatMap.1 h
        obtain ⟨j, hj, h3⟩ := List.mem_flatMap.1 h2
        have hj' := List.mem_range.1 hj
        simp at h3
        exact ⟨x, hx, h3.1, by omega⟩
    · obtain ⟨l, _, h2⟩ := List.mem_flatMap.1 h
      simp at h2
  · simp at h

/-- Where a level of the table side stands in the row. -/
theorem mem_tab {f : LFace} {l : Nat} (hs : Stage.tab l ∈ stages f) : l < f.d := by
  unfold stages at hs
  rcases List.mem_append.1 hs with h | h
  · rcases List.mem_append.1 h with h | h
    · rcases List.mem_append.1 h with h | h
      · exfalso
        by_cases hc : f.shifted = true <;> simp [hc] at h
      · obtain ⟨x, hx, h2⟩ := List.mem_flatMap.1 h
        obtain ⟨j, hj, h3⟩ := List.mem_flatMap.1 h2
        simp at h3
    · obtain ⟨j, hj, h2⟩ := List.mem_flatMap.1 h
      have hj' := List.mem_range.1 hj
      simp at h2
      omega
  · simp at h

/-- At a key level of the row the face's order has as many members as the level has variables. -/
theorem order_len {f : LFace} (hok : f.ok = true) {i m : Nat} (hs : Stage.key i m ∈ stages f) :
    (f.orders i m).length = m := by
  obtain ⟨x, hx, hi, hm⟩ := mem_key hs
  simp only [VerifiableInference.Desc.K3.Face.ok, Bool.and_eq_true, List.all_eq_true] at hok
  have h1 := hok.2 x hx
  simp only [VerifiableInference.Desc.First.Prod.runOk, Bool.and_eq_true, List.all_eq_true] at h1
  have h2 := h1.2 m (List.mem_range.2 hm)
  simp only [VerifiableInference.Desc.First.Prod.orderOk, Bool.and_eq_true, beq_iff_eq,
    Nat.zero_add] at h2
  rw [hi]
  exact h2.1.1

/-- A stage's variables at the run's points, blanked, are its shape's. -/
theorem blank_varsAt (f : LFace) (s : Stage) (k : MaskedSum.Call) (base : Nat)
    (heard : List Fmt.Drawn) (hk : s.call f = some k) (hs : s ∈ stages f) (hok : f.ok = true) :
    (varsAt f s (ptsOf f base heard)).map blank = k.vs := by
  cases s with
  | key i m =>
    simp only [Stage.call, Option.some.injEq] at hk
    subst hk
    exact blank_levelVars m _ _ (order_len hok hs)
  | tab l =>
    simp only [Stage.call, Option.some.injEq] at hk
    subst hk
    exact blank_levelVars _ _ _ (by simp [orderDefault])
  | leaves =>
    simp only [Stage.call, Option.some.injEq] at hk
    subst hk
    show (leafVars f _).map blank = leafVars f #[]
    simp [leafVars, blank]
  | bits =>
    simp only [Stage.call, Option.some.injEq] at hk
    subst hk
    show ((bitsCall (ptsOf f base heard).zeroPt.toList).vs).map blank =
      (bitsCall (List.replicate (f.mu + f.d) zeroE)).vs
    apply List.ext_getElem
    · simp [bitsCall, ptsOf, drawsAt]
    · intro j h1 h2
      simp [bitsCall, blank]
  | tie n =>
    cases n <;>
    · simp only [Stage.call, Option.some.injEq] at hk
      subst hk
      rfl
  | split i =>
    simp only [Stage.call, Option.some.injEq] at hk
    subst hk
    rfl
  | shift => simp [Stage.call] at hk
  | alpha => simp [Stage.call] at hk
  | join => simp [Stage.call] at hk
  | keyLine i m => simp [Stage.call] at hk
  | tabLine l => simp [Stage.call] at hk
  | zero => simp [Stage.call] at hk

/-- **At every sumcheck of the row, the shape with `pointsAt` laid in is the verifier's own list
of variables at the run's points.** At every face that passes the verifier's tests (`hok`), whatever
its parts. -/
theorem withPoints_varsAt (f : LFace) (s : Stage) (k : MaskedSum.Call) (base : Nat)
    (heard : List Fmt.Drawn) (hk : s.call f = some k) (hs : s ∈ stages f) (hok : f.ok = true) :
    withPoints k.vs (pointsAt f s (ptsOf f base heard)) = varsAt f s (ptsOf f base heard) := by
  rw [← blank_varsAt f s k base heard hk hs hok]
  exact withPoints_blank _

theorem elemsAt_take (front ds : List Fmt.Drawn) (n i : Nat) (h : i < front.length + n) :
    elemsAt (front ++ ds.take n) i = elemsAt (front ++ ds) i := by
  unfold elemsAt
  by_cases hi : i < front.length
  · rw [List.getElem?_append_left hi, List.getElem?_append_left hi]
  · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
      List.getElem?_take_of_lt (by omega)]

theorem elemAt_take (front ds : List Fmt.Drawn) (n i : Nat) (h : i < front.length + n) :
    elemAt (front ++ ds.take n) i = elemAt (front ++ ds) i := by
  unfold elemAt
  rw [elemsAt_take front ds n i h]

theorem drawsAt_take (front ds : List Fmt.Drawn) (n i k : Nat) (h : i < front.length + n) :
    drawsAt (front ++ ds.take n) i k = drawsAt (front ++ ds) i k := by
  unfold drawsAt
  rw [elemsAt_take front ds n i h]

theorem varChals_take (f : LFace) (front ds : List Fmt.Drawn) (n : Nat) (s : Stage) (k : Nat)
    (h : firstRound f s + 1 + k ≤ n) :
    varChals f front.length (front ++ ds.take n) s k = varChals f front.length (front ++ ds) s k :=
      by
  unfold varChals roundAt
  apply List.map_congr_left
  intro l hl
  have hl' := List.mem_range.1 hl
  exact elemAt_take front ds n _ (by omega)

section Prefix
variable (f : LFace) (v : Nat) (hp : f.parts = [v]) (front ds : List Fmt.Drawn)
include hp

theorem keyPt_take {m n : Nat} (hm : m ≤ v) (hn : oKey f + K 0 m ≤ n) :
    (ptsOf f front.length (front ++ ds.take n)).keyPt 0 m =
      (ptsOf f front.length (front ++ ds)).keyPt 0 m := by
  cases m with
  | zero => rfl
  | succ m =>
    rw [K_succ] at hn
    show behind m (f.orders 0 m) (varChals f front.length (front ++ ds.take n) (.key 0 m) m)
        (elemAt (front ++ ds.take n) (roundAt f front.length (.keyLine 0 m))) =
      behind m (f.orders 0 m) (varChals f front.length (front ++ ds) (.key 0 m) m)
        (elemAt (front ++ ds) (roundAt f front.length (.keyLine 0 m)))
    rw [varChals_take f front ds n _ _ (by rw [fr_key f v hp (by omega)]; omega),
      elemAt_take front ds n _ (by unfold roundAt; rw [fr_keyLine f v hp (by omega)]; omega)]

theorem rhoT_take {n : Nat} (hn : oKey f ≤ n) :
    (ptsOf f front.length (front ++ ds.take n)).rhoT =
      (ptsOf f front.length (front ++ ds)).rhoT := by
  have c : oKey f = oJoin f + 1 := rfl
  show (drawsAt (front ++ ds.take n) (roundAt f front.length .join) f.mu).toArray.reverse =
    (drawsAt (front ++ ds) (roundAt f front.length .join) f.mu).toArray.reverse
  rw [drawsAt_take front ds n _ _ (by unfold roundAt; rw [fr_join f v hp]; omega)]

theorem tabPt_take {l n : Nat} (hl : l ≤ f.d) (hn : oTab f v + K f.mu l ≤ n) :
    (ptsOf f front.length (front ++ ds.take n)).tabPt l =
      (ptsOf f front.length (front ++ ds)).tabPt l := by
  cases l with
  | zero =>
    have c : oTab f v = oKey f + K 0 v := rfl
    exact rhoT_take f v hp front ds (by omega)
  | succ l =>
    rw [K_succ] at hn
    show behind (f.mu + l) (orderDefault (f.mu + l))
        (varChals f front.length (front ++ ds.take n) (.tab l) (f.mu + l))
        (elemAt (front ++ ds.take n) (roundAt f front.length (.tabLine l))) =
      behind (f.mu + l) (orderDefault (f.mu + l))
        (varChals f front.length (front ++ ds) (.tab l) (f.mu + l))
        (elemAt (front ++ ds) (roundAt f front.length (.tabLine l)))
    rw [varChals_take f front ds n _ _ (by rw [fr_tab f v hp (by omega)]; omega),
      elemAt_take front ds n _ (by unfold roundAt; rw [fr_tabLine f v hp (by omega)]; omega)]

theorem zeroPt_take {n : Nat} (hn : oBits f v ≤ n) :
    (ptsOf f front.length (front ++ ds.take n)).zeroPt =
      (ptsOf f front.length (front ++ ds)).zeroPt := by
  have c : oBits f v = oZero f v + 1 := rfl
  show (drawsAt (front ++ ds.take n) (roundAt f front.length .zero) (f.mu + f.d)).toArray.reverse =
    (drawsAt (front ++ ds) (roundAt f front.length .zero) (f.mu + f.d)).toArray.reverse
  rw [drawsAt_take front ds n _ _ (by unfold roundAt; rw [fr_zero f v hp]; omega)]

/-- **Conditional: at one part of keys. A stage's variables read the challenges in front of the
stage alone**: of the list cut in front of the stage they are what they are of the whole list. -/
theorem varsAt_prefix (s : Stage) (hs : s ∈ stages f) :
    varsAt f s (ptsOf f front.length (front ++ ds.take (firstRound f s))) =
      varsAt f s (ptsOf f front.length (front ++ ds)) := by
  cases s with
  | key i m =>
    obtain ⟨x, hx, hi, hm⟩ := mem_key hs
    rw [hp] at hx
    have hx' : x = (v, 0) := by simpa using hx
    subst hx'
    simp only at hi hm
    subst hi
    show levelVars m _ _ = levelVars m _ _
    rw [keyPt_take f v hp front ds (by omega) (by rw [fr_key f v hp hm])]
  | tab l =>
    have hl := mem_tab hs
    show levelVars _ _ _ = levelVars _ _ _
    rw [tabPt_take f v hp front ds (by omega) (by rw [fr_tab f v hp hl])]
  | leaves =>
    show leafVars f _ = leafVars f _
    rw [tabPt_take f v hp front ds (Nat.le_refl _) (by rw [fr_leaves f v hp]; exact Nat.le_refl _)]
  | bits =>
    show (bitsCall _).vs = (bitsCall _).vs
    rw [zeroPt_take f v hp front ds (by rw [fr_bits f v hp])]
  | tie n => rfl
  | split i => rfl
  | shift => rfl
  | alpha => rfl
  | join => rfl
  | keyLine i m => rfl
  | tabLine l => rfl
  | zero => rfl

end Prefix

#print axioms ProofFile.Honest.K3.withPoints_varsAt
#print axioms ProofFile.Honest.K3.varsAt_prefix
-- the helpers, each asked by name: other files' proofs may call them
#print axioms ProofFile.Honest.K3.one_drop
#print axioms ProofFile.Honest.K3.seg_drop
#print axioms ProofFile.Honest.K3.many_drop
#print axioms ProofFile.Honest.K3.seg_take
#print axioms ProofFile.Honest.K3.drop_cons
#print axioms ProofFile.Honest.K3.one_of_get
#print axioms ProofFile.Honest.K3.range_getD
#print axioms ProofFile.Honest.K3.seg_eq_range
#print axioms ProofFile.Honest.K3.allOf_get
#print axioms ProofFile.Honest.K3.elemsAt_all
#print axioms ProofFile.Honest.K3.elemAt_all
#print axioms ProofFile.Honest.K3.varChals_all
#print axioms ProofFile.Honest.K3.drawsAt_all
#print axioms ProofFile.Honest.K3.Cuts.bind
#print axioms ProofFile.Honest.K3.cuts_pure
#print axioms ProofFile.Honest.K3.cuts_slot
#print axioms ProofFile.Honest.K3.cuts_owe
#print axioms ProofFile.Honest.K3.cuts_must
#print axioms ProofFile.Honest.K3.cuts_foldlM
#print axioms ProofFile.Honest.K3.drawsV_spec
#print axioms ProofFile.Honest.K3.drawV_spec
#print axioms ProofFile.Honest.K3.varsRead_firsts
#print axioms ProofFile.Honest.K3.whole_seg
#print axioms ProofFile.Honest.K3.readAll_none_spec
#print axioms ProofFile.Honest.K3.hear_none_seg
#print axioms ProofFile.Honest.K3.sumV_spec
#print axioms ProofFile.Honest.K3.cuts_sumV
#print axioms ProofFile.Honest.K3.openV_spec
#print axioms ProofFile.Honest.K3.cuts_tieV
#print axioms ProofFile.Honest.K3.level_seg
#print axioms ProofFile.Honest.K3.run_cuts
#print axioms ProofFile.Honest.K3.run_point
#print axioms ProofFile.Honest.K3.lastPt_drop
#print axioms ProofFile.Honest.K3.keysV_one
#print axioms ProofFile.Honest.K3.stages_one
#print axioms ProofFile.Honest.K3.ties_succ
#print axioms ProofFile.Honest.K3.keysL_succ
#print axioms ProofFile.Honest.K3.tabsL_succ
#print axioms ProofFile.Honest.K3.keysL_split
#print axioms ProofFile.Honest.K3.tabsL_split
#print axioms ProofFile.Honest.K3.rounds_tie
#print axioms ProofFile.Honest.K3.rounds_key
#print axioms ProofFile.Honest.K3.rounds_tab
#print axioms ProofFile.Honest.K3.rounds_leaves
#print axioms ProofFile.Honest.K3.rounds_bits
#print axioms ProofFile.Honest.K3.sum_blkA
#print axioms ProofFile.Honest.K3.sum_ties
#print axioms ProofFile.Honest.K3.sum_keysL
#print axioms ProofFile.Honest.K3.sum_tabsL
#print axioms ProofFile.Honest.K3.sum_preJoin
#print axioms ProofFile.Honest.K3.sum_preKey
#print axioms ProofFile.Honest.K3.sum_preTab
#print axioms ProofFile.Honest.K3.firstRound_split
#print axioms ProofFile.Honest.K3.notMem_blkA
#print axioms ProofFile.Honest.K3.notMem_ties
#print axioms ProofFile.Honest.K3.notMem_keysL
#print axioms ProofFile.Honest.K3.notMem_tabsL
#print axioms ProofFile.Honest.K3.notMem_preJoin
#print axioms ProofFile.Honest.K3.notMem_preKey
#print axioms ProofFile.Honest.K3.notMem_preTab
#print axioms ProofFile.Honest.K3.fr_shift
#print axioms ProofFile.Honest.K3.fr_alpha
#print axioms ProofFile.Honest.K3.fr_join
#print axioms ProofFile.Honest.K3.fr_key
#print axioms ProofFile.Honest.K3.fr_keyLine
#print axioms ProofFile.Honest.K3.fr_tab
#print axioms ProofFile.Honest.K3.fr_tabLine
#print axioms ProofFile.Honest.K3.fr_leaves
#print axioms ProofFile.Honest.K3.fr_zero
#print axioms ProofFile.Honest.K3.fr_bits
#print axioms ProofFile.Honest.K3.pure_spec
#print axioms ProofFile.Honest.K3.ite_bind_some
#print axioms ProofFile.Honest.K3.dd
#print axioms ProofFile.Honest.K3.walk
#print axioms ProofFile.Honest.K3.K_succ
#print axioms ProofFile.Honest.K3.K_mono
#print axioms ProofFile.Honest.K3.o_chain
#print axioms ProofFile.Honest.K3.theta_all
#print axioms ProofFile.Honest.K3.alpha_all
#print axioms ProofFile.Honest.K3.rhoT_all
#print axioms ProofFile.Honest.K3.zeroPt_all
#print axioms ProofFile.Honest.K3.keyPt_all
#print axioms ProofFile.Honest.K3.tabPt_all
#print axioms ProofFile.Honest.K3.leavesR_all
#print axioms ProofFile.Honest.K3.bitsR_all
#print axioms ProofFile.Honest.K3.mem_key
#print axioms ProofFile.Honest.K3.mem_tab
#print axioms ProofFile.Honest.K3.order_len
#print axioms ProofFile.Honest.K3.blank_varsAt
#print axioms ProofFile.Honest.K3.elemsAt_take
#print axioms ProofFile.Honest.K3.elemAt_take
#print axioms ProofFile.Honest.K3.drawsAt_take
#print axioms ProofFile.Honest.K3.varChals_take
#print axioms ProofFile.Honest.K3.keyPt_take
#print axioms ProofFile.Honest.K3.rhoT_take
#print axioms ProofFile.Honest.K3.tabPt_take
#print axioms ProofFile.Honest.K3.zeroPt_take

#print axioms ProofFile.Honest.K3.pointsAgree_of_hearV
#print axioms ProofFile.Honest.K3.keyPtsAt_of_hearVia

end ProofFile.Honest.K3
