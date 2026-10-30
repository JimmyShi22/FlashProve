-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/SumLaw/Fits.lean: THE MESSAGES OF THE MASKED SUMCHECK's PART HAVE THE
STATED SHAPE, and its two stops never stop: what Honest/SumLaw/Plays.lean asks of a part, shown of
`sumPart` (Honest/Sum.lean), at declared rounds that state, round by round, as many scalars as the
call sends (`scalarsOf`), no other item but roots' places, and no oracle message, where every
variable of the shape has at least two coefficients and the challenges are as many as the part's
moves. Definitions of propositions, and statements with their proofs.
Main names:
  `StatedBy ns rs`: the declared rounds rs state just ns scalars, round by round, and no oracle
    message. `statedBy_nums`: it reads three numbers of a round's entry alone: the message's bytes,
    the answers, the roots. `statedBy_like`: **every list of declared rounds whose entries have
    these three numbers of the call's entries, and no oracle message, states the call's scalars**:
    the work bits, the names and what is sampled are free. `statedBy_entries`: its case at rounds
    that are made of the call's own entries.
  `LensBy ns gs`: the lists that the moves say have the lengths ns, at all that is shown (`Seen`)
    and every state.
  `sayE_fits`, `fitsFrom_mvOf`: from the two to the frame's test on shapes.
  `sentOfL_length`, `lensBy_sumGs`: **the part's lists have the call's lengths.**
  `shape_two`: where the call as it stands in a run passes `shapeOk`, every variable of the job's
    shape has at least two coefficients. `moves_length`, `scalarsOf_length`: the numbers of moves.
  `fits_sumPart`: **the test on shapes passes.** `bad_sumPart`, `hid_sumPart`: no stop stops.
  `plays_sumPart`: **the frame's `play` goes through on the part's steps and shows `sumOut`.** The
    whole list that it returns, and the law at a lifted part: PlaysSum.lean of this folder.

Limits. In every statement here m (the frame's `Mid`) is any state of a run and seen any `Seen`:
their field `opened` (where the player hands them, the columns that the sub-protocols before the
round have read: in the first and in the shared chain that chain's own alone, in the second chain
the first's, the shared chain's and its own: `Seen.opened`, Honest/Frame.lean) may have any value:
no premise is laid on it. Every variable of the shape has at least two coefficients: a premise
(`shape_two` has it from the verifier's test on the plan). Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.SumLaw.Out

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.SumLaw
open OnBytes (E addE subE mulE zeroE oneE)
open VerifiableInference.Desc (Oracle itemOf)
open VerifiableInference.Desc.Part.MaskedSum

variable {V W X : Type}

/-- The declared rounds state just so many scalars, round by round, and no oracle message. -/
def StatedBy : List Nat → List (Fmt.DeclaredRound × List Oracle) → Prop
  | [], [] => True
  | n :: ns, r :: rs =>
    r.1.items.filter (· != .root) = List.replicate n .e ∧ r.2 = [] ∧ StatedBy ns rs
  | _, _ => False

/-- The lists that the moves say have these lengths, at all that is shown (`Seen`) and every state.
-/
def LensBy : List Nat → List (Seen → State W X → List E) → Prop
  | [], [] => True
  | n :: ns, g :: gs => (∀ s t, (g s t).length = n) ∧ LensBy ns gs
  | _, _ => False

/-- What is said are elements of the extension field. -/
theorem sayE_items : ∀ l : List E,
    (sayE l).vals.map (fun v => itemOf v.got) = List.replicate l.length .e
  | [] => rfl
  | _ :: l => congrArg (Fmt.Item.e :: ·) (sayE_items l)

/-- Scalars fit a declared round that states as many, and no oracle message. -/
theorem sayE_fits (l : List E) (r : Fmt.DeclaredRound) (os : List Oracle)
    (h : r.items.filter (· != .root) = List.replicate l.length .e) (ho : os = []) :
    (sayE l).fits r os = true := by
  unfold Sending.fits
  rw [h, ho, sayE_items]
  simp [sayE]

/-- Moves that say scalars pass the test on shapes, where the lists have the stated lengths. -/
theorem fitsFrom_mvOf {C : Type} (c : C) : ∀ (ns : List Nat)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (gs : List (C → Seen → State W X → List E))
    (t : State W X)
    (seen : Seen) (ds : List Fmt.Drawn), StatedBy ns rs → LensBy ns (gs.map (· c)) →
    ds.length = ns.length → fitsFrom c rs (gs.map mvOf) t seen ds = true
  | [], [], [], _, _, [], _, _, _ => rfl
  | n :: ns, r :: rs, g :: gs, t, seen, d :: ds, ⟨h1, h2, h3⟩, ⟨k1, k2⟩, hl => by
    show ((sayE (g c seen t)).fits r.1 r.2 &&
      fitsFrom c rs (gs.map mvOf) (t.hears d) (seen.plus [rvSaid (g c seen t) d]) ds) = true
    rw [sayE_fits _ r.1 r.2 (by rw [k1 seen t]; exact h1) h2,
      fitsFrom_mvOf c ns rs gs _ _ ds h3 k2 (by simp only [List.length_cons] at hl; omega)]
    rfl
  | [], [], _ :: _, _, _, _, _, k, _ => k.elim
  | [], _ :: _, _, _, _, _, h, _, _ => h.elim
  | _ :: _, [], _, _, _, _, h, _, _ => h.elim
  | _ :: _, _ :: _, [], _, _, _, _, k, _ => k.elim
  | [], [], [], _, _, _ :: _, _, _, hl => by
    simp only [List.length_cons, List.length_nil] at hl
    omega
  | _ :: _, _ :: _, _ :: _, _, _, [], _, _, hl => by
    simp only [List.length_cons, List.length_nil] at hl
    omega

/-- Two stretches of moves. -/
theorem lensBy_append : ∀ (n₁ n₂ : List Nat) (g₁ g₂ : List (Seen → State W X → List E)),
    LensBy n₁ g₁ → LensBy n₂ g₂ → LensBy (n₁ ++ n₂) (g₁ ++ g₂)
  | [], _, [], _, _, h => h
  | _ :: n₁, n₂, _ :: g₁, g₂, ⟨a, b⟩, h => ⟨a, lensBy_append n₁ n₂ g₁ g₂ b h⟩
  | [], _, _ :: _, _, a, _ => a.elim
  | _ :: _, _, [], _, a, _ => a.elim

/-- Moves that are given by number. -/
theorem lensBy_range (G : Nat → Seen → State W X → List E) : ∀ (ns : List Nat) (s : Nat),
    (∀ j, j < ns.length → ∀ S t, (G (s + j) S t).length = ns.getD j 0) →
    LensBy ns ((List.range' s ns.length).map G)
  | [], _, _ => trivial
  | n :: ns, s, h => by
    rw [List.length_cons, List.range'_succ, List.map_cons]
    refine ⟨fun S t => h 0 (Nat.succ_pos _) S t, lensBy_range G ns (s + 1) fun j hj S t => ?_⟩
    have := h (j + 1) (by simp only [List.length_cons]; omega) S t
    have e : s + 1 + j = s + (j + 1) := by omega
    rw [e, this]
    rfl

/-! ## The part's lists -/

/-- A sum of two lists is as long as the longer. -/
theorem addL_length : ∀ a b : List E, (addL a b).length = max a.length b.length
  | [], b => by
    show b.length = _
    simp
  | x :: a, [] => by
    show (x :: a).length = _
    simp
  | x :: a, y :: b => by
    show (addL a b).length + 1 = _
    rw [addL_length a b]
    simp only [List.length_cons]
    omega

/-- One scalar fewer is sent than the variable has coefficients. -/
theorem sentOfL_length (v : Var) (g : List E) (h2 : 2 ≤ v.d) : (sentOfL v g).length = v.d - 1 := by
  have := cutOf_length v (padTo v.d g) (padTo_length _ _) h2
  rw [sentOfL_eq]
  omega

/-- To lay the run's points in turns no number of coefficients. -/
theorem withPoints_d : ∀ (vs : List Var) (zs : List E) (i : Nat),
    ((withPoints vs zs).getD i (.plain 0)).d = (vs.getD i (.plain 0)).d
  | [], _, _ => rfl
  | .plain _ :: _, _, 0 => rfl
  | .plain _ :: vs, zs, i + 1 => by
    show ((withPoints vs zs).getD i (.plain 0)).d = _
    exact withPoints_d vs zs i
  | .point _ _ :: _, _ :: _, 0 => rfl
  | .point _ _ :: vs, _ :: zs, i + 1 => by
    show ((withPoints vs zs).getD i (.plain 0)).d = _
    exact withPoints_d vs zs i
  | .point _ _ :: _, [], 0 => rfl
  | .point _ _ :: vs, [], i + 1 => by
    show ((withPoints vs []).getD i (.plain 0)).d = _
    exact withPoints_d vs [] i

/-- The variable number i of the call as it stands in a run has the shape's number of coefficients.
-/
theorem all_d (J : SumJob W X) (w : W) (fr : Front X) (i : Nat) (hi : i < J.shape.vs.length) :
    ((J.callAt w fr).all.getD i (.plain 0)).d = (J.shape.vs.getD i (.plain 0)).d := by
  cases he : J.shape.ends with
  | none => rw [all_none J w fr he, withPoints_d]
  | some e =>
    rw [all_some J w fr e he, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by rw [withPoints_length]; exact hi),
      ← List.getD_eq_getElem?_getD, withPoints_d]

/-- **The part's lists have the call's lengths.** -/
theorem lensBy_sumGs (name endName : String) (J : SumJob W X) (c : SumCoins name endName J)
    (h2 : ∀ v ∈ J.shape.vs, 2 ≤ v.d) :
    LensBy (scalarsOf J.shape) ((sumGs name endName J).map (· c)) := by
  unfold scalarsOf sumGs
  rw [List.map_append, List.map_append, List.map_map]
  refine lensBy_append _ _ _ _ (lensBy_append _ _ _ _ ⟨fun s t => ?_, trivial⟩ ?_) ?_
  · show (addL (padTo J.shape.lead _) ((coinsE c.2.1.1).take J.shape.lead) ++ [_]).length = _
    rw [List.length_append, addL_length, padTo_length, List.length_take]
    simp only [List.length_cons, List.length_nil]
    omega
  · have e : (List.range J.shape.vs.length).map
        ((fun x => x c) ∘ fun i => askG name endName J (saidVar J i) (i + 1)) =
        (List.range' 0 (J.shape.vs.map fun v => v.d - 1).length).map
          fun i => askG name endName J (saidVar J i) (i + 1) c := by
      rw [List.length_map, ← List.range_eq_range']
      rfl
    rw [e]
    refine lensBy_range _ _ 0 fun j hj s t => ?_
    rw [List.length_map] at hj
    rw [Nat.zero_add]
    show (sentOfL ((J.callAt t.input _).all.getD j (.plain 0)) _).length = _
    have hd := all_d J t.input
      ⟨t.heard.take (t.heard.length - (j + 1)), t.own, s.front (j + 1)⟩ j hj
    have hm : J.shape.vs.getD j (.plain 0) ∈ J.shape.vs := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
      exact List.getElem_mem hj
    rw [sentOfL_length _ _ (by rw [hd]; exact h2 _ hm), hd, List.getD_eq_getElem?_getD,
      List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj]
    rfl
  · cases he : J.shape.ends with
    | none => trivial
    | some e =>
      refine ⟨fun s t => ?_, fun s t => ?_, trivial⟩
      · show (sentOfL (.point zeroE (e.dY + 1)) _).length = e.dY
        show ((padTo (e.dY + 1) _).drop 1).length = e.dY
        rw [List.length_drop, padTo_length]
        rfl
      · show (addL (padTo e.n _) (scaleL _ (padTo e.n _))).length = e.n
        rw [addL_length, padTo_length]
        show max e.n ((padTo e.n _).map _).length = e.n
        rw [List.length_map, padTo_length, Nat.max_self]

/-- The call sends in as many rounds as the part has moves. -/
theorem scalarsOf_length (name endName : String) (J : SumJob W X) :
    (scalarsOf J.shape).length = (sumGs name endName J).length := by
  unfold scalarsOf sumGs
  cases he : J.shape.ends <;> simp

/-- The part has as many moves as `sumGs` lists. -/
theorem moves_length (name endName : String) (J : SumJob W X) :
    (sumPart (V := V) name endName J).moves.length = (sumGs name endName J).length := by
  exact (congrArg List.length (sumPart_moves (V := V) name endName J)).trans (List.length_map ..)

/-- Where the call as it stands in a run passes the verifier's test on the plan, every variable of
the job's shape has at least two coefficients. -/
theorem shape_two (J : SumJob W X) (w : W) (fr : Front X) (h : shapeOk (J.callAt w fr) = true) :
    ∀ v ∈ J.shape.vs, 2 ≤ v.d := by
  intro v hv
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
  have hg : J.shape.vs.getD i (.plain 0) = J.shape.vs[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    rfl
  have hlen : i < (J.callAt w fr).vs.length := by
    show i < (withPoints J.shape.vs (J.points w fr)).length
    rw [withPoints_length]
    exact hi
  have hm : (J.callAt w fr).vs.getD i (.plain 0) ∈ (J.callAt w fr).vs := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]
    exact List.getElem_mem hlen
  have hd : ((J.callAt w fr).vs.getD i (.plain 0)).d = (J.shape.vs.getD i (.plain 0)).d :=
    withPoints_d J.shape.vs (J.points w fr) i
  have h2 : 2 ≤ ((J.callAt w fr).vs.getD i (.plain 0)).d := by
    simp only [shapeOk, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
    exact (h.1 _ hm).1
  rw [← hg, ← hd]
  exact h2

/-- **The test on shapes passes.** -/
theorem fits_sumPart (name endName : String) (J : SumJob W X) (c : SumCoins name endName J)
    (h2 : ∀ v ∈ J.shape.vs, 2 ≤ v.d) (rs : List (Fmt.DeclaredRound × List Oracle))
    (hr : StatedBy (scalarsOf J.shape) rs) (t : State W X) (seen : Seen)
    (ds : List Fmt.Drawn) (hl : ds.length = (sumGs name endName J).length) :
    fitsFrom (C := SumCoins name endName J) c rs (sumPart (V := V) name endName J).moves t seen ds =
      true := by
  rw [sumPart_moves]
  exact fitsFrom_mvOf c _ rs _ t seen ds hr (lensBy_sumGs name endName J c h2)
    (by rw [hl, scalarsOf_length name endName J])

/-- The part's first stop never stops. -/
theorem bad_sumPart (name endName : String) (J : SumJob W X) (f o : List Fmt.Drawn) :
    (sumPart (V := V) name endName J).bad f o = none := rfl

/-- The part's second stop never stops. -/
theorem hid_sumPart (name endName : String) (J : SumJob W X) (v : V) (f o : List Fmt.Drawn) :
    (sumPart (V := V) name endName J).hid v f o = none := rfl

/-- **The frame's `play` goes through on the part's steps and shows `sumOut`.** -/
theorem plays_sumPart (name endName : String) (J : SumJob W X) (c : SumCoins name endName J)
    (h2 : ∀ v ∈ J.shape.vs, 2 ≤ v.d) (nm : String) (a : Addr)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (hr : StatedBy (scalarsOf J.shape) rs) (v : Option V)
    (ds : List Fmt.Drawn) (hl : ds.length = (sumGs name endName J).length) (back : List Fmt.RoundView)
    (m : Mid W X) :
    ∃ l, play ((sumPart (V := V) name endName J).steps nm a rs v c) ds back m =
        .ok (l, ⟨⟨m.st.input, m.st.heard ++ ds, m.st.own⟩, m.loc ++ ds,
          m.seen ++ sumOut J c m.st m.shown ds, m.opened⟩) ∧
              roundsOf l = sumOut J c m.st m.shown ds := by
  have h := play_steps (sumPart (V := V) name endName J) (bad_sumPart name endName J)
    (hid_sumPart name endName J) nm a rs v c ds back m (sumOut J c m.st m.shown ds)
    (fits_sumPart name endName J c h2 rs hr m.st m.shown ds hl)
    (alone_sumPart name endName J c m.st m.shown ds hl)
  rw [state_sumPart name endName J m.st ds hl] at h
  exact h

/-- `StatedBy` reads three numbers of a round's entry alone. -/
theorem statedBy_nums : ∀ (ns : List Nat) (rs : List (Fmt.DeclaredRound × List Oracle)),
    rs.map (fun r => (r.1.entry.msg, r.1.entry.answers, r.1.entry.roots)) =
      ns.map (fun n => (24 * n, 0, 0)) → (∀ r ∈ rs, r.2 = []) → StatedBy ns rs
  | [], [], _, _ => trivial
  | n :: ns, r :: rs, h, ho => by
    rw [List.map_cons, List.map_cons, List.cons.injEq, Prod.mk.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨h1, h2, h3⟩, ht⟩ := h
    refine ⟨?_, ho r List.mem_cons_self,
      statedBy_nums ns rs ht fun x hx => ho x (List.mem_cons_of_mem _ hx)⟩
    simp [Fmt.DeclaredRound.items, Fmt.Entry.cut, h1, h2, h3]
  | [], _ :: _, h, _ => by simp at h
  | _ :: _, [], h, _ => by simp at h

/-- The three numbers of the call's own entries. -/
theorem entries_nums (k : Call) :
    (entries k).map (fun e => (e.msg, e.answers, e.roots)) =
      (scalarsOf k).map (fun n => (24 * n, 0, 0)) := by
  unfold entries scalarsOf
  rw [List.map_append, List.map_append, List.map_append, List.map_append, List.map_map,
    List.map_map]
  cases k.ends <;> rfl

/-- **Every list of declared rounds whose entries have the call's entries' bytes, answers and roots,
and no oracle message, states the call's scalars.** -/
theorem statedBy_like (k : Call) (rs : List (Fmt.DeclaredRound × List Oracle))
    (h : rs.map (fun r => (r.1.entry.msg, r.1.entry.answers, r.1.entry.roots)) =
      (entries k).map (fun e => (e.msg, e.answers, e.roots)))
    (ho : ∀ r ∈ rs, r.2 = []) : StatedBy (scalarsOf k) rs :=
  statedBy_nums _ rs (h.trans (entries_nums k)) ho

/-- Its case: rounds that are made of the call's own entries. -/
theorem statedBy_entries (k : Call) :
    StatedBy (scalarsOf k) ((entries k).map fun x => ({ entry := x }, [])) := by
  refine statedBy_like k _ ?_ fun r hr => ?_
  · rw [List.map_map]
    rfl
  · obtain ⟨x, _, rfl⟩ := List.mem_map.1 hr
    rfl

end ProofFile.Honest.SumLaw

#print axioms ProofFile.Honest.SumLaw.sayE_items
#print axioms ProofFile.Honest.SumLaw.sayE_fits
#print axioms ProofFile.Honest.SumLaw.fitsFrom_mvOf
#print axioms ProofFile.Honest.SumLaw.lensBy_append
#print axioms ProofFile.Honest.SumLaw.lensBy_range
#print axioms ProofFile.Honest.SumLaw.addL_length
#print axioms ProofFile.Honest.SumLaw.sentOfL_length
#print axioms ProofFile.Honest.SumLaw.withPoints_d
#print axioms ProofFile.Honest.SumLaw.all_d
#print axioms ProofFile.Honest.SumLaw.lensBy_sumGs
#print axioms ProofFile.Honest.SumLaw.scalarsOf_length
#print axioms ProofFile.Honest.SumLaw.fits_sumPart
#print axioms ProofFile.Honest.SumLaw.bad_sumPart
#print axioms ProofFile.Honest.SumLaw.hid_sumPart
#print axioms ProofFile.Honest.SumLaw.plays_sumPart
#print axioms ProofFile.Honest.SumLaw.statedBy_nums
#print axioms ProofFile.Honest.SumLaw.entries_nums
#print axioms ProofFile.Honest.SumLaw.statedBy_like
#print axioms ProofFile.Honest.SumLaw.statedBy_entries
#print axioms ProofFile.Honest.SumLaw.moves_length
#print axioms ProofFile.Honest.SumLaw.shape_two
#print axioms ProofFile.Honest.SumLaw.StatedBy
#print axioms ProofFile.Honest.SumLaw.LensBy
