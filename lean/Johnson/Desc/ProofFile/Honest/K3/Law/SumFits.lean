-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/SumFits.lean: plain facts on the masked sumcheck's part
(`sumPart`, Honest/Sum.lean), for every job, for a caller that lays it into a row. Theorems, with
three definitions. No round of the sumcheck is written again here: its text is unfolded.

Terms. Honest/K3/GLOSSARY.md ("book, coins", "job, summand", "part, stretch").

What is shown.
  `AllTwo`, `allTwo_append`, `allTwo_range`, `allTwo_length`, `allTwo_zip`, `allTwo_right`: two
    lists, entry by entry. (`AllTwo R l m` says what Lean's own `List.Forall₂ R l m` says, as a
    recursive definition.)
  `len_padTo`, `len_addL`, `len_scaleL`, `len_sentOfL`, `withPoints_d`, `withPoints_length`:
    lengths, and the variables' numbers of coefficients.
  `Sends n mv`: at all coins, at all that was shown and at every state the move answers, with n
    scalars and no table.
  `sumPart_sends`: the part's moves send, round by round, as many scalars as `scalarsOf` states,
    where no variable has just one coefficient.
  `fits_sayE`: n scalars have the shape of an entry of 24 n bytes without a root or an answer.
  `SameSays`, `aloneFrom_congr`: moves that say and hand on the same, played alone, yield the same.
  `sumPart_coins`: the part reads its coins through the two lists `coinsE` and `endCoins` alone, and
    its stretches' names not at all.
  `sumPart_alone_congr`: the same for the part played alone, at two jobs that are equal.
  `aloneFrom_some`: moves that always answer, played alone at as many challenges, yield rounds.
  `endFrom_unit`: where nothing is handed on, the state behind the moves has heard the challenges.

Hypotheses that remain.
  `hv`: (in `sumPart_sends`) no variable of the job's shape has just one coefficient. `h`: (in
    `len_sentOfL`) the same of one variable; its proof spends it at a plainly summed variable alone.
  `he`, `ha`, `hr`: (in `fits_sayE`) the entry states 24 bytes a scalar, no answer and no root.
  `h1`, `h2`, `hJ`: (in `sumPart_coins`, `sumPart_alone_congr`) the two lists of coins are equal;
    the two jobs are.
  `hq`: (in `allTwo_right`) R gives Q of its right side.
  Without a name, in front of arrows: in `aloneFrom_some`: every move always answers; as many
    challenges as moves; in `endFrom_unit`: as many challenges as moves; in the lemmas on `AllTwo`:
    `AllTwo` of what goes in (in `allTwo_range`: R holds of the two makers' values, index by index);
    in `aloneFrom_congr`: `SameSays`.

Two texts. `withPoints_length` has the statement and the proof of `Spec.withPoints_len`
(Honest/K3/Law/SpecStage.lean). The files on the masked sumcheck's laws (Honest/SumLaw/;
of these this file has Terms.lean beneath it and no other) state the like, with proofs of
their own: `padTo_length` (Lists.lean), `addL_length`, `sentOfL_length` (at two coefficients or
more), `withPoints_d` (at one default), `sayE_fits`, `lensBy_sumGs` (Fits.lean), `withPoints_length`
(Out.lean).

Imported. Honest/Sum.lean lies beneath this file.
So do four more:
Honest/SumLaw/Terms.lean (`alone`, `aloneFrom`, `SumCoins`),
Honest/Frame.lean, Honest/Side.lean and Honest/Law/Play.lean (through Honest/K3/Law/PlayPart.lean).

Users. This file is imported by Honest/K3/Law/PlayLift.lean, Honest/K3/Law/RowPlays.lean and
Honest/K3/Law/Keep/RowTwin.lean.

Limits. Every variable that has just one coefficient is left out by `hv`, of whatever sort. It is
needed at one that is summed plainly: there the part's text sends one scalar where `scalarsOf`
states none. Nothing is said on what the scalars are worth. `Sends`, `SameSays` and the hypothesis
of `aloneFrom_some` on the moves range over every term of the frame's `Seen`: over every list of
rounds and every value of the columns opened.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.PlayPart

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes (E zeroE)
open VerifiableInference.Desc (Oracle)
open VerifiableInference.Desc.Part.MaskedSum (Var Ends Call)
open ProofFile.Honest.SumLaw (alone aloneFrom SumCoins)

variable {V W X C C' : Type}

/-! ## Two lists, entry by entry -/

/-- The two lists are as long as each other, and R holds entry by entry. -/
def AllTwo {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | a :: l, b :: m => R a b ∧ AllTwo R l m
  | _, _ => False

theorem allTwo_append {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ l₂ : List α} {m₁ m₂ : List β}, AllTwo R l₁ m₁ → AllTwo R l₂ m₂ →
      AllTwo R (l₁ ++ l₂) (m₁ ++ m₂)
  | [], _, [], _, _, h => h
  | [], _, _ :: _, _, h, _ => h.elim
  | _ :: _, _, [], _, h, _ => h.elim
  | _ :: _, _, _ :: _, _, h, h' => ⟨h.1, allTwo_append h.2 h'⟩

theorem allTwo_range {α β γ : Type} {R : β → γ → Prop} (f : α → β) (g : Nat → γ) :
    ∀ (vs : List α) (k : Nat), (∀ i (h : i < vs.length), R (f vs[i]) (g (k + i))) →
      AllTwo R (vs.map f) ((List.range' k vs.length).map g)
  | [], _, _ => trivial
  | v :: vs, k, h => by
    rw [List.length_cons, List.range'_succ]
    refine ⟨h 0 (by simp), allTwo_range f g vs (k + 1) fun i hi => ?_⟩
    have := h (i + 1) (by simpa using hi)
    rw [show k + (i + 1) = k + 1 + i by omega] at this
    simpa using this

theorem allTwo_length {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {m : List β}, AllTwo R l m → l.length = m.length
  | [], [], _ => rfl
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | _ :: _, _ :: _, h => by simp [allTwo_length h.2]

theorem allTwo_zip {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {m : List β}, AllTwo R l m → ∀ r ∈ l.zip m, R r.1 r.2
  | [], [], _, _, hr => by simp at hr
  | [], _ :: _, h, _, _ => h.elim
  | _ :: _, [], h, _, _ => h.elim
  | _ :: _, _ :: _, h, r, hr => by
    rw [List.zip_cons_cons, List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact h.1
    · exact allTwo_zip h.2 r hr

theorem allTwo_right {α β : Type} {R : α → β → Prop} {Q : β → Prop} (hq : ∀ a b, R a b → Q b) :
    ∀ {l : List α} {m : List β}, AllTwo R l m → ∀ b ∈ m, Q b
  | [], [], _, _, hb => by simp at hb
  | [], _ :: _, h, _, _ => h.elim
  | _ :: _, [], h, _, _ => h.elim
  | _ :: _, _ :: _, h, b, hb => by
    rw [List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact hq _ _ h.1
    · exact allTwo_right hq h.2 b hb

/-! ## Lengths -/

theorem len_padTo (n : Nat) (a : List E) : (padTo n a).length = n := by
  unfold padTo
  simp only [List.length_take, List.length_append, List.length_replicate]
  omega

theorem len_addL : ∀ (a b : List E), (addL a b).length = max a.length b.length
  | [], b => by simp [addL]
  | _ :: _, [] => by simp [addL]
  | _ :: a, _ :: b => by simp [addL, len_addL a b]

theorem len_scaleL (k : E) (a : List E) : (scaleL k a).length = a.length := by simp [scaleL]

theorem len_sentOfL (v : Var) (g : List E) (h : v.d ≠ 1) : (sentOfL v g).length = v.d - 1 := by
  cases v with
  | plain d =>
    have hd : d ≠ 1 := h
    simp only [sentOfL, List.length_append, List.length_take, List.length_drop, len_padTo, Var.d]
    omega
  | point z d => simp [sentOfL, len_padTo, Var.d]

theorem withPoints_d (dflt : Var) : ∀ (vs : List Var) (zs : List E) (i : Nat),
    ((withPoints vs zs).getD i dflt).d = (vs.getD i dflt).d
  | [], _, _ => by simp [withPoints]
  | .plain d :: vs, zs, 0 => by simp [withPoints]
  | .plain d :: vs, zs, i + 1 => by simpa [withPoints] using withPoints_d dflt vs zs i
  | .point _ d :: vs, z :: zs, 0 => by simp [withPoints, Var.d]
  | .point _ d :: vs, z :: zs, i + 1 => by simpa [withPoints] using withPoints_d dflt vs zs i
  | .point z d :: vs, [], 0 => by simp [withPoints]
  | .point z d :: vs, [], i + 1 => by simpa [withPoints] using withPoints_d dflt vs [] i

theorem withPoints_length : ∀ (vs : List Var) (zs : List E), (withPoints vs zs).length = vs.length
  | [], _ => rfl
  | .plain _ :: vs, zs => by simp [withPoints, withPoints_length vs zs]
  | .point _ _ :: vs, _ :: zs => by simp [withPoints, withPoints_length vs zs]
  | .point _ _ :: vs, [] => by simp [withPoints, withPoints_length vs []]

/-! ## What the part's moves send -/

/-- At all coins, at all that was shown and at every state the move answers, with n scalars and no
table. All that was shown: every term of the frame's `Seen`, whatever rounds and whatever columns
opened it holds. -/
def Sends (n : Nat) (mv : Move C W X) : Prop :=
  ∀ (c : C) (sn : Seen) (u : State W X), ∃ l : List E, mv.say c sn u = .ok (sayE l) ∧ l.length = n

/-- **The part's moves send, round by round, as many scalars as `scalarsOf` states**, where no
variable has just one coefficient. -/
theorem sumPart_sends (name endName : String) (J : SumJob W X)
    (hv : ∀ v ∈ J.shape.vs, v.d ≠ 1) :
    AllTwo Sends (scalarsOf J.shape) (sumPart (V := V) name endName J).moves := by
  obtain ⟨⟨lead, vs, ends⟩, points, ld, round, inY, endsF⟩ := J
  have hmid : ∀ (tl : List Var) (zs : List E) (i : Nat) (hi : i < vs.length) (g : List E),
      (sentOfL ((withPoints vs zs ++ tl).getD i (.plain 0)) g).length = vs[i].d - 1 := by
    intro tl zs i hi g
    have e1 : (withPoints vs zs ++ tl).getD i (.plain 0) =
        (withPoints vs zs).getD i (.plain 0) := by
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by rw [withPoints_length]; exact hi)]
    have e2 : ((withPoints vs zs).getD i (.plain 0)).d = vs[i].d := by
      rw [withPoints_d]
      simp [List.getD_eq_getElem?_getD, hi]
    rw [e1, len_sentOfL _ _ (by rw [e2]; exact hv _ (List.getElem_mem hi)), e2]
  cases ends with
  | none =>
    unfold sumPart scalarsOf
    simp only [Option.map_none, Option.getD_none, List.range_eq_range']
    refine allTwo_append (allTwo_append ⟨?_, trivial⟩ ?_) trivial
    · intro c sn u
      exact ⟨_, rfl, by simp [len_addL, len_padTo]⟩
    · refine allTwo_range _ _ vs 0 fun i hi c sn u => ⟨_, rfl, ?_⟩
      have h0 : ∀ (zs g : List E),
          (sentOfL ((withPoints vs zs).getD i (.plain 0)) g).length = vs[i].d - 1 :=
        fun zs g => by simpa using hmid [] zs i hi g
      simp only [SumJob.callAt, Call.all, Nat.zero_add]
      exact h0 _ _
  | some e =>
    unfold sumPart scalarsOf
    simp only [Option.map_some, Option.getD_some, List.range_eq_range']
    refine allTwo_append (allTwo_append ⟨?_, trivial⟩ ?_) ⟨?_, ?_, trivial⟩
    · intro c sn u
      exact ⟨_, rfl, by simp [len_addL, len_padTo]⟩
    · refine allTwo_range _ _ vs 0 fun i hi c sn u => ⟨_, rfl, ?_⟩
      simp only [SumJob.callAt, Call.all, Nat.zero_add]
      exact hmid [.point zeroE (e.dY + 1)] _ i hi _
    · intro c sn u
      exact ⟨_, rfl, by simp [sentOfL, len_padTo]⟩
    · intro c sn u
      exact ⟨_, rfl, by simp [len_addL, len_padTo, len_scaleL]⟩

/-- n scalars have the shape of an entry of 24 n bytes that has no root and no answer. -/
theorem fits_sayE (l : List E) (e : Fmt.Entry) (he : e.msg = 24 * l.length) (ha : e.answers = 0)
    (hr : e.roots = 0) : (sayE l).fits { entry := e } [] = true := by
  have h1 : ((sayE l).vals.map fun v => VerifiableInference.Desc.itemOf v.got) =
      List.replicate l.length Fmt.Item.e := by
    refine List.eq_replicate_iff.2 ⟨by simp [sayE], fun b hb => ?_⟩
    simp only [sayE, List.map_map, List.mem_map] at hb
    obtain ⟨_, _, rfl⟩ := hb
    rfl
  have h2 : (({ entry := e } : Fmt.DeclaredRound).items.filter (· != .root)) =
      List.replicate l.length Fmt.Item.e := by
    simp [Fmt.DeclaredRound.items, Fmt.Entry.cut, he, ha, hr]
  unfold Sending.fits
  rw [h1, h2]
  simp [sayE]

/-! ## The coins -/

/-- The moves of two lists say and hand on the same, each list at its own coins. What a move says is
compared as a function of what is shown (a `Seen`) and of the state: so at every value of the
columns opened too. -/
def SameSays (c : C) (c' : C') (ms : List (Move C W X)) (ms' : List (Move C' W X)) : Prop :=
  ms.map (fun mv => (mv.say c, mv.hand)) = ms'.map fun mv => (mv.say c', mv.hand)

theorem aloneFrom_congr (c : C) (c' : C') : ∀ (ms : List (Move C W X)) (ms' : List (Move C' W X)),
    SameSays c c' ms ms' → ∀ (t : State W X) (seen : Seen) (ds : List Fmt.Drawn),
      aloneFrom c ms t seen ds = aloneFrom c' ms' t seen ds
  | [], [], _, _, _, ds => by cases ds <;> simp [aloneFrom]
  | [], _ :: _, h, _, _, _ => by simp [SameSays] at h
  | _ :: _, [], h, _, _, _ => by simp [SameSays] at h
  | mv :: ms, mv' :: ms', h, t, seen, ds => by
    simp only [SameSays, List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    cases ds with
    | nil => simp [aloneFrom]
    | cons d ds =>
      unfold aloneFrom
      rw [h1, h2]
      cases mv'.say c' seen t with
      | error e => rfl
      | ok x => simp only [aloneFrom_congr c c' ms ms' h3]

/-- **The part reads its coins through two lists alone, and its stretches' names not at all.** -/
theorem sumPart_coins (name endName name' endName' : String) (J : SumJob W X)
    (c : SumCoins name endName J) (c' : SumCoins name' endName' J)
    (h1 : coinsE c.2.1.1 = coinsE c'.2.1.1)
    (h2 : endCoins endName J.shape.ends c.2.1.2 = endCoins endName' J.shape.ends c'.2.1.2) :
    SameSays c c' (sumPart (V := V) name endName J).moves
      (sumPart (V := V) name' endName' J).moves := by
  revert h1 h2
  revert c c'
  obtain ⟨⟨lead, vs, ends⟩, points, ld, round, inY, endsF⟩ := J
  cases ends with
  | none =>
    intro c c' h1 _
    unfold SameSays sumPart
    simp only [List.map_append, List.map_map, List.map_cons, List.map_nil, Function.comp_def,
      Option.map_none, Option.getD_none, h1]
  | some e =>
    intro c c' h1 h2
    unfold SameSays sumPart
    simp only [List.map_append, List.map_map, List.map_cons, List.map_nil, Function.comp_def,
      Option.map_some, Option.getD_some, h1, h2]

/-- The part played alone, at two jobs that are equal, under whatever names. -/
theorem sumPart_alone_congr (name endName name' endName' : String) (J J' : SumJob W X) (hJ : J = J')
    (c : SumCoins name endName J) (c' : SumCoins name' endName' J')
    (h1 : coinsE c.2.1.1 = coinsE c'.2.1.1)
    (h2 : endCoins endName J.shape.ends c.2.1.2 = endCoins endName' J'.shape.ends c'.2.1.2)
    (t : State W X) (seen : Seen) (ds : List Fmt.Drawn) :
    alone (sumPart (V := V) name endName J) c t seen ds =
      alone (sumPart (V := V) name' endName' J') c' t seen ds := by
  subst hJ
  exact aloneFrom_congr c c' _ _ (sumPart_coins name endName name' endName' J c c' h1 h2) t seen ds

/-! ## Moves that always answer; a state that hands nothing on -/

theorem aloneFrom_some (c : C) : ∀ (ms : List (Move C W X)) (t : State W X) (seen : Seen)
    (ds : List Fmt.Drawn), (∀ mv ∈ ms, ∀ (sn : Seen) (u : State W X), ∃ y, mv.say c sn u = .ok y) →
    ds.length = ms.length → ∃ x, aloneFrom c ms t seen ds = some x
  | [], _, _, [], _, _ => ⟨[], by simp [aloneFrom]⟩
  | [], _, _, _ :: _, _, h => by simp at h
  | _ :: _, _, _, [], _, h => by simp at h
  | mv :: ms, t, seen, d :: ds, hs, hl => by
    obtain ⟨y, hy⟩ := hs mv List.mem_cons_self seen t
    obtain ⟨x, hx⟩ := aloneFrom_some c ms { t.hears d with own := mv.hand (t.hears d) }
      (seen.plus [⟨y.vals.map Said.got, d⟩]) ds (fun m hm => hs m (List.mem_cons_of_mem _ hm))
      (by simpa using hl)
    refine ⟨⟨y.vals.map Said.got, d⟩ :: x, ?_⟩
    unfold aloneFrom
    simp only [hy, hx, Option.map_some]

theorem endFrom_unit : ∀ (ms : List (Move C W Unit)) (t : State W Unit) (ds : List Fmt.Drawn),
    ds.length = ms.length → endFrom ms t ds = { t with heard := t.heard ++ ds }
  | [], t, [], _ => by simp [endFrom]
  | [], _, _ :: _, h => by simp at h
  | _ :: _, _, [], h => by simp at h
  | mv :: ms, t, d :: ds, h => by
    unfold endFrom
    rw [endFrom_unit ms _ ds (by simpa using h)]
    simp [State.hears, List.append_assoc]

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.sumPart_alone_congr
#print axioms ProofFile.Honest.K3.Law.aloneFrom_some
#print axioms ProofFile.Honest.K3.Law.endFrom_unit
#print axioms ProofFile.Honest.K3.Law.sumPart_sends
#print axioms ProofFile.Honest.K3.Law.fits_sayE
#print axioms ProofFile.Honest.K3.Law.aloneFrom_congr
#print axioms ProofFile.Honest.K3.Law.sumPart_coins
#print axioms ProofFile.Honest.K3.Law.allTwo_append
#print axioms ProofFile.Honest.K3.Law.allTwo_range
#print axioms ProofFile.Honest.K3.Law.allTwo_length
#print axioms ProofFile.Honest.K3.Law.allTwo_zip
#print axioms ProofFile.Honest.K3.Law.allTwo_right
#print axioms ProofFile.Honest.K3.Law.len_padTo
#print axioms ProofFile.Honest.K3.Law.len_addL
#print axioms ProofFile.Honest.K3.Law.len_scaleL
#print axioms ProofFile.Honest.K3.Law.len_sentOfL
#print axioms ProofFile.Honest.K3.Law.withPoints_d
#print axioms ProofFile.Honest.K3.Law.withPoints_length
