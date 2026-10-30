-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/SumLaw/Said.lean: THE MOVES OF THE MASKED SUMCHECK's PART ARE MOVES
THAT SAY SCALARS: what each move of `sumPart` (Honest/Sum.lean) says, copied out of the part's text
and held against it (`sumPart_moves`); moves of that sort played alone; and the variables' rounds by
a walk. The rounds themselves: Out.lean of this folder. Definitions that the statements need, and
statements with their proofs. Nothing here is part of a prover: the prover's text is `sumPart`.
Main names:
  `elemOf d`: the element that a challenge holds. `rvSaid l d`: a round in which the scalars l are
    said, as a view shows it.
  `mvOf g`: a move that says the scalars g and hands on what it was handed. `outOf gs t seen ds`:
    the rounds of such moves.
  `aloneFrom_mvOf`, `stateFrom_mvOf`: such moves played alone; the state behind them.
  `askG`, `saidFirst`, `saidVar`, `saidY`, `saidEnds`, `sumGs`, `sumPart_moves`: **`sumPart`'s moves
    are such moves**, with what each says, in the part's own words.
  `varOut eps poly L a past ds`: the variables' rounds, by a walk along the variables: L: those that
    are left, each with its share of the hiding polynomial; a: the accumulator of the part's walk.
  `sharesOf`: the variables with their shares. `askG_at`: what a move says at the state that the run
    has reached. `outOf_vars`: moves that say, each from the start of the part's walk, what the walk
    says step by step.

Limits. If Honest/Sum.lean's text of the part turns, `sumPart_moves` no longer compiles. `mvOf`
hands its g the frame's `Seen` whole; `askG` hands a job all of it but the part's own rounds
(`Seen.front`): the field `opened` in both: they carry it and do not read it. So a job of any kind
over this folder can, by its type, read the columns opened (`Front.seen.opened`); the field's
docstring (`Seen.opened`, Honest/Frame.lean) lays on a part that reads it the duty to err at `none`,
and no type and no test asks it; a move of this sort always answers, so such a job could not, and
would break that duty. None in this folder does; a job or a row that does is a new thing, to be
looked at by itself. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.SumLaw.Walk
import Johnson.Desc.ProofFile.Honest.SumLaw.Plays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.SumLaw
open OnBytes (E addE subE mulE zeroE oneE)
open VerifiableInference.Desc.Part.MaskedSum

variable {V W X : Type}

/-! ## Moves that say scalars -/

/-- The element that a challenge holds; 0 where it holds none. -/
def elemOf (d : Fmt.Drawn) : E := (d.elems.head?.map E.ofTriple).getD zeroE

theorem drawnE_eq (ds : List Fmt.Drawn) : drawnE ds = ds.map elemOf := rfl

/-- A round in which scalars are said, as a view shows it. -/
def rvSaid (l : List E) (d : Fmt.Drawn) : Fmt.RoundView := ⟨(sayE l).vals.map Said.got, d⟩

/-- A move that says scalars and hands on what it was handed. g: of the coins, what is shown
(`Seen`) and the state. -/
def mvOf {C : Type} (g : C → Seen → State W X → List E) : Move C W X :=
  ⟨fun c s t => .ok (sayE (g c s t)), fun t => t.own⟩

/-- The rounds of such moves. -/
def outOf : List (Seen → State W X → List E) → State W X → Seen → List Fmt.Drawn →
    List Fmt.RoundView
  | g :: gs, t, seen, d :: ds =>
    rvSaid (g seen t) d :: outOf gs (t.hears d) (seen.plus [rvSaid (g seen t) d]) ds
  | _, _, _, _ => []

theorem aloneFrom_mvOf {C : Type} (c : C) : ∀ (gs : List (C → Seen → State W X → List E))
    (t : State W X) (seen : Seen) (ds : List Fmt.Drawn), gs.length = ds.length →
    aloneFrom c (gs.map mvOf) t seen ds = some (outOf (gs.map (· c)) t seen ds)
  | [], _, _, [], _ => rfl
  | g :: gs, t, seen, d :: ds, h => by
    show (aloneFrom c (gs.map mvOf) (t.hears d) (seen.plus [rvSaid (g c seen t) d]) ds).map
      (rvSaid (g c seen t) d :: ·) = _
    rw [aloneFrom_mvOf c gs _ _ ds (by simp only [List.length_cons] at h; omega)]
    rfl
  | [], _, _, _ :: _, h => by simp only [List.length_cons, List.length_nil] at h; omega
  | _ :: _, _, _, [], h => by simp only [List.length_cons, List.length_nil] at h; omega

theorem stateFrom_mvOf {C : Type} : ∀ (gs : List (C → Seen → State W X → List E))
    (t : State W X)
    (ds : List Fmt.Drawn), gs.length = ds.length →
    stateFrom (gs.map mvOf) t ds = ⟨t.input, t.heard ++ ds, t.own⟩
  | [], t, [], _ => by
    show t = _
    rw [List.append_nil]
  | g :: gs, t, d :: ds, h => by
    show stateFrom (gs.map mvOf) (t.hears d) ds = _
    rw [stateFrom_mvOf gs _ ds (by simp only [List.length_cons] at h; omega)]
    show (⟨t.input, (t.heard ++ [d]) ++ ds, t.own⟩ : State W X) = _
    rw [List.append_assoc]
    rfl
  | [], _, _ :: _, h => by simp only [List.length_cons, List.length_nil] at h; omega
  | _ :: _, _, [], h => by simp only [List.length_cons, List.length_nil] at h; omega

theorem outOf_append : ∀ (g₁ g₂ : List (Seen → State W X → List E)) (t : State W X)
    (seen : Seen) (d₁ d₂ : List Fmt.Drawn), g₁.length = d₁.length →
    outOf (g₁ ++ g₂) t seen (d₁ ++ d₂) =
      outOf g₁ t seen d₁ ++
        outOf g₂ ⟨t.input, t.heard ++ d₁, t.own⟩ (seen.plus (outOf g₁ t seen d₁)) d₂
  | [], g₂, t, seen, [], d₂, _ => by
    show outOf g₂ t seen d₂ = outOf g₂ ⟨t.input, t.heard ++ [], t.own⟩ (seen.plus []) d₂
    rw [List.append_nil, Seen.plus_nil]
  | g :: g₁, g₂, t, seen, d :: d₁, d₂, h => by
    show rvSaid (g seen t) d ::
      outOf (g₁ ++ g₂) (t.hears d) (seen.plus [rvSaid (g seen t) d]) (d₁ ++ d₂) = _
    rw [outOf_append g₁ g₂ _ _ d₁ d₂ (by simp only [List.length_cons] at h; omega)]
    show _ = rvSaid (g seen t) d ::
      (outOf g₁ (t.hears d) (seen.plus [rvSaid (g seen t) d]) d₁ ++ _)
    have e : (t.hears d).heard ++ d₁ = t.heard ++ d :: d₁ := by
      show (t.heard ++ [d]) ++ d₁ = _
      rw [List.append_assoc]
      rfl
    rw [e, Seen.plus_plus]
    rfl
  | [], _, _, _, _ :: _, _, h => by simp only [List.length_cons, List.length_nil] at h; omega
  | _ :: _, _, _, _, [], _, h => by simp only [List.length_cons, List.length_nil] at h; omega

/-! ## The part's moves -/

/-- The variables with their shares of the hiding polynomial, of the first stretch of coins. -/
def sharesOf (lead : Nat) (all : List Var) (u : List E) : List (Var × List E) :=
  all.zip (wOf all (u.drop lead))

/-- What a move of the part says, in the part's own words: n: the move's number. -/
def askG (name endName : String) (J : SumJob W X)
    (f : List Var → Front X → List E → List E → List E → W → List E) (n : Nat) :
    SumCoins name endName J → Seen → State W X → List E :=
  fun c s t =>
    let fr : Front X := ⟨t.heard.take (t.heard.length - n), t.own, s.front n⟩
    f (J.callAt t.input fr).all fr (coinsE c.2.1.1) (endCoins endName J.shape.ends c.2.1.2)
      (drawnE (t.lately n)) t.input

/-- The first message. -/
def saidFirst (J : SumJob W X) : List Var → Front X → List E → List E → List E → W → List E :=
  fun all fr u _ _ w =>
    addL (padTo J.shape.lead (J.lead w fr)) (u.take J.shape.lead) ++
      [tailSum (sharesOf J.shape.lead all u)]

/-- The message of the variable number i. -/
def saidVar (J : SumJob W X) (i : Nat) :
    List Var → Front X → List E → List E → List E → W → List E :=
  fun all fr u _ ds w =>
    sentOfL (all.getD i (.plain 0)) (addL (hAt (sharesOf J.shape.lead all u) (ds.drop 1) zeroE)
      (scaleL (ds.headD zeroE) (J.round w fr (ds.drop 1))))

/-- The message of the further variable Y. -/
def saidY (J : SumJob W X) (e : Ends) :
    List Var → Front X → List E → List E → List E → W → List E :=
  fun all fr u m ds w =>
    sentOfL (.point zeroE (e.dY + 1)) (addL (hAt (sharesOf J.shape.lead all u) (ds.drop 1) zeroE)
      (scaleL (ds.headD zeroE) (J.inY w fr (ds.drop 1) m)))

/-- The end values' message. -/
def saidEnds (J : SumJob W X) (e : Ends) :
    List Var → Front X → List E → List E → List E → W → List E :=
  fun _ fr _ m ds w =>
    addL (padTo e.n (J.ends w fr ((ds.drop 1).take J.shape.vs.length)))
      (scaleL (ds.getLastD zeroE) (padTo e.n m))

/-- What the part's moves say. -/
def sumGs (name endName : String) (J : SumJob W X) :
    List (SumCoins name endName J → Seen → State W X → List E) :=
  [askG name endName J (saidFirst J) 0] ++
    ((List.range J.shape.vs.length).map fun i => askG name endName J (saidVar J i) (i + 1)) ++
    ((J.shape.ends.map fun e =>
      [askG name endName J (saidY J e) (J.shape.vs.length + 1),
        askG name endName J (saidEnds J e) (J.shape.vs.length + 2)]).getD [])

/-- **The part's moves are moves that say scalars.** -/
theorem sumPart_moves (name endName : String) (J : SumJob W X) :
    (sumPart (V := V) name endName J).moves = (sumGs name endName J).map mvOf := by
  unfold sumGs
  rw [List.map_append, List.map_append, List.map_map]
  cases h : J.shape.ends with
  | none =>
    unfold sumPart
    simp only [h]
    rfl
  | some e =>
    unfold sumPart
    simp only [h]
    rfl

/-! ## What a move says at the state that the run has reached -/

/-- At a state that has heard n challenges of the part's own, behind n rounds of its own. -/
theorem askG_at (name endName : String) (J : SumJob W X)
    (f : List Var → Front X → List E → List E → List E → W → List E) (n : Nat)
    (c : SumCoins name endName J) (w : W) (H own : List Fmt.Drawn) (x0 : X)
    (S : Seen) (shown : List Fmt.RoundView) (h : own.length = n) (hs : shown.length = n) :
    askG name endName J f n c (S.plus shown) ⟨w, H ++ own, x0⟩ =
      f (J.callAt w ⟨H, x0, S⟩).all ⟨H, x0, S⟩ (firstRun c) (endRun c) (drawnE own) w := by
  have e0 : (S.plus shown).front n = S := Seen.front_plus S shown n hs
  have e1 : (H ++ own).take ((H ++ own).length - n) = H := by
    rw [List.length_append, h, Nat.add_sub_cancel, List.take_left']
    rfl
  have e2 : State.lately (⟨w, H ++ own, x0⟩ : State W X) n = own := by
    show (H ++ own).drop ((H ++ own).length - n) = own
    rw [List.length_append, h, Nat.add_sub_cancel, List.drop_left']
    rfl
  show f (J.callAt w ⟨(H ++ own).take ((H ++ own).length - n), x0,
      (S.plus shown).front n⟩).all
    ⟨(H ++ own).take ((H ++ own).length - n), x0, (S.plus shown).front n⟩
    (firstRun c) (endRun c) (drawnE (State.lately (⟨w, H ++ own, x0⟩ : State W X) n)) w = _
  rw [e0, e1, e2]

/-! ## The variables' rounds, by a walk -/

/-- The variables' rounds. -/
def varOut (eps : E) (poly : List E → List E) :
    List (Var × List E) → E → List E → List Fmt.Drawn → List Fmt.RoundView
  | (v, w) :: rest, a, past, d :: ds =>
    rvSaid (sentOfL v (addL (hAt ((v, w) :: rest) [] a) (scaleL eps (poly past)))) d ::
      varOut eps poly rest (addE (mulE a (psiAt v (elemOf d))) (valueAt w (elemOf d)))
        (past ++ [elemOf d]) ds
  | _, _, _, _ => []

theorem varOut_cons (eps : E) (poly : List E → List E) (v : Var) (w : List E)
    (rest : List (Var × List E)) (a : E) (past : List E) (d : Fmt.Drawn) (ds : List Fmt.Drawn) :
    varOut eps poly ((v, w) :: rest) a past (d :: ds) =
      rvSaid (sentOfL v (addL (hAt ((v, w) :: rest) [] a) (scaleL eps (poly past)))) d ::
        varOut eps poly rest (addE (mulE a (psiAt v (elemOf d))) (valueAt w (elemOf d)))
          (past ++ [elemOf d]) ds := by
  rw [varOut.eq_def]

theorem varOut_nil (eps : E) (poly : List E → List E) (L : List (Var × List E)) (a : E)
    (past : List E) : varOut eps poly L a past [] = [] := by
  rw [varOut.eq_def]
  cases L <;> rfl

/-- Moves that say, each from the start of the part's walk, what the walk says step by step. -/
theorem outOf_vars (gAt : Nat → Seen → State W X → List E) (w : W) (H : List Fmt.Drawn)
    (x0 : X) (S : Seen) (all : List Var) (Lall : List (Var × List E)) (eps : E)
    (poly : List E → List E) (bound : Nat)
    (Hg : ∀ (i : Nat) (own : List Fmt.Drawn) (shown : List Fmt.RoundView), i < bound →
      own.length = i + 1 → shown.length = i + 1 →
      gAt i (S.plus shown) ⟨w, H ++ own, x0⟩ =
        sentOfL (all.getD i (.plain 0)) (addL (hAt Lall ((drawnE own).drop 1) zeroE)
          (scaleL ((drawnE own).headD zeroE) (poly ((drawnE own).drop 1))))) :
    ∀ (n s : Nat) (Lrest : List (Var × List E)) (a : E) (past : List E)
      (own ds' : List Fmt.Drawn) (shown : List Fmt.RoundView), own.length = s + 1 →
      shown.length = s + 1 → drawnE own = eps :: past →
      s + n ≤ bound → ds'.length = n → n ≤ Lrest.length →
      (∀ x, hAt Lall (past ++ x) zeroE = hAt Lrest x a) →
      (∀ j, j < Lrest.length →
        all.getD (s + j) (.plain 0) = (Lrest.map (·.1)).getD j (.plain 0)) →
      outOf ((List.range' s n).map gAt) ⟨w, H ++ own, x0⟩ (S.plus shown) ds' =
        varOut eps poly Lrest a past ds'
  | 0, s, Lrest, a, past, own, [], shown, _, _, _, _, _, _, _, _ => by
    rw [varOut_nil]
    rfl
  | n + 1, s, (v, sh) :: rest, a, past, own, d :: ds'', shown, h1, hs, h2, h3, h4, h5, hA, hV => by
    rw [List.range'_succ, List.map_cons, varOut_cons]
    show rvSaid (gAt s (S.plus shown) ⟨w, H ++ own, x0⟩) d ::
      outOf ((List.range' (s + 1) n).map gAt) ⟨w, (H ++ own) ++ [d], x0⟩
        ((S.plus shown).plus [rvSaid (gAt s (S.plus shown) ⟨w, H ++ own, x0⟩) d]) ds'' = _
    have e1 := hA []
    rw [List.append_nil] at e1
    have e2 : all.getD s (.plain 0) = v := hV 0 (Nat.succ_pos _)
    have e3 : (drawnE own).drop 1 = past := by rw [h2]; rfl
    have e4 : (drawnE own).headD zeroE = eps := by rw [h2]; rfl
    rw [Hg s own shown (by omega) h1 hs, e3, e4, e1, e2, List.append_assoc, Seen.plus_plus]
    congr 1
    refine outOf_vars gAt w H x0 S all Lall eps poly bound Hg n (s + 1) rest _
      (past ++ [elemOf d]) (own ++ [d]) ds'' _ (by rw [List.length_append, h1]; rfl)
      (by rw [List.length_append, hs]; rfl) ?_ (by omega)
      (by simp only [List.length_cons] at h4; omega)
      (by simp only [List.length_cons] at h5; omega) ?_ ?_
    · rw [drawnE_eq, List.map_append, ← drawnE_eq, h2]
      rfl
    · intro x
      rw [List.append_assoc]
      show hAt Lall (past ++ elemOf d :: x) zeroE = _
      rw [hA (elemOf d :: x), hAt_cons]
    · intro j hj
      have := hV (j + 1) (by simp only [List.length_cons]; omega)
      have e : s + 1 + j = s + (j + 1) := by omega
      rw [e, this]
      rfl
  | 0, _, _, _, _, _, _ :: _, _, _, _, _, _, h4, _, _, _ => by
    simp only [List.length_cons] at h4
    omega
  | _ + 1, _, _, _, _, _, [], _, _, _, _, _, h4, _, _, _ => by
    simp only [List.length_nil] at h4
    omega
  | _ + 1, _, [], _, _, _, _ :: _, _, _, _, _, _, _, h5, _, _ => by
    simp only [List.length_nil] at h5
    omega

end ProofFile.Honest.SumLaw

#print axioms ProofFile.Honest.SumLaw.drawnE_eq
#print axioms ProofFile.Honest.SumLaw.aloneFrom_mvOf
#print axioms ProofFile.Honest.SumLaw.stateFrom_mvOf
#print axioms ProofFile.Honest.SumLaw.outOf_append
#print axioms ProofFile.Honest.SumLaw.sumPart_moves
#print axioms ProofFile.Honest.SumLaw.askG_at
#print axioms ProofFile.Honest.SumLaw.varOut_cons
#print axioms ProofFile.Honest.SumLaw.varOut_nil
#print axioms ProofFile.Honest.SumLaw.outOf_vars
#print axioms ProofFile.Honest.SumLaw.elemOf
#print axioms ProofFile.Honest.SumLaw.rvSaid
#print axioms ProofFile.Honest.SumLaw.mvOf
#print axioms ProofFile.Honest.SumLaw.outOf
#print axioms ProofFile.Honest.SumLaw.sharesOf
#print axioms ProofFile.Honest.SumLaw.askG
#print axioms ProofFile.Honest.SumLaw.saidFirst
#print axioms ProofFile.Honest.SumLaw.saidVar
#print axioms ProofFile.Honest.SumLaw.saidY
#print axioms ProofFile.Honest.SumLaw.saidEnds
#print axioms ProofFile.Honest.SumLaw.sumGs
#print axioms ProofFile.Honest.SumLaw.varOut
