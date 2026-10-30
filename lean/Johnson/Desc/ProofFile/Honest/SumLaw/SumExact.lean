-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/SumLaw/SumExact.lean: WHAT THE FRAME's MASKED SUMCHECK's PART SHOWS,
OVER THE TWO STRETCHES OF COINS THAT IT SPENDS, AND WHAT THE SIMULATOR BESIDE IT YIELDS, OVER ITS
OWN COINS: ONE DISTRIBUTION. At every job; at every shape that passes the library's `shapeOk`, and
at every shape that passes the weaker `shapeFair` (ShapeFair.lean); UNDER THE FOUR PREMISES ON
PUBLIC DATA TOLD BELOW, of which the test on the shape is one. Statements with their proofs.

THE OWNERS' SENTENCES ARE NOT TYPED IN THIS FOLDER. Never left off: the spender's half alone · the
owners' sentences are typed by no file of this folder, and none is called here · one part at a time,
all else fixed before the coins · it holds at every job, right or wrong, so it says nothing on
whether the job is the protocol's · nothing on hiding.

What that means here. Both stretches are TAKEN as uniform, as independent of each other and of all
that is fixed. What is lacking is the field `fresh` of `Good` at the parts that OWN the two
stretches: no file of this folder states it. A JOB MAY READ WHAT IS SHOWN IN FRONT OF THE PART
(`Front.seen`): THE ROUNDS AND, WHERE THEY ARE HANDED, THE COLUMNS OPENED: these are fixed before
the coins here; where an item that it reads was sent under an entry which is spent here, or a column
that it reads is of a table that was sent under such an entry, that is not so in a run, and this
file says nothing: for items the condition stands in Honest/Sum.lean's head; for columns no file of
this folder states it; it is the caller's to meet.

Premises, four, each on public data alone: `shapeOk J.shape`, or `shapeFair J.shape` · `StatedBy
(scalarsOf J.shape) rs` (Fits.lean) · `betaMarked J.shape rs` (BetaMarked.lean) · `drawsFit` at the
declared rounds. At the lifted part two more, on the lens. NOTHING IS ASKED OF THE JOB's FIVE
FUNCTIONS BUT THEIR TYPES: the part fills or cuts their lists to the shape's counts, and the
statement holds at lists that do not fit too. Where a sentence says WHAT is sent, the frame's tests
on these lists (Honest/SumFits.lean) are still owed.
Main names:
  `shapeFair_callAt`, `shown_msgs`, `law_sumOut`: the test on the shape reads no point; what is
    shown of the part's rounds written out (`sumOut`, Out.lean); the statement at these.
  `exact_sumPart`, `exact_sumPart_lift`: **the statement at the frame's `play`**, at the part as it
    is and at the part lifted into a wider input and state. `exact_sumPart_fair`,
    `exact_sumPart_lift_fair`: the same under the weaker test.
  `exact_sumPart_field`, `exact_sumPart_field_bare`, with `_fair`: **`ExactMember`
    (Honest/Small/Field.lean) at a member written out: the text of the field `exact` of `Good`
    without its premise on `opened`**, at every face, side, On and bud.
  `fresh_sumPart_field`: the text of the field `fresh` there (`FreshMember`), where by the book no
    part spends a run of this part's coins: the frame's own `fresh_of_nil` (Honest/Law/ToyLaw.lean),
    called. The part owns no coin. IT HOLDS OF EVERY PART BY THE SAME TERM AND CARRIES NOTHING.

Limits. In every statement here m (the frame's `Mid`) is any state of a run and seen any `Seen`:
their field `opened` (where the player hands them, the columns that the sub-protocols before the
round have read: in the first and in the shared chain that chain's own alone, in the second chain
the first's, the shared chain's and its own: `Seen.opened`, Honest/Frame.lean) may have any value:
no premise is laid on it. So `ExactMember` (Honest/Small/Field.lean) is shown here at more states
than the field `exact` of the frame's `Good` asks, which has a premise on `opened`. It gives the
field's text, in which that premise goes unused: the step is `exactAt_of_exact`
(Honest/Small/Field.lean). WHAT IS SAID HERE OF `ExactMember` (without the premise on `opened`; six
premises; at more states) HANGS ON Honest/Small/Field.lean's TEXT: if that text takes the premise,
these sentences and the four terms `fun ca m front ds asks _ _ hd _ _ _` turn with it. `shapeOk` and
`shapeFair` are sufficient; of `shapeFair`'s clauses the one on a variable without ends is shown
needed (SumExactAt.lean); 1 ≤ dY is sufficient, not shown needed; that 2 ≤ d is needed at a plain
variable is shown by no theorem here. Where `shapeFair` accepts and `shapeOk` rejects, the library's
own verifier text rejects the call: the statements under `shapeFair` bear the same four premises;
what they give a caller is a first premise with two clauses fewer to show (d ≤ 65 at a variable;
1 ≤ n at ends). At ends with no end value `betaMarked` is asked and idle (shown by no theorem here).
WHICH CLAUSES OF THE PREMISES ARE SHOWN NEEDED, AND HOW (SumExactAt.lean). By a run that does not go
through, so that the part's side is the symbol for a fault at every coin: of `StatedBy` a round too
many (`fails_long`); of `drawsFit` the count (`fails_count`). By a fault or by the number of rounds
shown: of `StatedBy` a round too few (`fails_rounds`, `fails_early`). By two different coins that
show the same, both sides being rounds: of `drawsFit` the mark at Y (`fails_unfit`); of `betaMarked`
the clause that the FIRST element is marked (`fails_unmarked`, at a round that samples one element);
of the test on the shape the variable without ends (`fails_empty`, at the one shape without a lead,
a variable or ends). By no theorem: the clause of `StatedBy` on oracle messages (`oracle_unstated`,
SumExactAt.lean, has declared rounds that do not meet it and bears no inequality); that the
statement fails where the second element alone is marked (`second_marked_rejected`, BetaMarked.lean:
the test rejects such a round; no inequality); a shape with a lead, no variable and no ends; the
clause of `StatedBy` on the items; the other clauses of `drawsFit`; the other clauses of
`betaMarked` (that the round samples an element, that the format knows its name, that the round is
there). The two laws of the lens are what `plays_lift_sumPart` (PlaysSum.lean) asks; they are
sufficient. THE FIRST, `get (set x y) = y`, IS NOT NEEDED FOR THAT STEP, the one step in which the
two are spent: `plays_lift_same` (LiftSame.lean) has the same equation from the second alone. At a
lens that does not meet the first (`seatLens_not`, LiftSame.lean) the four statements at the lifted
part speak of nothing. With a face as a variable `ExactMember` says something only where a face
exists (Honest/Frame.lean: two constructors). `Good` is built at no side. This file imports
FitsAt.lean for two small lemmas on a call's variables; no statement here names a test of
Honest/SumFits.lean.
-/
import Johnson.Desc.ProofFile.Honest.SumLaw.SumBij
import Johnson.Desc.ProofFile.Honest.SumLaw.BetaMarked
import Johnson.Desc.ProofFile.Honest.SumLaw.FitsAt
import Johnson.Desc.ProofFile.Honest.Law.Along
import Johnson.Desc.ProofFile.Honest.Law.ToyLaw
import Johnson.Desc.ProofFile.Honest.Small.Field

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.SumLaw
open OnBytes (E zeroE)
open OnBytes.Model (Reading)
open OnBytes.Slice (GE)
open VerifiableInference.Desc (Oracle)
open VerifiableInference.Desc.Part.MaskedSum
open ProofFile.Honest.Small (ExactMember FreshMember)

variable {S Cl V V' W W' X Y Pb : Type}

/-- Declared rounds that state a list of numbers are as many. -/
theorem statedBy_len : ∀ (ns : List Nat) (rs : List (Fmt.DeclaredRound × List Oracle)),
    StatedBy ns rs → rs.length = ns.length
  | [], [], _ => rfl
  | _ :: ns, _ :: rs, h => congrArg (· + 1) (statedBy_len ns rs h.2.2)
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- Declared rounds that state a list of numbers have no oracle message. -/
theorem stated_no_oracle : ∀ (ns : List Nat) (rs : List (Fmt.DeclaredRound × List Oracle)),
    StatedBy ns rs → ∀ r ∈ rs, r.2 = []
  | [], [], _, _, hr => by cases hr
  | _ :: ns, r0 :: rs, h, r, hr => by
    rcases List.mem_cons.1 hr with rfl | hr
    · exact h.2.1
    · exact stated_no_oracle ns rs h.2.2 r hr
  | [], _ :: _, h, _, _ => h.elim
  | _ :: _, [], h, _, _ => h.elim

/-- A list of challenges, cut in three. -/
theorem split_draws (ds : List Fmt.Drawn) (N e : Nat) (h : ds.length = 1 + N + e) :
    ∃ d0 dv dl, ds = d0 :: (dv ++ dl) ∧ dv.length = N ∧ dl.length = e := by
  cases ds with
  | nil =>
    simp only [List.length_nil] at h
    omega
  | cons d0 r =>
    simp only [List.length_cons] at h
    exact ⟨d0, r.take N, r.drop N, by rw [List.take_append_drop],
      by rw [List.length_take]; omega, by rw [List.length_drop]; omega⟩

/-- The test on the shape reads no point: it is the same at the call in a run and at the job's
shape. -/
theorem shapeFair_callAt (J : SumJob W X) (w : W) (fr : Front X) :
    shapeFair (J.callAt w fr) = shapeFair J.shape := by
  have e : ∀ l : List Var, (l.all fun v => decide (2 ≤ v.d)) =
      (l.map Var.d).all fun d => decide (2 ≤ d) := by
    intro l
    rw [List.all_map]
    rfl
  show ((withPoints J.shape.vs (J.points w fr)).all (fun v => decide (2 ≤ v.d)) &&
    (match J.shape.ends with
     | none => !(withPoints J.shape.vs (J.points w fr)).isEmpty
     | some e => decide (1 ≤ e.dY))) = shapeFair J.shape
  rw [e, withPoints_ds, ← e, withPoints_isEmpty]
  rfl

/-- The challenges are as many as the part has moves. -/
theorem draws_moves (name endName : String) (J : SumJob W X)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (hr : StatedBy (scalarsOf J.shape) rs)
    (ds : List Fmt.Drawn) (hd : drawsFit (rs.map (·.1)) ds = true) :
    ds.length = (sumGs name endName J).length := by
  rw [drawsFit_length _ _ hd, List.length_map, statedBy_len _ _ hr, scalarsOf_length name endName J]

/-- **What is shown of the part's rounds written out: the messages as values.** -/
theorem shown_msgs {name endName : String} (J : SumJob W X) (c : Spent name endName J.shape)
    (t : State W X) (seen : Seen) (d0 : Fmt.Drawn) (dv dl : List Fmt.Drawn)
    (hs : shapeFair (J.callAt t.input (frontOf t seen)) = true)
    (hv : dv.length = (J.callAt t.input (frontOf t seen)).all.length)
    (hl : dl.length = if J.shape.ends.isSome then 1 else 0) (nm : String) (a : Addr)
    (asks : List (List (List Nat))) :
    shownOf ((sumOut J c.all t seen (d0 :: (dv ++ dl))).map (saidPlayed nm a)) asks =
      (msgsAt J t seen d0 dv c).map fun l => ⟨gotsOf l, []⟩ := by
  have h := sumOut_vals J c.all t seen d0 dv dl hs hv hl
  have e : ∀ l : List Fmt.RoundView, (l.map fun r => (⟨r.vals, []⟩ : Shown)) =
      (l.map (·.vals)).map fun x => ⟨x, []⟩ := fun l => by
    rw [List.map_map]
    rfl
  rw [shown_said, e, h, List.map_map]
  rfl

/-- **The statement at the part's rounds written out.** -/
theorem law_sumOut (name endName : String) (J : SumJob W X) (hk : shapeFair J.shape = true)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (hr : StatedBy (scalarsOf J.shape) rs)
    (hb : betaMarked J.shape rs = true) (nm : String) (a a' : Addr) (t : State W X)
    (seen : Seen) (pb : Pb) (front : Before) (ds : List Fmt.Drawn)
    (hd : drawsFit (rs.map (·.1)) ds = true) (asks : List (List (List Nat))) :
    (Prob.unif (Spent name endName J.shape)).map
        (fun c => some (shownOf ((sumOut J c.all t seen ds).map (saidPlayed nm a)) asks)) =
      (Prob.unif (Cs ⟨0, runOf J.shape⟩)).map fun c =>
        (sumSim (Pb := Pb) a' J.shape).tell pb front ds asks c := by
  have hs : shapeFair (J.callAt t.input (frontOf t seen)) = true := by
    rw [shapeFair_callAt]
    exact hk
  have hlen := draws_moves name endName J rs hr ds hd
  rw [sumGs_length name endName J t.input (frontOf t seen)] at hlen
  obtain ⟨d0, dv, dl, rfl, hv, hl⟩ := split_draws ds _ _ hlen
  have hβ : J.shape.ends.isSome = true →
      Reading.gl.val ((drawnE (d0 :: dv)).getLastD zeroE) ≠ 0 := by
    intro he
    obtain ⟨R, hR, hne⟩ := beta_ne_zero J.shape rs _ hb hd he
    have hN : dv.length = J.shape.vs.length + 1 := by
      rw [hv, all_length]
      cases hx : J.shape.ends with
      | none =>
        rw [hx] at he
        cases he
      | some _ => rfl
    rw [last_is_Y d0 dv dl J.shape.vs.length R hN hR]
    exact hne
  rw [← Prob.map_unif_of_bijective (toSim_bij (name := name) (endName := endName) J t seen d0 dv hs
    hv hβ)]
  refine Eq.trans ?_ (PMF.map_comp (toSim J t seen d0 dv) (Prob.unif _) _).symm
  congr 1
  funext c
  show some _ = (sumSim (Pb := Pb) a' J.shape).tell pb front _ asks (toSim J t seen d0 dv c)
  rw [tell_toSim J t seen d0 dv c hs hv, shown_msgs J c t seen d0 dv dl hs hv hl]

/-- **The statement at the frame's `play`, at the part as it is, under the weaker test on the
shape.** The spender's half alone: see the head. ca: what the part carries: nothing. -/
theorem exact_sumPart_fair (name endName : String) (J : SumJob W X) (hk : shapeFair J.shape = true)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (hr : StatedBy (scalarsOf J.shape) rs)
    (hb : betaMarked J.shape rs = true) (nm : String) (a a' : Addr) (v : Option V) (m : Mid W X)
    (pb : Pb) (front : Before) (ds : List Fmt.Drawn) (hd : drawsFit (rs.map (·.1)) ds = true)
    (asks : List (List (List Nat))) (ca : CsAll (sumPart (V := V) name endName J).carries) :
    (Prob.unif (Cs (sumPart (V := V) name endName J).takes ×
        CsAll (sumPart (V := V) name endName J).spends)).map
        (fun c => (play ((sumPart (V := V) name endName J).steps nm a rs v (c.1, c.2, ca)) ds []
          m).toOption.map fun y => shownOf y.1 asks) =
      (Prob.unif (Cs (sumSim (Pb := Pb) a' J.shape).takes)).map fun c =>
        (sumSim (Pb := Pb) a' J.shape).tell pb front ds asks c := by
  have e : (fun c : Cs (sumPart (V := V) name endName J).takes ×
        CsAll (sumPart (V := V) name endName J).spends =>
      (play ((sumPart (V := V) name endName J).steps nm a rs v (c.1, c.2, ca)) ds []
        m).toOption.map fun y => shownOf y.1 asks) = fun c : Spent name endName J.shape =>
      some (shownOf ((sumOut J c.all m.st m.shown ds).map (saidPlayed nm a)) asks) :=
    funext fun c =>
      congrArg (fun r => r.toOption.map fun y => shownOf y.1 asks)
        (plays_sumPart_whole name endName J (c.1, c.2, ca) (fair_vs_two hk) nm a rs hr v ds
          (draws_moves name endName J rs hr ds hd) [] m)
  rw [e]
  exact law_sumOut name endName J hk rs hr hb nm a a' m.st m.shown pb front ds hd asks

/-- **THE STATEMENT AT THE FRAME's `play`, AT THE PART AS IT IS.** The spender's half alone: see the
head. ca: what the part carries: nothing. -/
theorem exact_sumPart (name endName : String) (J : SumJob W X) (hk : shapeOk J.shape = true)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (hr : StatedBy (scalarsOf J.shape) rs)
    (hb : betaMarked J.shape rs = true) (nm : String) (a a' : Addr) (v : Option V) (m : Mid W X)
    (pb : Pb) (front : Before) (ds : List Fmt.Drawn) (hd : drawsFit (rs.map (·.1)) ds = true)
    (asks : List (List (List Nat))) (ca : CsAll (sumPart (V := V) name endName J).carries) :
    (Prob.unif (Cs (sumPart (V := V) name endName J).takes ×
        CsAll (sumPart (V := V) name endName J).spends)).map
        (fun c => (play ((sumPart (V := V) name endName J).steps nm a rs v (c.1, c.2, ca)) ds []
          m).toOption.map fun y => shownOf y.1 asks) =
      (Prob.unif (Cs (sumSim (Pb := Pb) a' J.shape).takes)).map fun c =>
        (sumSim (Pb := Pb) a' J.shape).tell pb front ds asks c :=
  exact_sumPart_fair name endName J (shapeFair_of_ok hk) rs hr hb nm a a' v m pb front ds hd asks ca

/-- **The same at the part lifted into a wider input and state, under the weaker test on the
shape**, general in see and wit, at a lens with the two laws. -/
theorem exact_sumPart_lift_fair (see : V → V') (wit : W → W') (get : X → Y) (set : X → Y → X)
    (hgs : ∀ x y, get (set x y) = y) (hsg : ∀ x, set x (get x) = x) (name endName : String)
    (J : SumJob W' Y) (hk : shapeFair J.shape = true) (rs : List (Fmt.DeclaredRound × List Oracle))
    (hr : StatedBy (scalarsOf J.shape) rs) (hb : betaMarked J.shape rs = true) (nm : String)
    (a a' : Addr) (v : Option V) (m : Mid W X) (pb : Pb) (front : Before) (ds : List Fmt.Drawn)
    (hd : drawsFit (rs.map (·.1)) ds = true) (asks : List (List (List Nat)))
    (ca : CsAll ((sumPart (V := V') name endName J).lift see wit get set).carries) :
    (Prob.unif (Cs ((sumPart (V := V') name endName J).lift see wit get set).takes ×
        CsAll ((sumPart (V := V') name endName J).lift see wit get set).spends)).map
        (fun c => (play (((sumPart (V := V') name endName J).lift see wit get set).steps nm a rs v
          (c.1, c.2, ca)) ds [] m).toOption.map fun y => shownOf y.1 asks) =
      (Prob.unif (Cs (sumSim (Pb := Pb) a' J.shape).takes)).map fun c =>
        (sumSim (Pb := Pb) a' J.shape).tell pb front ds asks c := by
  have e : (fun c : Cs ((sumPart (V := V') name endName J).lift see wit get set).takes ×
        CsAll ((sumPart (V := V') name endName J).lift see wit get set).spends =>
      (play (((sumPart (V := V') name endName J).lift see wit get set).steps nm a rs v
        (c.1, c.2, ca)) ds [] m).toOption.map fun y => shownOf y.1 asks) =
      fun c : Spent name endName J.shape =>
        some (shownOf ((sumOut J c.all (m.st.narrow wit get) m.shown ds).map (saidPlayed nm a))
          asks) :=
    funext fun c =>
      congrArg (fun r => r.toOption.map fun y => shownOf y.1 asks)
        (plays_lift_sumPart see wit get set hgs hsg name endName J (c.1, c.2, ca) (fair_vs_two hk)
          nm a rs hr v ds (draws_moves name endName J rs hr ds hd) [] m)
  rw [e]
  exact law_sumOut name endName J hk rs hr hb nm a a' (m.st.narrow wit get) m.shown pb front ds hd
    asks

/-- **THE SAME AT THE PART LIFTED INTO A WIDER INPUT AND STATE**, general in see and wit, at a lens
with the two laws. -/
theorem exact_sumPart_lift (see : V → V') (wit : W → W') (get : X → Y) (set : X → Y → X)
    (hgs : ∀ x y, get (set x y) = y) (hsg : ∀ x, set x (get x) = x) (name endName : String)
    (J : SumJob W' Y) (hk : shapeOk J.shape = true) (rs : List (Fmt.DeclaredRound × List Oracle))
    (hr : StatedBy (scalarsOf J.shape) rs) (hb : betaMarked J.shape rs = true) (nm : String)
    (a a' : Addr) (v : Option V) (m : Mid W X) (pb : Pb) (front : Before) (ds : List Fmt.Drawn)
    (hd : drawsFit (rs.map (·.1)) ds = true) (asks : List (List (List Nat)))
    (ca : CsAll ((sumPart (V := V') name endName J).lift see wit get set).carries) :
    (Prob.unif (Cs ((sumPart (V := V') name endName J).lift see wit get set).takes ×
        CsAll ((sumPart (V := V') name endName J).lift see wit get set).spends)).map
        (fun c => (play (((sumPart (V := V') name endName J).lift see wit get set).steps nm a rs v
          (c.1, c.2, ca)) ds [] m).toOption.map fun y => shownOf y.1 asks) =
      (Prob.unif (Cs (sumSim (Pb := Pb) a' J.shape).takes)).map fun c =>
        (sumSim (Pb := Pb) a' J.shape).tell pb front ds asks c :=
  exact_sumPart_lift_fair see wit get set hgs hsg name endName J (shapeFair_of_ok hk) rs hr hb nm a
    a' v m pb front ds hd asks ca

/-! ## `ExactMember` and `FreshMember` at a member written out -/

/-- **`ExactMember` at a member written out, under the weaker test on the shape.**
-/
theorem exact_sumPart_field_fair (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (chain firstTree : Nat)
    (On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) (see : V → V') (wit : W → W')
    (get : X → Y) (set : X → Y → X) (hgs : ∀ x y, get (set x y) = y)
    (hsg : ∀ x, set x (get x) = x) (name endName : String) (J : SumJob W' Y)
    (hk : shapeFair J.shape = true) (rs : List (Fmt.DeclaredRound × List Oracle))
    (hr : StatedBy (scalarsOf J.shape) rs) (hb : betaMarked J.shape rs = true) (j : Nat)
    (a' : Addr) :
    ExactMember φ σ chain firstTree On bud
      ⟨j, rs, (sumPart (V := V') name endName J).lift see wit get set, sumSim a' J.shape⟩ :=
  fun ca m front ds asks _ _ hd _ _ _ =>
    exact_sumPart_lift_fair see wit get set hgs hsg name endName J hk rs hr hb σ.block.name
      ⟨σ.block.place, j⟩ a' (φ.sees m.st.input) m (φ.pub m.st.input) front ds hd asks ca

/-- **`ExactMember` AT A MEMBER WRITTEN OUT: THE TEXT OF THE FIELD `exact` OF `Good` WITHOUT ITS
PREMISE ON `opened`**: number j, the declared rounds rs, the masked sumcheck's part lifted into a
wider input and state, the simulator beside it at an address a': at every face, side, On and bud. Of
its six premises the one on the challenges is spent. The spender's half alone: see the head.
-/
theorem exact_sumPart_field (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (chain firstTree : Nat)
    (On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) (see : V → V') (wit : W → W')
    (get : X → Y) (set : X → Y → X) (hgs : ∀ x y, get (set x y) = y)
    (hsg : ∀ x, set x (get x) = x) (name endName : String) (J : SumJob W' Y)
    (hk : shapeOk J.shape = true) (rs : List (Fmt.DeclaredRound × List Oracle))
    (hr : StatedBy (scalarsOf J.shape) rs) (hb : betaMarked J.shape rs = true) (j : Nat)
    (a' : Addr) :
    ExactMember φ σ chain firstTree On bud
      ⟨j, rs, (sumPart (V := V') name endName J).lift see wit get set, sumSim a' J.shape⟩ :=
  fun ca m front ds asks _ _ hd _ _ _ =>
    exact_sumPart_lift see wit get set hgs hsg name endName J hk rs hr hb σ.block.name
      ⟨σ.block.place, j⟩ a' (φ.sees m.st.input) m (φ.pub m.st.input) front ds hd asks ca

/-- The like at the part as it is, under the weaker test on the shape. It says something only at
types at which a face exists. -/
theorem exact_sumPart_field_bare_fair (φ : Face V W Pb) (σ : Side S Cl V W X Pb)
    (chain firstTree : Nat)
    (On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) (name endName : String)
    (J : SumJob W X) (hk : shapeFair J.shape = true) (rs : List (Fmt.DeclaredRound × List Oracle))
    (hr : StatedBy (scalarsOf J.shape) rs) (hb : betaMarked J.shape rs = true) (j : Nat)
    (a' : Addr) :
    ExactMember φ σ chain firstTree On bud
      ⟨j, rs, sumPart (V := V) name endName J, sumSim a' J.shape⟩ :=
  fun ca m front ds asks _ _ hd _ _ _ =>
    exact_sumPart_fair name endName J hk rs hr hb σ.block.name ⟨σ.block.place, j⟩ a'
      (φ.sees m.st.input) m (φ.pub m.st.input) front ds hd asks ca

/-- **The like at the part as it is.** It says something only at types at which a face exists. -/
theorem exact_sumPart_field_bare (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (chain firstTree : Nat)
    (On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) (name endName : String)
    (J : SumJob W X) (hk : shapeOk J.shape = true) (rs : List (Fmt.DeclaredRound × List Oracle))
    (hr : StatedBy (scalarsOf J.shape) rs) (hb : betaMarked J.shape rs = true) (j : Nat)
    (a' : Addr) :
    ExactMember φ σ chain firstTree On bud
      ⟨j, rs, sumPart (V := V) name endName J, sumSim a' J.shape⟩ :=
  fun ca m front ds asks _ _ hd _ _ _ =>
    exact_sumPart name endName J hk rs hr hb σ.block.name ⟨σ.block.place, j⟩ a'
      (φ.sees m.st.input) m (φ.pub m.st.input) front ds hd asks ca

/-- **The text of the field `fresh` at that member**, where by the book no part spends a run of this
part's coins: the frame's own `fresh_of_nil` (Honest/Law/ToyLaw.lean), called. The part owns no
coin. None of the field's premises is spent. IT HOLDS OF EVERY PART BY THE SAME TERM AND CARRIES
NOTHING: what is lacking is the field `fresh` at the parts that OWN the two stretches. -/
theorem fresh_sumPart_field (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (Bk : ProverCoinCounts)
    (ord : List VerifiableInference.Desc.Place)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) (see : V → V') (wit : W → W')
    (get : X → Y) (set : X → Y → X) (name endName : String) (J : SumJob W' Y)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (j : Nat) (a' : Addr)
    (hown : ∀ p, Bk.spentBy ⟨σ.block.place, j⟩ p = []) :
    FreshMember φ σ Bk ord bud
      ⟨j, rs, (sumPart (V := V') name endName J).lift see wit get set, sumSim a' J.shape⟩ :=
  fun p sp ca m ds asks _ _ _ =>
    fresh_of_nil (Bk.spentBy ⟨σ.block.place, j⟩ p) (hown p)
      (fun c => σ.shows φ
        ⟨j, rs, (sumPart (V := V') name endName J).lift see wit get set, sumSim a' J.shape⟩
        (c, sp, ca) m ds asks)
      fun c => cutAll c (Bk.knownBy ord ⟨σ.block.place, j⟩ p)

end ProofFile.Honest.SumLaw

#print axioms ProofFile.Honest.SumLaw.statedBy_len
#print axioms ProofFile.Honest.SumLaw.stated_no_oracle
#print axioms ProofFile.Honest.SumLaw.split_draws
#print axioms ProofFile.Honest.SumLaw.shapeFair_callAt
#print axioms ProofFile.Honest.SumLaw.draws_moves
#print axioms ProofFile.Honest.SumLaw.shown_msgs
#print axioms ProofFile.Honest.SumLaw.law_sumOut
#print axioms ProofFile.Honest.SumLaw.exact_sumPart_fair
#print axioms ProofFile.Honest.SumLaw.exact_sumPart
#print axioms ProofFile.Honest.SumLaw.exact_sumPart_lift_fair
#print axioms ProofFile.Honest.SumLaw.exact_sumPart_lift
#print axioms ProofFile.Honest.SumLaw.exact_sumPart_field_fair
#print axioms ProofFile.Honest.SumLaw.exact_sumPart_field
#print axioms ProofFile.Honest.SumLaw.exact_sumPart_field_bare_fair
#print axioms ProofFile.Honest.SumLaw.exact_sumPart_field_bare
#print axioms ProofFile.Honest.SumLaw.fresh_sumPart_field
