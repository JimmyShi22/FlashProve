-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/SumLaw/SumExactAt.lean: beside SumExact.lean of this folder: INSTANCES
AT WHICH ALL ITS PREMISES ARE MET TOGETHER, AND INSTANCES AT WHICH THE STATEMENT FAILS WHERE ONE OF
ITS FOUR PREMISES ON PUBLIC DATA IS NOT MET. Definitions, and statements with their proofs. All
names stand in the namespace ProofFile.Honest.SumLaw.At.

The instances. A shape with a lead of two, one plain variable of three coefficients and two end
values with dY = 2; declared rounds made of the library's own entries for that call; four
challenges.
  `exact_at`: at ANY five functions of a job at that shape, at the frame's `play`, with no premise
    left. `exact_at_field`: `ExactMember` (Honest/Small/Field.lean: the text of the field `exact` of
    `Good` without its premise on `opened`) at the lifted part there.
  `exact_at_empty`: at the job whose five lists are all empty. WHICH OF THESE DO NOT FIT: the lead's
    list (two values are due) and the end values' (two): the frame's own test rejects that job at
    all arguments (`empty_unfit`). Clause by clause (`empty_clauses`): the list of points passes
    (the shape has no variable that is summed at a point); the two lists of coefficients, though
    shorter than the shape's counts, pass (nothing of them is cut).
  `exact_at_n0`: at the like shape with ends whose number of end values is 0: the library's
    `shapeOk` rejects it, `shapeFair` accepts, and the statement holds. `exact_at_66`: the like at
    one plain variable of 66 coefficients.

That none of the four premises can be dropped whole. Clause by clause much is shown by no theorem:
the list stands in SumExact.lean's Limits. Of the two premises on the lens at the lifted part
nothing is shown here. `law_inj`: if the two distributions are one, what the part's side yields
fixes the coins. So the statement fails wherever two different coins show the same. `fails_unfit`,
`fails_unmarked`, `fails_empty`, `fails_long` and `fails_early` state, beside the inequality, which
premises are met at their instances.
  `fails_beta`, `fails_unfit`, `fails_unmarked` (and `msgs_zero` beneath them) STAND AT THE JOB
    WHOSE LISTS ARE ALL EMPTY, at the instances' shape and at one fixed list of challenges: it is
    shown at no other job; for "needed" one instance is enough. `fails_beta`: at a challenge of Y
    that reads 0, at whichever declared rounds that state the call's scalars. `dsZero_unfit`,
    `fails_unfit`: at the library's own entries the premise on the challenges shuts that list out,
    all other premises are met, and the statement fails: so that premise is needed.
    `fails_unmarked`: at declared rounds whose element for Y is not marked, all other premises are
    met and the test on Y's round rejects.
  `fails_empty`: at the one shape without a lead, a variable or ends (`kNone`), at every job of that
    shape. At a shape with a lead, no variable and no ends no theorem speaks.
  `fails_count`: where the challenges are not as many as the rounds that are played, the part's side
    is the one symbol for a fault. `fails_long`: declared rounds one too many, at challenges that
    fit them. `fails_rounds`: where fewer rounds are played than the call has, the part's side is
    the symbol for a fault, or shows fewer rounds than the simulator yields. `fails_early`: declared
    rounds that end a round early, at challenges that fit them.
  `oracle_unstated`: an instance: declared rounds of which one has an oracle message do not state
    the call's scalars. It bears no inequality: the statement fails there: said here without a
    theorem; no theorem of this folder shows it.

THE OWNERS' SENTENCES ARE NOT TYPED IN THIS FOLDER. Never left off, as in SumExact.lean's head: the
spender's half alone · the owners' sentences are typed by no file of this folder, and none is called
here · one part at a time, all else fixed before the coins · it holds at every job, right or wrong,
so it says nothing on whether the job is the protocol's · nothing on hiding.
-/
import Johnson.Desc.ProofFile.Honest.SumLaw.SumExact

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.SumLaw.At
open OnBytes (E zeroE)
open OnBytes.Model (Reading)
open OnBytes.Slice (GE ofE toE)
open VerifiableInference.Desc (Oracle)
open VerifiableInference.Desc.Part.MaskedSum (Call Var Ends shapeOk entries entry)
open ProofFile.Honest.Small (ExactMember)

variable {S Cl V V' W W' X Pb : Type}

/-! ## 1 Instances -/

/-- A lead of two, one plain variable of three coefficients, two end values with dY = 2. -/
def kAt : Call := { lead := 2, vs := [.plain 3], ends := some { dY := 2, n := 2 } }

/-- Declared rounds made of the library's own entries for that call. -/
def rsAt : List (Fmt.DeclaredRound × List Oracle) := (entries kAt).map fun x => ({ entry := x }, [])

/-- A challenge of one element. -/
def one (x : UInt64) : Fmt.Drawn :=
  { elems := [(x, 0, 0)], poss := [], trits := [], digest := none }
/-- A challenge without an element. -/
def nil0 : Fmt.Drawn := { elems := [], poss := [], trits := [], digest := none }

/-- Four challenges: eps, the variable's, Y's, and the last round's, which holds no element. -/
def dsAt : List Fmt.Drawn := [one 11, one 5, one 9, nil0]

/-- The shape passes the library's test. -/
theorem kAt_ok : shapeOk kAt = true := by decide

/-- The challenges fit the declared rounds. -/
theorem dsAt_fit : drawsFit (rsAt.map (·.1)) dsAt = true := by decide +kernel

/-- A job at that shape, of any five functions. -/
def jobAt (p l : W → Front X → List E) (r : W → Front X → List E → List E)
    (y : W → Front X → List E → List E → List E) (e : W → Front X → List E → List E) :
    SumJob W X :=
  { shape := kAt, points := p, lead := l, round := r, inY := y, ends := e }

/-- **The statement at the instance, at any five functions, with no premise left.** -/
theorem exact_at (p l : W → Front X → List E) (r : W → Front X → List E → List E)
    (y : W → Front X → List E → List E → List E) (e : W → Front X → List E → List E)
    (name endName nm : String) (a a' : Addr) (v : Option V) (m : Mid W X) (pb : Pb)
    (front : Before) (asks : List (List (List Nat)))
    (ca : CsAll (sumPart (V := V) name endName (jobAt p l r y e)).carries) :
    (Prob.unif (Cs (sumPart (V := V) name endName (jobAt p l r y e)).takes ×
        CsAll (sumPart (V := V) name endName (jobAt p l r y e)).spends)).map
        (fun c => (play ((sumPart (V := V) name endName (jobAt p l r y e)).steps nm a rsAt v
          (c.1, c.2, ca)) dsAt [] m).toOption.map fun z => shownOf z.1 asks) =
      (Prob.unif (Cs (sumSim (Pb := Pb) a' kAt).takes)).map fun c =>
        (sumSim (Pb := Pb) a' kAt).tell pb front dsAt asks c :=
  exact_sumPart name endName (jobAt p l r y e) kAt_ok rsAt (statedBy_entries kAt)
    (betaMarked_entries kAt) nm a a' v m pb front dsAt dsAt_fit asks ca

/-- The job at that shape whose five lists are all empty. -/
def jobEmpty : SumJob W X :=
  jobAt (fun _ _ => []) (fun _ _ => []) (fun _ _ _ => []) (fun _ _ _ _ => []) fun _ _ _ => []

/-- **The statement at the job whose five lists are all empty.** -/
theorem exact_at_empty (name endName nm : String) (a a' : Addr) (v : Option V) (m : Mid W X)
    (pb : Pb) (front : Before) (asks : List (List (List Nat)))
    (ca : CsAll (sumPart (V := V) name endName (jobEmpty (W := W) (X := X))).carries) :
    (Prob.unif (Cs (sumPart (V := V) name endName (jobEmpty (W := W) (X := X))).takes ×
        CsAll (sumPart (V := V) name endName (jobEmpty (W := W) (X := X))).spends)).map
        (fun c => (play ((sumPart (V := V) name endName (jobEmpty (W := W) (X := X))).steps nm a
          rsAt v (c.1, c.2, ca)) dsAt [] m).toOption.map fun z => shownOf z.1 asks) =
      (Prob.unif (Cs (sumSim (Pb := Pb) a' kAt).takes)).map fun c =>
        (sumSim (Pb := Pb) a' kAt).tell pb front dsAt asks c :=
  exact_at _ _ _ _ _ name endName nm a a' v m pb front asks ca

/-- **The frame's own test on a job's lists rejects that job**, at all arguments: two lead values
and two end values are due. -/
theorem empty_unfit (w : W) (fr : Front X) (rs m : List E) :
    (jobEmpty (W := W) (X := X)).fitsAt w fr rs m = false := rfl

/-- That test's clauses on the job's five lists (Honest/SumFits.lean, `SumJob.fitsAt`), one by one,
at that job: the points' passes, the lead's fails, the rounds' passes, that on Y's list passes, the
end values' fails. -/
theorem empty_clauses (w : W) (fr : Front X) (rs m : List E) :
    (((jobEmpty (W := W) (X := X)).points w fr).length == pointsIn kAt.vs) = true ∧
    (((jobEmpty (W := W) (X := X)).lead w fr).length == kAt.lead) = false ∧
    (kAt.vs.zipIdx.all fun v =>
      noneCut v.1.d ((jobEmpty (W := W) (X := X)).round w fr (rs.take v.2))) = true ∧
    noneCut (2 + 1) ((jobEmpty (W := W) (X := X)).inY w fr rs m) = true ∧
    (((jobEmpty (W := W) (X := X)).ends w fr rs).length == 2) = false :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **`ExactMember` at the lifted part, at the instance**: at any five functions, any see and wit,
the lens onto Unit, every face, side, On and bud; no premise stands in front of it. It says
something only at types at which a face exists. -/
theorem exact_at_field (φ : Face V W Pb) (σ : Side S Cl V W X Pb) (chain firstTree : Nat)
    (On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) (see : V → V') (wit : W → W')
    (p l : W' → Front Unit → List E) (r : W' → Front Unit → List E → List E)
    (y : W' → Front Unit → List E → List E → List E) (e : W' → Front Unit → List E → List E)
    (name endName : String) (j : Nat) (a' : Addr) :
    ExactMember φ σ chain firstTree On bud
      ⟨j, rsAt, (sumPart (V := V') name endName (jobAt p l r y e)).lift see wit (fun _ => ())
        fun x _ => x, sumSim a' kAt⟩ :=
  exact_sumPart_field φ σ chain firstTree On bud see wit (fun _ => ()) (fun x _ => x)
    (fun _ _ => rfl) (fun _ => rfl) name endName (jobAt p l r y e) kAt_ok rsAt
    (statedBy_entries kAt) (betaMarked_entries kAt) j a'

/-- The like shape with ends whose number of end values is 0. -/
def kN0 : Call := { lead := 2, vs := [.plain 3], ends := some { dY := 2, n := 0 } }

/-- Declared rounds made of the library's own entries for that call. -/
def rsN0 : List (Fmt.DeclaredRound × List Oracle) := (entries kN0).map fun x => ({ entry := x }, [])

/-- The library's test rejects that shape; the weaker one accepts. -/
theorem kN0_tests : shapeOk kN0 = false ∧ shapeFair kN0 = true := by decide

/-- The four challenges fit these declared rounds too. -/
theorem dsN0_fit : drawsFit (rsN0.map (·.1)) dsAt = true := by decide +kernel

/-- A job at that shape, of any five functions. -/
def jobN0 (p l : W → Front X → List E) (r : W → Front X → List E → List E)
    (y : W → Front X → List E → List E → List E) (e : W → Front X → List E → List E) :
    SumJob W X :=
  { shape := kN0, points := p, lead := l, round := r, inY := y, ends := e }

/-- **The statement at a shape with ends whose number of end values is 0**, which the library's test
rejects: at any five functions, with no premise left. -/
theorem exact_at_n0 (p l : W → Front X → List E) (r : W → Front X → List E → List E)
    (y : W → Front X → List E → List E → List E) (e : W → Front X → List E → List E)
    (name endName nm : String) (a a' : Addr) (v : Option V) (m : Mid W X) (pb : Pb)
    (front : Before) (asks : List (List (List Nat)))
    (ca : CsAll (sumPart (V := V) name endName (jobN0 p l r y e)).carries) :
    (Prob.unif (Cs (sumPart (V := V) name endName (jobN0 p l r y e)).takes ×
        CsAll (sumPart (V := V) name endName (jobN0 p l r y e)).spends)).map
        (fun c => (play ((sumPart (V := V) name endName (jobN0 p l r y e)).steps nm a rsN0 v
          (c.1, c.2, ca)) dsAt [] m).toOption.map fun z => shownOf z.1 asks) =
      (Prob.unif (Cs (sumSim (Pb := Pb) a' kN0).takes)).map fun c =>
        (sumSim (Pb := Pb) a' kN0).tell pb front dsAt asks c :=
  exact_sumPart_fair name endName (jobN0 p l r y e) kN0_tests.2 rsN0 (statedBy_entries kN0)
    (betaMarked_entries kN0) nm a a' v m pb front dsAt dsN0_fit asks ca

/-- One plain variable of 66 coefficients; no lead, no ends. -/
def k66 : Call := { lead := 0, vs := [.plain 66], ends := none }

/-- Declared rounds made of the library's own entries for that call. -/
def rs66 : List (Fmt.DeclaredRound × List Oracle) := (entries k66).map fun x => ({ entry := x }, [])

/-- The library's test rejects that shape; the weaker one accepts. -/
theorem k66_tests : shapeOk k66 = false ∧ shapeFair k66 = true := by decide

/-- Two challenges of one element fit these declared rounds. -/
theorem ds66_fit : drawsFit (rs66.map (·.1)) [one 11, one 5] = true := by decide +kernel

/-- A job at that shape, of any five functions. -/
def job66 (p l : W → Front X → List E) (r : W → Front X → List E → List E)
    (y : W → Front X → List E → List E → List E) (e : W → Front X → List E → List E) :
    SumJob W X :=
  { shape := k66, points := p, lead := l, round := r, inY := y, ends := e }

/-- **The statement at a variable of 66 coefficients**, which the library's test rejects: at any
five functions, with no premise left. -/
theorem exact_at_66 (p l : W → Front X → List E) (r : W → Front X → List E → List E)
    (y : W → Front X → List E → List E → List E) (e : W → Front X → List E → List E)
    (name endName nm : String) (a a' : Addr) (v : Option V) (m : Mid W X) (pb : Pb)
    (front : Before) (asks : List (List (List Nat)))
    (ca : CsAll (sumPart (V := V) name endName (job66 p l r y e)).carries) :
    (Prob.unif (Cs (sumPart (V := V) name endName (job66 p l r y e)).takes ×
        CsAll (sumPart (V := V) name endName (job66 p l r y e)).spends)).map
        (fun c => (play ((sumPart (V := V) name endName (job66 p l r y e)).steps nm a rs66 v
          (c.1, c.2, ca)) [one 11, one 5] [] m).toOption.map fun z => shownOf z.1 asks) =
      (Prob.unif (Cs (sumSim (Pb := Pb) a' k66).takes)).map fun c =>
        (sumSim (Pb := Pb) a' k66).tell pb front [one 11, one 5] asks c :=
  exact_sumPart_fair name endName (job66 p l r y e) k66_tests.2 rs66 (statedBy_entries k66)
    (betaMarked_entries k66) nm a a' v m pb front [one 11, one 5] ds66_fit asks ca

/-! ## 2 If the two distributions are one, what the part shows fixes the coins -/

/-- The values of what is shown, in a row, as coins. -/
def decode (R : Nat) (y : Option (List Shown)) : Cs ⟨0, R⟩ :=
  ⟨fun i => i.elim0, fun i => (((y.getD []).flatMap (·.vals)).map fun g =>
    match g with
    | .e t => toE t
    | _ => 0).getD i.1 0⟩

/-- Lists cut by numbers, in a row again: the first so many members. -/
theorem roundsCut_join : ∀ (ns : List Nat) (L : List E), (roundsCut ns L).flatten = L.take ns.sum
  | [], L => by simp [roundsCut]
  | n :: ns, L => by
    show L.take n ++ (roundsCut ns (L.drop n)).flatten = _
    rw [roundsCut_join ns, List.sum_cons, List.take_add]

/-- **What the simulator yields tells its coins.** -/
theorem decode_tell (a' : Addr) (k : Call) (pb : Pb) (front : Before) (ds : List Fmt.Drawn)
    (asks : List (List (List Nat))) (c : Cs ⟨0, runOf k⟩) :
    decode (runOf k) ((sumSim (Pb := Pb) a' k).tell pb front ds asks c) = c := by
  refine cs_ext _ _ fun i => ?_
  have h1 : ((roundsCut (scalarsOf k) (coinsE c)).map
      fun l => (⟨l.map fun x => .e x.triple, []⟩ : Shown)).flatMap (·.vals) =
      (coinsE c).map fun x => .e x.triple := by
    rw [List.flatMap_map]
    show (roundsCut (scalarsOf k) (coinsE c)).flatMap (List.map fun x => Fmt.ItemValue.e x.triple) = _
    rw [List.flatMap_def, ← List.map_flatten, roundsCut_join, ← runOf_sum, List.take_of_length_le]
    unfold coinsE
    rw [List.length_ofFn]
  show ((((some ((roundsCut (scalarsOf k) (coinsE c)).map
    fun l => (⟨l.map fun x => .e x.triple, []⟩ : Shown))).getD []).flatMap (·.vals)).map _).getD
      i.1 0 = c.e i
  rw [Option.getD_some, h1, List.map_map, List.getD_eq_getElem?_getD, List.getElem?_map]
  unfold coinsE
  rw [List.getElem?_ofFn, dif_pos i.2]
  show toE (E.ofTriple (ofE (c.e ⟨i.1, i.2⟩))).triple = c.e i
  rw [E.triple_ofTriple, OnBytes.Slice.toE_ofE]

/-- **If the two distributions are one, what the part's side yields fixes the coins.** F: any
function of the coins that the part spends. -/
theorem law_inj (name endName : String) (k : Call) (F : Spent name endName k → Option (List Shown))
    (a' : Addr) (pb : Pb) (front : Before) (ds : List Fmt.Drawn) (asks : List (List (List Nat)))
    (h : (Prob.unif (Spent name endName k)).map F =
      (Prob.unif (Cs ⟨0, runOf k⟩)).map fun c =>
        (sumSim (Pb := Pb) a' k).tell pb front ds asks c) : Function.Injective F := by
  have h1 := congrArg (PMF.map (decode (runOf k))) h
  rw [PMF.map_comp, PMF.map_comp] at h1
  have e : (decode (runOf k) ∘ fun c => (sumSim (Pb := Pb) a' k).tell pb front ds asks c) = id :=
    funext fun c => decode_tell a' k pb front ds asks c
  have h2 : (Prob.unif (Cs ⟨0, runOf k⟩)).map
      (decode (runOf k) ∘ fun c => (sumSim (Pb := Pb) a' k).tell pb front ds asks c) =
      Prob.unif (Cs ⟨0, runOf k⟩) := by
    rw [e]
    exact PMF.map_id _
  have hs := Prob.surjective_of_map_unif (h1.trans h2)
  have hb := (Fintype.bijective_iff_surjective_and_card _).2 ⟨hs, card_spent name endName k⟩
  exact Function.Injective.of_comp hb.1

/-! ## 3 At a challenge of Y that reads 0 -/

/-- The same four challenges, but Y's holds the element 0. -/
def dsZero : List Fmt.Drawn := [one 11, one 5, one 0, nil0]

/-- Coins of the part's at that shape: all 0, but the second stretch's first, which is x. -/
def coinsAt (name endName : String) (x : GE) : Spent name endName kAt :=
  (Cs.empty, (⟨fun i => i.elim0, fun _ => 0⟩,
    ((⟨fun i => i.elim0, fun i => if i.1 = 0 then x else 0⟩ : Cs ⟨0, 2⟩), ())))

/-- The empty job's list for a round is empty. -/
theorem jobPoly_empty (w : W) (fr : Front X) (m p : List E) :
    jobPoly (jobEmpty (W := W) (X := X)) w fr m p = [] := by
  unfold jobPoly
  split <;> rfl

/-- At Y's challenge 0, AT THE JOB WHOSE LISTS ARE ALL EMPTY and with the two other challenges
fixed, the messages do not hang on the second stretch's first coin. -/
theorem msgs_zero (name endName : String) (t : State W X) (seen : Seen) (x x' : GE) :
    msgsAt (jobEmpty (W := W) (X := X)) t seen (one 11) [one 5, one 0] (coinsAt name endName x) =
      msgsAt (jobEmpty (W := W) (X := X)) t seen (one 11) [one 5, one 0]
        (coinsAt name endName x') := by
  have hz : Reading.gl.val ((drawnE [one 11, one 5, one 0]).getLastD zeroE) = 0 :=
    OnBytes.Slice.toE_zeroE
  unfold msgsAt sumMsgs
  rw [hz]
  exact msgsK_beta_zero _ _ _ _ _ _ 2 _ _ _ _ (funext fun p => funext fun i => by
    rw [jobPoly_empty, jobPoly_empty])

/-- **At a challenge of Y that reads 0 the two distributions differ**, at the job whose lists are
all empty and at whichever declared rounds that state the call's scalars: the end values' mask
entries then stand in no message. -/
theorem fails_beta (rs : List (Fmt.DeclaredRound × List Oracle)) (hr : StatedBy (scalarsOf kAt) rs)
    (name endName nm : String) (a a' : Addr) (v : Option V) (m : Mid W X) (pb : Pb)
    (front : Before) (asks : List (List (List Nat)))
    (ca : CsAll (sumPart (V := V) name endName (jobEmpty (W := W) (X := X))).carries) :
    (Prob.unif (Cs (sumPart (V := V) name endName (jobEmpty (W := W) (X := X))).takes ×
        CsAll (sumPart (V := V) name endName (jobEmpty (W := W) (X := X))).spends)).map
        (fun c => (play ((sumPart (V := V) name endName (jobEmpty (W := W) (X := X))).steps nm a
          rs v (c.1, c.2, ca)) dsZero [] m).toOption.map fun z => shownOf z.1 asks) ≠
      (Prob.unif (Cs (sumSim (Pb := Pb) a' kAt).takes)).map fun c =>
        (sumSim (Pb := Pb) a' kAt).tell pb front dsZero asks c := by
  intro hE
  have hinj := law_inj name endName kAt _ a' pb front dsZero asks hE
  have hF : ∀ c : Spent name endName kAt,
      ((play ((sumPart (V := V) name endName (jobEmpty (W := W) (X := X))).steps nm a rs v
        (c.1, c.2, ca)) dsZero [] m).toOption.map fun z => shownOf z.1 asks) =
      some ((msgsAt (jobEmpty (W := W) (X := X)) m.st m.shown (one 11) [one 5, one 0] c).map
        fun l => ⟨gotsOf l, []⟩) := fun c =>
    (congrArg (fun r => r.toOption.map fun z => shownOf z.1 asks)
      (plays_sumPart_whole (V := V) name endName (jobEmpty (W := W) (X := X)) (c.1, c.2, ca)
        (fair_vs_two (shapeFair_of_ok kAt_ok)) nm a rs hr v dsZero rfl [] m)).trans
      (congrArg some (shown_msgs (jobEmpty (W := W) (X := X)) c m.st m.shown (one 11)
        [one 5, one 0] [nil0] (shapeFair_of_ok kAt_ok) rfl rfl nm a asks))
  have h01 : coinsAt name endName 0 = coinsAt name endName 1 :=
    hinj ((hF _).trans ((congrArg (fun L => some (L.map fun l => (⟨gotsOf l, []⟩ : Shown)))
      (msgs_zero name endName m.st m.shown 0 1)).trans (hF _).symm))
  have h2 := congrFun (congrArg (fun c : Spent name endName kAt => c.2.2.1.e) h01)
    ⟨0, Nat.zero_lt_succ 1⟩
  exact zero_ne_one h2

/-- At the library's own entries that list of challenges does not fit: so there the premise on the
challenges shuts it out. -/
theorem dsZero_unfit : drawsFit (rsAt.map (·.1)) dsZero = false := by decide +kernel

/-- **The premise on the challenges is needed**: AT THE JOB WHOSE LISTS ARE ALL EMPTY, at one fixed
list of challenges: at the library's own entries the shape passes, the declared rounds state the
call's scalars and the test on Y's round accepts; the challenges do not fit; and the two
distributions differ. -/
theorem fails_unfit (name endName nm : String) (a a' : Addr) (v : Option V) (m : Mid W X)
    (pb : Pb) (front : Before) (asks : List (List (List Nat)))
    (ca : CsAll (sumPart (V := V) name endName (jobEmpty (W := W) (X := X))).carries) :
    shapeOk kAt = true ∧ StatedBy (scalarsOf kAt) rsAt ∧ betaMarked kAt rsAt = true ∧
    drawsFit (rsAt.map (·.1)) dsZero = false ∧
    (Prob.unif (Cs (sumPart (V := V) name endName (jobEmpty (W := W) (X := X))).takes ×
        CsAll (sumPart (V := V) name endName (jobEmpty (W := W) (X := X))).spends)).map
        (fun c => (play ((sumPart (V := V) name endName (jobEmpty (W := W) (X := X))).steps nm a
          rsAt v (c.1, c.2, ca)) dsZero [] m).toOption.map fun z => shownOf z.1 asks) ≠
      (Prob.unif (Cs (sumSim (Pb := Pb) a' kAt).takes)).map fun c =>
        (sumSim (Pb := Pb) a' kAt).tell pb front dsZero asks c :=
  ⟨kAt_ok, statedBy_entries kAt, betaMarked_entries kAt, dsZero_unfit,
    fails_beta rsAt (statedBy_entries kAt) name endName nm a a' v m pb front asks ca⟩

/-- Declared rounds as the library's, but that Y's element is not marked as never 0. -/
def rsUnmarked : List (Fmt.DeclaredRound × List Oracle) :=
  [entry "PSC epsilon" 3 1 0, entry "PSC round" 2 1 0, entry "PSC Y" 2 1 0,
    entry "PSC values" 2 0 0].map fun x => ({ entry := x }, [])

/-- They state the call's scalars. -/
theorem rsUnmarked_stated : StatedBy (scalarsOf kAt) rsUnmarked :=
  statedBy_nums _ _ rfl fun r hr => by
    obtain ⟨x, _, rfl⟩ := List.mem_map.1 hr
    rfl

/-- The list of challenges with Y's at 0 fits them. -/
theorem rsUnmarked_fit : drawsFit (rsUnmarked.map (·.1)) dsZero = true := by decide +kernel

/-- The test on Y's round rejects them. -/
theorem rsUnmarked_unmarked : betaMarked kAt rsUnmarked = false := by decide

/-- **The test on Y's round is needed**: an instance, AT THE JOB WHOSE LISTS ARE ALL EMPTY and one
fixed list of challenges, at which the shape passes, the declared rounds state the call's scalars
and the challenges fit them; the test on Y's round rejects; and the two distributions differ. -/
theorem fails_unmarked (name endName nm : String) (a a' : Addr) (v : Option V) (m : Mid W X)
    (pb : Pb) (front : Before) (asks : List (List (List Nat)))
    (ca : CsAll (sumPart (V := V) name endName (jobEmpty (W := W) (X := X))).carries) :
    shapeOk kAt = true ∧ StatedBy (scalarsOf kAt) rsUnmarked ∧
    drawsFit (rsUnmarked.map (·.1)) dsZero = true ∧ betaMarked kAt rsUnmarked = false ∧
    (Prob.unif (Cs (sumPart (V := V) name endName (jobEmpty (W := W) (X := X))).takes ×
        CsAll (sumPart (V := V) name endName (jobEmpty (W := W) (X := X))).spends)).map
        (fun c => (play ((sumPart (V := V) name endName (jobEmpty (W := W) (X := X))).steps nm a
          rsUnmarked v (c.1, c.2, ca)) dsZero [] m).toOption.map fun z => shownOf z.1 asks) ≠
      (Prob.unif (Cs (sumSim (Pb := Pb) a' kAt).takes)).map fun c =>
        (sumSim (Pb := Pb) a' kAt).tell pb front dsZero asks c :=
  ⟨kAt_ok, rsUnmarked_stated, rsUnmarked_fit, rsUnmarked_unmarked,
    fails_beta rsUnmarked rsUnmarked_stated name endName nm a a' v m pb front asks ca⟩

/-! ## 4 Without a lead, a variable or ends -/

/-- The shape without a lead, a variable or ends. -/
def kNone : Call := { lead := 0, vs := [], ends := none }

/-- Both tests on the shape reject it. -/
theorem kNone_not : shapeOk kNone = false ∧ shapeFair kNone = false := by decide

/-- A job at that shape, of any five functions. -/
def jobNone (p l : W → Front X → List E) (r : W → Front X → List E → List E)
    (y : W → Front X → List E → List E → List E) (e : W → Front X → List E → List E) :
    SumJob W X :=
  { shape := kNone, points := p, lead := l, round := r, inY := y, ends := e }

/-- The one coin that is lent there. -/
def coinNone (name endName : String) (x : GE) : Spent name endName kNone :=
  (Cs.empty, ((⟨fun i => i.elim0, fun _ => x⟩ : Cs ⟨0, 1⟩), ()))

/-- Rounds made of the library's own entries for that call state its one scalar. -/
theorem rsNone_stated :
    StatedBy (scalarsOf kNone) ((entries kNone).map fun x => ({ entry := x }, [])) :=
  statedBy_entries kNone

/-- One challenge of one element fits them. -/
theorem dsNone_fit :
    drawsFit (((entries kNone).map fun x => (({ entry := x }, []) :
      Fmt.DeclaredRound × List Oracle)).map (·.1)) [one 11] = true := by decide +kernel

/-- **At the shape without a lead, a variable or ends (`kNone`) the two distributions differ**, at
every five functions of a job at that shape: the part sends the constant 0 where one coin is lent.
All other premises are met there. So the premise on the shape is needed. -/
theorem fails_empty (p l : W → Front X → List E) (r : W → Front X → List E → List E)
    (y : W → Front X → List E → List E → List E) (e : W → Front X → List E → List E)
    (name endName nm : String) (a a' : Addr) (v : Option V) (m : Mid W X) (pb : Pb)
    (front : Before) (asks : List (List (List Nat)))
    (ca : CsAll (sumPart (V := V) name endName (jobNone p l r y e)).carries) :
    shapeFair kNone = false ∧
    StatedBy (scalarsOf kNone) ((entries kNone).map fun x => ({ entry := x }, [])) ∧
    betaMarked kNone ((entries kNone).map fun x => ({ entry := x }, [])) = true ∧
    drawsFit (((entries kNone).map fun x => (({ entry := x }, []) :
      Fmt.DeclaredRound × List Oracle)).map (·.1)) [one 11] = true ∧
    (Prob.unif (Cs (sumPart (V := V) name endName (jobNone p l r y e)).takes ×
        CsAll (sumPart (V := V) name endName (jobNone p l r y e)).spends)).map
        (fun c => (play ((sumPart (V := V) name endName (jobNone p l r y e)).steps nm a
          ((entries kNone).map fun x => ({ entry := x }, [])) v (c.1, c.2, ca)) [one 11] []
          m).toOption.map fun z => shownOf z.1 asks) ≠
      (Prob.unif (Cs (sumSim (Pb := Pb) a' kNone).takes)).map fun c =>
        (sumSim (Pb := Pb) a' kNone).tell pb front [one 11] asks c := by
  refine ⟨kNone_not.2, rsNone_stated, betaMarked_entries kNone, dsNone_fit, ?_⟩
  intro hE
  have hinj := law_inj name endName kNone _ a' pb front [one 11] asks hE
  have hF : ∀ c : Spent name endName kNone,
      ((play ((sumPart (V := V) name endName (jobNone p l r y e)).steps nm a
        ((entries kNone).map fun x => ({ entry := x }, [])) v (c.1, c.2, ca)) [one 11] []
        m).toOption.map fun z => shownOf z.1 asks) =
      some (shownOf ([rvSaid [zeroE] (one 11)].map (saidPlayed nm a)) asks) := fun c =>
    congrArg (fun r => r.toOption.map fun z => shownOf z.1 asks)
      (plays_sumPart_whole (V := V) name endName (jobNone p l r y e) (c.1, c.2, ca)
        (fun _ h => by cases h) nm a _ rsNone_stated v [one 11] rfl [] m)
  have h01 : coinNone name endName 0 = coinNone name endName 1 :=
    hinj ((hF _).trans (hF _).symm)
  have h2 := congrFun (congrArg (fun c : Spent name endName kNone => c.2.1.e) h01)
    ⟨0, Nat.zero_lt_succ 0⟩
  exact zero_ne_one h2

/-! ## 5 Where the challenges are not as many as the rounds that are played -/

/-- A run that goes through has as many challenges as rounds. -/
theorem play_len : ∀ (ss : List (Step W X)) (ds : List Fmt.Drawn) (back : List Fmt.RoundView)
    (m : Mid W X) (z : List Played × Mid W X), play ss ds back m = .ok z → ss.length = ds.length
  | [], [], _, _, _, _ => rfl
  | s :: ss, d :: ds, back, m, z, h => by
    rw [play] at h
    cases h1 : s.tell back.head? m with
    | error _ =>
      rw [h1] at h
      cases h
    | ok x =>
      rw [h1] at h
      cases h2 : s.hear x d m with
      | error _ =>
        simp only [Except.bind, h2] at h
        cases h
      | ok m' =>
        simp only [Except.bind, h2] at h
        cases h3 : play ss ds back.tail m' with
        | error _ =>
          rw [h3] at h
          cases h
        | ok z' => exact congrArg (· + 1) (play_len ss ds back.tail m' z' h3)
  | [], _ :: _, _, _, _, h => by simp [play] at h
  | _ :: _, [], _, _, _, h => by simp [play] at h

/-- **Where the challenges are not as many as the rounds that are played, the two distributions
differ**: the part's side is the one symbol for a fault; the simulator yields rounds. -/
theorem fails_count (name endName : String) (J : SumJob W X)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (nm : String) (a a' : Addr) (v : Option V)
    (m : Mid W X) (pb : Pb) (front : Before) (ds : List Fmt.Drawn)
    (hl : min rs.length (sumPart (V := V) name endName J).moves.length ≠ ds.length)
    (asks : List (List (List Nat))) (ca : CsAll (sumPart (V := V) name endName J).carries) :
    (Prob.unif (Cs (sumPart (V := V) name endName J).takes ×
        CsAll (sumPart (V := V) name endName J).spends)).map
        (fun c => (play ((sumPart (V := V) name endName J).steps nm a rs v (c.1, c.2, ca)) ds []
          m).toOption.map fun z => shownOf z.1 asks) ≠
      (Prob.unif (Cs (sumSim (Pb := Pb) a' J.shape).takes)).map fun c =>
        (sumSim (Pb := Pb) a' J.shape).tell pb front ds asks c := by
  intro hE
  have hy : (sumSim (Pb := Pb) a' J.shape).tell pb front ds asks default ∈
      ((Prob.unif (Cs (sumSim (Pb := Pb) a' J.shape).takes)).map fun c =>
        (sumSim (Pb := Pb) a' J.shape).tell pb front ds asks c).support :=
    (PMF.mem_support_map_iff _ _ _).2 ⟨default, PMF.mem_support_uniformOfFintype _, rfl⟩
  rw [← hE] at hy
  obtain ⟨c, -, hc⟩ := (PMF.mem_support_map_iff _ _ _).1 hy
  cases hp : play ((sumPart (V := V) name endName J).steps nm a rs v (c.1, c.2, ca)) ds [] m with
  | error _ =>
    rw [hp] at hc
    cases hc
  | ok z =>
    have h := play_len _ _ _ _ _ hp
    unfold Part.steps at h
    rw [List.length_map, List.length_zipIdx, List.length_zip] at h
    exact hl h

/-- Declared rounds one too many: the last of them once more. -/
def rsLong : List (Fmt.DeclaredRound × List Oracle) :=
  rsAt ++ [({ entry := entry "PSC values" 2 0 0 }, [])]
/-- Challenges that fit them. -/
def dsLong : List Fmt.Drawn := dsAt ++ [nil0]

/-- They fit. -/
theorem dsLong_fit : drawsFit (rsLong.map (·.1)) dsLong = true := by decide +kernel

/-- **An instance**: the shape passes, the test on Y's round passes, the challenges fit the declared
rounds; these state a round too many: the two distributions differ. So the premise on what the
declared rounds state is needed. -/
theorem fails_long (p l : W → Front X → List E) (r : W → Front X → List E → List E)
    (y : W → Front X → List E → List E → List E) (e : W → Front X → List E → List E)
    (name endName nm : String) (a a' : Addr) (v : Option V) (m : Mid W X) (pb : Pb)
    (front : Before) (asks : List (List (List Nat)))
    (ca : CsAll (sumPart (V := V) name endName (jobAt p l r y e)).carries) :
    shapeOk kAt = true ∧ betaMarked kAt rsLong = true ∧
    drawsFit (rsLong.map (·.1)) dsLong = true ∧ ¬ StatedBy (scalarsOf kAt) rsLong ∧
    (Prob.unif (Cs (sumPart (V := V) name endName (jobAt p l r y e)).takes ×
        CsAll (sumPart (V := V) name endName (jobAt p l r y e)).spends)).map
        (fun c => (play ((sumPart (V := V) name endName (jobAt p l r y e)).steps nm a rsLong v
          (c.1, c.2, ca)) dsLong [] m).toOption.map fun z => shownOf z.1 asks) ≠
      (Prob.unif (Cs (sumSim (Pb := Pb) a' kAt).takes)).map fun c =>
        (sumSim (Pb := Pb) a' kAt).tell pb front dsLong asks c :=
  ⟨kAt_ok, by decide, dsLong_fit, fun h => absurd (statedBy_len _ _ h) (by decide),
    fails_count name endName (jobAt p l r y e) rsLong nm a a' v m pb front dsLong
    (by
      show min 5 4 ≠ 5
      decide) asks ca⟩

/-! ## 6 Where fewer rounds are played than the call has -/

/-- A run that goes through yields as many rounds as it has steps. -/
theorem play_out_len : ∀ (ss : List (Step W X)) (ds : List Fmt.Drawn) (back : List Fmt.RoundView)
    (m : Mid W X) (z : List Played × Mid W X), play ss ds back m = .ok z → z.1.length = ss.length
  | [], [], _, _, z, h => by
    rw [play] at h
    obtain rfl := Except.ok.inj h
    rfl
  | s :: ss, d :: ds, back, m, z, h => by
    rw [play] at h
    cases h1 : s.tell back.head? m with
    | error _ =>
      rw [h1] at h
      cases h
    | ok x =>
      rw [h1] at h
      cases h2 : s.hear x d m with
      | error _ =>
        simp only [Except.bind, h2] at h
        cases h
      | ok m' =>
        simp only [Except.bind, h2] at h
        cases h3 : play ss ds back.tail m' with
        | error _ =>
          rw [h3] at h
          cases h
        | ok z' =>
          rw [h3] at h
          obtain rfl := Except.ok.inj h
          exact congrArg (· + 1) (play_out_len ss ds back.tail m' z' h3)
  | [], _ :: _, _, _, _, h => by simp [play] at h
  | _ :: _, [], _, _, _, h => by simp [play] at h

/-- Coins cut into rounds: as many rounds as numbers. -/
theorem roundsCut_length : ∀ (ns : List Nat) (L : List E), (roundsCut ns L).length = ns.length
  | [], _ => rfl
  | _ :: ns, L => congrArg (· + 1) (roundsCut_length ns (L.drop _))

/-- **Where fewer rounds are played than the call has, the two distributions differ**: the part's
side is the symbol for a fault, or shows fewer rounds than the simulator yields. (More are never
played: the part has as many moves as the call has rounds: `moves_length`, `scalarsOf_length`,
Fits.lean.) -/
theorem fails_rounds (name endName : String) (J : SumJob W X)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (nm : String) (a a' : Addr) (v : Option V)
    (m : Mid W X) (pb : Pb) (front : Before) (ds : List Fmt.Drawn)
    (hl : min rs.length (sumPart (V := V) name endName J).moves.length ≠
      (scalarsOf J.shape).length)
    (asks : List (List (List Nat))) (ca : CsAll (sumPart (V := V) name endName J).carries) :
    (Prob.unif (Cs (sumPart (V := V) name endName J).takes ×
        CsAll (sumPart (V := V) name endName J).spends)).map
        (fun c => (play ((sumPart (V := V) name endName J).steps nm a rs v (c.1, c.2, ca)) ds []
          m).toOption.map fun z => shownOf z.1 asks) ≠
      (Prob.unif (Cs (sumSim (Pb := Pb) a' J.shape).takes)).map fun c =>
        (sumSim (Pb := Pb) a' J.shape).tell pb front ds asks c := by
  intro hE
  have hy : (sumSim (Pb := Pb) a' J.shape).tell pb front ds asks default ∈
      ((Prob.unif (Cs (sumSim (Pb := Pb) a' J.shape).takes)).map fun c =>
        (sumSim (Pb := Pb) a' J.shape).tell pb front ds asks c).support :=
    (PMF.mem_support_map_iff _ _ _).2 ⟨default, PMF.mem_support_uniformOfFintype _, rfl⟩
  rw [← hE] at hy
  obtain ⟨c, -, hc⟩ := (PMF.mem_support_map_iff _ _ _).1 hy
  cases hp : play ((sumPart (V := V) name endName J).steps nm a rs v (c.1, c.2, ca)) ds [] m with
  | error _ =>
    rw [hp] at hc
    cases hc
  | ok z =>
    rw [hp] at hc
    have h1 := play_out_len _ _ _ _ _ hp
    unfold Part.steps at h1
    rw [List.length_map, List.length_zipIdx, List.length_zip] at h1
    have h2 : shownOf z.1 asks = (roundsCut (scalarsOf J.shape) (coinsE default)).map
        fun l => (⟨l.map fun x => .e x.triple, []⟩ : Shown) := Option.some.inj hc
    have h3 := congrArg List.length h2
    unfold shownOf at h3
    rw [List.length_map, List.length_zipIdx, List.length_map, roundsCut_length, h1] at h3
    exact hl h3

/-- Declared rounds that end a round early. -/
def rsEarly : List (Fmt.DeclaredRound × List Oracle) := rsAt.take 3

/-- Challenges that fit them. -/
def dsEarly : List Fmt.Drawn := dsAt.take 3

/-- They fit. -/
theorem dsEarly_fit : drawsFit (rsEarly.map (·.1)) dsEarly = true := by decide +kernel

/-- **An instance**: the shape passes, the test on Y's round passes, the challenges fit the declared
rounds; these end a round early: they do not state the call's scalars, and the two distributions
differ. -/
theorem fails_early (p l : W → Front X → List E) (r : W → Front X → List E → List E)
    (y : W → Front X → List E → List E → List E) (e : W → Front X → List E → List E)
    (name endName nm : String) (a a' : Addr) (v : Option V) (m : Mid W X) (pb : Pb)
    (front : Before) (asks : List (List (List Nat)))
    (ca : CsAll (sumPart (V := V) name endName (jobAt p l r y e)).carries) :
    shapeOk kAt = true ∧ betaMarked kAt rsEarly = true ∧
    drawsFit (rsEarly.map (·.1)) dsEarly = true ∧ ¬ StatedBy (scalarsOf kAt) rsEarly ∧
    (Prob.unif (Cs (sumPart (V := V) name endName (jobAt p l r y e)).takes ×
        CsAll (sumPart (V := V) name endName (jobAt p l r y e)).spends)).map
        (fun c => (play ((sumPart (V := V) name endName (jobAt p l r y e)).steps nm a rsEarly v
          (c.1, c.2, ca)) dsEarly [] m).toOption.map fun z => shownOf z.1 asks) ≠
      (Prob.unif (Cs (sumSim (Pb := Pb) a' kAt).takes)).map fun c =>
        (sumSim (Pb := Pb) a' kAt).tell pb front dsEarly asks c :=
  ⟨kAt_ok, by decide, dsEarly_fit, fun h => absurd (statedBy_len _ _ h) (by decide),
    fails_rounds name endName (jobAt p l r y e) rsEarly nm a a' v m pb front dsEarly
    (by
      show min 3 4 ≠ 4
      decide) asks ca⟩

/-! ## 7 A declared round with an oracle message -/

/-- The declared rounds of the instance, but that the second has one oracle message. -/
def rsOracle : List (Fmt.DeclaredRound × List Oracle) :=
  rsAt.zipIdx.map fun r => (r.1.1, if r.2 = 1 then [default] else r.1.2)

/-- **An instance: the declared rounds `rsOracle`, of which one has an oracle message, do not state
the call's scalars**, though their declarations are the library's own. It bears no inequality. The
general fact: `stated_no_oracle` (SumExact.lean). The two distributions differ there: said here
without a theorem; no theorem of this folder shows it. -/
theorem oracle_unstated :
    rsOracle.map (·.1) = rsAt.map (·.1) ∧ ¬ StatedBy (scalarsOf kAt) rsOracle :=
  ⟨by decide, fun h => by
    have := stated_no_oracle _ _ h ({ entry := entry "PSC round" 2 1 0 }, [default]) (by decide)
    cases this⟩

end ProofFile.Honest.SumLaw.At

#print axioms ProofFile.Honest.SumLaw.At.kAt_ok
#print axioms ProofFile.Honest.SumLaw.At.dsAt_fit
#print axioms ProofFile.Honest.SumLaw.At.exact_at
#print axioms ProofFile.Honest.SumLaw.At.exact_at_empty
#print axioms ProofFile.Honest.SumLaw.At.empty_unfit
#print axioms ProofFile.Honest.SumLaw.At.empty_clauses
#print axioms ProofFile.Honest.SumLaw.At.exact_at_field
#print axioms ProofFile.Honest.SumLaw.At.kN0_tests
#print axioms ProofFile.Honest.SumLaw.At.dsN0_fit
#print axioms ProofFile.Honest.SumLaw.At.exact_at_n0
#print axioms ProofFile.Honest.SumLaw.At.k66_tests
#print axioms ProofFile.Honest.SumLaw.At.ds66_fit
#print axioms ProofFile.Honest.SumLaw.At.exact_at_66
#print axioms ProofFile.Honest.SumLaw.At.roundsCut_join
#print axioms ProofFile.Honest.SumLaw.At.decode_tell
#print axioms ProofFile.Honest.SumLaw.At.law_inj
#print axioms ProofFile.Honest.SumLaw.At.jobPoly_empty
#print axioms ProofFile.Honest.SumLaw.At.msgs_zero
#print axioms ProofFile.Honest.SumLaw.At.fails_beta
#print axioms ProofFile.Honest.SumLaw.At.dsZero_unfit
#print axioms ProofFile.Honest.SumLaw.At.fails_unfit
#print axioms ProofFile.Honest.SumLaw.At.rsUnmarked_stated
#print axioms ProofFile.Honest.SumLaw.At.rsUnmarked_fit
#print axioms ProofFile.Honest.SumLaw.At.rsUnmarked_unmarked
#print axioms ProofFile.Honest.SumLaw.At.fails_unmarked
#print axioms ProofFile.Honest.SumLaw.At.kNone_not
#print axioms ProofFile.Honest.SumLaw.At.rsNone_stated
#print axioms ProofFile.Honest.SumLaw.At.dsNone_fit
#print axioms ProofFile.Honest.SumLaw.At.fails_empty
#print axioms ProofFile.Honest.SumLaw.At.play_len
#print axioms ProofFile.Honest.SumLaw.At.fails_count
#print axioms ProofFile.Honest.SumLaw.At.dsLong_fit
#print axioms ProofFile.Honest.SumLaw.At.fails_long
#print axioms ProofFile.Honest.SumLaw.At.play_out_len
#print axioms ProofFile.Honest.SumLaw.At.roundsCut_length
#print axioms ProofFile.Honest.SumLaw.At.fails_rounds
#print axioms ProofFile.Honest.SumLaw.At.dsEarly_fit
#print axioms ProofFile.Honest.SumLaw.At.fails_early
#print axioms ProofFile.Honest.SumLaw.At.oracle_unstated
#print axioms ProofFile.Honest.SumLaw.At.kAt
#print axioms ProofFile.Honest.SumLaw.At.rsAt
#print axioms ProofFile.Honest.SumLaw.At.one
#print axioms ProofFile.Honest.SumLaw.At.nil0
#print axioms ProofFile.Honest.SumLaw.At.dsAt
#print axioms ProofFile.Honest.SumLaw.At.jobAt
#print axioms ProofFile.Honest.SumLaw.At.jobEmpty
#print axioms ProofFile.Honest.SumLaw.At.kN0
#print axioms ProofFile.Honest.SumLaw.At.rsN0
#print axioms ProofFile.Honest.SumLaw.At.jobN0
#print axioms ProofFile.Honest.SumLaw.At.k66
#print axioms ProofFile.Honest.SumLaw.At.rs66
#print axioms ProofFile.Honest.SumLaw.At.job66
#print axioms ProofFile.Honest.SumLaw.At.decode
#print axioms ProofFile.Honest.SumLaw.At.dsZero
#print axioms ProofFile.Honest.SumLaw.At.coinsAt
#print axioms ProofFile.Honest.SumLaw.At.rsUnmarked
#print axioms ProofFile.Honest.SumLaw.At.kNone
#print axioms ProofFile.Honest.SumLaw.At.jobNone
#print axioms ProofFile.Honest.SumLaw.At.coinNone
#print axioms ProofFile.Honest.SumLaw.At.rsLong
#print axioms ProofFile.Honest.SumLaw.At.dsLong
#print axioms ProofFile.Honest.SumLaw.At.rsEarly
#print axioms ProofFile.Honest.SumLaw.At.dsEarly
#print axioms ProofFile.Honest.SumLaw.At.rsOracle
