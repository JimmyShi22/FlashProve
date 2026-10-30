-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/RunsJoin.lean: ONE OF THE FOUR RUNS OF CLAIMS THAT STAND IN THE BLOCK OF
AN ATTENTION SEGMENT's OWN ROUNDS: "join" (the text is the lookup's kind's:
Johnson/Desc/First/Look/K3Runs.lean, LookClaims.lean), ON THE FIRST CHAIN's SHAPE, IN THE FORM
`RunLaw` (Johnson/Desc/First/Batch/Shape/ClaimShape.lean). Definitions, and statements with their
proofs.

Main names:
  `unpaidSh`, `unpaid_sh`   the debt of that number is not yet marked as paid, on the ledger's shape
  `joinFormSh`, `fold_sh`, `range_getD`, `joinF_sh`, `joinF_counts`   **the shape of the run's one
    claim is a closed term**: the key forms' entries and slots, call by call; then those of the form
    that the lookup's last claim left
  `k5JoinG`   **the run on shapes**
  `joinLaw`, `pre_of_join`   **the law**; a return of the run gives its premise on values

IT READS FOUR COMPONENTS OF THE SHAPE: the ledger; what the lookup's hearing laid (lookHeard); and,
through the key forms, what the link's own rounds handed on and look. At an attention link look
reads the field g and lookHeard a field of its own: TWO FIELDS, which the hearing's one door
(S.hearLook, Johnson/Desc/First/State.lean) lays at once with one value; a later put writes the
first alone.

Limits. As Johnson/Desc/K5/Honest/Law/RunsLaw.lean's: the key forms on shapes are made by running
"first" and "keys" at zeros; the one Bool is sufficient, not shown to be necessary; no statement
says that the run on shapes returns anywhere. Shapes alone: nothing on the claim's worth.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.RunsLaw
import Johnson.Desc.First.Att.K05JoinRunN
import Johnson.Desc.First.Att.K05ReturnsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model
open VerifiableInference.Desc (First.S First.AttOwn Claim named need)
open VerifiableInference.Desc.K9.Shape (RunLaw)
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (ParC Heard)
open VerifiableInference.Desc.First.Shape (ChainSh chainSh ClaimSh claimSh AffSh affSh affSh_addMul
  affSh_add affSh_sub HeardAll heardAll heard5Sh LedSh ledSh paidB ledSh_paid chainSh_putFork)
open K5Law (OptRel)

/-! ## 1 The ledger's mark -/

/-- The debt of that number is not yet marked as paid: `K3.unpaid`
(Johnson/Desc/First/Look/K3Runs.lean) on the ledger's shape. -/
def unpaidSh (L : LedSh) (i : Nat) : Bool := L.owed[i]? != some true

theorem unpaid_sh (F : Fork) (i : Nat) :
    VerifiableInference.Desc.K3.unpaid F i = unpaidSh (ledSh F) i := by
  show ((F.owed[i]?).map (·.added) != some true) =
    ((F.owed.toList.map (·.added))[i]? != some true)
  rw [List.getElem?_map, Array.getElem?_toList]

/-! ## 2 The one claim's shape -/

/-- **The shape of "join"'s one claim.** Kh: the shape of what the lookup's hearing laid. kf: the
key forms' shapes, call by call. -/
def joinFormSh (Kh : HeardAll) (kf : List AffSh) : AffSh :=
  AffSh.mk (kf.flatMap (·.ents) ++ Kh.cEnd.ents) (kf.flatMap (·.slots) ++ Kh.cEnd.slots)

/-- The fold over the calls appends the key forms' entries and slots, in the calls' order. -/
theorem fold_sh (KF : Array Aff) (d : Aff) (al ee : Nat → E) : ∀ (l : List Nat) (f : Aff),
    affSh (l.foldl (fun (f : Aff) c => Aff.addMul f (Aff.ofConst (al c) - KF.getD c d) (ee c)) f) =
      AffSh.mk ((affSh f).ents ++ (l.map fun c => affSh (KF.getD c d)).flatMap (·.ents))
        ((affSh f).slots ++ (l.map fun c => affSh (KF.getD c d)).flatMap (·.slots))
  | [], f => by
    show affSh f = AffSh.mk ((affSh f).ents ++ []) ((affSh f).slots ++ [])
    rw [List.append_nil, List.append_nil]
    rfl
  | c :: l, f => by
    rw [List.foldl_cons, fold_sh KF d al ee l, affSh_addMul, affSh_sub]
    show AffSh.mk (((affSh f).ents ++ ([] ++ (affSh (KF.getD c d)).ents)) ++ _)
      (((affSh f).slots ++ ([] ++ (affSh (KF.getD c d)).slots)) ++ _) = _
    simp only [List.nil_append, List.append_assoc, List.map_cons, List.flatMap_cons]

theorem range_getD (KF : Array Aff) (d : Aff) :
    (List.range KF.size).map (fun c => KF.getD c d) = KF.toList := by
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
  have hi : i < KF.size := by simpa using h2
  simp [Array.getD, hi]

/-- **What the lookup's function for the join returns**: a form of that shape; the ledger with the
one debt marked as paid. CONDITIONAL on its return. -/
theorem joinF_sh {g : Forest.Heard} {KF : Array Aff} {F : Fork} {l : OnBytes.K.Kc.Tape}
    {x : Aff × Fork × OnBytes.K.Kc.Tape}
    (h : VerifiableInference.Desc.First.Look.joinF g KF F l = some x) :
    affSh x.1 = joinFormSh (heardAll g) (formsSh KF) ∧ x.2.1 = F.paid g.owedJoin := by
  unfold VerifiableInference.Desc.First.Look.joinF at h
  by_cases hb : (KF.size == g.shape.calls.size && g.e.size == g.shape.calls.size) = true
  · simp only [bind, OnBytes.K.Kc.Fl.andThen, OnBytes.K.Kc.Fl.must, hb, if_true,
      VerifiableInference.Desc.First.Look.joinAddedF, VerifiableInference.Desc.First.Look.paidF,
      OnBytes.K.Kc.Fl.change, Option.map_some, pure, OnBytes.K.Kc.Fl.ret,
      Option.some.injEq] at h
    subst h
    refine ⟨?_, rfl⟩
    dsimp only
    rw [affSh_sub, affSh_add, fold_sh]
    have e := range_getD KF (Aff.ofConst zeroE)
    have e' : (List.range KF.size).map (fun c => affSh (KF.getD c (Aff.ofConst zeroE))) =
        formsSh KF := by
      unfold formsSh
      rw [← e, List.map_map]
      rfl
    rw [e']
    show AffSh.mk ((([] ++ _) ++ []) ++ (affSh g.cEnd).ents)
      ((([] ++ _) ++ []) ++ (affSh g.cEnd).slots) = _
    simp only [List.nil_append, List.append_nil]
    rfl
  · simp only [bind, OnBytes.K.Kc.Fl.andThen, OnBytes.K.Kc.Fl.must, hb] at h
    cases h

/-- And the two counts fit. CONDITIONAL on its return. -/
theorem joinF_counts {g : Forest.Heard} {KF : Array Aff} {F : Fork} {l : OnBytes.K.Kc.Tape}
    {x : Aff × Fork × OnBytes.K.Kc.Tape}
    (h : VerifiableInference.Desc.First.Look.joinF g KF F l = some x) :
    KF.size = g.shape.calls.size ∧ g.e.size = g.shape.calls.size := by
  unfold VerifiableInference.Desc.First.Look.joinF at h
  by_cases hb : (KF.size == g.shape.calls.size && g.e.size == g.shape.calls.size) = true
  · simpa only [Bool.and_eq_true, beq_iff_eq] using hb
  · simp only [bind, OnBytes.K.Kc.Fl.andThen, OnBytes.K.Kc.Fl.must, hb] at h
    cases h

/-! ## 3 The run on shapes, and the law -/

section
variable (A : Attention.Plan)

/-- **"join" on shapes.** It lays the ledger alone: one mark. -/
def k5JoinG (_ : Nat) (a : ChainSh) : Except String (List ClaimSh × ChainSh) :=
  if tabsGC A a then
    match a.led, a.lookHeard, keysBlank A a with
    | some L, some Kh, some kf =>
      if unpaidSh L Kh.owedJoin &&
          (kf.size == Kh.shape.calls.size && Kh.e == Kh.shape.calls.size) then
        .ok ([bareSh (joinFormSh Kh (formsSh kf))],
          a.setLed (L.setOwed (paidB L.owed Kh.owedJoin)))
      else .error "K3 join on shapes: paid already, or the numbers of forms and weights"
    | _, _, _ => .error "K3 join on shapes: a part is not laid"
  else .error "K3 join on shapes: the tables' test"

/-- The run, as the kind's list of runs typed at Claim holds it (`join_in_runsN`,
Johnson/Desc/First/Att/K05JoinRunN.lean). -/
abbrev joinRunA : VerifiableInference.Desc.K9.Shape.Run :=
  VerifiableInference.Desc.K3.joinRun (VerifiableInference.Desc.K3.seatCalls K3Lot.ofForm)
    (P.keysOfO A)

/-- **What a return of the run holds.** -/
theorem join_ok_is {n : Nat} {s s' : First.S} {cs : List Claim}
    (h : joinRunA A n s = .ok (cs, s')) :
    ∃ F g KF x, s.fork? = some F ∧ s.lookHeard? = some g ∧
      VerifiableInference.Desc.K3.unpaid F g.owedJoin = true ∧ P.keysOfO A s = some KF ∧
      VerifiableInference.Desc.First.Look.joinF g KF F [] = some x ∧
      cs = [({ form := x.1 } : Claim)] ∧ s' = s.putFork x.2.1 := by
  unfold joinRunA VerifiableInference.Desc.K3.joinRun at h
  cases hF : s.fork? with
  | none =>
    simp [VerifiableInference.Desc.K3.seatCalls, hF, named, bind, Except.bind] at h
  | some F =>
    cases hg : s.lookHeard? with
    | none =>
      simp [VerifiableInference.Desc.K3.seatCalls, hF, hg, named, bind, Except.bind] at h
    | some g =>
      cases hu : VerifiableInference.Desc.K3.unpaid F g.owedJoin with
      | false =>
        simp [VerifiableInference.Desc.K3.seatCalls, hF, hg, hu, named, need, bind,
          Except.bind] at h
      | true =>
        cases hk : P.keysOfO A s with
        | none =>
          simp [VerifiableInference.Desc.K3.seatCalls, hF, hg, hu, hk, named, need, bind,
            Except.bind] at h
        | some KF =>
          cases hx : VerifiableInference.Desc.First.Look.joinF g KF F [] with
          | none =>
            simp [VerifiableInference.Desc.K3.seatCalls, hF, hg, hu, hk, hx, named, need, bind,
              Except.bind] at h
          | some x =>
            simp [VerifiableInference.Desc.K3.seatCalls, hF, hg, hu, hk, hx, named, need, bind,
              Except.bind, pure, Except.pure] at h
            exact ⟨F, g, KF, x, rfl, rfl, hu, rfl, hx, h.1.symm, h.2.symm⟩

/-- And back. -/
theorem join_ok_of {n : Nat} {s : First.S} {F : Fork} {g : Forest.Heard} {KF : Array Aff}
    {x : Aff × Fork × OnBytes.K.Kc.Tape} (hF : s.fork? = some F) (hg : s.lookHeard? = some g)
    (hu : VerifiableInference.Desc.K3.unpaid F g.owedJoin = true) (hk : P.keysOfO A s = some KF)
    (hx : VerifiableInference.Desc.First.Look.joinF g KF F [] = some x) :
    joinRunA A n s = .ok ([({ form := x.1 } : Claim)], s.putFork x.2.1) := by
  unfold joinRunA VerifiableInference.Desc.K3.joinRun
  simp [VerifiableInference.Desc.K3.seatCalls, hF, hg, hu, hk, hx, named, need, bind, Except.bind,
    pure, Except.pure, K3Lot.ofForm]

/-- The key forms at a state's parts. -/
theorem keysO_at {s : First.S} {a : First.AttOwn} {h : Heard} {gl : Forest.Heard}
    (hh : s.here = .att a) (h5 : a.heard5 = some h) (hg : a.g = some gl) :
    P.keysOfO A s =
      (K5Law.inAt (P.parCOf A) gl h a.F).bind fun x => (P.Runs.firstRun x.1 x.2).bind fun y =>
        P.Runs.keysRun x.1 (P.padOfO gl.shape) y.2 :=
  keysK_at hh h5 hg

end

section
variable (A : Attention.Plan)

/-- Arrays of forms of one shape have one size. -/
theorem size_of_formsSh {k k' : Array Aff} (h : formsSh k = formsSh k') : k.size = k'.size := by
  have e := congrArg List.length h
  unfold formsSh at e
  simpa using e

/-- What the run on shapes' return holds at a state's shape. -/
theorem joinG_ok_is {n : Nat} {s : First.S} {y : List ClaimSh × ChainSh}
    (hg : k5JoinG A n (chainSh s) = .ok y) :
    ∃ a h gl gL kf, s.here = .att a ∧ a.heard5 = some h ∧ a.g = some gl ∧
      a.lookHeard = some gL ∧ tabsG A (heard5Sh h) (heardAll gl) (ledSh a.F) = true ∧
      keysBlank A (chainSh s) = some kf ∧ unpaidSh (ledSh a.F) gL.owedJoin = true ∧
      kf.size = gL.shape.calls.size ∧ gL.e.size = gL.shape.calls.size ∧
      y = ([bareSh (joinFormSh (heardAll gL) (formsSh kf))],
        (chainSh s).setLed ((ledSh a.F).setOwed (paidB (ledSh a.F).owed gL.owedJoin))) := by
  unfold k5JoinG at hg
  split at hg
  · rename_i hG
    obtain ⟨a, h, gl, hh, h5, hgl, hT, _⟩ := front_of A hG
    have e3 : (chainSh s).led = some (ledSh a.F) := by
      show s.fork?.map ledSh = _
      unfold First.S.fork?
      rw [hh]
      rfl
    have e4 : (chainSh s).lookHeard = a.lookHeard.map heardAll := by
      show s.lookHeard?.map heardAll = _
      unfold First.S.lookHeard?
      rw [hh]
    rw [e3, e4] at hg
    cases hL : a.lookHeard with
    | none =>
      rw [hL] at hg
      simp at hg
    | some gL =>
      rw [hL] at hg
      cases hk : keysBlank A (chainSh s) with
      | none =>
        rw [hk] at hg
        simp at hg
      | some kf =>
        rw [hk] at hg
        simp only [Option.map_some] at hg
        split at hg
        · rename_i hb
          simp only [Bool.and_eq_true, beq_iff_eq] at hb
          exact ⟨a, h, gl, gL, kf, hh, h5, hgl, hL, hT, rfl, hb.1, hb.2.1, hb.2.2,
            (Except.ok.inj hg).symm⟩
        · cases hg
  · cases hg

/-- **"join".** -/
def joinLaw : RunLaw (joinRunA A) where
  runG := k5JoinG A
  pre := preK5 A
  carries := by
    intro n s s' cs y _ hr hg
    obtain ⟨a, h, gl, gL, kf, hh, h5, hgl, hL, _, hk, _, _, _, rfl⟩ := joinG_ok_is A hg
    obtain ⟨F, g, KF, x, hF, hg', _, hK, hx, rfl, rfl⟩ := join_ok_is A hr
    have eF : F = a.F := by
      unfold First.S.fork? at hF
      rw [hh] at hF
      exact (Option.some.inj hF).symm
    have eg : g = gL := by
      unfold First.S.lookHeard? at hg'
      rw [hh] at hg'
      exact Option.some.inj (hg'.symm.trans hL)
    subst eF eg
    obtain ⟨f1, f2⟩ := joinF_sh hx
    rw [keysO_at A hh h5 hgl] at hK
    rw [keysBlank_at A hh h5 hgl] at hk
    obtain ⟨i, hi, hK⟩ := Option.bind_eq_some_iff.1 hK
    obtain ⟨i', hi', hk⟩ := Option.bind_eq_some_iff.1 hk
    obtain ⟨S, eK⟩ := blank_sh hi hi'
    have r := keys_both (gl := gl) S eK
    rw [hK, hk] at r
    have r' : formsSh KF = formsSh kf := r
    have e1 : [({ form := x.1 } : Claim)].map claimSh =
        [bareSh (joinFormSh (heardAll g) (formsSh kf))] := by
      show [bareSh (affSh x.1)] = _
      rw [f1, r']
    have e2 : chainSh (s.putFork x.2.1) =
        (chainSh s).setLed ((ledSh a.F).setOwed (paidB (ledSh a.F).owed g.owedJoin)) := by
      rw [f2, chainSh_putFork, ledSh_paid]
    rw [e1, e2]
  returns := by
    intro n s y hg hp
    obtain ⟨a, h, gl, gL, kf, hh, h5, hgl, hL, hT, hk, hu, hs1, hs2, _⟩ := joinG_ok_is A hg
    have hV : valsT A gl h a.F = true := by
      rw [← vals_at A hh h5 hgl]
      exact hp
    rw [keysBlank_at A hh h5 hgl] at hk
    obtain ⟨i', hi', hk⟩ := Option.bind_eq_some_iff.1 hk
    obtain ⟨i, hi⟩ := real_in A hT hV hi'
    obtain ⟨S, eK⟩ := blank_sh hi hi'
    have r := keys_both (gl := gl) S eK
    rw [hk] at r
    cases hK : ((P.Runs.firstRun i.1 i.2).bind fun y =>
        P.Runs.keysRun i.1 (P.padOfO gl.shape) y.2) with
    | none =>
      rw [hK] at r
      exact r.elim
    | some KF =>
      rw [hK] at r
      have r' : formsSh KF = formsSh kf := r
      obtain ⟨x, hx⟩ := P.joinF_ret (g := gL) (KF := KF)
        ((size_of_formsSh r').trans hs1) hs2 a.F []
      have hF : s.fork? = some a.F := by
        unfold First.S.fork?
        rw [hh]
      have hg' : s.lookHeard? = some gL := by
        unfold First.S.lookHeard?
        rw [hh]
        exact hL
      have hKO : P.keysOfO A s = some KF := by
        rw [keysO_at A hh h5 hgl, hi]
        exact hK
      exact ⟨_, join_ok_of A hF hg' (by rw [unpaid_sh]; exact hu) hKO hx⟩

/-- A return of the run gives its premise on values: its key forms are made of the runs' input. -/
theorem pre_of_join {n : Nat} {s : First.S} {z : List Claim × First.S}
    (h : joinRunA A n s = .ok z) : preK5 A n s := by
  obtain ⟨_, _, KF, _, _, _, _, hK, _⟩ := join_ok_is A (cs := z.1) (s' := z.2) h
  unfold P.keysOfO P.keysOfK at hK
  obtain ⟨x, hx, _⟩ := Option.bind_eq_some_iff.1 hK
  exact pre_of_inOf A hx

end

end H2K5.Honest

#print axioms H2K5.Honest.unpaid_sh
#print axioms H2K5.Honest.fold_sh
#print axioms H2K5.Honest.range_getD
#print axioms H2K5.Honest.joinF_sh
#print axioms H2K5.Honest.joinF_counts
#print axioms H2K5.Honest.join_ok_is
#print axioms H2K5.Honest.join_ok_of
#print axioms H2K5.Honest.keysO_at
#print axioms H2K5.Honest.size_of_formsSh
#print axioms H2K5.Honest.joinG_ok_is
#print axioms H2K5.Honest.joinLaw
#print axioms H2K5.Honest.pre_of_join
