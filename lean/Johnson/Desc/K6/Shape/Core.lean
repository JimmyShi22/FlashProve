-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K6/Shape/Core.lean: the output head's four runs of claims ("norm", "join", "policy",
"logits") on shapes: each run as code on a view, with the laws that tie the code to the run.

What it is not. NOT YET A LAW ON THE WHOLE CHAIN's SHAPE: the runs on shapes stand here on `View`
(Seat.lean): just what these runs read. It does not say that a state at which a run returns is ever
reached, nor that the test on values holds anywhere. THE RUNS ARE THE KIND's OWN: in the list of an
IOP as written in Lean each stands under a guard that asks one test more behind it
(Johnson/Desc/SeatGuard.lean: Block.guarded): nothing is said of the guarded run. Nothing on any
property of the protocol. It stands on four files of Johnson/Desc/First/Shape/ (Seat.lean's head
names them).

  `plainSh`     the shape of a form's plain claim (claimSh_asClaim)
  `letters_spec`   THE HINGE: where the letters are read: a view; its tests and the test on values
                accept; the 35 forms' and the six key vectors' shapes are the code's
  `threeG p h iU3 name v`   **"norm" | "policy" | "logits" ON A VIEW**: the claims' shapes, or a
                rejection; the state stays
  `joinG p h iU3 v`   **"join" ON A VIEW**: the one claim's shape and the ledger's shape behind
  `threeG_of`, `unpaidB`, `unpaid_sh`, `lookup_map`   small laws beneath
  `Ends p s`    THE PREMISE ON VALUES, a structure with one field: where what the lookup heard is
                laid, endsB accepts it
  `three_strong`, `join_strong`   where the run returns: there is a view; the run on it returns the
                shapes of the run's claims (and of the ledger behind); the state behind is the state
                in front (with the ledger turned); AND Ends HOLDS: so the premise costs a caller
                nothing behind a return; in front of one it is the head's own step's test
  `three_returns`, `join_returns`   where the run on the view returns and Ends holds: the run
                returns
  `three_reply`, `join_reply`   where a run returns, the heard reply is as it was: what a law on the
                guarded run wants of each run; `three_keeps`, `join_keeps`: the same in the form
                of the guard's own test

-/
import Johnson.Desc.K6.Shape.Seat
import Johnson.Desc.Kinds.Law.K06Runs
import Johnson.Desc.Kinds.Law.HeadRunsCarry
import Johnson.Desc.ProofFile.Frames1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Shape
open OnBytes.Model (Aff Fork)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape (AffSh affSh ClaimSh claimSh LedSh ledSh paidB ledSh_paid
  heardAll)

/-- A run of claims, as a sub-protocol states it. -/
abbrev Run : Type := Nat → S → Except String (List Claim × S)

/-- The shape of the claim that a form is 0, under its own number's weight. -/
def plainSh (a : AffSh) : ClaimSh := ClaimSh.mk none a []

theorem claimSh_asClaim (f : Form) : claimSh (asClaim f) = plainSh (affSh f) := by
  rfl

/-- **THE PREMISE ON VALUES.** -/
structure Ends (p : Par) (s : S) : Prop where
  /-- where what the lookup heard is laid: each call's key point ends in the lookup's point -/
  ends : ∀ g, s.lookHeard? = some g → endsB p g = true

/-- **"norm" | "policy" | "logits" ON A VIEW.** -/
def threeG (p : Par) (h : OnBytes.Model.Head.Shape) (iU3 : Nat) (name : String) (v : View) :
    Except String (List ClaimSh) :=
  if lettersB p h iU3 v then
    named "the run is there" <|
      ((@formsSh p.sizes (v.leaves iU3)).lookup name).map fun fs => fs.map plainSh
  else .error "the letters, as far as a shape says"

/-- The debt of that number is not yet marked as paid. -/
def unpaidB (L : LedSh) (i : Nat) : Bool := L.owed[i]? != some true

/-- **"join" ON A VIEW.** -/
def joinG (p : Par) (h : OnBytes.Model.Head.Shape) (iU3 : Nat) (v : View) :
    Except String (List ClaimSh × LedSh) :=
  if unpaidB v.led v.look.owedJoin && lettersB p h iU3 v &&
      (callList.length == v.look.shape.calls.size && v.look.e == v.look.shape.calls.size) then
    .ok ([plainSh (joinSh (@keysSh p.sizes (v.leaves iU3)) v.look.cEnd)],
      v.led.setOwed (paidB v.led.owed v.look.owedJoin))
  else .error "join, as far as a shape says"

/-- A look-up in a list whose second members are mapped. -/
theorem lookup_map {α β : Type} (f : α → β) (name : String) :
    ∀ l : List (String × α), (l.map fun c => (c.1, f c.2)).lookup name = (l.lookup name).map f
  | [] => rfl
  | c :: l => by
    rw [List.map_cons, List.lookup_cons, List.lookup_cons, lookup_map f name l]
    cases name == c.1 <;> rfl

theorem unpaid_sh (F : Fork) (i : Nat) : K3.unpaid F i = unpaidB (ledSh F) i := by
  show (((F.owed[i]?).map (·.added)) != some true) =
    ((F.owed.toList.map (·.added))[i]? != some true)
  rw [List.getElem?_map, Array.getElem?_toList]

section Laws
variable (h : OnBytes.Model.Head.Shape) (iU3 : Nat) (p : Par)

/-- **Where the letters are read**: there is a view; the tests on it and the test on values
accept; the 35 forms' and the six key vectors' shapes are the code's at the view's leaves. -/
theorem letters_spec {s : S} {g : Given} {b : Behind} {x : Places}
    (e : lettersAt p (seatAt h iU3) s = .ok (g, b, x)) :
    ∃ v gl, viewOf s = some v ∧ s.lookHeard? = some gl ∧ v.look = heardAll gl ∧
      lettersB p h iU3 v = true ∧ endsB p gl = true ∧
      (((fun (_ : Given) (_ : Behind) (_ : Places) => claims) g b x).map
        fun c => (c.1, c.2.map affSh)) = @formsSh p.sizes (v.leaves iU3) ∧
      ((fun (g : Given) (_ : Behind) (_ : Places) =>
        g.calls.map fun c => affSh (keyVector key c.1 c.2)) g b x) =
          @keysSh p.sizes (v.leaves iU3) := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (view_of_letters h iU3 p e)
  obtain ⟨gl, hgl, hlook⟩ := view_look hv
  have hB := letters_iff h iU3 p hv hgl
  rw [e] at hB
  have hB' : (lettersB p h iU3 v && endsB p gl) = true := hB.symm
  rw [Bool.and_eq_true] at hB'
  obtain ⟨H, r, e1, e2, e3, e4⟩ := Law.lettersAt_ok h iU3 p e
  simp only [Prod.mk.injEq, true_and] at e4
  obtain ⟨rfl, rfl⟩ := e4
  obtain ⟨z, y, _, _, _, hgg⟩ := Law.Came.given_ok p (seatAt h iU3) s g e1
  have hL := leaves_at h iU3 hv e2 e3
  have hp : g.sizes = p.sizes := by rw [hgg]
  have hc : g.calls.map (·.2) = callList := by
    rw [hgg]
    exact @calls_keys_all p.sizes p.floor z.1 z.2
  letI := g
  letI : Norm.Heard := H.1
  letI : FinalNorm.Heard := H.2.1
  letI : Heard := H.2.2
  letI : FinalNorm.Reads := r.1
  letI : Reads := r.2
  refine ⟨v, gl, hv, hgl, hlook, hB'.1, hB'.2, ?_, ?_⟩
  · rw [← hp]
    exact claims_sh (v.leaves iU3) hL
  · rw [← hp]
    unfold keysSh
    rw [← hc, List.map_map]
    exact List.map_congr_left fun c _ => keyVector_sh (v.leaves iU3) hL c.1 c.2

/-- Where the tests on the view accept, the run on the view returns the code's list under the
run's name. -/
theorem threeG_of {v : View} (hB : lettersB p h iU3 v = true) (name : String)
    (fs : List AffSh) (hl : (@formsSh p.sizes (v.leaves iU3)).lookup name = some fs) :
    threeG p h iU3 name v = .ok (fs.map plainSh) := by
  unfold threeG
  rw [if_pos hB, hl]
  rfl

/-- **WHERE ONE OF THE THREE RUNS RETURNS.** -/
theorem three_strong (l piece : Nat) (name : String) (run : Run)
    (hrun : (kind asClaim (seatAt h iU3) l piece p).claims.lookup name = some run)
    (n : Nat) (s s' : S) (cs : List Claim) (hz : run n s = .ok (cs, s')) :
    (∃ v, viewOf s = some v ∧ threeG p h iU3 name v = .ok (cs.map claimSh)) ∧ s' = s ∧
      Ends p s := by
  obtain ⟨g, b, x, fs, h1, h2, h3⟩ :=
    Law.k6_run_spec asClaim (seatAt h iU3) l piece p name run n s s' cs hrun hz
  have hs : s' = s :=
    Law.k6_same h iU3 l piece p (name, run) (Law.lookup_mem _ _ _ hrun) n s (cs, s') hz
  obtain ⟨v, gl, hv, hgl, _, hB, hE, hF, _⟩ := letters_spec h iU3 p h1
  refine ⟨⟨v, hv, ?_⟩, hs, ⟨fun g' hg' => ?_⟩⟩
  · unfold threeG
    rw [if_pos hB, ← hF, lookup_map, h2, h3]
    show Except.ok ((fs.map affSh).map plainSh) = Except.ok ((fs.map asClaim).map claimSh)
    rw [List.map_map, List.map_map]
    rfl
  · rw [hgl] at hg'
    rw [← Option.some.inj hg']
    exact hE

/-- **WHERE THE RUN ON THE VIEW RETURNS AND THE PREMISE ON VALUES HOLDS, THE RUN RETURNS.** -/
theorem three_returns (l piece : Nat) (name : String) (run : Run)
    (hrun : (kind asClaim (seatAt h iU3) l piece p).claims.lookup name = some run)
    (n : Nat) (s : S) (v : View) (hv : viewOf s = some v) (y : List ClaimSh)
    (hg : threeG p h iU3 name v = .ok y) (hp : Ends p s) : ∃ z, run n s = .ok z := by
  have h1' : (runsBy ["norm", "policy", "logits"] (fun _ _ _ => claims)
      (fun g _ _ => g.calls.map fun c => keyVector key c.1 c.2) asClaim p
      (seatAt h iU3)).lookup name = some run := hrun
  unfold runsBy at h1'
  have hr := Law.lookup_map_self _ _ _ _ h1'
  obtain ⟨gl, hgl, _⟩ := view_look hv
  unfold threeG at hg
  by_cases hB : lettersB p h iU3 v = true
  · rw [if_pos hB] at hg
    have hI := letters_iff h iU3 p hv hgl
    rw [hB, hp.ends gl hgl] at hI
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hI
    obtain ⟨g, b, x⟩ := w
    have hw' : lettersAt p (seatAt h iU3) s = .ok (g, b, x) := by
      cases hx : lettersAt p (seatAt h iU3) s with
      | error m =>
        rw [hx] at hw
        cases hw
      | ok w' =>
        rw [hx] at hw
        exact congrArg Except.ok (Option.some.inj hw)
    obtain ⟨v', _, hv', _, _, _, _, hF, _⟩ := letters_spec h iU3 p hw'
    rw [hv] at hv'
    obtain rfl := Option.some.inj hv'
    rw [← hF, lookup_map] at hg
    cases hl : ((fun (_ : Given) (_ : Behind) (_ : Places) => claims) g b x).lookup name with
    | none =>
      rw [hl] at hg
      cases hg
    | some fs =>
      cases hres : run n s with
      | ok z => exact ⟨z, rfl⟩
      | error m =>
        exfalso
        rw [hr] at hres
        simp [hw', hl, named, bind, Except.bind, pure, Except.pure] at hres
  · rw [if_neg hB] at hg
    cases hg

/-- **WHERE "join" RETURNS.** G: the ledger behind. -/
theorem join_strong (n : Nat) (s s' : S) (cs : List Claim)
    (hz : K3.joinRun (K3.seatCalls asClaim) (callerKeys p (seatAt h iU3)) n s = .ok (cs, s')) :
    (∃ v G, viewOf s = some v ∧ s' = s.putFork G ∧
      joinG p h iU3 v = .ok (cs.map claimSh, ledSh G)) ∧ Ends p s := by
  obtain ⟨F, gl, hF, hgl, e2⟩ := Law.k6_join _ n s (cs, s') hz
  unfold K3.joinRun at hz
  simp only [bind, Except.bind] at hz
  have hF' : (K3.seatCalls asClaim).fork s = some F := hF
  have hg' : (K3.seatCalls asClaim).heard s = some gl := hgl
  simp only [hF', hg', named] at hz
  split at hz
  · cases hz
  · rename_i _ hu
    split at hz
    · cases hz
    · rename_i KF hKF
      split at hz
      · cases hz
      · rename_i y hy
        have hK : callerKeys p (seatAt h iU3) s = some KF := by
          cases hk : callerKeys p (seatAt h iU3) s with
          | none => simp [hk] at hKF
          | some K' =>
            simp [hk] at hKF
            rw [hKF]
        have hy' : First.Look.joinF gl KF F [] = some y := by
          cases hj : First.Look.joinF gl KF F [] with
          | none => simp [hj] at hy
          | some y' =>
            simp [hj] at hy
            rw [hy]
        obtain ⟨hsz, _, _, hf⟩ := (Law.Came.joinF_spec gl KF F y.2.1 [] y.2.2 y.1).mp hy'
        have hun : K3.unpaid F gl.owedJoin = true := by
          cases hq : K3.unpaid F gl.owedJoin with
          | false => simp [hq, need] at hu
          | true => rfl
        unfold callerKeys at hK
        obtain ⟨w, hw, hKF'⟩ := Option.map_eq_some_iff.mp hK
        obtain ⟨g, b, x⟩ := w
        have hl : lettersAt p (seatAt h iU3) s = .ok (g, b, x) := by
          cases hx : lettersAt p (seatAt h iU3) s with
          | error m =>
            rw [hx] at hw
            cases hw
          | ok w' =>
            rw [hx] at hw
            exact congrArg Except.ok (Option.some.inj hw)
        obtain ⟨v, gl', hv, hgl', hlook, hB, hE, _, hKs⟩ := letters_spec h iU3 p hl
        rw [hgl] at hgl'
        obtain rfl := Option.some.inj hgl'
        obtain ⟨o, _, _, _, _, hh, ho, _, _, _, _, hvv⟩ := view_spec hv
        have hled : v.led = ledSh F := by
          have e := (fork_at hh ho).symm.trans hF
          rw [hvv, ← Option.some.inj e]
        have ez := Except.ok.inj hz
        simp only [Prod.mk.injEq] at ez
        refine ⟨⟨v, F.paid gl.owedJoin, hv, e2, ?_⟩, ⟨fun g' hg2 => ?_⟩⟩
        · have hlen : KF.size = callList.length := by
            rw [← hKF', List.size_toArray, List.length_map,
              ← List.length_map (f := fun c => affSh (keyVector key c.1 c.2))]
            exact (congrArg List.length hKs).trans (by unfold keysSh; rw [List.length_map])
          have hsz' : (callList.length == (heardAll gl).shape.calls.size &&
              (heardAll gl).e == (heardAll gl).shape.calls.size) = true := by
            rw [← hlen]
            exact hsz
          have hc : (K3.unpaid F (heardAll gl).owedJoin && lettersB p h iU3 v &&
              (callList.length == (heardAll gl).shape.calls.size &&
                (heardAll gl).e == (heardAll gl).shape.calls.size)) = true := by
            rw [Bool.and_eq_true, Bool.and_eq_true]
            exact ⟨⟨hun, hB⟩, hsz'⟩
          have hk2 : KF.toList.map affSh = @keysSh p.sizes (v.leaves iU3) := by
            rw [← hKF', ← hKs]
            dsimp only
            rw [List.map_map]
            rfl
          unfold joinG
          rw [hlook, hled, ← unpaid_sh, if_pos hc, ← ez.1, ledSh_paid, ← hk2]
          show _ = Except.ok ([claimSh (asClaim y.1)], _)
          rw [hf, claimSh_asClaim, joinForm_sh]
          rfl
        · rw [hgl] at hg2
          rw [← Option.some.inj hg2]
          exact hE

/-- **WHERE "join" ON THE VIEW RETURNS AND THE PREMISE ON VALUES HOLDS, "join" RETURNS.** -/
theorem join_returns (n : Nat) (s : S) (v : View) (hv : viewOf s = some v)
    (y : List ClaimSh × LedSh) (hg : joinG p h iU3 v = .ok y) (hp : Ends p s) :
    ∃ z, K3.joinRun (K3.seatCalls asClaim) (callerKeys p (seatAt h iU3)) n s = .ok z := by
  obtain ⟨gl, hgl, hlook⟩ := view_look hv
  obtain ⟨o, _, _, _, _, hh, ho, _, _, _, _, hvv⟩ := view_spec hv
  have hF := fork_at hh ho
  have hled : v.led = ledSh o.F := by rw [hvv]
  unfold joinG at hg
  split at hg
  · rename_i hc
    rw [Bool.and_eq_true, Bool.and_eq_true] at hc
    obtain ⟨⟨hun, hB⟩, hsz⟩ := hc
    have hI := letters_iff h iU3 p hv hgl
    rw [hB, hp.ends gl hgl] at hI
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hI
    obtain ⟨g, b, x⟩ := w
    have hl : lettersAt p (seatAt h iU3) s = .ok (g, b, x) := by
      cases hx : lettersAt p (seatAt h iU3) s with
      | error m =>
        rw [hx] at hw
        cases hw
      | ok w' =>
        rw [hx] at hw
        exact congrArg Except.ok (Option.some.inj hw)
    obtain ⟨v', _, hv', _, _, _, _, _, hKs⟩ := letters_spec h iU3 p hl
    rw [hv] at hv'
    obtain rfl := Option.some.inj hv'
    have hK : callerKeys p (seatAt h iU3) s =
        some (g.calls.map fun c => keyVector key c.1 c.2).toArray := by
      unfold callerKeys
      rw [hl]
      rfl
    have hlen : (g.calls.map fun c => keyVector key c.1 c.2).toArray.size = callList.length := by
      rw [List.size_toArray, List.length_map,
        ← List.length_map (f := fun c => affSh (keyVector key c.1 c.2))]
      exact (congrArg List.length hKs).trans (by unfold keysSh; rw [List.length_map])
    have hj := (Law.Came.joinF_spec gl _ o.F (o.F.paid gl.owedJoin) [] [] _).mpr
      ⟨by rw [hlen]; rw [hlook] at hsz; exact hsz, rfl, rfl, rfl⟩
    rw [hled, hlook, ← unpaid_sh] at hun
    have hun' : K3.unpaid o.F gl.owedJoin = true := hun
    have hF' : (K3.seatCalls asClaim).fork s = some o.F := hF
    have hg' : (K3.seatCalls asClaim).heard s = some gl := hgl
    cases hres : K3.joinRun (K3.seatCalls asClaim) (callerKeys p (seatAt h iU3)) n s with
    | ok z => exact ⟨z, rfl⟩
    | error m =>
      exfalso
      unfold K3.joinRun at hres
      simp [hF', hg', hK, hj, hun', named, need, bind, Except.bind, pure, Except.pure] at hres
  · cases hg

/-- Where one of the three runs returns, the reply is as it was. -/
theorem three_reply (l piece : Nat) (name : String) (run : Run)
    (hrun : (kind asClaim (seatAt h iU3) l piece p).claims.lookup name = some run)
    (n : Nat) (s s' : S) (cs : List Claim) (hz : run n s = .ok (cs, s')) :
    s'.out.reply = s.out.reply := by
  rw [(three_strong h iU3 p l piece name run hrun n s s' cs hz).2.1]

/-- Where "join" returns, the reply is as it was. keys: any. -/
theorem join_reply (keys : S → Option (Array Aff)) (n : Nat) (s s' : S) (cs : List Claim)
    (hz : K3.joinRun (K3.seatCalls asClaim) keys n s = .ok (cs, s')) :
    s'.out.reply = s.out.reply := by
  obtain ⟨F, g, _, _, e2⟩ := Law.k6_join keys n s (cs, s') hz
  have e : s' = s.putFork (F.paid g.owedJoin) := e2
  rw [e]
  unfold S.putFork
  split <;> (try split) <;> rfl

/-- The same as the guard of a seated chain asks it (Johnson/Desc/ProofFile/Frames1.lean:
sameReply). -/
theorem three_keeps (l piece : Nat) (name : String) (run : Run)
    (hrun : (kind asClaim (seatAt h iU3) l piece p).claims.lookup name = some run)
    (n : Nat) (s s' : S) (cs : List Claim) (hz : run n s = .ok (cs, s')) :
    ProofFile.sameReply s s' = true := by
  unfold ProofFile.sameReply
  rw [three_reply h iU3 p l piece name run hrun n s s' cs hz]
  exact beq_self_eq_true _

/-- The like for "join". -/
theorem join_keeps (keys : S → Option (Array Aff)) (n : Nat) (s s' : S) (cs : List Claim)
    (hz : K3.joinRun (K3.seatCalls asClaim) keys n s = .ok (cs, s')) :
    ProofFile.sameReply s s' = true := by
  unfold ProofFile.sameReply
  rw [join_reply keys n s s' cs hz]
  exact beq_self_eq_true _

end Laws

end VerifiableInference.Desc.Kinds.Head.Shape

#print axioms VerifiableInference.Desc.Kinds.Head.Shape.claimSh_asClaim
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.lookup_map
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.unpaid_sh
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.letters_spec
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.threeG_of
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.three_strong
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.three_returns
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.join_strong
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.join_returns
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.three_reply
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.join_reply
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.three_keeps
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.join_keeps
