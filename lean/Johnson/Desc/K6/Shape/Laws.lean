-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K6/Shape/Laws.lean: what the output head's four runs of claims owe on the shape of the
first chain's state: one term of RunLaw (Johnson/Desc/First/Batch/Shape/ClaimShape.lean) a run.

What it is not. THE RUNS ARE THE KIND's OWN, not the guarded runs in the list of an IOP as written
in Lean (Johnson/Desc/SeatGuard.lean: Block.guarded); from the seated sub-protocol's runs to these:
Johnson/Desc/Kinds/Law/SeatedRuns.lean. It does not say that the chain ever reaches a shape at which
a run on shapes returns, nor a state at which the premise holds: for one shape and one state of a
small plan see Toy.lean beside it; of the full size nothing is said. Nothing on any property of the
protocol. It stands on files of Johnson/Desc/First/Shape/, on ClaimShape.lean and on what these
import; of the chain's shape it wants that the head's part holds the shape of what the head's own
rounds heard (x) and the table of the tables of reads (tab): over a HeadPart.lean whose HeadSh has
not both fields this file does not elaborate.

  `viewSh`, `view_sh`   the view (Seat.lean) read off the chain's shape; at a state's shape it is
                the state's view
  `threeRunG`, `joinRunG`   THE RUNS ON SHAPES, by name
  `three_runG_returns`, `join_runG_returns`   where the run returns, its run on shapes returns at
                the state's shape, with the shapes of what the run returns
  `bare`, `bare_look`   the kind's own run of a name, read off the kind's own list (lookup_isSome)
  `threeLaw`    one of the three runs, general in its name and in the run that stands under it
  `normLaw`, `joinLaw`, `policyLaw`, `logitsLaw`   **THE FOUR TERMS**, each at a run that is a term
  `*_runG`, `*_pre`   each term's run on shapes and its premise, by name: equations by rfl
  `three_pre`, `join_pre`   a return of the run gives its premise
AT THE FILE's FOOT the axioms are asked of 16 names: the 11 theorems, and the 5 terms of RunLaw
(threeLaw and the four), whose fields carries and returns are proofs inside a definition.
THE PREMISE of all four is `Ends p s` (Core.lean): one test on values: where what the lookup heard
is laid, each call's key point ends in the lookup's point. WHO PAYS IT: each run asks that test
itself, so a return pays it; in front of a return: whoever has that `given`
(Johnson/Desc/Kinds/HeadFrame.lean) returned at a state in which the lookup's points are the same:
the head's own step asks it.

-/
import Johnson.Desc.K6.Shape.Core
import Johnson.Desc.First.Batch.Shape.ClaimShape
import Johnson.Desc.Kinds.Law.SeatedRuns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Shape
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Shape (ChainSh chainSh ClaimSh claimSh ledSh heardAll hereNo
  headOf pscSh headHeardSh chainSh_putFork)
open VerifiableInference.Desc.K9.Shape (RunLaw)

/-- The view, read off the chain's shape: the chain stands in the head's link, opened; the ledger,
what the lookup heard, the level's sumcheck, what the head heard and the tables are there. -/
def viewSh (a : ChainSh) : Option View :=
  if a.here == 3 then
    a.led.bind fun led => a.lookHeard.bind fun look => a.head.bind fun hd =>
      hd.squaresP.bind fun Q => hd.x.bind fun X => hd.tab.map fun tab =>
        { reply := a.reply, led := led, look := look, Q := Q, X := X, tab := tab }
  else none

/-- At a state's shape it is the state's view. -/
theorem view_sh (s : S) : viewSh (chainSh s) = viewOf s := by
  unfold viewSh viewOf
  cases hh : s.here with
  | head o =>
    have e1 : (chainSh s).here = hereNo s.here := rfl
    have e2 : (chainSh s).led = s.fork?.map ledSh := rfl
    have e3 : (chainSh s).lookHeard = s.lookHeard?.map heardAll := rfl
    have e5 : (chainSh s).head = headOf s.here := rfl
    rw [e1, e2, e3, e5, hh]
    cases hop : o.opened with
    | true =>
      have h3 : (hereNo (First.Here.head o) == 3) = true := by
        show ((if o.opened then 3 else 4 : Nat) == 3) = true
        rw [hop]
        rfl
      rw [fork_at hh hop, look_at hh hop, if_pos h3]
      show ((o.lookHeard.map heardAll).bind fun look => (o.squaresP.map pscSh).bind fun Q =>
          (o.x.map headHeardSh).bind fun X => (o.t.map (·.tab)).map fun tab =>
            ({ reply := s.out.reply.isSome, led := ledSh o.F, look := look, Q := Q, X := X,
               tab := tab } : View)) =
        (if o.opened = true then
          (o.lookHeard.bind fun g => o.squaresP.bind fun q => o.x.bind fun x => o.t.map fun tt =>
            ({ reply := s.out.reply.isSome, led := ledSh o.F, look := heardAll g, Q := pscSh q,
               X := headHeardSh x, tab := tt.tab } : View))
        else none)
      rw [if_pos hop]
      cases o.lookHeard <;> cases o.squaresP <;> cases o.x <;> cases o.t <;> rfl
    | false =>
      have h4 : ¬ (hereNo (First.Here.head o) == 3) = true := by
        show ¬ ((if o.opened then 3 else 4 : Nat) == 3) = true
        rw [hop]
        exact Bool.false_ne_true
      rw [if_neg h4]
      show none = (if o.opened = true then _ else none)
      rw [if_neg (by rw [hop]; exact Bool.false_ne_true)]
  | _ =>
    have e1 : ((chainSh s).here == 3) = false := by
      show (hereNo s.here == 3) = false
      rw [hh]
      rfl
    rw [e1]
    rfl

/-- A name that stands in a list is found there. -/
theorem lookup_isSome {α : Type} : ∀ (l : List (String × α)) (n : String), n ∈ l.map (·.1) →
    (l.lookup n).isSome = true
  | [], _, hn => by simp at hn
  | c :: l, n, hn => by
    rw [List.lookup_cons]
    cases hc : n == c.1 with
    | true => rfl
    | false =>
      have hl : n ∈ l.map (·.1) := by
        simp only [List.map_cons, List.mem_cons] at hn
        rcases hn with e | e
        · rw [e] at hc
          simp at hc
        · exact e
      exact lookup_isSome l n hl

section Laws
variable (h : OnBytes.Model.Head.Shape) (iU3 : Nat) (p : Par)

/-- **"norm" | "policy" | "logits" ON THE CHAIN's SHAPE**: the claims' shapes; the shape stays. -/
def threeRunG (name : String) (_ : Nat) (a : ChainSh) : Except String (List ClaimSh × ChainSh) :=
  (named "the head's view" (viewSh a)).bind fun v =>
    (threeG p h iU3 name v).map fun cs => (cs, a)

/-- **"join" ON THE CHAIN's SHAPE**: the one claim's shape; the ledger's shape turns. -/
def joinRunG (_ : Nat) (a : ChainSh) : Except String (List ClaimSh × ChainSh) :=
  (named "the head's view" (viewSh a)).bind fun v =>
    (joinG p h iU3 v).map fun y => (y.1, a.setLed y.2)

/-- Where one of the three runs returns, the run on shapes returns at the state's shape: so
"carries" speaks at every return. -/
theorem three_runG_returns (l piece : Nat) (name : String) (run : Run)
    (hrun : (kind asClaim (seatAt h iU3) l piece p).claims.lookup name = some run)
    (n : Nat) (s s' : S) (cs : List Claim) (hz : run n s = .ok (cs, s')) :
    threeRunG h iU3 p name n (chainSh s) = .ok (cs.map claimSh, chainSh s') := by
  obtain ⟨⟨v, hv, hG⟩, hs, _⟩ := three_strong h iU3 p l piece name run hrun n s s' cs hz
  unfold threeRunG
  rw [view_sh, hv, hs]
  show (threeG p h iU3 name v).map (fun cs => (cs, chainSh s)) = _
  rw [hG]
  rfl

/-- The like for "join". -/
theorem join_runG_returns (n : Nat) (s s' : S) (cs : List Claim)
    (hz : K3.joinRun (K3.seatCalls asClaim) (callerKeys p (seatAt h iU3)) n s = .ok (cs, s')) :
    joinRunG h iU3 p n (chainSh s) = .ok (cs.map claimSh, chainSh s') := by
  obtain ⟨⟨v, G, hv, hs, hG⟩, _⟩ := join_strong h iU3 p n s s' cs hz
  unfold joinRunG
  rw [view_sh, hv, hs, chainSh_putFork]
  show (joinG p h iU3 v).map (fun y => (y.1, (chainSh s).setLed y.2)) = _
  rw [hG]
  rfl

/-- One of the three runs, general in its name. -/
def threeLaw (l piece : Nat) (name : String) (run : Run)
    (hrun : (kind asClaim (seatAt h iU3) l piece p).claims.lookup name = some run) :
    RunLaw run where
  runG := threeRunG h iU3 p name
  pre := fun _ s => Ends p s
  carries := fun n s s' cs _ _ hz hg =>
    Except.ok.inj (hg.symm.trans (three_runG_returns h iU3 p l piece name run hrun n s s' cs hz))
  returns := fun n s _ hg hp => by
    unfold threeRunG at hg
    rw [view_sh] at hg
    cases hv : viewOf s with
    | none =>
      rw [hv] at hg
      cases hg
    | some v =>
      rw [hv] at hg
      cases ht : threeG p h iU3 name v with
      | error m =>
        have hg' : (threeG p h iU3 name v).map (fun cs => (cs, chainSh s)) = .ok _ := hg
        rw [ht] at hg'
        cases hg'
      | ok cs => exact three_returns h iU3 p l piece name run hrun n s v hv cs ht hp

/-- The kind's own run of that name, read off the kind's own list: no second text. Where the list
has no such name: a run that rejects. THE LIST HAS THREE NAMES; "join" IS NOT AMONG THEM: it is laid
in beside them (Johnson/Desc/Kinds/HeadCaller.lean: kindWithJoin), and its term is K3.joinRun at the
head's key vectors: see joinLaw. -/
def bare (l piece : Nat) (name : String) : Run :=
  ((kind asClaim (seatAt h iU3) l piece p).claims.lookup name).getD fun _ _ => .error "no such run"

/-- Under each of the three names the kind's list holds that run. -/
theorem bare_look (l piece : Nat) (name : String) (hn : name ∈ ["norm", "policy", "logits"]) :
    (kind asClaim (seatAt h iU3) l piece p).claims.lookup name =
      some (bare h iU3 p l piece name) := by
  have hs := lookup_isSome (kind asClaim (seatAt h iU3) l piece p).claims name
    (by rw [Law.kind_names]; exact hn)
  obtain ⟨r, hr⟩ := Option.isSome_iff_exists.mp hs
  unfold bare
  rw [hr]
  rfl

/-- **"norm".** -/
def normLaw (l piece : Nat) : RunLaw (bare h iU3 p l piece "norm") :=
  threeLaw h iU3 p l piece "norm" _ (bare_look h iU3 p l piece "norm" (by simp))

/-- **"policy".** -/
def policyLaw (l piece : Nat) : RunLaw (bare h iU3 p l piece "policy") :=
  threeLaw h iU3 p l piece "policy" _ (bare_look h iU3 p l piece "policy" (by simp))

/-- **"logits".** -/
def logitsLaw (l piece : Nat) : RunLaw (bare h iU3 p l piece "logits") :=
  threeLaw h iU3 p l piece "logits" _ (bare_look h iU3 p l piece "logits" (by simp))

/-- **"join".** -/
def joinLaw : RunLaw (K3.joinRun (K3.seatCalls asClaim) (callerKeys p (seatAt h iU3))) where
  runG := joinRunG h iU3 p
  pre := fun _ s => Ends p s
  carries := fun n s s' cs _ _ hz hg =>
    Except.ok.inj (hg.symm.trans (join_runG_returns h iU3 p n s s' cs hz))
  returns := fun n s _ hg hp => by
    unfold joinRunG at hg
    rw [view_sh] at hg
    cases hv : viewOf s with
    | none =>
      rw [hv] at hg
      cases hg
    | some v =>
      rw [hv] at hg
      cases ht : joinG p h iU3 v with
      | error m =>
        have hg' : (joinG p h iU3 v).map (fun y => (y.1, (chainSh s).setLed y.2)) = .ok _ := hg
        rw [ht] at hg'
        cases hg'
      | ok y => exact join_returns h iU3 p n s v hv y ht hp

theorem threeLaw_runG (l piece : Nat) (name : String) (run : Run)
    (hrun : (kind asClaim (seatAt h iU3) l piece p).claims.lookup name = some run) :
    (threeLaw h iU3 p l piece name run hrun).runG = threeRunG h iU3 p name := rfl

theorem threeLaw_pre (l piece : Nat) (name : String) (run : Run)
    (hrun : (kind asClaim (seatAt h iU3) l piece p).claims.lookup name = some run) :
    (threeLaw h iU3 p l piece name run hrun).pre = fun _ s => Ends p s := rfl

theorem joinLaw_runG : (joinLaw h iU3 p).runG = joinRunG h iU3 p := rfl

theorem joinLaw_pre : (joinLaw h iU3 p).pre = fun _ s => Ends p s := rfl

/-- A return of one of the three runs gives its premise. -/
theorem three_pre (l piece : Nat) (name : String) (run : Run)
    (hrun : (kind asClaim (seatAt h iU3) l piece p).claims.lookup name = some run)
    (n : Nat) (s : S) (z : List Claim × S) (hz : run n s = .ok z) :
    (threeLaw h iU3 p l piece name run hrun).pre n s := by
  obtain ⟨cs, s'⟩ := z
  exact (three_strong h iU3 p l piece name run hrun n s s' cs hz).2.2

/-- A return of "join" gives its premise. -/
theorem join_pre (n : Nat) (s : S) (z : List Claim × S)
    (hz : K3.joinRun (K3.seatCalls asClaim) (callerKeys p (seatAt h iU3)) n s = .ok z) :
    (joinLaw h iU3 p).pre n s := by
  obtain ⟨cs, s'⟩ := z
  exact (join_strong h iU3 p n s s' cs hz).2

end Laws

end VerifiableInference.Desc.Kinds.Head.Shape

#print axioms VerifiableInference.Desc.Kinds.Head.Shape.view_sh
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.lookup_isSome
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.three_runG_returns
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.join_runG_returns
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.bare_look
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.threeLaw_runG
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.threeLaw_pre
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.joinLaw_runG
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.joinLaw_pre
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.three_pre
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.join_pre
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.threeLaw
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.normLaw
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.policyLaw
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.logitsLaw
#print axioms VerifiableInference.Desc.Kinds.Head.Shape.joinLaw
