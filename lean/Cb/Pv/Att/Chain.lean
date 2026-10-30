-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/Chain.lean: a chain of masked sumchecks, draws and sent scalars as one reduction, with
knowledge soundness from the parts' own conditions.

Definitions, statements and proofs. No value of a sub-proof occurs here: maps, weights, claims and
linear claims are parameters. A sub-proof's own rounds are a row of stages of three kinds: a masked
sumcheck with short messages and further scalars in its first message (`rideNR`,
Cb/Pv/Att/Ride.lean); a round with an empty message in which the verifier draws (`IOR.draw`,
Ior/Draw.lean); a round in which scalars are sent and then the verifier draws (`send`,
Cb/Pv/Lay/Draws.lean). The statement grows: each stage puts what was sent, drawn and put out behind
the statement that it found.

Main names:
  `Ch E M X`: a chain that starts at statements of type X. M: the tuples of committed messages.
    `done`: no stage. `ride Y n F cl msg L Ow next`: a sumcheck with the parameters Y, n further
    scalars r, the pick F, the claim `cl x r`, the reading msg of the messages; `L x r m`: what is
    claimed of the further scalars and is not tested here; `Ow b m`: the part of the sumcheck's
    output claims that is still owed at the chain's end. `draw D err P next`: a draw from D; `P x
    m`: what is claimed before it. `send n D err P L next`: n scalars, then a draw from D.
  `c.End`, `c.back`: the type of the last statements; the first statement inside a last one.
  `c.R Ex`: the reduction. `c.eps Ex`: its errors: each a count among its own round's draws.
    `c.nums`, `Ch.errList_eps`: their list. `c.sh`, `Ch.shape_R`: its rounds.
  `c.Todo x m`: what is claimed at the start, defined from the back. At a sumcheck: there are
    further scalars r with `L x r m`, the sum claim `cl x r` holds, and for some output o the rest's
    claim holds at ((x, r), o). At a draw and at sent scalars: P.
  `c.Last Dn`: what is claimed at the end: Dn of the first statement, every L, and every Ow.
  `c.OK`: the conditions. At a sumcheck: the library's three (`VarsOK`, `DegOK`, `ValInj`), and: Ow
    together with the rest's claim gives the sumcheck's output claims. So an output claim that a
    later stage's claim gives is not owed at the end. At a draw: for every x and m of which P is
    false, at most err draws make the rest's claim true. So whatever claim rides past a draw must be
    a conjunct of P as well as of the rest's claim: where it is false no draw makes the rest's claim
    true, and the count is 0. The conditions do not ask the converse: a claim of the rest's that P
    leaves out is lost from `c.Todo`, and `Ch.knowAt` is then silent on it. At sent scalars: the
    same for every tuple of scalars of which L is true.
  `Ch.knowAt`: under `c.OK`, `KnowAt` (Cb/G6/Cut.lean) from "Dn and `c.Todo`" to `c.Last Dn`, beside
    any joint A0 on a part of the first statement, with the errors `c.eps`.

Limits: nothing on an honest prover, completeness or zero knowledge. The messages m are fixed before
the chain's first round. `c.Last` is a claim that whoever follows must discharge: the chain tests
nothing of L or of Ow. Where a later stage's claim reads an earlier sumcheck's output o, `c.Todo`
keeps of it only that it holds for some o: what hangs on a sumcheck's own challenges cannot stand in
a claim before that sumcheck. What does not read o is kept whole (`Ch.todo_ride_const`). The
conditions at draws and sent scalars speak of all m: they are laws on the parameters, to be proved
at a value.

-/
import Cb.Pv.Att.Ride
import Cb.Pv.Lay.Draws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att
open Iop Prob Cb IOR TWhole Johnson.L5.Layers Johnson.L5.Door Cb.Pv.Lay

/-- A joint: A0 at a part of the statement, and a claim G on the statement and the messages. -/
def jt {Kc X0 X M Wp : Type} {Ex : ExtSpec} (A0 : Rels Kc X0 Ex (M × Wp)) (pr : X → X0)
    (G : X → M → Prop) : Rels Kc X Ex (M × Wp) :=
  ⟨fun x y w => A0.rel (pr x) y w ∧ G x w.1, fun a w => A0.relR (pr a.1, a.2) w ∧ G a.1 w.1,
    fun a => A0.on (pr a.1, a.2), A0.core⟩

/-- A finite set of draws that is not empty. -/
structure Dr where
  D : Type
  [fin : Fintype D]
  [ne : Nonempty D]

attribute [instance] Dr.fin Dr.ne

/-- A chain of stages that starts at statements of type X. -/
inductive Ch (E : Type) [Field E] [Fintype E] (M : Type) : Type → Type 1
  | done (X : Type) : Ch E M X
  | ride {X : Type} (Y : PscPar E) (n : ℕ) (F : ∀ st, HFixs (Y.vars st))
      (cl : X → (Fin n → E) → E × Y.St) (msg : M → Y.J → E) (L : X → (Fin n → E) → M → Prop)
      (Ow : (X × (Fin n → E)) × Y.Out → M → Prop)
      (next : Ch E M ((X × (Fin n → E)) × Y.Out)) : Ch E M X
  | draw {X : Type} (D : Dr) (err : ℕ) (P : X → M → Prop) (next : Ch E M (X × D.D)) : Ch E M X
  | send {X : Type} (n : ℕ) (D : Dr) (err : ℕ) (P : X → M → Prop)
      (L : X → (Fin n → E) → M → Prop) (next : Ch E M ((X × (Fin n → E)) × D.D)) : Ch E M X

variable {E : Type} [Field E] [Fintype E] {M : Type}

namespace Ch

/-- The type of the last statements. -/
def End : {X : Type} → Ch E M X → Type
  | X, .done _ => X
  | _, .ride _ _ _ _ _ _ _ next => next.End
  | _, .draw _ _ _ next => next.End
  | _, .send _ _ _ _ _ next => next.End

/-- The first statement inside a last one. -/
def back : {X : Type} → (c : Ch E M X) → c.End → X
  | _, .done _ => fun e => e
  | _, .ride _ _ _ _ _ _ _ next => fun e => (next.back e).1.1
  | _, .draw _ _ _ next => fun e => (next.back e).1
  | _, .send _ _ _ _ _ next => fun e => (next.back e).1.1

/-- The reduction. -/
noncomputable def R (Ex : ExtSpec) : {X : Type} → (c : Ch E M X) → IOR X Ex c.End Ex
  | _, .done _ => IOR.pure some (ExtMap.id Ex)
  | _, .ride Y n F cl _ _ _ next => (rideNR Y n F cl Ex).seq (next.R Ex)
  | _, .draw D _ _ next => (IOR.draw D.D (fun x β => (x, β)) Ex).seq (next.R Ex)
  | _, .send n D _ _ _ next => (Lay.send E (Fin n) D.D _ Ex).seq (next.R Ex)

/-- Its errors. -/
noncomputable def eps (Ex : ExtSpec) : {X : Type} → (c : Ch E M X) → Err (c.R Ex).shape
  | _, .done _ => ()
  | _, .ride Y n _ _ _ _ _ next => Err.app (rideNE Y n Ex) (next.eps Ex)
  | _, .draw D err _ next => Err.app (s := [drawRound D.D]) (err, ()) (next.eps Ex)
  | _, .send n D err _ _ next =>
    Err.app (s := [sendRound E (Fin n) D.D]) (err, ()) (next.eps Ex)

/-- The list of its errors. -/
def nums : {X : Type} → Ch E M X → List ℕ
  | _, .done _ => []
  | _, .ride Y _ _ _ _ _ _ next => (1 :: (Y.fmt.map PFmt.n ++ [0])) ++ next.nums
  | _, .draw _ err _ next => [err] ++ next.nums
  | _, .send _ _ err _ _ next => [err] ++ next.nums

/-- Its rounds. -/
def sh : {X : Type} → Ch E M X → Shape
  | _, .done _ => []
  | _, .ride Y n _ _ _ _ _ next => shapeRN Y n ++ next.sh
  | _, .draw D _ _ next => [drawRound D.D] ++ next.sh
  | _, .send n D _ _ _ next => [sendRound E (Fin n) D.D] ++ next.sh

/-- What is claimed at the start, defined from the back. -/
def Todo : {X : Type} → Ch E M X → X → M → Prop
  | _, .done _ => fun _ _ => True
  | _, .ride Y _ _ cl msg L _ next => fun x m =>
    ∃ r, L x r m ∧ Y.SumHolds (cl x r) (msg m) ∧ ∃ o, next.Todo ((x, r), o) m
  | _, .draw _ _ P _ => P
  | _, .send _ _ _ P _ _ => P

/-- What is claimed at the end. -/
def Last : {X : Type} → (c : Ch E M X) → (X → M → Prop) → c.End → M → Prop
  | _, .done _, Dn => Dn
  | _, .ride _ _ _ _ _ L Ow next, Dn => next.Last fun b m => Dn b.1.1 m ∧ L b.1.1 b.1.2 m ∧ Ow b m
  | _, .draw _ _ _ next, Dn => next.Last fun b m => Dn b.1 m
  | _, .send _ _ _ _ L next, Dn => next.Last fun b m => Dn b.1.1 m ∧ L b.1.1 b.1.2 m

/-- The conditions. -/
def OK : {X : Type} → Ch E M X → Prop
  | _, .done _ => True
  | _, .ride Y _ _ _ msg _ Ow next =>
    (Y.VarsOK ∧ Y.DegOK ∧ Y.ValInj) ∧
      (∀ b m, Ow b m → next.Todo b m → Y.OutHolds b.2 (msg m)) ∧ next.OK
  | _, .draw _ err P next =>
    (∀ x m, ¬ P x m → cnt (fun β => next.Todo (x, β) m) ≤ err) ∧ next.OK
  | _, .send _ _ err P L next =>
    (∀ x m, ¬ P x m → ∀ s, L x s m → cnt (fun β => next.Todo ((x, s), β) m) ≤ err) ∧ next.OK

end Ch

/-! ### The stages, each between joints of the one form -/

section Stages
variable {Kc X0 X Wp : Type} {Ex : ExtSpec} (A0 : Rels Kc X0 Ex (M × Wp)) (pr : X → X0)
  (Dn : X → M → Prop)

/-- No stage. -/
theorem done_knowAt :
    KnowAt (IOR.pure (some : X → Option X) (ExtMap.id Ex)) (jt A0 pr fun x m => Dn x m ∧ True)
      (jt A0 pr Dn) (fun _ _ _ wp => wp) () where
  point := ⟨()⟩
  isLocal :=
    { out := fun _ _ _ _ _ _ _ _ _ => rfl
      imp := fun _ _ _ _ q _ _ h _ => h q (Finset.mem_singleton_self q) }
  onOut := fun a _ b ha hb => by
    have e : (a.1, a.2) = b := Option.some.inj hb
    rw [← e]
    exact ha
  know := fun _ a _ => Doomed.of_forall _ _ fun _ b wp hb hw => by
    have e : (a.1, a.2) = b := Option.some.inj hb
    rw [← e] at hw
    exact ⟨hw.1, hw.2, trivial⟩

/-- A sumcheck. T: the rest's claim. -/
theorem ride_knowAt (Y : PscPar E) (n : ℕ) (F : ∀ st, HFixs (Y.vars st))
    (cl : X → (Fin n → E) → E × Y.St) (msg : M → Y.J → E) (L : X → (Fin n → E) → M → Prop)
    (Ow T : (X × (Fin n → E)) × Y.Out → M → Prop) (hV : Y.VarsOK) (hD : Y.DegOK) (hI : Y.ValInj)
    (hO : ∀ b m, Ow b m → T b m → Y.OutHolds b.2 (msg m)) :
    KnowAt (rideNR Y n F cl Ex)
      (jt A0 pr fun x m =>
        Dn x m ∧ ∃ r, L x r m ∧ Y.SumHolds (cl x r) (msg m) ∧ ∃ o, T ((x, r), o) m)
      (jt A0 (fun b => pr b.1.1) fun b m =>
        (Dn b.1.1 m ∧ L b.1.1 b.1.2 m ∧ Ow b m) ∧ T b m)
      (fun _ _ _ wp => wp) (rideNE Y n Ex) :=
  have g := rideN_knowAt Y n F cl Ex (jt A0 pr fun _ _ => True) msg (fun _ _ _ => True) hV hD hI
  { point := g.point
    isLocal := g.isLocal
    onOut := fun a τ b ha hb => g.onOut a τ b ha hb
    know := fun m a _ => by
      refine Doomed.mono _ _ ?_ (rideN_doomed Y n F cl Ex hV hD hI a.1 a.2 (msg m))
      intro τ hτ b wp hb hB
      obtain ⟨xo, hxo, rfl⟩ := Option.map_eq_some_iff.1 hb
      obtain ⟨o, ho, rfl⟩ := Option.map_eq_some_iff.1 hxo
      have hs : Y.SumHolds (cl a.1 (riders Y n τ)) (msg m) := by
        by_contra hn
        exact hτ hn o ho (hO _ m hB.2.1.2.2 hB.2.2)
      exact ⟨hB.1, hB.2.1.1, riders Y n τ, hB.2.1.2.1, hs, o, hB.2.2⟩ }

/-- A draw. T: the rest's claim. -/
theorem draw_knowAt (D : Type) [Fintype D] [Nonempty D] (err : ℕ) (P : X → M → Prop)
    (T : X × D → M → Prop) (h : ∀ x m, ¬ P x m → cnt (fun β => T (x, β) m) ≤ err) :
    KnowAt (IOR.draw D (fun (x : X) β => (x, β)) Ex) (jt A0 pr fun x m => Dn x m ∧ P x m)
      (jt A0 (fun b => pr b.1) fun b m => Dn b.1 m ∧ T b m) (fun _ _ _ wp => wp)
      ((err, ()) : ℕ × Unit) :=
  knowAt_draw (fun (x : X) β => (x, β)) _ _ err (fun _ _ _ ha => ha) fun x _ m _ => by
    by_cases hP : P x m
    · rw [cnt_false fun β hβ => by
        obtain ⟨_, h1, h2⟩ := hβ
        exact h2 ⟨h1.1, h1.2.1, hP⟩]
      exact Nat.zero_le _
    · refine le_trans (cnt_mono fun β hβ => ?_) (h x m hP)
      obtain ⟨_, h1, _⟩ := hβ
      exact h1.2.2

omit [Fintype E] in
/-- Scalars, then a draw. T: the rest's claim. -/
theorem send_knowAtM (n : ℕ) (D : Type) [Fintype D] [Nonempty D] (err : ℕ) (P : X → M → Prop)
    (L : X → (Fin n → E) → M → Prop) (T : (X × (Fin n → E)) × D → M → Prop)
    (h : ∀ x m, ¬ P x m → ∀ s, L x s m → cnt (fun β => T ((x, s), β) m) ≤ err) :
    KnowAt (send E (Fin n) D X Ex) (jt A0 pr fun x m => Dn x m ∧ P x m)
      (jt A0 (fun b => pr b.1.1) fun b m => (Dn b.1.1 m ∧ L b.1.1 b.1.2 m) ∧ T b m)
      (fun _ _ _ wp => wp) ((err, ()) : ℕ × Unit) :=
  have g := send_knowAt (E := E) (ι := Fin n) (D := D) (J := Unit) (jt A0 pr fun _ _ => True)
    (fun _ _ => (0 : E)) (fun _ _ => True) (fun _ _ => True) 0 fun _ _ hn => absurd trivial hn
  { point := g.point
    isLocal := g.isLocal
    onOut := fun a τ b ha hb => g.onOut a τ b ha hb
    know := fun m a _ mm => by
      classical
      by_cases hP : P a.1 m
      · refine le_trans (le_of_eq (cnt_false fun β hβ => hβ fun b wp hb' hB => ?_)) (Nat.zero_le _)
        obtain ⟨h1, h2⟩ := IOR.red_out_eq_some.1 hb'
        have e : b = (((a.1, mm.2), β), a.2) := Prod.ext (Option.some.inj h1).symm h2
        rw [e] at hB
        exact ⟨hB.1, hB.2.1.1, hP⟩
      · by_cases hL : L a.1 mm.2 m
        · refine le_trans (cnt_mono fun β hβ => ?_) (h a.1 m hP mm.2 hL)
          by_contra hn
          refine hβ fun b wp hb' hB => ?_
          obtain ⟨h1, h2⟩ := IOR.red_out_eq_some.1 hb'
          have e : b = (((a.1, mm.2), β), a.2) := Prod.ext (Option.some.inj h1).symm h2
          rw [e] at hB
          exact absurd hB.2.2 hn
        · refine le_trans (le_of_eq (cnt_false fun β hβ => hβ fun b wp hb' hB => ?_))
            (Nat.zero_le _)
          obtain ⟨h1, h2⟩ := IOR.red_out_eq_some.1 hb'
          have e : b = (((a.1, mm.2), β), a.2) := Prod.ext (Option.some.inj h1).symm h2
          rw [e] at hB
          exact absurd hB.2.1.2 hL }

end Stages

/-! ### The chain -/

namespace Ch

/-- Knowledge soundness of the chain. This is said under the hypotheses that stand in the statement
itself, which this comment does not list; it is no claim that they hold. -/
theorem knowAt {Kc X0 Wp : Type} (Ex : ExtSpec) (A0 : Rels Kc X0 Ex (M × Wp)) :
    ∀ {X : Type} (c : Ch E M X) (pr : X → X0) (Dn : X → M → Prop), c.OK →
      KnowAt (c.R Ex) (jt A0 pr fun x m => Dn x m ∧ c.Todo x m)
        (jt A0 (fun e => pr (c.back e)) (c.Last Dn)) (fun _ _ _ wp => wp) (c.eps Ex)
  | _, .done _, pr, Dn, _ => done_knowAt A0 pr Dn
  | _, .ride Y n F cl msg L Ow next, pr, Dn, h =>
    knowAt_seq (ride_knowAt A0 pr Dn Y n F cl msg L Ow next.Todo h.1.1 h.1.2.1 h.1.2.2 h.2.1)
      (knowAt Ex A0 next (fun b => pr b.1.1) (fun b m => Dn b.1.1 m ∧ L b.1.1 b.1.2 m ∧ Ow b m)
        h.2.2)
  | _, .draw D err P next, pr, Dn, h =>
    knowAt_seq (draw_knowAt A0 pr Dn D.D err P next.Todo h.1)
      (knowAt Ex A0 next (fun b => pr b.1) (fun b m => Dn b.1 m) h.2)
  | _, .send n D err P L next, pr, Dn, h =>
    knowAt_seq (send_knowAtM A0 pr Dn n D.D err P L next.Todo h.1)
      (knowAt Ex A0 next (fun b => pr b.1.1) (fun b m => Dn b.1.1 m ∧ L b.1.1 b.1.2 m) h.2)

/-- The list of the chain's errors. -/
theorem errList_eps (Ex : ExtSpec) : ∀ {X : Type} (c : Ch E M X), errList (c.eps Ex) = c.nums
  | _, .done _ => rfl
  | _, .ride Y n _ _ _ _ _ next =>
    (errList_app _ _).trans (congrArg₂ (· ++ ·) (rideN_nums Y n Ex) (errList_eps Ex next))
  | _, .draw _ _ _ next => (errList_app _ _).trans (congrArg₂ (· ++ ·) rfl (errList_eps Ex next))
  | _, .send _ _ _ _ _ next =>
    (errList_app _ _).trans (congrArg₂ (· ++ ·) rfl (errList_eps Ex next))

/-- The chain's rounds. -/
theorem shape_R (Ex : ExtSpec) : ∀ {X : Type} (c : Ch E M X), (c.R Ex).shape = c.sh
  | _, .done _ => rfl
  | _, .ride Y n _ _ _ _ _ next => congrArg (shapeRN Y n ++ ·) (shape_R Ex next)
  | _, .draw D _ _ next => congrArg ([drawRound D.D] ++ ·) (shape_R Ex next)
  | _, .send n D _ _ _ next => congrArg ([sendRound E (Fin n) D.D] ++ ·) (shape_R Ex next)

/-- Where the rest's claim does not read the sumcheck's output, it is kept whole. -/
theorem todo_ride_const {X : Type} (Y : PscPar E) (n : ℕ) (F : ∀ st, HFixs (Y.vars st))
    (cl : X → (Fin n → E) → E × Y.St) (msg : M → Y.J → E) (L : X → (Fin n → E) → M → Prop)
    (Ow : (X × (Fin n → E)) × Y.Out → M → Prop)
    (next : Ch E M ((X × (Fin n → E)) × Y.Out)) (T : X × (Fin n → E) → M → Prop)
    (hT : ∀ b m, next.Todo b m ↔ T b.1 m) [Nonempty Y.Out] (x : X) (m : M) :
    (Ch.ride Y n F cl msg L Ow next).Todo x m ↔
      ∃ r, L x r m ∧ Y.SumHolds (cl x r) (msg m) ∧ T (x, r) m :=
  ⟨fun ⟨r, h1, h2, _, h3⟩ => ⟨r, h1, h2, (hT _ m).1 h3⟩,
    fun ⟨r, h1, h2, h3⟩ => ⟨r, h1, h2, Classical.arbitrary _, (hT _ m).2 h3⟩⟩

end Ch
end Cb.Pv.Att
