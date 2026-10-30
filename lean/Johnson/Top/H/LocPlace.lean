-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/LocPlace.lean: the law of a place (`KObj.RowCar.PlaceAt`,
Johnson/Top/H/RowMeet.lean) at the two rounds "SEND seed" and "LOC" of the code switch between two
groups of a request's chain, for the block of the kind `kSendLocRideInto`
(Johnson/Top/H/SendLocInto.lean). Definitions, statements and proofs.

What it is for. The laws of the places of a chain, laid behind each other, say: the written
transcript has an image, and on it the typed chain's verifier puts out the last statement. The law
of one place says: if the rounds that the run has still to take begin with the reading of this
place's written stretch, then the stretch has an image under the place's map, the block's verifier
puts out on it the statement from which the next block starts, and the rounds still to be taken are
the rest.

The two written rounds r₁, r₂ and seven readings are letters (`Rd`): view₁, view₂ read a written
prover's and verifier's message as a round of a view; words and mask read the new members' words and
the rider's word off the first written prover's message; rdSeed, rdAns, rdPos read what a view's
round drew as a joint seed, a list of the program's field elements as the members' answers, and what
a view's round drew as positions.

Main names:
  `Rd s r₁ r₂`: the seven readings. `Rd.ViewOK`: the items of the second round's view do not hang on
    the verifier's message.
  `ansOf rv`: the answers among a view's round's items.
  `Rd.carS`: the map of the place, a `CarryS` of two steps. `Rd.carS_fits`: which error counts of
    the written rounds bear the typed rounds'. `Rd.carS_tr`: its image of a written
  transcript.
  `Rd.after`: the typed statement behind the block, from the statement before, a joint seed,
    positions, answers, and the first written prover's message: the explicit part does not hang on
    the written stretch; THE NEW MEMBERS' WORDS AND THE RIDER DO.
  `loc_place`: from the record of a run of the switch on a view (`LocRan`), if rdSeed and rdPos are
    defined at what the run's two rounds drew: there are the rows with which the sampled oracle
    messages were admitted, and at every written stretch τ the law of the place holds, from the
    rounds to come before the run to those behind it, from a typed statement a to `Rd.after` at the
    readings of the record and at τ's first message.
Limits: r₁, r₂, the readings and the size are letters. Nothing says that the long symbols of the
typed open word at the positions read are the reading of the symbols that the program has read
(`LocTaken.y`). The law asks nothing of `ok`. One direction. Nothing on an honest prover.

-/
import OnBytes.Tie.Pv.Switch.LocAnswers
import Johnson.Top.H.SendLocInto
import Johnson.Top.H.RowMeet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Switch
open OnBytes OnBytes.Slice Iop OnBytes.Flat KObj KObj.RowCar VerifiableInference.OnPublicFiles Cb Cb.Pv

/-- The answers among a view's round's items. -/
def ansOf (rv : Fmt.RoundView) : List OnBytes.E :=
  rv.vals.filterMap fun g => match g with
    | .answer x => some (OnBytes.E.ofTriple x)
    | _ => none

theorem ansOf_answers (l : List OnBytes.E) (d : Fmt.Drawn) :
    ansOf ⟨l.map (fun x => Fmt.ItemValue.answer x.triple), d⟩ = l := by
  unfold ansOf
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.map_cons, List.filterMap_cons, OnBytes.E.ofTriple_triple]
    exact congrArg (x :: ·) ih

variable {K : Type} [Field K] [Fintype K] (s : SendLocRide.Size K) (r₁ r₂ : Round)

/-- The seven readings. -/
structure Rd where
  view₁  : r₁.Msg → r₁.Chal → Fmt.RoundView
  view₂  : r₂.Msg → r₂.Chal → Fmt.RoundView
  words  : r₁.Msg → s.sw.d.N.ext.Str
  mask   : r₁.Msg → s.Cw.Word
  rdSeed : Fmt.Drawn → Option s.sw.d.Sd.D
  rdAns  : List OnBytes.E → s.sw.d.N.Answ
  rdPos  : Fmt.Drawn → Option (Fin s.sw.t → s.sw.P)

variable {s r₁ r₂} (ρ : Rd s r₁ r₂)

/-- The items of the second round's view do not hang on the verifier's message. -/
def Rd.ViewOK : Prop := ∀ m c c', (ρ.view₂ m c).vals = (ρ.view₂ m c').vals

/-- The answers off a second written prover's message. -/
noncomputable def Rd.answ (m₂ : r₂.Msg) : s.sw.d.N.Answ :=
  ρ.rdAns (ansOf (ρ.view₂ m₂ (Classical.choice r₂.neChal)))

/-- The map of the place. -/
noncomputable def Rd.carS : CarryS [r₁, r₂] (SendLocRide.R s).shape :=
  .step (fun m => ((ρ.mask m, ρ.words m), ((), ()))) (fun m c => ρ.rdSeed (ρ.view₁ m c).drawn)
    fun _ _ => .step (fun m₂ => (((), ()), (ρ.answ m₂, ()))) (fun m₂ c₂ => ρ.rdPos (ρ.view₂ m₂
        c₂).drawn)
      fun _ _ => .nil

theorem Rd.carS_tr (τ : Tr [r₁, r₂]) (sd : s.sw.d.Sd.D) (Qs : Fin s.sw.t → s.sw.P)
    (h₁ : ρ.rdSeed (ρ.view₁ τ.1 τ.2.1).drawn = some sd)
    (h₂ : ρ.rdPos (ρ.view₂ τ.2.2.1 τ.2.2.2.1).drawn = some Qs) :
    ρ.carS.tr τ = some (((ρ.mask τ.1, ρ.words τ.1), ((), ())), sd,
      (((), ()), (ρ.answ τ.2.2.1, ())), Qs, ()) := by
  obtain ⟨m, c, m₂, c₂, u⟩ := τ
  show (ρ.rdSeed (ρ.view₁ m c).drawn).bind (fun sd => ((ρ.rdPos (ρ.view₂ m₂ c₂).drawn).bind fun Qs
      =>
    (some ()).map fun τ' => (_, Qs, τ')).map fun τ' => (_, sd, τ')) = _
  rw [h₁, h₂]
  rfl

/-- The written rounds' error counts bear the typed rounds': if at most w₁ written verifier's
messages are read as one joint seed, and at most w₂ as one tuple of positions. -/
theorem Rd.carS_fits (w₁ w₂ e₁ e₂ : ℕ)
    (h₁ : ∀ m c', Prob.cnt (fun c => ρ.rdSeed (ρ.view₁ m c).drawn = some c') ≤ w₁)
    (h₂ : ∀ m₂ c', Prob.cnt (fun c₂ => ρ.rdPos (ρ.view₂ m₂ c₂).drawn = some c') ≤ w₂)
    (k₁ : ldSendFamErr s.sw.d.N s.sw.d.Sd s.sw.d.L * w₁ ≤ e₁)
    (k₂ : (Fintype.card s.sw.P - s.sw.e - 1) ^ s.sw.t * w₂ ≤ e₂) :
    ρ.carS.Fits (SendLocRide.eps s) (e₁, e₂, ()) := by
  have h' : [(SendLocRide.eps s).1, (SendLocRide.eps s).2.1] =
      [ldSendFamErr s.sw.d.N s.sw.d.Sd s.sw.d.L, (Fintype.card s.sw.P - s.sw.e - 1) ^ s.sw.t] :=
    SendLocRide.errs s
  injection h' with a b
  injection b with b _
  have q₁ : (SendLocRide.eps s).1 * w₁ ≤ e₁ := by rw [a]; exact k₁
  have q₂ : (SendLocRide.eps s).2.1 * w₂ ≤ e₂ := by rw [b]; exact k₂
  exact ⟨⟨w₁, h₁, q₁⟩, fun _ _ => ⟨⟨w₂, h₂, q₂⟩, fun _ _ => trivial⟩⟩

/-- The typed statement behind the block. -/
def Rd.after (a : (SendLoc.stage s.sw).X × (SendLoc.stage s.sw).Ex.Str) (sd : s.sw.d.Sd.D)
    (Qs : Fin s.sw.t → s.sw.P) (ans : s.sw.d.N.Answ) (m : r₁.Msg) :
    (SendLoc.loc s.sw).tgt.X × ((SendLoc.loc s.sw).tgt.Ex.prod s.Cw.nat).Str :=
  ((((a.1.1.1, (Qs, fun i => s.sw.C.T a.2.1.1 (Qs i))), a.1.1.2),
      s.sw.S₀.join s.sw.d.N (T := OMsg.Smp) a.1.2 fun o => (s.sw.d.Sd.sd o sd, ans o)),
    ((a.2.1.2, s.sw.S₀.join s.sw.d.N (T := OMsg.Str) a.2.2 (ρ.words m)), ρ.mask m))

/-- **The law of the place "SEND seed, LOC".** -/
theorem loc_place {old : SingleRows} {T : SwitchTarget} {gp : Nat} {others : Array OracleNotice}
    {out : Switched} {c c' : Ctx} {D : LocTaken} (R : LocRan old T gp others out c c' D)
    (hd : c.ch.dry = false) (hv : ρ.ViewOK) (sd : s.sw.d.Sd.D) (Qs : Fin s.sw.t → s.sw.P)
    (hS : ρ.rdSeed D.dS = some sd) (hP : ρ.rdPos D.dL = some Qs)
    (ok : Tr [r₁, r₂] → Prop) (L : List (SendLocRide.Size K))
    (a : (SendLoc.stage s.sw).X × (SendLoc.stage s.sw).Ex.Str) :
    ∃ rowss : List (Array Row),
      Admitted D.c0.st D.seeds ((todoOf D.c0.st D.ids).zip D.shapes) rowss D.c1 D.cA ∧
      ∀ τ : Tr [r₁, r₂],
        PlaceAt (fun τ : Tr [r₁, r₂] => [ρ.view₁ τ.1 τ.2.1, ρ.view₂ τ.2.2.1 τ.2.2.2.1]) ok
          ((kSendLocRideInto L).block s) ρ.carS τ c.ch.pending a c'.ch.pending
          (ρ.after a sd Qs (ρ.rdAns (rowss.flatMap targets)) τ.1) := by
  obtain ⟨v₁, v₂, rowss, h1, -, h3, h4, h5, h6, -⟩ := R.view_rows hd
  refine ⟨rowss, h4, fun τ rest _ hτ => ?_⟩
  rw [h1] at hτ
  obtain ⟨e1, e'⟩ := List.cons.inj hτ
  obtain ⟨e2, e3⟩ := List.cons.inj e'
  have g₁ : ρ.rdSeed (ρ.view₁ τ.1 τ.2.1).drawn = some sd := by rw [← e1, h3]; exact hS
  have g₂ : ρ.rdPos (ρ.view₂ τ.2.2.1 τ.2.2.2.1).drawn = some Qs := by rw [← e2, h6]; exact hP
  have g₃ : ρ.answ τ.2.2.1 = ρ.rdAns (rowss.flatMap targets) := by
    unfold Rd.answ
    have k : ansOf (ρ.view₂ τ.2.2.1 (Classical.choice r₂.neChal)) = ansOf v₂ := by
      unfold ansOf
      rw [hv τ.2.2.1 _ τ.2.2.2.1, ← e2]
    rw [k]
    obtain ⟨vals, d⟩ := v₂
    have h5' : vals = (rowss.flatMap targets).map fun x => Fmt.ItemValue.answer x.triple := h5
    subst h5'
    rw [ansOf_answers]
  refine ⟨_, ρ.carS_tr τ sd Qs g₁ g₂, ?_, e3⟩
  rw [g₃]
  rfl

end OnBytes.Tie.Pv.Switch

#print axioms OnBytes.Tie.Pv.Switch.Rd.carS_fits
#print axioms OnBytes.Tie.Pv.Switch.loc_place
