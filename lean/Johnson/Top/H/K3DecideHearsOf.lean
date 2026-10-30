-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3DecideHearsOf.lean: the kind "lookup" (K3): the law `K3DecideHears`
(Johnson/Top/H/K3LawKind.lean) of the field decide of `K3.block` (Johnson/Desc/First/Look/K3Lookup.lean:
decide asks that nothing is heard yet), FROM TWO NAMED PREMISES that are proved elsewhere. Without
that test in decide the law is false at the seat on a link's calls: a second hearing keeps the
first (Johnson/Desc/First/Look/K3SeatLaw.lean, calls_twice).

What is proved here is the wrapper alone: decide's yes is the yes of `hear`; that is the yes of
`messages` on the tape that `tapeT` makes of the view's rounds and the plan's entries, with
nothing left; and that tape, read, is the view's rounds, read.

The two premises, each a definition of type Prop in this file:

  `LkPadHears`: the library's flat copy of the lookup's hearing (`lkPad`,
    OnBytes/K/Kc/FlatHear.lean), where it returns on a tape and uses it up, leaves a record and a
    ledger that meet the record of end values at the tape's own rounds. NOT PROVED HERE:
    Johnson/Top/H/K3DecideHearsAt.lean.
  `MessagesCut`: where `K3.messages` returns, `lkPad` returns the same. NOT PROVED HERE:
    Johnson/Top/H/K3DecideHearsAt.lean.

Further premises of the theorem: two laws on the seat: `SeatReads`
(Johnson/Desc/First/Look/K3SeatLaw.lean: proved there of both seats that run) and `SeatKeeps`
(Johnson/Top/H/K3SeatFits.lean: where a ledger is open and nothing is heard yet, the ledger that
`put` lays is read back; proved there of both seats that run). The kind's test on the plan is not
a premise.

Uses of the library's plain functions and records: Fork, Forest.Shape, Forest.Heard, Forest.shape,
Forest.pubAsk; sentOf, drawnOf, eOf (OnBytes/Tie/Pv/Psc/PscView.lean); rdRV; ShapeOf, PadLeft,
HeardIs; endsOf, planF; lkPad and the type Fl.

Limits. The wrapper alone: under its two premises. It is a tie: it has no error term. Nothing is
said where decide refuses. No routine in a context is named in a statement or reached by a proof
of this file (held by the walk in Johnson/Top/H/K3Walk.lean [not in this library] from k3DecideHears
and yesToAll_not).
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3LawKind
import Johnson.Desc.First.Look.K3Lookup
import Johnson.Desc.First.Look.K3SeatLaw
import Johnson.Top.H.K3SeatFits
import Johnson.Desc.First.Tape.TapeHolds
import Johnson.Desc.First.Look.LookKindAgrees

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun OnBytes.PscTie _root_.Fo
open Cb Cb.Fo
open OnBytes.K.Kc (FlatRound Tape lkPad)
open VerifiableInference.Desc (named need)
open VerifiableInference.Desc.First.Tape (tapeT roundT flRun readT TapeRule roundT_holds
  flRun_holds)

/-! ## The tape, read -/

/-- A round of a tape, read into a ring. -/
def rdFl {K : Type} [CommRing K] (ρ : OnBytes.Model.Reading K) (x : FlatRound) : List K × List K :=
  (x.sent.map ρ.val, x.drawn.map ρ.val)

/-- Where all items are elements, the elements among the items are all of them. -/
theorem sent_of_elemsOf : ∀ (l : List Fmt.ItemValue) (s : List OnBytes.E),
    Desc.First.Tape.elemsOf l = some s → l.filterMap eOf = s
  | [], s, h => by
    simp only [Desc.First.Tape.elemsOf, Option.some.injEq] at h
    simp [← h]
  | g :: l, s, h => by
    cases g with
    | e x =>
      cases hl : Desc.First.Tape.elemsOf l with
      | none => simp [Desc.First.Tape.elemsOf, hl] at h
      | some s' =>
        have ih := sent_of_elemsOf l s' hl
        simp [Desc.First.Tape.elemsOf, hl] at h
        subst h
        have he : eOf (Fmt.ItemValue.e x) = some (E.ofTriple x) := rfl
        rw [List.filterMap_cons_some he, ih]
    | f _ => simp [Desc.First.Tape.elemsOf] at h
    | word _ => simp [Desc.First.Tape.elemsOf] at h
    | root _ => simp [Desc.First.Tape.elemsOf] at h
    | answer _ => simp [Desc.First.Tape.elemsOf] at h

/-- A round of the tape holds what the view's round sends and draws. -/
theorem roundT_reads (rule : TapeRule) (r : Fmt.RoundView) (e : Fmt.Entry) (x : FlatRound)
    (h : roundT rule r e = some x) : x.sent = sentOf r ∧ x.drawn = drawnOf r := by
  obtain ⟨sent, hs, rfl, -⟩ := roundT_holds rule r e x h
  exact ⟨(sent_of_elemsOf _ _ hs).symm, rfl⟩

/-- The tape's rounds are the view's, one for one. -/
theorem tapeT_reads (rule : TapeRule) : ∀ (rs : List Fmt.RoundView) (es : List Fmt.Entry) (t : Tape),
    tapeT rule rs es = some t → t.map (fun x => (x.sent, x.drawn)) =
      rs.map fun r => (sentOf r, drawnOf r)
  | [], [], t, h => by
    simp only [tapeT, Option.some.injEq] at h
    simp [← h]
  | [], _ :: _, _, h => by simp [tapeT] at h
  | _ :: _, [], _, h => by simp [tapeT] at h
  | r :: rs, e :: es, t, h => by
    simp only [tapeT] at h
    cases hx : roundT rule r e with
    | none => simp [hx] at h
    | some x =>
      cases ht : tapeT rule rs es with
      | none => simp [hx, ht] at h
      | some t' =>
        simp only [hx, ht, Option.some.injEq] at h
        subst h
        obtain ⟨h1, h2⟩ := roundT_reads rule r e x hx
        simp only [List.map_cons, tapeT_reads rule rs es t' ht, h1, h2]

theorem tapeT_rd {K : Type} [CommRing K] (ρ : OnBytes.Model.Reading K) (rule : TapeRule)
    (rs : List Fmt.RoundView) (es : List Fmt.Entry) (t : Tape) (h : tapeT rule rs es = some t) :
    t.map (rdFl ρ) = rs.map (rdRV ρ) := by
  calc t.map (rdFl ρ)
      = (t.map fun x => (x.sent, x.drawn)).map
          fun q : List OnBytes.E × List OnBytes.E => (q.1.map ρ.val, q.2.map ρ.val) := by
        rw [List.map_map]; rfl
    _ = (rs.map fun r => (sentOf r, drawnOf r)).map
          fun q : List OnBytes.E × List OnBytes.E => (q.1.map ρ.val, q.2.map ρ.val) := by
        rw [tapeT_reads rule rs es t h]
    _ = rs.map (rdRV ρ) := by
        rw [List.map_map]; rfl

theorem tapeT_sizes (rule : TapeRule) (rs : List Fmt.RoundView) (es : List Fmt.Entry) (t : Tape)
    (h : tapeT rule rs es = some t) :
    t.map (fun x => (x.sent.length, x.drawn.length)) =
      rs.map fun r => ((sentOf r).length, (drawnOf r).length) := by
  calc t.map (fun x => (x.sent.length, x.drawn.length))
      = (t.map fun x => (x.sent, x.drawn)).map
          fun q : List OnBytes.E × List OnBytes.E => (q.1.length, q.2.length) := by
        rw [List.map_map]; rfl
    _ = (rs.map fun r => (sentOf r, drawnOf r)).map
          fun q : List OnBytes.E × List OnBytes.E => (q.1.length, q.2.length) := by
        rw [tapeT_reads rule rs es t h]
    _ = rs.map fun r => ((sentOf r).length, (drawnOf r).length) := by
        rw [List.map_map]; rfl

/-! ## The two premises -/

/-- **The law of the library's flat copy, on a tape that it uses up.** NOT PROVED HERE. -/
def LkPadHears : Prop :=
  ∀ (K : Type) [CommRing K] (ρ : OnBytes.Model.Reading K) (calls : Array Call) (pub : Array Nat)
    (lid lm : ℕ) (F F' : Fork) (t : Tape) (g : Heard),
    lkPad calls pub lid F t = some (g, F', []) →
    t.map (fun x => (x.sent.length, x.drawn.length)) = planF g.shape ∧
      (Sized F →
        ShapeOf calls pub lid g.shape ∧ PadLeft g.shape F F' g ∧
          HeardIs ρ g F' (endsOf g.shape lm F.next (t.map (rdFl ρ))))

/-- **Where the kind's own hearing returns, the library's flat copy returns the same.** NOT PROVED
HERE. -/
def MessagesCut : Prop :=
  ∀ (calls : Array Call) (pub : Array Nat) (lid : ℕ) (h : Shape) (F : Fork) (t : Tape)
    (x : Heard × Fork × Tape),
    ShapeOf calls pub lid h → 1 < h.NC →
    Desc.K3.messages h F t = some x → lkPad calls pub lid F t = some x

/-! ## Unfoldings -/

theorem named_bind_ok {α β : Type} (n : String) (o : Option α) (f : α → Except String β) (b : β) :
    (named n o >>= f) = .ok b ↔ ∃ a, o = some a ∧ f a = .ok b := by
  cases o with
  | none => simp [named, bind, Except.bind]
  | some a => simp [named, bind, Except.bind]

theorem need_bind_ok {β : Type} (n : String) (c : Bool) (f : Unit → Except String β) (b : β) :
    (need n c >>= f) = .ok b ↔ c = true ∧ f () = .ok b := by
  cases c with
  | false => simp [need, bind, Except.bind]
  | true => simp [need, bind, Except.bind]

theorem ok_of_toBool (x : Except String Unit) (h : x.toBool = true) : x = .ok () := by
  cases x with
  | error e => simp [Except.toBool] at h
  | ok u => rfl

/-- The shape that a place's parameters fix is made by the two public tests. -/
theorem shape_some (p : Desc.First.Look.P) (h : Shape) (hs : p.shape = some h) :
    ShapeOf p.calls p.pub p.lid h := by
  rw [Desc.First.Look.P.shape_older] at hs
  cases h0 : Forest.shape p.calls p.lid with
  | error e => simp [h0] at hs
  | ok h0' =>
    simp only [h0] at hs
    split at hs
    · rename_i hb
      exact ⟨h0', h0, ok_of_toBool _ hb, (Option.some.inj hs).symm⟩
    · exact absurd hs (by simp)

/-- decide's yes, unfolded. -/
theorem decide_ok {S Cl : Type} (seat : Desc.K3.Seat S Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl))
    (s s' : S) (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (h : (Desc.K3.block seat piece laid before p guests).decide s rs cols = .ok s') :
    ∃ F x, seat.fork s = some F ∧ seat.heard s = none ∧
      Desc.K3.hear p (p.entries.getD []) F rs = some x ∧ s' = seat.put s x.1 x.2 := by
  simp only [Desc.K3.block] at h
  rw [named_bind_ok] at h
  obtain ⟨F, hF, h⟩ := h
  rw [need_bind_ok] at h
  obtain ⟨hn, h⟩ := h
  rw [need_bind_ok] at h
  obtain ⟨-, h⟩ := h
  rw [need_bind_ok] at h
  obtain ⟨-, h⟩ := h
  rw [named_bind_ok] at h
  obtain ⟨x, hx, h⟩ := h
  exact ⟨F, x, hF, Option.isNone_iff_eq_none.mp hn, hx, (Except.ok.inj h).symm⟩

/-! ## The law -/

/-- **(L2a) of `K3.block`'s decide, from the two premises.** -/
theorem k3DecideHears_of {S Cl : Type} (seat : Desc.K3.Seat S Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl))
    (hfork : SeatKeeps seat) (hheard : Desc.K3.SeatReads seat)
    (hPad : LkPadHears) (hCut : MessagesCut) :
    K3DecideHears seat.fork seat.heard p.calls p.pub p.lid
      (Desc.K3.block seat piece laid before p guests).decide := by
  intro K _ ρ lm s s' rs cols _ hdec
  obtain ⟨F, x, hF, hn, hx, rfl⟩ := decide_ok seat piece laid before p guests s s' rs cols hdec
  have hsome : (seat.fork s).isSome = true := by rw [hF]; rfl
  unfold Desc.K3.hear at hx
  cases hsh : p.shape with
  | none => simp [hsh] at hx
  | some h =>
    simp only [hsh] at hx
    split at hx
    · rename_i hNC
      obtain ⟨t, ht, hm⟩ := (flRun_holds _ _ _ _ _ _ _ _).1
        (show flRun {} (Desc.K3.messages h) (p.entries.getD []) F rs = some (x.1, x.2) from hx)
      have hl := hCut p.calls p.pub p.lid h F t _ (shape_some p h hsh) hNC hm
      obtain ⟨hsz, hrest⟩ := hPad K ρ p.calls p.pub p.lid lm F x.2 t x.1 hl
      refine ⟨F, x.2, x.1, hF, hfork _ _ _ hsome hn, hheard _ _ _ hsome hn, ?_, ?_⟩
      · rw [← tapeT_sizes _ _ _ _ ht]
        exact hsz
      · intro hS
        rw [← tapeT_rd ρ _ _ _ _ ht]
        exact hrest hS
    · exact absurd hx (by simp)

/-! ## The member that says yes to all fails the law -/

/-- A decide that returns its record on everything does not meet (L2a): behind no round and behind
one round it would have to leave one and the same plan of rounds. -/
theorem yesToAll_not {S : Type} [Inhabited S] (fork : S → Option Fork) (heard : S → Option Heard)
    (calls : Array Call) (pub : Array Nat) (lid : ℕ) :
    ¬ K3DecideHears fork heard calls pub lid (fun s _ _ => .ok s) := by
  intro h
  obtain ⟨_, _, g, _, _, hg, h0, _⟩ :=
    h Cb.Gl.E OnBytes.Model.Reading.gl 0 default default [] [] (by simp [okRoundsE]) rfl
  obtain ⟨_, _, g', _, _, hg', h1, _⟩ :=
    h Cb.Gl.E OnBytes.Model.Reading.gl 0 default default [⟨[], ⟨[], [], [], none⟩⟩] []
      (by simp [okRoundsE]) rfl
  have e : g = g' := Option.some.inj (hg.symm.trans hg')
  subst e
  have := h0.trans h1.symm
  simp at this

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3DecideHears_of
#print axioms VerifiableInference.OnPublicFiles.yesToAll_not
