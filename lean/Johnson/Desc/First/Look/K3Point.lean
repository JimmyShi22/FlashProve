-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3Point.lean: the kind "lookup" (Johnson/Desc/First/Look/K3Lookup.lean) AS A HOST:
all calls' key points end in the whole of zx, word for word. Theorems on the text that runs: on
`messages`, `hear` and the field `decide` of `K3.block`.

Why. Another kind's test may borrow coordinates of the lookup's key point (a guest). It compares
machine words. So it needs, of the very record that the lookup's block leaves: how long zx and zy
are, that there is a key point for each call, and that call c's key point is the last iota_c
coordinates of zy followed by all of zx. The lookup's files state that sentence of a kind's
field `decide` as a letter (K3CallsShareThePoint, Johnson/Top/H/K3LawKind.lean). Here it
is proved of K3.block's own `decide`.

Main theorems:
  `run_size`: behind a run of n levels of the grand product from a point of m0 coordinates, the
    point has m0 + n (over `layBack_size`, `level_size`, `turn_size`, `fold_size`).
  `messages_point`: where `messages h` returns: the record's shape is h; the sizes; the key points.
    THE CONTENT IS THE THREE SIZES AND iota_c ≤ rK: the equation on a key point is the text's own
    line, unfolded.
  `hear_some`: where `hear` returns at a place, the place's shape is made by the two public tests
    and has several calls; the strict reading of these very rounds against these entries has given a
    tape; and `messages` has returned at the shape on that tape and has used it up. (The door for
    the law on the hearing.)
  `block_point`: **the sentence, of the block's `decide`**, at every record. Its one premise is on
    the seat: where a ledger is open and nothing is heard yet, what `put` lays, `heard` reads:
    proved of the two seats that run in Johnson/Desc/First/Look/K3SeatLaw.lean.

WHAT OF THE VERIFIER PROGRAM IT USES, so that it can be counted: records and pure functions alone,
through K3Lookup.lean: `Model.Fork`, `Model.Aff`, `Model.Forest.Shape`, `Model.Forest.Heard`,
`Model.Forest.shape`, `Model.Forest.pubAsk`; the carrier `Fl` with its `ret`, `andThen`, `must`
(OnBytes/K/Kc/Flat.lean). No routine in a context (no `Blk`, `Ctx`, `SubM`) stands in a statement
here; that none is reached from a proof is to be held by a walk over constants.

Limits: IT IS A HALF: a sentence on the SHAPE of what the record holds, never on what was heard: it
does NOT say that zx and zy are what was drawn: that is the law on the hearing (row (L2a)), without
which this counts for nothing. A `decide` that says yes to all at a record that holds one
well-shaped value meets the sentence. Nothing on any value of the field. A block that always refuses
meets it emptily. The premise on the seat is not shown here. IT STANDS OVER K3Lookup.lean,
whose `decide` asks that nothing is heard yet at the seat.

It speaks of that text, over the flat
carrier.
No soundness is claimed.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Look.K3Lookup
import Johnson.Desc.First.Look.LookKindAgrees

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3
open OnBytes OnBytes.K.Kc
open OnBytes.Model (Fork Call Aff)
open OnBytes.Model.Forest (Shape Heard)

/-! ## The carrier -/

theorem bind_some {α β : Type} {x : Fl α} {f : α → Fl β} {F : Fork} {t : Tape}
    {r : β × Fork × Tape} (h : (x >>= f) F t = some r) :
    ∃ a G u, x F t = some (a, G, u) ∧ f a G u = some r := by
  change Fl.andThen x f F t = some r at h
  unfold Fl.andThen at h
  split at h
  · exact ⟨_, _, _, ‹_›, h⟩
  · cases h

theorem pure_some {α : Type} {a : α} {F : Fork} {t : Tape} {r : α × Fork × Tape}
    (h : (pure a : Fl α) F t = some r) : r = (a, F, t) := by
  change Fl.ret a F t = some r at h
  unfold Fl.ret at h
  exact (Option.some.inj h).symm

/-! ## The grand product's point -/

theorem layBack_size (m : Nat) (order : List Nat) (cs : List E) :
    (First.Prod.layBack m order cs).size = m := by
  unfold First.Prod.layBack
  have key : ∀ (l : List (Nat × E)) (r : Array E),
      (l.foldl (fun (r : Array E) x => r.set! (m - 1 - x.1) x.2) r).size = r.size := by
    intro l
    induction l with
    | nil => intro r; rfl
    | cons a l ih =>
      intro r
      rw [List.foldl_cons, ih]
      simp
  rw [key]
  simp

theorem level_size {m : Nat} {z : Array E} {order : List Nat} {C : Aff} {F G : Fork} {t u : Tape}
    {o : First.Prod.LevelOut} (h : First.Prod.level m z order C F t = some (o, G, u)) :
    o.r.size = m := by
  unfold First.Prod.level at h
  obtain ⟨w, G₁, u₁, _, h⟩ := bind_some h
  obtain ⟨xi, G₂, u₂, _, h⟩ := bind_some h
  have := pure_some h
  simp only [Prod.mk.injEq] at this
  rw [this.1]
  exact layBack_size _ _ _

theorem turn_size {order : List Nat} {s s' : First.Prod.Carried} {m : Nat} {F G : Fork}
    {t u : Tape} (h : First.Prod.turn order s m F t = some (s', G, u)) :
    s'.point.size = m + 1 := by
  unfold First.Prod.turn at h
  obtain ⟨o, G₁, u₁, ho, h⟩ := bind_some h
  have := pure_some h
  simp only [Prod.mk.injEq] at this
  rw [this.1]
  simp [First.Prod.stepDown, level_size ho]
  omega

theorem fold_size (m0 : Nat) (orders : Nat → List Nat) :
    ∀ (l : List Nat) (s s' : First.Prod.Carried) (F G : Fork) (t u : Tape),
      l.foldlM (fun s i => First.Prod.turn (orders (m0 + i)) s (m0 + i)) s F t = some (s', G, u) →
      s'.point.size = (l.getLast?.map (m0 + · + 1)).getD s.point.size := by
  intro l
  induction l with
  | nil =>
    intro s s' F G t u h
    have := pure_some h
    simp only [Prod.mk.injEq] at this
    simp [this.1]
  | cons a l ih =>
    intro s s' F G t u h
    rw [List.foldlM_cons] at h
    obtain ⟨s₁, G₁, u₁, h₁, h⟩ := bind_some h
    have e := ih s₁ s' G₁ G u₁ u h
    rw [e, turn_size h₁]
    cases l with
    | nil => simp
    | cons b l =>
      rw [List.getLast?_cons_cons]
      cases hx : (b :: l).getLast? with
      | none => simp at hx
      | some x => simp

theorem run_size {m0 n : Nat} {orders : Nat → List Nat} {s s' : First.Prod.Carried} {F G : Fork}
    {t u : Tape} (h : First.Prod.run m0 n orders s F t = some (s', G, u))
    (hs : s.point.size = m0) : s'.point.size = m0 + n := by
  unfold First.Prod.run at h
  rw [fold_size m0 orders _ _ _ _ _ _ _ h]
  cases n with
  | zero => simp [hs]
  | succ n => simp [List.range_succ]; omega

/-! ## The lookup's hearing -/

theorem must_some {b : Bool} {F G : Fork} {t u : Tape} {x : Unit}
    (h : Fl.must b F t = some (x, G, u)) : b = true := by
  unfold Fl.must at h
  cases b with
  | true => rfl
  | false => simp at h

theorem all_getD {a : Array Nat} {k : Nat} (h : (a.all fun i => decide (i ≤ k)) = true)
    (c : Nat) : a.getD c 0 ≤ k := by
  by_cases hc : c < a.size
  · have := (Array.all_eq_true.1 h) c hc
    simpa [Array.getD, hc] using this
  · simp [Array.getD, hc]

/-- **What the hearing returns, as far as the key points go.** -/
theorem messages_point {h : Shape} {F F' : Fork} {t t' : Tape} {g : Heard}
    (H : messages h F t = some (g, F', t')) :
    g.shape = h ∧ g.zx.size = h.dT ∧ g.zy.size = h.rK ∧ g.zk.size = h.NC ∧
      ∀ c, c < h.NC → h.iota.getD c 0 ≤ h.rK ∧
        g.zk.getD c #[] = g.zy.extract (h.rK - h.iota.getD c 0) g.zy.size ++ g.zx := by
  unfold messages at H
  dsimp only at H
  obtain ⟨slot0, G, u, -, H⟩ := bind_some H
  obtain ⟨o₁, G, u, -, H⟩ := bind_some H
  obtain ⟨o₂, G, u, -, H⟩ := bind_some H
  obtain ⟨o₃, G, u, -, H⟩ := bind_some H
  obtain ⟨theta, G, u, -, H⟩ := bind_some H
  obtain ⟨alpha, G, u, -, H⟩ := bind_some H
  obtain ⟨⟨rows, sZ, sG⟩, G, u, -, H⟩ := bind_some H
  dsimp only at H
  obtain ⟨rho, G, u, -, H⟩ := bind_some H
  obtain ⟨keys, G, u, hk, H⟩ := bind_some H
  obtain ⟨table, G, u, -, H⟩ := bind_some H
  obtain ⟨_, G, u, -, H⟩ := bind_some H
  obtain ⟨leaves, G, u, -, H⟩ := bind_some H
  obtain ⟨⟨zb0, leaves'⟩, G, u, -, H⟩ := bind_some H
  dsimp only at H
  obtain ⟨r5, G, u, -, H⟩ := bind_some H
  obtain ⟨bits, G, u, -, H⟩ := bind_some H
  obtain ⟨sl, G, u, -, H⟩ := bind_some H
  obtain ⟨_, G, u, -, H⟩ := bind_some H
  obtain ⟨_, G, u, hi, H⟩ := bind_some H
  obtain ⟨_, G, u, -, H⟩ := bind_some H
  have e := pure_some H
  simp only [Prod.mk.injEq] at e
  obtain ⟨rfl, -, -⟩ := e
  have hs : keys.point.size = 0 + h.v := run_size hk rfl
  have hv : h.v = h.dT + h.rK := rfl
  have hio := all_getD (must_some hi)
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · simp [Array.size_extract]; omega
  · simp [Array.size_extract]; omega
  · simp
  · intro c hc
    refine ⟨hio c, ?_⟩
    simp [Array.getD, hc]

/-! ## The block -/

theorem ebind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem named_ok {α : Type} {n : String} {o : Option α} {a : α} (h : named n o = .ok a) :
    o = some a := by
  cases o with
  | none => cases h
  | some x => cases h; rfl

theorem need_ok {n : String} {b : Bool} {x : Unit} (h : need n b = .ok x) : b = true := by
  cases b with
  | true => rfl
  | false => cases h

/-- Where the hearing at a place returns, the place has a shape, made by the two public tests, with
several calls; THE STRICT READING OF THESE VERY ROUNDS AGAINST THESE ENTRIES HAS GIVEN A TAPE; and
the text `messages` has returned at the shape, on that tape, and has used it up. -/
theorem hear_some {p : First.Look.P} {es : List Fmt.Entry} {F G : Fork} {rs : List Fmt.RoundView}
    {g : Heard} (H : hear p es F rs = some (g, G)) :
    ∃ h0 t, Model.Forest.shape p.calls p.lid = .ok h0 ∧ Model.Forest.pubAsk h0 p.pub = .ok () ∧
      1 < h0.NC ∧ First.Tape.tapeT {} rs es = some t ∧
      messages { h0 with pub := p.pub } F t = some (g, G, []) := by
  unfold hear at H
  cases hp : p.shape with
  | none => rw [hp] at H; cases H
  | some h =>
    rw [hp] at H
    dsimp only at H
    split at H
    · rename_i hNC
      unfold First.Tape.flRun at H
      split at H
      · cases H
      · rename_i t ht
        split at H
        · rename_i a G' hm
          cases H
          obtain ⟨h0, e₁, e₂, rfl⟩ := First.Look.P.shape_made hp
          exact ⟨h0, t, e₁, e₂, hNC, ht, hm⟩
        · cases H
    · cases H

/-- **THE HOST'S OWN SENTENCE, OF THE BLOCK'S decide.** Where it says yes, in what it leaves: the
two public tests have passed; zx has dT coordinates and zy has rK; there is a key point for each
call; and call c's key point is the last iota_c coordinates of zy, then ALL OF zx, as arrays of
machine words. ONE PREMISE, ON THE SEAT: where a ledger is open and nothing is heard yet, what `put`
lays, `heard` reads (`SeatReads`, Johnson/Desc/First/Look/K3SeatLaw.lean, where it is proved of the
two seats that run). That a ledger is open and that nothing is heard yet are `decide`'s own first
two tests. -/
theorem block_point {S Cl : Type} (seat : Seat S Cl)
    (hseat : ∀ s g F, (seat.fork s).isSome = true → seat.heard s = none →
      seat.heard (seat.put s g F) = some g)
    (piece : Nat) (laid : Array Nat)
    (before : List (Nat × Nat)) (p : First.Look.P) (guests : List (First.Look.Guest S Cl))
    {s s' : S} {rs : List Fmt.RoundView} {cols : List (List (Nat × List UInt64))}
    (H : (block seat piece laid before p guests).decide s rs cols = .ok s') :
    ∃ g, seat.heard s' = some g ∧
      (∃ h0, Model.Forest.shape p.calls p.lid = .ok h0 ∧
        Model.Forest.pubAsk h0 p.pub = .ok () ∧ g.shape = { h0 with pub := p.pub }) ∧
      g.zx.size = g.shape.dT ∧ g.zy.size = g.shape.rK ∧ g.zk.size = g.shape.NC ∧
      ∀ c, c < g.shape.NC → g.shape.iota.getD c 0 ≤ g.shape.rK ∧
        g.zk.getD c #[] =
          g.zy.extract (g.shape.rK - g.shape.iota.getD c 0) g.zy.size ++ g.zx := by
  unfold block at H
  dsimp only at H
  obtain ⟨F, hF, H⟩ := ebind_ok H
  obtain ⟨_, hn, H⟩ := ebind_ok H
  obtain ⟨_, -, H⟩ := ebind_ok H
  obtain ⟨_, -, H⟩ := ebind_ok H
  obtain ⟨x, hx, H⟩ := ebind_ok H
  have h0 : seat.heard s = none := Option.isNone_iff_eq_none.1 (need_ok hn)
  have hf : (seat.fork s).isSome = true := by rw [named_ok hF]; rfl
  cases H
  obtain ⟨g, G⟩ := x
  obtain ⟨h0', t, e₁, e₂, -, -, hm⟩ := hear_some (named_ok hx)
  obtain ⟨hs, h₁, h₂, h₃, h₄⟩ := messages_point hm
  refine ⟨g, hseat _ _ _ hf h0, ⟨h0', e₁, e₂, hs⟩, ?_, ?_, ?_, ?_⟩
  · rw [hs]; exact h₁
  · rw [hs]; exact h₂
  · rw [hs]; exact h₃
  · rw [hs]; exact h₄

end VerifiableInference.Desc.K3
