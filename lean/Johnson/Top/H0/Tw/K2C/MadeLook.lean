-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/MadeLook.lean: TWO OF THE PUBLIC ITEMS THAT THE CODE SWITCH's PLACE
MAKES: «linkFresh l» AND «lookIn l pc»: their tests at the composed public tests (pubAll) hold
behind an accept of the switch's decision followed by the step that opens the link: the frame's
«opened» at a layers' or an attention link, "H.1.quiet" at the head's. NO BLOCK IMPORTS THIS FILE.

Which lookup. The piece right behind a link's first place (2; at the head's link 3) is the lookup on
the calls: so the sort is «some false», and "nothing is heard at this seat" reads lookHeard?.

  madeLookB d l pc A next ns   ONE Bool ON THE PLAN ALONE: piece pc of link l is the lookup on the
                     calls · A is the plan's table of arrays of link l · the public parameters have
                     that lookup's place, its first slot is next, it has a shape, and the lookup's
                     slots from there on lie below ns
  sizedB_emptySlots · freeB_emptySlots · not_freeB_emptySlots   a ledger of n empty slots has its
                     sizes; k slots from first on are free in it JUST IF first + k ≤ n
  placeAt_is         a place of placeAt bears the asked sort and the asked link's number
  made_of_state      THE HEART, AT A STATE: from the Bool and what the state's readers return
  openLay_parts · openAtt_parts · headOpenQ_parts · headSwitch_parts   what these steps' accepts
                     leave in the readers: by other files' laws on the same texts
  pub_of_made        from the lookups' two Bools to the two items' tests at pubAll
  made_lay · made_att · made_head   **the statement**: at the three sorts of link
  not_made_between   IT CAN FAIL: where no link is open both Bools say no: so a step that accepts
                     all and hands the state on does not meet the statement

Premises that stay. On the plan: madeLookB; the plan's state of the smallness test has nothing
heard. At the head's link ALSO ONE ON THE STATE IN FRONT: hU: the head's own part has nothing heard
at either seat: "H.1.quiet" lays the link's context and the ledger anew and leaves these two as they
came in. Who makes hU: K2C/HeadUnheard.lean.
Searched (by name and by shape, over three sets of this project's Lean files and the code switch's
own files before it was typed; a later set behind): the lookups' k3PlaceThere (Look/K3BoolsAt.lean)
and dataThere (Johnson/Desc/First/AllThere.lean) say "the place is there and has a shape":
a part of madeLookB. A SIBLING AT LINK 0, met in that later set when this file had been typed:
openingZero_linkFresh | openingZero_lookIn (Johnson/Desc/K13/Law/MadeAtOpeningLook.lean):
the same two items behind the first segment's opening, the premises on the plan by name. Here: the
links behind link 0; these premises in one Bool; "the lookup on the calls" and "the place's link is
l" are paid (placeAt_is).
Limits. madeLookB is evaluated at no plan here. Shown at no real state. No soundness statement.

-/
import Johnson.Top.H0.Walk.FrameHere
import Johnson.Top.H0.Tw.K2C.HeadLedger
import Johnson.Top.H0.Tw.K2C.HeadTl
import Johnson.Desc.First.Look.K3CallsAddress
import Johnson.Desc.First.PubAllAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Look (K3Data k3SortAt lookInC linkFreshC placeAt)
open Johnson.Desc.First.Walk (LayPar AttPar openLay openAtt startFork emptySlots weightsAtZero)

/-- **The plan's side of the two makings.** A: the opened link's table of arrays. next, ns: the
fresh ledger's next free slot and its number of slots. -/
def madeLookB (d : K3Data) (l pc : Nat) (A : Array (Nat × String)) (next ns : Nat) : Bool :=
  k3SortAt d.X l pc == some false && A == d.arrayOf.getD l #[] &&
    (placeAt d.X l false).any fun p =>
      p.first == next && p.shape.any fun h => decide (p.first + Forest.elems h ≤ ns)

/-! ## A ledger of empty slots -/

theorem sizedB_emptySlots (F : Fork) (n : Nat) : Desc.K3.sizedB (emptySlots F n) = true := by
  simp [Desc.K3.sizedB, emptySlots]

theorem freeB_emptySlots (F : Fork) {n first k : Nat} (h : first + k ≤ n) :
    Desc.K3.freeB (emptySlots F n) first k = true := by
  unfold Desc.K3.freeB
  rw [Bool.and_eq_true]
  refine ⟨decide_eq_true h, List.all_eq_true.2 fun j hj => ?_⟩
  have hj' : first + j < n := by
    have := List.mem_range.1 hj
    omega
  show (!(Array.replicate n false).getD (first + j) true) = true
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate, if_pos hj']
  rfl

/-- It can fail: where the slots do not lie below n. -/
theorem not_freeB_emptySlots (F : Fork) {n first k : Nat} (h : n < first + k) :
    Desc.K3.freeB (emptySlots F n) first k = false := by
  unfold Desc.K3.freeB
  rw [Bool.and_eq_false_iff]
  exact Or.inl (decide_eq_false (Nat.not_le.2 h))

/-! ## The place -/

theorem placeAt_is {X : Verify.Public} {i : Nat} {dg : Bool} {p : Look.P}
    (h : placeAt X i dg = some p) : p.digits = dg ∧ p.link = i := by
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨rfl, VerifiableInference.OnPublicFiles.lookAt_link hx⟩

/-! ## The heart, at a state -/

theorem made_of_state {d : K3Data} {l pc : Nat} {A : Array (Nat × String)} {next ns : Nat}
    (hB : madeLookB d l pc A next ns = true) {t : S} {tl : HTailF2} {L : LinkCtx} {F₀ : Fork}
    (htl : t.tl? = some tl) (hh : tl.heard = none) (hq : t.lookHeard? = none)
    (hr : t.rowsOwed = none) (hL : t.link? = some L) (hl : L.link = l) (hA : L.arrayOf = A)
    (hF : t.fork? = some (emptySlots F₀ ns)) (hn : F₀.next = next) :
    linkFreshC d l t = true ∧ lookInC d l false t = true := by
  unfold madeLookB at hB
  rw [Bool.and_eq_true, Bool.and_eq_true] at hB
  obtain ⟨⟨_, hAr⟩, hp⟩ := hB
  have hAr : L.arrayOf = d.arrayOf.getD l #[] := hA.trans (eq_of_beq hAr)
  have hArB : (L.arrayOf == d.arrayOf.getD l #[]) = true := by rw [hAr]; exact beq_self_eq_true _
  cases hpl : placeAt d.X l false with
  | none =>
    rw [hpl] at hp
    cases hp
  | some p =>
    rw [hpl] at hp
    have hp : (p.first == next && p.shape.any fun h =>
        decide (p.first + Forest.elems h ≤ ns)) = true := hp
    rw [Bool.and_eq_true] at hp
    obtain ⟨hfst, hsh⟩ := hp
    have hfst : p.first = next := eq_of_beq hfst
    obtain ⟨hdg, hlk⟩ := placeAt_is hpl
    cases hs : p.shape with
    | none =>
      rw [hs] at hsh
      cases hsh
    | some h =>
      rw [hs] at hsh
      have hle : p.first + Forest.elems h ≤ ns := of_decide_eq_true hsh
      constructor
      · unfold linkFreshC
        rw [htl, hL]
        show (tl.heard.isNone && (L.arrayOf == d.arrayOf.getD l #[])) = true
        rw [hh, hArB]
        rfl
      · unfold lookInC
        rw [hpl, hL]
        show (Desc.K3.k3OnIn p t &&
          (L.link == p.link && L.arrayOf == d.arrayOf.getD l #[])) = true
        have hk : Desc.K3.k3OnIn p t = true := by
          unfold Desc.K3.k3OnIn
          rw [hs]
          show ((Desc.K3.heardAt p.digits t).isNone && Tape.RowsOwed.noneWaits t.rowsOwed &&
            t.fork?.any fun G => G.next == p.first && Desc.K3.sizedB G &&
              Desc.K3.freeB G p.first (Forest.elems h)) = true
          rw [hdg, hr, hF]
          show (t.lookHeard?.isNone && true &&
            ((emptySlots F₀ ns).next == p.first && Desc.K3.sizedB (emptySlots F₀ ns) &&
              Desc.K3.freeB (emptySlots F₀ ns) p.first (Forest.elems h))) = true
          rw [hq, sizedB_emptySlots, freeB_emptySlots F₀ hle]
          show (true && true && ((F₀.next == p.first) && true && true)) = true
          rw [hn, hfst, beq_self_eq_true]
          rfl
        rw [hk, hArB, hl, hlk, beq_self_eq_true]
        rfl

/-- **It can fail**: where no link is open both say no. -/
theorem not_made_between (d : K3Data) (l : Nat) (dg : Bool) {t : S} (h : t.here = .between) :
    linkFreshC d l t = false ∧ lookInC d l dg t = false := by
  have hL : t.link? = none := by simp [S.link?, h]
  constructor
  · unfold linkFreshC
    rw [hL]
    simp
  · unfold lookInC
    rw [hL]
    cases placeAt d.X l dg <;> simp

/-! ## What the opening steps leave in the readers -/

theorem openLay_parts {P : LayPar} {m t : S} (h : openLay P m = .ok t) :
    t.tl? = some P.tl₀ ∧ t.lookHeard? = none ∧
      t.link? = some { check := m.check, link := P.l, arrayOf := P.X.arrayOf, list := P.X.Tp } ∧
      t.fork? = some (startFork P.X P.ns) ∧ t.rowsOwed = m.rowsOwed := by
  have e := Johnson.Desc.First.Walk.Tied.openedLay_here h
  have hr : t.rowsOwed = m.rowsOwed := by
    obtain ⟨a, e'⟩ := Johnson.Desc.First.Walk.Tied.openLay_eq h
    rw [e']
  exact ⟨by simp [S.tl?, e], by simp [S.lookHeard?, e], by simp [S.link?, e],
    by simp [S.fork?, e], hr⟩

theorem openAtt_parts {P : AttPar} {m t : S} (h : openAtt P m = .ok t) :
    t.tl? = some { P.tl₀ with funClosed := false, foldDrawn := 0 } ∧ t.lookHeard? = none ∧
      t.link? = some { check := m.check, link := P.l, arrayOf := P.X.arrayOf, list := P.X.Tp } ∧
      t.fork? = some (startFork P.X P.ns) ∧ t.rowsOwed = m.rowsOwed := by
  have e := Johnson.Desc.First.Walk.Tied.openedAtt_here h
  have hr : t.rowsOwed = m.rowsOwed := by
    obtain ⟨a, e'⟩ := Johnson.Desc.First.Walk.Tied.openAtt_eq h
    rw [e']
  exact ⟨by simp [S.tl?, e], by simp [S.lookHeard?, e], by simp [S.link?, e],
    by simp [S.fork?, e], hr⟩

/-- "H.1.quiet": the two seats are those of the head's own part as it came in. -/
theorem headOpenQ_parts {P : HeadPar} {m t : S} (h : headOpenQ P m = .ok t) :
    ∃ a L, m.here = .head a ∧ t.tl? = some a.tl ∧ t.lookHeard? = a.lookHeard ∧
      t.link? = some L ∧ L.link = P.l ∧ L.arrayOf = P.X.arrayOf ∧ t.rowsOwed = m.rowsOwed := by
  obtain ⟨a, st, f, mine, L, out, y, cov, s₁, b, k⟩ := (headOpenQ_iff P m t).1 h
  have h0 : m.openHead.unmarked = .ok s₁ := k.opens
  have h1 := ((S.unmarked_ok _ _).1 h0).1
  have hb := k.opened
  rw [← h1] at hb
  simp [S.openHead, k.here, k.fresh] at hb
  have hr : s₁.rowsOwed = m.rowsOwed := by
    rw [← h1]
    simp [S.openHead, k.here, k.fresh]
  obtain ⟨_, _, hL, _⟩ := Johnson.Desc.First.Walk.Law.front_ok k.front
  refine ⟨a, L, k.here, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [k.out', ← hb]
    simp [S.tl?]
  · rw [k.out', ← hb]
    simp [S.lookHeard?]
  · rw [k.out', ← hb]
    simp [S.link?]
  · rw [hL]
  · rw [hL]
  · rw [k.out']
    exact hr

/-- The switch's decision at the head's link leaves both seats. -/
theorem headSwitch_parts {snd : _root_.Tw.K2.SendFn} {p : P2} {s : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} {m : S} (hp : p.stands = .head)
    (h : decideWith snd p s rs gs = .ok m) :
    ∃ a b, s.here = .head a ∧ m.here = .head b ∧ b.tl = a.tl ∧ b.lookHeard = a.lookHeard := by
  obtain ⟨r₁, r₂, a, G, w, roots, _, k⟩ := head_inv hp h
  exact ⟨a, { a with kept := w.out.kept, ids := w.out.others }, k.hHere, by rw [k.hOut], rfl, rfl⟩

/-! ## At the composed public tests -/

variable {Pp : Type}

theorem pub_of_made (D : PubData) (base : Pub → Pp × S → Bool) (z : Pp) {l pc : Nat}
    {A : Array (Nat × String)} {next ns : Nat} (hB : madeLookB D.d3 l pc A next ns = true) {t : S}
    (h : linkFreshC D.d3 l t = true ∧ lookInC D.d3 l false t = true) :
    pubAll D base (.linkFresh l) (z, t) = true ∧ pubAll D base (.lookIn l pc) (z, t) = true := by
  unfold madeLookB at hB
  rw [Bool.and_eq_true, Bool.and_eq_true] at hB
  have hsort : k3SortAt D.d3.X l pc = some false := eq_of_beq hB.1.1
  constructor
  · rw [pubAll_linkFresh]
    exact h.1
  · rw [pubAll_lookIn D base l pc false hsort]
    exact h.2

/-! ## The statement -/

/-- **At a layers' link.** -/
theorem made_lay (D : PubData) (base : Pub → Pp × S → Bool) (z : Pp) {pc : Nat} {P : LayPar}
    {snd : _root_.Tw.K2.SendFn} {p : P2} {s m t : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (hB : madeLookB D.d3 P.l pc P.X.arrayOf P.X.Fp.next P.ns = true) (hh : P.tl₀.heard = none)
    (h₁ : decideWith snd p s rs gs = .ok m) (h₂ : openLay P m = .ok t) :
    pubAll D base (.linkFresh P.l) (z, t) = true ∧
      pubAll D base (.lookIn P.l pc) (z, t) = true := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := openLay_parts h₂
  exact pub_of_made D base z hB (made_of_state hB e1 hh e2
    (e5.trans (nothingWaits snd p s rs gs m h₁).2) e3 rfl rfl e4 rfl)

/-- **At an attention link.** -/
theorem made_att (D : PubData) (base : Pub → Pp × S → Bool) (z : Pp) {pc : Nat} {P : AttPar}
    {snd : _root_.Tw.K2.SendFn} {p : P2} {s m t : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))}
    (hB : madeLookB D.d3 P.l pc P.X.arrayOf P.X.Fp.next P.ns = true) (hh : P.tl₀.heard = none)
    (h₁ : decideWith snd p s rs gs = .ok m) (h₂ : openAtt P m = .ok t) :
    pubAll D base (.linkFresh P.l) (z, t) = true ∧
      pubAll D base (.lookIn P.l pc) (z, t) = true := by
  obtain ⟨e1, e2, e3, e4, e5⟩ := openAtt_parts h₂
  exact pub_of_made D base z hB (made_of_state hB e1 hh e2
    (e5.trans (nothingWaits snd p s rs gs m h₁).2) e3 rfl rfl e4 rfl)

/-- **At the head's link.** hU: on the state in front of the switch. -/
theorem made_head (D : PubData) (base : Pub → Pp × S → Bool) (z : Pp) {pc : Nat} {P : HeadPar}
    {snd : _root_.Tw.K2.SendFn} {p : P2} {s m t : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hp : p.stands = .head)
    (hB : madeLookB D.d3 P.l pc P.X.arrayOf 0 P.hp.ns = true)
    (hU : ∀ a, s.here = .head a → a.tl.heard = none ∧ a.lookHeard = none)
    (h₁ : decideWith snd p s rs gs = .ok m) (h₂ : headOpenQ P m = .ok t) :
    pubAll D base (.linkFresh P.l) (z, t) = true ∧
      pubAll D base (.lookIn P.l pc) (z, t) = true := by
  obtain ⟨a, b, ha, hb, t1, t2⟩ := headSwitch_parts hp h₁
  obtain ⟨c, L, hc, e1, e2, e3, e4, e5, e6⟩ := headOpenQ_parts h₂
  rw [hb] at hc
  injection hc with hc
  subst hc
  obtain ⟨u1, u2⟩ := hU a ha
  exact pub_of_made D base z hB (made_of_state hB e1 (t1 ▸ u1) (e2.trans (t2.trans u2))
    (e6.trans (nothingWaits snd p s rs gs m h₁).2) e3 e4 e5 (headOpenQ_fork h₂) rfl)

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.sizedB_emptySlots
#print axioms VerifiableInference.Desc.First.K2.freeB_emptySlots
#print axioms VerifiableInference.Desc.First.K2.not_freeB_emptySlots
#print axioms VerifiableInference.Desc.First.K2.placeAt_is
#print axioms VerifiableInference.Desc.First.K2.made_of_state
#print axioms VerifiableInference.Desc.First.K2.not_made_between
#print axioms VerifiableInference.Desc.First.K2.openLay_parts
#print axioms VerifiableInference.Desc.First.K2.openAtt_parts
#print axioms VerifiableInference.Desc.First.K2.headOpenQ_parts
#print axioms VerifiableInference.Desc.First.K2.headSwitch_parts
#print axioms VerifiableInference.Desc.First.K2.pub_of_made
#print axioms VerifiableInference.Desc.First.K2.made_lay
#print axioms VerifiableInference.Desc.First.K2.made_att
#print axioms VerifiableInference.Desc.First.K2.made_head
