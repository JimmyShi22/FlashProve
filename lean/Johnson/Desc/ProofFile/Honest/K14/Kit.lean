-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/Kit.lean: GENERAL LEMMAS ON WHAT A CHAIN's THREAD ASKS OF THE
PROVER's SIDE AT A MEMBER (Honest/Thread/Pays.lean), on the frame's own functions, all forwards. No
kind is named. They stand beside Honest/K13/DebtsKit.lean (chainSteps_one, fresh_none).

  playedBy        a round as played by the first part of the half at a sub-protocol's place
  pastOf          where a run stands behind a round whose move hands on the state's own part as it
                  is; the opened columns as they were
  steps_one, one_plays   a row of one part with one move and no stop, at a sub-protocol that
                  declares one round: its steps; and that play returns where the move's message
                  fits: the round as played and the stand behind it are written out
  reads_none      a round that opens no tree and reads no committed table reads nothing
  find_of_mem     in a list of halves at different places, the half that stands at a place is found

What is not claimed. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.Law.ToyPlay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open VerifiableInference.Desc (Block Place OpenedColumn)

variable {S Cl V W X : Type}

/-- A round as played by the first part of the half at b's place: what it showed in the clear, the
tables that it sent, and the challenge x. -/
def playedBy (b : Block S Cl) (vals : List Fmt.ItemValue) (tables : List (Option Table))
    (x : Fmt.Drawn) : Played :=
  { name := b.name, place := b.place, part := 0, told := true, vals := vals, tables := tables
    drawn := x }

/-- Where a run stands behind a round that showed vals and heard x, the state's own part and the
opened columns as they were. -/
def pastOf (m : Mid W X) (vals : List Fmt.ItemValue) (x : Fmt.Drawn) : Mid W X :=
  { st := m.st.hears x, loc := m.loc ++ [x], seen := m.seen ++ [{ vals := vals, drawn := x }],
    opened := m.opened }

/-- The steps of a row of one part with one move, at a sub-protocol that declares one round. -/
theorem steps_one (b : Block S Cl) (d : Fmt.DeclaredRound) (os : List VerifiableInference.Desc.Oracle)
    (hb : b.rounds.zip b.oracles = [(d, os)]) (p : Part V W X) (mv : Move p.Coins W X)
    (hm : p.moves = [mv]) (v : Option V) (c : RowCoins [p]) :
    ({ place := b.place, parts := [p] } : Placed V W X).steps b v c =
      [{ name := b.name, addr := { place := b.place, part := 0 }, decl := d, oracles := os
         bad := p.bad, hid := fun f o => v.bind fun w => p.hid w f o, nth := 0, last := true
         move := some { say := fun _ => mv.say c.1, hand := mv.hand } }] := by
  simp [Placed.steps, rowSteps, Part.steps, hb, hm]

/-- **A row of one part with one move and no stop plays**, where the move answers a message that
fits the declared round. -/
theorem one_plays (b : Block S Cl) (d : Fmt.DeclaredRound) (os : List VerifiableInference.Desc.Oracle)
    (hb : b.rounds.zip b.oracles = [(d, os)]) (p : Part V W X) (mv : Move p.Coins W X)
    (hm : p.moves = [mv]) (hbad : ∀ f o, p.bad f o = none) (hhid : ∀ w f o, p.hid w f o = none)
    (v : Option V) (c : RowCoins [p]) (m : Mid W X) (x : Fmt.Drawn) (z : Sending)
    (hz : mv.say c.1 m.shown m.st = .ok z) (hf : z.fits d os = true) :
    play (({ place := b.place, parts := [p] } : Placed V W X).steps b v c) [x] [] m =
      .ok ([playedBy b (z.vals.map Said.got) (z.tables.map some) x],
        m.after { say := fun _ => mv.say c.1, hand := mv.hand } (z.vals.map Said.got) x) := by
  rw [steps_one b d os hb p mv hm v c]
  exact play_one (mv := { say := fun _ => mv.say c.1, hand := mv.hand }) hbad
    (fun f o => by cases v <;> simp [hhid]) rfl hz hf

/-- A round that opens no tree and reads no committed table reads nothing. -/
theorem reads_none (chain ft : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) (d : Fmt.DeclaredRound) (x : Fmt.Drawn)
    (ho : d.opens = []) (hs : d.stored = []) : readsOf chain ft stored tree [d] [x] = [] := by
  simp [readsOf, ho, hs]

/-- In a list of halves at different places, the half that stands at a place is found. -/
theorem find_of_mem : ∀ (hs : List (Placed V W X)) (h : Placed V W X),
    (hs.map (·.place)).Nodup → h ∈ hs → (hs.find? fun g => g.place == h.place) = some h
  | [], _, _, hm => by cases hm
  | g :: hs, h, hn, hm => by
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.1 hm with rfl | hm'
    · simp
    · have hne : (g.place == h.place) = false := by
        rw [beq_eq_false_iff_ne]
        intro e
        exact hn.1 (e ▸ List.mem_map_of_mem hm')
      rw [List.find?_cons, hne]
      exact find_of_mem hs h hn.2 hm'

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.steps_one
#print axioms ProofFile.Honest.K14.one_plays
#print axioms ProofFile.Honest.K14.reads_none
#print axioms ProofFile.Honest.K14.find_of_mem
#print axioms ProofFile.Honest.K14.playedBy
#print axioms ProofFile.Honest.K14.pastOf
