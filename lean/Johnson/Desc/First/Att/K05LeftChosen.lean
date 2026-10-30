-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05LeftChosen.lean: kind K5: FROM THE LOOKUPS' SHARP PROMISE (K3LeftAt,
Johnson/Top/H/K3LeftStatement.lean), which names a carried record alone, TO
WHAT THE KIND's LAW ASKS OF THE LOOKUP (K3LeftOutIs, Johnson/Desc/First/Att/K05LeftSeats.lean),
which names two letters more: the lookup's typed out-statement x0 and what it has heard gOf.

Why. The table of joints says "what the lookup on the calls left" by a Prop on the public record
(Meaning.pubP at the item left m). K05_at_table (Johnson/Desc/First/Att/K05AtTable.lean) spends it
under the premise hleftIs, which can be met only where x0 and gOf hang on the record alone.

Main names:
  `leftAt_mono`: K3LeftAt passes from a condition Q on the ledger in front of the lookup to every
    condition that follows from Q and "the ledger's next free number is first".
  `room_of_leftQ`: a ledger that is sized, has n slots and is free from its next free number on has
    room (Room, Johnson/Desc/First/Att/K05Room.lean) for every k with next + k ≤ n.
  `leftOut_chosen`: **there are functions x0 and gOf OF THE RECORD at which K3LeftAt gives
    K3LeftOutIs.** By choice, out of leftOut_of_leftAtIs (Johnson/Desc/First/Att/K05LeftOut.lean)
    and leftAtIs_of_leftAt (Johnson/Desc/First/Att/K05LeftIs.lean).
  `leftOut_chosen_room`: the same from K3LeftAt at the condition "sized, n slots, free from next on"
    to K3LeftOutIs at the law's own condition Room F n first k, where first + k ≤ n.
Beside it: Johnson/Road/K4/K4PromiseFront.lean holds a leftAt_mono of its own (the two are not
compared here): the one here
falls for it, if that one hands "the next free number is first" to the step from Q to Q' as well.
Limits. x0 and gOf are found by choice: no program is given. Nothing says that the relation behind
the lookup's block holds at the rounds that are chosen (K05LeftOut.lean's own limit). No member is
shown. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05LeftOut
import Johnson.Desc.First.Att.K05LeftIs

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Cb Cb.LdLkp OnBytes OnBytes.Model OnBytes.Model.Road
open VerifiableInference.OnPublicFiles (K3LeftAt)

/-- The sharp promise at a weaker condition on the ledger in front. -/
theorem leftAt_mono {S : Type} {fork : S → Option Fork} {heard : S → Option Forest.Heard}
    {h : Forest.Shape} {lm first : ℕ} {Q Q' : Fork → Prop} {s : S}
    (hQ : ∀ F, Q F → F.next = first → Q' F) (A : K3LeftAt fork heard h lm first Q s) :
    K3LeftAt fork heard h lm first Q' s := by
  obtain ⟨F, F', g, rs, q, hn, L, hh, hf⟩ := A
  exact ⟨F, F', g, rs, hQ F q hn, hn, L, hh, hf⟩

/-- Sized, n slots, free from the next free number on: room for every k that fits. -/
theorem room_of_leftQ {F : Fork} {n nx k : ℕ}
    (q : OnBytes.PscRun.Sized F ∧ F.ns = n ∧ ∀ j, F.next ≤ j → j < F.ns → F.gotF.getD j true = false)
    (hn : F.next = nx) (hk : nx + k ≤ n) : Room F n nx k := by
  obtain ⟨⟨z1, z2, z3⟩, e, fr⟩ := q
  exact ⟨e, hn, ⟨z1, z2, z3⟩, z3, by omega, fun j h1 h2 => fr j (by omega) (by omega)⟩

/-- **The law's two letters x0 and gOf can be chosen off the record alone**: there are functions of
the record at which the lookups' sharp promise gives the promise that the kind's law asks. -/
theorem leftOut_chosen {S St₀ J₀ : Type} [DecidableEq J₀] (fork : S → Option Fork)
    (heard : S → Option Forest.Heard) (h : Forest.Shape) (lm first : ℕ) (ι : Fo.Pl → Option J₀)
    (Q : Fork → Prop) (st : St₀) :
    ∃ (x0 : S → TX (St₀ × Cb.Gl.E) Cb.Gl.E (Option J₀)) (gOf : S → Forest.Heard),
      ∀ s, K3LeftAt fork heard h lm first Q s → K3LeftOutIs fork heard h lm first ι Q (x0 s) (gOf s) s := by
  classical
  have key : ∀ s, ∃ p : TX (St₀ × Cb.Gl.E) Cb.Gl.E (Option J₀) × Forest.Heard,
      K3LeftAt fork heard h lm first Q s → K3LeftOutIs fork heard h lm first ι Q p.1 p.2 s := by
    intro s
    by_cases A : K3LeftAt fork heard h lm first Q s
    · obtain ⟨rs, g, hL⟩ := leftOut_of_leftAtIs ι st (leftAtIs_of_leftAt A)
      exact ⟨(_, g), fun _ => hL⟩
    · exact ⟨(Fo.lookOutE h lm first ι st (Fo.endsOf h lm first []), { shape := {}, leaves := {} }),
        fun B => absurd B A⟩
  choose p hp using key
  exact ⟨fun s => (p s).1, fun s => (p s).2, hp⟩

/-- **The same from the condition "sized, n slots, free from next on" to the law's own Room.** -/
theorem leftOut_chosen_room {S St₀ J₀ : Type} [DecidableEq J₀] (fork : S → Option Fork)
    (heard : S → Option Forest.Heard) (h : Forest.Shape) (lm first n k : ℕ) (ι : Fo.Pl → Option J₀)
    (st : St₀) (hk : first + k ≤ n) :
    ∃ (x0 : S → TX (St₀ × Cb.Gl.E) Cb.Gl.E (Option J₀)) (gOf : S → Forest.Heard),
      ∀ s, K3LeftAt fork heard h lm first (fun F => OnBytes.PscRun.Sized F ∧ F.ns = n ∧
          ∀ j, F.next ≤ j → j < F.ns → F.gotF.getD j true = false) s →
        K3LeftOutIs fork heard h lm first ι (fun F => Room F n first k) (x0 s) (gOf s) s := by
  obtain ⟨x0, gOf, H⟩ := leftOut_chosen fork heard h lm first ι (fun F => Room F n first k) st
  exact ⟨x0, gOf, fun s A => H s (leftAt_mono (fun F q hn => room_of_leftQ q hn hk) A)⟩

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.leftAt_mono
#print axioms VerifiableInference.Desc.First.Att.P.room_of_leftQ
#print axioms VerifiableInference.Desc.First.Att.P.leftOut_chosen
#print axioms VerifiableInference.Desc.First.Att.P.leftOut_chosen_room
