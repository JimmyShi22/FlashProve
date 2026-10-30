-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/SealedNoColl.lean: WHAT A SEALED SENDING GIVES AT A NEW TENANT: "NO COLLISION".
From the sending kind's own word for a new message (`Sealed`, Johnson/Desc/K1/Law/GoodSend3.lean:
the statement holds its one sample row at a seed at which the library's `Clash` does not hold of its
word) to the table's letter "no collision" as another file fills it (`noCollJT`,
Johnson/Desc/Sound/MeaningSig.lean). KIND-FREE: no block, no piece, no plan. Statements as
definitions of a Prop, and their proofs.
Main names:
  `SmpTie cs smp a x St o`: **THE ONE TIE THAT THE PROOF WANTS BETWEEN smp AND THE RECORD's SAMPLE
    ROWS**, at the member x, the record a, the statement St and the message's number o: at every
    seed ρ and answer v at which the statement's sample rows of message o are the kind's one row
    (`K1.SeedIs`): smp gives the record a sample of that member, and ITS SEED HAS THE SAME VALUES AS
    ρ (the library's `Sample.val`: through which alone `Clash` reads a seed). It does not ask that
    the two seeds be one, and nothing of the answers.
  `OwedSealedNoColl`, `sealed_noColl`: at a seat (j, t): where each member of ms that sits there is
    shown, sealed AT ITS OWN SHAPE, RADIUS AND WORD at some statement and number, and tied:
    `noCollJT cs G smp ms j t a y`.
  `OwedSealedAt`, `sealed_at`: the same with the shape, the radius and the word AS LETTERS, as a
    sending's law hands them (`shapeAt P j`, `rad j`, `fOf x.2 j`): the member's entry of its list
    is that shape with that radius, and the word is the member's word (an equation between two
    types that are one only then: `HEq`).
  `tie_smpOf`: at smp := `smpOf cs forms ans` (Johnson/Desc/Sound/Seed.lean) the tie comes down to:
    where `K1.SeedIs` holds at ρ, the letter forms gives the library's rows at ρ
    (`Sound.SeedIs`), and the letter ans gives some answers.
What is not claimed. The tie at any smp of a top statement: smp stays a letter. "Shown" at the new
tenant: ShownNew.lean. "Held": other files' to show. That the word which a sending's
law speaks of (`fOf`) is the member's word off the strings: a premise of `sealed_at`. Nothing on
soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K1.Law.GoodSend3
import Johnson.Desc.Sound.MeaningSig

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Slice OnBytes.Maker Johnson.Pack
open VerifiableInference.Desc.Sound (Sending Mem SitsAt noCollJT CfAt ShownAt wordsOf clash_congr
  smpOf smpOf_of seedIs_val)

section
variable (cs : Codes) {A : Type}
  (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)

/-- **The tie between smp and the record's sample rows**, at one member. -/
def SmpTie (a : A) (x : Mem) (St : Statement) (o : ℕ) : Prop :=
  ∀ ρ v, SeedIs cs (x.1.l.get x.2).1 St o ρ v →
    ∃ z, smp a x.1 x.2 = some z ∧
      ((sigOf cs x.1.l).om x.2).Z.val z.1 = ((sigOf cs x.1.l).om x.2).Z.val ρ

end

/-- **OWED.** Sealed, shown and tied at every member at the seat: no collision there. -/
def OwedSealedNoColl : Prop :=
  ∀ {A Xi : Type} (cs : Codes) (G : FileDescription Xi)
    (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (j t : ℕ) (a : A) (y : Strs),
    (∀ x ∈ ms, SitsAt x j t → ShownAt G cs x.1.l x.1.seat y x.2 ∧
      ∃ St o, Sealed cs (x.1.l.get x.2).1 (x.1.l.get x.2).2 (wordsOf G cs x.1.l x.1.seat y x.2) St
        o ∧ SmpTie cs smp a x St o) →
    noCollJT cs G smp ms j t a y

theorem sealed_noColl : OwedSealedNoColl := by
  intro A Xi cs G smp ms j t a y h x hx hs
  obtain ⟨hsh, St, o, ⟨ρ, v, hS, hn⟩, hT⟩ := h x hx hs
  obtain ⟨z, hz, hv⟩ := hT ρ v hS
  exact ⟨z, hz, hsh, fun hc => hn ((clash_congr _ _ z.1 ρ hv).1 hc)⟩

/-- **OWED.** The same with the shape, the radius and the word as letters. -/
def OwedSealedAt : Prop :=
  ∀ {A Xi : Type} (cs : Codes) (G : FileDescription Xi)
    (smp : A → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (ms : List Mem) (j t : ℕ) (a : A) (y : Strs),
    (∀ x ∈ ms, SitsAt x j t → ShownAt G cs x.1.l x.1.seat y x.2 ∧
      ∃ (s : OracleShape) (e : ℕ) (f : (portOmZ cs s e).Str) (St : Statement) (o : ℕ),
        (x.1.l.get x.2).1 = s ∧ (x.1.l.get x.2).2 = e ∧
          HEq f (wordsOf G cs x.1.l x.1.seat y x.2) ∧ Sealed cs s e f St o ∧
          SmpTie cs smp a x St o) →
    noCollJT cs G smp ms j t a y

theorem sealed_at : OwedSealedAt := by
  intro A Xi cs G smp ms j t a y h
  refine sealed_noColl cs G smp ms j t a y fun x hx hs => ?_
  obtain ⟨hsh, s, e, f, St, o, rfl, rfl, hf, hS, hT⟩ := h x hx hs
  obtain rfl := eq_of_heq hf
  exact ⟨hsh, St, o, hS, hT⟩

/-- **At the reading that is made of the two letters forms and ans** the tie comes down to these
two. -/
theorem tie_smpOf (cs : Codes) {A : Type}
    (forms : A → (s : Sending) → (i : Fin s.l.length) →
      Option (((sigOf cs s.l).om i).Z.S → ((sigOf cs s.l).om i).C.J → GE))
    (ans : A → (s : Sending) → (i : Fin s.l.length) → Option (((sigOf cs s.l).om i).Z.S → GE))
    (a : A) (x : Mem) (St : Statement) (o : ℕ)
    (h : ∀ ρ v, SeedIs cs (x.1.l.get x.2).1 St o ρ v →
      Sound.SeedIs cs forms a x.1 x.2 ρ ∧ (ans a x.1 x.2).isSome = true) :
    SmpTie cs (smpOf cs forms ans) a x St o := by
  intro ρ v hS
  obtain ⟨h1, h2⟩ := h ρ v hS
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.1 h2
  obtain ⟨ρ', e, h'⟩ := smpOf_of cs forms ans a x.1 x.2 ρ u h1 hu
  exact ⟨(ρ', u), e, seedIs_val cs forms a x.1 x.2 ρ' ρ h' h1⟩

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.sealed_noColl
#print axioms VerifiableInference.Desc.K1.sealed_at
#print axioms VerifiableInference.Desc.K1.tie_smpOf
