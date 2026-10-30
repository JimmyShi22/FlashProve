-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SendSeam.lean: THE SEAM OF LETTERS AT A SENDING: from the law of the kind K1 in
its own letters (`send_gives_smpAt`, Johnson/Desc/K1/Law/GoodSendForms.lean) to the row that the
rule of composition asks of a block which sends sampled members (`SendGivesSmp`,
Johnson/Desc/Sound/SendLaw.lean). Statements and proofs, over the library's text alone. NO NEW GAME:
the kind's own game is taken as it stands.

The kind speaks of the place's messages k (by their number among all that the place sends), each at
the library's oracle message of its shape and a radius (`portOmZ`), of a word fOf y k (a letter),
and of its own reading `smpAt` of the record behind, at the number "the record's size less the
place's messages, and k". The rule speaks of members (`Mem`), of the strings' reading of a member's
word (`wordsOf`) and of its own reading smp of the record (a letter).
  `clash_cross`: "no collision" crosses from one oracle message of the library to an equal one, the
    word carried along, at two seeds that the sample maps read alike.
  `SendSeams …`: THE SEAMS, as one record: `entry`: (i) a sampled message's member has that
    message's shape with that radius as its entry; `all`: the new members are such members;
    `keeps`: the promise behind; `smp`: (iii) AT THE PIECE's OUTPUTS INSIDE On, AND NOWHERE ELSE:
    where the kind's reading gives a sample, the rule's reading gives one whose seed the sample map
    reads as it reads that one's: UP TO THE SAMPLE MAP: NO EQUATION OF SEEDS.
  `sendGivesSmp_of_send`: **THE ROW AT A SENDING**, from the kind's premises, the seams, and `word`:
    (ii) the members' words behind the block hang on the strings in front and the first round's
    message alone.
  `smpByNumber`: a reading THAT STAYS: a member's sample read off the statement at a fixed number of
    the record. `smp_of_number`: **(iii) HAS A PAYER**: that reading meets `smp` wherever, at the
    piece's outputs inside On, the member's number is the message's.

Why (iii) is asked at outputs alone. `send_gives_smp` (Johnson/Desc/K1/Law/GoodSendSmp.lean) takes
the reading as a letter and asks its tie AT EVERY RECORD t, at the number "t's size less the place's
messages, and k". A reading at a fixed number meets that only at records of the sender's own size;
and only a reading at fixed numbers stays when later blocks add messages. So that theorem is not
called here.

Limits. (1) EVERY FIELD OF `SendSeams` IS A PREMISE: shown here of no record and no plan. (2) The
block is any block that `IsSend` holds of, over its own record T: what sits in a chain is a seat of
it. (3) The piece is the kind's `sendPiece`: two written rounds; its errors are the kind's, not the
cap: IT IS NO ENTRY OF A DESCRIPTION's LIST OF PIECES: the carriage to one is not begun here. (4)
The kind's word fOf is FILLED here with the rule's, carried along the equation of the two oracle
messages. (5) `smp_of_number`'s premise hnum wants On to pin the record's size in front, and the
block to add just the place's messages: neither is shown here. `smpByNumber` is ONE filling of the
letter smp (a seed by choice among those whose matrix is the record's forms): that it and any other
reading of the seed off the record's sample rows give one sample map and one answer is not shown.
(6) Nothing on an honest prover, on acceptance or on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.SendLaw
import Johnson.Desc.K1.Law.GoodSendForms

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Fo.Peel Cb Johnson.Pack OnBytes.Slice
open _root_.Run (ckP)
open _root_.Iop (Doomed)
open VerifiableInference.Desc.K1 (Par shapesOf shapeAt sampledAt condPort errPort IsSend sendPiece
  seedEntry)

/-- A member's oracle message of the library, by the member's entry. -/
theorem om_of_entry' (cs : OnBytes.Codes) (x : Mem) (sh : OnBytes.OracleShape) (e0 : ℕ)
    (he : x.1.l.get x.2 = (sh, e0)) : (sigOf cs x.1.l).om x.2 = portOmZ cs sh e0 := by
  show portOmZ cs (x.1.l.get x.2).1 (x.1.l.get x.2).2 = portOmZ cs sh e0
  rw [he]

/-- "No collision" crosses between equal oracle messages, the word carried along, at two seeds that
the sample maps read alike. -/
theorem clash_cross {o o₂ : OMsg GE} (ho : o = o₂) (f : o.Str) (ρ : o.Z.D) (ρ₂ : o₂.Z.D)
    (hv : HEq (o.Z.val ρ) (o₂.Z.val ρ₂)) (h : ¬ o₂.Clash (cast (congrArg OMsg.Str ho) f) ρ₂) :
    ¬ o.Clash f ρ := by
  subst ho
  exact fun hc => h ((K1.clash_val _ _ ρ ρ₂ (eq_of_heq hv)).1 hc)

section
variable {Xi : Type} (G : FileDescription Xi) {T Cl W : Type} {Fr : Frame} (P : Par) (rad : ℕ → ℕ)
  (smp : T → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf P.codes s.l).om i).Smp)

/-- **The seams of letters at a sending.** -/
structure SendSeams (stOf : T → OnBytes.Statement) (p : Piece (ckP .two) Fr T Cl W)
    (mem : Fin (shapesOf P).length → Mem) (new : List Mem)
    (On On' : T × Fr.E.Str → Prop) : Prop where
  entry : ∀ k, (mem k).1.l.get (mem k).2 = (shapeAt P k, rad k.val)
  all : ∀ x ∈ new, ∃ k, sampledAt P k ∧ mem k = x
  keeps : ∀ a τ x, On a → p.ior.red.out a τ = some x → On' x
  smp : ∀ a τ x, On a → p.ior.red.out a τ = some x → ∀ k, sampledAt P k → ∀ z,
    K1.smpAt P.codes (shapeAt P k) (rad k.val) (stOf x.1)
      ((stOf x.1).oracles.size - (shapesOf P).length + k.val) = some z →
    ∃ z', smp x.1 (mem k).1 (mem k).2 = some z' ∧
      HEq (((sigOf P.codes (mem k).1.l).om (mem k).2).Z.val z'.1)
        ((portOmZ P.codes (shapeAt P k) (rad k.val)).Z.val z.1)

/-- **THE ROW AT A SENDING.** word: the members' words behind the block hang on the strings in front
and the first round's message alone. -/
theorem sendGivesSmp_of_send (hC : condPort P rad = true) (b : Block T Cl)
    (stOf : T → OnBytes.Statement) (hS : IsSend P stOf b) (base : ℕ) (d₁ d₂ : RDT)
    (he₁ : d₁.entry = seedEntry P) (hk₁ : d₁.kind = .seeds) (e : ℕ) (he : errPort P rad ≤ e)
    (mem : Fin (shapesOf P).length → Mem) (new : List Mem) (On On' : T × Fr.E.Str → Prop)
    (Q : SendSeams P rad smp stOf
      (sendPiece (W := W) (F := Fr) b base d₁ d₂ P.coordinates e) mem new On On')
    (fIn : Fr.E.Str → (OnBytes.Flat.wT d₁).Msg →
      ∀ k, ((sigOf P.codes (mem k).1.l).om (mem k).2).Str)
    (word : ∀ y τ k, wordsOf G P.codes (mem k).1.l (mem k).1.seat (strsOf Fr
      ((sendPiece (W := W) (F := Fr) b base d₁ d₂ P.coordinates e).ior.imp y τ)) (mem k).2 =
        fIn y τ.1 k) :
    SendGivesSmp P.codes G smp (sendPiece (W := W) (F := Fr) b base d₁ d₂ P.coordinates e) new On
      On' := by
  have ho := fun k => om_of_entry' P.codes (mem k) (shapeAt P k) (rad k.val) (Q.entry k)
  have g := K1.send_gives_smpAt (W := W) (F := Fr) P rad hC b stOf hS base d₁ d₂ he₁ hk₁ e he
    (fun y k => cast (congrArg OMsg.Str (ho k))
      (wordsOf G P.codes (mem k).1.l (mem k).1.seat (strsOf Fr y) (mem k).2))
    (fun y m k => cast (congrArg OMsg.Str (ho k)) (fIn y m k))
    (fun y τ => funext fun k => congrArg _ (word y τ k)) On On' Q.keeps
  intro a ha
  refine Doomed.mono _ _ (fun τ hτ x hx => ⟨(hτ x hx).1, fun m hm => ?_⟩) (g a ha)
  obtain ⟨k, hk, rfl⟩ := Q.all m hm
  obtain ⟨z, hz, hn⟩ := (hτ x hx).2 k hk
  obtain ⟨z', h1, h2⟩ := Q.smp a τ x ha hx k hk z hz
  exact ⟨z', h1, clash_cross (ho k) _ z'.1 z.1 h2 hn⟩

end

/-- **A reading that stays**: a member's sample, read off the statement at a FIXED number of the
record (num), by the kind's own reading. -/
def smpByNumber {T : Type} (cs : OnBytes.Codes) (stOf : T → OnBytes.Statement) (num : Mem → ℕ)
    (t : T) (s : Sending) (i : Fin s.l.length) : Option ((sigOf cs s.l).om i).Smp :=
  K1.smpAt cs (s.l.get i).1 (s.l.get i).2 (stOf t) (num ⟨s, i⟩)

/-- **(iii) HAS A PAYER**: the reading at fixed numbers meets `SendSeams.smp` wherever, at the
piece's outputs inside On, the member's number is the message's: the record's size less the place's
messages, and k. -/
theorem smp_of_number {T Cl W : Type} {Fr : Frame} (P : Par) (rad : ℕ → ℕ)
    (stOf : T → OnBytes.Statement) (num : Mem → ℕ) (p : Piece (ckP .two) Fr T Cl W)
    (mem : Fin (shapesOf P).length → Mem) (On : T × Fr.E.Str → Prop)
    (entry : ∀ k, (mem k).1.l.get (mem k).2 = (shapeAt P k, rad k.val))
    (hnum : ∀ a τ x, On a → p.ior.red.out a τ = some x → ∀ k, sampledAt P k →
      num (mem k) = (stOf x.1).oracles.size - (shapesOf P).length + k.val) :
    ∀ a τ x, On a → p.ior.red.out a τ = some x → ∀ k, sampledAt P k → ∀ z,
      K1.smpAt P.codes (shapeAt P k) (rad k.val) (stOf x.1)
        ((stOf x.1).oracles.size - (shapesOf P).length + k.val) = some z →
      ∃ z', smpByNumber P.codes stOf num x.1 (mem k).1 (mem k).2 = some z' ∧
        HEq (((sigOf P.codes (mem k).1.l).om (mem k).2).Z.val z'.1)
          ((portOmZ P.codes (shapeAt P k) (rad k.val)).Z.val z.1) := by
  intro a τ x ha hx k hk z hz
  have key : ∀ (q : OnBytes.OracleShape × ℕ), q = (shapeAt P k, rad k.val) →
      ∃ z' : (portOmZ P.codes q.1 q.2).Smp,
        K1.smpAt P.codes q.1 q.2 (stOf x.1)
          ((stOf x.1).oracles.size - (shapesOf P).length + k.val) = some z' ∧
        HEq ((portOmZ P.codes q.1 q.2).Z.val z'.1)
          ((portOmZ P.codes (shapeAt P k) (rad k.val)).Z.val z.1) := by
    rintro _ rfl
    exact ⟨z, hz, HEq.rfl⟩
  obtain ⟨z', h1, h2⟩ := key _ (entry k)
  refine ⟨z', ?_, h2⟩
  show K1.smpAt P.codes ((mem k).1.l.get (mem k).2).1 ((mem k).1.l.get (mem k).2).2 (stOf x.1)
    (num ⟨(mem k).1, (mem k).2⟩) = some z'
  rw [show (⟨(mem k).1, (mem k).2⟩ : Mem) = mem k from rfl, hnum a τ x ha hx k hk]
  exact h1

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.clash_cross
#print axioms VerifiableInference.Desc.Sound.sendGivesSmp_of_send
#print axioms VerifiableInference.Desc.Sound.smp_of_number
