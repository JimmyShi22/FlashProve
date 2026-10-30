-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/LedgerSend.lean: what is owed at a block of a proof file's shared chain behind
"LIN point" (ClauseAt, Johnson/Desc/Sound/LedgerClause.lean), paid at a block that is a sending: the
second and the fifth block ("send o_u", "send o_omega"), whose rows in the table name nothing in
front. The weight is the promise behind: it follows from what every yes carries (Sure) and from
"each new sampled message is sealed", which the law of a sending (send_goodIn_entry, GoodSend4.lean)
gives at the written count that bears the number of the place's bad seeds.

Main names:
  isSend_lift      a sending that is lifted to a wider record is a sending.
  ins_two, ins_five   the table's rows 2 and 5 name nothing in front.
  clause_of_send   the clause at a block whose row names nothing in front.
  isSend_two, isSend_five   the shared chain's second and fifth block, lifted to the pair of what
                   was handed to the chain and the chain's own record, are sendings: so
                   clause_of_send is called at them with ins_two, ins_five.

What is not claimed. THE TABLE's MEANINGS ARE LETTERS, AND THREE PREMISES SPEAK OF THEM: what every
yes carries (hsure); that this with "sealed" gives the shared promise behind (htie): the
book-keeping on the record, the stored table's promise, the elder messages' clauses, and of each new
message "shown, no two members of its list answer the sample alike"; and that the shared items
that are open in front ride back (frames). NO MEMBER OF THE THREE IS SHOWN. The law's own premises
stand: the one Boolean on the plan and the radii; the first written round has the place's entry of
the seeds; the words are read off the first round's message alone. Nothing on soundness of a
protocol, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.GoodSend4
import Johnson.Desc.BlockKeeps
import Johnson.Desc.Sound.LedgerClause
import Johnson.Desc.K14.Law.SendGood

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat OnBytes.Slice
open Johnson.Pack Cb Cb.Ood
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.Keeps (emap_ok)

/-- **A sending that is lifted to a wider record is a sending.** -/
theorem isSend_lift {T T' Cl : Type} (P : Par) (stOf : T → Statement) (b : Block T Cl)
    (get : T' → T) (set : T' → T → T') (hgs : ∀ t x, get (set t x) = x) (h : IsSend P stOf b) :
    IsSend P (fun t => stOf (get t)) (b.lift get set) := by
  intro s s' r₁ r₂ gs hy
  obtain ⟨x, h1, h2⟩ := emap_ok (x := b.decide (get s) [r₁, r₂] gs) hy
  subst h2
  obtain ⟨L, d, d', owed, ids, hyes, hsame, hsz⟩ := h _ _ _ _ _ h1
  refine ⟨L, d, d', owed, ids, hyes, ?_, ?_⟩
  · show SameMsgs d'.st (stOf (get (set s x)))
    rw [hgs]
    exact hsame
  · show (stOf (get (set s x))).oracles.size = d'.st.oracles.size
    rw [hgs]
    exact hsz

/-- The table's second row names nothing in front. -/
theorem ins_two (split : Bool) (i : ItemS) : ¬ insSh split 2 i := by
  intro h
  cases split <;> simp [insSh, rowAtS, sharedPlaces, rowS] at h

/-- The table's fifth row names nothing in front. -/
theorem ins_five (split : Bool) (i : ItemS) : ¬ insSh split 5 i := by
  intro h
  cases split <;> simp [insSh, rowAtS, sharedPlaces, rowS] at h

variable {P₁ S₂ Cl Wt : Type} {Fr : Frame} (N : NumbersS) (Mg : MeaningS S₂ P₁ Wt)
  (Pm : PromMeaning S₂) (Oc : P₁ → Strs → Prop) (split : Bool)
  (p : Piece (ckP .two) Fr (P₁ × S₂) Cl Wt) (l : List (Piece (ckP .two) Fr (P₁ × S₂) Cl Wt))
  (e₀ : ∀ k, (actQ N p l k).1 → Wt → Wt)

/-- **The clause at a sending whose row names nothing in front.** x: the maker's piece: the block,
the base and the two written rounds; its own extractor and errors are read by nothing here. -/
theorem clause_of_send (k : ℕ) (hIn : ∀ i, ¬ insSh split k i) (P : Par) (rad : Nat → Nat)
    (hC : condPort P rad = true) (b : Block (P₁ × S₂) Cl) (stOf : P₁ × S₂ → Statement)
    (hS : IsSend P stOf b) (base : Nat) (d₁ d₂ : RDT) (he₁ : d₁.entry = seedEntry P)
    (hk₁ : d₁.kind = .seeds) (e : Nat) (he : errPort P rad ≤ e)
    (fOf : Fr.E.Str → ∀ j, (portOmZ P.codes (shapeAt P j) (rad j.val)).Str)
    (fIn : Fr.E.Str → (wT d₁).Msg → ∀ j, (portOmZ P.codes (shapeAt P j) (rad j.val)).Str)
    (hf : ∀ y τ,
      fOf ((sendPiece (W := Wt) (F := Fr) b base d₁ d₂ P.coordinates e).ior.imp y τ) = fIn y τ.1)
    (ext₀ : (P₁ × S₂) × Fr.E.Str → Iop.Tr (uLT (ckP .two) [d₁, d₂]) → Wt → Wt)
    (err₀ : Err (uLT (ckP .two) [d₁, d₂])) (Sure : (P₁ × S₂) × Fr.E.Str → Prop)
    (hsure : ∀ a τ y, onQ₂ N Pm Oc split p l k a →
      (sendPiece (W := Wt) (F := Fr) b base d₁ d₂ P.coordinates e).ior.red.out a τ = some y →
      Sure y)
    (htie : ∀ y, Sure y →
      (∀ j, sampledAt P j → Sealed P.codes (shapeAt P j) (rad j.val) (fOf y.2 j) (stOf y.1)
        ((stOf y.1).oracles.size - (shapesOf P).length + j.val)) →
      promQ N Pm split p l (k + 1) ((actQ N p l (k + 1)).2 y))
    (frames : ∀ a τ y w i, onQ₂ N Pm Oc split p l k a →
      (sendPiece (W := Wt) (F := Fr) b base d₁ d₂ P.coordinates e).ior.red.out a τ = some y →
      promQ N Pm split p l (k + 1) ((actQ N p l (k + 1)).2 y) → openSh split k i →
      ¬ insSh split k i → muQ N Mg p l i (k + 1) ((actQ N p l (k + 1)).2 y) w →
      muQ N Mg p l i k ((actQ N p l k).2 a) (e₀ k ((actQ N p l k).2 a) w)) :
    ClauseAt N Mg Pm Oc split p l e₀ k
      (⟨b, base, [d₁, d₂], [], ext₀, err₀⟩ : Piece (ckP .two) Fr (P₁ × S₂) Cl Wt)
      ((seedMaps d₁ d₂ P.coordinates).err ((e, ()) : Nat × Unit)) := by
  refine clause_of_own N Mg Pm Oc split p l e₀ k _ _ ?_ frames
  have g := send_goodIn_entry (W := Wt) (F := Fr) P rad hC b stOf hS base d₁ d₂ he₁ hk₁ e he fOf
    fIn hf (onQ₂ N Pm Oc split p l k) Sure (fun _ _ => True) (fun _ _ => True) hsure
    (fun _ _ _ _ _ _ _ => trivial)
  intro a ha
  refine Doomed.mono _ _ (fun τ hτ y hy => ?_) (g a ha)
  exact ⟨htie y (hτ y hy).1.1 (hτ y hy).1.2, fun _ _ i hi => absurd hi (hIn i)⟩

/-- **The shared chain's second block, lifted to the pair, is a sending.** -/
theorem isSend_two (A : Type) (Q : Desc.K14.P14) (b1 b2 b3 b4 b5 b6 b7 b8 : Block Desc.K14.St Unit)
    (hbl : Desc.K14.blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8])
    (sentU : Array OracleNotice) (hU : Desc.K14.withU Q.S = some sentU) :
    IsSend (Desc.K14.parK1 Q 2 "o_u and the first mask" sentU)
      (fun t : A × Desc.K14.St => t.2.st) (b2.lift Prod.snd fun t s => (t.1, s)) := by
  obtain ⟨u, hu, h2, _⟩ := Desc.K14.Law.isSend_of_blocks Q b1 b2 b3 b4 b5 b6 b7 b8 hbl
  obtain rfl := Option.some.inj (hu.symm.trans hU)
  exact isSend_lift _ (fun s : Desc.K14.St => s.st) b2 Prod.snd (fun t s => (t.1, s))
    (fun _ _ => rfl) h2

/-- **So is the fifth.** -/
theorem isSend_five (A : Type) (Q : Desc.K14.P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block Desc.K14.St Unit)
    (hbl : Desc.K14.blocks Q = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    IsSend (Desc.K14.parK1 Q 5 "o_omega and o_sp" (Desc.K14.withOmega Q.S))
      (fun t : A × Desc.K14.St => t.2.st) (b5.lift Prod.snd fun t s => (t.1, s)) := by
  obtain ⟨_, _, _, h5⟩ := Desc.K14.Law.isSend_of_blocks Q b1 b2 b3 b4 b5 b6 b7 b8 hbl
  exact isSend_lift _ (fun s : Desc.K14.St => s.st) b5 Prod.snd (fun t s => (t.1, s))
    (fun _ _ => rfl) h5


end VerifiableInference.Desc.K1
