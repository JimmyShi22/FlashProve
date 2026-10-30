-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/IMR/GrowsFlat.lean: THE FIELD "grows" OF ShapeDebts (Johnson/IMR/ShapesJoin.lean), PAID: in
the goals' scope, at the second hash function: at every number of the first chain whose kind does
not send, every
accepting decision lets the statement grow (Grows, Johnson/Desc/Grows.lean). Theorems, proved.

Compiled with the whole library.

  grows_front   at every number below 353 (in front of the last link's end), whatever its kind: by
    open_front (Johnson/IMR/OpenWalk.lean) at seatKeeps_grows k2Grows (Johnson/IMR/GrowsSeat.lean,
      Johnson/IMR/K2ShareAt.lean).
  kinds_back   the kinds at 353, 354 and 356 of the written list of places send: by the kernel.
  grows_calm   THE FIELD: below 353 by grows_front; at 355 by atM3_grows
    (Johnson/Desc/K13/Keeps.lean) under the seat; at 357 the state behind an accepting decision is
    the state in front (chainEnd_decide_iff).

OBJECT: c.blocksInOrder[j]. USER: ShapeDebts.grows. LETTERS: none free but the opening's.

What is not claimed. Anything at the 78 numbers that send behind 352. No soundness.
-/
import Johnson.IMR.ShapesJoin
import Johnson.IMR.OpenWalk
import Johnson.IMR.K2ShareAt

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace IM

open OnBytes (Codes OracleNotice)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName OpenedColumn foldBlocks Grows)
open VerifiableInference.Desc.First (S kindsBeforeBatching closeKinds backKinds)
open Meaning.K2 (frontOf backOf flat_eq open_front seatKeeps_grows k2Grows)
open ProofFile (Cl)

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- In front of the last link's end: every accepting decision lets the statement grow. -/
theorem grows_front (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {j : ℕ} (hj : j < 353)
    {b : Block S Cl} (hb : c.blocksInOrder[j]? = some b) :
    ∀ s rs gs s', b.decide s rs gs = .ok s' → Grows s.st s'.st := by
  obtain ⟨hfr, h352⟩ := links_flat_352 hS hR O
  have hlen : (frontOf c).length = 353 := by
    unfold frontOf
    rw [List.length_cons, h352]
  have hm : b ∈ frontOf c := by
    rw [flat_eq hfr, List.getElem?_append_left (by omega)] at hb
    exact List.mem_of_getElem? hb
  exact (open_front (seatKeeps_grows k2Grows) O trivial fun _ _ _ => trivial).2 b hm

set_option maxRecDepth 1000000 in
theorem kinds_back : (kindW 353).map senderKind = some true ∧
    (kindW 354).map senderKind = some true ∧ (kindW 356).map senderKind = some true := by
  decide +kernel

/-- **THE FIELD "grows" OF ShapeDebts, PAID**: in scope, at every number whose kind does not
send. -/
theorem grows_calm (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    ∀ (j : ℕ) (b : Block S Cl), c.blocksInOrder[j]? = some b → senderKind b.place.kind = false →
      ∀ s rs gs s', b.decide s rs gs = .ok s' → Grows s.st s'.st := by
  intro j b hb hk
  by_cases hj : j < 353
  · exact grows_front hS hR O hj hb
  have hkind : kindW j = some b.place.kind := by
    unfold kindW
    rw [place_at hS hR O hb]
    rfl
  have hlen : c.blocksInOrder.length = 358 := by
    rw [← List.length_map (f := (·.place)), places_scope hS hR O, places_len]
  have hj2 : j < 358 := hlen ▸ (List.getElem?_eq_some_iff.1 hb).1
  have hcases : j = 353 ∨ j = 354 ∨ j = 355 ∨ j = 356 ∨ j = 357 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl
  · have e := kinds_back.1
    rw [hkind] at e
    have e' : senderKind b.place.kind = true := Option.some.inj e
    rw [hk] at e'
    cases e'
  · have e := kinds_back.2.1
    rw [hkind] at e
    have e' : senderKind b.place.kind = true := Option.some.inj e
    rw [hk] at e'
    cases e'
  · obtain ⟨-, -, ⟨b2, b2', e2, -, rfl, hla2⟩, -⟩ := back_of O
    have hix := (back_numbers hS hR O).1 2 b2 e2
    obtain rfl := Option.some.inj (hb.symm.trans hix)
    intro s rs gs s' h
    have h' : (VerifiableInference.Desc.K13.atM3 (Cl := Unit)
        (VerifiableInference.Desc.K13.whereOf Z)).decide s rs gs = .ok s' :=
      (alone_underR hla2).2 s rs gs s' h
    exact VerifiableInference.Desc.K13.atM3_grows _ s rs gs s' h'
  · have e := kinds_back.2.2
    rw [hkind] at e
    have e' : senderKind b.place.kind = true := Option.some.inj e
    rw [hk] at e'
    cases e'
  · obtain ⟨b', -, rfl, hla⟩ := seal_seated O
    obtain rfl := Option.some.inj (hb.symm.trans (back_numbers hS hR O).2)
    intro s rs gs s' h
    have h' : (VerifiableInference.Desc.ChainEnd.chainEnd (Cl := Unit) 1 5 true
        (VerifiableInference.Desc.K13.inFrontOf Z) VerifiableInference.Desc.First.endAsks).decide s
        rs gs = .ok s' := (alone_underR hla).2 s rs gs s' h
    obtain rfl := ((VerifiableInference.Desc.ChainEnd.chainEnd_decide_iff (Cl := Unit) 1 5 true
      (VerifiableInference.Desc.K13.inFrontOf Z) VerifiableInference.Desc.First.endAsks s s' rs
      gs).1 h').1
    exact Grows.refl _

end IM

#print axioms IM.grows_front
#print axioms IM.grows_calm
