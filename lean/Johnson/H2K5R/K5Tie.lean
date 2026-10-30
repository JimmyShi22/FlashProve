-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-


Johnson/H2K5R/K5Tie.lean: KIND K5's THREE TIES OF THE LINK's LAW, WHOLE, AT THE SEAT: at a link of the description's first chain whose hearing block
number 2 is of the kind K5, whatever run stands at the entries (2, "first"), (2, "keys"), (2, "second") of its order stands under the kind's law's own runs
runFirst | runKeys | runSecond (Johnson/Desc/First/Att/Claims/K5Still.lean) AT parCOf OF ONE PLAN A: THE PLAN OF THAT LINK's GROUP in the seat's own letters:
AttTake.tFirst | tKeys | tSecond (Johnson/Desc/First/Link/Law/PayAttention.lean) to the letter, at c := parCOf A. Theorems. After the pattern Johnson/LPFK9R/MergeTie.lean.

What is said.
  k5_claims_at: A "FOR ALL" ON THE LOT's BLOCKS: a block of K5's lot (Johnson/Desc/ProofFile/Lot/K5.lean: lotN) at the place ⟨1, some l, 3, K5⟩ states runsN A, A the plan of the group of
    the link number l of the letters' list, which is of the kind 1. By blocks_mem and k5OwnN_mem (Johnson/IMR/LotKinds.lean, K5Seat.lean), called.
  lookup_first | lookup_keys | lookup_second: what runsN A states under the three names: the law's runs (rfl).
  k5_ties: **the three ties, at one plan**: through ties_at_seat (Johnson/LPFK9R/TiesAtSeat.lean), lot_of_kind (Johnson/IMR/LotKinds.lean) and k5_claims_at.
Limits. Three of 21 ties. Under the seat's three yeses. "join" stands at (2, "join") too: it is the lookup's kind's run; no tie is asked of it. Nothing on soundness.

-/
import Johnson.LPFK9R.TiesAtSeat
import Johnson.IMR.K5Seat
import Johnson.Desc.First.Att.Claims.K5Still

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Chain Link Place KindName)
open VerifiableInference.Desc.First (S ModelPart kindsBeforeBatching)
open VerifiableInference.Desc.First.Att (P.runsN P.k5AtN P.k5AtN_states P.parCOf)
open VerifiableInference.Desc.LinkJoin (At Under)
open K5Law (runFirst runKeys runSecond)
open ProofFile (Cl)

/-- **Every block of K5's lot at the place.** -/
theorem k5_claims_at {Z : ProofFile.Pub} {G : ProofFile.Ground} {b' : Block S Cl} (h : b' ∈ (H2K5.lotN Z).blocks G) {l : ℕ}
    (hp : b'.place = { chain := 1, link := some l, piece := 3, kind := .K5 }) :
    ∃ Xl A, G.built[l]? = some Xl ∧ Xl.kind = 1 ∧ G.W.A[Xl.g]? = some A ∧ b'.claims = P.runsN A := by
  rcases IM.blocks_mem h with ⟨x, hx, _⟩ | h
  · exact absurd hx (List.not_mem_nil)
  · obtain ⟨l', Xl, b₀, hX, hk, hb, rfl⟩ := IM.k5OwnN_mem h
    have hp' : b₀.place = { chain := 1, link := some l, piece := 3, kind := .K5 } := hp
    have e := (P.k5AtN_states hb).2.2
    rw [hp'] at e
    have el : l = l' := by
      injection e with _ h2
      exact Option.some.inj h2
    subst el
    unfold P.k5AtN at hb
    obtain ⟨A, hA, rfl⟩ := Option.map_eq_some_iff.1 hb
    exact ⟨Xl, A, hX, hk, hA, rfl⟩

theorem lookup_first (A : Attention.Plan) : (P.runsN A).lookup "first" = some (runFirst (P.parCOf A)) := rfl
theorem lookup_keys (A : Attention.Plan) : (P.runsN A).lookup "keys" = some (runKeys (P.parCOf A)) := rfl
theorem lookup_second (A : Attention.Plan) : (P.runsN A).lookup "second" = some (runSecond (P.parCOf A)) := rfl

variable {o : ProofFile.SecondHashFunctionArgument}

/-- **K5's THREE TIES, WHOLE, AT THE SEAT, AT ONE PLAN.** -/
theorem k5_ties {Z : ProofFile.Pub} {B : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} (hB : ProofFile.baseOf Z (ProofFile.pureSeat o Z) = .ok B)
    (hb : (ProofFile.partsAt (ProofFile.pureSeat o Z) B).base = .ok base)
    (hc : ProofFile.chainBy Z base (ProofFile.partsAt (ProofFile.pureSeat o Z) B).frames
      (ProofFile.partsAt (ProofFile.pureSeat o Z) B).road = .ok c) (l : ℕ) (sub : ModelPart)
    (hl : (ProofFile.subsOf Z)[l]? = some sub)
    (hk : (kindsBeforeBatching sub (l == 0))[2]? = some KindName.K5) :
    ∃ Lk Xl A, c.links[l]? = some Lk ∧ B.G₀.built[l]? = some Xl ∧ Xl.kind = 1 ∧ B.G₀.W.A[Xl.g]? = some A ∧
      (∀ run, At Lk (2, "first") run → Under run (runFirst (P.parCOf A))) ∧
      (∀ run, At Lk (2, "keys") run → Under run (runKeys (P.parCOf A))) ∧
      ∀ run, At Lk (2, "second") run → Under run (runSecond (P.parCOf A)) := by
  obtain ⟨Lk, e1, L, hL, b', hb', ep, t1, _⟩ :=
    LPFK9.ties_at_seat hB hb hc l sub hl 2 .K5 hk (by decide) (by decide) (by decide)
  obtain rfl : L = H2K5.lotN Z := IM.lot_of_kind hL hb' (by rw [ep]; rfl)
  obtain ⟨Xl, A, hX, hk1, hA, ec⟩ := k5_claims_at hb' ep
  refine ⟨Lk, Xl, A, e1, hX, hk1, hA, fun run h => ?_, fun run h => ?_, fun run h => ?_⟩
  · obtain ⟨r', h1, hu⟩ := t1 "first" run h
    rw [ec, lookup_first] at h1
    obtain rfl := Option.some.inj h1
    exact hu
  · obtain ⟨r', h1, hu⟩ := t1 "keys" run h
    rw [ec, lookup_keys] at h1
    obtain rfl := Option.some.inj h1
    exact hu
  · obtain ⟨r', h1, hu⟩ := t1 "second" run h
    rw [ec, lookup_second] at h1
    obtain rfl := Option.some.inj h1
    exact hu

end H2K5

#print axioms H2K5.k5_claims_at
#print axioms H2K5.lookup_first
#print axioms H2K5.k5_ties
