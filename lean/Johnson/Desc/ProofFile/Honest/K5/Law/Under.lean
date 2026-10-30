-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/Under.lean: CONDITIONAL: what lies under a slot, part by part:
in the world in which the items "the forms of a run are worth 0" are said (worldOwn,
Johnson/Desc/Sound/FormsQ.lean), at no late slot: under a slot lies what the ledger shows there less
the slot's factor times the mask row's entry. Statements with their proofs, general in the caller's
job: nothing of one kind of sub-protocol is in them. EVERY STATEMENT IS CONDITIONAL.

  slot_put, slot_worldOf   the world's slot, off what lies in the ledger; it is the slot of the
                 ledger's own world
  lead_under     under the slots of the scalars in front of a masked sumcheck lie the job's lead
                 values
  own_under      under a sumcheck's own slots lie the coins that the part spent for the hiding
                 polynomial
  end_under      under the end values' slots lie the job's end values
  one_under      under the slots of a round that sends scalars by themselves lie the values

The premises. That the part, played alone, says the rounds that the verifier heard. What lies in
the ledger (LeadPut, SumPut, Johnson/Desc/K5/Honest/Law/Puts.lean). AND THAT THE MASK ROW's ENTRY
UNDER EACH SLOT IS THE COIN THAT THE PART SPENT FOR IT: that is shown of no run.

Limits. Nothing is said on who sees what. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.Puts
import Johnson.Desc.Sound.FormsQ
import Johnson.Desc.ProofFile.Honest.SumLaw.LawEnds
import Johnson.Desc.ProofFile.Honest.ForKinds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes (E zeroE oneE subE)
open OnBytes.Model (Reading Aff Fork)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ worldOwn slotW slotW_ledger)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Call Ends ownSlots scalars)
open VerifiableInference.Desc.First.Att.P (Put Open scalars_take scalars_map)
open H2K5.Honest (LeadPut SumPut)
open ProofFile.Honest.SumLaw

/-! ## 1 The world's slot -/

/-- The value under a slot that is filled. CONDITIONAL: y lies there with the factor f. -/
theorem slot_put (a : VerifiableInference.Desc.K9.Part) (D : Bound GQ) {j : Nat} {y f : E}
    (h : Put a.F j y f) :
    (worldOwn a [] D).slot j = Reading.gl.val y - Reading.gl.val f * D.mask j := by
  show slotW a.F [] D.mask j = _
  rw [slotW_ledger a.F [] D.mask j rfl, h.2.1, h.2.2]

/-- It is the slot of the ledger's own world. No premise. -/
theorem slot_worldOf (a : VerifiableInference.Desc.K9.Part) (D : Bound GQ)
    (entry : Nat → Nat → Nat → GQ) (j : Nat) :
    (worldOwn a [] D).slot j = (a.F.worldOf Reading.gl D.mask entry).slot j := by
  show slotW a.F [] D.mask j = _
  rw [slotW_ledger a.F [] D.mask j rfl]
  rfl

/-! ## 2 A masked sumcheck's part -/

section
variable {V W X : Type} {name endName : String} {J : SumJob W X} {c : SumCoins name endName J}
  {t : State W X} {seen : Seen} {dr : List Fmt.Drawn} {rounds : List Fmt.RoundView}

/-- **Under the slots of the scalars in front of the sumcheck lie the job's lead values.** n: the
first of these slots; rs: rounds of which the first is the part's first. CONDITIONAL: ha: played
alone, the part says `rounds`; L: what lies in the ledger; hm: the mask entries are the coins. -/
theorem lead_under (ha : alone (sumPart (V := V) name endName J) c t seen dr = some rounds)
    {rs : List Fmt.RoundView} (hr : rs.head? = rounds.head?) {n : Nat}
    (a : VerifiableInference.Desc.K9.Part) (D : Bound GQ) (L : LeadPut J.shape.lead n rs a.F)
    (hm : ∀ i, i < J.shape.lead → D.mask (n + i) = Reading.gl.val ((firstRun c).getD i zeroE)) :
    ∀ i, i < J.shape.lead → (worldOwn a [] D).slot (n + i) =
      Reading.gl.val ((J.lead t.input (frontOf t seen)).getD i zeroE) := by
  obtain ⟨r, rest, s, e, hs, _, hv⟩ := sumFirst V W X name endName J c t seen dr rounds ha
  obtain ⟨pre, ho, hp⟩ := L
  rw [e] at hr
  cases rs with
  | nil => cases hr
  | cons r' rs' =>
    obtain rfl : r' = r := Option.some.inj hr
    have h1 : some pre = some (s.take J.shape.lead) :=
      ho.1.symm.trans (scalars_take hs J.shape.lead)
    obtain rfl := Option.some.inj h1
    intro i hi
    rw [slot_put a D (hp i hi), hm i hi, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi,
      ← List.getD_eq_getElem?_getD, hv i hi, Reading.gl.one]
    ring

/-- **Under the sumcheck's own slots lie the coins that the part spent for the hiding
polynomial.** CONDITIONAL: under each own slot lies 0 with the factor -1; the mask entries are the
coins. -/
theorem own_under (c : SumCoins name endName J) {k : Call} {n : Nat} {rs : List Fmt.RoundView}
    {hh : MaskedSum.Heard} (a : VerifiableInference.Desc.K9.Part) (D : Bound GQ)
    (S : SumPut k n rs hh a.F)
    (hm : ∀ i, i < ownSlots k.all → D.mask (hh.first + i) = hidingCoin c i) :
    ∀ i, i < ownSlots k.all → (worldOwn a [] D).slot (hh.first + i) = hidingCoin c i := by
  intro i hi
  rw [slot_put a D (S.coefs i hi), hm i hi, Reading.gl.sub, Reading.gl.zero, Reading.gl.one]
  ring

/-- **Under the end values' slots lie the job's end values.** CONDITIONAL: the call has end values;
the verifier's text for the sumcheck has heard the part's rounds from a ledger F whose arrays have
their length; the world's ledger is later than the one that it handed back; the mask entries are the
coins. -/
theorem end_under {e : Ends} (he : J.shape.ends = some e)
    (hd : drawsOk (J.callAt t.input (frontOf t seen)) dr = true)
    (ha : alone (sumPart (V := V) name endName J) c t seen dr = some rounds) {C : Aff} {F G : Fork}
    {hh : MaskedSum.Heard} (hz : OnBytes.PscRun.Sized F)
    (h : MaskedSum.hear C (J.callAt t.input (frontOf t seen)) F rounds = some (hh, G))
    (a : VerifiableInference.Desc.K9.Part) (D : Bound GQ) (hl : OnBytes.PscRun.Later G a.F)
    (hm : ∀ j, j < e.n → D.mask (hh.sEnd + j) = Reading.gl.val ((endRun c).getD j zeroE)) :
    ∀ j, j < e.n → (worldOwn a [] D).slot (hh.sEnd + j) =
      Reading.gl.val ((J.ends t.input (frontOf t seen)
        ((varsOf (J.callAt t.input (frontOf t seen)) dr).take J.shape.vs.length)).getD j
          zeroE) := by
  intro j hj
  rw [slot_worldOf a D fun _ _ _ => 0]
  exact sumEnds V W X name endName J c t seen dr C F G a.F rounds hh e D.mask _ he hz hd ha h hl j
    hj (hm j hj)

end

/-! ## 3 A round that sends scalars by themselves -/

/-- **Under the slots of a round that sends scalars by themselves lie the values.** said: the
scalars that the round holds; vals, coins: lists such that scalar number i reads as value number i
plus coin number i. CONDITIONAL: the first round of rs holds `said`; what lies in the ledger; the
mask entries are the coins. -/
theorem one_under {m n : Nat} {rs : List Fmt.RoundView} {r : Fmt.RoundView} (hr : rs.head? = some r)
    {said vals coins : List E} (hs : scalars r.vals = some said)
    (hv : ∀ i, i < m → Reading.gl.val (said.getD i zeroE) =
      Reading.gl.val (vals.getD i zeroE) + Reading.gl.val (coins.getD i zeroE))
    (a : VerifiableInference.Desc.K9.Part) (D : Bound GQ) (L : LeadPut m n rs a.F)
    (hm : ∀ i, i < m → D.mask (n + i) = Reading.gl.val (coins.getD i zeroE)) :
    ∀ i, i < m → (worldOwn a [] D).slot (n + i) = Reading.gl.val (vals.getD i zeroE) := by
  obtain ⟨pre, ho, hp⟩ := L
  cases rs with
  | nil => cases hr
  | cons r' rs' =>
    obtain rfl : r' = r := Option.some.inj hr
    have h1 : some pre = some (said.take m) := ho.1.symm.trans (scalars_take hs m)
    obtain rfl := Option.some.inj h1
    intro i hi
    rw [slot_put a D (hp i hi), hm i hi, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi,
      ← List.getD_eq_getElem?_getD, hv i hi, Reading.gl.one]
    ring

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.slot_put
#print axioms ProofFile.Honest.K5.slot_worldOf
#print axioms ProofFile.Honest.K5.lead_under
#print axioms ProofFile.Honest.K5.own_under
#print axioms ProofFile.Honest.K5.end_under
#print axioms ProofFile.Honest.K5.one_under
