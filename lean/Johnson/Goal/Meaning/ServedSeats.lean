--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Meaning/ServedSeats.lean: THE SEATS SIT, AT EVERY FAMILY OF SYMBOLS: SymsSit
(Johnson/Desc/First/Att/K05MsgOnto.lean) at the lookups' own seats seatCalls D k, for every y, from
premises on public data alone. Statements and proofs. NO SOUNDNESS AND NO ACCEPTANCE IS CLAIMED.

Why. A tuple of oracle messages with prescribed symbols (msgOf, symAt_msgOf) is had under SymsSit:
main (a symbol sits in no mask row), seated (a symbol other than 0 has a seat that fits), apart (two
symbol addresses with one seat hold one value). The members of the ways back at the lookups
(Johnson/Goal/Meaning/ServedJoint.lean, ServedJointAtt.lean) stand under it, at the packing of lists
that stand under "there is": a premise that nobody can pay unless it is paid AT EVERY y. Here it is.

The road. Two cells with one seat are one element of one array (SeatsApartAt: the sentence of
seatCalls_apart, Johnson/Desc/First/Look/K3CallerSeatsApart.lean, which has it from the layout's own
test reqLayoutOk). names says which array the tree of entry μ names: (ownerK, nameOf ownerA) of μ's
label. nameOf is one to one. So one array gives one owner; and where two entries of the list never
have one owner (OwnersApart), one entry. arrs gives every symbol a seat that fits.

Main names.
  nameOf_inj   "M" ++ toString a is one to one (VerifierAndGoals.Lines.spelled: a number's decimal spelling
    spells the number).
  SeatsApartAt D k   A DEFINITION: the sentence on seats, as a premise: two cells of link k with one
    seat name one array, and are one element of it.
  OwnersApart X k n   A DEFINITION: two entries below n of sub-proof k's list with one owner (ownerK
    and ownerA of their labels) are one entry. The two definitions are sentences on public data:
    names for premises: they name no goal's form.
  entry_of_array   under names and OwnersApart: two entries whose trees name one array are one.
  symsSit_of_apart   AT LETTERS: SeatsApartAt, names, arrs, OwnersApart give SymsSit at every y.
  names_arrs_of_tie   names and arrs are two of the three conjuncts of the public test linkTieB
    (Johnson/Goal/Meaning/ReadingsOne.lean); they are conjuncts of K4's symTieB
    (Johnson/Road/K4/SymsOfLayout.lean) too. The third conjunct, with its letter idx, is not needed.
  owners_apart   IN SCOPE, AT ALL 25 SUB-PROOFS: OwnersApart X k (matsAt X k).size: by owner_cases
    (Johnson/Goal/Meaning/HidOwner.lean): an entry's label names the entry itself, or the entry is
    the one reader of its list and the label names another sub-proof.
  symsSit_of_layout   THE END: in scope, at the plan's own record tlAt X k: the programs' own test
    on the layout, reqLayoutOk, with names and arrs, gives SymsSit at every y.
  symsSit_of_layout_tie   the same from linkTieB.

WAYS IN WHICH "apart" COULD FAIL, AND WHAT SHUTS EACH. A list of trees shorter than the list of
matrices (gtTree.getD μ 0 then hands tree 0 to two entries): names asks at EVERY entry that its tree
names its own label's array, and OwnersApart parts the labels. One array named twice in the
list (the planner does not refuse it): the same. Two matrices side by side in one symbol array (a
symbol's address drops the matrix's first column): the same. The identifier 0 (linkOf 0 = linkOf 1):
OwnersApart speaks of ownerK itself, not of the identifier, and owner_cases gives ownerK at every
entry in scope. An own message's number against a kept one's: msgIn_inj
(Johnson/Desc/First/Look/K3CallerMsgIn.lean), inside the sentence on seats.

Limits. names AND arrs ARE PREMISES EVERYWHERE HERE. SeatsApartAt is a theorem from reqLayoutOk
(seatCalls_apart; spent in symsSit_of_layout). names and arrs are sentences on public data; where
they are paid is other files' matter. D, rad, num, idx stay letters. In symsSit_of_apart tl is a
letter too, while OwnersApart and names read the labels of THE PLAN's record tlAt X k: true at every
tl, meetable at the plan's alone (symsSit_of_layout). seatCalls are the seats of the lookups on a
link's CALLS (the kept messages, then the link's own of moment 0): the digits' lookup and the
smallness test read by other seats: nothing is said of these. Nothing on mask entries' seats but
"main". SymsSit gives a tuple by choice: no program, no honest prover.
Not claimed: anything on completeness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Meaning.ReadingsOne
import Johnson.Goal.Meaning.HidOwner
import Johnson.Goal.Meaning.HidPlanNM
import Johnson.Goal.Meaning.ScopeScan
import Johnson.Desc.First.Att.K05MsgOnto
import Johnson.Desc.First.Look.K3CallerSeatsApart

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Verify (publicOf)
open OnBytes.Model.Layer (matIx)
open OnBytes.Road.Rows (Addr)
open VerifiableInference.Desc.First.Look (Sent Seat seatCalls sigListCalls szOf symArrB sym_seated)
open VerifiableInference.Desc.First.Att.P (SymsSit symAddr seatCalls_main)

/-! ## 1 Names -/

/-- **An array's name names its number.** -/
theorem nameOf_inj {a b : ℕ} (h : nameOf a = nameOf b) : a = b := by
  have e : toString a = toString b := (String.append_right_inj "M").1 h
  calc a = Config.digitsValue (Config.bytesOf (toString a)) := (VerifierAndGoals.Lines.spelled a).2.2.symm
    _ = Config.digitsValue (Config.bytesOf (toString b)) := by rw [e]
    _ = b := (VerifierAndGoals.Lines.spelled b).2.2

/-! ## 2 The two premises on public data -/

/-- Two cells of link k with one seat name one array, and are one element of it. -/
def SeatsApartAt (D : Sent) (k : ℕ) : Prop :=
  ∀ (t t' r c r' c' : ℕ) (s : Seat), seatCalls D k (.cell t r c) = some s →
    seatCalls D k (.cell t' r' c') = some s →
    (D.arrayOf.getD k #[])[t]? = (D.arrayOf.getD k #[])[t']? ∧ r = r' ∧ c = c'

/-- Two entries below n of sub-proof k's list with one owner are one entry. -/
def OwnersApart (X : Model.Verify.Public) (k n : ℕ) : Prop :=
  ∀ μ < n, ∀ μ' < n, ownerK (labAt X k μ) = ownerK (labAt X k μ') →
    ownerA (labAt X k μ) = ownerA (labAt X k μ') → μ = μ'

/-! ## 3 From arrays to entries, and the end at letters -/

section
variable {X : Model.Verify.Public} {D : Sent} {rad : OracleShape → ℕ} {num : ℕ → ℕ → ℕ}
  {idx : ℕ → ℕ} {k : ℕ} {tl : HTailF2}

/-- **Two entries whose trees name one array are one.** names: the tree of each entry names the
array of the entry's label. -/
theorem entry_of_array
    (names : ∀ μ < (szOf tl).NM, (D.arrayOf.getD k #[])[tl.gtTree.getD μ 0]? =
      some (ownerK (labAt X k μ), nameOf (ownerA (labAt X k μ))))
    (O : OwnersApart X k (szOf tl).NM) {μ μ' : ℕ} (hμ : μ < (szOf tl).NM)
    (hμ' : μ' < (szOf tl).NM)
    (e : (D.arrayOf.getD k #[])[tl.gtTree.getD μ 0]? =
      (D.arrayOf.getD k #[])[tl.gtTree.getD μ' 0]?) : μ = μ' := by
  rw [names μ hμ, names μ' hμ'] at e
  have p := Option.some.inj e
  exact O μ hμ μ' hμ' (congrArg Prod.fst p) (nameOf_inj (congrArg Prod.snd p))

/-- **THE SEATS SIT AT EVERY FAMILY OF SYMBOLS**, from four premises on public data. arrs: the
lookups' own test on each entry's array (the array is there, its message stands in link k's list,
its blocks tile the entry's rows of symbols and columns inside that message's table). -/
theorem symsSit_of_apart (A : SeatsApartAt D k)
    (names : ∀ μ < (szOf tl).NM, (D.arrayOf.getD k #[])[tl.gtTree.getD μ 0]? =
      some (ownerK (labAt X k μ), nameOf (ownerA (labAt X k μ))))
    (arrs : ∀ μ < (szOf tl).NM, symArrB D (sigListCalls D rad k) k (tl.gtTree.getD μ 0)
      (Alg.symRows ((szOf tl).m μ)) ((szOf tl).k μ) = true)
    (O : OwnersApart X k (szOf tl).NM) (y : Cb.Pv.Tail.Syms Cb.Gl.E (szOf tl)) :
    SymsSit D.codes (sigListCalls D rad k) (seatCalls D k) tl y := by
  refine ⟨fun _ _ _ s hs => seatCalls_main k _ _ _ s hs,
    fun μ i' c _ => sym_seated (arrs μ.val μ.isLt) i'.isLt c.isLt, ?_⟩
  intro μ i' c μ' i'' c' s hs hs'
  obtain ⟨ea, er, ec⟩ := A _ _ _ _ _ _ s hs hs'
  obtain rfl : μ = μ' := Fin.ext (entry_of_array names O μ.isLt μ'.isLt ea)
  obtain rfl : i' = i'' := Fin.ext er
  obtain rfl : c = c' := Fin.ext ec
  rfl

/-- The two premises names and arrs are conjuncts of the public test linkTieB. -/
theorem names_arrs_of_tie (T : linkTieB X D rad num idx k tl = true) :
    (∀ μ < (szOf tl).NM, (D.arrayOf.getD k #[])[tl.gtTree.getD μ 0]? =
      some (ownerK (labAt X k μ), nameOf (ownerA (labAt X k μ)))) ∧
    ∀ μ < (szOf tl).NM, symArrB D (sigListCalls D rad k) k (tl.gtTree.getD μ 0)
      (Alg.symRows ((szOf tl).m μ)) ((szOf tl).k μ) = true := by
  have t : ∀ μ < (szOf tl).NM, entryTieB X D rad num idx k tl μ = true := fun μ hμ =>
    List.all_eq_true.1 T μ (List.mem_range.2 hμ)
  refine ⟨fun μ hμ => ?_, fun μ hμ => ?_⟩
  · have t' := t μ hμ
    unfold entryTieB at t'
    rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at t'
    exact t'.1.1
  · have t' := t μ hμ
    unfold entryTieB at t'
    rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at t'
    exact t'.1.2

end

/-! ## 4 In the goals' scope -/

section Core
variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}

/-- **In scope, at each of the 25 sub-proofs: two entries of the list with one owner are one.** -/
theorem owners_apart (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) {k : ℕ}
    (hk : k < 25) : OwnersApart X k (matsAt X k).size := by
  intro a ha a' ha' eK eA
  rcases owner_cases h C hk ha with ⟨o1, o2⟩ | ⟨g, g0, hg, rfl, e, o1, o2⟩ |
      ⟨g, hg, rfl, e, o1, o2⟩ | ⟨rfl, e, o1, o2⟩ <;>
    rcases owner_cases h C hk ha' with ⟨p1, p2⟩ | ⟨g', g0', hg', ek, e', p1, p2⟩ |
      ⟨g', hg', ek, e', p1, p2⟩ | ⟨ek, e', p1, p2⟩
  · omega
  · omega
  · omega
  · omega
  · omega
  · rw [e, e']
  · omega
  · omega
  · omega
  · omega
  · obtain rfl : g = g' := by omega
    rw [e, e']
  · omega
  · omega
  · omega
  · omega
  · rw [e, e']

end Core

section Scope
variable {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray} {X : Model.Verify.Public}
  {D : Sent} {rad : OracleShape → ℕ} {num : ℕ → ℕ → ℕ} {idx : ℕ → ℕ} {k : ℕ}

/-- **THE END: IN SCOPE, AT THE PLAN's OWN RECORD OF SUB-PROOF k, THE SEATS SIT AT EVERY FAMILY OF
SYMBOLS**: from the programs' own test on the layout and the two premises names and arrs. -/
theorem symsSit_of_layout (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (hk : k < 25)
    (ok : reqLayoutOk D.codes D.shape D.layout = true)
    (names : ∀ μ < (szOf (tlAt X k)).NM, (D.arrayOf.getD k #[])[(tlAt X k).gtTree.getD μ 0]? =
      some (ownerK (labAt X k μ), nameOf (ownerA (labAt X k μ))))
    (arrs : ∀ μ < (szOf (tlAt X k)).NM, symArrB D (sigListCalls D rad k) k
      ((tlAt X k).gtTree.getD μ 0) (Alg.symRows ((szOf (tlAt X k)).m μ))
      ((szOf (tlAt X k)).k μ) = true)
    (y : Cb.Pv.Tail.Syms Cb.Gl.E (szOf (tlAt X k))) :
    SymsSit D.codes (sigListCalls D rad k) (seatCalls D k) (tlAt X k) y := by
  have C := Hd.core_of_scope hZ hR h
  refine symsSit_of_apart
    (fun _ _ _ _ _ _ _ a b => VerifiableInference.Desc.First.Look.seatCalls_apart ok a b)
    names arrs ?_ y
  have e : (szOf (tlAt X k)).NM = (matsAt X k).size := nm_of_core h C hk
  rw [e]
  exact owners_apart h C hk

/-- The same from the public test linkTieB. -/
theorem symsSit_of_layout_tie (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (hk : k < 25)
    (ok : reqLayoutOk D.codes D.shape D.layout = true)
    (T : linkTieB X D rad num idx k (tlAt X k) = true)
    (y : Cb.Pv.Tail.Syms Cb.Gl.E (szOf (tlAt X k))) :
    SymsSit D.codes (sigListCalls D rad k) (seatCalls D k) (tlAt X k) y :=
  symsSit_of_layout hZ hR h hk ok (names_arrs_of_tie T).1 (names_arrs_of_tie T).2 y

end Scope

end Meaning

#print axioms Meaning.nameOf_inj
#print axioms Meaning.SeatsApartAt
#print axioms Meaning.OwnersApart
#print axioms Meaning.entry_of_array
#print axioms Meaning.symsSit_of_apart
#print axioms Meaning.names_arrs_of_tie
#print axioms Meaning.owners_apart
#print axioms Meaning.symsSit_of_layout
#print axioms Meaning.symsSit_of_layout_tie
