-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/EPubAtK10.lean (kind K10): THE PROMISE's PUBLIC TEST AT A BORDER
(`ePubAt`, Johnson/Desc/First/EPubAt.lean) IS HANDED ON BY K10's STEP, AT THE COMPOSED PUBLIC TESTS
AND THE COMPOSED ROWS, FROM A STATE WHOSE INDEX MASKS' MESSAGE IS A MEMBER OF NO GROUP. It is the
sixth of the six things that a sub-protocol owes to "the half of the table's promise that reads the
verifier's state is handed on" (the field "more"). Definitions, statements and proofs.

  `keepsK`: the two readers of the verifier's state (Johnson/Desc/First/PubFoot.lean) that are spent
    here: what goes on to the later chains; whether the pending claim on the weights can be made.
  `askedK M links ps k`: the list of public items over which `ePubAt` at border k runs: its own
    text.
  `pubFitK M links ps`: a test with code on the table's lists: at every place of the kind K10, every
    item asked behind is asked in front, and is "the index masks' message is there" or reads readers
    of `keepsK` alone. `fitK_at`: what its yes gives at a place.
  `hasRow_of_ledger`: where what goes on, what the open link's sub-proof has left, and the index
    masks' message's ledger are as they were: "the pending claim on the weights can be made" is as
    it was. (After the proof of `eq_hasRow`, Johnson/Desc/First/Link/Law/DoorBlind.lean; there the
    message's whole entry is asked to stay; the ledger is all that `pendingRowO` reads.)
  `leftOf_putRec`: K10's writing leaves what the open link's sub-proof has left.
  `k10_sameOn`: along `K10Step s s'` (AsksOfMg.lean, beside this file), under hout: s and s' agree
    on `keepsK`. `k10_there`: a message is there behind just if it is there in front.
  `e_k10`: THE SENTENCE: `pubFitK`'s yes; pl[k]? = some p of the kind K10; the base's tests answer
    alike at any two states; `K10Step s s'`; hout: the index masks' message is a member of no group
    of s.st: `ePubAt (pubAll D base) moreAll links pl k (z, s) = true` gives the same at k + 1 and
    s'.
Why hout. K10's closing closes the ledger of every member of the link's group; "the pending claim on
the weights can be made" wants the index masks' message's ledger not closed. Without hout the
sentence is not shown, and by reading it fails at a state whose index masks' message is a member.
Limits. hout IS A PREMISE: a fact at reached states: other files' to show. `pubFitK`'s yes is a
premise here. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.EPubRides
import Johnson.Desc.First.Close.Law.AsksOfMg
import Johnson.Desc.First.Close.Law.LedgerBehind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Model
open VerifiableInference.Desc (Place KindName)
open VerifiableInference.Desc.Sound (moreAll)
open VerifiableInference.Desc.LinkJoin (isThere foot0 foot_at)
open VerifiableInference.Desc.First (S ModelPart Pub PubData More Rdr SameOn pubAll ePubAt start pubSets
  openSets pubOfItems pubAll_same pubAll_indexThere)
open VerifiableInference.Desc.K9 (recOf putRec)
open Johnson.Desc.First.Walk.Law (hasRow rowAt rowBy_some leftOf)

/-- The two readers that are spent here. -/
def keepsK : List Rdr := [.out, .row]

/-- The list over which the promise's public test at border k runs. -/
def askedK (M : More) (links : List ModelPart) (ps : List Place) (k : ℕ) : List Pub :=
  (pubSets M links ps)[k]?.getD [] ++ pubOfItems ((openSets links ps (start links))[k]?.getD [])

/-- **The test along the list.** -/
def pubFitK (M : More) (links : List ModelPart) (ps : List Place) : Bool :=
  (List.range ps.length).all fun k => (ps[k]?).all fun p => p.kind != KindName.K10 ||
    (askedK M links ps (k + 1)).all fun q => (askedK M links ps k).contains q &&
      (isThere q || (foot0 q).any fun R => R.all keepsK.contains)

/-- The fact at a place. -/
theorem fitK_at (M : More) (links : List ModelPart) (ps : List Place) (h : pubFitK M links ps = true)
    (k : ℕ) (p : Place) (hp : ps[k]? = some p) (hK : p.kind = KindName.K10) :
    ∀ q ∈ askedK M links ps (k + 1), q ∈ askedK M links ps k ∧
      (isThere q = true ∨ ((foot0 q).any fun R => R.all keepsK.contains) = true) := by
  unfold pubFitK at h
  have h0 := List.all_eq_true.1 h k (List.mem_range.2 (List.getElem?_eq_some_iff.1 hp).1)
  rw [hp] at h0
  simp only [Option.all_some, hK, bne_self_eq_false, Bool.false_or] at h0
  intro q hq
  have h1 := List.all_eq_true.1 h0 q hq
  obtain ⟨a, b⟩ := Bool.and_eq_true_iff.1 h1
  exact ⟨by simpa using a, Bool.or_eq_true_iff.1 b⟩

/-- **"The pending claim on the weights can be made" reads, of the statement, one ledger.** -/
theorem hasRow_of_ledger {s s' : S} (ho : s'.out = s.out) (hl : leftOf s' = leftOf s)
    (hd : (s'.st.oracles[s.out.indexMasks]?).bind (·.ledger) =
      (s.st.oracles[s.out.indexMasks]?).bind (·.ledger))
    (lay : WsLay) (n : ℕ) (lin : Params.LinShape) : hasRow lay n lin s' = hasRow lay n lin s := by
  have key : ∀ (A B : Array OnBytes.Oracle) (i : ℕ) (w : WsForkOut) (r : TensorRow),
      (B[i]?).bind (·.ledger) = (A[i]?).bind (·.ledger) →
      (∃ os, First.Pend.pendingRowO lay i w n lin A = .ok (r, os)) →
      ∃ os, First.Pend.pendingRowO lay i w n lin B = .ok (r, os) := by
    intro A B i w r hAB ⟨os, hos⟩
    obtain ⟨c1, c2, c3, c4, fi, la, c5, c6, c7, c8, c9, Ga, c10, g, c11, l, c12, c, l', c13, c14,
      _⟩ := (First.Pend.pendingRowO_iff lay i w n lin A os r).1 hos
    exact ⟨_, (First.Pend.pendingRowO_iff lay i w n lin B _ r).2 ⟨c1, c2, c3, c4, fi, la, c5, c6,
      c7, c8, c9, Ga, c10, g, c11, l, by rw [hAB]; exact c12, c, l', c13, c14, rfl⟩⟩
  have hrow : rowAt lay n lin s' = rowAt lay n lin s := by
    apply Option.ext
    intro r
    unfold rowAt
    rw [rowBy_some, rowBy_some, hl, ho]
    constructor
    · rintro ⟨w, os, hw, hp⟩
      obtain ⟨os', hp'⟩ := key _ _ _ w r hd.symm ⟨os, hp⟩
      exact ⟨w, os', hw, hp'⟩
    · rintro ⟨w, os, hw, hp⟩
      obtain ⟨os', hp'⟩ := key _ _ _ w r hd ⟨os, hp⟩
      exact ⟨w, os', hw, hp'⟩
  unfold hasRow
  rw [hrow]

/-- K10's writing leaves what the open link's sub-proof has left. -/
theorem leftOf_putRec (s : S) (r : Rec) : leftOf (putRec s r) = leftOf s := by
  obtain ⟨st, book, roots, rowsOwed, failed, check, out, here, req⟩ := s
  cases here <;> first | rfl | (rename_i a; by_cases h : a.opened = true <;> simp [putRec, leftOf,
    S.putLive, S.live, S.link?, S.putLink, h] <;> rfl)

/-- A message is there behind just if it is there in front. -/
theorem k10_there {s s' : S} (hs : K10Step s s') (j : ℕ) :
    (s'.st.oracles[j]?).isSome = (s.st.oracles[j]?).isSome := by
  obtain ⟨es, rs, x, hx, rfl⟩ := hs
  have e := (k10_rides_more s es rs x hx).2.2.2.2.1 j
  have := congrArg Option.isSome e
  simpa using this

/-- **Along K10's step the two readers give one value**, from a state whose index masks' message
is a member of no group. -/
theorem k10_sameOn (D : PubData) {s s' : S} (hs : K10Step s s')
    (hout : ∀ G ∈ s.st.groups, s.out.indexMasks ∉ G.members) : SameOn D keepsK s s' := by
  obtain ⟨es, rs, x, hx, rfl⟩ := hs
  obtain ⟨hl, -, ho⟩ := k10_ledger s es rs x hx _ hout
  intro r hr
  simp only [keepsK, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ho
  · exact fun lay n lin => hasRow_of_ledger ho (leftOf_putRec s _) hl lay n lin

variable {P : Type}

/-- **THE PROMISE's PUBLIC TEST IS HANDED ON BY K10's STEP.** -/
theorem e_k10 (D : PubData) (base : Pub → P × S → Bool) (links : List ModelPart) (pl : List Place)
    (z : P) (hb : ∀ q (s s' : S), base q (z, s') = base q (z, s)) (k : ℕ) (p : Place)
    (hfit : pubFitK moreAll links pl = true) (hp : pl[k]? = some p) (hK : p.kind = KindName.K10)
    (s s' : S) (hs : K10Step s s') (hout : ∀ G ∈ s.st.groups, s.out.indexMasks ∉ G.members)
    (h : ePubAt (pubAll D base) moreAll links pl k (z, s) = true) :
    ePubAt (pubAll D base) moreAll links pl (k + 1) (z, s') = true := by
  have hS := k10_sameOn D hs hout
  unfold ePubAt at h ⊢
  rw [List.all_eq_true] at h ⊢
  intro q hq
  obtain ⟨hin, h3⟩ := fitK_at moreAll links pl hfit k p hp hK q hq
  have hfront := h q hin
  rcases h3 with hth | hfoot
  · cases q with
    | indexThere =>
      rw [pubAll_indexThere] at hfront ⊢
      have ho : s'.out = s.out := hS .out (by simp [keepsK])
      show (s'.st.oracles[s'.out.indexMasks]?).isSome = true
      rw [ho, k10_there hs]
      exact hfront
    | _ => simp [isThere] at hth
  · have e0 := foot_at D keepsK (by decide) q hfoot
    cases hf : foot0 q with
    | none => simp [hf] at hfoot
    | some R =>
      rw [hf] at hfoot e0
      have h4 : R.all keepsK.contains = true := hfoot
      rw [pubAll_same D base q R e0 z s s' (fun r hr => hS r (by
        have := List.all_eq_true.1 h4 r hr
        simpa using this)) (hb q s s')]
      exact hfront

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.hasRow_of_ledger
#print axioms VerifiableInference.Desc.First.Close.leftOf_putRec
#print axioms VerifiableInference.Desc.First.Close.k10_sameOn
#print axioms VerifiableInference.Desc.First.Close.e_k10
