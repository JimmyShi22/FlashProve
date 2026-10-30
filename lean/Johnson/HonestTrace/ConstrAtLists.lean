-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/ConstrAtLists.lean

The library's sentence "constrQAt" (Johnson/P5J/MeansQ.lean) at the 24 sub-proofs of the layers and
of attention, from lists of integers that meet MeetsAll (Johnson/HonestTrace/Full.lean).

The sentence. constrQAt hd put H headPart digitsPart k p a y w is what the library's filling of its
table of items (meaningQAt) says under the item "constr k p": k is a sub-proof's number, p one of
six parts, H a way of reading a witness w. At a part p other than lookDigits it says: if p is small,
H.base k w; and, for every table M that H.dec a y yields and every index i' that M holds: headPart p
i' a y w if k = hd; else partG at the list (H.hid w).MG (k / 2) if k is even; else partA at the list
(H.hid w).MA (k / 2).

Main definitions and theorems:
* "partG_of_meetsAll", "partA_of_meetsAll": under MeetsAll X i x T and g < 12, for every part p:
  partG X i x (fun g => T (2 * g)) g p, and partA (Hd.shapeA X g) (T (2 * g + 1)) p.
* "smallH_of_meetsAll": under MeetsAll X i x T: Hd.SmallH at the list T 24.
* "mgOf_trace", "maOf_trace": under MeetsAll X i x T and g < 12: mgOf X.y T g = T (2 * g) and maOf X
  T g = T (2 * g + 1), as whole lists, at all numbers, rows and columns.
* "ConstrTies put H a y w i x T": five conditions that join a way of reading a witness to an index
  i, a request x and lists T.
* "constr_layers": under ConstrTies put H a y w i x T and MeetsAll X i x T, for k < 24 and p among
  the four parts of parts4 (idn, lookCalls, rider, small): constrQAt 24 put H headPart digitsPart k
  p a y w, for all headPart and digitsPart.

Limits. These are conditional lemmas. MeetsAll and ConstrTies are premises: this file shows them of
no X, T or H. constr_layers DOES NOT SHOW H.base: the field "base" of ConstrTies is, in its words,
the first half of the sentence at the part small, and is handed through. headPart and digitsPart are
arbitrary in constr_layers because at k < 24 and a part of parts4 the sentence reads neither:
nothing is said of them. Nothing is said here of sub-proof 24 but smallH_of_meetsAll, and nothing of
the sentence at the parts lookDigits and lookCallsHeard (partG and partA are True there by their
text). All is at 12 groups. WHAT THIS FILE USES OF THE FOLDER Johnson/Goal/. It imports no file of
that folder; Johnson/P5J/MeansQ.lean, which it imports, does. By name: the definitions Meaning.mgOf
and Meaning.maOf (Johnson/Goal/Meaning/HidOwn.lean). By projection: the fields tok, MG and MA of
Meaning.Hid (Johnson/Goal/Meaning/Row.lean), the type of the values of HidAt.hid. Other types of the
library bear the short name Hid (among them those of Johnson/Desc/Kinds/HeadParts.lean,
Inst/Model/Head/PolicyDefs.lean and Johnson/Desc/Reads/HeadStated.lean); they are not meant. By
unfolding and not by name: through P5J.partA the statements of partA_of_meetsAll and constr_layers
unfold to AttSmall, AttKey, AttOwn1, AttOwn2 and AttRidden (Johnson/Goal/Meaning/Row.lean). Nothing
else of the folder is named, and no theorem or lemma of the folder is called.

Not claimed: anything on a prover, on what a verifier accepts, or on a property of the protocol.

-/
import Johnson.P5J.MeansQ
import Johnson.HonestTrace.Full

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Inst.Model Inst.Model.All
open OnBytes.Road OnBytes.Road.L5 OnBytes.Road.Rows.Norms
open OnBytes.Model.Verify (publicOf layerShape borderOf)
open OnBytes.Model.Layer (Lay matIx)
open VerifiableInference.OnPublicFiles.Flat (Holds GE)
open VerifiableInference.Desc (Strs Wit)
open Meaning (mgOf maOf)
open P5J (TPart TReq TS HidAt partG partA parts4 constrQAt)

variable {X : Model.Verify.Public} {i : Cm.Idx} {x : Instance ppref} {T : Tr}

/-! ## At lists -/

/-- Under MeetsAll X i x T, for g < 12 and every part p: the part p of a group's share holds at the
list T (2 * g). By the five sentences that layer_fields draws from LayerOrd
(Johnson/Road/Rows/LayerTop.lean); at lookDigits and lookCallsHeard partG is True by its text. -/
theorem partG_of_meetsAll (M : MeetsAll X i x T) {g : ℕ} (hg : g < 12) (p : TPart) :
    partG X i x (fun g => T (2 * g)) g p := by
  obtain ⟨a, b, c, d, e⟩ := layer_fields (M.ords.layer g hg)
  cases p
  all_goals first
    | exact a
    | exact ⟨b, d⟩
    | exact c
    | exact e
    | exact trivial

/-- Under MeetsAll X i x T, for g < 12 and every part p: the part p of an attention sub-proof's
share holds at the list T (2 * g + 1). By the clauses of AttOrd. -/
theorem partA_of_meetsAll (M : MeetsAll X i x T) {g : ℕ} (hg : g < 12) (p : TPart) :
    partA (Hd.shapeA X g) (T (2 * g + 1)) p := by
  have O := M.ords.att g hg
  cases p
  all_goals first
    | exact O.rel.1
    | exact O.rel.2.1
    | exact ⟨fun k b g' n hv => O.rel.2.2 (.at1 k b g' n) hv,
        fun b g' n hv => O.rel.2.2 (.at2 b g' n) hv⟩
    | exact fun b g' n hv => O.rel.2.2 (.at3 b g' n) hv
    | exact trivial

/-- Under MeetsAll X i x T: the head's bound Hd.SmallH holds at the list T 24. It is the first
clause of Hd.HeadOrdLB. -/
theorem smallH_of_meetsAll (M : MeetsAll X i x T) :
    Hd.SmallH X.hS X.HLy (borderOf X.y) (T 24) :=
  M.ords.head.1

/-! ## The lists that hidOf makes -/

/-- Under MeetsAll X i x T, for g < 12: the list that mgOf makes for group g out of T is T (2 * g),
at all numbers, rows and columns. mgOf reads the stream that comes into a later group in the list of
the group before; by MeetsAll the two have the same entries at all rows and columns. -/
theorem mgOf_trace (M : MeetsAll X i x T) {g : ℕ} (hg : g < 12) : mgOf X.y T g = T (2 * g) := by
  funext a r c
  unfold mgOf
  by_cases h : a = (matIx X.y).iXI ∧ 0 < g
  · rw [if_pos h, h.1]
    exact (M.ords.seamFF g h.2 hg r c).symm
  · rw [if_neg h]

/-- Under MeetsAll X i x T, for g < 12: the list that maOf makes for the attention sub-proof of
group g out of T is T (2 * g + 1), at all numbers, rows and columns. maOf reads qa in the group's
list; by MeetsAll the two have the same entries at all rows and columns. -/
theorem maOf_trace (M : MeetsAll X i x T) {g : ℕ} (hg : g < 12) : maOf X T g = T (2 * g + 1) := by
  funext a r c
  unfold maOf
  by_cases h : a = (Hd.shapeA X g).cf.NAs + 3
  · rw [if_pos h, h]
    exact (M.ords.seamA g hg r c).symm
  · rw [if_neg h]

/-! ## The sentence -/

/-- **Five conditions** that join a way of reading a witness (H, put), at a pair a, strings y and a
witness w, to an index i, a request x and lists T. -/
structure ConstrTies {P W : Type} {rows cols : ℕ} (put : TReq → Fin ppref.V → TReq)
    (H : HidAt X P W rows cols) (a : P × TS) (y : Strs) (w : W) (i : Cm.Idx) (x : Instance ppref)
    (T : Tr) : Prop where
  /-- whatever index the decoded table holds is i -/
  one : ∀ M i', H.dec a y = some M → Holds M i' → i' = i
  /-- the request's public part, with the witness's token put in, is x -/
  req : (put (H.req a) (H.hid w).tok).val = x
  /-- the list that H reads for group g is T (2 g) -/
  mg : ∀ g < 12, (H.hid w).MG g = T (2 * g)
  /-- the list that H reads for the attention sub-proof of group g is T (2 g + 1) -/
  ma : ∀ g < 12, (H.hid w).MA g = T (2 * g + 1)
  /-- H.base at each of the 25 sub-proofs -/
  base : ∀ k < 25, H.base k w

/-- **The sentence at the 24 sub-proofs of the layers and of attention, at the four parts of
parts4.** Under ConstrTies put H a y w i x T and MeetsAll X i x T, for k < 24 and p in parts4:
constrQAt 24 put H headPart digitsPart k p a y w, for all headPart and digitsPart, which the
sentence does not read there. The first half of the part small, H.base k w, is the field "base" of
ConstrTies handed through: it is not shown here. The index falls by the field "one". -/
theorem constr_layers {P W : Type} {rows cols : ℕ} {put : TReq → Fin ppref.V → TReq}
    {H : HidAt X P W rows cols} {a : P × TS} {y : Strs} {w : W}
    (Ti : ConstrTies put H a y w i x T) (M : MeetsAll X i x T)
    (headPart : TPart → Cm.Idx → P × TS → Strs → W → Prop)
    (digitsPart : ℕ → P × TS → Strs → W → Prop) {k : ℕ} (hk : k < 24) {p : TPart}
    (hp : p ∈ parts4) : constrQAt 24 put H headPart digitsPart k p a y w := by
  have hpd : p ≠ .lookDigits := by
    rintro rfl
    exact absurd hp (by decide)
  unfold constrQAt
  rw [if_neg hpd]
  refine ⟨fun _ => Ti.base k (by omega), fun M' i' hM hi' => ?_⟩
  obtain rfl : i' = i := Ti.one M' i' hM hi'
  rw [if_neg (by omega : ¬ k = 24), Ti.req]
  have hg : k / 2 < 12 := by omega
  by_cases h2 : k % 2 = 0
  · rw [if_pos h2]
    have A := partG_of_meetsAll M hg p
    have e2 := Ti.mg _ hg
    cases p <;> simp only [partG] at A ⊢ <;> first
      | exact trivial
      | (rw [e2]; exact A)
  · rw [if_neg h2, Ti.ma _ hg]
    exact partA_of_meetsAll M hg p

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.partG_of_meetsAll
#print axioms OnBytes.HonestTrace.partA_of_meetsAll
#print axioms OnBytes.HonestTrace.smallH_of_meetsAll
#print axioms OnBytes.HonestTrace.mgOf_trace
#print axioms OnBytes.HonestTrace.maOf_trace
#print axioms OnBytes.HonestTrace.constr_layers
