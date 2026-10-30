-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K10/Honest/BaseOfYes.lean: the closing of a segment (kind K10): from one acceptance of the kind's
decision, and five facts on the record before it, to all twenty facts of `CloseBase`
(Johnson/Desc/K10/Honest/Base.lean). Lemmas on the verifier's own text; they name no honest side's frame and none of
the library's goals. No definition.

The words.
  The record: a value s of `Rec`: what is owed, the frame, the statement. The group: the group G of the statement at
      the number that the frame names. The test on the group: its proximity test; the rows that it takes in are
      `Slice.runRows`.
  An acceptance: `(kind P).decide s rs gs = .ok s'`: the kind's block's decision returns a record.
  `CloseBase P s D`: twenty facts on s that name no challenge of the closing's own rounds. Below each fact is called
      by its field's name in Base.lean.
  `CloseFront P s x D` (Johnson/Desc/K10/Honest/Front.lean): the facts that an acceptance gives, at the element x
      that its first round drew.

What is proved.
  `mask_pow`: where the program's test on the codes' lengths accepts (`Codes.lengthsOk`), the message length of a
      mask code that is there is 2 to the `ceilLog2` of itself. The proof is that of the library's `Meaning.ell_pow`
      (Johnson/Goal/Meaning/LaidInside.lean), which speaks of main codes.
  `code_of_shape`: where a group is in order (`GroupOk`), a fold's shape has the group's members, and the test
      `Own.foldShapeFits` accepts that shape: the group's main code is the shape's. The test finds a member with main
      rows, under the shape's code; `GroupOk` puts that member under the group's code.
  `closeBase_of_yes`: from an acceptance h and the premises hI, hC, hTerms, hMask, hBits: there is D with
      `CloseBase P s D`.
  `closeBase_of_closing`: the same from an acceptance of the block lifted to the first chain's state (`K9.closing`),
      at the record `K9.recOf t`.

Where each of the twenty facts comes from.
  From the acceptance (by `front_of_yes`, Front.lean, and `close_keeps`, Keeps.lean): owed, link, group, due, mask,
      beginRun, there, rows, kh, stretch, shape, maskfits, spendAsMask.
  From hI, at the group of there: inOrder and rowsIn (`InOrder.groups`, `InOrder.runRows`:
      Johnson/Desc/Means/Order.lean).
  From the acceptance and hI: code (`code_of_shape`).
  From the acceptance and hC: power (`mask_pow`; the test on the fold's shape says that the mask code is there).
  From the acceptance, code and hBits: bits.
  Premises outright: termsOk (hTerms) and maskCode (hMask).

Limits. Every premise, by name.
  h: the acceptance.
  hI: the statement is in order (`InOrder`).
  hC: `Codes.lengthsOk` accepts the statement's codes. The half on the mask codes alone is read (`mask_pow`).
  hTerms: every structured vector among the terms on a main table, of every row that the test on the group takes in,
      is in order (`Tensor.ok`). This is the field termsOk, asked of whichever group is there.
  hMask: the group's mask code is the one that the frame's shape names. This is the field maskCode, asked of
      whichever group is there.
  hBits: the row variables of the request's group at the frame's link, plus the `logEll` of the main code that the
      frame's shape names, are at most 63.
None of these is shown of any record here. hTerms and hMask are not derived from the acceptance: `RowIn` does not ask
`Tensor.ok` of a row's terms, and the test on the fold's shape ties the mask code of those members alone that have mask
rows. Further along the road from `CloseBase` to the sentence of the item carry, termsOk and bits are spent again: in
`closeFront_all` (Johnson/Desc/K10/Honest/Base.lean), `closeBase_holds` (Holds.lean) and `rows_named` (LeftClaim.lean),
and in `base_row` (Johnson/Desc/ProofFile/Honest/K10/AskLaw.lean), where termsOk is spent for two things. An acceptance
gives one of the facts that they serve, the yes of the test `Own.foldRowFits` at the element drawn
(`CloseFront.rowfits`, Front.lean). Whether forms of these laws over an acceptance could do without the two fields is
not looked into here. Where the decision rejects, the two main statements hold for nothing. No example that meets the
six premises together is given here. Nothing is shown of a run. No property of the protocol is claimed: nothing is said
on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.K10.Honest.Base
import Johnson.Desc.K10.Honest.Keeps
import Johnson.Desc.Means.Order

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10.YesFree
open OnBytes OnBytes.Means VerifiableInference.Desc VerifiableInference.Desc.First.Close
open VerifiableInference.Desc.First (S)

/-- Where the program's test on the codes' lengths accepts, the message length of a mask code that is there is 2 to the
`ceilLog2` of itself. -/
theorem mask_pow {codes : Codes} (hC : codes.lengthsOk = true) {j : Nat} (hj : j < codes.mask.size) :
    (codes.mask.getD j default).ell = 2 ^ ceilLog2 (codes.mask.getD j default).ell := by
  unfold Codes.lengthsOk at hC
  rw [Bool.and_eq_true] at hC
  have e : codes.mask.getD j default = codes.mask[j] := by
    simp [Array.getD_eq_getD_getElem?, hj]
  have t := Array.all_eq_true_iff_forall_mem.1 hC.2 codes.mask[j] (Array.getElem_mem hj)
  simp only [powerOfTwo, Bool.and_eq_true, beq_iff_eq] at t
  rw [e]
  exact t.2.symm

/-- Where a group is in order and the test on a fold's shape accepts a shape with the group's members, the group's main
code is the shape's. -/
theorem code_of_shape {T : OnBytes.Statement} {G : OnBytes.Group} {F : FoldShape} (hOk : GroupOk T G)
    (hs : Own.foldShapeFits T F = true) (hm : F.layout.members = G.members) : G.code = F.code := by
  obtain ⟨_, _, -, -, -, -, -, -, -, -, -, hall, i, hi, x, hx, hpos, -⟩ := (Own.foldShapeFits_iff T F).1 hs
  obtain ⟨x', hx', hc, -⟩ := hall i hi
  have ex : x' = x := Option.some.inj (hx'.symm.trans hx)
  rw [ex] at hc
  have h1 : x.shape.code = F.code := hc.resolve_left (by omega)
  rw [hm] at hi hx
  have hmem : G.members.getD i noId ∈ G.members.toList := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi]
    exact Array.getElem_mem_toList hi
  have h2 : x.shape.code = G.code := (hOk.mainCode _ hmem x hx).resolve_left (by omega)
  exact h2.symm.trans h1

/-- **From one acceptance of the kind's decision and five facts on the record before it, the twenty facts of
`CloseBase`.** -/
theorem closeBase_of_yes {Cl : Type} {P : Par} {s s' : Rec} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : ((kind (Cl := Cl)) P).decide s rs gs = .ok s')
    (hI : InOrder s.st) (hC : s.st.codes.lengthsOk = true)
    (hTerms : ∀ G, s.st.groups[s.frame.group]? = some G → ∀ r ∈ (Slice.runRows s.st G).toList,
      ∀ t ∈ r.terms.toList, t.part = .main → t.v.ok = true)
    (hMask : ∀ G, s.st.groups[s.frame.group]? = some G → G.maskCode = s.frame.shape.maskCode)
    (hBits : ∀ Gq, s.frame.groups[s.frame.link]? = some Gq →
      Gq.k + (s.st.codes.base.getD s.frame.shape.code default).logEll ≤ 63) :
    ∃ D, CloseBase P s D := by
  obtain ⟨_, _, G, _, _, _, _, _, _, _, _, hG, _, _, _⟩ := close_keeps h
  obtain ⟨t, ⟨L, Gq, m, input, d, d2, row⟩, -, Fc, -, -⟩ := front_of_yes h
  have hb : Ground.ok (Ground.beginRunL (onSt s.st).st s.frame.group) = true :=
    List.all_eq_true.2 Fc.beginRun
  have ht : (onSt s.st).st.groups[s.frame.group]? = some G := hG
  have e0 : Ground.beginRunP (onSt s.st) s.frame.group =
      some (⟨Own.layoutOf s.st G, Slice.runRows s.st G⟩,
        { onSt s.st with st := Slice.begun s.st s.frame.group G }) := by
    unfold Ground.beginRunP
    rw [if_pos hb, ht]
    rfl
  have e1 := Option.some.inj (e0.symm.trans Fc.layout)
  have ei : input = ⟨Own.layoutOf s.st G, Slice.runRows s.st G⟩ := (congrArg Prod.fst e1).symm
  have ed : d = { onSt s.st with st := Slice.begun s.st s.frame.group G } := (congrArg Prod.snd e1).symm
  subst ei ed
  have hE := extends_begun s.st s.frame.group G
  have hOk : GroupOk s.st G := hI.groups _ G hG
  have hOk' : GroupOk (Slice.begun s.st s.frame.group G) { G with inRun := true, rows := #[] } :=
    hOk.extends hE rfl rfl rfl rfl
  have hcode : G.code = s.frame.shape.code := code_of_shape hOk' Fc.shape rfl
  obtain ⟨_, zk, -, hz, -⟩ := (Own.foldShapeFits_iff _ _).1 Fc.shape
  have hz' : (Slice.begun s.st s.frame.group G).codes.mask[s.frame.shape.maskCode]? = some zk := hz
  rw [hE.codes] at hz'
  have hj : s.frame.shape.maskCode < s.st.codes.mask.size := (Array.getElem?_eq_some_iff.1 hz').1
  have hbits : (Own.layoutOf s.st G).k + (Own.layoutOf s.st G).logEll ≤ 63 := by
    have k1 : (Own.layoutOf s.st G).k = Gq.k := Fc.kh.1
    have k2 : (Own.layoutOf s.st G).logEll =
        (s.st.codes.base.getD s.frame.shape.code default).logEll := by
      show (s.st.codes.base.getD G.code default).logEll = _
      rw [hcode]
    rw [k1, k2]
    exact hBits Gq Fc.group
  exact ⟨⟨L, Gq, m, G⟩, Fc.owed, Fc.link, Fc.group, Fc.due, Fc.mask, hb, hG, hOk, hI.runRows _ G hG,
    hTerms G hG, Fc.rows, Fc.kh, Fc.stretch, hcode, hMask G hG, mask_pow hC hj, hbits, Fc.shape, Fc.maskfits,
    List.all_eq_true.2 Fc.spendAsMask⟩

/-- **The same from an acceptance of the block lifted to the first chain's state**, at the record that `K9.recOf` reads
off the state before it. -/
theorem closeBase_of_closing {Cl : Type} {P : Par} {t t' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (K9.closing (Cl := Cl) P).decide t rs gs = .ok t')
    (hI : InOrder (K9.recOf t).st) (hC : (K9.recOf t).st.codes.lengthsOk = true)
    (hTerms : ∀ G, (K9.recOf t).st.groups[(K9.recOf t).frame.group]? = some G →
      ∀ r ∈ (Slice.runRows (K9.recOf t).st G).toList, ∀ u ∈ r.terms.toList, u.part = .main → u.v.ok = true)
    (hMask : ∀ G, (K9.recOf t).st.groups[(K9.recOf t).frame.group]? = some G →
      G.maskCode = (K9.recOf t).frame.shape.maskCode)
    (hBits : ∀ Gq, (K9.recOf t).frame.groups[(K9.recOf t).frame.link]? = some Gq →
      Gq.k + ((K9.recOf t).st.codes.base.getD (K9.recOf t).frame.shape.code default).logEll ≤ 63) :
    ∃ D, CloseBase P (K9.recOf t) D := by
  obtain ⟨x, hx, -⟩ := closing_writes P t t' rs gs h
  have hy : ((kind (Cl := Cl)) P).decide (K9.recOf t) rs gs = .ok ⟨none, x.1, x.2⟩ :=
    (kind_decide_iff P (K9.recOf t) ⟨none, x.1, x.2⟩ rs gs).2 ⟨x, hx, rfl⟩
  exact closeBase_of_yes hy hI hC hTerms hMask hBits

end ProofFile.Honest.K10.YesFree

#print axioms ProofFile.Honest.K10.YesFree.mask_pow
#print axioms ProofFile.Honest.K10.YesFree.code_of_shape
#print axioms ProofFile.Honest.K10.YesFree.closeBase_of_yes
#print axioms ProofFile.Honest.K10.YesFree.closeBase_of_closing
