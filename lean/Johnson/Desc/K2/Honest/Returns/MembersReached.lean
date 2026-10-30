-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K2/Honest/Returns/MembersReached.lean: FIVE MORE CLAUSES OF THE LAW "THE KIND's OWN
DECISION SAYS YES AT A SEGMENT's FIRST PLACE" (`LinkPlain`, Returns/LinkSent.lean) AT A STATE THAT
IS REACHED IN FRONT OF THE SWITCH INTO A LATER GROUP, IN THE GOALS' SCOPE, WITH NO TEST ON THE
PUBLIC PART: `OldFits.rows` · `OldFits.named` · `TablesFit.claimKept` · `ReadFits.stated` ·
`ReadFits.placed`. All five read the members of the layout that the last closing laid into the
carried rows; behind the bridge (Returns/ClosedReached.lean) the closing's own tests on the fold's
shape and row say what is wanted. `claimKept` is one of the law's two clauses that compare field
elements with (1, 1): it holds whoever plays, since every closing that says yes has asked it.
Statements with their proofs: calls and unfoldings.

  `closeFrame_keptForms` a yes of the frame's closing: the kept forms that it lays into the carried
                    rows are a multiple each of the forms of a row that passed the test on rows, at
                    the closing's own statement
  `member_of_kept`, `kept_of_flag` a kept old message is a member of the layout; a member whose flag
                    says "kept" is a kept old message
  `member_there` each member of that layout is a message of the closing's statement
  `stated_of_close` so each message that the reading names (the members and the fresh mask) is one
                    of every statement grown out of it
  `rows_of_close` `OldFits.rows` there
  `tableBits_grown` a table keeps its index bits where the statement grows
  `scale_slice`, `formFits_scale` a multiple of a tensor has its slice; a multiple of a form fits
                    what the form fits
  `named_of_close`, `claimKept_of_close` `OldFits.named`, `TablesFit.claimKept` there
  `link_members_reached` `rows`, `named`, `claimKept` at `frontAt s L Q`, each in its structure's
                    own letters, for all L and Q
  `link_book_reached` `placed` and `stated` in `ReadFits`' own letters, at what the reading is
                    handed

By, all the library's: `closeFrame_iff` (Johnson/Desc/First/Close/Law/CloseMeans.lean) ·
`foldRowFits_iff` (Johnson/Desc/Own/FoldMean.lean) · `formFits_iff`
(Johnson/Desc/Own/ShapesMean.lean) · `closeFrame_sizes`
(Johnson/Desc/First/Link/Law/CarriedSizes.lean) · `closeFrame_carried`
(Johnson/Desc/First/Close/Law/CarriedRows.lean) · `idxOf_some` (OnBytes/Slice/BlkProxMany.lean) ·
`Tensor.pairs_scale`, `Tensor.denseVars_scale` (OnBytes/Iop/FixLaws.lean) · `bookHas_reached`
(Johnson/IMR/AtReach.lean) · `front_len` (Johnson/IMR/FinPin.lean) · `reach_raw`
(Johnson/Top/H0/Walk/Reach.lean). Near relatives, not called: `tableBits_same`
(Johnson/Desc/Key/RowsCarry.lean): `tableBits_grown` from the two messages, their shapes and the
codes · `switchKept_list` (Johnson/Top/H0/K2Hears/KeptNos.lean): the kept old messages as the
members at the kept places: `member_of_kept` and `kept_of_flag` read off it · `Tensor.InOrder.scale`
(the same file), `orderForm_scale` (OnBytes/Slice/BlkProxOrder.lean): `formFits_scale` for two
weaker words for "in order" · `rows_pin` (Returns/TargetPin.lean) with `written_at`
(Returns/WrittenFronts.lean): `OldFits.rows` under three named tests on the public part; here none
is asked.

Limits. The links' places alone. `TablesFit.claimMain` IS NOT REACHED: the carried claim is the
row's form with its lowest variables fixed, and the library's `Form.fixLow_shape`
(OnBytes/Iop/FixLaws.lean) says in its own docstring that it does not show that the result fits.
`ReadFits.own`, `OldFits.once`, `keptCode`: not reached. "Reached" is: over the list of the wrapped
sub-protocols. THE PREMISES IN FRONT ARE SHOWN MET TOGETHER BY NOBODY HERE: NO MEMBER. This file's
imports are heavy. Nothing on any property.



-/
import Johnson.Desc.K2.Honest.Returns.ClosedReached
import OnBytes.Slice.BlkProxMany

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns
open OnBytes
open OnBytes.Slice.ProxRun (idxOf_some)
open VerifiableInference.Desc (Block Chain FileDescription Grows)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (closeFrame closeFrame_iff closeFrame_carried)
open VerifiableInference.Desc.LinkJoin (closeFrame_sizes)
open VerifiableInference.Desc.Sound (below)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open _root_.Tw.K2 (Par9 Sent Col)
open ProofFile (Cl)

/-! ## Right behind a closing: no state of the walk -/

theorem closeFrame_keptForms {owed : Option Nat} {f : ReqFrame} {S₀ : Statement}
    {es : List Fmt.Entry} {rs : List Fmt.RoundView} {x : ReqFrame × Statement}
    (h : closeFrame owed f S₀ es rs = .ok x) :
    ∃ (F : FoldShape) (row : GroupRow) (a : E), Own.FoldRowFit x.2 F row ∧
      x.1.rows.layout = F.layout ∧
      x.1.rows.kept = row.kept.map fun k => { k with c := k.c.scale a } := by
  obtain ⟨-, Lk, -, Gf, -, -, rows, hc, e⟩ := (closeFrame_iff owed f S₀ es rs x.1 x.2).1 h
  obtain ⟨eB, es', rB, rs', -, -, m, -, row, L, S₁, -, -, hF⟩ := hc
  obtain ⟨eE, eR, rE, rR, -, -, -, -, -, -, -, d2, -, sum, eps, -, hrow, gamma, claim, -, hout,
    hS'⟩ := hF
  have hR := (Own.foldRowFits_iff _ _ _).1 hrow
  rw [← hS'] at hR
  refine ⟨_, row, foldKeptFactor eps gamma, hR, ?_, ?_⟩
  · rw [e]
    show rows.layout = _
    rw [hout]
    rfl
  · rw [e]
    show rows.kept = _
    rw [hout]
    rfl

theorem member_of_kept {old : SingleRows} {o : Nat} (ho : o ∈ (switchKept old).toList) :
    o ∈ old.layout.members.toList := by
  unfold switchKept at ho
  simp only [Array.toList_map, Array.toList_filter, Array.toList_zip, List.mem_map,
    List.mem_filter] at ho
  obtain ⟨⟨a, b⟩, ⟨hp, -⟩, rfl⟩ := ho
  exact (List.of_mem_zip hp).1

theorem kept_of_flag {old : SingleRows} (hs : old.layout.kept.size = old.layout.members.size)
    {i : Nat} (hi : i < old.layout.members.size) (hf : old.layout.kept.getD i false = true) :
    old.layout.members[i] ∈ (switchKept old).toList := by
  have hk : i < old.layout.kept.size := by omega
  have hf' : old.layout.kept[i] = true := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hk] at hf
    exact hf
  have hm : (old.layout.members[i], old.layout.kept[i]) ∈
      old.layout.members.zip old.layout.kept :=
    Array.mem_iff_getElem.2 ⟨i, by simp only [Array.size_zip]; omega, by simp⟩
  exact Array.mem_toList_iff.2 (Array.mem_map.2 ⟨_, Array.mem_filter.2 ⟨hm, hf'⟩, rfl⟩)

theorem member_there {owed : Option Nat} {f : ReqFrame} {S₀ : Statement}
    {es : List Fmt.Entry} {rs : List Fmt.RoundView} {x : ReqFrame × Statement}
    (h : closeFrame owed f S₀ es rs = .ok x) :
    ∀ o ∈ x.1.rows.layout.members.toList, ∃ y, x.2.oracles[o]? = some y := by
  obtain ⟨S₁, F, ⟨c, zk, -, -, -, -, -, -, -, -, -, hmem, -⟩, g1, eL, -⟩ := closeFrame_shape h
  rw [eL]
  intro o ho
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ho
  have hi' : i < F.layout.members.size := by simpa using hi
  obtain ⟨y, hy, -⟩ := hmem i hi'
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hi'] at hy
  obtain ⟨y₂, h2, -⟩ := g1.2.2 _ y hy
  exact ⟨y₂, by simpa using h2⟩

theorem stated_of_close {owed : Option Nat} {f : ReqFrame} {S₀ : Statement}
    {es : List Fmt.Entry} {rs : List Fmt.RoundView} {x : ReqFrame × Statement}
    (h : closeFrame owed f S₀ es rs = .ok x) {T : Statement} (hg : Grows x.2 T) :
    ∀ o ∈ (singleRowsOracles x.1.rows).toList, o < T.oracles.size := by
  obtain ⟨Gf, -, hm, -, -, -, y₀, h0, -⟩ := closeFrame_sizes h
  have there : ∀ (o : Nat) (y : OnBytes.Oracle), x.2.oracles[o]? = some y →
      o < T.oracles.size := fun o y hy => by
    obtain ⟨y', h1, -⟩ := hg.2.2 o y hy
    exact (Array.getElem?_eq_some_iff.1 h1).1
  intro o ho
  unfold singleRowsOracles at ho
  rw [hm] at ho
  simp only [beq_self_eq_true, ↓reduceIte, Array.toList_push, List.mem_append,
    List.mem_singleton] at ho
  rcases ho with ho | rfl
  · obtain ⟨y, hy⟩ := member_there h o ho
    exact there o y hy
  · exact there _ y₀ h0

theorem rows_of_close {owed : Option Nat} {f : ReqFrame} {S₀ : Statement}
    {es : List Fmt.Entry} {rs : List Fmt.RoundView} {x : ReqFrame × Statement}
    (h : closeFrame owed f S₀ es rs = .ok x) {T : Statement} (hg : Grows x.2 T) :
    x.1.rows.keptRows = ((switchKept x.1.rows).toList.map fun o =>
      (T.oracles.getD o default).shape.mainRows).sum := by
  obtain ⟨Gf, G, -, -, CO⟩ := closeFrame_carried h
  rw [CO.keptRows]
  refine congrArg List.sum (List.map_congr_left fun o ho => ?_)
  obtain ⟨y, hy⟩ := member_there h o (member_of_kept ho)
  rw [hy, grown_shape hg hy]
  rfl

theorem tableBits_grown {T T' : Statement} (hg : Grows T T') {o : Nat} {y : OnBytes.Oracle}
    (hy : T.oracles[o]? = some y) (part : OnBytes.Part) :
    T'.tableBits o part = T.tableBits o part := by
  obtain ⟨y', h1, h2, -⟩ := hg.2.2 o y hy
  unfold Statement.tableBits Statement.rowBits Statement.placeBits
  simp only [h1, hy, hg.1, h2]

theorem scale_slice (v : Tensor) (a : E) :
    (v.scale a).first = v.first ∧ (v.scale a).values = v.values := by
  unfold Tensor.scale
  exact ⟨rfl, rfl⟩

theorem formFits_scale {c : Form} {n : Nat} (h : Own.formFits c n = true) (a : E) :
    Own.formFits (c.scale a) n = true := by
  obtain ⟨h1, h2⟩ := (Own.formFits_iff c n).1 h
  refine (Own.formFits_iff _ _).2 ⟨fun v hv => ?_, fun e he => ?_⟩
  · obtain ⟨v₀, hv₀, rfl⟩ := List.mem_map.1 hv
    have h0 := h1 v₀ hv₀
    unfold Own.InOrder at h0 ⊢
    rw [Tensor.pairs_scale, Tensor.denseVars_scale, (scale_slice v₀ a).1, (scale_slice v₀ a).2]
    exact h0
  · obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.1 he
    exact h2 e₀ he₀

theorem named_of_close {owed : Option Nat} {f : ReqFrame} {S₀ : Statement}
    {es : List Fmt.Entry} {rs : List Fmt.RoundView} {x : ReqFrame × Statement}
    (h : closeFrame owed f S₀ es rs = .ok x) :
    ∀ k ∈ x.1.rows.kept.toList, k.oracle ∈ (switchKept x.1.rows).toList := by
  obtain ⟨F, row, a, R, eL, eK⟩ := closeFrame_keptForms h
  have hs := (layFits_of_close h (Grows.refl x.2)).keptSize
  intro k hk
  rw [eK] at hk
  simp only [Array.toList_map, List.mem_map] at hk
  obtain ⟨k₀, hk₀, rfl⟩ := hk
  obtain ⟨⟨i, hi, hflag⟩, -⟩ := R.2.2 k₀ (Array.mem_toList_iff.1 hk₀)
  rw [← eL] at hi hflag
  obtain ⟨h1, h2⟩ := idxOf_some _ _ _ hi
  have e : x.1.rows.layout.members[i] = k₀.oracle := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1] at h2
    exact h2
  show k₀.oracle ∈ _
  rw [← e]
  exact kept_of_flag hs h1 hflag

theorem claimKept_of_close {owed : Option Nat} {f : ReqFrame} {S₀ : Statement}
    {es : List Fmt.Entry} {rs : List Fmt.RoundView} {x : ReqFrame × Statement}
    (h : closeFrame owed f S₀ es rs = .ok x) {T : Statement} (hg : Grows x.2 T) :
    ∀ k ∈ x.1.rows.kept.toList, Own.formFits k.c (T.tableBits k.oracle .main) = true := by
  obtain ⟨F, row, a, R, eL, eK⟩ := closeFrame_keptForms h
  intro k hk
  obtain ⟨y, hy⟩ := member_there h _ (member_of_kept (named_of_close h k hk))
  rw [tableBits_grown hg hy]
  rw [eK] at hk
  simp only [Array.toList_map, List.mem_map] at hk
  obtain ⟨k₀, hk₀, rfl⟩ := hk
  show Own.formFits (k₀.c.scale a) (x.2.tableBits k₀.oracle .main) = true
  exact formFits_scale (R.2.2 k₀ (Array.mem_toList_iff.1 hk₀)).2 a

/-! ## At a reached state -/

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {z : ProofFile.InstPub}

/-- **`OldFits.rows`, `OldFits.named`, `TablesFit.claimKept`, with no test on the public part.** -/
theorem link_members_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {m : Nat} (h23 : m < 23) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s))
    (L : Params.ReqLink) (Q : ReqGroup) :
    (frontAt s L Q).f.rows.keptRows = ((switchKept (frontAt s L Q).f.rows).toList.map fun o =>
        ((frontAt s L Q).st.oracles.getD o default).shape.mainRows).sum ∧
      (∀ k ∈ (frontAt s L Q).f.rows.kept.toList,
        k.oracle ∈ (switchKept (frontAt s L Q).f.rows).toList) ∧
      ∀ k ∈ (frontAt s L Q).f.rows.kept.toList,
        Own.formFits k.c ((frontAt s L Q).st.tableBits k.oracle .main) = true := by
  obtain ⟨owed, f, S₀, es, rs, x, hx, hf, hg⟩ := link_closed_reached hS hR O h23 hr
  show s.check.frame.rows.keptRows = ((switchKept s.check.frame.rows).toList.map fun o =>
      (s.st.oracles.getD o default).shape.mainRows).sum ∧
    (∀ k ∈ s.check.frame.rows.kept.toList, k.oracle ∈ (switchKept s.check.frame.rows).toList) ∧
    ∀ k ∈ s.check.frame.rows.kept.toList, Own.formFits k.c (s.st.tableBits k.oracle .main) = true
  rw [hf]
  exact ⟨rows_of_close hx hg, named_of_close hx, claimKept_of_close hx hg⟩

/-- **`ReadFits.placed` and `stated`.** -/
theorem link_book_reached (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {m : Nat} (h23 : m < 23) {s : S}
    (hr : Reach 0 (c.blocksInOrder.map below) (ProofFile.startS Z) (14 * (m + 1) + 2) (z, s))
    (L : Params.ReqLink) (Q : ReqGroup)
    (P9 : Par9) (y : Sent) (rL : Fmt.RoundView) (cols : List OpenedColumn) :
    (∀ o ∈ (idsOf (inFront P9 (frontAt s L Q) s.book y rL cols)).toList,
        o < (inFront P9 (frontAt s L Q) s.book y rL cols).book.place.size) ∧
      ∀ o ∈ (idsOf (inFront P9 (frontAt s L Q) s.book y rL cols)).toList,
        o < (inFront P9 (frontAt s L Q) s.book y rL cols).st.oracles.size := by
  obtain ⟨owed, f, S₀, es, rs, x, hx, hf, hg⟩ := link_closed_reached hS hR O h23 hr
  have hlen : 14 * (m + 1) + 2 ≤ (Meaning.K2.frontOf c).length := by
    rw [Meaning.K2.front_len hS hR O]
    omega
  have hb := Meaning.K2.bookHas_reached O (reach_raw hr) hlen
  have H := stated_of_close hx hg
  rw [← hf] at H
  exact ⟨fun o ho => by
    show o < s.book.place.size
    rw [hb]
    exact H o ho, fun o ho => H o ho⟩

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.closeFrame_keptForms
#print axioms VerifiableInference.Desc.K2.Honest.Returns.member_of_kept
#print axioms VerifiableInference.Desc.K2.Honest.Returns.kept_of_flag
#print axioms VerifiableInference.Desc.K2.Honest.Returns.member_there
#print axioms VerifiableInference.Desc.K2.Honest.Returns.stated_of_close
#print axioms VerifiableInference.Desc.K2.Honest.Returns.rows_of_close
#print axioms VerifiableInference.Desc.K2.Honest.Returns.tableBits_grown
#print axioms VerifiableInference.Desc.K2.Honest.Returns.scale_slice
#print axioms VerifiableInference.Desc.K2.Honest.Returns.formFits_scale
#print axioms VerifiableInference.Desc.K2.Honest.Returns.named_of_close
#print axioms VerifiableInference.Desc.K2.Honest.Returns.claimKept_of_close
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_members_reached
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_book_reached
