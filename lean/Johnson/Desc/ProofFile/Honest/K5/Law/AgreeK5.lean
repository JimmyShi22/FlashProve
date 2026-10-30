-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/AgreeK5.lean: K5's OWN LOTS AGREE WITH ONE ANOTHER: so what is
left, for one of them, of the frame's premise "the other lots of the same message agree with this
one" (`LotsAgree`, Johnson/Desc/ProofFile/Honest/Thread/ScriptLots.lean) IS AGAINST THE OTHER
KINDS' LOTS ALONE. IT PAYS A PART OF THAT PREMISE, AND EXCHANGES ANOTHER PART FOR ONE PREMISE ON
PUBLIC DATA. CONDITIONAL: under the hypothesis h, the library's head on the public input
(`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean), and on hAp. Two definitions; seven theorems.

Main names:
  `IsK5Lot h S rd seat heard Z5 L`: L IS ONE OF K5's LOTS (LotsK5.lean in this folder): the mask's
    lot (`maskLot`) of one of the twelve groups, at the group's plan, the place of its lookup on the
    calls, the member that `maskMsg` names, the seat Z5 g a and the plan's first free slot; or the
    filling's lot (`fillLot`) at an address that is seated in a segment. A PROPERTY, NOT A LIST: no
    seat's addresses are given as a list anywhere, and to agree needs none.
  `k5Lots_agree`: **ANY TWO OF THEM AGREE.** `k5_msgsAgree`: a list of them agrees in itself.
  `k5_agree_cut`: **THE CUT**: for a list ml₅ of them and one of them, L:
    `LotsAgree (ml₅ ++ rest) L` holds just if `LotsAgree rest L` does.
  `MaskNosApart h`: THE PREMISE hAp, ON PUBLIC DATA: the messages with two segments' mask rows bear
    two numbers in the witness. NOT PAID HERE: `maskNosApart_head` (MaskNos.lean in this folder)
    pays it under h, and states the three tops without it.
  `lays_one_text_S`: `lays_one_text` (KeysCover.lean in this folder) at every sizes S: ITS LINES ARE
    THAT THEOREM's, with S for `Sz.ref`; that one follows from this one at `Sz.ref`.
  `fillTxt_some`, `agree2_fill_fill`, `agree2_mask_fill`: where the filling's text answers; the
    cases.

How. Filling against filling: both texts answer what the filling's call that asks first answers;
one number gives one segment and message (`num_apart_head`), so one array and entry
(`ask_is_array`), whose value does not read the challenges. Mask against filling: the flag parts
them: the one answers in the mask table alone, the other in the main rows alone: no premise. Mask
against mask: one number gives one link by hAp, so one group, plan, place and member: one lot. The
cut: `lotsAgree_cut` (AgreeParts.lean in this folder).

Limits. AGAINST THE OTHER KINDS' LOTS NOTHING IS PROVED: not against the lot of whoever sends the
whole mask row or the whole message, not against another kind's slots. That K5's lots ARE among the
lots is not proved. hAp IS A DEBT OF THIS FILE (see above). It speaks only of the member that
`maskMsg` names: a message that a segment keeps from an earlier one is seen from both under one
number. It asks every link at which `maskMsg` answers; the proof spends it at the twelve lookups'.
Whether two groups' slots of the mask row overlap was not looked at: the proof goes by the numbers.
One S, one reader rd and one family Z5 in all lots; the seats and the numbers of challenges heard
may differ from segment to segment, BUT THE FAMILY IS ONE OVER ALL SEGMENTS: a caller whose laws
stand group by group hands in one family for all twelve. `k5_agree_cut` stands at ml₅ ++ rest:
`LotsAgree` reads membership alone, so at a list that is dealt otherwise `lotsAgree_iff` with
`k5Lots_agree` serves, and `lotsAgree_flatten` at a list of lists. Of no lot's text is it proved
that it is what an honest prover sends. The file stands over LotsK5.lean, a working form, and over
the frame's ScriptLots.lean: neither lies in a seal. Through its imports it stands above
Cb/Bridge/CodeListRSProved.lean, and so above the files under ThirdParty/ (lean/LIMITS.md, L15): a
fact on import lines. At the earlier hash `OnBytes.secondHashFunction`, a fixed function.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.LotsK5
import Johnson.Desc.ProofFile.Honest.K5.Law.KeysCover
import Johnson.Desc.ProofFile.Honest.K5.Law.AgreeParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First.Look (lookAt sigListCalls)
open VerifiableInference.Desc.First.Att.P (maskMsg)
open ProofFile.Honest.FirstThread (MsgLot LotsAgree MsgsAgree Agree2 agree2_self agree2_symm
  msgsAgree_of_pairs lotsAgree_cut)
open ProofFile.Honest.K1 (cellsVals firstData)
open P5J (AtMgA TS)

/-- **Where the filling's text answers**: in the main rows, and with what the filling's call that
asks first answers. -/
theorem fillTxt_some {Bk : ProverCoinCounts} {W : Type} {S : Sz} {codes : OnBytes.Codes}
    {s : OnBytes.Params.ReqShape} {ly : OnBytes.Params.ReqLayout} {rd : W → Readers}
    {seat : MsgAddr → Option (ℕ × ℕ)} {heard : MsgAddr → ℕ} {Ad : MsgAddr} {l m : ℕ}
    {k : Coins Bk} {v : W} {hd : List Fmt.Drawn} {mask : Bool} {row place : ℕ}
    {y : OnBytes.Slice.GE}
    (q : fillTxt S codes s ly rd seat heard Ad l m k v hd mask row place = some y) :
    mask = false ∧ ∃ z, (firstData S codes s ly seat heard).ask (rd v) hd Ad row place =
      .ok (some z) ∧ y = asE (some z) := by
  cases mask with
  | true => simp [fillTxt] at q
  | false =>
    refine ⟨rfl, ?_⟩
    simp only [fillTxt, Bool.false_eq_true, ↓reduceIte] at q
    split at q
    · split at q
      · split at q
        · rename_i z hz
          exact ⟨z, hz, (Option.some.inj q).symm⟩
        · cases q
      · cases q
    · cases q

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr : Type}

/-- **THE FORM ASKS NO NUMBER FOR TWO TEXTS, AT EVERY SIZES S.** CONDITIONAL: under the hypothesis
h; the two addresses' seats; both calls answer an element at one row and place; the two pairs bear
one number in the witness. -/
theorem lays_one_text_S (S : Sz) {seat seat' : MsgAddr → Option (ℕ × ℕ)}
    {heard heard' : MsgAddr → ℕ} {R : Readers} {hd hd' : List Fmt.Drawn} {Ad Ad' : MsgAddr}
    {l m l' m' row place : ℕ} {y y' : Cb.Gl.F ⊕ Cb.Gl.E} (hAd : seat Ad = some (l, m))
    (hAd' : seat' Ad' = some (l', m'))
    (q : (firstData S h.𝔇.sent.codes h.𝔇.sent.shape h.𝔇.sent.layout seat heard).ask R hd Ad row
      place = .ok (some y))
    (q' : (firstData S h.𝔇.sent.codes h.𝔇.sent.shape h.𝔇.sent.layout seat' heard').ask R hd'
      Ad' row place = .ok (some y'))
    (e : P5J.At.num Zp l m = P5J.At.num Zp l' m') : y = y' := by
  obtain ⟨A, i, c, hA, hm, hB, ey⟩ := ask_is_array hAd q
  obtain ⟨A', i', c', -, -, hB', ey'⟩ := ask_is_array hAd' q'
  have mem : ∀ {l₀ : ℕ} {B : OnBytes.Params.ReqArray}, B ∈ h.𝔇.sent.layout.link.getD l₀ [] →
      ∃ As, h.𝔇.sent.layout.link[l₀]? = some As ∧ B ∈ As := by
    intro l₀ B hBm
    rw [List.getD_eq_getElem?_getD] at hBm
    cases hq : h.𝔇.sent.layout.link[l₀]? with
    | none =>
      rw [hq] at hBm
      exact absurd hBm (by simp)
    | some As =>
      rw [hq] at hBm
      exact ⟨As, rfl, hBm⟩
  obtain ⟨As, hl, hAs⟩ := mem hA
  obtain ⟨rfl, e2⟩ := num_apart_head h (l' := l') (m' := m') hl hAs (by rw [hm]; exact e)
  obtain rfl : m = m' := by rw [← hm]; exact e2
  obtain ⟨rfl, rfl, rfl⟩ : A = A' ∧ i = i' ∧ c = c' := by
    have k := Option.some.inj (hB.symm.trans hB')
    exact ⟨(Prod.mk.inj k).1, (Prod.mk.inj (Prod.mk.inj k).2).1, (Prod.mk.inj (Prod.mk.inj k).2).2⟩
  rw [ey, ey']
  rfl

/-- **Two of the filling's lots agree.** CONDITIONAL: under the hypothesis h; the two addresses'
seats. One S and one reader in both. -/
theorem agree2_fill_fill (S : Sz) (rd : Local W₀ Rc ProofFile.Inst Tr → Readers)
    {seat seat' : MsgAddr → Option (ℕ × ℕ)} {heard heard' : MsgAddr → ℕ} {Ad Ad' : MsgAddr}
    {l m l' m' : ℕ} (hAd : seat Ad = some (l, m)) (hAd' : seat' Ad' = some (l', m')) :
    Agree2 (fillLot (Bk := Bk) h S rd seat heard Ad l m)
      (fillLot h S rd seat' heard' Ad' l' m') := by
  intro e k w hd mask row place y y' q q'
  obtain ⟨-, z, hz, rfl⟩ := fillTxt_some (Bk := Bk) (k := k) q
  obtain ⟨-, z', hz', rfl⟩ := fillTxt_some (Bk := Bk) (k := k) q'
  rw [lays_one_text_S h S hAd hAd' hz hz' e.symm]

/-- **The mask's lot and a lot of the filling agree**: the flag parts them: they never answer at one
entry. No premise. -/
theorem agree2_mask_fill (x₁ : VerifiableInference.Desc.First.Look.Place) (kM : ℕ)
    (hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length) (Z5 : Seat5) (ν₅ : ℕ) (S : Sz)
    (rd : Local W₀ Rc ProofFile.Inst Tr → Readers) (seat : MsgAddr → Option (ℕ × ℕ))
    (heard : MsgAddr → ℕ) (Ad : MsgAddr) (l m : ℕ) :
    Agree2 (maskLot (Bk := Bk) h x₁ kM hk Z5 ν₅) (fillLot h S rd seat heard Ad l m) := by
  intro _ k w hd mask row place y y' q q'
  obtain ⟨hm, -⟩ := fillTxt_some (Bk := Bk) (k := k) q'
  subst hm
  simp [maskLot, maskTxt] at q

/-- **The messages with two segments' mask rows bear two numbers in the witness.** It is a
definition: the form of a hypothesis ON PUBLIC DATA. Only the member that `maskMsg` names is spoken
of: a message that a segment keeps from an earlier one is seen from both. -/
def MaskNosApart : Prop :=
  ∀ (x₁ x₁' : VerifiableInference.Desc.First.Look.Place) (kM kM' : ℕ)
    (hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length)
    (hk' : kM' < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁'.link).length),
    maskMsg h.𝔇.sent x₁.link = some kM → maskMsg h.𝔇.sent x₁'.link = some kM' →
    maskNo5 h x₁ kM hk = maskNo5 h x₁' kM' hk' → x₁.link = x₁'.link

/-- **L is one of K5's lots**: the mask's lot of one of the twelve groups, or the filling's lot at
an address that is seated in a segment. seat, heard: by segment. Z5: the seat, by group and plan. It
is a definition. -/
def IsK5Lot (S : Sz) (rd : Local W₀ Rc ProofFile.Inst Tr → Readers)
    (seat : ℕ → MsgAddr → Option (ℕ × ℕ)) (heard : ℕ → MsgAddr → ℕ)
    (Z5 : ℕ → OnBytes.Attention.Plan → Seat5) (L : MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr)) : Prop :=
  (∃ (g : ℕ) (a : OnBytes.Attention.Plan) (x₁ : VerifiableInference.Desc.First.Look.Place)
      (kM : ℕ) (hk : kM < (sigListCalls h.𝔇.sent h.𝔇.l3.rad x₁.link).length),
      g < 12 ∧ (P5J.At.X Zp).A[g]? = some a ∧
      lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ ∧ maskMsg h.𝔇.sent x₁.link = some kM ∧
      L = maskLot h x₁ kM hk (Z5 g a) (OnBytes.Model.Forest.elems a.fs)) ∨
    ∃ (l : ℕ) (Ad : MsgAddr) (m : ℕ), seat l Ad = some (l, m) ∧
      L = fillLot h S rd (seat l) (heard l) Ad l m

variable {h}

/-- **ANY TWO OF K5's LOTS AGREE.** CONDITIONAL: under the hypothesis h; hAp, on public data. -/
theorem k5Lots_agree (hAp : MaskNosApart h) {S : Sz} {rd : Local W₀ Rc ProofFile.Inst Tr → Readers}
    {seat : ℕ → MsgAddr → Option (ℕ × ℕ)} {heard : ℕ → MsgAddr → ℕ}
    {Z5 : ℕ → OnBytes.Attention.Plan → Seat5} {L L' : MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr)}
    (H : IsK5Lot h S rd seat heard Z5 L) (H' : IsK5Lot h S rd seat heard Z5 L') :
    Agree2 L L' := by
  rcases H with ⟨g, a, x₁, kM, hk, -, ha, hx, hm, rfl⟩ | ⟨l, Ad, m, hAd, rfl⟩
  · rcases H' with ⟨g', a', x₁', kM', hk', -, ha', hx', hm', rfl⟩ | ⟨l', Ad', m', -, rfl⟩
    · intro e
      have el := hAp x₁' x₁ kM' kM hk' hk hm' hm e
      have e1 := VerifiableInference.OnPublicFiles.lookAt_link hx
      have e2 := VerifiableInference.OnPublicFiles.lookAt_link hx'
      obtain rfl : g' = g := by omega
      obtain rfl := Option.some.inj (ha'.symm.trans ha)
      obtain rfl := Option.some.inj (hx'.symm.trans hx)
      obtain rfl := Option.some.inj (hm'.symm.trans hm)
      exact agree2_self _ rfl
    · exact agree2_mask_fill h _ _ _ _ _ _ _ _ _ _ _ _
  · rcases H' with ⟨g', a', x₁', kM', hk', -, -, -, -, rfl⟩ | ⟨l', Ad', m', hAd', rfl⟩
    · exact agree2_symm (agree2_mask_fill h _ _ _ _ _ _ _ _ _ _ _ _)
    · exact agree2_fill_fill h S rd hAd hAd'

/-- **A LIST OF K5's LOTS AGREES IN ITSELF.** CONDITIONAL: as `k5Lots_agree`. -/
theorem k5_msgsAgree (hAp : MaskNosApart h) {S : Sz} {rd : Local W₀ Rc ProofFile.Inst Tr → Readers}
    {seat : ℕ → MsgAddr → Option (ℕ × ℕ)} {heard : ℕ → MsgAddr → ℕ}
    {Z5 : ℕ → OnBytes.Attention.Plan → Seat5} {ml₅ : List (MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr))}
    (hm : ∀ L ∈ ml₅, IsK5Lot h S rd seat heard Z5 L) : MsgsAgree ml₅ :=
  msgsAgree_of_pairs (fun _ _ H H' => k5Lots_agree hAp H H') hm

/-- **WHAT IS LEFT OF "AGREE" FOR ONE OF K5's LOTS IS AGAINST THE OTHERS' LOTS ALONE.** CONDITIONAL:
as `k5Lots_agree`. -/
theorem k5_agree_cut (hAp : MaskNosApart h) {S : Sz} {rd : Local W₀ Rc ProofFile.Inst Tr → Readers}
    {seat : ℕ → MsgAddr → Option (ℕ × ℕ)} {heard : ℕ → MsgAddr → ℕ}
    {Z5 : ℕ → OnBytes.Attention.Plan → Seat5}
    {ml₅ rest : List (MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr))}
    (hm : ∀ L ∈ ml₅, IsK5Lot h S rd seat heard Z5 L) {L : MsgLot Bk (Local W₀ Rc ProofFile.Inst Tr)}
    (hL : IsK5Lot h S rd seat heard Z5 L) : LotsAgree (ml₅ ++ rest) L ↔ LotsAgree rest L :=
  lotsAgree_cut (fun _ _ H H' => k5Lots_agree hAp H H') hm hL

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.fillTxt_some
#print axioms ProofFile.Honest.K5.lays_one_text_S
#print axioms ProofFile.Honest.K5.agree2_fill_fill
#print axioms ProofFile.Honest.K5.agree2_mask_fill
#print axioms ProofFile.Honest.K5.k5Lots_agree
#print axioms ProofFile.Honest.K5.k5_msgsAgree
#print axioms ProofFile.Honest.K5.k5_agree_cut
