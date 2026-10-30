-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/HonestTrace/ConstrHeadAtTrace.lean

Conditional lemma for public files in the goals' scope and a served request: the sentence constrQAt
(Johnson/P5J/MeansQ.lean) at sub-proof 24, the output head's, and each of the four parts idn,
lookCalls, rider and small, at the library's way of reading a witness, hidAtSeat, and the head's
filling headPartK6 (Johnson/Desc/Kinds/Law/HeadCutsK6.lean): from one condition on the symbols that
the witness's messages hold at the seats, two on the decoder, one on the request, and three on the
table's sizes and the table of the exponential.
This file states no goal.

The three premises on the files: Z is in the goals' scope (VerifierAndGoals.InScope Z = true); the goals'
reader returns pp at Z (VerifierAndGoals.readFiles Z = .ok pp); publicOf returns X at Z's parameter file and
scale file.

Main theorem:
* "constr_head": under the three premises on the public files, ServesAt X i x, sizes s that follow
  X's plans with the shift 2^17 and the radix 2^20, SymsOfTrace at the messages readAt cs arr ms N k
  w and theTrace X i x; if every table that dec a y yields holds i (hH) and is the witness's own
  cells (hW), the request with the witness's token put in is x (hq), rows ≤ hRef, cols ≤ 2^kRef, and
  tab u is EX u below 2^16 (htab): for p in parts4: constrQAt 24 put (hidAtSeat ... dec ...)
  (headPartK6 ... pl tab put (hidAtSeat ... dec' ...) tokH) digitsPart 24 p a y w. pl, tokH, dec'
  and digitsPart are arbitrary.

How. The way back from the output head's relation to the head's four parts is parts_of_headOrd
(Johnson/Desc/K6/Honest/Law/Back/PartsOfHeadOrd.lean). It takes nine premises on public data. Three
stay premises here: hr0, hc0 and htab. Six are had here: Hd.FullH and digSh = 8 are fields of the
first part of Hd.eleven_of_core at Hd.core_of_scope (Johnson/Meaning/PublicCore.lean;
Johnson/Goal/Meaning/ScopeCore.lean); Hd.NumH by Hd.numH_of_layout and Hd.BorderH by
Hd.borderH_of_layout (Johnson/Road/HeadPlace.lean), at fields of the same; that the tests on the
head's plan pass by ok_in_scope (Johnson/Goal/Meaning/HeadCondScope.lean); Head3 x by
Meaning.head3_of_req (Johnson/Goal/Meaning/Row.lean), carried along hq. Five of the six are had by
the steps of headCuts_k6 (Johnson/Desc/Kinds/Law/HeadCutsK6.lean); there the tests on the plan are a
premise, which headCuts_atAll (Johnson/Desc/Kinds/Law/HeadCutsAtAll.lean) has by ok_in_scope too.
The two other premises of parts_of_headOrd: Holds w.cells i is the sentence's own premise on the
decoded table, carried along hW; Hd.HeadOrdLB at the list that ownQ reads at sub-proof 24 is a
clause of MeetsAll X i x (theTrace X i x) (its field ords; meetsAll_theTrace,
Johnson/Goal/HonestTrace/FullPlanesInScope.lean), carried along the equation that ownQ reads
theTrace X i x 24 there (base_own_of_syms, Johnson/Goal/HonestTrace/ConstrAtTrace.lean). The index
falls by holds_unique (Johnson/Goal/Meaning/NextToken.lean).

Limits. A conditional lemma, and a joining: its weight lies in parts_of_headOrd and the four files
of its folder beneath it (Johnson/Desc/K6/Honest/Law/Back/), which are not of this folder.
No theorem of this file shows its premises of any Z, witness, decoder or table. At the part small it
says less than constr_head_small (ConstrAtTrace.lean), under more premises: there any H' stands
inside headPartK6, here hidAtSeat at a decoder dec'. Where dec a y is none, hH and hW ask nothing,
and the sentence says Base at the part small alone. The parts lookDigits and lookCallsHeard are not
in parts4 and are not treated here. All is at the full size. This file can be built only where
Johnson/Desc/K6/Honest/Law/Back/PartsOfHeadOrd.lean and what it imports lie.

Not claimed: that an honest prover's witness meets these premises; anything on what a verifier
accepts; any property of the protocol.

-/
import Johnson.Goal.HonestTrace.ConstrAtTrace
import Johnson.Desc.K6.Honest.Law.Back.PartsOfHeadOrd
import Johnson.Goal.Meaning.HeadCondScope

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
open VerifiableInference.Desc.Sound (MsgT Mem readAt SeatsNamed GroupsSeated)
open VerifiableInference.Desc.First (Numbers)
open Meaning (Follows)
open P5J (TPart TReq TS HidAt parts4 constrQAt hidAtSeat ownQ)
open Cb.Pv.Tail (Size)
open VerifiableInference.Desc.Kinds.Head.Law (headPartK6 partsAtX)

variable {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : Model.Verify.Public}
  {i : Cm.Idx} {x : Instance ppref}

section AtSeat
variable {P Tok : Type} {rows cols : ℕ} (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem)
  (N : Numbers) (s : ℕ → Size) (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ)
  (tokV : Tok → Fin ppref.V) (req : P × TS → TReq)
  (dec : P × TS → Strs → Option (Fin rows → Fin cols → GE)) (hSN : SeatsNamed arr N s seat)
  (hGS : GroupsSeated ms N)

/-- **The sentence at sub-proof 24 and the four parts of parts4.** Under the premises of
base_own_of_syms at the messages readAt cs arr ms N k w; hH: every table that dec a y yields holds
i; hW: it is the witness's own cells; hq: the request with the witness's token put in is x; hr0,
hc0: the table's rows and columns are at most the reference's; htab: tab is the library's EX below
2^16. dec': the decoder inside headPartK6's own H may be another than the outer one. By
parts_of_headOrd, at Hd.HeadOrdLB off MeetsAll X i x (theTrace X i x); six of its nine public
premises follow from the three premises on the files and from hq. -/
theorem constr_head (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (Sv : ServesAt X i x) (Fo : Follows X s)
    (hb : ∀ k < 25, (s k).beta = 2 ^ 17) (hr : ∀ k < 25, (s k).rad = 2 ^ 20)
    (put : TReq → Fin ppref.V → TReq) (a : P × TS) (y : Strs)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT)
    (hH : ∀ M, dec a y = some M → Holds M i) (hW : ∀ M, dec a y = some M → M = w.cells)
    (hq : (put (req a) (tokV w.tok)).val = x)
    (S : SymsOfTrace X s seat (fun k => readAt cs arr ms N k w) (theTrace X i x))
    (pl : ℕ → ℕ × Bool × ℕ × ℕ) (tab : ℕ → ℕ) (tokH : P × TS → Fin ppref.V)
    (dec' : P × TS → Strs → Option (Fin rows → Fin cols → GE))
    (hr0 : rows ≤ Inst.Model.Layout.hRef) (hc0 : cols ≤ 2 ^ Inst.Model.Layout.kRef)
    (htab : ∀ u, u < 2 ^ 16 → (tab u : Int) = Inst.Model.EX u)
    (digitsPart : ℕ → P × TS → Strs → Wit (Fin rows → Fin cols → GE) Tok MsgT → Prop)
    {p : TPart} (hp : p ∈ parts4) :
    constrQAt 24 put (hidAtSeat X cs arr ms N s seat tokV req dec hSN hGS)
      (headPartK6 cs arr ms N s seat X pl tab put
        (hidAtSeat X cs arr ms N s seat tokV req dec' hSN hGS) tokH)
      digitsPart 24 p a y w := by
  have C := base_own_of_syms hZ hR h Sv Fo hb hr S 24 (by omega)
  have M := meetsAll_theTrace hZ hR h Sv
  have A := Hd.core_of_scope hZ hR h
  have B := (Hd.eleven_of_core h A (Hd.npOf X.hS)).1
  have Bd := Hd.borderH_of_layout B.lay B.switches B.sized B.sized2
  have NH := Hd.numH_of_layout B.full B.head
  have h3 : Inst.Model.Head3 x := hq ▸ Meaning.head3_of_req (put (req a) (tokV w.tok))
  have hpd : p ≠ .lookDigits := by
    rintro rfl
    exact absurd hp (by decide)
  have hph : p ≠ .lookCallsHeard := by
    rintro rfl
    exact absurd hp (by decide)
  have e24 : ownQ cs arr ms N s seat w 24 = theTrace X i x 24 := by
    unfold ownQ
    exact C.2
  unfold constrQAt
  rw [if_neg hpd]
  refine ⟨fun _ => C.1, fun M' i' hM hi' => ?_⟩
  obtain rfl : i' = i := VerifiableInference.Meaning.holds_unique hi' (hH M' hM)
  rw [if_pos rfl, VerifiableInference.Desc.Kinds.Head.Law.Came.headPartK6_at cs arr ms N s seat X
    pl tab put _ tokH p hph]
  show partsAtX cs arr ms N s seat X pl tab i' (put (req a) (tokV w.tok)).val w p
  rw [hq]
  exact VerifiableInference.Desc.Kinds.Head.Law.Came.parts_of_headOrd cs arr ms N s seat X pl hr0
    hc0 tab i' x w B.full NH Bd B.sh
    (VerifiableInference.Desc.Kinds.Head.Law.InScope.ok_in_scope hZ hR h _) h3 htab
    (hW M' hM ▸ hi') (e24 ▸ M.ords.head) p hp

end AtSeat

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.constr_head
