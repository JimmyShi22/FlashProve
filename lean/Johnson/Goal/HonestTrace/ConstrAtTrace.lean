-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/HonestTrace/ConstrAtTrace.lean

The library's sentence "constrQAt" (Johnson/P5J/MeansQ.lean) at the library's own way of reading a
witness, hidAtSeat, for public files in the goals' scope and a served request: from one condition on
the symbols that the witness's messages hold at the seats and, for the layers, two on the decoder
and the request.
This file states no goal.

The three premises on the files: Z is in the goals' scope (VerifierAndGoals.InScope Z = true); the goals'
reader returns pp at Z (VerifierAndGoals.readFiles Z = .ok pp); publicOf returns X at Z's parameter file and
scale file.

Main definitions and theorems:
* "SymsOfTrace X s seat msgF T": at each of the 25 sub-proofs the symbols at the seats "seat", read
  in the messages msgF k, are the symbols of the library's packing msgOf s T at the seats seatBy
  seat0 (msgOf, seat0: Johnson/Goal/Meaning/HidPack.lean; seatBy:
  Johnson/Goal/Meaning/HidPlan.lean).
* "base_own_of_syms": under the three premises, at a served request, for sizes s that follow X's
  plans with the shift 2^17 and the radix 2^20, under SymsOfTrace at theTrace X i x: at each k < 25
  the symbols are a packing of small integers (Base), and the list that ownOf reads back from them
  is theTrace X i x k.
* "ownSame_theTrace": under the three premises, at a served request, for sizes that follow X's
  plans: Meaning.OwnSame X s (theTrace X i x) k for k < 25.
* "tiesAt_hidAtSeat": under the premises of base_own_of_syms, SymsOfTrace among them, if every table
  that dec a y yields holds i, and the request with the witness's token put in is x: ConstrTies
  (Johnson/HonestTrace/ConstrAtLists.lean) at hidAtSeat and theTrace X i x.
* "constr_head_small": under the premises of base_own_of_syms: the sentence at sub-proof 24 and the
  part small, with headPartK6 (Johnson/Desc/Kinds/Law/HeadCutsK6.lean) at any H' for headPart.

Limits. These are conditional lemmas. SymsOfTrace is a premise: no theorem of this file shows it of
any seats and messages (at seatBy seat0 and the messages msgOf s T it holds by its text).
base_own_of_syms rewrites with that premise and then calls packs_in_scope
(Johnson/Goal/HonestTrace/FullInScope.lean). Of sub-proof 24 the part small alone is treated:
nothing is said of the head's parts idn, lookCalls and rider. Nothing on the parts lookDigits and
lookCallsHeard. All is at the full size: 12 groups, 25 sub-proofs. No theorem of this file shows
that some Z meets the three premises together.

Not claimed: anything on a prover, on what a verifier accepts, or on a property of the protocol.

-/
import Johnson.HonestTrace.ConstrAtLists
import Johnson.P5J.CellQ
import Johnson.Goal.Meaning.NextToken
import Johnson.Goal.Meaning.HidPack
import Johnson.Goal.Meaning.HidBase
import Johnson.Desc.Kinds.Law.HeadCutsK6
import Johnson.Goal.HonestTrace.FullPlanesInScope

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
open Meaning (Hid hidOf mgOf maOf ownOf symAt Msgs msgOf seat0 seatBy Follows)
open P5J (TPart TReq TS HidAt partG partA parts4 constrQAt hidAtSeat ownQ)
open Cb.Pv.Tail (Size Base)

variable {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} {lay : Option ByteArray} {X : Model.Verify.Public}
  {i : Cm.Idx} {x : Instance ppref} {T : Tr}

/-! ## From the symbols at the seats -/

/-- **The condition on the witness's messages.** msgF k: the messages as sub-proof k reads them. For
each k < 25 the symbols at the seats seat k, read in msgF k, are the symbols of the library's
packing msgOf s T at the seats seatBy seat0: entry (μ, i', c) is the image of row i' of the packing
of column c of the matrix that owns the entry's label, at the owner's radix and rows. Rows and
columns run inside the sizes s k, by the type of symAt. -/
def SymsOfTrace (X : Model.Verify.Public) (s : ℕ → Size)
    (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ) (msgF : ℕ → Msgs) (T : Tr) : Prop :=
  ∀ k < 25, symAt (s k) (seat k) (msgF k) = symAt (s k) (seatBy seat0 X s k) (msgOf s T)

/-- Under the three premises on the files, at a served request, for sizes s that follow X's plans
with the shift 2^17 and the radix 2^20: if the symbols at (seat, msgF) are those of the packing of
theTrace X i x (SymsOfTrace), then at each k < 25 they are a packing of small integers (Base), and
ownOf reads back from them the whole list theTrace X i x k. By packs_in_scope, after rewriting with
the premise: Base and ownOf read of seats and messages the symbols alone. -/
theorem base_own_of_syms (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (Sv : ServesAt X i x) {s : ℕ → Size} (Fo : Follows X s)
    (hb : ∀ k < 25, (s k).beta = 2 ^ 17) (hr : ∀ k < 25, (s k).rad = 2 ^ 20)
    {seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ} {msgF : ℕ → Msgs}
    (S : SymsOfTrace X s seat msgF (theTrace X i x)) :
    ∀ k < 25, Base (symAt (s k) (seat k) (msgF k)) ∧
      (ownOf s fun k => symAt (s k) (seat k) (msgF k)) k = theTrace X i x k := by
  intro k hk
  have Pk := packs_in_scope hZ hR h (pl := plOf X i x)
    (fun k r c => planesOf_01 X x i.mat _ k r c) Sv Fo hb hr k hk
  have e := S k hk
  refine ⟨?_, ?_⟩
  · rw [e]
    exact Pk.1
  · show mzTot (Rows.mzAt (symAt (s k) (seat k) (msgF k))) = _
    rw [e]
    exact Pk.2

/-- Under the three premises on the files, at a served request, for sizes s that follow X's plans:
OwnSame X s (theTrace X i x) k for k < 25 (Johnson/Goal/Meaning/HidPack.lean): at every entry of
sub-proof k's list the owner that the entry's label names has the same radix, the same rows and,
inside the entry's sizes, the same integers. It is a step of the proof of packs_in_scope, stated by
itself. -/
theorem ownSame_theTrace (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (Sv : ServesAt X i x) {s : ℕ → Size} (Fo : Follows X s)
    {k : ℕ} (hk : k < 25) : Meaning.OwnSame X s (theTrace X i x) k := by
  have C := Hd.core_of_scope hZ hR h
  obtain ⟨w, Mh, -, M, -, -⟩ :=
    Meaning.trace_of_true hZ hR h i x ((servesAt_iff_in_scope hZ hR h i x).1 Sv)
  have O0 := Meaning.ownSame_seenC h C Fo M hk
  obtain ⟨b1, b2, b3⟩ := borrowed_core h C (plOf X i x) i x
  refine ⟨O0.rad, O0.m, fun a ha r _ c _ => ?_⟩
  have ha' : a < (Meaning.matsAt X k).size := by
    rw [← Fo.NM k hk]
    exact ha
  rcases Meaning.owner_cases h C hk ha' with ⟨o1, o2⟩ | ⟨g, h0, hg, rfl, rfl, o1, o2⟩ |
    ⟨g, hg, rfl, rfl, o1, o2⟩ | ⟨rfl, rfl, o1, o2⟩
  · rw [o1, o2]
  · rw [o1, o2]
    exact (b1 g h0 hg r c).symm
  · rw [o1, o2]
    exact (b2 g hg r c).symm
  · rw [o1, o2]
    exact (b3 r c).symm

section AtSeat
variable {P Tok : Type} {rows cols : ℕ} (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem)
  (N : Numbers) (s : ℕ → Size) (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ)
  (tokV : Tok → Fin ppref.V) (req : P × TS → TReq)
  (dec : P × TS → Strs → Option (Fin rows → Fin cols → GE)) (hSN : SeatsNamed arr N s seat)
  (hGS : GroupsSeated ms N)

/-- **The five conditions at the library's own way of reading a witness** (hidAtSeat,
Johnson/P5J/MeansQ.lean). Under the premises of base_own_of_syms at the messages readAt cs arr ms N
k w: if every table that dec a y yields holds i (hH), and the request with the witness's token put
in is x (hq): ConstrTies at hidAtSeat, a, y, w, i, x and theTrace X i x. The field "one" is by
holds_unique (Johnson/Goal/Meaning/NextToken.lean). -/
theorem tiesAt_hidAtSeat (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (Sv : ServesAt X i x) (Fo : Follows X s)
    (hb : ∀ k < 25, (s k).beta = 2 ^ 17) (hr : ∀ k < 25, (s k).rad = 2 ^ 20)
    (put : TReq → Fin ppref.V → TReq) (a : P × TS) (y : Strs)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT)
    (hH : ∀ M, dec a y = some M → Holds M i)
    (hq : (put (req a) (tokV w.tok)).val = x)
    (S : SymsOfTrace X s seat (fun k => readAt cs arr ms N k w) (theTrace X i x)) :
    ConstrTies put (hidAtSeat X cs arr ms N s seat tokV req dec hSN hGS) a y w i x
      (theTrace X i x) := by
  have C := base_own_of_syms hZ hR h Sv Fo hb hr S
  have M := meetsAll_theTrace hZ hR h Sv
  refine ⟨fun M' i' hM hi' => VerifiableInference.Meaning.holds_unique hi' (hH M' hM), hq,
    fun g hg => ?_, fun g hg => ?_, fun k hk => (C k hk).1⟩
  · rw [← mgOf_trace M hg]
    show mgOf X.y _ g = _
    funext a'
    unfold mgOf
    rw [(C (2 * g) (by omega)).2, (C (2 * (g - 1)) (by omega)).2]
  · rw [← maOf_trace M hg]
    show maOf X _ g = _
    funext a'
    unfold maOf
    rw [(C (2 * g) (by omega)).2, (C (2 * g + 1) (by omega)).2]

open VerifiableInference.Desc.Kinds.Head.Law (headPartK6)

/-- **The sentence at sub-proof 24 and the part small**: under the premises of base_own_of_syms at
the messages readAt cs arr ms N k w: Base at sub-proof 24, and Hd.SmallH at the list that ownQ reads
there, which is theTrace X i x 24. H' is arbitrary: at the part small headPartK6 reads nothing of
it. -/
theorem constr_head_small (hZ : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (h : publicOf Z.pol Z.KL lay = .ok X) (Sv : ServesAt X i x) (Fo : Follows X s)
    (hb : ∀ k < 25, (s k).beta = 2 ^ 17) (hr : ∀ k < 25, (s k).rad = 2 ^ 20)
    (put : TReq → Fin ppref.V → TReq) (a : P × TS) (y : Strs)
    (w : Wit (Fin rows → Fin cols → GE) Tok MsgT)
    (S : SymsOfTrace X s seat (fun k => readAt cs arr ms N k w) (theTrace X i x))
    (pl : ℕ → ℕ × Bool × ℕ × ℕ) (tab : ℕ → ℕ) (tokH : P × TS → Fin ppref.V)
    (H' : HidAt X P (Wit (Fin rows → Fin cols → GE) Tok MsgT) rows cols)
    (digitsPart : ℕ → P × TS → Strs → Wit (Fin rows → Fin cols → GE) Tok MsgT → Prop) :
    constrQAt 24 put (hidAtSeat X cs arr ms N s seat tokV req dec hSN hGS)
      (headPartK6 cs arr ms N s seat X pl tab put H' tokH) digitsPart 24 .small a y w := by
  have C := base_own_of_syms hZ hR h Sv Fo hb hr S 24 (by omega)
  have M := meetsAll_theTrace hZ hR h Sv
  unfold constrQAt
  rw [if_neg (by decide)]
  refine ⟨fun _ => C.1, fun M' i' _ _ => ?_⟩
  rw [if_pos rfl]
  show Hd.SmallH X.hS X.HLy (borderOf X.y) (ownQ cs arr ms N s seat w 24)
  unfold ownQ
  rw [C.2]
  exact smallH_of_meetsAll M

end AtSeat

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.base_own_of_syms
#print axioms OnBytes.HonestTrace.ownSame_theTrace
#print axioms OnBytes.HonestTrace.tiesAt_hidAtSeat
#print axioms OnBytes.HonestTrace.constr_head_small
