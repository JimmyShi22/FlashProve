-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/ShapeAtM3.lean: kind K13, the members' batching: THE ACCEPTANCE OF
THE KIND's MEMBER BY THE CUT "STRUCTURE | VALUES" (Honest/Thread/Shape.lean): `Carries`, `Returns`
and `Values` at the member, for a chain's shape that HOLDS THE KIND's OWN SHAPE THROUGH A LENS and
whose guards at the member are the kind's one test and one update (`gK`,
Johnson/Desc/K13/Honest/ShapeAll.lean); and so `Accepted` (Honest/Thread/Pays.lean) under the named
premise `Shape.yes`. Definitions of the premises, and statements with their proofs. The words
thread, member and fall are explained in the head of Honest/Thread/Thr.lean; structure, values and
shape in that of Honest/Thread/Shape.lean.

The premises.
  `MemberIs`: the member has the kind's rounds; it returns, from a state without a mark of failure,
    wherever the kind's own sub-protocol (`atM3 P`) does; and only there. At the IOP's own member:
    `memberIs_open`, by the law on the member at a lot's place (Honest/Member/Uses.lean).
  `HoldsK`: of the chain's shape Z, with get and put: (reads) get of a state's shape is the kind's
    shape of the state; (fills) Z's guards at the member are `gK` under the lens; (lays) the kind's
    sub-protocol turns nothing of a state's shape but what the kind's shape holds; (vals) the member
    has no named test on a value. (reads) and (lays) are statements on the chain's projection Z.sh;
    (fills) and (vals) say how Z's two fields g and vals are filled at the member.
  `Carries` AT EVERY OTHER MEMBER, `Shape.yes`, and that the chain's first state has the first
    shape: premises of `accepted_of_shape`, on other members and on the whole run of the shape.
Main names:
  `k13_Carries`, `k13_Returns`, `k13_Values`: **the three at the member.**
  `k13_FitsAt`: what was played passes the step's own tests: `fitsAt_half` at the kind's half.
  `k13_Accepted_shape`: **the member is accepted**, at every `fall`.
  `memberIs_open`: the first premise at the IOP's own member.

What is not claimed. That a CHAIN's shape with such a lens can be had: the one instance
(HoldsKInstance.lean; Instances.lean) is at the kind's own shape and a thread of one member. That
`Shape.yes` holds at a chain of the protocol. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.Thread.ShapeRow
import Johnson.Desc.ProofFile.Honest.K13.AtThread
import Johnson.Desc.ProofFile.Honest.K13.AtMember
import Johnson.Desc.K13.Honest.ShapeAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open OnBytes
open VerifiableInference.Desc (Block Chain FileDescription noDigest step_iff)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13 (Where battRounds atM3 whereOf)
open VerifiableInference.Desc.K13.Honest (ShK shK gK gK_step gK_ready gK_returns)

variable {Cl : Type}

/-- **The member against the kind's own sub-protocol.** -/
structure MemberIs (bs : List (Block S Cl)) (b : Nat) (P : Where) (Cl' : Type) : Prop where
  rounds : ∀ blk, bs[b]? = some blk → blk.rounds = battRounds P
  forth : ∀ blk, bs[b]? = some blk → ∀ s rs gs t', s.failed = none →
    (atM3 (Cl := Cl') P).decide s rs gs = .ok t' → blk.decide s rs gs = .ok t'
  back : ∀ blk, bs[b]? = some blk → ∀ s rs gs t', blk.decide s rs gs = .ok t' →
    (atM3 (Cl := Cl') P).decide s rs gs = .ok t'

/-- **The chain's shape holds the kind's own through a lens, and its guards at the member are the
kind's.** -/
structure HoldsK (Z : Shape S) (b : Nat) (P : Where) (Cl' : Type) (get : Z.Sh → ShK)
    (put : Z.Sh → ShK → Z.Sh) : Prop where
  reads : ∀ s, get (Z.sh s) = shK s
  fills : ∀ a, Z.g b a = (gK P (get a)).map (put a)
  lays : ∀ s s' rs gs, (atM3 (Cl := Cl') P).decide s rs gs = .ok s' →
    Z.sh s' = put (Z.sh s) (shK s')
  vals : ∀ s rs gs, Z.vals b s rs gs = true

variable {bs : List (Block S Cl)} {ft b : Nat} {P : Where} {Cl' : Type} {Z : Shape S}
  {get : Z.Sh → ShK} {put : Z.Sh → ShK → Z.Sh}

/-- What a return of the chain's guards at the member says. -/
theorem holdsK_ok (hZ : HoldsK Z b P Cl' get put) {s : S} {t : Z.Sh}
    (h : Z.g b (Z.sh s) = .ok t) : ∃ k, gK P (shK s) = .ok k ∧ t = put (Z.sh s) k := by
  rw [hZ.fills, hZ.reads] at h
  cases hk : gK P (shK s) with
  | error e =>
    rw [hk] at h
    cases h
  | ok k =>
    rw [hk] at h
    exact ⟨k, rfl, (Except.ok.inj h).symm⟩

/-- **(B1) at the member.** -/
theorem k13_Carries (hM : MemberIs bs b P Cl') (hZ : HoldsK Z b P Cl' get put) :
    Carries bs ft Z b := by
  intro blk hb s rs cols s' n t hst hg
  obtain ⟨-, hdec, -⟩ := (step_iff ft blk s s' rs cols n).1 hst
  have ha := hM.back blk hb _ _ _ _ hdec
  obtain ⟨k, hk, rfl⟩ := holdsK_ok hZ hg
  have e := gK_step ha (gK_ready hk).2.1
  obtain rfl : k = shK s' := Except.ok.inj (hk.symm.trans e)
  exact (hZ.lays _ _ _ _ ha).symm

/-- **(B2) at the member.** -/
theorem k13_Returns (hM : MemberIs bs b P Cl') (hZ : HoldsK Z b P Cl' get put) :
    Returns bs ft Z b := by
  intro blk hb s rs cols t hg hfit _
  obtain ⟨k, hk, -⟩ := holdsK_ok hZ hg
  have hr := hfit.1
  rw [hM.rounds blk hb] at hr
  obtain ⟨s', hs'⟩ := gK_returns (Cl := Cl') hk rs hr (blk.shown ft rs cols)
  exact ⟨s', hM.forth blk hb _ _ _ _ (gK_ready hk).2.1 hs'⟩

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb}
  {weights : W₀ → Weights} {pile : PileOf Xi}

/-- **The values at the member**: it has no named test on a value. -/
theorem k13_Values (hZ : HoldsK Z b P Cl' get put)
    (fall : Nat → S → List Fmt.Drawn → Option String) : Values T Z fall b :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => hZ.vals _ _ _

/-- What was played and read passes the step's own tests on rounds and columns. -/
theorem k13_FitsAt (h : AtK13 T b weights pile P) {blk : Block S Cl} (hb : T.bs[b]? = some blk) :
    FitsAt T b :=
  fitsAt_half T hb (h.half blk hb)
    (by rw [k13Half_rounds, h.rounds blk hb, battRounds_length])
    (by rw [h.oracles blk hb, h.rounds blk hb, battRounds_length, List.length_replicate])

/-- **THE MEMBER IS ACCEPTED**, at every `fall`, under the named premise that the shape's run
returns. -/
theorem k13_Accepted_shape (h : AtK13 T b weights pile P) (hM : MemberIs T.bs b P Cl')
    (hZ : HoldsK Z b P Cl' get put) {a₀ : Z.Sh} {n : Nat} (hn : n ≤ T.bs.length) (hb : b < n)
    (hyes : Z.yes a₀ n = true)
    (hfirst : ∀ k w hd s₀, T.valid w → T.begun k w hd s₀ → Z.sh s₀ = a₀)
    (hC : ∀ j, j ≠ b → Carries T.bs T.ft Z j)
    (fall : Nat → S → List Fmt.Drawn → Option String) : Accepted T fall b := by
  obtain ⟨blk, hblk⟩ : ∃ blk, T.bs[b]? = some blk :=
    ⟨T.bs[b]'(Nat.lt_of_lt_of_le hb hn), List.getElem?_eq_getElem _⟩
  refine accepted_of_shape T Z hn hb hyes hfirst (fun j => ?_) (k13_Returns hM hZ)
    (k13_FitsAt h hblk) (k13_Values hZ fall)
  by_cases hj : j = b
  · rw [hj]
    exact k13_Carries hM hZ
  · exact hC j hj

section
open ProofFile.Honest.AtPlace (k13_m3_decides k13_at_m3)

variable {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription Inst} {Zp : Pub} {Bs : PureBase}
  {base : List (Block S ProofFile.Cl)} {c₁ : Chain S ProofFile.Cl} {A : SharedSeat} {B : SecondSeat}

/-- **The first premise at the IOP's own member**: where the member number b of the first chain's
flat list stands at the kind's place. -/
theorem memberIs_open (O : IM.Open o pol lay KL F Zp Bs base c₁ A B) {b : Nat}
    (hp : ∀ blk, c₁.blocksInOrder[b]? = some blk → blk.place = ⟨1, none, 3, .K13⟩) :
    MemberIs c₁.blocksInOrder b (whereOf Zp) Unit where
  rounds := fun blk hb => (k13_member_fields O (List.mem_of_getElem? hb) (hp blk hb)).1
  forth := fun blk hb s rs gs t' h0 h =>
    k13_at_m3 o pol lay KL F Zp Bs base c₁ A B O blk (List.mem_of_getElem? hb) (hp blk hb) s t' rs
      gs h0 h
  back := fun blk hb s rs gs t' h =>
    ((k13_m3_decides O (List.mem_of_getElem? hb) (hp blk hb) s t' rs gs).1 h).1

end

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.holdsK_ok
#print axioms ProofFile.Honest.K13.k13_Carries
#print axioms ProofFile.Honest.K13.k13_Returns
#print axioms ProofFile.Honest.K13.k13_Values
#print axioms ProofFile.Honest.K13.k13_FitsAt
#print axioms ProofFile.Honest.K13.k13_Accepted_shape
#print axioms ProofFile.Honest.K13.memberIs_open
