-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/LookMemberHead.lean: CONDITIONAL.

What is here. The hypothesis `K4LookLaid` (Law/ReadyHead.lean: what `AcceptedS` at the member of the
feed-forward layers' rounds still asks of what the lookup has heard) from either of two hypotheses,
`LookRestIx` and `LookRestAt` (each the conclusion of a statement of the writers of Honest/K3/); and
two public facts on the member that stands right in front, shown under h : AtMgA, by which
`LookRestAt` gives `LookRestIx`. Definitions of two hypotheses' forms, and statements with their
proofs. Words: Law/ElevenHead.lean's head; the seat: `seatS`, the readers of the verifier's state
that the sub-protocol's decision calls; on the calls: of a segment's two lookups the one on the
calls' keys, not the one on the digits.

Not shown here. `LookRestIx` AND `LookRestAt` ARE HYPOTHESES: each is THE CONCLUSION, WITHOUT ITS
PREMISES, of a statement of the writers of Honest/K3/, whose files are not imported here.
`LookRestIx bs j`: of `look_rest_link` (Johnson/Desc/ProofFile/Honest/K3/Law/Thread/AtLink.lean),
which stands under h and "l < 25" alone, at j in the stead of the library's `borderOf l false`
(Johnson/Desc/Sound/MgAt/K3Open.lean; at l = 2 g it is 28 g + 3: `border_calls`); THE CALL IS MADE
IN Law/LookJoin.lean, which imports their file: there `LookRestIx cF.blocksInOrder (28 g + 3)` stands under h
alone. `LookRestAt bs pc`: of `look_rest_at` (…/K3/Law/Thread/LookRest.lean), at pc in the stead of
their `lot.place`; that statement has four hypotheses more (beside an opening of the description,
which h gives), which are not said here, since their types are their own files': a site is in their
list of lookups; it is on the calls; a sub-protocol is in their lot's list at the ground; its place
is the site's; and that this place is `IM.k3Place (2 * g) false` is owed beside. That the top's
hypotheses can hold together: no example is known (by binder, beside h: `lookRestIx_of_at`: hg, hL ·
`k4LookLaid_head`: Lh, hL · `k4_accepted_rest`: Lh, hQ, half, hPl, hSh, hn, h2, hL, hTok, hf).
`lookMember_head` takes h and g < 12 alone, and of h alone: the side library AtFullSide proves, with
no hypothesis, that h has a member at one place (AtFullSide.Top.headMember_zFull,
AtFullSide/Top/HeadMemberAtFull.lean, whose own Limits say what it is worth). `Behind` and
`AcceptedS` speak only where the thread stands: that it stands at any run is not shown. NOT
COMPLETENESS. THE MEMBER's STEP TESTS NO SENT VALUE (Law/Hears.lean): it accepts every play of the
right shape, a false one too. THE FULL SIZE ALONE, and at `OnBytes.secondHashFunction`, the format's second
hash function, alone. A LAW, NOT A PART: no file that defines a part of the proof file's description
may import this one: its imports reach Johnson/Goal/. Transitive imports, by a program's walk
over import lines. Opening every module that it reaches: 163 modules under Johnson/Goal/, 53 whose
name holds RecCompile, 140 under ThirdParty/. Stopping unopened at Johnson/Goal/, Johnson/D/ and
ThirdParty/ (so these are floors): 70 under Johnson/Goal/, 46 whose name holds RecCompile, 2 under
ThirdParty/. By both: none under Johnson/D/; none of RecCompile's Honest*, Both or PassH*.
No property is claimed.

  `LookRestAt bs pc`, `LookRestIx bs j`   the two hypotheses.
  `look_lay`   where the seat reads what the lookup returned, a layers' segment is open and holds
      it.
  `k4LookLaid_of_ix`, `k4LookLaid_of_rest`   K4LookLaid at the member number j, from either. General
      in the list.
  `lookMember_head`   **under h, at each group g below 12: a member number 28 g + 3 of the chain is
      there, stands at the library's address of the lookup on the calls of segment 2 g, and passes
      its test on the plan.**
  `border_calls`   the library's `borderOf (2 * g) false` is 28 g + 3.
  `lookRestIx_of_at`   so, under h, the hypothesis at that address gives the one at that number.
  `k4LookLaid_head`   K4LookLaid in the form in which `k4_accepted_all` asks it.
  `k4_accepted_rest`   **`AcceptedS` at the member**, with `LookRestIx` in `K4LookLaid`'s stead.

-/
import Johnson.Desc.ProofFile.Honest.K4.Law.ElevenHead
import Johnson.IMR.K3Seat
import Johnson.IMR.FlatScope
import Johnson.IMR.PlanOkFlat
import Johnson.Desc.Sound.MgAt.K3Open

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4 (Par seatS)
open OnBytes.Desc.First.K4.Honest (K4Pub)
open OnBytes.Desc.First.K4.Rt (k4Takes)
open OnBytes.Desc.First.K4.RtPub (tokensFit)
open OnBytes.Road.K4 (AtK4 parOf)
open OnBytes.Road.K4.More (PS)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Place Chain Strs Claim Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT linksFull)
open Johnson.Desc.First.Walk.Tied (StepYes)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)
open ProofFile.Honest.K4.SeatedHead (LaidK4)

/-- **Behind an accepting step of a member that stands at the place pc and passes its test on the
plan: the calls' points end as the lookup's own, and the lookup's weights are as many as its shape's
calls.** The conclusion of `look_rest_at`, without its hypotheses. This defines a hypothesis; the
definition claims nothing. -/
def LookRestAt (bs : List (Block S Claim)) (pc : Place) : Prop :=
  ∀ blk ∈ bs, blk.place = pc → blk.planOk = true →
    ∀ (ft : Nat) (s₀ s' : S), StepYes ft blk s₀ s' →
      ∀ a fo, s'.here = .lay a → a.fo = some fo →
        (∀ k Zl, (lastOf fo.zx k).toOption = some Zl →
          ∃ ends, (fo.zk.mapM fun zk => (lastOf zk k).toOption) = some ends ∧
            ends.all (· == Zl) = true) ∧
        fo.e.size = fo.shape.NC

/-- **The same behind an accepting step of the member number j.** The conclusion of `look_rest_link`
(Johnson/Desc/ProofFile/Honest/K3/Law/Thread/AtLink.lean, by the writers of Honest/K3/; not imported
here), at j in the stead of the library's `borderOf l false`. This defines a hypothesis; the
definition claims nothing. -/
def LookRestIx (bs : List (Block S Claim)) (j : Nat) : Prop :=
  ∀ blk, bs[j]? = some blk →
    ∀ (ft : Nat) (s₀ s' : S), StepYes ft blk s₀ s' →
      ∀ a fo, s'.here = .lay a → a.fo = some fo →
        (∀ k Zl, (lastOf fo.zx k).toOption = some Zl →
          ∃ ends, (fo.zk.mapM fun zk => (lastOf zk k).toOption) = some ends ∧
            ends.all (· == Zl) = true) ∧
        fo.e.size = fo.shape.NC

/-- Where the seat reads what the lookup returned, a layers' segment is open and holds it. -/
theorem look_lay {s : S} {fo : Forest.Heard} (h : seatS.look s = some fo) :
    ∃ a, s.here = .lay a ∧ a.fo = some fo := by
  obtain ⟨st, book, roots, ro, failed, check, out, here, req⟩ := s
  cases here with
  | lay a => exact ⟨a, rfl, h⟩
  | between => cases h
  | att _ => cases h
  | head _ => cases h
  | fin _ => cases h
  | mem _ => cases h

/-- **`K4LookLaid` at the member number j**, from the hypothesis at that number. -/
theorem k4LookLaid_of_ix {P : Type} {bs : List (Block S Claim)} {st : P → S} {j : Nat} {par : Par}
    (hL : LookRestIx bs j) : K4LookLaid bs st j par := by
  intro blk hblk z s₀ s _ hy fo hlk
  obtain ⟨a, ha, hfo⟩ := look_lay hlk
  obtain ⟨h1, h2⟩ := hL blk hblk 0 s₀ s hy a fo ha hfo
  exact ⟨fun Zl hZ => h1 _ Zl hZ, h2⟩

/-- CONDITIONAL: on hL and hm. **`K4LookLaid` at the member number j**, where that member stands at
pc and passes its test on the plan. -/
theorem k4LookLaid_of_rest {P : Type} {bs : List (Block S Claim)} {st : P → S} {j : Nat}
    {pc : Place} {par : Par} (hL : LookRestAt bs pc)
    (hm : ∀ blk, bs[j]? = some blk → blk.place = pc ∧ blk.planOk = true) :
    K4LookLaid bs st j par :=
  k4LookLaid_of_ix fun blk hblk =>
    hL blk (List.mem_of_getElem? hblk) (hm blk hblk).1 (hm blk hblk).2

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- **THE MEMBER RIGHT IN FRONT, UNDER h**: its place and its test on the plan. -/
theorem lookMember_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {g : ℕ} (hg : g < 12) :
    ∃ blk, cF.blocksInOrder[28 * g + 3]? = some blk ∧
      blk.place = IM.k3Place (2 * g) false ∧ blk.planOk = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨Lk, b, b', e1, e2, _, e4⟩ := IM.k3_of h.scope h.reads O (2 * g) (by omega) false
  have hix : IM.k3Ix (2 * g) false = 1 := by
    show (if false = true then 6 else 1) + (if 2 * g = 24 then 1 else 0) = 1
    rw [if_neg (by omega : ¬ 2 * g = 24)]
    rfl
  rw [hix] at e2
  have hi : IM.flatIx cF (2 * g) 1 = 28 * g + 3 := by
    rw [IM.flatIx_scope h.scope h.reads O (by omega) 1]
    omega
  have hf : cF.blocksInOrder[28 * g + 3]? = some b := by
    rw [← hi]
    exact IM.hear_at_flat e1 e2
  have ok := IM.blocksOk_of_planOk O h.laid.planOk
  unfold VerifiableInference.Desc.blocksOk at ok
  have h1 := List.all_eq_true.1 ok b (List.mem_of_getElem? hf)
  exact ⟨b, hf, IM.alone_place e4, ((Bool.and_eq_true _ _).mp h1).1⟩

/-- The library's number of the border in front of the lookup on the calls of segment 2 g. -/
theorem border_calls {g : ℕ} (hg : g < 12) :
    VerifiableInference.Desc.Sound.MgAt.borderOf (2 * g) false = 28 * g + 3 := by
  show 14 * (2 * g) + ((if false = true then 6 else 1) + (if 2 * g = 24 then 1 else 0)) + 2 =
    28 * g + 3
  rw [if_neg (by omega : ¬ 2 * g = 24), if_neg (by decide : ¬ false = true)]
  omega

/-- **Under h the hypothesis at the place gives the one at the number.** -/
theorem lookRestIx_of_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {g : ℕ} (hg : g < 12)
    (hL : LookRestAt cF.blocksInOrder (IM.k3Place (2 * g) false)) : LookRestIx cF.blocksInOrder (28 * g + 3) := by
  obtain ⟨b, hb, hp, hk⟩ := lookMember_head h hg
  intro blk hblk
  obtain rfl : b = blk := Option.some.inj (hb.symm.trans hblk)
  exact hL b (List.mem_of_getElem? hb) hp hk

/-- **`K4LookLaid`, in the form in which `k4_accepted_all` asks it.** -/
theorem k4LookLaid_head {k m g : ℕ} {x : Bool × Par} {blk : Block TS ProofFile.Cl}
    (Lh : LaidK4 Zp cF k m g x blk) (hL : LookRestIx cF.blocksInOrder (28 * g + 3)) :
    ∀ j q, k = j + 1 → PS[j]? = some q → q.link = some m → q.piece = 2 →
      K4LookLaid cF.blocksInOrder (ProofFile.startS Zp) j (parOf x) := by
  intro j q hk _ _ _
  have e : j = 28 * g + 3 := by
    have := Lh.num
    omega
  subst e
  exact k4LookLaid_of_ix hL

variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **`AcceptedS` AT THE MEMBER**, with `LookRestIx` as the one hypothesis on what the lookup has
heard. CONDITIONAL: as `k4_accepted_all` (Law/ElevenHead.lean). -/
theorem k4_accepted_rest (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X' → Prop)
    {k m g : ℕ} {x : Bool × Par} {blk : Block TS ProofFile.Cl} (Lh : LaidK4 Zp cF k m g x blk)
    {cells : Tr → Cells}
    {weights : W₀ → Weights} {tokens : ProofFile.Inst → Array Nat}
    {look : K4Pub → List Fmt.Drawn → Forest.Heard} {Qp : K4Pub}
    {fall : Nat → S → List Fmt.Drawn → Option String} (hQ : k4PubOf Zp x.2 = some Qp)
    (half : H.first.find? (fun z => z.place == IM.k4Place g) =
      some (k4Half cells weights tokens look Qp))
    (hPl : k4PlanB (parOf x) = true) (hSh : k4ShapeB (parOf x) = true)
    (hn : Forest.elems (P5J.At.X Zp).y.fo + k4Takes (parOf x).P (parOf x).hp (parOf x).g ≤
      (parOf x).hp.ns)
    (h2 : (parOf x).P.y.h.lt ≤ (parOf x).P.y.fo.dT)
    (hL : LookRestIx cF.blocksInOrder (28 * g + 3))
    (hTok : g = 0 → ∀ c s mm E,
      ThrS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said k c s mm E →
      tokensFit { (parOf x).P with tokv := seatS.tokv s } (parOf x).g = true)
    (hf : ∀ s ds, fall k s ds = none → k4CoinZero Qp ds = none) :
    AcceptedS (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread Said fall k :=
  k4_accepted_all h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w Said Lh hQ half hPl hSh hn h2
    (k4LookLaid_head Lh hL) hTok hf

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.look_lay
#print axioms ProofFile.Honest.K4.k4LookLaid_of_ix
#print axioms ProofFile.Honest.K4.k4LookLaid_of_rest
#print axioms ProofFile.Honest.K4.lookMember_head
#print axioms ProofFile.Honest.K4.border_calls
#print axioms ProofFile.Honest.K4.lookRestIx_of_at
#print axioms ProofFile.Honest.K4.k4LookLaid_head
#print axioms ProofFile.Honest.K4.k4_accepted_rest
