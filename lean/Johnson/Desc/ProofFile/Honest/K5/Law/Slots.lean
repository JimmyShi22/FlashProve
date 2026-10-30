-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/Slots.lean: CONDITIONAL: WHAT LIES UNDER A SLOT of an attention
segment's own rounds (kind K5), at the member of a chain's thread at which the kind's honest side is
seated: in the world in which the items "the forms of a run are worth 0" are said behind the member,
the value under each slot that the member takes is the honest side's value of that number.
Statements with their proofs. EVERY STATEMENT IS CONDITIONAL, and all but mask_behind hang on the
ties (K5Script, Honest/K5/Law/Script.lean), WHICH ARE NOT SHOWN.

The letters. s, m: the verifier's state and the prover's stand in front of the member; att: the open
attention segment, so att.F.next is the first slot that the member takes; ds: the member's
challenges; y: the rounds as played; hd5, G: what the kind's hearing returns. D: any data whose mask
row is the witness's at a continuation dc of the challenges heard in front (MaskIs). The world is
worldOwn (behindPart s att G) [] D.

  MaskIs         D's mask row is the one that is read off the witness
  mask_part      the mask row's entry under scalar number i of part q is coin number i of the coins
                 that the book lends that part
  sum_slots      **a masked sumcheck that is part q**, at the coins cq that the book lends the
                 part: played alone at these, the part says its stretch of the rounds; under the
                 slots in front lie the part's lead values; under its own slots the coins spent for
                 the hiding polynomial; the mask entries under the end values' slots are the coins
                 spent for these; and, where the verifier's text for the sumcheck has heard the
                 stretch, under the end values' slots lie the summand's end values at the part's
                 challenges
  one_slots      **the round that sends scalars by themselves**: under its slots lie the values
  mask_behind    the data of the item's own sentence behind the member meet MaskIs

Who is meant to show the premises. K5Seated: whoever lays the halves and makes the seat. K5Script:
nobody yet. SumPut, LeadPut: laid_of_hear (Johnson/Desc/K5/Honest/Law/Numbers.lean), from the
hearing's return. The rest is in hand wherever a law on the member is asked.

Limits. Nothing is said on who sees what. No property is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.Coins
import Johnson.Desc.ProofFile.Honest.K5.Law.Under
import Johnson.Desc.ProofFile.Honest.K5.Law.Stretch
import Johnson.Desc.ProofFile.Honest.K5.Law.SumsTo
import Johnson.Desc.ProofFile.Honest.Thread.HeardLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes (E zeroE)
open OnBytes.Model (Reading Aff Fork)
open VerifiableInference.Desc (Block Claim OpenedColumn First.S noDigest)
open VerifiableInference.Desc.K9 (segAt?)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ MsgQ Stated dataQ worldOwn)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.Part.MaskedSum (Var Ends Call ownSlots scalars)
open VerifiableInference.Desc.First.Att.P (Par segAt_front)
open H2K5.Honest (PartShape shapes slotsTo LeadPut SumPut K5In)
open ProofFile.Honest.SumLaw

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {Z : Seat5} {p : Par} {blk : Block First.S Claim}
  {A : OnBytes.Attention.Plan} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}

/-- The open segment's part behind the member: the ledger G, and nothing owed. -/
abbrev behindPart (s : First.S) (att : VerifiableInference.Desc.First.AttOwn) (G : Fork) :
    VerifiableInference.Desc.K9.Part :=
  VerifiableInference.Desc.First.Att.P.partAt s att G none

/-- **D's mask row is the one that is read off the witness**, at the continuation dc of the
challenges heard in front of the member. It is a definition. -/
def MaskIs (T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb)
    (own : List (Nat × Nat)) (rdOf : T.Wt → Nat × Nat → MsgQ) (k : Coins Bk) (s : First.S)
    (att : VerifiableInference.Desc.First.AttOwn) (m : Mid (Local W₀ Rc Xi Tr) X)
    (dc : List Fmt.Drawn) (D : Bound GQ) : Prop :=
  D.mask = (dataQ own (VerifiableInference.Desc.First.Att.P.partAt s att att.F
    (VerifiableInference.Desc.K9.owedOf s)) (rdOf (T.wit k m.st.input (m.st.heard ++ dc)))).mask

section
variable (Hs : K5Seated T b cells Z p blk) (Sc : K5Script T b cells Z A blk own rdOf)
  {k : Coins Bk} {s : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env} {ds : List Fmt.Drawn}
  {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn} (hT : Thr T b k s m E)
  (hd : drawsFit blk.rounds ds = true) (hM : T.Moved blk k m E ds y cols)
  {att : VerifiableInference.Desc.First.AttOwn} (e : s.here = .att att) {dc : List Fmt.Drawn}
  {D : Bound GQ} (hD : MaskIs T own rdOf k s att m dc D)
include Hs Sc hT hM e hD

/-- **The mask row's entry under scalar number i of part q is coin number i of that part's.**
CONDITIONAL: on the ties; the half's seat; the thread in front; the prover's side of the step; sq is
part number q, and cq what the book lends it. -/
theorem mask_part {q : Nat} {sq : PartShape} (hq : (shapes Z.P.x)[q]? = some sq)
    {cq : (K5.partAt Z.place (chalOf Z) (jobs Z.P) (sq, q)).Coins}
    (hl : lendPart Bk (Bk.rowsOf T.chain) (k.look T.chain) ⟨Z.place, q⟩
      ((K5.partAt Z.place (chalOf Z) (jobs Z.P) (sq, q)).lift (V := Local W₀ Rc Xi Tr) (X := X)
        (fun _ => ()) (fun t : Local W₀ Rc Xi Tr => inOf Z.P.S Z.link (cells t.trace))
        (fun _ => ()) fun x _ => x) = .ok cq) {i : Nat} (hi : i < sq.scalars) :
    D.mask (att.F.next + slotsTo Z.P.x q + i) = Reading.gl.val
      ((runsE (K5.partAt Z.place (chalOf Z) (jobs Z.P) (sq, q)).spends cq.2.1).getD i zeroE) := by
  obtain ⟨⟨l, hst, -⟩, -⟩ := hM
  obtain ⟨c, hc, -⟩ := steps_one_half Hs.half hst
  rw [Hs.place] at hc
  obtain ⟨h1, h2⟩ := k5_spent cells Z hc hq hl hi
  have h3 := Sc.maskTie k s m E hT _ c (segAt_front e) hc dc _ h1
  rw [hD, ← h2, ← h3, Nat.add_assoc]
  rfl

include hd

/-- **A masked sumcheck that is part number q.** kq := ⟨ld, vs, some en⟩: the part's call; hq: it is
part q; SP: what lies in the ledger G behind the hearing (`SumPut`); cq: what the book lends the
part at the address (the place, q). CONDITIONAL: on the ties; the
half's seat; the thread in front; the challenges are such as the member's rounds can draw; the
prover's side of the step. -/
theorem sum_slots {q ld : Nat} {vs : List Var} {en : Ends}
    (hq : (shapes Z.P.x)[q]? = some (.sum ⟨ld, vs, some en⟩)) {G : Fork} {hhq : MaskedSum.Heard}
    (SP : SumPut ⟨ld, vs, some en⟩ (att.F.next + slotsTo Z.P.x q)
      ((roundsOf y.1).drop (H2K5.Honest.firstOf Z.P.x q)) hhq G)
    {cq : SumCoins (nameOf Z.place q "sum") (nameOf Z.place q "ends")
        (jobOf (X := Unit) ⟨ld, vs, some en⟩
          (fun w fr => (jobs Z.P).alone q w (chalOf Z fr.heard))
          fun w fr => (jobs Z.P).sum q w (chalOf Z fr.heard))}
    (hl : lendPart Bk (Bk.rowsOf T.chain) (k.look T.chain) ⟨Z.place, q⟩
      ((K5.partAt Z.place (chalOf Z) (jobs Z.P) (.sum ⟨ld, vs, some en⟩, q)).lift
        (V := Local W₀ Rc Xi Tr) (X := X) (fun _ => ())
        (fun t : Local W₀ Rc Xi Tr => inOf Z.P.S Z.link (cells t.trace))
        (fun _ => ()) fun x _ => x) = .ok cq) :
      alone (sumPart (V := Unit) (nameOf Z.place q "sum") (nameOf Z.place q "ends")
          (jobOf ⟨ld, vs, some en⟩ (fun w fr => (jobs Z.P).alone q w (chalOf Z fr.heard))
            fun w fr => (jobs Z.P).sum q w (chalOf Z fr.heard))) cq
          ⟨inOf Z.P.S Z.link (cells m.st.input.trace),
            m.st.heard ++ ds.take (H2K5.Honest.firstOf Z.P.x q), ()⟩
          (m.shown.plus ((roundsOf y.1).take (H2K5.Honest.firstOf Z.P.x q)))
          ((ds.drop (H2K5.Honest.firstOf Z.P.x q)).take (vs.length + 3)) =
        some (((roundsOf y.1).drop (H2K5.Honest.firstOf Z.P.x q)).take (vs.length + 3)) ∧
      (∀ i, i < ld → (worldOwn (behindPart s att G) [] D).slot
          (att.F.next + slotsTo Z.P.x q + i) =
        Reading.gl.val (((jobs Z.P).alone q (inOf Z.P.S Z.link (cells m.st.input.trace))
          (chalOf Z (m.st.heard ++ ds.take (H2K5.Honest.firstOf Z.P.x q)))).getD i zeroE)) ∧
      (∀ i, i < ownSlots (vs ++ [.point zeroE (en.dY + 1)]) →
        (worldOwn (behindPart s att G) [] D).slot (hhq.first + i) = hidingCoin cq i) ∧
      (∀ j, j < en.n → D.mask (hhq.sEnd + j) = Reading.gl.val ((endRun cq).getD j zeroE)) ∧
      ∀ (C : Aff) (F' G' : Fork),
        drawsOk ⟨ld, vs, some en⟩
          ((ds.drop (H2K5.Honest.firstOf Z.P.x q)).take (vs.length + 3)) = true →
        OnBytes.PscRun.Sized F' →
        MaskedSum.hear C ⟨ld, vs, some en⟩ F'
          (((roundsOf y.1).drop (H2K5.Honest.firstOf Z.P.x q)).take (vs.length + 3)) =
            some (hhq, G') →
        OnBytes.PscRun.Later G' G → ∀ j, j < en.n →
        (worldOwn (behindPart s att G) [] D).slot (hhq.sEnd + j) =
          Reading.gl.val ((((jobs Z.P).sum q (inOf Z.P.S Z.link (cells m.st.input.trace))
            (chalOf Z (m.st.heard ++ ds.take (H2K5.Honest.firstOf Z.P.x q)))).endsAt
              ((varsOf ⟨ld, vs, some en⟩
                ((ds.drop (H2K5.Honest.firstOf Z.P.x q)).take (vs.length + 3))).take
                  vs.length)).getD j zeroE) := by
  have hM' := hM
  obtain ⟨⟨l, hst, hy⟩, -⟩ := hM'
  obtain ⟨cq', hl', ha⟩ := k5_cut T Hs hd hst hy q _ hq
  obtain rfl : cq = cq' := Except.ok.inj (hl.symm.trans hl')
  have hmk := fun i hi => mask_part Hs Sc hT hM e hD hq hl (i := i) hi
  have hruns : runsE (K5.partAt Z.place (chalOf Z) (jobs Z.P)
      (.sum ⟨ld, vs, some en⟩, q)).spends cq.2.1 = firstRun cq ++ endRun cq := sum_runs rfl cq
  have hlen : (firstRun cq).length = ld + ownSlots (vs ++ [.point zeroE (en.dY + 1)]) :=
    coinsE_length _
  have hsc : (PartShape.sum ⟨ld, vs, some en⟩).scalars =
      ld + ownSlots (vs ++ [.point zeroE (en.dY + 1)]) + en.n := rfl
  have hfirst : ∀ i, i < ld + ownSlots (vs ++ [.point zeroE (en.dY + 1)]) →
      D.mask (att.F.next + slotsTo Z.P.x q + i) = Reading.gl.val ((firstRun cq).getD i zeroE) := by
    intro i hi
    rw [hmk i (by rw [hsc]; omega), hruns, List.getD_append _ _ _ _ (by rw [hlen]; exact hi)]
  have hends : ∀ j, j < en.n →
      D.mask (hhq.sEnd + j) = Reading.gl.val ((endRun cq).getD j zeroE) := by
    intro j hj
    have h1 := hmk (ld + ownSlots (vs ++ [.point zeroE (en.dY + 1)]) + j) (by rw [hsc]; omega)
    rw [hruns, List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen,
      Nat.add_sub_cancel_left] at h1
    rw [SP.sEnd, ← h1]
    congr 1
    show att.F.next + slotsTo Z.P.x q + ld + ownSlots (vs ++ [.point zeroE (en.dY + 1)]) + j =
      att.F.next + slotsTo Z.P.x q + (ld + ownSlots (vs ++ [.point zeroE (en.dY + 1)]) + j)
    omega
  refine ⟨ha, ?_, ?_, hends, ?_⟩
  · refine lead_under (V := Unit) ha ?_ (behindPart s att G) D SP.lead
      fun i hi => hfirst i (Nat.lt_of_lt_of_le hi (Nat.le_add_right _ _))
    cases (roundsOf y.1).drop (H2K5.Honest.firstOf Z.P.x q) <;> rfl
  · refine own_under cq (behindPart s att G) D SP fun i hi => ?_
    rw [SP.first, Nat.add_assoc]
    exact hfirst (ld + i) (Nat.add_lt_add_left hi ld)
  · intro C F' G' hdo hz' hhear hlat
    have ec := callAt_jobOf (X := Unit) ⟨ld, vs, some en⟩
      (fun w fr => (jobs Z.P).alone q w (chalOf Z fr.heard))
      (fun w fr => (jobs Z.P).sum q w (chalOf Z fr.heard))
      (inOf Z.P.S Z.link (cells m.st.input.trace))
      (frontOf (⟨inOf Z.P.S Z.link (cells m.st.input.trace),
        m.st.heard ++ ds.take (H2K5.Honest.firstOf Z.P.x q), ()⟩ : State K5In Unit)
        (m.shown.plus ((roundsOf y.1).take (H2K5.Honest.firstOf Z.P.x q))))
    have h := end_under (V := Unit) (e := en) rfl (by rw [ec]; exact hdo) ha hz'
      (by rw [ec]; exact hhear) (behindPart s att G) D hlat hends
    rw [ec] at h
    exact h

/-- **The round that sends scalars by themselves and is part number q.** CONDITIONAL: as
`sum_slots`; LP: what lies in the ledger G behind the hearing (`LeadPut`). The values are padded to
the round's number of scalars: where the list has that length the pad does nothing. -/
theorem one_slots {q n : Nat} (hq : (shapes Z.P.x)[q]? = some (.one (n + 1))) {G : Fork}
    (LP : LeadPut (n + 1) (att.F.next + slotsTo Z.P.x q)
      ((roundsOf y.1).drop (H2K5.Honest.firstOf Z.P.x q)) G) :
    ∀ i, i < n + 1 → (worldOwn (behindPart s att G) [] D).slot
        (att.F.next + slotsTo Z.P.x q + i) =
      Reading.gl.val ((padTo (n + 1) ((jobs Z.P).alone q
        (inOf Z.P.S Z.link (cells m.st.input.trace))
        (chalOf Z (m.st.heard ++ ds.take (H2K5.Honest.firstOf Z.P.x q))))).getD i zeroE) := by
  have hM' := hM
  obtain ⟨⟨l, hst, hy⟩, -⟩ := hM'
  obtain ⟨cq, hl, ha⟩ := k5_cut T Hs hd hst hy q _ hq
  have hmk := fun i hi => mask_part Hs Sc hT hM e hD hq hl (i := i) hi
  have ha' : alone (K5.partAt Z.place (chalOf Z) (jobs Z.P) (.one (n + 1), q)) cq
      ⟨inOf Z.P.S Z.link (cells m.st.input.trace),
        m.st.heard ++ ds.take (H2K5.Honest.firstOf Z.P.x q), ()⟩
      (m.shown.plus ((roundsOf y.1).take (H2K5.Honest.firstOf Z.P.x q)))
      ((ds.drop (H2K5.Honest.firstOf Z.P.x q)).take 1) =
        some (((roundsOf y.1).drop (H2K5.Honest.firstOf Z.P.x q)).take 1) := ha
  have hlen1 := alone_length _ _ _ _ _ _ ha'
  cases hdr : (ds.drop (H2K5.Honest.firstOf Z.P.x q)).take 1 with
  | nil =>
    rw [hdr] at ha'
    cases ha'
  | cons d tl =>
    have htl : tl = [] := by
      have h1 : (d :: tl).length ≤ 1 := by
        rw [← hdr]
        exact List.length_take_le 1 _
      cases tl with
      | nil => rfl
      | cons _ _ => exact absurd h1 (by simp)
    subst htl
    rw [hdr] at ha'
    have hst1 : some [rvSaid (scalarsSaid (n + 1)
        (fun w fr => (jobs Z.P).alone q w (chalOf Z fr.heard)) cq.2.1.1
        (m.shown.plus ((roundsOf y.1).take (H2K5.Honest.firstOf Z.P.x q)))
        ⟨inOf Z.P.S Z.link (cells m.st.input.trace),
          m.st.heard ++ ds.take (H2K5.Honest.firstOf Z.P.x q), ()⟩) d] =
        some (((roundsOf y.1).drop (H2K5.Honest.firstOf Z.P.x q)).take 1) := ha'
    have hhead : ((roundsOf y.1).drop (H2K5.Honest.firstOf Z.P.x q)).head? = some (rvSaid
        (scalarsSaid (n + 1) (fun w fr => (jobs Z.P).alone q w (chalOf Z fr.heard)) cq.2.1.1
        (m.shown.plus ((roundsOf y.1).take (H2K5.Honest.firstOf Z.P.x q)))
        ⟨inOf Z.P.S Z.link (cells m.st.input.trace),
          m.st.heard ++ ds.take (H2K5.Honest.firstOf Z.P.x q), ()⟩) d) := by
      have h2 := congrArg List.head? (Option.some.inj hst1)
      cases hl2 : (roundsOf y.1).drop (H2K5.Honest.firstOf Z.P.x q) with
      | nil =>
        rw [hl2] at h2
        cases h2
      | cons r0 _ =>
        rw [hl2] at h2
        exact h2.symm
    refine one_under hhead (scalars_rvSaid d _) (coins := coinsE cq.2.1.1) (fun i hi => ?_)
      (behindPart s att G) D LP fun i hi => ?_
    · have hsl := scalarsSaid_length (n + 1)
        (fun w fr => (jobs Z.P).alone q w (chalOf Z fr.heard)) cq.2.1.1
        (m.shown.plus ((roundsOf y.1).take (H2K5.Honest.firstOf Z.P.x q)))
        (⟨inOf Z.P.S Z.link (cells m.st.input.trace),
          m.st.heard ++ ds.take (H2K5.Honest.firstOf Z.P.x q), ()⟩ : State K5In Unit)
      rw [List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_eq_getElem (by rw [hsl]; exact hi), Option.map_some, Option.getD_some,
        canon_gl, ← List.getD_eq_getElem _ zeroE]
      exact addL_getD Reading.gl _ _ i
    · rw [hmk i hi]
      show Reading.gl.val ((coinsE cq.2.1.1 ++ []).getD i zeroE) = _
      rw [List.append_nil]

end

/-- **The data of the item's own sentence behind the member have the witness's mask row.** St: the
stated functions; s': the state behind; ds': a continuation of the challenges heard behind the
member. CONDITIONAL: hSt: the stated functions leave the mask row as it is (the field mask of
StatedAtt, Johnson/Desc/First/Att/K05WorldTieAt.lean; hSt_of_arm,
Johnson/Desc/First/Att/K05StatedArm.lean, shows that structure of the library's own stated functions
at an attention segment); the prover's side of the step. -/
theorem mask_behind {k : Coins Bk} {s s' : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
    {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X} {cols : List OpenedColumn}
    (hM : T.Moved blk k m E ds y cols) (att : VerifiableInference.Desc.First.AttOwn) (G : Fork)
    (at1 : First.S → Bound GQ → Bound GQ) (hSt : ∀ Dt, (at1 s' Dt).mask = Dt.mask)
    (ds' : List Fmt.Drawn) :
    MaskIs T own rdOf k s att m (ds ++ ds')
      (at1 s' (dataQ own (behindPart s att G)
        (rdOf (T.wit k y.2.st.input (y.2.st.heard ++ ds'))))) := by
  obtain ⟨⟨l, -, hy⟩, -⟩ := hM
  unfold MaskIs
  rw [hSt, play_heard _ _ _ _ _ hy, (play_mid _ _ _ _ _ hy).1, List.append_assoc]
  rfl

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.mask_part
#print axioms ProofFile.Honest.K5.sum_slots
#print axioms ProofFile.Honest.K5.one_slots
#print axioms ProofFile.Honest.K5.mask_behind
