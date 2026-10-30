-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/KeyTextK3.lean: CONDITIONAL: THE TEXT ON THE KEY POINTS (the
premise hK of `k5_owes_all_joined_T`, Honest/K5/Law/AllJoined.lean) AT THE READER `keyOfK3`
(Honest/K5/Law/KeyOfK3.lean), WITH THE `Thread` T A VARIABLE: FROM A PREMISE ON THE VERIFIER's OWN
STEP OF THE MEMBER RIGHT IN FRONT, the segment's lookup on the calls. No stand of the `Thread`, no
run and no witness is named in that premise.

Why. hK ties what the open segment's field g holds TO THE CHALLENGES THAT THE `Thread` HAS HEARD.
Three laws of others meet here: one step back from a border with the step's rounds named
(`thr_back_rounds`, `thr_back_heard`, Honest/Thread/ReachRounds.lean); where the lookup's seated
hearing returns on some rounds, its three fields zx, zy, zk are `keyPtsAt`'s at every list front ++
the rounds' samples ++ back (`keyPtsAt_of_hearVia`, Honest/K3/HeardLaw.lean); and, as the premise,
the form `K3Back`.

  `K3Back`       A PREMISE's FORM, on a sub-protocol and a lookup's public parameters: where the
                 sub-protocol's step accepts, from whatever state and on whatever rounds, the seated
                 hearing has returned on these very rounds, and at an attention segment the field g
                 of the state behind holds what was heard
  `keyText_K3`   CONDITIONAL: **hK's text at `keyOfK3`**

THE PREMISES OF `keyText_K3`, ALL OF THEM. h · A: `K5AtT` · hg · hG · ha · hfr: T's chain has no
round in front (T.front = 0) · hb₃: blk₃ is the member number 14 (2 g + 1) + 3 · hp: the parameters'
shape is the plan's · H3: `K3Back` at T.ft, blk₃ and these parameters.

Limits. Conditional. `K3Back` is shown here of nothing. Its form is the last clause of the
conclusion of `att_back_head` (Honest/K3/Law/Thread/AttBackHead.lean), at one number ft; that file
is not imported here. hfr IS NEEDED, NOT A FORMALITY: the reader's base counts the rounds of the
first chain from its start, and what the `Thread` has heard holds T.front challenges more in front:
at T.front above 0 the reader would cut at the wrong place. h is a hypothesis of every statement
that names it. Where `Thr` T has no member the statement says nothing. At the library's full size
and the format's second hash function alone.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K5.Law.KeysFitK3
import Johnson.Desc.ProofFile.Honest.K5.Law.AtT
import Johnson.Desc.ProofFile.Honest.K3.HeardLaw
import Johnson.Desc.ProofFile.Honest.Thread.ReachRounds
import Johnson.Desc.ProofFile.Honest.Thread.PaysLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K5
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc (Block OpenedColumn Strs Chain)
open VerifiableInference.Desc.First.Att.P (K3Pts)
open ProofFile.Honest.K3 (keyPtsAt keyPtsOf keyPtsAt_of_hearVia)
open ProofFile.Honest.FirstThread (WtF)
open P5J (AtMgA TS CellsM)

/-- **WHERE THE LOOKUP's MEMBER ACCEPTS, THE SEATED HEARING HAS RETURNED ON THESE VERY ROUNDS, AND g
HOLDS WHAT WAS HEARD.** ft: the first tree's number. It is a definition: a premise's form. Nothing
is claimed of it. -/
def K3Back (ft : Nat) (blk₃ : Block TS ProofFile.Cl) (p : VerifiableInference.Desc.First.Look.P) : Prop :=
  ∀ (sj s' : TS) (rs : List Fmt.RoundView) (c : List OpenedColumn) (n : Nat), blk₃.step ft sj rs c = .ok (s', n) →
    ∃ F H G₁, VerifiableInference.Desc.K3.Law.hearVia p F rs = some (H, G₁) ∧
      ∀ att, s'.here = .att att → att.g = some H

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
  {T : Thread Bk TS ProofFile.Cl (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X ProofFile.Inst}
  {g : Nat} {it : VerifiableInference.Desc.First.Item → T.ι} {pb : T.P → ProofFile.InstPub}
  {wt : T.Wt → WtF}
  {ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop} {test : Nat → TS → Option String}
  {carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop}
  {cq : (Local W₀ Rc ProofFile.Inst Tr) → CellsM OnBytes.Flat.numsFull}
  (A : K5AtT h T g it pb wt ans test carryX cq)
include A

/-- **THE TEXT ON THE KEY POINTS AT `keyOfK3`.** T IS A VARIABLE. CONDITIONAL: every premise stands,
by name, in the file's head. H3 (`K3Back`) is shown here of nothing. -/
theorem keyText_K3 (hg : g < 12) {G : Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G)
    {a : Attention.Plan} (ha : (P5J.At.X Zp).A[g]? = some a) (hfr : T.front = 0)
    {blk₃ : Block TS ProofFile.Cl} (hb₃ : cF.blocksInOrder[14 * (2 * g + 1) + 3]? = some blk₃)
    {p : VerifiableInference.Desc.First.Look.P} (hp : p.shape = some a.fs)
    (H3 : K3Back T.ft blk₃ p) (blk : Block TS ProofFile.Cl) :
    ∀ k s m E, Thr T (borderOf g) k s m E → ∀ att g', s.here = .att att →
      att.g = some g' →
      K3Pts a.fs g'.zx g'.zy g'.zk (OnBytes.Slice.readV (g'.zx ++ g'.zy)) ∧
        ∀ ds n, drawsFit blk.rounds ds = true →
          (seatOf keyOfK3 Zp G cF g a).keyAt (m.st.heard ++ ds.take n) = g'.zk := by
  intro k s m E hT att g' e hg'
  have hT' : Thr T (14 * (2 * g + 1) + 3 + 1) k s m E := hT
  have hbT : T.bs[14 * (2 * g + 1) + 3]? = some blk₃ := by
    rw [A.bs]
    exact hb₃
  have hlen : 14 * (2 * g + 1) + 3 + 1 ≤ T.bs.length :=
    (List.getElem?_eq_some_iff.1 hbT).1
  obtain ⟨s₀, cols, sj, blk', c, -, -, hblk', -, -, hst⟩ := thr_back_rounds T hlen hT'
  obtain rfl : blk' = blk₃ := Option.some.inj (hblk'.symm.trans hbT)
  have hh := thr_back_heard T hT'
  obtain ⟨F, H, G₁, hv, hgH⟩ := H3 sj s _ c _ hst
  obtain rfl : H = g' := Option.some.inj ((hgH att e).symm.trans hg')
  have hM : T.front + roundsTo T.bs (14 * (2 * g + 1) + 3) =
      roundsTo cF.blocksInOrder (14 * (2 * g + 1) + 3) := by
    rw [hfr, A.bs, Nat.zero_add]
  have hlenH := T.heard_length hT'.2.1
  have hle : T.front + roundsTo T.bs (14 * (2 * g + 1) + 3) ≤ m.st.heard.length := by
    rw [hlenH]
    unfold roundsTo
    rw [declsTo_succ hbT, List.length_append]
    omega
  have hfl : (m.st.heard.take (T.front + roundsTo T.bs (14 * (2 * g + 1) + 3))).length =
      roundsTo cF.blocksInOrder (14 * (2 * g + 1) + 3) := by
    rw [List.length_take, ← hM]
    omega
  have key : ∀ back : List Fmt.Drawn,
      H.zx = (keyPtsAt a.fs (roundsTo cF.blocksInOrder (14 * (2 * g + 1) + 3)) (m.st.heard ++ back)).zx ∧
      H.zy = (keyPtsAt a.fs (roundsTo cF.blocksInOrder (14 * (2 * g + 1) + 3)) (m.st.heard ++ back)).zy ∧
      H.zk = (keyPtsAt a.fs (roundsTo cF.blocksInOrder (14 * (2 * g + 1) + 3)) (m.st.heard ++ back)).zk := by
    intro back
    have h0 := keyPtsAt_of_hearVia p a.fs hp F G₁ _ H
      (m.st.heard.take (T.front + roundsTo T.bs (14 * (2 * g + 1) + 3))) back hv
    rw [hh, List.take_append_drop, hfl] at h0
    exact h0
  obtain ⟨-, a', -, Pl, -⟩ := k5_member h hg
  obtain rfl : a' = a := Option.some.inj (Pl.plan.symm.trans ha)
  obtain ⟨x₁, hx⟩ := Pl.look
  obtain ⟨-, nc⟩ := H2K5.Honest.fo_at_head h hg ha hx
  refine ⟨?_, fun ds n _ => ?_⟩
  · obtain ⟨ex, ey, ez⟩ := key []
    rw [ex, ey, ez]
    unfold keyPtsAt
    exact k3Pts_cut a'.fs
      (show _ = a'.fs.dT + a'.fs.rK from keyPt_size _ _ _ _ a'.fs.v) nc
  · show keyOfK3 Zp G (2 * g + 1) _ = H.zk
    rw [keyOfK3_at_head h hg hG ha, (key (ds.take n)).2.2]

end

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.keyText_K3
