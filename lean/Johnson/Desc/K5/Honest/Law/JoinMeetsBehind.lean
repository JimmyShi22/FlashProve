-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/JoinMeetsBehind.lean: CONDITIONAL: the lookup's half of the join
(`JoinMeets`, Johnson/Desc/K5/Honest/Law/Join.lean) in the world of the table's sentence at the
state BEHIND the lay of an attention segment's own rounds, IF the table's item on the worth of the
keys (`K3WorthKeys`, Johnson/Top/H/K3Worth.lean) holds at the state IN FRONT, at the same witness.
It is `joinMeets_of_worth` (Johnson/Desc/K5/Honest/Law/JoinFromKeys.lean) with three of its premises
paid: the ledger behind the lay is later than the one in front; the mask row is laid as the item's
own places at the masks; the one form that the lookup left for the join has one worth in the
sentence's world and in the world of the ledger behind.

How. The third follows the road of `formsPlanes_behind`
(Johnson/Desc/K5/Honest/Law/PlanesForward.lean) line by line, for a list of one form, which names no
entry of an array: the library's tie of the two worlds (`worldTie_at`,
Johnson/Desc/First/Att/K05WorldTieAt.lean), brought to the item's places at the masks
(`WorldTie.mask_to`, Johnson/Desc/First/Att/K05WorthLate.lean; `mask_is_nu`,
Johnson/Desc/First/Att/K05PlacesNu.lean), then `value_late`. A joining; no algebra is in this file.

Main name:
  `joinMeets_behind`   **`JoinMeets` in the sentence's world behind the lay**

THE PREMISES. e, hu, h5, hh, hin: an attention segment is open, nothing has failed, the segment's
own rounds have not been heard before, their hearing returns, the claims' reading returns behind the
lay. hfront, hpub, hhi, hmem, hSt: what the library's law on the two worlds asks in front, on public
data and of the stated functions. hFil: every slot that the form left for the join names is filled
in the ledger in front. hl: what the lookup leaves. hItem: the item, at the witness w. hok, nc:
public. Kp: the key points that the lookup left, read, are the library's at z. hKv: THE ITEM'S KEY
VECTORS ARE kvec. kvec is a free letter; what is meant are the library's key vectors of the honest
cells, and there hKv is a tie on the witness: Johnson/Desc/K5/Honest/Law/KvOfCells.lean draws it,
under the library's head, from a tie of the cells to the witness's data, which is shown nowhere.
Ex, Wp, al, ns, N: free letters of the library's law on the two worlds.
Limits. None of the premises is shown to be met here.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.K5.Honest.Law.PlanesForward
import Johnson.Desc.K5.Honest.Law.JoinFromKeys

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End
open OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Road OnBytes.Road.Rows OnBytes.Params
open VerifiableInference.Desc (Wit Claim)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.Sound (GQ MsgQ Stated Mem seatTab MsgT worldOwn dataQ)
open VerifiableInference.Desc.First.Look (Sent JAtt sigListCalls)
open VerifiableInference.OnPublicFiles (attNu K3WorthKeys)
open K5Law (funsAt)
open VerifiableInference.Desc.First.Att.P
open VerifiableInference.Desc

section
variable {Cells Tok : Type} (x : VerifiableInference.Desc.First.Look.Place) (A : Attention.Plan)
  (D : Sent) (rad : OracleShape → Nat)

/-- **The lookup's half of the join, in the sentence's world behind the lay, from the item on the
keys' worth in front.** Conditional; the premises are listed in the file's head. -/
theorem joinMeets_behind (Ex : Iop.ExtSpec) (Wp : Type)
    (al : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns A.seam.tl)) → Cb.Gl.E)
    (claim : Aff → Claim) {s : First.S} {att : First.AttOwn} {xr : Params.AttentionRounds}
    {rs : List Fmt.RoundView} {h : Heard} {G : Fork} (e : s.here = .att att) (hu : s.failed = none)
    (h5 : att.heard5 = none) (hh : hear xr (att.F, rs, 0) = some (h, G, [], 0)) {i : Runs.In}
    {K : ℕ} (hin : inOf (seatCO (parCOf A)) (parCOf A) (behind s att h G) = some (i, K))
    {gL : Forest.Heard} (hFil : _root_.Fo.FilledA att.F gL.cEnd) (ns : ℕ) (N : Nums) (St : Stated)
    (Nn : Numbers) (arr : ℕ → ℕ → ℕ) (seat : Fin (sigListCalls D rad x.link).length → ℕ × ℕ)
    (ms : List Mem) (hi : ℕ)
    (hfront : FrontAll x A D (Nn.sent x.link 0)
      (psOf (sigListCalls D rad x.link) seat (readMsgs D x A.seam.tl))
      (qsOf (sigListCalls D rad x.link) (readMsgs D x A.seam.tl)) hi gL s)
    (hpub : TiePub D x A.seam.tl hi rad) (hhi : hi ≤ x.ns) {w : Wit Cells Tok MsgT}
    {J₀ : Type} [DecidableEq J₀] {ι : _root_.Fo.Pl → Option J₀} {Q : Fork → Prop}
    {x0 : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option J₀)}
    (hl : K3LeftOutIs (K3.seatCalls claim).fork (K3.seatCalls claim).heard x.fs x.lm x.F.next ι Q
      x0 gL s)
    (Kv : Wit Cells Tok MsgT → ℕ → ℕ → Cb.Gl.E)
    (hItem : K3WorthKeys (K3.seatCalls claim).fork (K3.seatCalls claim).heard x.fs x.lm x.F.next
      (attNu x A.S A.seam.tl D rad seat arr) Kv s w)
    (hok : FoNums.ok x.fs = true) (nc : x.fs.NC = 4)
    (hmem : ∀ (fs : List Aff) (k : Fin (sigListCalls D rad x.link).length),
      ReadMsg (ReadAddr A.seam.tl fs) D x.link k.val → MemAt ms (sigListCalls D rad x.link) seat k)
    (hSt : ∀ s a₀, s.here = .att a₀ → a₀.L.check.frame.link = x.link →
      StatedAtt St A (funsAt A) s)
    {C : Inst.Model.AttSeg.Calls} {z : ℕ → Cb.Gl.E} (Kp : KeyPtsAre Reading.gl C z gL.zk)
    {kvec : Fin 4 → ℕ → Cb.Gl.E} (hKv : ∀ c : Fin 4, ∀ X < 2 ^ C.a c, Kv w c.val X = kvec c X) :
    JoinMeets Reading.gl
      (worldOwn (partAt s att G none) [] (St.at1 (behind s att h G)
        (dataQ (Nn.sent x.link 0) (partAt s att G none) (seatTab D.codes arr ms w)))) gL
      fun c => Blocks.ext (C.a c) (kvec c) (C.zC c z) := by
  have led : seatSO.ledger s = some att.F := by
    show (match s.here with | .att a => some a.F | _ => none) = _
    rw [e]
  obtain ⟨hz, _, _⟩ := hfront.ledger att.F led
  obtain ⟨g₀, hg₀, _⟩ := hfront.reads att e
  have hfP := frontAll_rides hfront led hh (lay_of_parts e h5 hg₀ hu h G)
  obtain ⟨_, bl⟩ := hear_below hh hz
  have lt : _root_.Fo.Later att.F G := by
    obtain ⟨_, _, _, _, _, _, st⟩ := hear_said hh hz
    exact ⟨bl.1, bl.ns, fun j hj => by
      obtain ⟨a, b, d⟩ := st j _ _ ⟨hj, rfl, rfl⟩
      exact ⟨a, b, d⟩⟩
  -- the facts in front, carried behind the lay
  obtain ⟨p1, p2, p3, p4⟩ := hpub
  obtain ⟨Lc, T⟩ := hfP.facts
  obtain ⟨_, hnsF, _⟩ := hfP.ledger G rfl
  have eL : att.L = Lc := Option.some.inj T.hL
  have hfl : att.L.check.frame.link = x.link := by
    rw [eL]
    exact (liveReqB_at T.hB1 T.hL).1.trans T.hlink
  have hents : ∀ f ∈ [gL.cEnd], ∀ y ∈ f.ents.toList, y.tree = A.iU3 ∧ y.row = 0 := by
    intro f hf y hy
    rw [List.mem_singleton.1 hf, hfront.plain] at hy
    cases hy
  have TF := tieFacts_here (rad := rad) (hi := hi) p3 p1
    (fun k hk => (hcov_of D rad x A.seam.tl seat [] k hk).2) T
    (segAt_behind (s := s) (a := att) (h := h) (G := G)) hnsF (hfP.sec Lc T.hL) hents
  have hslots : ∀ f ∈ [gL.cEnd], ∀ y ∈ f.slots.toList, y.1 < (partAt s att G none).F.ns := by
    intro f hf y hy
    rw [List.mem_singleton.1 hf] at hy
    show y.1 < G.ns
    rw [bl.ns]
    exact (hFil y hy).1
  -- the two worlds
  have Wt := worldTie_at x A D rad Ex Wp al ns N St (Nn.sent x.link 0) arr seat ms w [gL.cEnd] hi
    _ _ (funsAt A) _ p1 p2 p4 (hmem _) (hcov_of D rad x A.seam.tl seat _)
    (hcovM_of D rad x A.seam.tl) (hSt _ { att with F := G, heard5 := some h } rfl hfl) TF hslots
    (funsAt_of_inOf A hin gL)
  have Wt' := Wt.mask_to (mask' := fun j => attNu x A.S A.seam.tl D rad seat arr w (.mask j))
    fun f hf' y hy => mask_is_nu x A.S A.seam.tl D rad seat arr Ex Wp al ns N w y.1
      (Nat.lt_of_lt_of_le (hslots f hf' y hy) (Nat.le_trans TF.hns hhi))
  have hW := value_late (lateLaid_none (partAt s att G none).F [gL.cEnd]) Wt'
    (List.mem_singleton.2 rfl)
  refine joinMeets_of_worth hl _ Kv w hItem hok nc (G := G) (fun F' hf => ?_) _ _ (fun _ _ => rfl)
    hW.symm Kp hKv
  obtain rfl : F' = att.F :=
    Option.some.inj ((show s.fork? = some F' from hf).symm.trans (fork_front e))
  exact lt

end

end H2K5.Honest

#print axioms H2K5.Honest.joinMeets_behind
