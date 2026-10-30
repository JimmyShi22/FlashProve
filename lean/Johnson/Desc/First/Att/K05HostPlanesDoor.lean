-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05HostPlanesDoor.lean: kind K5: THE ROW K05_host_planes
(Johnson/Desc/First/Att/K05HostPlanes.lean), ITS PREMISES GATHERED: what it asks of the verifier's
state sP at which the lookup argument's run on the planes is read falls into FrontAll at sP
(Johnson/Desc/First/Att/K05BehindWorth.lean), four facts on public data (TiePub) and the table of
joints' own item on that run.

WHICH STATE IS sP? THE STATE BEHIND THE KIND's OWN BLOCK (piece 3 of the attention segment; the
border in front of piece 4): the kind's row opens formsT m 2 "planes" there, and the kind's two
readers want what that block has received. FrontAll at sP is had from FrontAll in front of the block
by frontAll_rides (Johnson/Desc/First/Att/K05FrontRides.lean); frontAll_of_door pays it in front.

IS IT EMPTY HERE? NO MEMBER IS SHOWN. A RULE OVER LETTERS.

EVERY LETTER UNDER ∀ IN A PREMISE, AND WHAT PINS IT: hmem: fs (free on purpose), k (ReadMsg) · hSt:
s, a₀ (s.here; the open link's number) · hents: f (a member), y (an entry of f) · hsub: y (a member
of clP). sP, a₀, pt, R, H, clP, gL are the theorem's letters.

Main names:
  `seg_ledger`: the open segment's part has the open segment's ledger.
  `hlook_of_reads`: the row's premise hlook, from SeatReadsSame (lookOfO_eq,
    Johnson/Desc/First/Att/LookOAgrees.lean).
  `tieFacts_here`: TieFacts at a state, from FrontFacts at that state (tieFacts_of,
    Johnson/Desc/First/Att/K05WorthAtFuns.lean, without a lay).
  `K05_host_planes_door`: **the row**, from: its own premises on the plan, on the kind's two readers
    and on the lookup argument's run · FrontAll at sP · TiePub, hi ≤ x.ns · the sentence of the item
    formsT x.link 2 "planes", written out, at sP, with (1, "planes") among its runs · the reader's
    answer R, whose list holds the claims' forms · LateLaid · MemAt · hSt · every entry of the
    claims' forms names row 0 of A.iU3.
Limits. LateLaid is another file's law (lateLaid_affInT, Johnson/Top/H/Keep/LateLaidAt.lean) at H :=
the ledger behind the run: the row is to be called there (hl is then Fo.Later.refl).
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Att.K05HostPlanesAt
import Johnson.Desc.First.Att.K05BehindWorth
import Johnson.Desc.First.Att.LookOAgrees

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb IOR TWhole Cb.Fo Cb.LdLkp Cb.Pv.Att Cb.Pv.Att.End Inst.Model Inst.Model.AttSeg
open OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Road OnBytes.Road.Rows OnBytes.Params
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.First (Meaning Numbers)
open VerifiableInference.Desc.K9 (Readers segAt?)
open VerifiableInference.Desc.Sound (GQ Stated Mem seatTab msgsOf MsgT formsTQ)
open VerifiableInference.Desc.First.Look (Sent JAtt sigListCalls)
open VerifiableInference.OnPublicFiles (attMs attNu K3PlanesPaid K3RanAt K3WorthPlanes)
open K5Law (funsAt matsOf PosG)

/-- The open segment's part has the open segment's ledger. -/
theorem seg_ledger {s : First.S} {pt : VerifiableInference.Desc.K9.Part} {a₀ : First.AttOwn}
    (hpt : segAt? s = some pt) (hs : s.here = .att a₀) : pt.F = a₀.F := by
  have hL : s.link? = some a₀.L := by
    unfold First.S.link?
    rw [hs]
  unfold segAt? at hpt
  rw [hL, fork_front hs, tl_front hs] at hpt
  obtain rfl := Option.some.inj hpt
  rfl

/-- The row's premise hlook. -/
theorem hlook_of_reads (A : Attention.Plan) {sP : First.S} {a₀ : First.AttOwn} {g gL : Forest.Heard}
    (hs : sP.here = .att a₀) (hg : a₀.g = some g) (h : SeatReadsSame g gL) :
    (seatCO (parCOf A)).look sP = some (lookOf A.S.cf.lmb gL) := by
  show (match sP.here with
    | .att a => a.g.map (lookOfO (parCOf A).geo.lmb)
    | _ => none) = _
  rw [hs]
  show a₀.g.map (lookOfO (parCOf A).geo.lmb) = _
  rw [hg]
  show some (lookOfO (parCOf A).geo.lmb g) = _
  rw [lookOfO_same h, lookOfO_eq]
  rfl

/-- TieFacts at a state, from FrontFacts at that state. -/
theorem tieFacts_here {x : VerifiableInference.Desc.First.Look.Place} {A : Attention.Plan} {D : Sent}
    {rad : OracleShape → Nat} {own : List (ℕ × ℕ)} {ps : List (ℕ × (ℕ × ℕ))}
    {qs : List (ℕ × OracleShape)} {hi : ℕ} {s : First.S} {L : LinkCtx}
    {pt : VerifiableInference.Desc.K9.Part} {fs : List Aff}
    (hlo : reqLayoutOk D.codes D.shape D.layout = true) (hR : SymsOK x A.seam.tl D rad)
    (hq : ∀ k : Fin (sigListCalls D rad x.link).length,
      ReadMsg (ReadAddr A.seam.tl []) D x.link k.val →
      (k.val, ((sigListCalls D rad x.link).get k).1) ∈ qs)
    (T : FrontFacts x A D own ps qs s L) (hpt : segAt? s = some pt) (hns : pt.F.ns ≤ hi)
    (hsec : SecL L A.iU3)
    (hents : ∀ f ∈ fs, ∀ y ∈ f.ents.toList, y.tree = A.iU3 ∧ y.row = 0) :
    TieFacts x A D rad own ps qs hi s L pt fs :=
  ⟨T.hB1, T.hB2, T.hB3, T.hlink, T.hshape, T.hlay, T.harr,
    laidOkAt_of hlo hR (frameIs_of_B T.hB1 T.hL T.hlink T.hshape) T.hL qs T.hB3 hq T.hcodes,
    hpt, T.hL, hns, T.there,
    (secL_gives hsec hpt T.hL).2,
    hents⟩

section
variable {Cells Tok : Type} (x : VerifiableInference.Desc.First.Look.Place) (A : Attention.Plan)
  (D : Sent) (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
  (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns A.seam.tl)) → Cb.Gl.E)

include Ex Wp α in
/-- **The row, its premises gathered.** -/
theorem K05_host_planes_door {Cl : Type} {gL : Forest.Heard}
    (fork : First.S → Option Fork) (heard : First.S → Option Forest.Heard) (form : Cl → Aff)
    {planes : ℕ → First.S → Except String (List Cl × First.S)} {bit : First.S → ℕ → ℕ → Aff}
    {pin : First.S → ℕ → Aff}
    (hPaid : K3PlanesPaid fork heard form A.S.cf.lmb planes bit pin) (sP : First.S)
    {r : (ℕ → ℕ → Option Aff) × (ℕ → Option Aff)} {lid : ℕ} {cf : Attention.Cfg}
    {fs : Model.Forest.Shape} (hp : PosG (parCOf A).geo)
    (hr : readersOfK (seatCO (parCOf A)) (parCOf A) sP = some r)
    (hr0 : ∀ col, col < gL.shape.NC * 2 ^ (gL.shape.kT + 5 - A.S.cf.lmb) → (r.1 0 col).isSome)
    (hr1 : ∀ col, col < gL.shape.NC * 2 ^ (gL.shape.kT + 5 - A.S.cf.lmb) → (r.1 1 col).isSome)
    (hrP : ∀ col, col < gL.shape.NC * 2 ^ (gL.shape.kT + 5 - A.S.cf.lmb) → (r.2 col).isSome)
    (hs : Attention.shapeHid lid cf = .ok (A.S, fs)) (hm : MatsFit A.S A.seam.tl)
    (hsh : gL.shape = fs) (hrows : (A.seam.tl.mats.getD (A.S.cf.NAs + 2) {}).m = 2 ^ A.S.cf.lmb)
    (hbit : bit sP = fun e col => (r.1 e col).getD (Aff.ofConst zeroE))
    (hpin : pin sP = fun col => (r.2 col).getD (Aff.ofConst zeroE))
    (first : ℕ) {s : First.S} {w : Wit Cells Tok MsgT} {F0 : Fork} (hf : fork s = some F0)
    (hg : heard s = some gL) (clP : List Cl) (GP H : Fork) (hok : FoNums.ok gL.shape = true)
    (hran : K3RanAt fork heard gL F0 planes sP clP GP) (hl : _root_.Fo.Later GP H)
    -- the table's filling, and what is asked at the state sP
    (ns : ℕ) (N : Nums) (Rds : ℕ → Readers) (runs : ℕ → ℕ → String → List (ℕ × String))
    (St : Stated) (Nn : Numbers) (arr : ℕ → ℕ → ℕ)
    (seat : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (ms : List Mem) (hi : ℕ)
    {pt : VerifiableInference.Desc.K9.Part} {R : VerifiableInference.Desc.K9.Read}
    {a₀ : First.AttOwn} (hsP : sP.here = .att a₀) (hpt : segAt? sP = some pt)
    (hfront : FrontAll x A D (Nn.sent x.link 0)
      (psOf (sigListCalls D rad x.link) seat (readMsgs D x A.seam.tl))
      (qsOf (sigListCalls D rad x.link) (readMsgs D x A.seam.tl)) hi gL sP)
    (hpub : TiePub D x A.seam.tl hi rad) (hhi : hi ≤ x.ns)
    (hItem : ∀ p ∈ runs x.link 2 "planes", formsTQ (Rds x.link) St (Nn.sent x.link 0) p.1 p.2 sP (seatTab D.codes arr ms w))
    (rP : (1, "planes") ∈ runs x.link 2 "planes")
    (hRr : (Rds x.link).forms 1 "planes" sP = some R) (hsub : ∀ y ∈ clP, form y ∈ R.forms)
    (hlate : LateLaid pt.F R.late H (clP.map form))
    (hmem : ∀ (fs : List Aff) (k : Fin (sigListCalls D rad x.link).length),
      ReadMsg (ReadAddr A.seam.tl fs) D x.link k.val → MemAt ms (sigListCalls D rad x.link) seat k)
    (hSt : ∀ s a₀, s.here = .att a₀ → a₀.L.check.frame.link = x.link →
      StatedAtt St A (funsAt A) s)
    (hents : ∀ f ∈ clP.map form, ∀ y ∈ f.ents.toList, y.tree = A.iU3 ∧ y.row = 0) :
    K3WorthPlanes fork heard gL.shape A.S.cf.lmb first
      (fun w q => attNu x A.S A.seam.tl D rad seat arr w q) s w := by
  obtain ⟨p1, p2, p3, p4⟩ := hpub
  obtain ⟨L, T⟩ := hfront.facts
  obtain ⟨_, hnsF, hU⟩ := hfront.ledger a₀.F (by
    show (match sP.here with
      | .att a => some a.F
      | _ => none) = _
    rw [hsP])
  obtain ⟨g, hg0, hrd⟩ := hfront.reads a₀ hsP
  have eL : a₀.L = L := by
    have := T.hL
    unfold First.S.link? at this
    rw [hsP] at this
    exact Option.some.inj this
  have hfl : a₀.L.check.frame.link = x.link := by
    rw [eL]
    exact (liveReqB_at T.hB1 T.hL).1.trans T.hlink
  have TF := tieFacts_here (rad := rad) (hi := hi) p3 p1
    (fun k hk => (hcov_of D rad x A.seam.tl seat [] k hk).2) T hpt
    (by rw [seg_ledger hpt hsP]; exact hnsF) (hfront.sec L T.hL) hents
  exact K05_host_planes_at x A D rad Ex Wp α fork heard form hPaid sP rfl rfl hp hr
    (hlook_of_reads A hsP hg0 hrd) hr0 hr1 hrP hs hm hsh hrows hbit hpin first hf hg clP GP H hok hran hl
    ns N (Rds x.link) St (Nn.sent x.link 0) arr seat ms 1 "planes" hi _ _ hsP hU (hItem _ rP) hRr hsub
    hlate p1 p2 hhi p4 (hmem _) (hcov_of D rad x A.seam.tl seat _) (hcovM_of D rad x A.seam.tl)
    (hSt sP a₀ hsP hfl) TF

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.seg_ledger
#print axioms VerifiableInference.Desc.First.Att.P.hlook_of_reads
#print axioms VerifiableInference.Desc.First.Att.P.tieFacts_here
#print axioms VerifiableInference.Desc.First.Att.P.K05_host_planes_door
