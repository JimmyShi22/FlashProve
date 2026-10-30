-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadLink.lean: the output head's link in one theorem: from claims of the verifier that
hold, and from what each random step is meant to give, to "the reply is the model's first choice".

The files beside this one compare, piece by piece, the forms that the verifier in OnBytes/ builds
for the output head's sub-proof with the library's head. This file joins them. Its theorem speaks of
one run R of the head's check, one world W (a value for every hidden value), and integer matrices Mz
of cells. It uses
  the nine segments' forms and the forms of the six calls (Johnson/Road/HeadCallLib.lean),
  the form of the claim that hands the calls' forms to the lookup (Johnson/Road/HeadJoin.lean),
  the 17 forms of the final normalisation's ledger (Johnson/Road/HeadLedger.lean),
  the verifier's tables and the cells read in the verifier's matrices
    (Johnson/Road/HeadBridge.lean, over HeadTabs.lean, HeadPlace.lean, HeadSum.lean).

What is a hypothesis. (1) Public facts on the layout and on the calls' key points. (2) That the
tables of the reads are true of the cells read in Mz, and that every entry of Mz is small: what the
smallness test is meant to give. (3) That claims hold in W: the 17 of the ledger, the one on the
calls' key vectors, and all other claims that the lookup leaves (LookupMeans): what the batching of
all claims is meant to give. (4) What 18 slots hold: the nine claimed sums of a product layer (hW),
the seven claimed sums of products (hP), and the first slots of two sumchecks (SlotsHold). (5) Two
steps from one point to all indices: StepPoint (17 extensions that are 0 at the point P_V are
extensions of functions that are 0) and StepLookup (if all claims of the lookup hold, every value of
each call's function is a row of the call's table). (6) What the layers must give. None of (2) to
(6) is derived from a verifier's acceptance.

What a step is, and is not. A step is an implication, taken as a hypothesis. Its conclusion implies
it, and under the theorem's other hypotheses it says as much as its conclusion: the theorem asks no
less than it would with the conclusion in the step's place. What the step adds is a name for the
premise: what the verifier's claims mean on the library's arrays. The world W is free: no hypothesis
ties the value under a slot to what the prover has shown, and the matrices, the index and the world
may hang on every challenge that R holds: which is fixed before which stands in no statement.
StepPoint reads no world, so of these two lacks the second alone touches it. StepLookup reads the
world; the claims that the lookup leaves are made on shown values, so whoever is to show it needs
the tie to what was shown besides. No probability is stated.

Main definitions: joinForm, CallsAt, SlotsHold, joinWorth, PlanesOf, LookupMeans, StepLookup,
StepPoint.
Main theorems: claimJoin_form (the claim that claimJoin adds is joinForm of the calls' forms);
planesOf_of_claim; joinForm_worth; head_link_rf, head_link.

The program does not import this file.
-/
import Johnson.Road.HeadBridge
import Johnson.Road.HeadJoin
import Johnson.Road.HeadLedger

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Finset
open Inst.Model Inst.Model.Head
open OnBytes.Model (Reading World Aff Fork SubM Row5)

/-- The form that the lookup's routine makes of the calls' forms KF. -/
def joinForm (g : Model.Forest.Heard) (KF : Array Aff) : Aff :=
  (List.range KF.size).foldl
      (fun (f : Aff) c =>
        Aff.addMul f (Aff.ofConst (subE g.alpha (scaleE c.toUInt64 g.theta)) -
          KF.getD c (Aff.ofConst zeroE)) (g.e.getD c zeroE))
      (Aff.ofConst zeroE) + Aff.ofConst (emptyE g) - g.cEnd

/-- KF holds, call by call, a form that keyForm returns from the state F and the context C. -/
def FormsOf (R : Model.Head.Run) (F : Fork) (C : Ctx) (KF : Array Aff) : Prop :=
  KF.size = R.L.calls.size ∧ ∀ q, q < R.L.calls.size → ∃ laid x,
    Ok (Model.Head.keyForm R q laid) F C x F C ∧ KF.getD q (Aff.ofConst zeroE) = x.1

/-- The claim that claimJoin adds is joinForm of the calls' forms. hLeaves: keyForm leaves state and
context. -/
theorem claimJoin_form {R : Model.Head.Run} {F G : Fork} {C D : Ctx} {u : Unit}
    (hLeaves : ∀ q laid x G' D', Ok (Model.Head.keyForm R q laid) F C x G' D' → G' = F ∧ D' = C)
    (h : Ok (Model.Head.claimJoin R) F C u G D) :
    D = C ∧ ∃ KF, FormsOf R F C KF ∧
      (F.paid R.x.g1.owedJoin).lin (joinForm R.x.g1 KF) = some G := by
  unfold Model.Head.claimJoin at h
  dsimp only at h
  rw [ok_bind] at h
  obtain ⟨⟨KF, laid⟩, F1, C1, h1, h2⟩ := h
  have i1 := ok_forIn_range R.L.calls.size _
    (fun q (b : MProd (Array Aff) (Array ℕ)) F' C' => F' = F ∧ C' = C ∧ b.1.size = q ∧
      ∀ c, c < q → ∃ laid x, Ok (Model.Head.keyForm R c laid) F C x F C ∧
        b.1.getD c (Aff.ofConst zeroE) = x.1)
    (by
      rintro q ⟨kf, ld⟩ F2 C2 r F3 C3 _ ⟨rfl, rfl, hs, hv⟩ hr
      try dsimp only at hr
      rw [ok_bind] at hr
      obtain ⟨⟨v, l⟩, F4, C4, h3, h4⟩ := hr
      obtain ⟨rfl, rfl⟩ := hLeaves q ld (v, l) F4 C4 h3
      try dsimp only at h4
      rw [ok_bind] at h4
      obtain ⟨_, F5, C5, h5, h6⟩ := h4
      rw [ok_pure] at h5 h6
      obtain ⟨_, rfl, rfl⟩ := h5
      obtain ⟨rfl, rfl, rfl⟩ := h6
      refine ⟨_, rfl, rfl, rfl, ?_, ?_⟩
      · show (kf.push v).size = q + 1
        rw [Array.size_push, hs]
      · intro c hc
        show ∃ (laid : Array ℕ) (x : Aff × Array ℕ), _ ∧
          (kf.push v).getD c (Aff.ofConst zeroE) = x.1
        rcases Nat.lt_succ_iff_lt_or_eq.mp hc with h7 | h7
        · have e : (kf.push v).getD c (Aff.ofConst zeroE) = kf.getD c (Aff.ofConst zeroE) := by
            simp [Array.getD, Array.getElem_push, hs, h7, Nat.lt_succ_of_lt h7]
          rw [e]
          exact hv c h7
        · have e : (kf.push v).getD c (Aff.ofConst zeroE) = v := by
            simp [Array.getD, Array.getElem_push, hs, h7]
          rw [e, h7]
          exact ⟨ld, (v, l), h3, rfl⟩)
    (b := ⟨#[], Array.replicate R.x.g1.shape.NT 0⟩)
    ⟨rfl, rfl, rfl, fun c hc => absurd hc (Nat.not_lt_zero c)⟩ h1
  obtain ⟨rfl, rfl, hsz, hval⟩ := i1
  dsimp only at h2
  rw [ok_bind] at h2
  obtain ⟨_, F2, C2, h3, h4⟩ := h2
  have h3' : Ok (liftM (Model.mustAs "internal-forest-padding-places"
      (laid == R.x.g1.shape.pub)) : SubM Unit) F1 C1 () F2 C2 := h3
  rw [ok_lift, mustAs_ok] at h3'
  obtain ⟨⟨_, rfl⟩, rfl⟩ := h3'
  rw [ok_bind] at h4
  obtain ⟨f, F3, C3, h5, h6⟩ := h4
  obtain ⟨rfl, rfl, _, rfl⟩ := ok_join h5
  rw [ok_lin] at h6
  exact ⟨h6.2, KF, ⟨hsz, hval⟩, h6.1⟩

section Link

variable {K : Type} [Field K]

/-- What is asked of each call and its key point p q: the call has 2^lJ columns; the point's first
lJ coordinates are the call's column coordinates, the next lt are the point u; every segment is the
one that its name finds, and bears one of the nine names. -/
def CallsAt (ρ : Reading K) (R : Model.Head.Run) (u : ℕ → K) (p : ℕ → ℕ → K) : Prop :=
  ∀ q, q < R.L.calls.size →
    (R.L.calls.getD q default).J = 2 ^ (R.L.calls.getD q default).lJ ∧
    (Model.Head.zjOf R.L R.x.g1 q).size = (R.L.calls.getD q default).lJ ∧
    (∀ k, k < (R.L.calls.getD q default).lJ →
      pt ρ (Model.Head.zjOf R.L R.x.g1 q) k = p q k) ∧
    (∀ k, k < R.h.lt → p q ((R.L.calls.getD q default).lJ + k) = u k) ∧
    ∀ g ∈ (R.L.calls.getD q default).segs, Found R q g ∧ ∃ s, g.name = nameOf s

/-- The first slots of two sumchecks hold what they are meant to hold: the weighted extension of the
differences of logits, and that of the products of stream and reciprocal. -/
def SlotsHold (ρ : Reading K) (W : World K) (R : Model.Head.Run) (t : Head.Cells K)
    (H : ℕ → ℕ → K) (y : Req) (u : ℕ → K) : Prop :=
  ∀ q, q < R.L.calls.size →
    (∀ g ∈ (R.L.calls.getD q default).segs, g.name = "HD0" →
      (2 : K) ^ R.h.lPd * W.slot R.x.tH.sCl = meantHD0 ρ R q HeadSizes.ref t H y u g) ∧
    (if q = R.x.qN then W.slot R.x.tN.sCl else 0) =
      ((R.L.calls.getD q default).segs.map fun g =>
        if g.name = "NF" then meantNF ρ R q HeadSizes.ref t u g else 0).sum

/-- What the claim on the calls' key vectors is worth if the form of call c is worth the extension
of fn c at p c. -/
def joinWorth (ρ : Reading K) (W : World K) (R : Model.Head.Run) (fn : ℕ → ℕ → ℕ → K)
    (p : ℕ → ℕ → K) : K :=
  ∑ c ∈ range R.L.calls.size, ρ.val (R.x.g1.e.getD c zeroE) *
      (ρ.val R.x.g1.alpha - ρ.val (ofF c.toUInt64) * ρ.val R.x.g1.theta -
        Blocks.ext ((R.L.calls.getD c default).lJ + R.h.lt)
          (fun X => fn c (X / 2 ^ R.h.lt) (X % 2 ^ R.h.lt)) (p c)) +
    ρ.val (emptyE R.x.g1) - R.x.g1.cEnd.value ρ W

/-- The forms of the calls put into the lookup's form: under the hypotheses of the statements on the
nine segments, with the two slots holding what they are meant to hold, the claim on the calls' key
vectors is worth joinWorth. -/
theorem joinForm_worth {ρ : Reading K} {W : World K} (hρ : Numerals ρ) {R : Model.Head.Run}
    {F : Fork} {C : Ctx} {low u : ℕ → K} {t : Head.Cells K} (H : ℕ → ℕ → K) {y : Req}
    (X : LinesFit ρ W R HeadSizes.ref (colsOf F R.iU3) t y low u) {p : ℕ → ℕ → K}
    (A : CallsAt ρ R u p) (S : SlotsHold ρ W R t H y u) {w : ℕ → Array ℕ}
    {fn : ℕ → ℕ → ℕ → K}
    (hw : ∀ q, (R.L.calls.getD q default).segs.foldlM
      (fun w g => Model.Head.markColumns R w g)
      (Array.replicate (R.L.calls.getD q default).J 0) = some (w q))
    (Kf : ∀ q, KeyFn (R.L.calls.getD q default).segs (w q) (R.L.calls.getD q default).J
      (kvOf (ρ.val (invE (Model.Head.pw (R.h.digSh + 15)))) HeadSizes.ref (npOf R.h) t H y)
      (ρ.val (ofF ((R.L.cl.getD q default).tauAt (R.L.cl.getD q default).t0))) (fn q))
    {KF : Array Aff} (hKF : FormsOf R F C KF) :
    (joinForm R.x.g1 KF).value ρ W = joinWorth ρ W R fn p := by
  unfold joinForm joinWorth
  rw [join_value, hKF.1]
  congr 2
  refine sum_congr rfl fun c hc => ?_
  have hc' := mem_range.mp hc
  obtain ⟨laid, x, hx, e⟩ := hKF.2 c hc'
  obtain ⟨a1, a2, a3, a4, a5⟩ := A c hc'
  obtain ⟨s1, s2⟩ := S c hc'
  obtain ⟨_, _, hv⟩ := keyForm_keys_zero hρ H X a1 a2 a3 a4 a5
    (fun w' hw' => by
      have e' : w' = w c := Option.some.inj (hw'.symm.trans (hw c))
      rw [e']
      exact Kf c) s1 s2 hx
  rw [e, hv]

end Link

/-- An entry of a table on the matrix of the lookup's counts, as claimPlanes names it. -/
def planeCol (R : Model.Head.Run) (t x : ℕ) : SubM Aff := do
  Model.mustAs "internal-h-table-index" (x < R.L.kb)
  Model.Head.U3at R t x

/-- A holds the three forms on the planes of the lookup's counts, as the lookup's routine
planeClaims returns them from the state F and the context C, with the reads that claimPlanes hands
to it. -/
def PlanesOf (R : Model.Head.Run) (F : Fork) (C : Ctx) (A : Array Aff) : Prop :=
  ∃ tB0 tB1 tP G D, Starts R "bH-bits-0" tB0 ∧ Starts R "bH-bits-1" tB1 ∧ Starts R "bH-pin" tP ∧
    Ok (Model.Forest.planeClaims R.x.g1 R.h.lmbH
      (fun e x => planeCol R (if e == 0 then tB0 else tB1) x) (planeCol R tP)) F C A G D

/-- If claimPlanes succeeds, planeClaims has returned three such forms. -/
theorem planesOf_of_claim {R : Model.Head.Run} {F G : Fork} {C D : Ctx} {u : Unit}
    (h : Ok (Model.Head.claimPlanes R) F C u G D) : ∃ A, PlanesOf R F C A := by
  unfold Model.Head.claimPlanes at h
  rw [ok_bind] at h
  obtain ⟨tB0, F1, C1, h1, h⟩ := h
  obtain ⟨rfl, rfl, s0⟩ := ok_tabAt h1
  rw [ok_bind] at h
  obtain ⟨tB1, F2, C2, h2, h⟩ := h
  obtain ⟨rfl, rfl, s1⟩ := ok_tabAt h2
  rw [ok_bind] at h
  obtain ⟨tP, F3, C3, h3, h⟩ := h
  obtain ⟨rfl, rfl, s2⟩ := ok_tabAt h3
  replace h : Ok (Model.Forest.planeClaims R.x.g1 R.h.lmbH
      (fun e x => planeCol R (if e == 0 then tB0 else tB1) x) (planeCol R tP) >>= fun A =>
        A.forM SubM.lin >>= fun _ => Model.Forest.planesAdded R.x.g1) _ _ u G D := h
  rw [ok_bind] at h
  obtain ⟨A, F4, C4, h4, _⟩ := h
  exact ⟨A, tB0, tB1, tP, F4, C4, s0, s1, s2, h4⟩

/-- The lookup's other claims hold in W: those that read mask entries alone (the tie's, one for each
level of the two product trees, the bits'), and the members of the array A. Here A is any array; the
theorems from Johnson/Road/HeadLinkRun.lean on take for it the three forms on the planes of the
counts that planeClaims returns (PlanesOf). -/
def LookupMeans (W : World Cb.Gl.E) (R : Model.Head.Run) (A : Array Aff) : Prop :=
  (∀ f ∈ R.x.g1.rows, f.value Reading.gl W = 0) ∧ ∀ f ∈ A, f.value Reading.gl W = 0

/-- The lookup's step, as a hypothesis: if ALL claims that the lookup leaves hold (its other claims,
and the claim on the calls' key vectors in the meaning that joinForm_worth gives it), every value of
each call's function is the reading of a row of the verifier's table of that call. The claim on the
key vectors is one of the claims that the lookup leaves; with the three forms of PlanesOf for A the
premise has them all. -/
def StepLookup (W : World Cb.Gl.E) (R : Model.Head.Run) (A : Array Aff)
    (fn : ℕ → ℕ → ℕ → Cb.Gl.E) (p : ℕ → ℕ → Cb.Gl.E) : Prop :=
  LookupMeans W R A → joinWorth Reading.gl W R fn p = 0 →
    ∀ q j, j < (R.L.calls.getD q default).J → ∀ a, a < nT →
      ∃ u, u < 2 ^ (R.L.cl.getD q default).k ∧
        fn q j a = Reading.gl.val (ofF ((R.L.cl.getD q default).tauAt u))

/-- The step from one point to all positions, as a hypothesis: if the extensions of the 17
identities are 0 at the point v, the identities are 0 at every position. -/
def StepPoint (np : NormPar) (t : Head.Cells Cb.Gl.E) (lt : ℕ) (v : ℕ → Cb.Gl.E) : Prop :=
  (∀ k, k < 17 → Blocks.ext lt (fun a => Cm.Plain.idn np t a k) v = 0) →
    ∀ a < nT, ∀ k < 17, Cm.Plain.idn np t a k = 0

/-- The head's link, as far as the field relation of the library's plain head over the challenge
field: head_link below without what the layers must give. -/
theorem head_link_rf {R : Model.Head.Run} {F : Fork} {C : Ctx} {W : World Cb.Gl.E}
    (hy : Model.Head.layout R.h tauFCw = .ok R.L) (hF : R.h.famF = 24) (hT : R.h.tabS = 4)
    (Hs : HasAll R) (i : Index ppref) (x : Instance ppref) (hr : x.r = 1023) {Mz : Mats ℤ}
    {low u v : ℕ → Cb.Gl.E} {p : ℕ → ℕ → Cb.Gl.E}
    (X : LinesFit Reading.gl W R HeadSizes.ref (colsOf F R.iU3)
      (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)) (Cm.reqOf x) low u)
    (hPV : ShortAt W R (colsOf F R.iU3) "hr@P_V" R.h.lt v
      (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)).hr)
    (small : ∀ a r c, |Mz a r c| < 2 ^ 18)
    (A : CallsAt Reading.gl R u p) {w : ℕ → Array ℕ} {fn : ℕ → ℕ → ℕ → Cb.Gl.E}
    (hw : ∀ q, (R.L.calls.getD q default).segs.foldlM
      (fun w g => Model.Head.markColumns R w g)
      (Array.replicate (R.L.calls.getD q default).J 0) = some (w q))
    (Kf : ∀ q, KeyFn (R.L.calls.getD q default).segs (w q) (R.L.calls.getD q default).J
      (kvOf (Reading.gl.val (invE (Model.Head.pw (R.h.digSh + 15)))) HeadSizes.ref (npOf R.h)
        (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))
        (fun j v => ((i.val.H j v : ℤ) : Cb.Gl.E)) (Cm.reqOf x))
      (Reading.gl.val (ofF ((R.L.cl.getD q default).tauAt (R.L.cl.getD q default).t0))) (fn q))
    {KF : Array Aff} (hKF : FormsOf R F C KF) {q5 : Row5 Aff}
    (hq5 : RowOf R (colsOf F R.iU3) "P_V" q5)
    (claimJ : (joinForm R.x.g1 KF).value Reading.gl W = 0)
    (claimL : ∀ k, k < 17 → ((ledCarries R q5 ++ ledTail R q5).getD k {}).value Reading.gl W = 0)
    (S : SlotsHold Reading.gl W R (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))
      (fun j v => ((i.val.H j v : ℤ) : Cb.Gl.E)) (Cm.reqOf x) u)
    (hW : ∀ s, s < 9 → W.slot (R.x.sW + s) = Blocks.ext R.h.lt (fun a => Ledger.Wsum nD
      (fun l j => bl (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)) l j a) s) v)
    (hP : ∀ j, j < 7 → W.slot (R.x.sPv + j) = Blocks.ext R.h.lt (fun a => Ledger.prods
      (fun n => Dv (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)) n a) j) v)
    (stepP : StepPoint (npOf R.h) (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))
      R.h.lt v)
    {A' : Array Aff} (claimK : LookupMeans W R A') (stepL : StepLookup W R A' fn p) :
    Cm.Plain.TP.RF (F := Cb.Gl.E) (npOf R.h) (fun j v => ((i.val.H j v : ℤ) : Cb.Gl.E))
      (Cm.reqOf x) (cellsH R.h R.L R.b Mz) := by
  have idns := stepP fun k hk => by
    rw [← ledger_idn_plain gl_numerals hq5 hPV hk hW hP]
    exact claimL k hk
  have keys := stepL claimK (by
    rw [← joinForm_worth gl_numerals _ X A S hw Kf hKF]
    exact claimJ)
  exact plainRF_of_port hy hF X.sh hT Hs i x hr hw Kf small keys idns

/-- **The head's link.** See the head of this file for what is a hypothesis. The cells are read in
the integer matrices Mz by the verifier's rule, in the challenge field. fn q: a function on the
columns of call q and the positions, with the library's keys at these cells in the segments' columns
and the verifier's padding key elsewhere (such a function exists: exists_keyFn in
Johnson/Road/HeadFn.lean). KF: the forms that keyForm returns. q5: the row of the
ledger's bytes that is read in the table "hr@P_V". A': any array of forms (the theorems above this
one take the three forms on the planes). If, BESIDES
(1), (2), (4), (5) and (6) of the file's head, the 17 claims of the ledger, the claim on the calls'
key vectors and the lookup's other claims hold in W, then, for a request for the next token, the
library's relation holds under every policy: the final normalisation runs, and the reply is the
least token of largest logit at the last position. That the 48 layers run, and that the head's cells
of the stream are the program's, is (6), a hypothesis. Nothing here ties the index i to a
commitment. -/
theorem head_link {R : Model.Head.Run} {F : Fork} {C : Ctx} {W : World Cb.Gl.E}
    (hy : Model.Head.layout R.h tauFCw = .ok R.L) (hF : R.h.famF = 24) (hT : R.h.tabS = 4)
    (Hs : HasAll R) {κ : ℕ → LayerScale} {tbs : ℕ → Tables} (hn : (npOf R.h).OK)
    (i : Index ppref) (x : Instance ppref) (hr : x.r = 1023) (he : x.e = 1024) {Mz : Mats ℤ}
    {low u v : ℕ → Cb.Gl.E} {p : ℕ → ℕ → Cb.Gl.E}
    (X : LinesFit Reading.gl W R HeadSizes.ref (colsOf F R.iU3)
      (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)) (Cm.reqOf x) low u)
    (hPV : ShortAt W R (colsOf F R.iU3) "hr@P_V" R.h.lt v
      (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)).hr)
    (small : ∀ a r c, |Mz a r c| < 2 ^ 18)
    (A : CallsAt Reading.gl R u p) {w : ℕ → Array ℕ} {fn : ℕ → ℕ → ℕ → Cb.Gl.E}
    (hw : ∀ q, (R.L.calls.getD q default).segs.foldlM
      (fun w g => Model.Head.markColumns R w g)
      (Array.replicate (R.L.calls.getD q default).J 0) = some (w q))
    (Kf : ∀ q, KeyFn (R.L.calls.getD q default).segs (w q) (R.L.calls.getD q default).J
      (kvOf (Reading.gl.val (invE (Model.Head.pw (R.h.digSh + 15)))) HeadSizes.ref (npOf R.h)
        (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))
        (fun j v => ((i.val.H j v : ℤ) : Cb.Gl.E)) (Cm.reqOf x))
      (Reading.gl.val (ofF ((R.L.cl.getD q default).tauAt (R.L.cl.getD q default).t0))) (fn q))
    {KF : Array Aff} (hKF : FormsOf R F C KF) {q5 : Row5 Aff}
    (hq5 : RowOf R (colsOf F R.iU3) "P_V" q5)
    (claimJ : (joinForm R.x.g1 KF).value Reading.gl W = 0)
    (claimL : ∀ k, k < 17 → ((ledCarries R q5 ++ ledTail R q5).getD k {}).value Reading.gl W = 0)
    (S : SlotsHold Reading.gl W R (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))
      (fun j v => ((i.val.H j v : ℤ) : Cb.Gl.E)) (Cm.reqOf x) u)
    (hW : ∀ s, s < 9 → W.slot (R.x.sW + s) = Blocks.ext R.h.lt (fun a => Ledger.Wsum nD
      (fun l j => bl (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)) l j a) s) v)
    (hP : ∀ j, j < 7 → W.slot (R.x.sPv + j) = Blocks.ext R.h.lt (fun a => Ledger.prods
      (fun n => Dv (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E)) n a) j) v)
    (stepP : StepPoint (npOf R.h) (cellsH R.h R.L R.b fun a r c => ((Mz a r c : ℤ) : Cb.Gl.E))
      R.h.lt v)
    {A' : Array Aff} (claimK : LookupMeans W R A') (stepL : StepLookup W R A' fn p)
    (hl : Top.LayersGive κ tbs i.val x.prompt (cellsH R.h R.L R.b Mz)) (pol : AcceptancePolicy) :
    RinfR ppref κ (npOf R.h) tbs pol i x :=
  reply_of_rf hn i x hr he
    (head_link_rf hy hF hT Hs i x hr X hPV small A hw Kf hKF hq5 claimJ claimL S hW hP stepP
      claimK stepL)
    hl pol

#print axioms claimJoin_form
#print axioms joinForm_worth
#print axioms head_link_rf
#print axioms head_link

end OnBytes.Road.Hd
