-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/LensLook.lean: FOR THE ITEM "totalB": THE LOOKUPS' RUNS' NUMBERS OF CLAIMS AT EVERY
STAND OF THE BATCHING, AT THE FRAME's OWN THREAD AT THE LIBRARY's HEAD, AT ALL THREE SORTS OF SEGMENT: PAID; AND SO
`LensAt` FROM THE PUBLIC TEST's YES AND THE SORT's OWN RUNS' NUMBERS ALONE, BESIDE THE HEAD, THE SEAT AND THE READINGS
THAT THE ASSEMBLIES ALREADY BIND. Statements and proofs: calls; no goal is stated.
  `snap_of_part`, `calls_heard`, `digits_heard`   what is fixed in front has a snapshot where the batching's part is
      there; what the two lookups returned stands at what is fixed (the library has the last two as equations:
      `hdCalls_all`, `hdDigits_all`)
  `shapeD_of_dig`   the shape that the digits' lookup's place makes is the one that the digits' data carry: by unfolding
      the library's `digAt`
  `calls_lens`, `digits_lens`   from the lookups' promise on the state at a shape sh (`K3LeftOn`) and their promise on
      the fixed part (`K3Ok`): "objects" is Forest.lins sh, "planes" 3, "join" 1 (`objLen_eq`, `pickLen_eq`,
      Johnson/Desc/K9/Honest/LensSmall.lean)
  **`lookLens_att`, `lookLens_lay`, `lookLens_head`**   under the head, an opening O of the head's own form and the
      readings hA (at attention), e3, hd, hC, hD of the assemblies: the premise hlook of `lensAt_att`, `_lay`, `_head`
      (Honest/K9/LensAtStand.lean), to the letter
  **`lensAt_att_look`, `lensAt_lay_look`, `lensAt_head_look`**   so `LensAt`, in the very form of the assemblies'
      premise hlens, from hLE (`LensEqAsked Zp`), Sd, these readings, and hruns (with hjoin at the head)
PAID INSIDE, BY CALLS: at the calls' seat: the promise on the state off the thread (the frame's `bridge_hL`); its shape
is the plan's (the library's `place_att`, `place_lay`, `place_head` at `h.pubOne`) · at the digits' seat: the promise on
the state at every state reached in front (the library's `leftOn_digits_front`, `leftOn_digits_head`, at the frame's
`thr_reach` and `bridge_hB`); its shape is the built segment's f9 (`shapeD_of_dig`, `placeD_of_dig`, the library's
`P5J.closed_at_hd`) · the promise on the fixed part: out of Ok itself · that the batching's part is there
(`part_of_behind`, off the stand's field bat) · that every block's plan is in order (the library's `IM.plan_flat` at
`h.laid.planOk`).
GROUND: beside the sealed library, what lies beneath Honest/K9/LensAtStand.lean, and our
Johnson/Desc/K9/Honest/LensSmall.lean. At the full size and the format's second hash function alone: the head's.
WHAT IS NOT CLAIMED. hLE at any public part; hruns, hjoin at any thread; the readings, O or Sd at any public part. That
a stand is there: where there is none all six say nothing. No member; `lensAt_head_look` and `lensAt_lay_look` are
called by Honest/K9/LensRuns.lean, `lensAt_att_look` by Honest/K9/LensAttPaid.lean. These are numbers of the lookups'
runs, typed by us off the library's and the frame's lemmas: the lookups' house has not read them. Nothing on any
property.

-/
import Johnson.Desc.K9.Honest.LensSmall
import Johnson.Desc.ProofFile.Honest.K9.LensAtStand
import Johnson.Desc.First.Look.K3PlaceLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.LinkJoin VerifiableInference.Desc.K9L VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.First.Att (P.parCOf)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First.Look (placeAt)
open VerifiableInference.OnPublicFiles (K3Ok K3LeftOn objLen pickLen)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread
open _root_.Desc.K14.Law (seatZ secondAt)

/-- Where the batching's part is there, what is fixed in front has a snapshot. -/
theorem snap_of_part {α : Type} (φ : S → α) {s : S} (hp : (Desc.K9.atS.get? s).isSome = true) :
    ∃ u, (fixed9 φ s).2 = some u := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.1 hp
  exact ⟨pubOf a, by
    show (Desc.K9.atS.get? s).map pubOf = _
    rw [ha]
    rfl⟩

/-- What the lookup on the calls returned, at what is fixed. -/
theorem calls_heard (u : HTailF2) {s : S} {g : Forest.Heard} (hg : s.lookHeard? = some g) :
    hdCalls (fixed9 (phiFill u) s).1 = some g := hg

/-- What the lookup on the digits returned, at what is fixed. -/
theorem digits_heard (u : HTailF2) {s : S} {g : Forest.Heard} (hg : heardDig s = some g) :
    hdDigits (fixed9 (phiFill u) s).1 = some g := by
  obtain ⟨tl, htl, hh⟩ := Option.bind_eq_some_iff.1 hg
  show (s.tl?.map (TailClaims.Law.blank u)).bind (fun t : HTailF2 => t.heard) = some g
  rw [htl]
  exact hh

/-- The shape that the digits' lookup's place makes is the one that the digits' data carry. -/
theorem shapeD_of_dig {X : Verify.Public} {i : ℕ} {xx : First.Look.Place} {tlD : HTailF2}
    (hd : First.Look.digAt X i = some (xx, tlD)) :
    (First.Look.P.ofPlace (Params.settingOf X.P.frame) true xx).shape = some tlD.f9 := by
  unfold First.Look.digAt at hd
  obtain ⟨y, -, h1⟩ := Option.bind_eq_some_iff.1 hd
  obtain ⟨tl, -, h2⟩ := Option.bind_eq_some_iff.1 h1
  obtain ⟨sh, hs, h3⟩ := Option.map_eq_some_iff.1 h2
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h3
  exact hs

/-- **The three numbers at the calls' seat**, from the lookups' promise on the state at the shape sh. -/
theorem calls_lens (u : HTailF2) {s : S} {sh : Forest.Shape} {lm first lmD jD : ℕ} {Qf : Fork → Prop}
    (L : K3LeftOn (fun s : S => s.fork?) (fun s : S => s.lookHeard?) sh lm first Qf s)
    (K : K3Ok hdCalls lm first (fixed9 (phiFill u) s)) (hp : (Desc.K9.atS.get? s).isSome = true) (k : ℕ)
    (hk : k < 6) :
    l3All lm first lmD jD (k, "objects") (fixed9 (phiFill u) s) = Forest.lins sh ∧
      l3All lm first lmD jD (k, "planes") (fixed9 (phiFill u) s) = 3 ∧
      l3All lm first lmD jD (k, "join") (fixed9 (phiFill u) s) = 1 := by
  obtain ⟨v, hv⟩ := snap_of_part (phiFill u) hp
  have hsh := leftOn_shape L
  obtain ⟨-, -, -, g, -, -, -, -, hg, -⟩ := L
  have hg' := calls_heard u hg
  refine ⟨?_, ?_, ?_⟩
  · rw [l3_calls lm first lmD jD k hk, objLen_eq hdCalls lm first K hg' hv, hsh g hg]
  · have e : l3All lm first lmD jD (k, "planes") = pickLen hdCalls lm first 3 := by simp [l3All]
    rw [e]
    exact pickLen_eq hdCalls lm first 3 K hg' hv
  · have e : l3All lm first lmD jD (k, "join") = pickLen hdCalls lm first 1 := by simp [l3All]
    rw [e]
    exact pickLen_eq hdCalls lm first 1 K hg' hv

/-- **The number at the digits' seat**, from the lookups' promise on the state at the shape sh. -/
theorem digits_lens (u : HTailF2) {s : S} {sh : Forest.Shape} {lmC jC lm first : ℕ} {Qf : Fork → Prop}
    (L : K3LeftOn S.fork? heardDig sh lm first Qf s) (K : K3Ok hdDigits lm first (fixed9 (phiFill u) s))
    (hp : (Desc.K9.atS.get? s).isSome = true) (k : ℕ) (hk : 6 ≤ k) :
    l3All lmC jC lm first (k, "objects") (fixed9 (phiFill u) s) = Forest.lins sh := by
  obtain ⟨v, hv⟩ := snap_of_part (phiFill u) hp
  have hsh := leftOn_shape L
  obtain ⟨-, -, -, g, -, -, -, -, hg, -⟩ := L
  have e : l3All lmC jC lm first (k, "objects") = objLen hdDigits lm first := by simp [l3All, hk]
  rw [e, objLen_eq hdDigits lm first K (digits_heard u hg) hv, hsh g hg]

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **The lookups' four numbers at an attention segment, at every stand.** -/
theorem lookLens_att {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np)
      (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {A : Attention.Plan} (hA : (P5J.At.X Zp).A[g]? = some A)
    {Xl : LinkH} (e3 : Bs.G₀.built[2 * g + 1]? = some Xl) {xx : First.Look.Place} {tlD : HTailF2}
    (hd : First.Look.digAt (P5J.At.X Zp) (2 * g + 1) = some (xx, tlD)) {pC pD : First.Look.P}
    (hC : placeAt (P5J.At.X Zp) (2 * g + 1) false = some pC)
    (hD : placeAt (P5J.At.X Zp) (2 * g + 1) true = some pD) (Lk : Link S ProofFile.Cl) (p : Desc.K9.Where) :
    ∀ on ∈ [((1, "objects"), Forest.lins A.fs), ((2, "join"), 1), ((1, "planes"), 3),
        ((6, "objects"), Forest.lins Xl.tl.f9)],
      NumAtStand Lk p (phiFill tlD) (okFillAtt A (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD)
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        (batchAt P5J.At.links P5J.At.ps (2 * g + 1)) (l3All pC.lm pC.first 0 pD.first on.1) on.2 := by
  intro on hon κ s m En ds y cols s' x' z G St hOk
  have hm : 2 * g + 1 < 25 := by omega
  have kx := kxAtt_k3 _ hOk.2
  have hpart := part_of_behind St.bat
  -- the calls' seat
  obtain ⟨p', hp', ⟨sh, esh, LC⟩, -⟩ := bridge_hL h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hm St.thr.1
  obtain rfl : pC = p' := Option.some.inj (hC.symm.trans hp')
  obtain ⟨h4, hN, -⟩ := H2K5.Door.scope_all h
  obtain ⟨a, ha, eA, -⟩ := First.Look.place_att h.pubOne hC (by rw [h4, hN]; simp; omega)
    (by rw [h4]; simp)
  have ea : a = A := by
    rw [h4] at ha
    have e : (2 * g + 1) / (if true = true then 2 else 1) = g := by simp; omega
    rw [e] at ha
    exact Option.some.inj (ha.symm.trans hA)
  have es : sh = A.fs := by
    rw [ea] at eA
    exact Option.some.inj (esh.symm.trans eA)
  obtain ⟨c1, c2, c3⟩ := calls_lens tlD (lmD := 0) (jD := pD.first) LC kx.1 hpart 1 (by omega)
  obtain ⟨-, -, c4⟩ := calls_lens tlD (lmD := 0) (jD := pD.first) LC kx.1 hpart 2 (by omega)
  -- the digits' seat
  have hf : cF.blocksInOrder.length = 358 := Meaning.K2.flat_358 h.toAtMg.scope O
  have hb := batch_at.1 (2 * g + 1) (by omega)
  have hq := thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (by rw [hf, hb]; omega) St.thr.1
  rw [hb] at hq
  obtain ⟨P', hh, eP, eS, -, LD⟩ := leftOn_digits_front h.scope h.reads O (IM.plan_flat O h.laid.planOk)
    (by omega : 2 * g + 1 < 24) hq (bridge_hB h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hm St.thr.1) 0
  have eP' : P' = pD := by
    rw [O.W] at eP
    exact Option.some.inj (eP.symm.trans hD)
  have eh : hh = Xl.tl.f9 := by
    have e1 := shapeD_of_dig hd
    rw [Option.some.inj ((placeD_of_dig hd).symm.trans hD), ← eP', eS] at e1
    rw [Option.some.inj e1]
    exact (P5J.closed_at_hd h O hm e3 hd).dig.same.f9.symm
  rw [eP'] at LD
  have d1 := digits_lens tlD (lmC := pC.lm) (jC := pC.first) LD kx.2 hpart 6 (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hon
  rcases hon with rfl | rfl | rfl | rfl
  · show l3All pC.lm pC.first 0 pD.first (1, "objects") _ = Forest.lins A.fs
    rw [← es]
    exact c1
  · show l3All pC.lm pC.first 0 pD.first (2, "join") _ = 1
    exact c4
  · show l3All pC.lm pC.first 0 pD.first (1, "planes") _ = 3
    exact c2
  · show l3All pC.lm pC.first 0 pD.first (6, "objects") _ = Forest.lins Xl.tl.f9
    rw [← eh]
    exact d1

/-- **The lookups' two numbers at a feed-forward segment, at every stand.** -/
theorem lookLens_lay {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np)
      (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {Xl : LinkH} (e3 : Bs.G₀.built[2 * g]? = some Xl)
    {xx : First.Look.Place} {tlD : HTailF2} (hd : First.Look.digAt (P5J.At.X Zp) (2 * g) = some (xx, tlD))
    (p4 : OnBytes.Desc.First.K4.Par) {pC pD : First.Look.P} (hC : placeAt (P5J.At.X Zp) (2 * g) false = some pC)
    (hD : placeAt (P5J.At.X Zp) (2 * g) true = some pD) (Lk : Link S ProofFile.Cl) (p : Desc.K9.Where) :
    ∀ on ∈ [((1, "objects"), Forest.lins Bs.G₀.W.layers.y.fo), ((6, "objects"), Forest.lins Xl.tl.f9)],
      NumAtStand Lk p (phiFill tlD) (okFillLay p4 (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD)
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        (batchAt P5J.At.links P5J.At.ps (2 * g)) (l3All pC.lm pC.first 0 pD.first on.1) on.2 := by
  intro on hon κ s m En ds y cols s' x' z G St hOk
  have hm : 2 * g < 25 := by omega
  have kx := kxAll3_k3 _ hOk.2
  have hpart := part_of_behind St.bat
  -- the calls' seat
  obtain ⟨p', hp', ⟨sh, esh, LC⟩, -⟩ := bridge_hL h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hm St.thr.1
  obtain rfl : pC = p' := Option.some.inj (hC.symm.trans hp')
  obtain ⟨h4, hN, -⟩ := H2K5.Door.scope_all h
  obtain ⟨-, -, eA, -⟩ := First.Look.place_lay h.pubOne hC (by rw [h4, hN]; simp; omega) (by rw [h4]; simp)
  have es : sh = Bs.G₀.W.layers.y.fo := by
    rw [O.W]
    exact Option.some.inj (esh.symm.trans eA)
  obtain ⟨c1, -, -⟩ := calls_lens tlD (lmD := 0) (jD := pD.first) LC kx.1 hpart 1 (by omega)
  -- the digits' seat
  have hf : cF.blocksInOrder.length = 358 := Meaning.K2.flat_358 h.toAtMg.scope O
  have hb := batch_at.1 (2 * g) (by omega)
  have hq := thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (by rw [hf, hb]; omega) St.thr.1
  rw [hb] at hq
  obtain ⟨P', hh, eP, eS, -, LD⟩ := leftOn_digits_front h.scope h.reads O (IM.plan_flat O h.laid.planOk)
    (by omega : 2 * g < 24) hq (bridge_hB h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hm St.thr.1) 0
  have eP' : P' = pD := by
    rw [O.W] at eP
    exact Option.some.inj (eP.symm.trans hD)
  have eh : hh = Xl.tl.f9 := by
    have e1 := shapeD_of_dig hd
    rw [Option.some.inj ((placeD_of_dig hd).symm.trans hD), ← eP', eS] at e1
    rw [Option.some.inj e1]
    exact (P5J.closed_at_hd h O hm e3 hd).dig.same.f9.symm
  rw [eP'] at LD
  have d1 := digits_lens tlD (lmC := pC.lm) (jC := pC.first) LD kx.2 hpart 6 (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hon
  rcases hon with rfl | rfl
  · show l3All pC.lm pC.first 0 pD.first (1, "objects") _ = Forest.lins Bs.G₀.W.layers.y.fo
    rw [← es]
    exact c1
  · show l3All pC.lm pC.first 0 pD.first (6, "objects") _ = Forest.lins Xl.tl.f9
    rw [← eh]
    exact d1

/-- **The lookups' three numbers at the head's segment, at every stand.** -/
theorem lookLens_head {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np)
      (secondAt Zp Np)) {Xl : LinkH} (e3 : Bs.G₀.built[24]? = some Xl)
    {xx : First.Look.Place} {tlD : HTailF2} (hd : First.Look.digAt (P5J.At.X Zp) 24 = some (xx, tlD))
    {pC pD : First.Look.P} (hC : placeAt (P5J.At.X Zp) 24 false = some pC)
    (hD : placeAt (P5J.At.X Zp) 24 true = some pD) (Lk : Link S ProofFile.Cl) (p : Desc.K9.Where) :
    ∀ on ∈ [((2, "objects"), Forest.lins Bs.G₀.W.HLy.fs), ((2, "planes"), 3),
        ((7, "objects"), Forest.lins Xl.tl.f9)],
      NumAtStand Lk p (phiFill tlD) (okFillHead Bs.G₀.W (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD)
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        (batchAt P5J.At.links P5J.At.ps 24) (l3All pC.lm pC.first 0 pD.first on.1) on.2 := by
  intro on hon κ s m En ds y cols s' x' z G St hOk
  have hm : 24 < 25 := by omega
  have kx := kxHead_k3 _ hOk.2
  have hpart := part_of_behind St.bat
  -- the calls' seat
  obtain ⟨p', hp', ⟨sh, esh, LC⟩, -⟩ := bridge_hL h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hm St.thr.1
  obtain rfl : pC = p' := Option.some.inj (hC.symm.trans hp')
  obtain ⟨h4, hN, -⟩ := H2K5.Door.scope_all h
  have e24 : (if (P5J.At.X Zp).p4 then 2 else 1) * (P5J.At.X Zp).NGr = 24 := by rw [h4, hN]; rfl
  obtain ⟨eA, -⟩ := First.Look.place_head h.pubOne (e24.symm ▸ hC)
  have es : sh = Bs.G₀.W.HLy.fs := by
    rw [O.W]
    exact Option.some.inj (esh.symm.trans eA)
  obtain ⟨c1, c2, -⟩ := calls_lens tlD (lmD := 0) (jD := pD.first) LC kx.1 hpart 2 (by omega)
  -- the digits' seat
  have hf : cF.blocksInOrder.length = 358 := Meaning.K2.flat_358 h.toAtMg.scope O
  have hq := thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (by rw [hf, batch_at.2]; omega) St.thr.1
  rw [batch_at.2] at hq
  obtain ⟨P', hh, eP, eS, -, LD⟩ := leftOn_digits_head h.scope h.reads O (IM.plan_flat O h.laid.planOk) hq
    (bridge_hB h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hm St.thr.1) 0
  have eP' : P' = pD := by
    rw [O.W] at eP
    exact Option.some.inj (eP.symm.trans hD)
  have eh : hh = Xl.tl.f9 := by
    have e1 := shapeD_of_dig hd
    rw [Option.some.inj ((placeD_of_dig hd).symm.trans hD), ← eP', eS] at e1
    rw [Option.some.inj e1]
    exact (P5J.closed_at_hd h O hm e3 hd).dig.same.f9.symm
  rw [eP'] at LD
  have d1 := digits_lens tlD (lmC := pC.lm) (jC := pC.first) LD kx.2 hpart 7 (by omega)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hon
  rcases hon with rfl | rfl | rfl
  · show l3All pC.lm pC.first 0 pD.first (2, "objects") _ = Forest.lins Bs.G₀.W.HLy.fs
    rw [← es]
    exact c1
  · show l3All pC.lm pC.first 0 pD.first (2, "planes") _ = 3
    exact c2
  · show l3All pC.lm pC.first 0 pD.first (7, "objects") _ = Forest.lins Xl.tl.f9
    rw [← eh]
    exact d1

/-- **`LensAt` at an attention segment**: the lookups' four numbers paid; what stays: the public test's yes, and the
number of the attention kind's two runs together. -/
theorem lensAt_att_look (hLE : LensEqAsked Zp) {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np)
      (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {kk : ℕ} {Lk : Link S ProofFile.Cl}
    {p : Desc.K9.Where} {ww : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree cF Zp (2 * g + 1) kk Lk p ww)
    {A : Attention.Plan} (hA : (P5J.At.X Zp).A[g]? = some A) {Xl : LinkH}
    (e3 : Bs.G₀.built[2 * g + 1]? = some Xl) {xx : First.Look.Place} {tlD : HTailF2}
    (hd : First.Look.digAt (P5J.At.X Zp) (2 * g + 1) = some (xx, tlD)) {pC pD : First.Look.P}
    (hC : placeAt (P5J.At.X Zp) (2 * g + 1) false = some pC)
    (hD : placeAt (P5J.At.X Zp) (2 * g + 1) true = some pD)
    (hruns : NumAtStand Lk p (phiFill tlD) (okFillAtt A (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD)
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps (2 * g + 1))
      (fun q => StillRun.lenStill (K5Law.fsFirst rdAll (P.parCOf A)) q +
        StillRun.lenStill (K5Law.fsSecond rdAll (P.parCOf A)) q) (K9Asks.attOwnB A.S)) :
    LensAt Lk p (phiFill tlD) (okFillAtt A (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD) (tmFillAtt A pC pD)
      (lenFillAtt A pC pD) (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps (2 * g + 1)) ww :=
  lensAt_att h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hLE O hg Sd hA e3 tlD pC pD
    (lookLens_att h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w O hg hA e3 hd hC hD Lk p) hruns

/-- **`LensAt` at a feed-forward segment**: the lookups' two numbers paid; what stays: the public test's yes, and the
number of the feed-forward kind's run "front". -/
theorem lensAt_lay_look (hLE : LensEqAsked Zp) {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np)
      (secondAt Zp Np)) {g : ℕ} (hg : g < 12) {kk : ℕ} {Lk : Link S ProofFile.Cl}
    {p : Desc.K9.Where} {ww : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree cF Zp (2 * g) kk Lk p ww)
    {Xl : LinkH} (e3 : Bs.G₀.built[2 * g]? = some Xl) {xx : First.Look.Place} {tlD : HTailF2}
    (hd : First.Look.digAt (P5J.At.X Zp) (2 * g) = some (xx, tlD)) (p4 : OnBytes.Desc.First.K4.Par)
    {pC pD : First.Look.P} (hC : placeAt (P5J.At.X Zp) (2 * g) false = some pC)
    (hD : placeAt (P5J.At.X Zp) (2 * g) true = some pD)
    (hruns : NumAtStand Lk p (phiFill tlD) (okFillLay p4 (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD)
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps (2 * g)) (K4Run.lenFront p4 (·.own)) (K9Asks.frontB Bs.G₀.W.layers.y g)) :
    LensAt Lk p (phiFill tlD) (okFillLay p4 (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD) (tmFillLay p4 pC pD)
      (lenFillLay p4 pC pD) (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps (2 * g)) ww :=
  lensAt_lay h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hLE O hg Sd e3 tlD p4 pC pD
    (lookLens_lay h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w O hg e3 hd p4 hC hD Lk p) hruns

/-- **`LensAt` at the head's segment**: the lookups' three numbers paid; what stays: the public test's yes, and the
numbers of the head's kind's three runs and of its join. -/
theorem lensAt_head_look (hLE : LensEqAsked Zp) {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF (seatZ Zp Np)
      (secondAt Zp Np)) {kk : ℕ} {Lk : Link S ProofFile.Cl} {p : Desc.K9.Where}
    {ww : Desc.K9.SegSort × ℕ × Desc.K9.TWhere} (Sd : SeatedFree cF Zp 24 kk Lk p ww) {Xl : LinkH}
    (e3 : Bs.G₀.built[24]? = some Xl) {xx : First.Look.Place} {tlD : HTailF2}
    (hd : First.Look.digAt (P5J.At.X Zp) 24 = some (xx, tlD)) {pC pD : First.Look.P}
    (hC : placeAt (P5J.At.X Zp) 24 false = some pC) (hD : placeAt (P5J.At.X Zp) 24 true = some pD)
    (hruns : ∀ on ∈ [("norm", 29), ("policy", 4), ("logits", 2)],
      NumAtStand Lk p (phiFill tlD) (okFillHead Bs.G₀.W (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD)
        (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
        (batchAt P5J.At.links P5J.At.ps 24)
        (StillRun.lenStill (Kinds.Head.Law.fsK6 Bs.G₀.W.hS (Kinds.Head.Law.readsOf Bs.G₀.W)
          (Kinds.Head.parOf Bs.G₀.W.hS (Kinds.Head.Law.workOf Bs.G₀.W)) kapAll on.1)) on.2)
    (hjoin : NumAtStand Lk p (phiFill tlD) (okFillHead Bs.G₀.W (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD)
      (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps 24)
      (StillRun.lenStill (Kinds.Head.Law.fsJoin Bs.G₀.W.hS (Kinds.Head.Law.readsOf Bs.G₀.W)
        (Kinds.Head.parOf Bs.G₀.W.hS (Kinds.Head.Law.workOf Bs.G₀.W)) kapAll)) 1) :
    LensAt Lk p (phiFill tlD) (okFillHead Bs.G₀.W (ProofFile.k8NU Bs.G₀ Xl) tlD pC pD) (tmFillHead Bs.G₀.W pC pD)
      (lenFillHead Bs.G₀.W pC pD) (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread
      (batchAt P5J.At.links P5J.At.ps 24) ww :=
  lensAt_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hLE O Sd e3 tlD pC pD
    (lookLens_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w O e3 hd hC hD Lk p) hruns hjoin

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.snap_of_part
#print axioms ProofFile.Honest.K9.calls_heard
#print axioms ProofFile.Honest.K9.digits_heard
#print axioms ProofFile.Honest.K9.shapeD_of_dig
#print axioms ProofFile.Honest.K9.calls_lens
#print axioms ProofFile.Honest.K9.digits_lens
#print axioms ProofFile.Honest.K9.lookLens_att
#print axioms ProofFile.Honest.K9.lookLens_lay
#print axioms ProofFile.Honest.K9.lookLens_head
#print axioms ProofFile.Honest.K9.lensAt_att_look
#print axioms ProofFile.Honest.K9.lensAt_lay_look
#print axioms ProofFile.Honest.K9.lensAt_head_look
