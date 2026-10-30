-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndHeadRun.lean: the premise `RawRows` of the theorems on what objectsF adds
(OnBytes/Tie/Pv/Tail/EndAll.lean, EndSpread.lean), at the check of the head's sub-proof
(`Head.runForkHidH2`, OnBytes/Model/Head.lean), from one run of the whole check.

Theorems with their proofs.

Main names:
  `getAs_ok`: a value that is unwrapped under a name was there; the context stays.
  `head_ran`: a run of the check holds: the closing of the list of tables; a run of objectsF; the
    runs of the routine that sets the row weights and of the test of the weights, both in one
    context; the arrays' shapes are kept from the check's first state to objectsF, shapes and
    batching element from objectsF to the state at which the row weights are set; the record's
    numbers of the arrays, blocks and lengths are kept from the closed list to objectsF.
  `rawRows_head_run`: `RawRows` as the theorems on objectsF ask it.

Limits: those of OnBytes/Tie/Pv/Tail/EndLayer.lean: the premises on the plan stay, and the context
in which the weights are tested must be a view.


-/
import OnBytes.Tie.Pv.Tail.EndLayer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail.Walk
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail

/-- A value that is unwrapped under a name was there; the context stays. -/
theorem getAs_ok {α : Type} (name : String) (x : Option α) (c c' : Ctx) (a : α)
    (h : Head.getAs name x c = .ok (a, c')) : x = some a ∧ c' = c := by
  unfold Head.getAs at h
  cases x with
  | none => simp [refuse, Blk.fail] at h
  | some b =>
    have h' : (Except.ok (b, c) : Except Failure (α × Ctx)) = .ok (a, c') := h
    cases h'
    exact ⟨rfl, rfl⟩

/-- A run of the check of the head's sub-proof, as far as the smallness test's claims go. -/
theorem head_ran (hS : Head.Shape) (Lh : Head.HL) (b : Head.Border) (hp : Head.HPlanH2)
    (O : Head.Owner) (cov : Head.Covered) (wsLay : WsLay) (L L' : LinkCtx) (F0 F' : Fork)
    (c c' : Ctx) (wo : WsForkOut)
    (h : Head.runForkHidH2 hS Lh b hp O cov wsLay L F0 c = .ok (((wo, L'), F'), c')) :
    ∃ (funs : Array HFun) (tl1 tlA tl : HTailF2) (F7 G F10 F11 F12 : Fork) (c7 c9 cT cT' : Ctx),
      hp.tl.closeFuns funs = some tl1 ∧ RecordKept tl1 tlA ∧ ShapesKept F0 F7 ∧
      tlA.objectsF funs F7 c7 = .ok ((tl, G), c9) ∧ FrameKept G F10 ∧
      tl.coefficientsF F10 cT = .ok (((), F11), cT) ∧
      tl.tileSelfTestF F11 cT = .ok (((), F12), cT') := by
  unfold Head.runForkHidH2 at h
  obtain ⟨_, _, _, _, k1, h⟩ := peelBy (R := ShapesKept) (by walkA) h
  obtain ⟨_, _, _, _, k2, h⟩ := peelBy (R := ShapesKept) (by walkA) h
  obtain ⟨_, _, _, _, k3, h⟩ := peelBy (R := ShapesKept) (by walkA) h
  obtain ⟨_, _, _, _, k4, h⟩ := peelBy (R := ShapesKept) (by walkA) h
  obtain ⟨_, _, _, _, k5, h⟩ := peelBy (R := ShapesKept) (by walkA) h
  obtain ⟨_, _, _, _, k6, h⟩ := peelBy (R := ShapesKept) (by walkA) h
  obtain ⟨_, _, _, _, k7, h⟩ := peelBy (R := ShapesKept) (by walkA) h
  obtain ⟨x, _, _, _, k8, h⟩ := peelBy (R := ShapesKept) (by walkA) h
  obtain ⟨_, _, _, _, k9, h⟩ := peelBy (R := ShapesKept) (by walkA) h
  obtain ⟨t, _, F10p, _, k10, h⟩ := peelBy (R := ShapesKept) (by walkA) h
  obtain ⟨tl1, La, Fa, ca, hc, h⟩ := (bindL_ok _ _ _ _ _ _).1 h
  obtain ⟨hc, -, eFa⟩ := liftBlkL_ok _ _ _ _ _ _ _ _ hc
  obtain ⟨hclosed, -⟩ := getAs_ok _ _ _ _ _ hc
  have k10b : ShapesKept F10p Fa := by
    rw [eFa]
    exact ShapesKept.refl _
  obtain ⟨tlA, Lb, Fb, cb, htr, h⟩ := (bindL_ok _ _ _ _ _ _).1 h
  have k11 := (inferInstance : PresL ShapesKept tl1.transcriptF).out _ _ _ _ _ _ _ htr
  obtain ⟨_, _, _, _, k12, h⟩ := peelBy (R := ShapesKept) (by walkA) h
  obtain ⟨_, _, _, _, k13, h⟩ := peelBy (R := ShapesKept) (by walkA) h
  obtain ⟨_, _, _, _, k14, h⟩ := peelBy (R := ShapesKept) (by walkA) h
  obtain ⟨_, _, _, _, k15, h⟩ := peelBy (R := ShapesKept) (by walkA) h
  obtain ⟨_, _, _, _, k16, h⟩ := peelBy (R := ShapesKept) (by walkA) h
  obtain ⟨_, _, _, _, k17, h⟩ := peelBy (R := ShapesKept) (by walkA) h
  obtain ⟨_, _, _, _, k18, h⟩ := peelBy (R := ShapesKept) (by walkA) h
  obtain ⟨tl, Lw, Fw, cw, hw, h⟩ := (bindL_ok _ _ _ _ _ _).1 h
  obtain ⟨_, Ls, Fs, cs, hs, h⟩ := (bindL_ok _ _ _ _ _ _).1 h
  obtain ⟨F7, c7, G, c9, kb, hobj, ka⟩ := head_walk_ran _ _ _ _ _ _ _ _ _ _ hw
  obtain ⟨F11, hco, htile⟩ := head_selfTests_ran _ _ _ _ _ _ _ _ _ hs
  refine ⟨_, tl1, tlA, tl, F7, G, Fw, F11, Fs, c7, c9, cw, cs, hclosed, transcriptF_record htr, ?_,
    hobj, ka, hco, htile⟩
  exact
    (((((((((((((((((((k1.trans k2).trans k3).trans k4).trans k5).trans k6).trans k7).trans
    k8).trans k9).trans k10).trans k10b).trans k11).trans k12).trans k13).trans k14).trans
    k15).trans k16).trans k17).trans k18).trans kb.shapes)

end OnBytes.Tie.Pv.Tail.Walk

namespace OnBytes.Tie.Pv.Tail
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail.Port OnBytes.Tie.Pv.Tail.Walk

variable {K : Type} [CommRing K] (ρ : Reading K)

/-- `RawRows` as the theorems on objectsF ask it, at the check of the head's sub-proof: a run of
objectsF, the state F11 at which the weights are tested and the context cT of that test; and, if cT
is a view, `RawRows` in every world that reads the four kinds of virtual row at F11 as sums of the
arrays' entries. -/
theorem rawRows_head_run (tl0 tla : HTailF2) (Fz Fa : Fork) (Tz Ta : Tail2) (nU aTX : Array Nat)
    (hb hbLine : Nat) (hS : Head.Shape) (Lh : Head.HL) (b : Head.Border) (hp : Head.HPlanH2)
    (O : Head.Owner) (cov : Head.Covered) (wsLay : WsLay) (L L' : LinkCtx) (F0 F' : Fork)
    (c c' : Ctx) (wo : WsForkOut)
    (hadd : tl0.addTreesF Fz Tz nU aTX hb hbLine = .ok (tla, Fa, Ta))
    (hrec : RecordKept tla hp.tl) (hk0 : ShapesKept Fa F0)
    (h : Head.runForkHidH2 hS Lh b hp O cov wsLay L F0 c = .ok (((wo, L'), F'), c')) :
    ∃ (funs : Array HFun) (tlA tl : HTailF2) (F7 G F10 F11 : Fork) (c7 c9 cT : Ctx),
      tlA.objectsF funs F7 c7 = .ok ((tl, G), c9) ∧
      tl.coefficientsF F10 cT = .ok (((), F11), cT) ∧
      (cT.ch.dry = false → ∀ (W : World K) (A : Nat → Nat → Nat → K),
        ReadsRaw ρ tl funs F11 W A → RawRows W tlA G funs (ρ.val G.theta) A) := by
  obtain ⟨funs, tl1, tlA, tl, F7, G, F10, F11, F12, c7, c9, cT, cT', hclosed, hrk, kS, hobj, kF,
    hco, htile⟩ := head_ran hS Lh b hp O cov wsLay L L' F0 F' c c' wo h
  have a9 := (inferInstance : Pres ShapesKept (tlA.objectsF funs)).out _ _ _ _ _ hobj
  exact ⟨funs, tlA, tl, F7, G, F10, F11, c7, c9, cT, hobj, hco, fun hv W A hW =>
    rawRows_kept ρ tl0 tla tlA tl funs Fz Fa F7 G F10 F11 F12 Tz Ta nU aTX hb hbLine
      c7 c9 cT cT cT cT' W A hadd ((hrec.trans (closeFuns_record hclosed)).trans hrk) hobj
      ((hk0.trans kS).trans a9) kF hco hv htile hW⟩

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.Walk.head_ran
#print axioms OnBytes.Tie.Pv.Tail.rawRows_head_run
