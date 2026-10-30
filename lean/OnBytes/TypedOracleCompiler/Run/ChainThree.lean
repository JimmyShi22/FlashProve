-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/ChainThree.lean: the typed verifier's chain over a file, cut as a verifier cuts it
that walks the three hash chains by three calls: three values, each of one step and one stretch with
no tail, from the three chains as read.



Why. `chain_whole` (OnBytes/TypedOracleCompiler/Run/ChainF.lean) gives the value of ONE chain over all rounds of the
batch's skeleton: front | ds₁ | joining round | ds₂ | seam | ds₃. A verifier that runs the first
chain, then the shared chain, then the last chain, each by a call of its own, has three values. Here
each is had by itself, in letters: the first round of a run is any skeleton round r with its wire w;
the stretch behind it is `SL C ds`; the run begins at any round number i.

Main names:
  `run1_line`: from the phase "first": the front's step (`chainP_firstT`, law s0), then a local
    stretch with no tail (`chain_end_lo`): the phase behind is "local" at a chain value v' whose
    bytes are the chain value behind the chain as read.
  `run2_line`: from the phase "local" at v: the joining step (`chainP_joinT`, laws sG, s4), then a
    shared stretch that ends in a sealed round, with no tail (`chain_end_shS`,
    OnBytes/TypedOracleCompiler/Run/ChainEndSh.lean): the phase behind is "shared" at THE SEAL of the stretch, with
    the slot value cS that g answered.
  `run3_line`: from the phase "shared" at v and cS: the seam's step (`chainP_f3T`, law s3), then a
    local stretch with no tail: the phase behind is "after" with the same slot value.
  `chainP_noX`: a chain that is handed no instance does not look at the round "late";
  `chain_end_lo'`: `chain_end_lo` under the condition hl below.
Each says also: what the stretch's verifier messages draw is what the reader drew (in the shared
stretch up to the seal's digest), and the typed tests of work pass as the reader's do.

THE CONDITION hl of the first and the third run: no instance is handed to the chain (a file whose
instance stands in the list of outer roots), or the round "late", in whose query the rest of an
instance is laid, is none of the stretch's rounds. SO A FILE THAT WRITES AN INSTANCE AND WHOSE ROUND
"late" STANDS IN ITS FIRST CHAIN IS NOT SERVED BY `run1_line`. At an object that has no round "late"
(late = none) hl holds.

WHAT ELSE IS ASKED: hypotheses all, none shown here. Of all three runs: hO: O's answers have 32
bytes; hkit: the kit chal fits the plan's field (`KitFits`); F : `StretchFacts`
(OnBytes/TypedOracleCompiler/Run/ChainFrom.lean), the reader's whole side: the rounds' data are the description's, K
blocks are enough for every round's verifier message, the rounds as read are the reader's trace at
`Fmt.HO O` from the chain c on, and the typed plain parts are the items read; z: the chain value at
c has 32 bytes; the law on g along the stretch (R : `RowEnd`; in the second run `RowShE`) and at the
step (s0; sG and s4; s3). Of the first and the third run also: hr, hr2: the first round's own roots
rt are as many as the trees over a slot's component in its wire (`depthJ`), and at most `maxRt`; and
hl. Of the second run also: ha: the joining round's annotation is of the kind "shared"; hj, h0: its
wire has no tree (`depthJ` and `depth0` are empty); hS: the stretch ends in a sealed round
(`SealLast`). Of `chain_end_lo'`: hO, hkit, F, the law `RowEnd`, hl, and that v has 256 bits and the
bytes of the chain value at c (hv256, hv).

Limits: what the head of OnBytes/TypedOracleCompiler/Run/ChainF.lean lists under WHAT IS NOT SAID, and the
hypotheses above. The laws on g (s0, sG, s4, s3, `RowEnd`, `RowShE`) are hypotheses: no family is
shown to have them here. That the three values are the value of one chain over all rounds is not
said here. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import OnBytes.TypedOracleCompiler.Run.ChainEndSh

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom TypedOracleCompiler.Iop _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
  TypedOracleCompiler.Run.Thin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run
open _root_.Run.Twin (allLo)
open _root_.Fmt (Chain RoundOut ChainOut Item ItemValue)
open TypedOracleCompiler.Slice (shdS wireSh)

/-! ## Without an instance the chain does not look at the round "late" -/

/-- A chain that is handed no instance lays none into any query, whatever the round "late" is. -/
theorem chainP_noX {I X : Type} {lam K : ℕ} (Lf : Unit → BatchProtocolWithLeafBody I X) (g : Fam (typedOracleFamily lam K (Lf ())))
    (early : X → X) (late late' : Option ℕ) (t : Tag) (cms : List (Dig lam)) (salt : Bits)
    (rtreq : Dig lam) :
    ∀ (S : List RS) (A : RoundSplits (up S)) (W : RoundsQueryLayout lam K (up S) A)
        (embP : PlainPart (up S) A → PlainPart (Compile.Batch.shapeOf (Lf ()) t) (annOf (Lf ()) t)) (i : ℕ)
        (ph : Phase lam) (rts : List (Dig lam)) (pls : Plains (up S)),
      chainP Lf g early late t cms none salt rtreq S A W embP i ph rts pls =
        chainP Lf g early late' t cms none salt rtreq S A W embP i ph rts pls
  | [], _, _, _, _, _, _, _ => rfl
  | _ :: S, (a, A), (w, W), embP, i, ph, rts, (pl, pls) => by
      have ih := chainP_noX Lf g early late late' t cms salt rtreq S A W
      simp only [Thin.chainP, ite_self, ih]

section Three
variable {I X : Type} (Lf : Unit → BatchProtocolWithLeafBody I X) (C : CK) (K : ℕ) (g : Fam (typedOracleFamily 256 (K + 1) (Lf ())))
  (early : X → X) (late : Option ℕ) (t : Tag) (cms : List (Dig 256)) (x : Option X) (salt : Bits)
  (rtreq : Dig 256) (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32) (P : _root_.Fmt.Plan)
  (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (hkit : KitFits P.field C K chal)
  (ds : List RD) (rs : List _root_.Fmt.Round) (ros : List RoundOut) (c : Chain)
  (roots : Array ByteArray) (i : ℕ) (rest : List (Dig 256))

include hO hkit in
/-- `chain_end_lo` (OnBytes/TypedOracleCompiler/Run/ChainFrom.lean) under a weaker condition on the round "late": no
instance is handed to the chain, or the round "late" is none of the stretch's. -/
theorem chain_end_lo' (v : Bits) (o : Option (Dig 256))
    (embP : PlainPart (uL C ds) (allLo (SL C ds)) →
      PlainPart (Compile.Batch.shapeOf (Lf ()) t) (annOf (Lf ()) t))
    (pls : Plains (uL C ds)) (F : StretchFacts O P C K ds rs ros c roots pls)
    (hrow : RowEnd Lf C K g t O c.label ds embP i (c.round + 1))
    (hv : bitsToBytes v = c.rho) (hv256 : v.length = 256)
    (hl : x = none ∨ ∀ k, k < ds.length → late ≠ some (i + k)) :
    ∃ (ρ : Rho (uL C ds)) (v' : Bits),
      chainP Lf g early late t cms x salt rtreq (SL C ds) (allLo (SL C ds)) (wiresSL C K chal ds)
          embP i (phLo o v) (rootsD ros ++ rest) pls =
        some (ρ, rtSL C ds ros, phLo o v') ∧
      drawnSL C ds ρ = ros.map (·.drawn) ∧
      passSL C ds ρ = passL (_root_.Fmt.HO O) rs ros c ∧
      bitsToBytes v' = (endOf (_root_.Fmt.HO O) rs ros c).rho ∧ v'.length = 256 := by
  rcases hl with rfl | hl
  · rw [chainP_noX Lf g early late none]
    exact chain_end_lo Lf C K g early none t cms none salt rtreq O hO P chal hkit ds rs ros i c
      roots v rest o embP pls F hrow hv hv256 fun _ _ h => nomatch h
  · exact chain_end_lo Lf C K g early late t cms x salt rtreq O hO P chal hkit ds rs ros i c roots
      v rest o embP pls F hrow hv hv256 hl

include hO hkit in
/-- **THE FIRST RUN**: the front's step, then a local stretch with no tail. rt: the front's own
roots. -/
theorem run1_line (r : RS) (w : WireRB 256 (K + 1) r.up r.lo)
    (embP : PlainPart (up (r :: SL C ds)) (r.lo, allLo (SL C ds)) →
      PlainPart (Compile.Batch.shapeOf (Lf ()) t) (annOf (Lf ()) t))
    (pl : r.Plain) (pls : Plains (uL C ds)) (rt : List (Dig 256))
    (hr : w.depthJ.length = rt.length) (hr2 : rt.length ≤ TypedOracleCompiler.Iop.maxRt)
    (F : StretchFacts O P C K ds rs ros c roots pls)
    (R : RowEnd Lf C K g t O c.label ds (fun z => embP (Sum.inr z)) (i + 1) (c.round + 1))
    (z : c.rho.size = 32)
    (s0 : (g (OracleName.fb t) (⟨i, .f1 cms (x.map early) salt, rt, embP (Sum.inl (Sum.inr pl))⟩ :
              FbIn 256 (Lf ()) t) : (Fin (K + 1) → Dig 256) × Dig 256).2 = bytesToDig c.rho)
    (hl : x = none ∨ ∀ k, k < ds.length → late ≠ some (i + 1 + k)) :
    ∃ (ρ : Rho (uL C ds)) (v' : Bits),
      chainP Lf g early late t cms x salt rtreq (r :: SL C ds) (r.lo, allLo (SL C ds))
          (w, wiresSL C K chal ds) embP i .first (rt ++ (rootsD ros ++ rest)) (pl, pls) =
        some ((w.chal (g (OracleName.fb t)
              (⟨i, .f1 cms (x.map early) salt, rt, embP (Sum.inl (Sum.inr pl))⟩ :
                FbIn 256 (Lf ()) t) : (Fin (K + 1) → Dig 256) × Dig 256).1, ρ),
          ((none, some rt), rtSL C ds ros), .loc v') ∧
      drawnSL C ds ρ = ros.map (·.drawn) ∧
      passSL C ds ρ = passL (_root_.Fmt.HO O) rs ros c ∧
      bitsToBytes v' = (endOf (_root_.Fmt.HO O) rs ros c).rho ∧ v'.length = 256 := by
  obtain ⟨ρ, v', e, d, p, hv, hv'⟩ := chain_end_lo' Lf C K g early late t cms x salt rtreq O hO P
    chal hkit ds rs ros c roots (i + 1) rest (List.ofFn (bytesToDig c.rho)) none
    (fun z => embP (Sum.inr z)) pls F R (TieTree.dig_bytes _ z) List.length_ofFn hl
  have st := chainP_firstT Lf g early late t cms x salt rtreq r (SL C ds) (allLo (SL C ds)) w
    (wiresSL C K chal ds) embP i (rt ++ (rootsD ros ++ rest)) (rootsD ros ++ rest) rt pl pls
    (takeRt_app _ rt _ hr hr2) _ s0
  exact ⟨ρ, v', st.trans (congrArg (Option.map _) e), d, p, hv, hv'⟩

include hO hkit in
/-- **THE SECOND RUN**: the joining step, then a shared stretch that ends in a sealed round, with no
tail. v: the chain value behind the first run; cS: what g answers, the slot value. -/
theorem run2_line (r : RS) (a : RAnn r.up) (ha : a.kind = Kind.sh) (w : WireRB 256 (K + 1) r.up a)
    (hj : w.depthJ = []) (h0 : w.depth0 = [])
    (embP : PlainPart (up (r :: SL C ds)) (a, annShE C ds) →
      PlainPart (Compile.Batch.shapeOf (Lf ()) t) (annOf (Lf ()) t))
    (v : Bits) (pl : r.Plain) (pls : Plains (uL C ds)) (hS : SealLast ds)
    (F : StretchFacts O P C K ds rs ros c roots pls)
    (R : RowShE Lf C K g t O c.label ds (fun z => embP (Sum.inr z)) (i + 1) (c.round + 1))
    (z : c.rho.size = 32) (cS : Dig 256)
    (sG : (g (OracleName.g t) (⟨i, v, [], embP (Sum.inl (Sum.inr (a.plain pl).2))⟩ : JoiningRoundQuery 256 (Lf ()) t) :
      Dig 256) = cS)
    (s4 : (g (OracleName.fb t) (⟨i, .f4 cms (List.ofFn rtreq), [],
                embP (Sum.inl (Sum.inl (a.plain pl).1))⟩ : FbIn 256 (Lf ()) t) :
      (Fin (K + 1) → Dig 256) × Dig 256).2 = bytesToDig c.rho) :
    ∃ ρ : Rho (uL C ds),
      chainP Lf g early late t cms x salt rtreq (r :: SL C ds) (a, annShE C ds)
          (w, wShE C K chal ds) embP i (.loc v) (rootsD ros ++ rest) (pl, pls) =
        some ((w.chal (g (OracleName.fb t) (⟨i, .f4 cms (List.ofFn rtreq), [],
                      embP (Sum.inl (Sum.inl (a.plain pl).1))⟩ : FbIn 256 (Lf ()) t) :
                (Fin (K + 1) → Dig 256) × Dig 256).1, ρ),
          ((some [], some []), rtShL C ds ros),
          .shr (List.ofFn (bytesToDig (sealOf (_root_.Fmt.HO O) rs ros c))) cS) ∧
      SameButSeal (drawnSL C ds ρ) (ros.map (·.drawn)) ∧
      passSL C ds ρ = passL (_root_.Fmt.HO O) rs ros c := by
  obtain ⟨ρ, v', e, d, p, hv⟩ := chain_end_shS Lf C K g early late t cms x salt rtreq O hO P chal
    hkit ds rs ros (i + 1) c roots (List.ofFn (bytesToDig c.rho)) rest cS
    (fun z => embP (Sum.inr z)) pls hS F R (TieTree.dig_bytes _ z) List.length_ofFn
  subst hv
  have st := chainP_joinT Lf g early late t cms x salt rtreq r a ha (SL C ds) (annShE C ds) w
    (wShE C K chal ds) embP i v (rootsD ros ++ rest) pl pls hj h0 cS (bytesToDig c.rho) sG s4
  exact ⟨ρ, st.trans (congrArg (Option.map _) e), d, p⟩

include hO hkit in
/-- **THE THIRD RUN**: the seam's step, then a local stretch with no tail. v: the chain value behind
the second run, the seal; cS: the slot value; rt: the seam's own roots. -/
theorem run3_line (r : RS) (w : WireRB 256 (K + 1) r.up r.lo)
    (embP : PlainPart (up (r :: SL C ds)) (r.lo, allLo (SL C ds)) →
      PlainPart (Compile.Batch.shapeOf (Lf ()) t) (annOf (Lf ()) t))
    (v : Bits) (cS : Dig 256) (pl : r.Plain) (pls : Plains (uL C ds)) (rt : List (Dig 256))
    (hr : w.depthJ.length = rt.length) (hr2 : rt.length ≤ TypedOracleCompiler.Iop.maxRt)
    (F : StretchFacts O P C K ds rs ros c roots pls)
    (R : RowEnd Lf C K g t O c.label ds (fun z => embP (Sum.inr z)) (i + 1) (c.round + 1))
    (z : c.rho.size = 32)
    (s3 : (g (OracleName.fb t) (⟨i, .f3 v (List.ofFn cS), rt, embP (Sum.inl (Sum.inr pl))⟩ :
              FbIn 256 (Lf ()) t) : (Fin (K + 1) → Dig 256) × Dig 256).2 = bytesToDig c.rho)
    (hl : x = none ∨ ∀ k, k < ds.length → late ≠ some (i + 1 + k)) :
    ∃ (ρ : Rho (uL C ds)) (v' : Bits),
      chainP Lf g early late t cms x salt rtreq (r :: SL C ds) (r.lo, allLo (SL C ds))
          (w, wiresSL C K chal ds) embP i (.shr v cS) (rt ++ (rootsD ros ++ rest)) (pl, pls) =
        some ((w.chal (g (OracleName.fb t)
              (⟨i, .f3 v (List.ofFn cS), rt, embP (Sum.inl (Sum.inr pl))⟩ :
                FbIn 256 (Lf ()) t) : (Fin (K + 1) → Dig 256) × Dig 256).1, ρ),
          ((none, some rt), rtSL C ds ros), .aft v' cS) ∧
      drawnSL C ds ρ = ros.map (·.drawn) ∧
      passSL C ds ρ = passL (_root_.Fmt.HO O) rs ros c ∧
      bitsToBytes v' = (endOf (_root_.Fmt.HO O) rs ros c).rho ∧ v'.length = 256 := by
  obtain ⟨ρ, v', e, d, p, hv, hv'⟩ := chain_end_lo' Lf C K g early late t cms x salt rtreq O hO P
    chal hkit ds rs ros c roots (i + 1) rest (List.ofFn (bytesToDig c.rho)) (some cS)
    (fun z => embP (Sum.inr z)) pls F R (TieTree.dig_bytes _ z) List.length_ofFn hl
  have st := chainP_f3T Lf g early late t cms x salt rtreq r (SL C ds) (allLo (SL C ds)) w
    (wiresSL C K chal ds) embP i v cS (rt ++ (rootsD ros ++ rest)) (rootsD ros ++ rest) rt pl pls
    (takeRt_app _ rt _ hr hr2) _ s3
  exact ⟨ρ, v', st.trans (congrArg (Option.map _) e), d, p, hv, hv'⟩

end Three

end TypedOracleCompiler.Run.PQ
