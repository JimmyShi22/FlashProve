-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Joined/K/RunsLine.lean: the three chains of a file's verifier, under fixed oracle
functions, at a file whose rounds and wire records are those of written rounds: their values from
the three chains as read.

A part of the tie between a reader of a file's bytes and the second form of the compiler's verifier
side (lean/OnBytes/TypedOracleCompiler/Joined/): it brings that verifier's yes, under fixed oracle functions, down
to conditions on what was read and on how these functions answer. That the reading of a real file,
and oracle functions made from the programs' hash, meet these conditions is not shown in this
folder.


OnBytes/TypedOracleCompiler/Run/ChainThree.lean has, for written rounds (`SL C ds`), the value of a step and a
stretch with no tail, three times, from a chain as read. It speaks of `chainP`, a function of the
oracle functions g, at the annotations `allLo` and `annShE`. The verifier of a file
(OnBytes/TypedOracleCompiler/Joined/Verifier.lean) runs `recomputeChain` at the annotations `RoundSplits.allLocal` and
`RoundSplits.const (RAnn.ofShared .sh)`. The two pairs of annotations are equal by a lemma, not by
unfolding. Here the values are carried over that equation.

Main names:
  `wTo`, `pTo`: a wire record, a plain part, carried along an equation of annotations.
  `chainB_ann`: the chain at the carried wire record is the chain at the wire record itself.
  `chainB_det`: under g the chain over written rounds has the value `chainP`.
  `count_rtSL`, `count_rtShL`: a stretch's roots round by round are as many as the chain as read
    has.
  `chainsL`: the rounds of a file whose three stretches are written rounds. `len_c₁`, `len_c₁₂`: the
    numbers of the joining round and of the seam, as the verifier writes them, from the lists'
    lengths.
  `det_run₁`, `det_run₂`, `det_run₃`: the values of the three chains under g.
  `whole_line`: the three together; so the whole chain's value under g (`whole_iff`,
    OnBytes/TypedOracleCompiler/Joined/WholeAt.lean), whose last phase holds the slot value that g answered.

Limits: that the file's wire records are the written rounds' is a hypothesis (`hw`), an equation
that a maker of the file is to meet. The laws on g are hypotheses, as in ChainThree.lean. One kit
(C, K, chal) serves all three chains: it must fit the field of each chain's plan. The first
and the third chain are served only if the file writes no instance into its queries, or the round
"late" is none of their stretches' rounds: a file that writes an instance and whose round "late"
stands in its first chain is not served. At an object that has no round "late" the condition holds.

Terms: lean/GLOSSARY.md.
-/
import OnBytes.TypedOracleCompiler.Run.ChainThree
import OnBytes.TypedOracleCompiler.Run.LaxThin
import OnBytes.TypedOracleCompiler.Joined.WholeAt

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Joined.K
open Rom TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin TypedOracleCompiler.Run.Thin
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open TypedOracleCompiler.Run.PQ
open _root_.Run.PQ (CK)
open _root_.Run (bytesToDig bitsToBytes)
open _root_.Run.Twin (RS up allLo allLo_eq)
open _root_.Fmt (Chain RoundOut)
open _root_.Compile.Joined (Chains Desc)

/-! ## Along an equation of annotations -/

section Ann
variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X} {s : Shape} {A A' : RoundSplits s}

/-- a wire record, carried along an equation of annotations -/
def wTo (h : A = A') (W : RoundsQueryLayout lam K s A) : RoundsQueryLayout lam K s A' := h ▸ W

/-- a plain part, carried along an equation of annotations -/
def pTo (h : A = A') (z : PlainPart s A) : PlainPart s A' := h ▸ z

/-- The chain at the carried wire record is the chain at the wire record itself; a plain part is
carried before it is written. -/
theorem chainB_ann (h : A = A') (t : Tag) (cms : List (Dig lam)) (x : Option X) (salt : Bits)
    (rtreq : Dig lam) (W : RoundsQueryLayout lam K s A) (embP : PlainPart s A' → PlainPart (shapeOf L t) (annOf L t))
    (i : ℕ) (ph : Phase lam) (rts : List (Dig lam)) (pls : Plains s) :
    recomputeChain t cms x salt rtreq s A' (wTo h W) embP i ph rts pls =
      recomputeChain t cms x salt rtreq s A W (fun z => embP (pTo h z)) i ph rts pls := by
  subst h
  rfl

/-- Under g the chain over written rounds has the value `chainP`, from any round and phase on. -/
theorem chainB_det (g : Fam (typedOracleFamily lam K L)) (t : Tag) (cms : List (Dig lam)) (x : Option X)
    (salt : Bits) (rtreq : Dig lam) (S : List RS) (A : RoundSplits (up S)) (W : RoundsQueryLayout lam K (up S) A)
    (embP : PlainPart (up S) A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : Phase lam)
    (rts : List (Dig lam)) (pls : Plains (up S)) :
    (recomputeChain t cms x salt rtreq (up S) A W embP i ph rts pls).det g =
      chainP (fun _ => L) g L.early L.late t cms x salt rtreq S A W embP i ph rts pls := by
  rw [← chainT_eq]
  exact (twd_chain I X lam K L g L.early L.late t cms x salt rtreq S A W embP i ph rts pls).trans
    (thin_chain I X lam K L g L.early L.late t cms x salt rtreq S A W embP i ph rts pls).symm

end Ann

/-! ## How many roots a stretch has taken -/

theorem count_rtSL (C : CK) : ∀ (ds : List RD) (ros : List RoundOut) (pls : Plains (uL C ds)),
    plainsSL C ds ros = some pls → RootsOfChain.count (uL C ds) (rtSL C ds ros) = (rootsD ros).length
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp [plainsSL] at h
  | _ :: _, [], _, h => by simp [plainsSL] at h
  | d :: ds, ro :: ros, _, h => by
    obtain ⟨_, r, -, h1, -⟩ := plainsSL_cons_some C h
    have ih := count_rtSL C ds ros r h1
    show 0 + ((_root_.Fmt.rootsOf ro.vals).map bytesToDig).length +
      RootsOfChain.count (uL C ds) (rtSL C ds ros) = _
    rw [ih]
    simp [rootsD, List.flatMap_cons]

theorem count_rtShL (C : CK) : ∀ (ds : List RD) (ros : List RoundOut) (pls : Plains (uL C ds)),
    plainsSL C ds ros = some pls → RootsOfChain.count (uL C ds) (rtShL C ds ros) = (rootsD ros).length
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp [plainsSL] at h
  | _ :: _, [], _, h => by simp [plainsSL] at h
  | d :: ds, ro :: ros, _, h => by
    obtain ⟨_, r, -, h1, -⟩ := plainsSL_cons_some C h
    have ih := count_rtShL C ds ros r h1
    show ((_root_.Fmt.rootsOf ro.vals).map bytesToDig).length + 0 +
      RootsOfChain.count (uL C ds) (rtShL C ds ros) = _
    rw [ih]
    simp [rootsD, List.flatMap_cons]

/-! ## A file whose stretches are written rounds -/

/-- The rounds of a file whose three stretches are written rounds; the front, the joining round and
the seam are any skeleton rounds. -/
@[reducible] def chainsL (C : CK) (rF rJ r3 : RS) (aJ : RAnn rJ.up) (ds₁ ds₂ ds₃ : List RD) :
    Chains where
  rF := rF.up
  s₁ := uL C ds₁
  rJ := rJ.up
  s₂ := uL C ds₂
  r3 := r3.up
  s₃ := uL C ds₃
  aJ := aJ

/-- written rounds are as many as their data -/
theorem length_uL (C : CK) : ∀ ds : List RD, (uL C ds).length = ds.length
  | [] => rfl
  | _ :: ds => congrArg (· + 1) (length_uL C ds)

/-- the number of the joining round -/
theorem len_c₁ (C : CK) (rF rJ r3 : RS) (aJ : RAnn rJ.up) (ds₁ ds₂ ds₃ : List RD) :
    0 + (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₁.length = 1 + ds₁.length := by
  show 0 + ((uL C ds₁).length + 1) = _
  rw [length_uL]
  omega

/-- the number of the seam -/
theorem len_c₁₂ (C : CK) (rF rJ r3 : RS) (aJ : RAnn rJ.up) (ds₁ ds₂ ds₃ : List RD) :
    0 + (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₁.length +
      (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₂.length = 1 + ds₁.length + 1 + ds₂.length := by
  show 0 + ((uL C ds₁).length + 1) + ((uL C ds₂).length + 1) = _
  rw [length_uL, length_uL]
  omega

/-- the second chain's annotation, at written rounds -/
abbrev annW₂ (C : CK) (rJ : RS) (aJ : RAnn rJ.up) (ds₂ : List RD) : RoundSplits (up (rJ :: SL C ds₂)) :=
  (aJ, annShE C ds₂)

/-- it is the file's -/
theorem annL₂ (C : CK) (rF rJ r3 : RS) (aJ : RAnn rJ.up) (ds₁ ds₂ ds₃ : List RD) :
    annW₂ C rJ aJ ds₂ = (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).A₂ :=
  congrArg (Prod.mk aJ) (annShE_eq C ds₂)

/-- the second chain's wire records, at written rounds -/
abbrev wireW₂ (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k) (rJ : RS)
    (aJ : RAnn rJ.up) (wJ : WireRB 256 (K + 1) rJ.up aJ) (ds₂ : List RD) :
    RoundsQueryLayout 256 (K + 1) (up (rJ :: SL C ds₂)) (annW₂ C rJ aJ ds₂) :=
  (wJ, wShE C K chal ds₂)

section Runs
variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {Y : Type} {E : ExtSpec} {C : CK} {K : ℕ} {rF rJ r3 : RS}
  {aJ : RAnn rJ.up} {ds₁ ds₂ ds₃ : List RD} {t : Tag}
  {D : Desc (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃) Y E} {wq : ProtocolQueryLayout 256 (K + 1) D.batch}
  {embP : PlainPart (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).sh (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).ann →
    PlainPart (shapeOf L t) (annOf L t)}
  {xin : Y → Option X} {cms : List (Dig 256)} {x : Y} {π : OneProtocolProof 256 D.batch}
  (g : Fam (typedOracleFamily 256 (K + 1) L)) (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32)
  (P : _root_.Fmt.Plan) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
  (hkit : KitFits P.field C K chal) (rs : List _root_.Fmt.Round) (ros : List RoundOut) (c : Chain)
  (roots : Array ByteArray) (rest : List (Dig 256))

/-- how a plain part of the first chain's rounds is written, at the written rounds' annotation -/
def embL₁
    (embP : PlainPart (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).sh (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).ann →
      PlainPart (shapeOf L t) (annOf L t)) :
    PlainPart (up (rF :: SL C ds₁)) (rF.lo, allLo (SL C ds₁)) → PlainPart (shapeOf L t) (annOf L t) :=
  fun z => emb₁ t embP (pTo (allLo_eq (rF :: SL C ds₁)) z)

include hO hkit in
/-- **The first chain's value under g.** hw: its wire records are the front's wF and the written
rounds'. rt: the front's own roots. -/
theorem det_run₁ (wF : WireRB 256 (K + 1) rF.up rF.lo)
    (hw : wire₁ wq = wTo (allLo_eq (rF :: SL C ds₁)) (wF, wiresSL C K chal ds₁))
    (rt : List (Dig 256)) (hroots : π.roots = rt ++ (rootsD ros ++ rest))
    (hr : wF.depthJ.length = rt.length) (hr2 : rt.length ≤ TypedOracleCompiler.Iop.maxRt)
    (F : StretchFacts O P C K ds₁ rs ros c roots (pls₁ D π).2)
    (R : RowEnd (fun _ => L) C K g t O c.label ds₁
      (fun z => embL₁ embP (Sum.inr z)) (0 + 1) (c.round + 1))
    (z : c.rho.size = 32)
    (s0 : (g (OracleName.fb t) (⟨0, .f1 cms ((xin x).map L.early) π.salt, rt,
                embL₁ embP (Sum.inl (Sum.inr (pls₁ D π).1))⟩ :
              FbIn 256 L t) : (Fin (K + 1) → Dig 256) × Dig 256).2 = bytesToDig c.rho)
    (hl : xin x = none ∨ ∀ k, k < ds₁.length → L.late ≠ some (0 + 1 + k)) :
    ∃ (c0 : rF.Chal) (ρ : Rho (uL C ds₁)) (v' : Bits),
      (run₁ t D wq embP xin cms x π).det g =
        some ((c0, ρ), ((none, some rt), rtSL C ds₁ ros), .loc v') ∧
      drawnSL C ds₁ ρ = ros.map (·.drawn) ∧
      passSL C ds₁ ρ = passL (_root_.Fmt.HO O) rs ros c ∧
      bitsToBytes v' = (endOf (_root_.Fmt.HO O) rs ros c).rho ∧ v'.length = 256 := by
  obtain ⟨ρ, v', e, d, p, hv, hv'⟩ := run1_line (fun _ => L) C K g L.early L.late t cms (xin x)
    π.salt π.rtreq O hO P chal hkit ds₁ rs ros c roots 0 rest rF wF
    (embL₁ embP) (pls₁ D π).1 (pls₁ D π).2 rt hr hr2
    F R z s0 hl
  have h0 : (run₁ t D wq embP xin cms x π).det g =
      chainP (fun _ => L) g L.early L.late t cms (xin x) π.salt π.rtreq (rF :: SL C ds₁)
        (rF.lo, allLo (SL C ds₁)) (wF, wiresSL C K chal ds₁) (embL₁ embP) 0 .first
        (rt ++ (rootsD ros ++ rest)) ((pls₁ D π).1, (pls₁ D π).2) := by
    unfold run₁
    rw [hw, hroots]
    exact (congrArg (fun q => q.det g) (chainB_ann (allLo_eq (rF :: SL C ds₁)) t cms (xin x)
      π.salt π.rtreq (wF, wiresSL C K chal ds₁) (emb₁ t embP) 0 .first _ (pls₁ D π))).trans
      (chainB_det g t cms (xin x) π.salt π.rtreq (rF :: SL C ds₁) (allLo (rF :: SL C ds₁))
        (wF, wiresSL C K chal ds₁) _ 0 .first _ (pls₁ D π))
  exact ⟨_, ρ, v', h0.trans e, d, p, hv, hv'⟩

/-- how a plain part of the second chain's rounds is written, at the written rounds' annotation -/
def embL₂
    (embP : PlainPart (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).sh (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).ann →
      PlainPart (shapeOf L t) (annOf L t)) :
    PlainPart (up (rJ :: SL C ds₂)) (annW₂ C rJ aJ ds₂) → PlainPart (shapeOf L t) (annOf L t) :=
  fun z => emb₂ t embP (pTo (annL₂ C rF rJ r3 aJ ds₁ ds₂ ds₃) z)

/-- the same for the third chain's rounds -/
def embL₃
    (embP : PlainPart (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).sh (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).ann →
      PlainPart (shapeOf L t) (annOf L t)) :
    PlainPart (up (r3 :: SL C ds₃)) (r3.lo, allLo (SL C ds₃)) → PlainPart (shapeOf L t) (annOf L t) :=
  fun z => emb₃ t embP (pTo (allLo_eq (r3 :: SL C ds₃)) z)

include hO hkit in
/-- **The second chain's value under g**, from what the first chain yielded: a, which ended in the
phase "local" at v and left the roots `rootsD ros ++ rest`. hw: the wire records are the joining
round's wJ and the written rounds'. cS: what g answers, the slot value. -/
theorem det_run₂ (wJ : WireRB 256 (K + 1) rJ.up aJ) (haJ : aJ.kind = Kind.sh)
    (hj : wJ.depthJ = []) (h0 : wJ.depth0 = [])
    (hw : wire₂ wq = wTo (annL₂ C rF rJ r3 aJ ds₁ ds₂ ds₃) (wireW₂ C K chal rJ aJ wJ ds₂))
    (a : Out 256 (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₁) (v : Bits) (ha : a.2.2 = .loc v)
    (hroots : π.roots.drop (RootsOfChain.count (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₁ a.2.1) =
      rootsD ros ++ rest)
    (hS : SealLast ds₂) (F : StretchFacts O P C K ds₂ rs ros c roots (pls₂ D π).2)
    (R : RowShE (fun _ => L) C K g t O c.label ds₂ (fun z => embL₂ embP (Sum.inr z))
      (0 + (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₁.length + 1) (c.round + 1))
    (z : c.rho.size = 32) (cS : Dig 256)
    (sG : (g (OracleName.g t) (⟨0 + (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₁.length, v, [],
                embL₂ embP (Sum.inl (Sum.inr (aJ.plain (pls₂ D π).1).2))⟩ : JoiningRoundQuery 256 L t) : Dig 256) = cS)
    (s4 : (g (OracleName.fb t) (⟨0 + (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₁.length,
                .f4 cms (List.ofFn π.rtreq), [], embL₂ embP (Sum.inl (Sum.inl (aJ.plain (pls₂ D π).1).1))⟩ :
              FbIn 256 L t) : (Fin (K + 1) → Dig 256) × Dig 256).2 = bytesToDig c.rho) :
    ∃ (c0 : rJ.Chal) (ρ : Rho (uL C ds₂)),
      (run₂ t D wq embP xin cms x π a).det g =
        some ((c0, ρ), ((some [], some []), rtShL C ds₂ ros),
          .shr (List.ofFn (bytesToDig (sealOf (_root_.Fmt.HO O) rs ros c))) cS) ∧
      SameButSeal (drawnSL C ds₂ ρ) (ros.map (·.drawn)) ∧
      passSL C ds₂ ρ = passL (_root_.Fmt.HO O) rs ros c := by
  obtain ⟨ρ, e, d, p⟩ := run2_line (fun _ => L) C K g L.early L.late t cms (xin x) π.salt π.rtreq
    O hO P chal hkit ds₂ rs ros c roots (0 + (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₁.length) rest rJ
    aJ haJ wJ hj h0 (embL₂ embP) v (pls₂ D π).1 (pls₂ D π).2 hS F R z cS sG s4
  have h1 : (run₂ t D wq embP xin cms x π a).det g =
      chainP (fun _ => L) g L.early L.late t cms (xin x) π.salt π.rtreq (rJ :: SL C ds₂)
        (aJ, annShE C ds₂) (wJ, wShE C K chal ds₂) (embL₂ embP)
        (0 + (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₁.length) (.loc v) (rootsD ros ++ rest)
        ((pls₂ D π).1, (pls₂ D π).2) := by
    unfold run₂
    rw [hw, hroots, ha]
    exact (congrArg (fun q => q.det g) (chainB_ann
      (annL₂ C rF rJ r3 aJ ds₁ ds₂ ds₃) t cms (xin x) π.salt π.rtreq
      (wireW₂ C K chal rJ aJ wJ ds₂) (emb₂ t embP) _ (.loc v) _ (pls₂ D π))).trans
      (chainB_det g t cms (xin x) π.salt π.rtreq (rJ :: SL C ds₂) (aJ, annShE C ds₂)
        (wJ, wShE C K chal ds₂) _ _ (.loc v) _ (pls₂ D π))
  exact ⟨_, ρ, h1.trans e, d, p⟩

include hO hkit in
/-- **The third chain's value under g**, from what the first two yielded: b ended in the phase
"shared" at v with the slot value cS; the two left the roots `rt ++ (rootsD ros ++ rest)`. hw: the
wire records are the seam's w3 and the written rounds'. rt: the seam's own roots. -/
theorem det_run₃ (w3 : WireRB 256 (K + 1) r3.up r3.lo)
    (hw : wire₃ wq = wTo (allLo_eq (r3 :: SL C ds₃)) (w3, wiresSL C K chal ds₃))
    (a : Out 256 (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₁)
    (b : Out 256 (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₂) (v : Bits) (cS : Dig 256)
    (hb : b.2.2 = .shr v cS) (rt : List (Dig 256))
    (hroots : (π.roots.drop (RootsOfChain.count (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₁ a.2.1)).drop
      (RootsOfChain.count (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₂ b.2.1) = rt ++ (rootsD ros ++ rest))
    (hr : w3.depthJ.length = rt.length) (hr2 : rt.length ≤ TypedOracleCompiler.Iop.maxRt)
    (F : StretchFacts O P C K ds₃ rs ros c roots (pls₃ D π).2)
    (R : RowEnd (fun _ => L) C K g t O c.label ds₃ (fun z => embL₃ embP (Sum.inr z))
      (0 + (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₁.length +
        (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₂.length + 1) (c.round + 1))
    (z : c.rho.size = 32)
    (s3 : (g (OracleName.fb t) (⟨0 + (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₁.length +
                (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₂.length, .f3 v (List.ofFn cS), rt,
                embL₃ embP (Sum.inl (Sum.inr (pls₃ D π).1))⟩ : FbIn 256 L t) :
      (Fin (K + 1) → Dig 256) × Dig 256).2 = bytesToDig c.rho)
    (hl : xin x = none ∨ ∀ k, k < ds₃.length →
      L.late ≠ some (0 + (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₁.length +
        (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₂.length + 1 + k)) :
    ∃ (c0 : r3.Chal) (ρ : Rho (uL C ds₃)) (v' : Bits),
      (run₃ t D wq embP xin cms x π a b).det g =
        some ((c0, ρ), ((none, some rt), rtSL C ds₃ ros), .aft v' cS) ∧
      drawnSL C ds₃ ρ = ros.map (·.drawn) ∧
      passSL C ds₃ ρ = passL (_root_.Fmt.HO O) rs ros c := by
  obtain ⟨ρ, v', e, d, p, -, -⟩ := run3_line (fun _ => L) C K g L.early L.late t cms (xin x)
    π.salt π.rtreq O hO P chal hkit ds₃ rs ros c roots
    (0 + (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₁.length +
      (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₂.length) rest r3 w3 (embL₃ embP) v cS (pls₃ D π).1
    (pls₃ D π).2 rt hr hr2 F R z s3 hl
  have h1 : (run₃ t D wq embP xin cms x π a b).det g =
      chainP (fun _ => L) g L.early L.late t cms (xin x) π.salt π.rtreq (r3 :: SL C ds₃)
        (r3.lo, allLo (SL C ds₃)) (w3, wiresSL C K chal ds₃) (embL₃ embP)
        (0 + (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₁.length +
          (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₂.length) (.shr v cS)
        (rt ++ (rootsD ros ++ rest)) ((pls₃ D π).1, (pls₃ D π).2) := by
    unfold run₃
    rw [hw, hroots, hb]
    exact (congrArg (fun q => q.det g) (chainB_ann (allLo_eq (r3 :: SL C ds₃)) t cms (xin x)
      π.salt π.rtreq (w3, wiresSL C K chal ds₃) (emb₃ t embP) _ (.shr v cS) _ (pls₃ D π))).trans
      (chainB_det g t cms (xin x) π.salt π.rtreq (r3 :: SL C ds₃) (allLo (r3 :: SL C ds₃))
        (w3, wiresSL C K chal ds₃) _ _ (.shr v cS) _ (pls₃ D π))
  exact ⟨_, ρ, v', h1.trans e, d, p⟩

end Runs

/-! ## The three together, and the whole chain -/

section Whole
variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {Y : Type} {E : ExtSpec} {C : CK} {K : ℕ} {rF rJ r3 : RS}
  {aJ : RAnn rJ.up} {ds₁ ds₂ ds₃ : List RD} {t : Tag}
  {D : Desc (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃) Y E} {wq : ProtocolQueryLayout 256 (K + 1) D.batch}
  {embP : PlainPart (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).sh (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).ann →
    PlainPart (shapeOf L t) (annOf L t)}
  {xin : Y → Option X} {cms : List (Dig 256)} {x : Y} {π : OneProtocolProof 256 D.batch}
  (g : Fam (typedOracleFamily 256 (K + 1) L)) (O : ByteArray → ByteArray) (hO : ∀ s, (O s).size = 32)
  (P₁ P₂ P₃ : _root_.Fmt.Plan) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
  (hkit₁ : KitFits P₁.field C K chal) (hkit₂ : KitFits P₂.field C K chal)
  (hkit₃ : KitFits P₃.field C K chal)

include hO hkit₁ hkit₂ hkit₃ in
/-- **THE THREE CHAINS' VALUES, AND THE WHOLE CHAIN'S, UNDER g, FROM THE THREE CHAINS AS READ.**
Each chain under its own plan. The list of roots of the proof string is: the front's, the first
chain's, the shared chain's, the seam's, the last chain's, and a rest. The last phase holds the slot
value cS, which g answers at the chain value behind the first chain. -/
theorem whole_line (wF : WireRB 256 (K + 1) rF.up rF.lo) (wJ : WireRB 256 (K + 1) rJ.up aJ)
    (w3 : WireRB 256 (K + 1) r3.up r3.lo) (haJ : aJ.kind = Kind.sh) (hj : wJ.depthJ = [])
    (h0 : wJ.depth0 = [])
    (hw₁ : wire₁ wq = wTo (allLo_eq (rF :: SL C ds₁)) (wF, wiresSL C K chal ds₁))
    (hw₂ : wire₂ wq = wTo (annL₂ C rF rJ r3 aJ ds₁ ds₂ ds₃) (wireW₂ C K chal rJ aJ wJ ds₂))
    (hw₃ : wire₃ wq = wTo (allLo_eq (r3 :: SL C ds₃)) (w3, wiresSL C K chal ds₃))
    (rtF rt3 rest : List (Dig 256)) (rs₁ rs₂ rs₃ : List _root_.Fmt.Round)
    (ros₁ ros₂ ros₃ : List RoundOut) (c₁ c₂ c₃ : Chain) (ro₁ ro₂ ro₃ : Array ByteArray)
    (hroots : π.roots =
      rtF ++ (rootsD ros₁ ++ (rootsD ros₂ ++ (rt3 ++ (rootsD ros₃ ++ rest)))))
    (hrF : wF.depthJ.length = rtF.length) (hrF2 : rtF.length ≤ TypedOracleCompiler.Iop.maxRt)
    (hr3 : w3.depthJ.length = rt3.length) (hr32 : rt3.length ≤ TypedOracleCompiler.Iop.maxRt)
    (F₁ : StretchFacts O P₁ C K ds₁ rs₁ ros₁ c₁ ro₁ (pls₁ D π).2)
    (F₂ : StretchFacts O P₂ C K ds₂ rs₂ ros₂ c₂ ro₂ (pls₂ D π).2)
    (F₃ : StretchFacts O P₃ C K ds₃ rs₃ ros₃ c₃ ro₃ (pls₃ D π).2) (hS : SealLast ds₂)
    (R₁ : RowEnd (fun _ => L) C K g t O c₁.label ds₁ (fun z => embL₁ embP (Sum.inr z)) (0 + 1)
      (c₁.round + 1))
    (R₂ : RowShE (fun _ => L) C K g t O c₂.label ds₂ (fun z => embL₂ embP (Sum.inr z))
      (0 + (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₁.length + 1) (c₂.round + 1))
    (R₃ : RowEnd (fun _ => L) C K g t O c₃.label ds₃ (fun z => embL₃ embP (Sum.inr z))
      (0 + (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₁.length +
        (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₂.length + 1) (c₃.round + 1))
    (z₁ : c₁.rho.size = 32) (z₂ : c₂.rho.size = 32) (z₃ : c₃.rho.size = 32) (cS : Dig 256)
    (s0 : (g (OracleName.fb t) (⟨0, .f1 cms ((xin x).map L.early) π.salt, rtF,
                embL₁ embP (Sum.inl (Sum.inr (pls₁ D π).1))⟩ : FbIn 256 L t) :
      (Fin (K + 1) → Dig 256) × Dig 256).2 = bytesToDig c₁.rho)
    (sG : ∀ ρ : Bits, ρ.length = 256 →
      bitsToBytes ρ = (endOf (_root_.Fmt.HO O) rs₁ ros₁ c₁).rho →
      (g (OracleName.g t) (⟨0 + (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₁.length, ρ, [],
                embL₂ embP (Sum.inl (Sum.inr (aJ.plain (pls₂ D π).1).2))⟩ : JoiningRoundQuery 256 L t) : Dig 256) = cS)
    (s4 : (g (OracleName.fb t) (⟨0 + (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₁.length,
                .f4 cms (List.ofFn π.rtreq), [], embL₂ embP (Sum.inl (Sum.inl (aJ.plain (pls₂ D π).1).1))⟩ :
              FbIn 256 L t) : (Fin (K + 1) → Dig 256) × Dig 256).2 = bytesToDig c₂.rho)
    (s3 : (g (OracleName.fb t) (⟨0 + (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₁.length +
                (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₂.length,
                .f3 (List.ofFn (bytesToDig (sealOf (_root_.Fmt.HO O) rs₂ ros₂ c₂))) (List.ofFn cS), rt3,
                embL₃ embP (Sum.inl (Sum.inr (pls₃ D π).1))⟩ : FbIn 256 L t) :
      (Fin (K + 1) → Dig 256) × Dig 256).2 = bytesToDig c₃.rho)
    (hl₁ : xin x = none ∨ ∀ k, k < ds₁.length → L.late ≠ some (0 + 1 + k))
    (hl₃ : xin x = none ∨ ∀ k, k < ds₃.length →
      L.late ≠ some (0 + (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₁.length +
        (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₂.length + 1 + k)) :
    ∃ (a : Out 256 (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₁)
      (b : Out 256 (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₂)
      (e : Out 256 (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₃) (v' : Bits),
      (run₁ t D wq embP xin cms x π).det g = some a ∧
      (run₂ t D wq embP xin cms x π a).det g = some b ∧
      (run₃ t D wq embP xin cms x π a b).det g = some e ∧
      (recomputeChainOfProof t D.batch wq embP xin cms x π).det g = some (glue a b e) ∧
      (glue a b e).2.2 = .aft v' cS ∧
      a.2.1 = ((none, some rtF), rtSL C ds₁ ros₁) ∧
      b.2.1 = ((some [], some []), rtShL C ds₂ ros₂) ∧
      e.2.1 = ((none, some rt3), rtSL C ds₃ ros₃) ∧
      drawnSL C ds₁ a.1.2 = ros₁.map (·.drawn) ∧
      SameButSeal (drawnSL C ds₂ b.1.2) (ros₂.map (·.drawn)) ∧
      drawnSL C ds₃ e.1.2 = ros₃.map (·.drawn) ∧
      passSL C ds₁ a.1.2 = passL (_root_.Fmt.HO O) rs₁ ros₁ c₁ ∧
      passSL C ds₂ b.1.2 = passL (_root_.Fmt.HO O) rs₂ ros₂ c₂ ∧
      passSL C ds₃ e.1.2 = passL (_root_.Fmt.HO O) rs₃ ros₃ c₃ := by
  obtain ⟨cF, ρ₁, v₁, e1, d1, p1, hv1, hv1l⟩ := det_run₁ g O hO P₁ chal hkit₁ rs₁ ros₁ c₁ ro₁
    (rootsD ros₂ ++ (rt3 ++ (rootsD ros₃ ++ rest))) wF hw₁ rtF hroots hrF hrF2 F₁ R₁ z₁ s0 hl₁
  have k1 : RootsOfChain.count (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₁
      ((none, some rtF), rtSL C ds₁ ros₁) = (rtF ++ rootsD ros₁).length := by
    show 0 + rtF.length + RootsOfChain.count (uL C ds₁) (rtSL C ds₁ ros₁) = _
    rw [count_rtSL C ds₁ ros₁ _ F₁.plains, List.length_append]
    omega
  have hd2 : π.roots.drop (RootsOfChain.count (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₁
      ((none, some rtF), rtSL C ds₁ ros₁)) = rootsD ros₂ ++ (rt3 ++ (rootsD ros₃ ++ rest)) := by
    rw [hroots, k1, ← List.append_assoc]
    exact List.drop_left' rfl
  obtain ⟨cJ, ρ₂, e2, d2, p2⟩ := det_run₂ g O hO P₂ chal hkit₂ rs₂ ros₂ c₂ ro₂
    (rt3 ++ (rootsD ros₃ ++ rest)) wJ haJ hj h0 hw₂
    ((cF, ρ₁), ((none, some rtF), rtSL C ds₁ ros₁), .loc v₁) v₁ rfl hd2 hS F₂ R₂ z₂ cS
    (sG v₁ hv1l hv1) s4
  have k2 : RootsOfChain.count (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₂
      ((some [], some []), rtShL C ds₂ ros₂) = (rootsD ros₂).length := by
    show 0 + 0 + RootsOfChain.count (uL C ds₂) (rtShL C ds₂ ros₂) = _
    rw [count_rtShL C ds₂ ros₂ _ F₂.plains]
    omega
  have hd3 : (π.roots.drop (RootsOfChain.count (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₁
      ((none, some rtF), rtSL C ds₁ ros₁))).drop
      (RootsOfChain.count (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₂ ((some [], some []), rtShL C ds₂ ros₂)) =
      rt3 ++ (rootsD ros₃ ++ rest) := by
    rw [hd2, k2]
    exact List.drop_left' rfl
  obtain ⟨c3', ρ₃, v', e3, d3, p3⟩ := det_run₃ g O hO P₃ chal hkit₃ rs₃ ros₃ c₃ ro₃ rest w3 hw₃
    ((cF, ρ₁), ((none, some rtF), rtSL C ds₁ ros₁), .loc v₁)
    ((cJ, ρ₂), ((some [], some []), rtShL C ds₂ ros₂),
      .shr (List.ofFn (bytesToDig (sealOf (_root_.Fmt.HO O) rs₂ ros₂ c₂))) cS) _ cS rfl rt3 hd3 hr3
    hr32 F₃ R₃ z₃ s3 hl₃
  exact ⟨_, _, _, v', e1, e2, e3, (whole_iff g _).2 ⟨_, _, _, e1, e2, e3, rfl⟩, rfl, rfl, rfl, rfl,
    d1, d2, d3, p1, p2, p3⟩

end Whole

end TypedOracleCompiler.Joined.K
