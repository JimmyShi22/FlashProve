-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/Batch3SWireW.lean: A SKELETON PROTOCOL's WIRING WITH WHOLE PATHS: THE FLAGS "one
walk over a pruned set of paths" (pr0 | prJ of every round's wire; pr of the stored string's)
SWITCHED OFF; THE LAWS STAY. At the batch: wqBSw.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.
WHY: the typed verifier for a proof file is the lax one WITH WHOLE PATHS: each opened position is
climbed along a path of its own. The maker's wires have the flag ON at all written rounds
(Run/PlanQS.lean: wireS; Slice/Batch3Wire.lean: wireSh; Slice/Plain3Wire.lean: we1). The flag is
data; no law of a wire names it.
  offS S A W            every round's wire with both flags off: BY RECURSION ON THE LIST OF SKELETON
    ROUNDS (no Shape, no Round as a parameter)
  offS_okg, offS_depth  the wires' laws and the bound on depths are those of W
  offE we, offE_ok      the stored string's wire with its flag off
  offQ P wq, offQ_okg    a skeleton protocol's wiring with all flags off; wq.OKG → (offQ P
    wq).OKG
  wqBSw D K chal o dec       offQ of wqBS;   wqBSw_okg (from (wqBS …).OKG);
    wqBSw_okg_pull (challenges as hash blocks: wqBS_okg_pull's hypotheses to the letter)
  offS_pr               what was wanted: in offS every wire has pr0 = false and prJ = false (AllOff)
wqBS_okg's PROOF DOES NOT CARE: the laws are carried field by field, without a look into wqBS.
WHAT IS NOT SAID. That the verifier at this wiring climbs each position alone: that is the
verifier's text (Forest.split | splitP at false). Nothing on the whole wire WF at this wiring
(Batch3SFace's WF has wqBS; a variant is a line).

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.Batch3SWire

set_option autoImplicit false

namespace TypedOracleCompiler.Slice
open TypedOracleCompiler.Iop TypedOracleCompiler.Run Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run.Twin (RS PS)

section
variable {lam K : ℕ}

/-- every round's wire with both flags off -/
def offS : (S : List RS) → (A : RoundSplits (_root_.Run.Twin.up S)) →
    RoundsQueryLayout lam K (_root_.Run.Twin.up S) A →
    RoundsQueryLayout lam K (_root_.Run.Twin.up S) A
  | [], _, _ => ()
  | _ :: S, (_, A), (w, W) => ({ w with pr0 := false, prJ := false }, offS S A W)

theorem offS_okg : ∀ (S : List RS) (A : RoundSplits (_root_.Run.Twin.up S))
    (W : RoundsQueryLayout lam K (_root_.Run.Twin.up S) A),
    RoundsQueryLayout.OKG (_root_.Run.Twin.up S) A W → RoundsQueryLayout.OKG (_root_.Run.Twin.up S) A (offS S A W)
  | [], _, _, _ => trivial
  | _ :: S, (_, A), (_, W), h =>
    ⟨⟨h.1.place_lt0, h.1.place_ltJ, h.1.posAt0_place, h.1.posAtJ_place, h.1.place_posAt0,
        h.1.place_posAtJ, h.1.no0,
        h.1.noJ, h.1.chal_unif, h.1.gr0_ok, h.1.grJ_ok⟩, offS_okg S A W h.2⟩

theorem offS_depth (n : ℕ) : ∀ (S : List RS) (A : RoundSplits (_root_.Run.Twin.up S))
    (W : RoundsQueryLayout lam K (_root_.Run.Twin.up S) A),
    RoundsQueryLayout.DepthLe n (_root_.Run.Twin.up S) A W → RoundsQueryLayout.DepthLe n (_root_.Run.Twin.up S)
        A (offS S A W)
  | [], _, _, _ => trivial
  | _ :: S, (_, A), (_, W), h => ⟨h.1, offS_depth n S A W h.2⟩

/-- all flags of a list of wires are off -/
def AllOff : (S : List RS) → (A : RoundSplits (_root_.Run.Twin.up S)) →
    RoundsQueryLayout lam K (_root_.Run.Twin.up S) A → Prop
  | [], _, _ => True
  | _ :: S, (_, A), (w, W) => (w.pr0 = false ∧ w.prJ = false) ∧ AllOff S A W

theorem offS_pr : ∀ (S : List RS) (A : RoundSplits (_root_.Run.Twin.up S))
    (W : RoundsQueryLayout lam K (_root_.Run.Twin.up S) A),
    AllOff S A (offS S A W)
  | [], _, _ => trivial
  | _ :: S, (_, A), (_, W) => ⟨⟨rfl, rfl⟩, offS_pr S A W⟩

/-- the stored string's wire with its flag off -/
def offE {E : ExtSpec} (we : WireE E) : WireE E := { we with pr := false }

theorem offE_ok {E : ExtSpec} {we : WireE E} (h : we.OK) : (offE we).OK :=
    ⟨h.nodup, h.complete, h.build_rd⟩

/-- A skeleton protocol's wiring with all flags off. -/
def offQ {Y : Type} {E : ExtSpec} (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up) : ProtocolQueryLayout lam K P.up :=
  ⟨offS P.S P.ann wq.sh, offE wq.ext, wq.decO, wq.nOpen, wq.maxDepth⟩

/-- The laws stay. -/
theorem offQ_okg {Y : Type} {E : ExtSpec} (P : PS Y E) (wq : ProtocolQueryLayout lam K P.up) (h : wq.OKG) :
    (offQ P wq).OKG :=
  ⟨offS_okg P.S P.ann wq.sh h.sh, offE_ok h.ext, h.opens,
      offS_depth wq.maxDepth P.S P.ann wq.sh h.depth⟩

end

variable {X : Type} (D : BD) (K : ℕ)

/-- The batch's wiring with whole paths. -/
def wqBSw (chal : ∀ e k, (Fin K → Dig 256) → D.G.C.Ch e k) (o : D.G.Ones)
    (dec : X → ((p : D.F.r.Pos) → D.F.r.Sym p) → D.F.r.Plain → PQ.View → PQ.View → PQ.View → Bool) :
    ProtocolQueryLayout 256 (K + 1) (BatchPS D dec).up :=
  offQ (BatchPS D dec) (wqBS D K chal o dec)

theorem wqBSw_okg (chal : ∀ e k, (Fin K → Dig 256) → D.G.C.Ch e k) (o : D.G.Ones)
    (dec : X → ((p : D.F.r.Pos) → D.F.r.Sym p) → D.F.r.Plain → PQ.View → PQ.View → PQ.View → Bool)
    (h : (wqBS D K chal o dec).OKG) : (wqBSw D K chal o dec).OKG :=
  offQ_okg (BatchPS D dec) (wqBS D K chal o dec) h

theorem wqBSw_okg_pull (f : Fmt.Fld) (o : (D.atP f).G.Ones)
    (dec : X → ((p : D.F.r.Pos) → D.F.r.Sym p) → D.F.r.Plain → PQ.View → PQ.View → PQ.View → Bool)
        (hF : D.F.Laws)
    (hK : ∀ d ∈ D.G.ds₁ ++ (D.G.ds₂ ++ D.G.ds₃), (_root_.Run.bsRound f d.entry d.kind).b ≤ K)
    (hw : ∀ d ∈ D.G.ds₁ ++ (D.G.ds₂ ++ D.G.ds₃), d.entry.work ≤ 64) :
    (wqBSw (D.atP f) K (_root_.Run.chalP f K) o dec).OKG :=
  wqBSw_okg (D.atP f) K (_root_.Run.chalP f K) o dec (wqBS_okg_pull D f K o dec hF hK hw)

end TypedOracleCompiler.Slice
